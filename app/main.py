# Copyright (c) 2026 Filipe Vasconcelos Batista <filipevbatista1@gmail.com>
# Licensed under the PolyForm Noncommercial License 1.0.0 (see LICENSE).
import copy
import hmac
import datetime
import json
import os
import re
import shutil
import threading
import time
import uuid
from zoneinfo import ZoneInfo

import requests
import yaml
from flask import Flask, jsonify, request, send_from_directory

# Caminhos: no Docker são os do container; fora dele (Flatpak, nativo) definem-se por variáveis de ambiente
DOWNLOADS = os.environ.get("LD_DOWNLOADS", "/downloads")  # destino por defeito
SELECTABLE = os.environ.get("LD_SELECTABLE", "/selectable")  # raiz opcional navegável na app
CONFIG_DIR = os.environ.get("LD_CONFIG_DIR", "/config")  # definições e histórico
CONFIG = os.path.join(CONFIG_DIR, "config.json")
HISTORY = os.path.join(CONFIG_DIR, "history.json")
USAGE = os.path.join(CONFIG_DIR, "usage.json")
SPEED_HISTORY = os.path.join(CONFIG_DIR, "speed_history.json")
# App de ambiente de trabalho (Flatpak/nativo): o destino escolhe-se com o diálogo de pastas do sistema
NATIVE = os.environ.get("LD_NATIVE") == "1"
PERIODS = ("day", "week", "month", "year")
GIB = 1024 ** 3
FR = ZoneInfo("Europe/Paris")  # a API do 1fichier indica que as datas são na hora de França
API = "https://api.1fichier.com/v1"
UA = "Mozilla/5.0 (X11; Linux x86_64) Gecko/20100101 Firefox/130.0"
ACTIVE = ("queued", "getting_link", "downloading", "paused")
RUNNING = ("queued", "getting_link", "downloading")

app = Flask(__name__, static_folder="static", static_url_path="")

# Janela de ambiente de trabalho: o servidor só atende quem tiver o segredo deste arranque (cookie) e só em localhost.
# Impede que páginas abertas no browser falem com ele (incluindo ataques de DNS rebinding, que mudam o nome do servidor).
TOKEN = os.environ.get("LD_TOKEN", "")


@app.before_request
def guard():
    if not TOKEN:
        return None
    if request.host.rsplit(":", 1)[0] not in ("127.0.0.1", "localhost"):
        return "Forbidden", 403
    given = request.args.get("token") or request.cookies.get("ld") or ""
    return None if hmac.compare_digest(given, TOKEN) else ("Forbidden", 403)


@app.after_request
def remember_token(resp):
    if TOKEN and request.args.get("token") == TOKEN:
        resp.set_cookie("ld", TOKEN, httponly=True, samesite="Strict")
    return resp
jobs = {}  # id -> dict
lock = threading.Lock()
queue_order = []  # ids dos downloads, de cima para baixo: é a ordem em que arrancam
queue_rank = {}  # id -> posição (reconstruído sempre que a ordem muda)


def rebuild_rank():
    global queue_rank
    queue_rank = {i: n for n, i in enumerate(queue_order)}


class Slots:
    """Lugares de download em simultâneo (o número pode mudar em execução). Quem espera arranca por ordem
    da fila: quando um lugar fica livre, avança o primeiro da fila que ainda está à espera."""

    def __init__(self):
        self.cv = threading.Condition()
        self.n = 0
        self.waiting = {}  # id -> (job, gen)

    @staticmethod
    def stale(job, gen):
        return job["gen"] != gen or job["status"] == "canceled"  # pausado, retomado de novo ou cancelado

    def my_turn(self, job_id):
        live = [i for i, (j, g) in self.waiting.items() if not self.stale(j, g)]
        return bool(live) and min(live, key=lambda i: queue_rank.get(i, 1 << 30)) == job_id

    def enqueue(self, job, gen):
        """Põe o job na fila já (antes de a thread arrancar), para a ordem não depender de quem arranca primeiro."""
        with self.cv:
            self.waiting[job["id"]] = (job, gen)

    def slot(self, job, gen):
        return _Slot(self, job, gen)


class _Slot:
    def __init__(self, slots, job, gen):
        self.slots, self.job, self.gen, self.got = slots, job, gen, False

    def __enter__(self):
        s, job, gen = self.slots, self.job, self.gen
        with s.cv:
            s.waiting[job["id"]] = (job, gen)
            # acorda de segundo a segundo, por isso apanha mudanças de ordem, pausas e cancelamentos
            while not (s.stale(job, gen) or (s.n < get_max_parallel() and s.my_turn(job["id"]))):
                s.cv.wait(timeout=1)
            if s.waiting.get(job["id"], (None, None))[1] == gen:  # não apaga a entrada de uma execução mais recente
                s.waiting.pop(job["id"])
            if s.stale(job, gen):
                s.cv.notify_all()
                return False  # pausado/cancelado enquanto esperava: não arranca
            s.n += 1
            self.got = True
            return True

    def __exit__(self, *exc):
        if self.got:
            with self.slots.cv:
                self.slots.n -= 1
                self.slots.cv.notify_all()


sem = Slots()


class Throttle:
    """Limite de velocidade global. Cada bloco reserva o seu intervalo de tempo num relógio partilhado,
    por isso a soma de todos os downloads em simultâneo respeita o limite."""

    def __init__(self):
        self.lock = threading.Lock()
        self.next = time.monotonic()

    def wait(self, nbytes):
        limit = get_speed_limit()  # bytes/s; 0 = sem limite
        if not limit:
            return
        with self.lock:
            now = time.monotonic()
            self.next = min(max(self.next, now), now + 1)  # não acumula atrasos se o limite mudar
            delay = self.next - now
            self.next += nbytes / limit
        if delay > 0:
            time.sleep(delay)


throttle = Throttle()


def load_cfg():
    try:
        with open(CONFIG) as f:
            return json.load(f)
    except Exception:
        return {}


def save_cfg(c):
    os.makedirs(os.path.dirname(CONFIG), exist_ok=True)
    with open(CONFIG, "w") as f:
        json.dump(c, f)
    os.chmod(CONFIG, 0o600)


# ---------------------------------------------------------------- definições (settings.yaml)
# Chaves e limites ficam num ficheiro YAML editável à mão (e pelo ecrã ⚙), fora do repositório.
# O estado interno (histórico, consumo, destino escolhido) continua em config.json/history.json/usage.json.
SETTINGS_FILE = os.environ.get("LD_SETTINGS_FILE", os.path.join(CONFIG_DIR, "settings.yaml"))
DEFAULTS = {
    "fichier_api_key": "",
    "tmdb_api_key": "",
    "downloads": {"max_parallel": 2, "speed_limit_mbps": 0},
    "api": {"requests_per_second": 2, "stop_after_errors": 5},
    "data_limit": {"gb": 0, "period": "month", "clock": "fichier", "month_start_day": 1},
    "disk": {"min_free_gb": 0, "warn_free_gb": 0},
    "network": {"detect": True},
}
ENV_INITIAL = {"fichier_api_key": "FICHIER_API_KEY", "tmdb_api_key": "TMDB_API_KEY",
               "downloads.max_parallel": "MAX_PARALLEL"}
_settings = {"mtime": -1, "data": {}, "error": ""}


def _dig(d, path, default=None):
    for k in path.split("."):
        if not isinstance(d, dict) or d.get(k) is None:
            return default
        d = d[k]
    return d


def load_settings():
    """Lê o settings.yaml (com cache pela data de modificação, para poder ser chamado a cada bloco)."""
    try:
        m = os.stat(SETTINGS_FILE).st_mtime_ns
    except OSError:
        m = None
    if m == _settings["mtime"]:
        return _settings["data"]
    data, err = {}, ""
    if m is not None:
        try:
            with open(SETTINGS_FILE) as f:
                data = yaml.safe_load(f) or {}
            if not isinstance(data, dict):
                raise ValueError("o ficheiro não é um mapa YAML")
        except Exception as e:  # ficheiro editado à mão com erro: mantém os últimos valores válidos
            data, err = _settings["data"], f"settings.yaml inválido ({e}); a usar os últimos valores válidos"
    _settings.update(mtime=m, data=data, error=err)
    return data


def sval(path, env=None):
    """Valor efetivo: settings.yaml > variável de ambiente (.env) > por defeito."""
    v = _dig(load_settings(), path)
    if v is None or v == "":
        e = os.environ.get(env, "").strip() if env else ""
        if e:
            return e
        v = _dig(DEFAULTS, path)
    return v


def ssource(path, env=None):
    v = _dig(load_settings(), path)
    if v is not None and str(v).strip():
        return "app"
    return "env" if env and os.environ.get(env, "").strip() else "none"


def snum(path, kind, lo, hi, env=None):
    try:
        v = kind(sval(path, env))
    except (TypeError, ValueError):
        v = kind(_dig(DEFAULTS, path))
    return max(lo, min(hi, v))


def render_settings(d):
    """Texto do settings.yaml, com comentários (o ficheiro é reescrito assim quando se guarda no ecrã ⚙)."""
    def g(path):
        v = _dig(d, path)
        return _dig(DEFAULTS, path) if v is None else v

    def q(v):
        return json.dumps(str(v), ensure_ascii=False)  # JSON é YAML válido

    return f"""# 1fichier Light Downloader - settings
# Podes editar este ficheiro à mão (a app relê-o sozinha) ou usar o ecrã ⚙ Definições.
# Contém as tuas API keys: NÃO o ponhas no repositório (já está no .gitignore).
# Ao guardar pelo ecrã ⚙, o ficheiro é reescrito: os comentários voltam a ser escritos e chaves desconhecidas perdem-se.

# API key do 1fichier (1fichier -> Parâmetros -> API)
fichier_api_key: {q(g("fichier_api_key"))}
# Chave do TMDB (opcional, para pesquisar nome e ano das séries)
tmdb_api_key: {q(g("tmdb_api_key"))}

downloads:
  # Downloads em simultâneo (1-10)
  max_parallel: {g("downloads.max_parallel")}
  # Limite de velocidade total em MB/s (0 = sem limite)
  speed_limit_mbps: {g("downloads.speed_limit_mbps")}

api:
  # Pedidos por segundo à API do 1fichier (máximo permitido por eles: 3)
  requests_per_second: {g("api.requests_per_second")}
  # Pausa tudo depois de N erros seguidos da API, para evitar bloqueio da conta/IP (0 = desligado)
  stop_after_errors: {g("api.stop_after_errors")}

data_limit:
  # Limite de dados descarregados por esta app, em GB (0 = sem limite)
  gb: {g("data_limit.gb")}
  # day | week | month | year
  period: {q(g("data_limit.period"))}
  # fichier = hora de França (a da API do 1fichier) | local = hora do sistema
  clock: {q(g("data_limit.clock"))}
  # Dia do mês (1-28) em que o período mensal começa
  month_start_day: {g("data_limit.month_start_day")}

disk:
  # Pausa os downloads com menos de X GB livres no destino (0 = desligado)
  min_free_gb: {g("disk.min_free_gb")}
  # Avisa quando restam menos de X GB livres (0 = desligado)
  warn_free_gb: {g("disk.warn_free_gb")}

network:
  # Guarda a velocidade por rede (operador da ligação), para não estimar tempos com a média de outra rede.
  # Para saber o operador, a app consulta o ipinfo.io de tempos a tempos (como qualquer site, esse serviço vê o teu IP;
  # a app só guarda o nome do operador). false = desligado: tudo conta como uma única rede.
  detect: {"true" if g("network.detect") in (True, "true", "True", 1, "1") else "false"}
"""


def update_settings(changes):
    """changes: {'caminho.com.pontos': valor}. Escreve o ficheiro de forma atómica, só legível pelo dono."""
    data = copy.deepcopy(load_settings())
    for path, value in changes.items():
        *parents, last = path.split(".")
        node = data
        for k in parents:
            node = node.setdefault(k, {})
        node[last] = value
    os.makedirs(os.path.dirname(SETTINGS_FILE), exist_ok=True)
    tmp = SETTINGS_FILE + ".tmp"
    with open(tmp, "w") as f:
        f.write(render_settings(data))
    os.chmod(tmp, 0o600)
    try:  # no Docker corremos como root: devolve o ficheiro ao dono da pasta, para o editares sem sudo
        st = os.stat(os.path.dirname(SETTINGS_FILE))
        os.chown(tmp, st.st_uid, st.st_gid)
    except OSError:
        pass
    os.replace(tmp, SETTINGS_FILE)
    _settings["mtime"] = -1  # força a releitura


def init_settings():
    """Primeira execução: cria o settings.yaml (e migra as definições da versão anterior, em config.json)."""
    if os.path.exists(SETTINGS_FILE):
        return
    old = load_cfg()
    legacy = {"fichier_api_key": old.get("api_key"), "tmdb_api_key": old.get("tmdb_key"),
              "downloads.max_parallel": old.get("max_parallel"), "downloads.speed_limit_mbps": old.get("speed_limit"),
              "data_limit.gb": old.get("quota_gb"), "data_limit.period": old.get("quota_period"),
              "data_limit.clock": old.get("quota_clock"), "data_limit.month_start_day": old.get("quota_day")}
    try:
        update_settings({k: v for k, v in legacy.items() if v not in (None, "")})
    except OSError as e:
        print(f"Aviso: não consegui criar {SETTINGS_FILE}: {e}", flush=True)


def get_key():
    return str(sval("fichier_api_key", "FICHIER_API_KEY")).strip()


def get_tmdb_key():
    return str(sval("tmdb_api_key", "TMDB_API_KEY")).strip()


def get_speed_limit():
    """Limite em bytes/s (definido em MB/s). 0 = sem limite."""
    return int(snum("downloads.speed_limit_mbps", float, 0, 10000) * 1_000_000)


def get_max_parallel():
    return snum("downloads.max_parallel", int, 1, 10, "MAX_PARALLEL")


def get_quota():
    """(limite em bytes, período). Limite 0 = sem limite."""
    period = sval("data_limit.period")
    return int(snum("data_limit.gb", float, 0, 1_000_000) * GIB), period if period in PERIODS else "month"


def month_anchor():
    """Dia do mês em que o 'mês' começa (1-28), para acompanhar a data de renovação da conta."""
    return snum("data_limit.month_start_day", int, 1, 28)


def quota_today():
    """O dia que conta para a quota: por defeito o de França (como o 1fichier); ou o do sistema."""
    if sval("data_limit.clock") == "local":
        return datetime.date.today()
    return datetime.datetime.now(FR).date()


def sbool(path):
    return sval(path) in (True, "true", "True", "yes", 1, "1")


def get_disk_limits():
    """(mínimo livre, aviso) em bytes. 0 = desligado."""
    return (int(snum("disk.min_free_gb", float, 0, 1_000_000) * GIB),
            int(snum("disk.warn_free_gb", float, 0, 1_000_000) * GIB))


def selectable_enabled():
    return bool(os.environ.get("HOST_SELECTABLE_DIR", "").strip())


def resolve_dir(rel):
    """Caminho dentro de /selectable; recusa tudo o que saia dessa raiz."""
    root = os.path.realpath(SELECTABLE)
    p = os.path.realpath(os.path.join(root, (rel or "").strip("/")))
    if p != root and not p.startswith(root + os.sep):
        raise ValueError("Pasta fora da raiz permitida")
    return p


def rel_dir(p):
    r = os.path.relpath(p, os.path.realpath(SELECTABLE))
    return "" if r == "." else r


def set_dest_abs(path):
    """Modo nativo: guarda uma pasta absoluta como destino (escolhida no diálogo do sistema)."""
    if not NATIVE:
        raise ValueError("Só disponível na aplicação de ambiente de trabalho")
    p = os.path.realpath(path)
    if not os.path.isdir(p) or not os.access(p, os.W_OK | os.X_OK):
        raise ValueError(f"Não consigo gravar em {p}")
    c = load_cfg()
    c["dest_abs"] = p
    save_cfg(c)
    return p


def current_dest():
    """(caminho onde se grava, rótulo para mostrar) do destino em vigor."""
    if NATIVE:
        p = load_cfg().get("dest_abs")
        return (p, p) if p else (DOWNLOADS, DOWNLOADS)
    rel = load_cfg().get("dest")  # None = destino por defeito
    if rel is not None and selectable_enabled():
        host = os.environ["HOST_SELECTABLE_DIR"].rstrip("/")
        return resolve_dir(rel), host + ("/" + rel if rel else "")
    return DOWNLOADS, os.environ.get("HOST_DOWNLOAD_DIR", DOWNLOADS)


def require_selectable():
    if not selectable_enabled():
        raise ValueError("Seleção de pastas desativada (SELECTABLE_DIR não definida)")


def load_history():
    try:
        with open(HISTORY) as f:
            return json.load(f)
    except Exception:
        return {}


def save_history(h):
    os.makedirs(os.path.dirname(HISTORY), exist_ok=True)
    with open(HISTORY, "w") as f:
        json.dump(h, f)


def period_start(period, today=None):
    d = today or quota_today()
    if period == "day":
        return d
    if period == "week":
        return d - datetime.timedelta(days=d.weekday())  # segunda-feira
    if period == "month":
        a = month_anchor()
        if d.day >= a:
            return d.replace(day=a)
        return (d.replace(day=1) - datetime.timedelta(days=1)).replace(day=a)
    return d.replace(month=1, day=1)


def next_period_start(period, start):
    if period == "day":
        return start + datetime.timedelta(days=1)
    if period == "week":
        return start + datetime.timedelta(days=7)
    if period == "month":
        return (start.replace(day=28) + datetime.timedelta(days=4)).replace(day=month_anchor())
    return start.replace(year=start.year + 1)


class Usage:
    """Bytes descarregados por esta app, guardados por dia. Assim o período (dia/semana/mês/ano)
    pode mudar a qualquer momento: soma-se apenas os dias que pertencem ao período em vigor."""

    def __init__(self):
        self.lock = threading.Lock()
        self.saved = time.monotonic()
        try:
            with open(USAGE) as f:
                self.days = json.load(f)
        except Exception:
            self.days = {}

    def add(self, nbytes):
        with self.lock:
            k = quota_today().isoformat()
            self.days[k] = self.days.get(k, 0) + nbytes
            if time.monotonic() - self.saved > 5:
                self._save()

    def used(self, period):
        start = period_start(period).isoformat()
        with self.lock:
            return sum(v for k, v in self.days.items() if k >= start)

    def _save(self):
        cutoff = (quota_today() - datetime.timedelta(days=400)).isoformat()
        self.days = {k: v for k, v in self.days.items() if k >= cutoff}
        os.makedirs(CONFIG_DIR, exist_ok=True)
        with open(USAGE, "w") as f:
            json.dump(self.days, f)
        self.saved = time.monotonic()

    def flush(self):
        with self.lock:
            self._save()

    def reset(self):
        with self.lock:
            self.days = {}
            self._save()


usage = Usage()


class NetworkInfo:
    """Identifica a rede pelo operador da ligação (ASN), via ipinfo.io. Só guarda o operador, nunca o IP.
    A consulta nunca corre no caminho do download: get() devolve o último valor conhecido."""

    TTL = 300  # s entre consultas
    UNKNOWN = {"id": "unknown", "name": ""}

    def __init__(self):
        self.lock = threading.Lock()
        self.value = dict(self.UNKNOWN)
        self.checked = 0.0

    def get(self):
        with self.lock:
            return dict(self.value)

    def refresh(self, force=False):
        if not sbool("network.detect"):
            with self.lock:
                self.value = dict(self.UNKNOWN)
            return
        now = time.monotonic()
        if not force and now - self.checked < self.TTL:
            return
        try:
            org = requests.get("https://ipinfo.io/json", timeout=5, headers={"User-Agent": UA}).json().get("org") or ""
            m = re.match(r"(AS\d+)\s*(.*)", org)
            value = {"id": m.group(1), "name": m.group(2)} if m else {"id": org, "name": org}
            if not value["id"]:
                raise ValueError("sem operador")
        except Exception:
            self.checked = now - self.TTL + 30  # falhou (sem rede?): tenta de novo daqui a 30 s e mantém o último valor
            return
        with self.lock:
            self.value, self.checked = value, now


network = NetworkInfo()


class SpeedLog:
    """Débito total (todos os downloads somados) por sessão, guardado para estimar tempos em sessões futuras.
    Uma sessão acaba quando passam SESSION_GAP segundos sem dados. Só conta o tempo em que houve dados
    (pausas e esperas ficam de fora) e esse tempo conta uma só vez, mesmo com downloads em paralelo."""

    SESSION_GAP = 600  # s sem dados -> nova sessão
    ACTIVE_GAP = 5  # s: intervalos maiores entre blocos não contam como tempo a descarregar
    KEEP = 30  # sessões guardadas
    RECENT = 5  # sessões usadas na média

    def __init__(self):
        self.lock = threading.Lock()
        self.cur = None
        self.last = None  # time.monotonic() do último bloco
        self.dirty = False
        try:
            with open(SPEED_HISTORY) as f:
                self.sessions = json.load(f)
        except Exception:
            self.sessions = []

    def add(self, nbytes):
        now = time.monotonic()
        net = network.get()
        with self.lock:
            # nova sessão: passou muito tempo sem dados ou a rede mudou
            if (self.cur is None or self.last is None or now - self.last > self.SESSION_GAP
                    or self.cur["net"] != net["id"]):
                self.cur = {"start": time.strftime("%Y-%m-%d %H:%M"), "bytes": 0, "secs": 0.0,
                            "net": net["id"], "net_name": net["name"]}
                self.sessions.append(self.cur)
                self.sessions = self.sessions[-self.KEEP:]
                self.last = None
            gap = now - self.last if self.last is not None else 0
            if gap <= self.ACTIVE_GAP:
                self.cur["secs"] += gap
            self.cur["bytes"] += nbytes
            self.last, self.dirty = now, True

    def _avg(self, sessions):
        usable = [x for x in sessions if x["secs"] >= 30]  # ignora sessões minúsculas
        secs = sum(x["secs"] for x in usable)
        return (sum(x["bytes"] for x in usable) / secs if secs else 0), len(usable)

    def stats(self):
        """Média só com sessões da rede atual: a velocidade de outra rede não serve para estimar esta."""
        net = network.get()
        with self.lock:
            by_net = {}
            for x in self.sessions:
                by_net.setdefault(x.get("net", "unknown"), []).append(x)
            mine = by_net.get(net["id"], [])[-self.RECENT:]
            avg, used = self._avg(mine)
            rows = [{"start": x["start"], "bytes": x["bytes"], "secs": round(x["secs"]),
                     "speed": x["bytes"] / x["secs"] if x["secs"] >= 10 else 0} for x in mine]
            networks = []
            for nid, xs in by_net.items():
                n_avg, n_used = self._avg(xs[-self.RECENT:])
                name = next((x.get("net_name") for x in reversed(xs) if x.get("net_name")), "")
                networks.append({"id": nid, "name": name, "avg": n_avg, "sessions": n_used, "current": nid == net["id"]})
            return {"network": net, "avg": avg, "used": used, "sessions": rows, "networks": networks}

    def flush(self):
        with self.lock:
            if not self.dirty:
                return
            os.makedirs(CONFIG_DIR, exist_ok=True)
            with open(SPEED_HISTORY, "w") as f:
                json.dump([{"start": x["start"], "bytes": x["bytes"], "secs": round(x["secs"], 1),
                            "net": x.get("net", "unknown"), "net_name": x.get("net_name", "")} for x in self.sessions], f)
            self.dirty = False


speedlog = SpeedLog()


def quota_exceeded():
    limit, period = get_quota()
    return limit > 0 and usage.used(period) >= limit


def quota_info():
    limit, period = get_quota()
    start = period_start(period)
    return {"period": period, "limit": limit, "used": usage.used(period),
            "since": start.isoformat(), "resets": next_period_start(period, start).isoformat(),
            "exceeded": limit > 0 and usage.used(period) >= limit}


def pause_all_for(reason):
    """Pausa tudo o que está ativo ou na fila. reason: quota | disk | api."""
    with lock:
        for j in jobs.values():
            if j["status"] in RUNNING:
                j["status"], j["paused_by"], j["speed"] = "paused", reason, 0
                j["gen"] += 1


def free_space(path):
    while path and not os.path.exists(path):  # a pasta de destino pode ainda não existir
        path = os.path.dirname(path)
    return shutil.disk_usage(path or "/").free


def disk_low(path):
    minimum, _ = get_disk_limits()
    return minimum > 0 and free_space(path) < minimum


def disk_state(path):
    minimum, warn = get_disk_limits()
    warn = max(warn, minimum) if warn else 0
    free = free_space(path)
    return {"free": free, "min_free": minimum, "warn_free": warn,
            "low": minimum > 0 and free < minimum, "near": warn > 0 and minimum <= free < warn}


class ApiGate:
    """Limita os pedidos à API do 1fichier (máx. 3/s segundo a documentação) e dispara um 'disjuntor':
    muitos erros seguidos (401/403/404/410/429, KO) levam a bloqueio temporário do IP/conta, por isso pára tudo."""

    def __init__(self):
        self.lock = threading.Lock()
        self.next = time.monotonic()
        self.errors = 0
        self.tripped = False

    def wait(self):
        rps = snum("api.requests_per_second", float, 0.2, 3)
        with self.lock:
            now = time.monotonic()
            self.next = max(self.next, now)
            delay = self.next - now
            self.next += 1 / rps
        if delay > 0:
            time.sleep(delay)

    def result(self, ok):
        with self.lock:
            self.errors = 0 if ok else self.errors + 1
            limit = int(snum("api.stop_after_errors", int, 0, 100))
            trip = limit > 0 and self.errors >= limit and not self.tripped
            self.tripped = self.tripped or trip
        if trip:
            pause_all_for("api")

    def reset(self):
        with self.lock:
            self.errors, self.tripped = 0, False

    def snapshot(self):
        return {"tripped": self.tripped, "errors": self.errors, "limit": int(snum("api.stop_after_errors", int, 0, 100))}


api_gate = ApiGate()


def api_post(path, payload):
    """POST à API do 1fichier, respeitando o limite de pedidos e a contagem de erros. Devolve (resposta, json)."""
    api_gate.wait()
    key = get_key()
    if not key:
        raise RuntimeError("API key não definida (Definições)")
    r = requests.post(f"{API}/{path}", json=payload, headers={"Authorization": f"Bearer {key}"}, timeout=30)
    try:
        j = r.json()
    except ValueError:
        j = {}
    api_gate.result(r.status_code not in (401, 403, 404, 410, 429) and j.get("status") != "KO")
    return r, j


def limits_tick():
    """Guarda o consumo e retoma o que um limite (dados, disco) tinha pausado, se já houver margem.
    O que o disjuntor da API pausou não retoma sozinho: tens de o fazer tu."""
    usage.flush()
    speedlog.flush()
    network.refresh()
    for j in list(jobs.values()):
        if j["status"] != "paused":
            continue
        why = j.get("paused_by")
        if (why == "quota" and not quota_exceeded()) or (why == "disk" and not disk_low(j["dest"])):
            resume_job(j)


def quota_watcher():
    while True:
        time.sleep(20)
        limits_tick()


def record_history(job, dest):
    """Guarda um download concluído: url -> {filename, path (no container), rel (no destino), date}."""
    with lock:
        h = load_history()
        h[job["url"]] = {"filename": job["filename"], "path": dest, "rel": os.path.relpath(dest, job["dest"]),
                         "size": job["size"], "date": time.strftime("%Y-%m-%d %H:%M")}
        save_history(h)


def safe_name(n):
    n = re.sub(r'[\\/:*?"<>|\x00-\x1f]', "_", n or "").strip(" .")
    return n or "ficheiro"


def list_folder(link):
    """Devolve [{filename,size,url}] de uma pasta partilhada do 1fichier."""
    m = re.search(r"1fichier\.com/(?:dir/|\?)([A-Za-z0-9]+)", link)
    if not m:
        raise ValueError("Link inválido")
    fid = m.group(1)
    r = requests.get(f"https://1fichier.com/dir/{fid}?json=2", headers={"User-Agent": UA}, timeout=30)
    try:
        data = r.json()
    except ValueError:
        data = None
    if isinstance(data, (list, dict)) and items_from_json(data):
        return items_from_json(data)
    # fallback: HTML da página da pasta
    html = requests.get(f"https://1fichier.com/dir/{fid}", headers={"User-Agent": UA}, timeout=30).text
    if "Accès restreint" in html or "professional infrastructure" in html:
        raise RuntimeError("O 1fichier bloqueou este IP (VPN/proxy/servidor?)")
    out = []
    for url, name in re.findall(r'<a href="(https://1fichier\.com/\?[A-Za-z0-9]+)"[^>]*>([^<]+)</a>', html):
        out.append({"filename": name.strip(), "size": 0, "url": url})
    if not out:
        raise RuntimeError("Não consegui listar ficheiros (pasta vazia, privada ou com password?)")
    return out


def items_from_json(data):
    """Normaliza as respostas do 1fichier (json=1 lista; json=2 dict indexado com a chave 'link')."""
    if isinstance(data, dict):
        vals = list(data.values())
        data = vals if vals and all(isinstance(v, dict) for v in vals) else \
            next((v for v in vals if isinstance(v, list)), [data])
    out = []
    for d in data:
        if isinstance(d, dict) and (d.get("url") or d.get("link")):
            out.append({"filename": d.get("filename") or "", "size": int(d.get("size") or 0),
                        "url": d.get("url") or d.get("link")})
    return out


def parse_tables(text):
    """Texto copiado da vista de tabela do browser ('0', 'link "..."', 'filename "..."', ...).
    Cada vez que o índice volta a 0 começa uma nova tabela."""
    tables, cur = [], None
    for line in text.splitlines():
        m = re.fullmatch(r"\s*(\d+)\s*", line)
        if m:
            if m.group(1) == "0" or not tables:
                tables.append([])
            cur = {}
            tables[-1].append(cur)
        elif cur is not None:
            m = re.match(r"\s*(\w+)\s+(.*?)\s*$", line)
            if m:
                cur[m.group(1)] = m.group(2).strip('"')
    return [items_from_json(t) for t in tables if items_from_json(t)]


def parse_json_docs(text):
    """Vários JSON seguidos -> lista de documentos; None se o texto não for só JSON (objetos/listas)."""
    dec, i, docs = json.JSONDecoder(), 0, []
    while True:
        while i < len(text) and text[i].isspace():
            i += 1
        if i >= len(text):
            return docs or None
        try:
            doc, i = dec.raw_decode(text, i)
        except ValueError:
            return None
        if not isinstance(doc, (dict, list)):
            return None
        docs.append(doc)


def parse_groups(text, folders=False):
    """Divide o input em grupos [{kind, ref, files}]: um por JSON, tabela ou pasta (/dir/)."""
    docs = parse_json_docs(text)
    if docs:
        groups = [{"kind": "json", "ref": "", "files": items_from_json(d)} for d in docs]
        if not all(g["files"] for g in groups):
            raise ValueError("JSON sem entradas com 'url'/'link'")
        return groups
    tables = parse_tables(text)
    if tables:
        return [{"kind": "table", "ref": "", "files": t} for t in tables]
    links = list(dict.fromkeys(re.findall(r"https?://1fichier\.com/(?:dir/|\?)[A-Za-z0-9]+", text)))
    if not links:
        raise ValueError("Não encontrei links do 1fichier")
    groups = [{"kind": "folder", "ref": u, "files": list_folder(u)}
              for u in links if "/dir/" in u or folders]
    plain = [u for u in links if "/dir/" not in u and not folders]
    if plain:
        groups.append({"kind": "links", "ref": "", "files": [{"filename": "", "size": 0, "url": u} for u in plain]})
    return groups


# Nome S01E02 | Nome S1.E01 | S1.E01.Título (sem nome de série à frente)
SERIES_RE = re.compile(r"^(?:(.*?)[\s._-]+)?S(\d{1,2})[\s._-]?E(\d{1,3})", re.I)
ALT_RE = re.compile(r"^(.*?)[\s._-]+(\d{1,2})x(\d{2,3})\b", re.I)  # Nome 1x05
# Nome - 05 - Título | Nome - 001 [tags] | Nome - 12.mkv  (numeração contínua; 4 dígitos só se não for um ano)
ABS_RE = re.compile(r"^(.*?)\s+-\s+(\d{1,3}|(?!19|20)\d{4})(?:\s*v\d+)?(?:\s+-\s+|\s*[\[(.]|\s*$)")
# [Grupo].Nome-22-Título.tags  (hífens sem espaços; último recurso)
DASH_RE = re.compile(r"^(?:\[[^\]]*\][\s._]*)?(.+?)-(\d{1,3})(?:v\d+)?(?=-|[\s._\[(]|$)")


def parse_episode(filename):
    """'Título.S02E05...' / 'Título 2x05' / 'Título - 05 - ...' -> ('Título', temporada, episódio).
    Sem temporada no nome assume-se a 1. Sem padrão -> ('', None, None)."""
    fn = (filename or "").replace("_", " ")  # 'Nome_-_001_[tags]' passa a 'Nome - 001 [tags]'
    m = SERIES_RE.match(fn) or ALT_RE.match(fn)
    if m:
        season, ep = int(m.group(2)), int(m.group(3))
    else:
        m = ABS_RE.match(fn) or DASH_RE.match(fn)
        if not m:
            return "", None, None
        season, ep = 1, int(m.group(2))
    title = re.sub(r"^(\[[^\]]*\]\s*)+", "", m.group(1) or "")  # tira [grupo] no início
    return safe_name(re.sub(r"[._]+", " ", title).strip()), season, ep


def describe_group(group):
    """Acrescenta série/temporada/episódio a cada ficheiro e os nomes detectados (mais frequente primeiro)."""
    counts, first = {}, {}
    for f in group["files"]:
        f["series"], f["season"], f["episode"] = parse_episode(f["filename"])
        if f["series"]:
            k = f["series"].lower()
            counts[k] = counts.get(k, 0) + 1
            first.setdefault(k, f["series"])
    group["names"] = [first[k] for k in sorted(counts, key=counts.get, reverse=True)]
    return group


def series_name(filename, series="", year=""):
    """'Nome (Ano)'. 'series' força o nome; sem ele usa o detectado no ficheiro."""
    name = safe_name(series) if series else parse_episode(filename)[0]
    if name and year and not re.search(r"\(\d{4}\)$", name):
        name += f" ({year})"
    return name


def target_folder(filename, series="", year="", tmdb_id=""):
    """'Nome (Ano) [tmdbid-N]/Season NN'."""
    name = series_name(filename, series, year)
    if not name:
        return ""
    if tmdb_id:
        name += f" [tmdbid-{tmdb_id}]"
    season = parse_episode(filename)[1]
    return os.path.join(name, f"Season {season:02d}") if season is not None else name


NAME_MODES = ("original", "series", "episode")


def target_filename(filename, series="", year="", mode="original"):
    """original | series ('Nome (Ano) S01E01.ext') | episode ('S01E01.ext')."""
    _, season, ep = parse_episode(filename)
    if mode == "original" or season is None:
        return safe_name(filename)
    code = f"S{season:02d}E{ep:02d}"
    ext = os.path.splitext(filename)[1]
    if mode == "episode":
        return code + ext
    return f"{series_name(filename, series, year)} {code}{ext}"


def tmdb_get(path, **params):
    key = get_tmdb_key()
    if not key:
        raise RuntimeError("Chave do TMDB não definida (Definições)")
    headers = {"Authorization": f"Bearer {key}"} if key.startswith("eyJ") else {}
    if not headers:
        params["api_key"] = key
    r = requests.get(f"https://api.themoviedb.org/3{path}", params=params, headers=headers, timeout=15)
    if r.status_code == 401:
        raise RuntimeError("TMDB: chave inválida")
    r.raise_for_status()
    return r.json()


def advance(job, gen, status):
    """Muda o estado só se esta execução (gen) continua a ser a atual e o job não foi cancelado."""
    with lock:
        if job["gen"] != gen or job["status"] == "canceled":
            return False
        job["status"] = status
        return True


def run_job(job, gen):
    with sem.slot(job, gen) as got:
        if not got:
            return
        for reason, hit in (("api", api_gate.tripped), ("quota", quota_exceeded()), ("disk", disk_low(job["dest"]))):
            if hit:  # nunca arranca com um limite esgotado
                pause_all_for(reason)
                return
        if not advance(job, gen, "getting_link"):
            return
        try:
            if not job["filename"]:
                _, info = api_post("file/info.cgi", {"url": job["url"]})
                if info.get("status") == "KO" or not info.get("filename"):
                    raise RuntimeError(info.get("message", "Ficheiro não encontrado"))
                job["filename"] = info["filename"]
                job["size"] = int(info.get("size") or 0)
            _, j = api_post("download/get_token.cgi", {"url": job["url"]})
            if j.get("status") != "OK":
                raise RuntimeError(j.get("message", "Erro ao obter link"))
            if not advance(job, gen, "downloading"):
                return
            dest = os.path.join(job["dest"], target_folder(job["filename"], job["series"], job["year"], job["tmdb_id"]),
                                target_filename(job["filename"], job["series"], job["year"], job["name_mode"]))
            os.makedirs(os.path.dirname(dest), exist_ok=True)
            part = dest + ".part"
            done = os.path.getsize(part) if os.path.exists(part) else 0
            hdr = {"User-Agent": UA}
            if done:
                hdr["Range"] = f"bytes={done}-"
            with requests.get(j["url"], headers=hdr, stream=True, timeout=60) as d:
                if d.status_code == 200:
                    done = 0
                elif d.status_code != 206:
                    raise RuntimeError(f"HTTP {d.status_code}")
                total = done + int(d.headers.get("Content-Length", 0))
                job["size"] = total or job["size"]
                t0, base, last_disk = time.time(), done, 0.0
                with open(part, "ab" if done else "wb") as f:
                    for chunk in d.iter_content(1 << 18):
                        throttle.wait(len(chunk))
                        if job["gen"] != gen or job["status"] == "canceled":
                            return  # pausado ou cancelado: o .part fica para retomar
                        f.write(chunk)
                        done += len(chunk)
                        job["done"] = done
                        job["speed"] = (done - base) / max(time.time() - t0, 0.001)
                        usage.add(len(chunk))
                        speedlog.add(len(chunk))
                        if quota_exceeded():
                            pause_all_for("quota")
                            return
                        if time.monotonic() - last_disk > 2:  # o disco não se verifica a cada bloco
                            last_disk = time.monotonic()
                            if disk_low(job["dest"]):
                                pause_all_for("disk")
                                return
            os.replace(part, dest)
            record_history(job, dest)
            job["status"] = "done"
        except Exception as e:
            with lock:
                if job["gen"] == gen:  # se entretanto foi pausado/cancelado, esse estado prevalece
                    job["status"], job["error"] = "error", str(e)


@app.get("/")
def index():
    return send_from_directory("static", "index.html")


@app.get("/api/config")
def get_config():
    return jsonify(has_key=bool(get_key()), has_tmdb=bool(get_tmdb_key()),
                   dest_label=current_dest()[1], selectable=selectable_enabled(),
                   selectable_root=os.environ.get("HOST_SELECTABLE_DIR", "").rstrip("/"),
                   dest_rel=load_cfg().get("dest") if selectable_enabled() else None,
                   native=NATIVE, dest_custom=bool(NATIVE and load_cfg().get("dest_abs")),
                   dest_missing=not os.path.isdir(current_dest()[0]))


@app.get("/api/usage")
def api_usage():
    return jsonify(quota_info())


@app.post("/api/usage/reset")
def api_usage_reset():
    usage.reset()
    return jsonify(ok=True)


def _num(kind, lo, hi):
    def f(v):
        return max(lo, min(hi, kind(v if v not in (None, "") else 0)))
    return f


def _enum(*options):
    def f(v):
        if v not in options:
            raise ValueError(v)
        return v
    return f


def _bool(v):
    if isinstance(v, str):
        return v.strip().lower() in ("true", "1", "yes")
    return bool(v)


def _secret(v):
    return (v or "").strip()


# campo do pedido -> (caminho no settings.yaml, validação/conversão)
FIELDS = {
    "fichier_api_key": ("fichier_api_key", _secret),
    "tmdb_api_key": ("tmdb_api_key", _secret),
    "max_parallel": ("downloads.max_parallel", _num(int, 1, 10)),
    "speed_limit": ("downloads.speed_limit_mbps", _num(float, 0, 10000)),
    "requests_per_second": ("api.requests_per_second", _num(float, 0.2, 3)),
    "stop_after_errors": ("api.stop_after_errors", _num(int, 0, 100)),
    "quota_gb": ("data_limit.gb", _num(float, 0, 1_000_000)),
    "quota_period": ("data_limit.period", _enum(*PERIODS)),
    "quota_clock": ("data_limit.clock", _enum("fichier", "local")),
    "quota_day": ("data_limit.month_start_day", _num(int, 1, 28)),
    "disk_min_free_gb": ("disk.min_free_gb", _num(float, 0, 1_000_000)),
    "disk_warn_free_gb": ("disk.warn_free_gb", _num(float, 0, 1_000_000)),
    "network_detect": ("network.detect", _bool),
}


@app.get("/api/limits")
def api_limits():
    """Estado dos limites que pedem atenção: disco do destino e disjuntor da API."""
    load_settings()
    return jsonify(disk=disk_state(current_dest()[0]), api=api_gate.snapshot(), settings_error=_settings["error"],
                   speed=speedlog.stats())


@app.get("/api/settings")
def get_settings():
    """Nunca devolve as chaves, só se existem e de onde vêm (settings.yaml ou .env)."""
    load_settings()
    minimum, warn = get_disk_limits()
    return jsonify(fichier={"set": bool(get_key()), "source": ssource("fichier_api_key", "FICHIER_API_KEY")},
                   tmdb={"set": bool(get_tmdb_key()), "source": ssource("tmdb_api_key", "TMDB_API_KEY")},
                   max_parallel=get_max_parallel(), speed_limit=get_speed_limit() / 1_000_000,
                   requests_per_second=snum("api.requests_per_second", float, 0.2, 3),
                   stop_after_errors=int(snum("api.stop_after_errors", int, 0, 100)),
                   quota_gb=get_quota()[0] / GIB, quota_period=get_quota()[1], usage=quota_info(),
                   quota_clock="local" if sval("data_limit.clock") == "local" else "fichier", quota_day=month_anchor(),
                   disk_min_free_gb=minimum / GIB, disk_warn_free_gb=warn / GIB, network_detect=sbool("network.detect"),
                   settings_file=os.environ.get("HOST_SETTINGS_FILE", SETTINGS_FILE), settings_error=_settings["error"])


@app.post("/api/settings")
def set_settings():
    """Só altera o que vier no pedido. Texto vazio numa chave apaga o valor (volta a valer o .env, se existir)."""
    changes = {}
    for field, value in request.json.items():
        if field not in FIELDS:
            continue
        path, convert = FIELDS[field]
        try:
            changes[path] = convert(value)
        except (TypeError, ValueError):
            return jsonify(error=f"{field} inválido"), 400
    try:
        update_settings(changes)
    except OSError as e:
        return jsonify(error=f"Não consegui guardar {SETTINGS_FILE}: {e}"), 500
    with sem.cv:
        sem.cv.notify_all()  # se o limite subiu, os downloads em espera arrancam já
    return jsonify(ok=True)


@app.get("/api/folders")
def api_folders():
    try:
        require_selectable()
        p = resolve_dir(request.args.get("path", ""))
        dirs = sorted((d for d in os.listdir(p) if not d.startswith(".") and os.path.isdir(os.path.join(p, d))),
                      key=str.lower)
        rel = rel_dir(p)
        return jsonify(path=rel, parent=None if not rel else rel_dir(os.path.dirname(p)), dirs=dirs)
    except Exception as e:
        return jsonify(error=str(e)), 400


@app.post("/api/folders")
def api_mkdir():
    try:
        require_selectable()
        p = os.path.join(resolve_dir(request.json.get("path", "")), safe_name(request.json.get("name", "")))
        resolve_dir(rel_dir(os.path.realpath(p)))
        os.makedirs(p, exist_ok=True)
        return jsonify(path=rel_dir(os.path.realpath(p)))
    except Exception as e:
        return jsonify(error=str(e)), 400


@app.post("/api/dest")
def api_dest():
    """{path} escolhe uma pasta dentro de SELECTABLE_DIR; {reset: true} volta ao destino por defeito."""
    try:
        c = load_cfg()
        if request.json.get("reset"):
            c.pop("dest", None)
            c.pop("dest_abs", None)
        elif "abs" in request.json:
            set_dest_abs(request.json["abs"])
            return jsonify(ok=True)
        else:
            require_selectable()
            p = resolve_dir(request.json.get("path", ""))
            if not os.path.isdir(p):
                raise ValueError("Pasta inexistente")
            c["dest"] = rel_dir(p)
        save_cfg(c)
        return jsonify(ok=True)
    except Exception as e:
        return jsonify(error=str(e)), 400


@app.get("/api/history")
def api_history():
    h = load_history()
    items = [dict(url=u, **{k: v[k] for k in ("filename", "rel", "date")}) for u, v in h.items()]
    return jsonify(items=sorted(items, key=lambda i: i["date"], reverse=True))


@app.post("/api/history/remove")
def api_history_remove():
    with lock:
        h = load_history()
        h.pop(request.json.get("url", ""), None)
        save_history(h)
    return jsonify(ok=True)


@app.post("/api/history/clear")
def api_history_clear():
    with lock:
        save_history({})
    return jsonify(ok=True)


@app.post("/api/list")
def api_list():
    try:
        groups = parse_groups(request.json["text"], request.json.get("folders", False))
        hist = load_history()
        for g in groups:
            for f in g["files"]:  # só conta como descarregado se o ficheiro ainda existir
                h = hist.get(f["url"])
                f["downloaded"] = bool(h and os.path.exists(h["path"]))
                f["downloaded_at"] = h["date"] if f["downloaded"] else ""
        return jsonify(groups=[describe_group(g) for g in groups])
    except Exception as e:
        return jsonify(error=str(e)), 400


@app.get("/api/tmdb")
def api_tmdb():
    try:
        data = tmdb_get("/search/tv", query=request.args.get("q", ""), language=request.args.get("lang", "en-US"))
        return jsonify(results=[
            {"id": r["id"], "name": r["name"], "original_name": r.get("original_name"),
             "year": (r.get("first_air_date") or "")[:4], "overview": (r.get("overview") or "")[:160]}
            for r in data.get("results", [])[:8]])
    except Exception as e:
        return jsonify(error=str(e)), 400


@app.post("/api/start")
def api_start():
    dest = current_dest()[0]
    if not os.path.isdir(dest):  # nunca grava noutro sítio sem avisar (ex.: disco externo desligado)
        return jsonify(error=f"A pasta de destino não está disponível: {dest}"), 409
    for g in request.json["groups"]:
        series = (g.get("series") or "").strip()
        year = g.get("year") or ""
        year = year if re.fullmatch(r"\d{4}", year) else ""
        tmdb_id = str(g.get("tmdb_id") or "")
        tmdb_id = tmdb_id if tmdb_id.isdigit() else ""
        name_mode = g.get("name_mode") if g.get("name_mode") in NAME_MODES else "original"
        for f in g["files"]:
            job = dict(id=uuid.uuid4().hex[:8], url=f["url"], filename=f["filename"], size=f.get("size", 0),
                       done=0, speed=0, gen=0, status="queued", error="", series=series, year=year,
                       tmdb_id=tmdb_id, name_mode=name_mode, dest=dest)
            with lock:
                jobs[job["id"]] = job
                queue_order.append(job["id"])
                rebuild_rank()
            sem.enqueue(job, job["gen"])
            threading.Thread(target=run_job, args=(job, job["gen"]), daemon=True).start()
    return jsonify(ok=True)


@app.get("/api/jobs")
def api_jobs():
    with lock:
        return jsonify([jobs[i] for i in queue_order if i in jobs])


def pause_job(job):
    with lock:
        if job["status"] in RUNNING:
            job["status"], job["paused_by"] = "paused", "user"
            job["gen"] += 1  # a thread atual para no próximo bloco
            job["speed"] = 0


def resume_job(job):
    with lock:
        if job["status"] != "paused":
            return
        if job.get("paused_by") == "api":
            api_gate.reset()  # tu verificaste o problema e retomaste: o contador de erros recomeça
        job["status"], job["error"], job["paused_by"] = "queued", "", None
        job["gen"] += 1
        gen = job["gen"]
    sem.enqueue(job, gen)
    threading.Thread(target=run_job, args=(job, gen), daemon=True).start()


@app.post("/api/cancel/<jid>")
def api_cancel(jid):
    with lock:
        if jid in jobs and jobs[jid]["status"] in ACTIVE:
            jobs[jid]["status"] = "canceled"
            jobs[jid]["gen"] += 1
    return jsonify(ok=True)


def retry_job(job):
    """Repete um download que falhou (ou foi cancelado); continua a partir do .part, se existir."""
    with lock:
        if job["status"] not in ("error", "canceled"):
            return
        job["status"], job["error"], job["paused_by"], job["speed"] = "queued", "", None, 0
        job["gen"] += 1
        gen = job["gen"]
    sem.enqueue(job, gen)
    threading.Thread(target=run_job, args=(job, gen), daemon=True).start()


@app.post("/api/retry/<jid>")
def api_retry(jid):
    if jid in jobs:
        retry_job(jobs[jid])
    return jsonify(ok=True)


@app.post("/api/reorder")
def api_reorder():
    """{ids: [...]}: nova ordem da fila (de cima para baixo). O que não vier na lista fica no fim."""
    ids = [i for i in dict.fromkeys(request.json.get("ids", [])) if i in jobs]
    with lock:
        queue_order[:] = ids + [i for i in queue_order if i not in ids]
        rebuild_rank()
    with sem.cv:
        sem.cv.notify_all()
    return jsonify(ok=True)


@app.post("/api/pause/<jid>")
def api_pause(jid):
    if jid in jobs:
        pause_job(jobs[jid])
    return jsonify(ok=True)


@app.post("/api/resume/<jid>")
def api_resume(jid):
    if jid in jobs:
        resume_job(jobs[jid])
    return jsonify(ok=True)


@app.post("/api/pause_all")
def api_pause_all():
    for j in list(jobs.values()):
        pause_job(j)
    return jsonify(ok=True)


@app.post("/api/resume_all")
def api_resume_all():
    for j in list(jobs.values()):
        resume_job(j)
    return jsonify(ok=True)


@app.post("/api/clear")
def api_clear():
    with lock:
        for k in [k for k, v in jobs.items() if v["status"] not in ACTIVE]:
            del jobs[k]
        queue_order[:] = [i for i in queue_order if i in jobs]
        rebuild_rank()
    return jsonify(ok=True)


init_settings()
threading.Thread(target=network.refresh, args=(True,), daemon=True).start()
threading.Thread(target=quota_watcher, daemon=True).start()
