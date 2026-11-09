"""
MINI CS 3D - FPS estilo CoD com bots e MULTIPLAYER (Python puro, só tkinter + socket)

Dois times: AZUL (CT) x LARANJA (T). Rodadas de eliminação, 7 vitórias vencem a partida.
Dá para jogar sozinho com bots, ou hospedar uma partida e chamar amigos pela
mesma rede (LAN) ou pelo Radmin VPN. Bots completam os times.

Controles:
  W A S D        mover            Mouse        mirar
  Clique         atirar           R            recarregar
  1 / 2          pistola / fuzil  Roda mouse   trocar arma
  Tab (segurar)  placar           Setas <- ->  girar (alternativa ao mouse)
  Shift          correr (não dá para atirar correndo)   Espaço   pular
  Botão direito  mirar na mira (zoom, mais preciso, mais lento)
  C ou Ctrl      deslizar (só correndo; dá para atirar deslizando, pulo cancela)
  Mouse p/ cima/baixo  olhar vertical (tiro na cabeça = dano x2,5)
  Escadas levam ao 2º andar; blocos baixos (caixotes, carros) dá para pular em cima
  F11            tela cheia (também há a opção no menu)
  Esc            pausar e soltar o mouse (clique na tela para voltar)

Rede:
  Host:   menu -> "HOSPEDAR NA REDE". Passe seu IP (LAN ou Radmin) e a porta aos amigos.
          Libere o Python / a porta (TCP) no firewall do Windows se pedir.
  Amigos: menu -> digitar o IP do host + porta -> "ENTRAR".
"""

import gc
import json
import math
import queue
import random
import socket
import sys
import threading
import time
import tkinter as tk
from collections import deque

# ============================================================ configuração
LARG, ALT = 960, 540
COL = 4                       # largura (px) de cada coluna do raycaster
NCOL = LARG // COL
FOV = math.radians(66)
TAN = math.tan(FOV / 2)
CAMX = [2.0 * i / NCOL - 1.0 for i in range(NCOL)]

RAIO = 0.25                   # raio de colisão dos personagens (em células)
RAIO_HIT = 0.30
HS_MULT = 2.5                 # multiplicador de tiro na cabeça
VEL_JOGADOR = 3.4             # células/s
SENS = 0.0025                 # rad por pixel do mouse
TEMPO_ROUND = 100
VITORIAS = 7

VERSAO = 2                    # versão do protocolo de rede
PORTA_PADRAO = 5555
TICK_REDE = 1.0 / 30.0        # envios por segundo (snapshots e entradas)

NOMES_CT = ["Alpha", "Bravo", "Charlie", "Delta"]
NOMES_T = ["Viper", "Cobra", "Raven", "Wolf", "Hawk"]

ARMAS = [
    dict(nome="USP .45", dano=30, cd=0.26, mag=12, reserva=48, auto=False,
         espalha=0.010, recuo=0.012, rel=1.3, comp=140),
    dict(nome="AK-47", dano=24, cd=0.10, mag=30, reserva=90, auto=True,
         espalha=0.018, recuo=0.010, rel=2.0, comp=210),
]

DIFIC = {
    "Fácil":   dict(reacao=0.75, erro=0.080, giro=3.2, dano=7,  vel=2.1, cd=0.16),
    "Normal":  dict(reacao=0.45, erro=0.050, giro=5.0, dano=10, vel=2.6, cd=0.13),
    "Difícil": dict(reacao=0.25, erro=0.030, giro=7.5, dano=14, vel=3.0, cd=0.10),
}

# ============================================================ mapa
MW, MH = 48, 32
STEP = 0.27       # maior degrau que se sobe andando (os degraus das escadas têm 0,25)

# tipo -> (cor, altura do topo). Chão livre = '.'. Blocos baixos servem de cobertura e dá
# para pular em cima; '=' (deck) + degraus a/b/c formam o 2º andar (piso a 1,0).
TIPOS = {
    "1": ((165, 165, 172), 3.0),   # muro externo
    "4": ((132, 134, 140), 2.4),   # parede de blocos de concreto
    "7": ((150, 104, 60), 2.4),    # parede de madeira
    "k": ((178, 178, 184), 1.4),   # mureta alta de concreto
    "q": ((132, 134, 140), 1.4),   # janela / parapeito (blocos)
    "w": ((150, 104, 60), 1.4),    # janela / guarda-corpo (madeira)
    "2": ((176, 118, 62), 0.45),   # caixotes e sacos de areia
    "x": ((160, 106, 56), 0.9),    # caixotes empilhados
    "8": ((92, 102, 92), 0.6),     # carcaça de carro
    "6": ((160, 56, 48), 1.3),     # contêiner vermelho
    "3": ((64, 110, 176), 1.3),    # contêiner azul
    "=": ((118, 106, 92), 1.0),    # piso do 2º andar
    "a": ((142, 108, 70), 0.25),   # degraus
    "b": ((142, 108, 70), 0.5),
    "c": ((142, 108, 70), 0.75),
}
CHAOS = "=abc"                     # andáveis acima do chão


def construir_mapa():
    """Inspirado no Shoot House: muro externo com recuos de spawn, pátio murado com portões,
    beco entre paredes de bloco, contêineres, carcaças de carro, torre de madeira e prédio
    de blocos com 2º andar ligados por uma passarela. A metade de cima é copiada girada 180°
    para a de baixo, então o mapa é justo para os dois times."""
    g = [["1"] * MW for _ in range(MH)]

    def ret(x, y, w, h, t):
        for yy in range(y, y + h):
            for xx in range(x, x + w):
                g[yy][xx] = t

    def rot(x, y, w, h, t):
        ret(x, y, w, h, t)
        ret(MW - x - w, MH - y - h, w, h, t)

    ret(4, 1, 40, 30, ".")                         # pátio principal
    ret(1, 12, 3, 8, "."); ret(44, 12, 3, 8, ".")  # recuos de spawn

    # ---- pátio murado com portões (como o da foto), caixotes no meio
    rot(6, 2, 9, 1, "k"); rot(6, 3, 1, 6, "k")
    rot(14, 3, 1, 2, "k"); rot(14, 7, 1, 2, "k")           # portão leste: y5..6
    rot(6, 9, 3, 1, "k"); rot(11, 9, 4, 1, "k")            # portão sul: x9..10
    rot(9, 5, 2, 1, "x"); rot(8, 7, 1, 1, "2"); rot(12, 3, 1, 1, "2")

    # ---- beco entre paredes de bloco (corredor estreito da foto)
    rot(16, 3, 1, 4, "4"); rot(16, 7, 1, 2, "q"); rot(16, 9, 1, 5, "4")
    rot(19, 3, 1, 6, "4"); rot(19, 11, 1, 3, "4")          # porta lateral: y9..10
    rot(17, 11, 1, 1, "2")

    # ---- torre de madeira com 2º andar (escada pelo sul, passarela pelo leste)
    rot(20, 2, 8, 1, "7"); rot(20, 3, 1, 1, "7"); rot(27, 3, 1, 1, "7")
    rot(21, 3, 6, 4, "=")                                  # piso x21..26, y3..6
    rot(20, 4, 1, 2, "w"); rot(27, 4, 1, 1, "w"); rot(27, 5, 1, 1, "=")
    rot(20, 6, 1, 2, "7"); rot(27, 6, 1, 2, "7")
    rot(21, 7, 2, 1, "7"); rot(25, 7, 2, 1, "7"); rot(23, 7, 2, 1, "=")
    rot(22, 8, 1, 3, "w"); rot(25, 8, 1, 3, "w")           # guarda-corpos da escada
    rot(23, 8, 2, 1, "c"); rot(23, 9, 2, 1, "b"); rot(23, 10, 2, 1, "a")

    # ---- passarela elevada ligando a torre ao prédio de blocos
    rot(28, 4, 5, 2, "="); rot(28, 3, 5, 1, "w"); rot(28, 6, 5, 1, "w")

    # ---- prédio de blocos com 2º andar (janelas p/ o pátio, escada pelo sul)
    rot(33, 2, 9, 1, "4"); rot(33, 3, 1, 1, "4"); rot(41, 3, 1, 6, "4")
    rot(34, 3, 7, 5, "=")                                  # piso x34..40, y3..7
    rot(33, 4, 1, 2, "=")                                  # porta da passarela
    rot(33, 6, 1, 2, "q")
    rot(33, 8, 3, 1, "q"); rot(36, 8, 2, 1, "="); rot(38, 8, 3, 1, "q")
    rot(38, 5, 3, 1, "4"); rot(35, 5, 1, 1, "q")           # divisória e pilar de cobertura
    rot(35, 9, 1, 3, "w"); rot(38, 9, 1, 3, "w")
    rot(36, 9, 2, 1, "c"); rot(36, 10, 2, 1, "b"); rot(36, 11, 2, 1, "a")

    # ---- contêineres, carros, caixotes, barreiras
    rot(8, 13, 1, 3, "3"); rot(10, 11, 3, 1, "6")
    rot(12, 14, 2, 1, "8"); rot(15, 12, 1, 1, "2")
    rot(22, 14, 3, 2, "x"); rot(26, 12, 2, 1, "x")         # "carcaça de helicóptero" central
    rot(30, 9, 3, 1, "6"); rot(29, 12, 1, 3, "2")
    rot(34, 14, 2, 1, "8"); rot(39, 11, 1, 2, "x"); rot(41, 12, 2, 1, "2")
    return ["".join(l) for l in g]


GRADE = construir_mapa()
TOPS = [[(TIPOS[c][1] if c != "." else 0.0) for c in linha] for linha in GRADE]
ANDA = [[(c == "." or c in CHAOS) for c in linha] for linha in GRADE]
LIVRES = [(x, y) for y in range(MH) for x in range(MW) if ANDA[y][x]]
SPAWNS = {
    0: [(x + 0.5, y + 0.5) for x in range(1, 4) for y in range(12, 20)],
    1: [(x + 0.5, y + 0.5) for x in range(MW - 4, MW - 1) for y in range(12, 20)],
}

# paleta de paredes com vários níveis de sombra (neblina)
NSH = 32


def hexcor(r, g, b, f=1.0):
    return "#%02x%02x%02x" % (int(r * f), int(g * f), int(b * f))


PAL = {t: [hexcor(*rgb, (i + 1) / NSH) for i in range(NSH)] for t, (rgb, _) in TIPOS.items()}
TMAX = 2.35       # paredes dessa altura (ou mais) tapam tudo que está atrás


# ============================================================ geometria
def norm(a):
    return (a + math.pi) % (2 * math.pi) - math.pi


def _dda(px, py, rdx, rdy):
    mx, my = int(px), int(py)
    ddx = abs(1.0 / rdx) if rdx else 1e30
    ddy = abs(1.0 / rdy) if rdy else 1e30
    if rdx < 0:
        sx, sdx = -1, (px - mx) * ddx
    else:
        sx, sdx = 1, (mx + 1 - px) * ddx
    if rdy < 0:
        sy, sdy = -1, (py - my) * ddy
    else:
        sy, sdy = 1, (my + 1 - py) * ddy
    return mx, my, ddx, ddy, sx, sy, sdx, sdy


def segmentos(px, py, rdx, rdy, eye, K, hor, nmax=4, _T=TOPS, _G=GRADE):
    """Raio com altura (DDA). Devolve de perto p/ longe as faces visíveis
    [(t, tipo, lado, y0, y1, fr)], já recortadas pelo que está na frente: dá para ver
    por cima de blocos baixos, subir degraus, ver o andar de cima, etc."""
    mx, my, ddx, ddy, sx, sy, sdx, sdy = _dda(px, py, rdx, rdy)
    antes = _T[my][mx]
    corte = float(ALT)
    out = []
    while True:
        if sdx < sdy:
            t = sdx; sdx += ddx; mx += sx; lado = 0
        else:
            t = sdy; sdy += ddy; my += sy; lado = 1
        topo = _T[my][mx]
        if topo > antes:
            if t < 0.05:
                t = 0.05
            lh = K / t
            ya = hor - (topo - eye) * lh
            if ya < corte:
                yb = hor + (eye - antes) * lh
                if yb > corte:
                    yb = corte
                if yb > ya:
                    w = (py + t * rdy) if lado == 0 else (px + t * rdx)
                    out.append((t, _G[my][mx], lado, ya, yb, w - int(w)))
                    corte = ya
                    if corte <= 0 or len(out) >= nmax:
                        break
            if topo >= TMAX:
                break
        antes = topo
    return out


def raio_h(px, py, dx, dy, z0, slope, _T=TOPS):
    """Distância até o primeiro bloco que o tiro (saindo à altura z0 com inclinação
    'slope') não consegue sobrevoar."""
    mx, my, ddx, ddy, sx, sy, sdx, sdy = _dda(px, py, dx, dy)
    while True:
        if sdx < sdy:
            t = sdx; sdx += ddx; mx += sx
        else:
            t = sdy; sdy += ddy; my += sy
        if not (0 <= mx < MW and 0 <= my < MH):
            return t
        if _T[my][mx] > z0 + slope * t:
            return t


def ve(x1, y1, x2, y2, z1=0.5, z2=0.5, _T=TOPS):
    """Linha de visão entre dois olhos (z1, z2 = alturas absolutas dos olhos)."""
    dx, dy = x2 - x1, y2 - y1
    d = math.hypot(dx, dy)
    if d < 1e-6:
        return True
    mx, my, ddx, ddy, sx, sy, sdx, sdy = _dda(x1, y1, dx / d, dy / d)
    k = (z2 - z1) / d
    while True:
        if sdx < sdy:
            t = sdx; sdx += ddx; mx += sx
        else:
            t = sdy; sdy += ddy; my += sy
        if t >= d:
            return True
        if _T[my][mx] > z1 + k * t:
            return False


def livre(x, y, z=0.0, _T=TOPS):
    """O corpo (com os pés a altura z) cabe em (x, y)? Degraus até STEP são vencidos."""
    r, lim = RAIO, z + STEP
    for cy in (int(y - r), int(y + r)):
        linha = _T[cy]
        for cx in (int(x - r), int(x + r)):
            if linha[cx] > lim:
                return False
    return True


def chao_em(x, y, z, _T=TOPS):
    """Altura do piso sob o corpo: o topo mais alto, entre as células pisadas, que dá para alcançar."""
    r, lim, melhor = RAIO, z + STEP, 0.0
    for cy in (int(y - r), int(y + r)):
        linha = _T[cy]
        for cx in (int(x - r), int(x + r)):
            t = linha[cx]
            if melhor < t <= lim:
                melhor = t
    return melhor


def mover(a, dx, dy):
    z = a.pz
    if livre(a.x + dx, a.y, z):
        a.x += dx
    if livre(a.x, a.y + dy, z):
        a.y += dy


def raio_circulo(ox, oy, dx, dy, cx, cy, r):
    fx, fy = cx - ox, cy - oy
    t = fx * dx + fy * dy
    if t < 0:
        return None
    d2 = fx * fx + fy * fy - t * t
    if d2 > r * r:
        return None
    return t - math.sqrt(r * r - d2)


def bfs(ini, fim):
    """Caminho (centros de células) entre duas células andáveis (sobe escadas), ou [] se não há."""
    if ini == fim:
        return []
    prev = {ini: None}
    fila = deque([ini])
    while fila:
        c = fila.popleft()
        if c == fim:
            break
        x, y = c
        tc = TOPS[y][x]
        for n in ((x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1)):
            if n not in prev and ANDA[n[1]][n[0]] and abs(TOPS[n[1]][n[0]] - tc) <= STEP:
                prev[n] = c
                fila.append(n)
    if fim not in prev:
        return []
    cam, c = [], fim
    while c != ini:
        cam.append((c[0] + 0.5, c[1] + 0.5))
        c = prev[c]
    cam.reverse()
    return cam


# ---- navegação dos bots: campos de distância em cache (1 BFS por destino, usado por todos)
_CAMPOS = {}
_VIZ = ((1, 0), (-1, 0), (0, 1), (0, -1))


def ancla(c):
    """Célula andável mais próxima de c (se c for um bloco/parede), ou None."""
    x, y = c
    if 0 <= x < MW and 0 <= y < MH and ANDA[y][x]:
        return c
    for r in range(1, 5):
        for dy in range(-r, r + 1):
            for dx in range(-r, r + 1):
                if max(abs(dx), abs(dy)) == r:
                    nx, ny = x + dx, y + dy
                    if 0 <= nx < MW and 0 <= ny < MH and ANDA[ny][nx]:
                        return (nx, ny)
    return None


def campo(meta):
    d = _CAMPOS.get(meta)
    if d is None:
        d = {meta: 0}
        fila = deque([meta])
        while fila:
            c = fila.popleft()
            x, y = c
            tc, dc = TOPS[y][x], d[c] + 1
            for ox, oy in _VIZ:
                n = (x + ox, y + oy)
                if n not in d and ANDA[n[1]][n[0]] and abs(TOPS[n[1]][n[0]] - tc) <= STEP:
                    d[n] = dc
                    fila.append(n)
        if len(_CAMPOS) > 220:
            _CAMPOS.pop(next(iter(_CAMPOS)))
        _CAMPOS[meta] = d
    return d


def siguiente(cel, meta):
    """(próxima célula, chegou?) para ir de cel até meta seguindo o campo de distância."""
    d = campo(meta)
    dc = d.get(cel)
    if dc is None:
        a = ancla(cel)
        return (a, False) if a and a != cel else (None, True)
    if dc == 0:
        return None, True
    x, y = cel
    tc = TOPS[y][x]
    best, bd = None, dc
    for ox, oy in _VIZ:
        n = (x + ox, y + oy)
        v = d.get(n)
        if v is not None and v < bd and abs(TOPS[n[1]][n[0]] - tc) <= STEP:
            best, bd = n, v
    return best, best is None


def _waypoints(n=46, sep=4.4):
    """Pontos de interesse espalhados pelo mapa (inclusive no 2º andar), por amostragem do mais distante."""
    cand = []
    for (x, y) in LIVRES:
        if TOPS[y][x] not in (0.0, 1.0) or not livre(x + 0.5, y + 0.5, TOPS[y][x]):
            continue
        abertos = sum(1 for dx in (-1, 0, 1) for dy in (-1, 0, 1)
                      if 0 <= x + dx < MW and 0 <= y + dy < MH and ANDA[y + dy][x + dx])
        if abertos >= 6:
            cand.append((x, y))
    cx, cy = MW / 2, MH / 2
    pts = [min(cand, key=lambda c: (c[0] - cx) ** 2 + (c[1] - cy) ** 2)]
    mind = [math.hypot(c[0] - pts[0][0], c[1] - pts[0][1]) for c in cand]
    while len(pts) < n:
        i = max(range(len(cand)), key=lambda k: mind[k])
        if mind[i] < sep:
            break
        p = cand[i]
        pts.append(p)
        for k, c in enumerate(cand):
            d = math.hypot(c[0] - p[0], c[1] - p[1])
            if d < mind[k]:
                mind[k] = d
    return _cobrir(pts)


def _cobrir(pts, alcance=11):
    """Acrescenta waypoints até toda célula (chão ou 2º andar) ser vista de algum deles."""
    cels = [c for c in LIVRES if TOPS[c[1]][c[0]] in (0.0, 1.0) and (c[0] + c[1]) % 2 == 0]

    def visto(c, p):
        return (abs(p[0] - c[0]) <= alcance and abs(p[1] - c[1]) <= alcance and
                ve(p[0] + 0.5, p[1] + 0.5, c[0] + 0.5, c[1] + 0.5,
                   TOPS[p[1]][p[0]] + 0.5, TOPS[c[1]][c[0]] + 0.5))

    sem = [c for c in cels if not any(visto(c, p) for p in pts)]
    while sem:
        c = sem[0]
        if livre(c[0] + 0.5, c[1] + 0.5, TOPS[c[1]][c[0]]):
            pts.append(c)
            sem = [k for k in sem if k != c and not visto(k, c)]
        else:
            sem.pop(0)
    return pts


WPS = _waypoints()
PAPEL_LADO = {"rush": 0.30, "normal": 0.13, "flank": 0.08, "hold": -0.05}


VEL_CORRIDA, VEL_MIRA = 1.55, 0.6      # multiplicadores de velocidade
GRAV, PULO = 9.5, 2.9                  # pulo: ~0,44 de altura (sobe em caixotes e carros)
PIT_MAX = 0.45
SENS_Y = 0.0018                        # inclinação (slope) por pixel do mouse na vertical
SLIDE_T, SLIDE_CD = 0.85, 0.9          # duração e recarga do deslize


def _vertical(j, dt, quer_pulo):
    """Gravidade, pulo e queda. pz é a altura ABSOLUTA dos pés (0 = chão, 1 = 2º andar)."""
    chao = chao_em(j.x, j.y, j.pz)
    if j.pz <= chao + 1e-3 and j.vz <= 0:
        j.pz, j.vz, j.noar = chao, 0.0, False
        if not quer_pulo:
            return
        j.vz = PULO
    j.noar = True
    j.vz -= GRAV * dt
    j.pz += j.vz * dt
    chao = chao_em(j.x, j.y, j.pz)
    if j.pz <= chao and j.vz <= 0:
        j.pz, j.vz, j.noar = chao, 0.0, False


def mover_jogador(j, dt, ent):
    """WASD + correr + pular + mirar + deslizar + degraus/queda. Usado pelo host (local)
    e pelo cliente (previsão)."""
    f, s = ent["mv"]
    n = math.hypot(f, s)
    pular = bool(ent.get("pular"))
    chao = chao_em(j.x, j.y, j.pz)
    no_chao = j.pz <= chao + 1e-3 and j.vz <= 0
    if j.slide_cd > 0:
        j.slide_cd -= dt

    # ---- deslize: só começa correndo; mantém a direção; pulo cancela
    if j.deslizando and pular and no_chao:
        j.deslizando, j.slide_cd = False, 0.4
    elif (not j.deslizando and ent.get("deslizar") and j.correndo and no_chao
            and j.slide_cd <= 0 and n):
        c, si = math.cos(j.ang), math.sin(j.ang)
        fn, sn = f / n, s / n
        j.sdx, j.sdy = c * fn - si * sn, si * fn + c * sn
        j.deslizando, j.slide_t = True, SLIDE_T
    if j.deslizando:
        j.slide_t -= dt
        k = max(0.0, j.slide_t / SLIDE_T)
        vel = VEL_JOGADOR * (0.55 + 1.5 * k * k)
        mover(j, j.sdx * vel * dt, j.sdy * vel * dt)
        j.andando, j.correndo, j.mira = True, False, False
        j.stam_t = 0.4
        if j.slide_t <= 0:
            j.deslizando, j.slide_cd = False, SLIDE_CD
        _vertical(j, dt, False)
        return

    j.andando = n > 0
    quer_mira = bool(ent.get("mirar"))
    quer_corre = bool(ent.get("correr")) and f > 0 and not quer_mira and not j.exausto
    vel = VEL_JOGADOR
    if quer_corre and j.stam > 0:
        j.correndo = True
        vel *= VEL_CORRIDA
        j.stam = max(0.0, j.stam - 26.0 * dt)
        j.stam_t = 0.7
        if j.stam <= 0:
            j.exausto = True
    else:
        j.correndo = False
        if j.stam_t > 0:
            j.stam_t -= dt
        else:
            j.stam = min(100.0, j.stam + 24.0 * dt)
            if j.stam > 30:
                j.exausto = False
    j.mira = quer_mira and not j.correndo
    if j.mira:
        vel *= VEL_MIRA
    if n:
        f, s = f / n, s / n
        c, si = math.cos(j.ang), math.sin(j.ang)
        mover(j, (c * f - si * s) * vel * dt, (si * f + c * s) * vel * dt)
    _vertical(j, dt, pular)


# ============================================================ lógica do jogo
def ent_remota():
    return {"x": None, "y": None, "ang": 0.0, "and": False, "fogo": False,
            "clique": False, "rec": False, "arma": None, "mv": (0, 0),
            "pz": 0.0, "pit": 0.0, "corre": False, "mira": False, "slide": False}


class Ator:
    def __init__(self, nome, time_, jogador=False):
        self.nome, self.time, self.jogador = nome, time_, jogador
        self.id = 0
        self.remoto = False          # humano controlado por outro computador
        self.ent = None              # última entrada recebida (só remotos)
        self.k = self.m = 0          # abates / mortes
        self.tx = self.ty = self.tang = 0.0   # alvo de interpolação (cliente)
        self.reset(1.5, 1.5, 0.0)

    def reset(self, x, y, ang):
        self.x, self.y, self.ang = x, y, ang
        self.hp, self.vivo = 100, True
        self.arma = 1
        self.mags = [a["mag"] for a in ARMAS]
        self.res = [a["reserva"] for a in ARMAS]
        self.cd = self.rel = self.flash = self.imp = self.hit = 0.0
        self.andando = False
        self.pz = self.vz = 0.0          # altura do pulo / velocidade vertical
        self.pit = 0.0                   # olhar vertical (inclinação do tiro; + = para cima)
        self.stam, self.stam_t, self.exausto = 100.0, 0.0, False
        self.correndo = self.corria = self.mira = False
        self.deslizando, self.slide_t, self.slide_cd = False, 0.0, 0.0
        self.sdx = self.sdy = 0.0
        self.noar = False
        # estado da IA
        self.alvo = None
        self.reacao = 0.0
        self.rajada = random.randint(3, 6)
        self.pausa = 0.0
        self.caminho = []
        self.repath = 0.0
        self.goal, self.goal_tipo, self.wp_i = None, "", -1     # destino atual e seu tipo
        self.hold, self.hold_ang = 0.0, ang                      # parado olhando em volta
        self.scan_t, self.scan_ph = random.uniform(0, 6), random.uniform(0, 6.28)
        self.reav, self.ouviu = random.uniform(0.3, 1.5), -9.0
        self.stuck_t, self.pos_ref = 0.0, (x, y)
        self.papel = random.choices(("rush", "normal", "flank", "hold"), (2, 5, 2, 1))[0]
        self.estrafe, self.estrafe_t = 0, 0.0
        self.ult = None
        self.sem_ver = 99.0
        self.alerta = 0.0
        self.perc = random.uniform(0.0, 0.12)


class Mundo:
    """Simulação completa. No multiplayer só o HOST roda isto."""
    pode_reiniciar = True

    def __init__(self, aliados, inimigos, dif, rede=False):
        self.dif = DIFIC[dif]
        self.auto = rede              # reinicia a partida sozinho (modo rede)
        self._id = 0
        self.atores, self.eventos, self.rede_ev = [], [], []
        self.jogador = self._novo("Você", 0, True)
        for i in range(aliados):
            n = NOMES_CT[i % len(NOMES_CT)]
            self._novo(n if i < len(NOMES_CT) else f"{n}{i // len(NOMES_CT) + 1}", 0)
        for i in range(inimigos):
            n = NOMES_T[i % len(NOMES_T)]
            self._novo(n if i < len(NOMES_T) else f"{n}{i // len(NOMES_T) + 1}", 1)
        self.res = None
        self.t_partida = 0.0
        self.relogio, self._t_purga = 0.0, 1.0
        self.vis_wp, self.intel = [{}, {}], [{}, {}]
        self.reiniciar()

    def _novo(self, nome, time_, jogador=False):
        a = Ator(nome, time_, jogador)
        a.id = self._id
        self._id += 1
        self.atores.append(a)
        return a

    # ---------------------------------------------------------- humanos remotos
    def adicionar_humano(self, nome):
        usados = {a.nome for a in self.atores}
        base, n = nome, 2
        while nome in usados:
            nome = f"{base}{n}"
            n += 1
        tot = [0, 0]
        for a in self.atores:
            tot[a.time] += 1
        t = 0 if tot[0] <= tot[1] else 1
        a = self._novo(nome, t, True)
        a.remoto, a.ent = True, ent_remota()
        x, y = random.choice(SPAWNS[t])
        a.reset(x, y, 0.0 if t == 0 else math.pi)
        if self.fase == "jogando":       # entrou no meio da rodada: espera a próxima
            a.vivo, a.hp = False, 0
        return a

    def remover(self, a):
        if a in self.atores and a is not self.jogador:
            self.atores.remove(a)

    # ---------------------------------------------------------- rodadas
    def reiniciar(self):
        self.placar = [0, 0]
        self.rodada = 0
        for a in self.atores:
            a.k = a.m = 0
        self.nova_rodada()

    def nova_rodada(self):
        self.rodada += 1
        self.tempo = TEMPO_ROUND
        self.res = None
        # cada time começa sem saber onde o outro está; waypoints "velhos" em tempos variados
        self.vis_wp = [{i: self.relogio - random.uniform(0, 14) for i in range(len(WPS))} for _ in (0, 1)]
        self.intel = [{}, {}]
        for t in (0, 1):
            membros = [a for a in self.atores if a.time == t]
            base = SPAWNS[t]
            pontos = random.sample(base, min(len(membros), len(base)))
            while len(pontos) < len(membros):
                pontos.append(random.choice(base))
            for a, (x, y) in zip(membros, pontos):
                a.reset(x, y, 0.0 if t == 0 else math.pi)
                if a.remoto:
                    a.ent["x"] = a.ent["y"] = None
        self.fase = "congelado"       # congelado -> jogando -> fim -> (partida)
        self.t_fase = 2.5

    def emit(self, tipo, a, b=None, extra=0):
        self.eventos.append((tipo, a, b, extra))
        self.rede_ev.append((tipo, a.id, b.id if b else -1, extra))

    # ---------------------------------------------------------- passo
    def passo(self, dt, ent):
        if self.fase == "congelado":
            self.t_fase -= dt
            for a in self.atores:
                if a.remoto:
                    a.ent["clique"], a.ent["arma"] = False, None
            if self.t_fase <= 0:
                self.fase = "jogando"
            return
        if self.fase == "fim":
            self.t_fase -= dt
            if self.t_fase <= 0:
                if max(self.placar) >= VITORIAS:
                    self.fase = "partida"
                    self.t_partida = 15.0
                else:
                    self.nova_rodada()
            return
        if self.fase == "partida":
            if self.auto:
                self.t_partida -= dt
                if self.t_partida <= 0:
                    self.reiniciar()
            return

        self.tempo -= dt
        self.relogio += dt
        self._t_purga -= dt
        if self._t_purga <= 0:
            self._t_purga = 1.0
            self.purgar_intel()
        for a in self.atores:
            a.cd = max(0.0, a.cd - dt)
            a.flash = max(0.0, a.flash - dt)
            a.imp = max(0.0, a.imp - 0.15 * dt)
        self.atualiza_humano(self.jogador, dt, ent)
        for b in list(self.atores):
            if b.remoto:
                self.atualiza_humano(b, dt, b.ent)
            elif not b.jogador and b.vivo:
                self.ia(b, dt)
                b.pz = chao_em(b.x, b.y, b.pz)
        self.separar()
        self.checar_fim()

    def checar_fim(self):
        vivos = [0, 0]
        for a in self.atores:
            if a.vivo:
                vivos[a.time] += 1
        if vivos[0] and vivos[1] and self.tempo > 0:
            return
        if vivos[0] and not vivos[1]:
            self.placar[0] += 1
            self.res = 0
        elif vivos[1] and not vivos[0]:
            self.placar[1] += 1
            self.res = 1
        elif not vivos[0] and not vivos[1]:
            self.res = "empate"
        else:
            self.res = "tempo"
        self.fase, self.t_fase = "fim", 4.0

    # ---------------------------------------------------------- humanos
    def atualiza_humano(self, j, dt, ent):
        if not j.vivo:
            j.correndo = j.mira = j.deslizando = False
            _vertical(j, dt, False)
            if j.remoto:
                ent["clique"], ent["arma"] = False, None
            return
        if j.remoto:
            nx, ny = ent["x"], ent["y"]
            if nx is not None:
                # posição vem do cliente; aceita só se válida (anti-teleporte básico)
                pz = max(0.0, min(2.6, ent["pz"]))
                if livre(nx, ny, pz) and math.hypot(nx - j.x, ny - j.y) < 4.0:
                    j.x, j.y = nx, ny
                j.pz = pz
                j.ang = ent["ang"]
                j.andando = ent["and"]
                j.pit = max(-0.5, min(0.5, ent["pit"]))
                j.correndo, j.mira = ent["corre"], ent["mira"]
                j.deslizando = ent["slide"]
        else:
            mover_jogador(j, dt, ent)

        if j.rel > 0:
            j.rel -= dt
            if j.rel <= 0:
                j.rel = 0.0
                ar = ARMAS[j.arma]
                pega = min(ar["mag"] - j.mags[j.arma], j.res[j.arma])
                j.mags[j.arma] += pega
                j.res[j.arma] -= pega
        elif ent["arma"] is not None and ent["arma"] != j.arma:
            j.arma = ent["arma"]
            j.cd = 0.35
        if ent["rec"]:
            self.iniciar_recarga(j)

        if j.corria and not j.correndo and not j.deslizando:
            j.cd = max(j.cd, 0.18)          # tempo para "levantar" a arma depois de correr
        j.corria = j.correndo

        ar = ARMAS[j.arma]
        quer = ent["fogo"] if ar["auto"] else ent["clique"]
        if quer and j.rel == 0 and j.cd <= 0 and not j.correndo:
            if j.mags[j.arma] > 0:
                j.mags[j.arma] -= 1
                j.cd = ar["cd"]
                j.flash = 0.06
                esp = ar["espalha"] + j.imp + (0.012 if j.andando else 0.0)
                if j.noar:
                    esp += 0.03                 # no ar a mira abre
                if j.deslizando:
                    esp += 0.02
                if j.mira:
                    esp *= 0.35                 # mirando: bem mais preciso
                j.imp = min(0.05, j.imp + ar["recuo"] * (0.5 if j.mira else 1.0))
                self.disparo(j, j.ang + random.uniform(-esp, esp), ar["dano"],
                             j.pit + random.uniform(-esp, esp))
            else:
                self.iniciar_recarga(j)
        if j.remoto:
            ent["clique"], ent["arma"] = False, None

    def iniciar_recarga(self, j):
        ar = ARMAS[j.arma]
        if j.rel == 0 and j.mags[j.arma] < ar["mag"] and j.res[j.arma] > 0:
            j.rel = ar["rel"]

    # ---------------------------------------------------------- tiro
    def disparo(self, a, ang, dano, slope=0.0):
        """Tiro com altura: sai do olho (pz+0,5; deslizando pz+0,28) e sobe/desce com 'slope';
        blocos baixos podem ser sobrevoados. O alvo ocupa de pz a pz+0,86 (deslizando: 0,52);
        a faixa de cima (0,26) é a cabeça: dano x HS_MULT para qualquer atirador."""
        self.emit("tiro", a)
        self.ouvir(a)
        dx, dy = math.cos(ang), math.sin(ang)
        olho = a.pz + (0.28 if a.deslizando else 0.5)
        tm = raio_h(a.x, a.y, dx, dy, olho, slope)
        alvo, cabeca = None, False
        for o in self.atores:
            if o is a or not o.vivo or o.time == a.time:
                continue
            t = raio_circulo(a.x, a.y, dx, dy, o.x, o.y, RAIO_HIT)
            if t is not None and t < tm:
                hb = olho + slope * t
                alt = 0.52 if o.deslizando else 0.86
                if o.pz - 0.02 <= hb <= o.pz + alt:
                    tm, alvo = t, o
                    cabeca = hb > o.pz + alt - 0.26
        if alvo:
            if cabeca:
                dano = int(dano * HS_MULT)
            alvo.hp -= dano
            alvo.alerta = 3.0
            alvo.ult = (a.x, a.y)
            self.emit("dano", a, alvo, int(cabeca))
            if alvo.hp <= 0:
                alvo.hp, alvo.vivo = 0, False
                a.k += 1
                alvo.m += 1
                self.emit("morte", a, alvo, int(cabeca))
        return alvo

    # ---------------------------------------------------------- IA dos bots
    def ia(self, b, dt):
        D = self.dif
        b.alerta = max(0.0, b.alerta - dt)
        b.sem_ver += dt
        b.perc -= dt
        if b.perc <= 0:
            # percepção só ~10x/s por bot (e escalonada): os raios de visão são caros
            b.perc = random.uniform(0.08, 0.14)
            alvo, melhor = None, 99.0
            for o in self.atores:
                if not o.vivo or o.time == b.time:
                    continue
                dx, dy = o.x - b.x, o.y - b.y
                d = math.hypot(dx, dy)
                if d >= melhor:
                    continue
                if abs(norm(math.atan2(dy, dx) - b.ang)) > 1.15 and d > 2.5 and b.alerta <= 0:
                    continue  # fora do campo de visão
                if ve(b.x, b.y, o.x, o.y, b.pz + 0.5, o.pz + (0.3 if o.deslizando else 0.5)):
                    alvo, melhor = o, d
            if alvo:
                if b.alvo is not alvo:
                    b.alvo, b.reacao = alvo, D["reacao"]
                b.ult, b.sem_ver = (alvo.x, alvo.y), 0.0
                self.intel[b.time][alvo.id] = (alvo.x, alvo.y, self.relogio)   # avisa o time
        elif b.alvo and b.sem_ver < 0.3:
            b.ult = (b.alvo.x, b.alvo.y)      # acompanha o alvo entre as percepções
        if b.alvo and (not b.alvo.vivo or b.sem_ver > 0.3):
            if not b.alvo.vivo:
                b.ult = None
            b.alvo, b.goal, b.hold = None, None, 0.0     # perdeu o alvo: vai investigar
        if b.alvo:
            self.ia_combate(b, dt)
        else:
            self.ia_mover(b, dt)

    def virar(self, b, desejado, dt):
        passo = self.dif["giro"] * dt
        dif = norm(desejado - b.ang)
        b.ang += max(-passo, min(passo, dif))
        return dif

    def ia_combate(self, b, dt):
        D = self.dif
        o = b.alvo
        dx, dy = o.x - b.x, o.y - b.y
        d = math.hypot(dx, dy)
        desej = math.atan2(dy, dx)
        dif = self.virar(b, desej, dt)

        b.reacao -= dt
        if b.reacao <= 0 and abs(dif) < 0.15:
            if b.pausa > 0:
                b.pausa -= dt
            elif b.cd <= 0:
                b.cd, b.flash = D["cd"], 0.07
                dalt = (o.pz + (0.26 if o.deslizando else 0.42)) - (b.pz + 0.5)
                self.disparo(b, b.ang + random.gauss(0, D["erro"]), D["dano"],
                             dalt / max(d, 0.3) + random.gauss(0, D["erro"] * 0.3))
                b.rajada -= 1
                if b.rajada <= 0:
                    b.rajada = random.randint(3, 6)
                    b.pausa = random.uniform(0.25, 0.8)

        b.estrafe_t -= dt
        if b.estrafe_t <= 0:
            b.estrafe = random.choice((-1, 0, 1))
            b.estrafe_t = random.uniform(0.4, 1.2)
        fwd = 1 if d > 10 else (-1 if d < 3.5 else 0)
        vx = -math.sin(desej) * b.estrafe + math.cos(desej) * fwd
        vy = math.cos(desej) * b.estrafe + math.sin(desej) * fwd
        n = math.hypot(vx, vy)
        if n:
            k = D["vel"] * 0.6 * dt / n
            mover(b, vx * k, vy * k)

    def ia_mover(self, b, dt):
        """Busca ativa: vai de waypoint em waypoint (mais 'velhos' / lado inimigo primeiro),
        investiga tiros ouvidos e avisos do time, para e olha em volta, varre a mira enquanto anda."""
        D = self.dif
        b.scan_t += dt
        if b.hold > 0:                                   # parado olhando em volta
            b.hold -= dt
            self.virar(b, b.hold_ang + math.sin(b.scan_t * 1.3 + b.scan_ph) * 1.5, dt)
            return
        b.reav -= dt
        if b.goal is not None and b.goal_tipo == "wp" and b.reav <= 0:
            b.reav = random.uniform(1.0, 2.2)
            alvo = self.melhor_intel(b)
            if alvo and random.random() < (0.35 if b.papel == "hold" else 0.9):
                self.definir(b, alvo, "intel")
        if b.goal is None:
            self.escolher(b)
            if b.goal is None:
                return
        # travou? (parede, colega no caminho) => escolhe outro destino
        b.stuck_t += dt
        if b.stuck_t >= 1.3:
            if math.hypot(b.x - b.pos_ref[0], b.y - b.pos_ref[1]) < 0.3:
                b.goal = None
                b.stuck_t, b.pos_ref = 0.0, (b.x, b.y)
                return
            b.stuck_t, b.pos_ref = 0.0, (b.x, b.y)
        nxt, chegou = siguiente((int(b.x), int(b.y)), b.goal)
        if chegou or nxt is None:
            self.chegou(b)
            return
        dx, dy = nxt[0] + 0.5 - b.x, nxt[1] + 0.5 - b.y
        d = math.hypot(dx, dy)
        if d > 1e-6:
            vel = D["vel"] * (1.12 if b.papel == "rush" else 1.0)
            mover(b, dx / d * vel * dt, dy / d * vel * dt)
            ang = math.atan2(dy, dx) + math.sin(b.scan_t * 1.7 + b.scan_ph) * 0.8   # varre a mira
            self.virar(b, ang, dt)

    def chegou(self, b):
        t = b.time
        if b.goal_tipo == "wp" and b.wp_i >= 0:
            self.vis_wp[t][b.wp_i] = self.relogio
        elif b.goal_tipo in ("intel", "investigar"):
            for k, (x, y, ts) in list(self.intel[t].items()):    # ninguém aqui: apaga o aviso
                if math.hypot(x - b.x, y - b.y) < 3.5:
                    del self.intel[t][k]
        if b.papel == "hold" and random.random() < 0.6:
            b.hold = random.uniform(3.0, 7.0)
        elif random.random() < 0.7:
            b.hold = random.uniform(0.5, 1.8)
        b.hold_ang = b.ang
        b.goal = None

    def definir(self, b, cel, tipo):
        a = ancla(cel)
        if a is None:
            return
        b.goal, b.goal_tipo = a, tipo
        b.stuck_t, b.pos_ref = 0.0, (b.x, b.y)
        campo(a)

    def melhor_intel(self, b):
        """Aviso recente do time mais próximo (célula) ou None."""
        melhor, bd = None, 1e9
        for (x, y, ts) in self.intel[b.time].values():
            if self.relogio - ts > 14.0:
                continue
            d = math.hypot(x - b.x, y - b.y)
            if 2.0 < d < bd:
                melhor, bd = (int(x), int(y)), d
        return melhor

    def escolher(self, b):
        t = b.time
        if b.ult and b.sem_ver < 10:                     # viu/ouviu alguém: vai conferir
            cel, b.ult = (int(b.ult[0]), int(b.ult[1])), None
            self.definir(b, cel, "investigar")
            if b.goal is not None:
                return
        alvo = self.melhor_intel(b)
        if alvo and random.random() < (0.4 if b.papel == "hold" else 0.85):
            self.definir(b, alvo, "intel")
            if b.goal is not None:
                return
        usados = {o.wp_i for o in self.atores
                  if o is not b and o.time == t and o.vivo and o.goal is not None and o.goal_tipo == "wp"}
        melhor, bs = None, -1e9
        for i in random.sample(range(len(WPS)), min(10, len(WPS))):
            if i == b.wp_i or i in usados:
                continue
            wx, wy = WPS[i]
            d = math.hypot(wx + 0.5 - b.x, wy + 0.5 - b.y)
            if d < 4.0:
                continue
            velho = min(40.0, self.relogio - self.vis_wp[t].get(i, 0.0))
            lado = (wx - MW / 2) * (1 if t == 0 else -1)          # + = lado do inimigo
            s = velho * 0.22 + lado * PAPEL_LADO[b.papel] - d * 0.05 + random.random() * 2.5
            if b.papel == "hold" and TOPS[wy][wx] >= 0.99:
                s += 5.0                                          # prefere o alto
            elif b.papel == "flank":
                s += abs(wy - MH / 2) * 0.15
            if s > bs:
                melhor, bs = i, s
        if melhor is None:
            melhor = random.randrange(len(WPS))
        b.wp_i = melhor
        self.definir(b, WPS[melhor], "wp")

    def ouvir(self, a):
        """Bots inimigos ouvem tiros num raio de ~20 células e vão investigar."""
        for b in self.atores:
            if b.jogador or b.remoto or not b.vivo or b.time == a.time or b.alvo:
                continue
            d = math.hypot(a.x - b.x, a.y - b.y)
            if d > 20.0 or random.random() > 0.95 - d * 0.025:
                continue
            b.ult, b.sem_ver = (a.x, a.y), 0.0
            b.alerta = max(b.alerta, 2.5)                # atenção 360 graus por um tempo
            if self.relogio - b.ouviu > 1.5:
                b.ouviu = self.relogio
                b.goal, b.hold = None, 0.0

    def purgar_intel(self):
        vivos = {x.id for x in self.atores if x.vivo}
        for t in (0, 1):
            for k, (x, y, ts) in list(self.intel[t].items()):
                if k not in vivos or self.relogio - ts > 20.0:
                    del self.intel[t][k]

    def separar(self):
        vivos = [a for a in self.atores if a.vivo]
        for i in range(len(vivos)):
            for k in range(i + 1, len(vivos)):
                a, b = vivos[i], vivos[k]
                dx, dy = b.x - a.x, b.y - a.y
                d = math.hypot(dx, dy)
                if 0 < d < 0.5:
                    p = (0.5 - d) / 2 / d
                    mover(a, -dx * p, -dy * p)
                    mover(b, dx * p, dy * p)

    # ---------------------------------------------------------- rede (host)
    def snapshot(self):
        a = [[x.id, x.time, round(x.x, 3), round(x.y, 3), round(x.ang, 3), x.hp, int(x.vivo),
              x.arma, round(x.rel, 2), x.mags[x.arma], x.res[x.arma], round(x.imp, 3),
              x.k, x.m, x.nome, int(x.andando), round(x.pz, 2), int(x.deslizando)]
             for x in self.atores]
        return {"t": "s", "f": self.fase, "tm": round(self.tempo, 1), "p": self.placar,
                "r": self.rodada, "v": self.res, "tp": round(self.t_partida, 1),
                "e": [list(e) for e in self.rede_ev], "a": a}


class MundoRemoto:
    """Espelho do mundo no cliente: só aplica snapshots do host e prevê o próprio movimento."""
    pode_reiniciar = False
    auto = True

    def __init__(self, meu_id):
        self.meu_id = meu_id
        self.jogador = Ator("Você", 0, True)
        self.jogador.id = meu_id
        self.por_id = {meu_id: self.jogador}
        self.atores = [self.jogador]
        self.eventos = []
        self.placar = [0, 0]
        self.rodada = 0
        self.tempo = 0.0
        self.fase = "congelado"
        self.res = None
        self.t_partida = 0.0

    def aplicar(self, s):
        self.fase, self.tempo, self.placar = s["f"], s["tm"], s["p"]
        self.rodada, self.res, self.t_partida = s["r"], s["v"], s["tp"]
        vistos = []
        for (i, time_, x, y, ang, hp, vivo, arma, rel, mag, res, imp, k, m, nome, and_, pz, desl) in s["a"]:
            a = self.por_id.get(i)
            novo = a is None
            if novo:
                a = Ator(nome, time_)
                a.id = i
                self.por_id[i] = a
                a.x, a.y, a.ang = x, y, ang
            a.nome, a.time = nome, time_
            a.hp, a.vivo, a.arma, a.rel = hp, bool(vivo), arma, rel
            a.mags[arma], a.res[arma], a.imp, a.k, a.m = mag, res, imp, k, m
            if a is self.jogador:
                # posição é do cliente; só obedece ao host em respawn / correção grande
                if s["f"] != "jogando" or not a.vivo or math.hypot(x - a.x, y - a.y) > 1.5:
                    a.x, a.y = x, y
                    a.pz, a.vz = pz, 0.0
            else:
                a.tx, a.ty, a.tang = x, y, ang
                a.andando = bool(and_)
                a.pz = pz
                a.deslizando = bool(desl)
            vistos.append(a)
        self.atores = vistos
        for a in list(self.por_id.values()):
            if a not in vistos:
                del self.por_id[a.id]
        for tipo, i1, i2, ex in s["e"]:
            a, b = self.por_id.get(i1), self.por_id.get(i2)
            if tipo == "tiro":
                if a:
                    a.flash = 0.06
            elif a and b:
                self.eventos.append((tipo, a, b, ex))

    def passo(self, dt, ent):
        j = self.jogador
        for a in self.atores:
            a.flash = max(0.0, a.flash - dt)
            if a.rel > 0:
                a.rel = max(0.0, a.rel - dt)
            if a is not j:
                k = min(1.0, dt * 18.0)
                a.x += (a.tx - a.x) * k
                a.y += (a.ty - a.y) * k
                a.ang += norm(a.tang - a.ang) * k
        if self.fase == "jogando" and j.vivo:
            mover_jogador(j, dt, ent)
        else:
            j.andando = j.correndo = j.mira = j.deslizando = False
            _vertical(j, dt, False)


# ============================================================ rede
def codificar(obj):
    return (json.dumps(obj, separators=(",", ":")) + "\n").encode()


def ips_locais():
    ips = set()
    try:
        for inf in socket.getaddrinfo(socket.gethostname(), None, socket.AF_INET):
            ips.add(inf[4][0])
    except OSError:
        pass
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("10.255.255.255", 1))
        ips.add(s.getsockname()[0])
        s.close()
    except OSError:
        pass
    ips.discard("127.0.0.1")
    return sorted(ips)


def rotular_ips(ips):
    return " · ".join(ip + (" (Radmin)" if ip.startswith("26.") else "") for ip in ips) or "não detectado"


class Conn:
    """Conexão TCP com threads de leitura/escrita (a thread principal nunca bloqueia)."""

    def __init__(self, sock):
        sock.settimeout(None)
        try:
            sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        except OSError:
            pass
        self.sock = sock
        self.q_in = queue.Queue()
        self.q_out = queue.Queue(maxsize=16)
        self.vivo = True
        threading.Thread(target=self._ler, daemon=True).start()
        threading.Thread(target=self._escrever, daemon=True).start()

    def _ler(self):
        buf = b""
        try:
            while self.vivo:
                d = self.sock.recv(65536)
                if not d:
                    break
                buf += d
                if len(buf) > (1 << 21):
                    break
                while b"\n" in buf:
                    lin, buf = buf.split(b"\n", 1)
                    if lin:
                        try:
                            self.q_in.put(json.loads(lin))
                        except ValueError:
                            pass
        except OSError:
            pass
        self.vivo = False

    def _escrever(self):
        try:
            while self.vivo:
                try:
                    d = self.q_out.get(timeout=0.5)
                except queue.Empty:
                    continue
                self.sock.sendall(d)
        except OSError:
            pass
        self.vivo = False

    def enviar(self, obj):
        if not self.vivo:
            return
        data = obj if isinstance(obj, bytes) else codificar(obj)
        try:
            self.q_out.put_nowait(data)
        except queue.Full:                 # cliente lento: descarta o mais antigo
            try:
                self.q_out.get_nowait()
                self.q_out.put_nowait(data)
            except (queue.Empty, queue.Full):
                pass

    def receber(self):
        out = []
        while True:
            try:
                out.append(self.q_in.get_nowait())
            except queue.Empty:
                return out

    def fechar(self):
        self.vivo = False
        try:
            self.sock.shutdown(socket.SHUT_RDWR)
        except OSError:
            pass
        try:
            self.sock.close()
        except OSError:
            pass


class Servidor:
    """Roda no host: aceita amigos, lê as entradas deles e envia snapshots do mundo."""

    def __init__(self, porta):
        self.ls = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.ls.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.ls.bind(("0.0.0.0", porta))
        self.ls.listen(8)
        self.ls.setblocking(False)
        self.porta = porta
        self.pend = []          # [conn, t0] ainda sem "hola"
        self.clientes = {}      # conn -> ator
        self.acum = 0.0

    def passo(self, mundo, dt):
        while True:
            try:
                s, _ = self.ls.accept()
            except OSError:
                break
            self.pend.append([Conn(s), time.time()])

        for item in list(self.pend):
            conn, t0 = item
            for m in conn.receber():
                if m.get("t") == "hola":
                    if m.get("v") != VERSAO:
                        conn.enviar({"t": "erro", "msg": "versões diferentes do jogo"})
                        break
                    nome = str(m.get("nome", "Jogador")).strip()[:12] or "Jogador"
                    a = mundo.adicionar_humano(nome)
                    self.clientes[conn] = a
                    conn.enviar({"t": "bemvindo", "id": a.id, "v": VERSAO})
                    self.pend.remove(item)
                    break
            else:
                if not conn.vivo or time.time() - t0 > 6:
                    conn.fechar()
                    self.pend.remove(item)
                continue
            if item in self.pend:        # versão errada
                conn.fechar()
                self.pend.remove(item)

        for conn, a in list(self.clientes.items()):
            for m in conn.receber():
                if m.get("t") != "in":
                    continue
                try:
                    e = a.ent
                    e["x"], e["y"], e["ang"] = float(m["x"]), float(m["y"]), float(m["a"])
                    e["and"] = bool(m.get("n"))
                    e["fogo"], e["rec"] = bool(m.get("f")), bool(m.get("r"))
                    e["pz"], e["pit"] = float(m.get("h", 0.0)), float(m.get("p", 0.0))
                    e["corre"], e["mira"] = bool(m.get("sp")), bool(m.get("ad"))
                    e["slide"] = bool(m.get("sd"))
                    if m.get("c"):
                        e["clique"] = True
                    if m.get("w") is not None:
                        e["arma"] = int(m["w"]) % len(ARMAS)
                except (KeyError, TypeError, ValueError):
                    pass
            if not conn.vivo:
                mundo.remover(a)
                del self.clientes[conn]
                conn.fechar()

        self.acum += dt
        if self.acum >= TICK_REDE:
            self.acum = 0.0
            if self.clientes:
                dados = codificar(mundo.snapshot())
                for conn in self.clientes:
                    conn.enviar(dados)
            mundo.rede_ev.clear()

    def fechar(self):
        for conn in list(self.clientes) + [p[0] for p in self.pend]:
            conn.fechar()
        try:
            self.ls.close()
        except OSError:
            pass


class Cliente:
    """Roda em quem entra: manda posição/mira/disparos e aplica os snapshots do host."""

    def __init__(self, ip, porta, nome):
        s = socket.create_connection((ip, porta), timeout=5)
        self.conn = Conn(s)
        self.conn.enviar({"t": "hola", "nome": nome, "v": VERSAO})
        self.id = None
        t0 = time.time()
        while time.time() - t0 < 6 and self.id is None:
            try:
                m = self.conn.q_in.get(timeout=0.2)
            except queue.Empty:
                if not self.conn.vivo:
                    break
                continue
            if m.get("t") == "bemvindo":
                self.id = m["id"]
            elif m.get("t") == "erro":
                self.conn.fechar()
                raise ConnectionError(m.get("msg", "recusado pelo host"))
        if self.id is None:
            self.conn.fechar()
            raise ConnectionError("o host não respondeu")
        self.mundo = MundoRemoto(self.id)
        self.t_env = 0.0
        self.l_clique = self.l_fogo = False
        self.l_arma = None

    def passo(self, dt, ent):
        for m in self.conn.receber():
            if m.get("t") == "s":
                self.mundo.aplicar(m)
        self.mundo.passo(dt, ent)
        self.l_clique |= ent["clique"]
        self.l_fogo |= ent["fogo"]
        if ent["arma"] is not None:
            self.l_arma = ent["arma"]
        self.t_env += dt
        if self.t_env >= TICK_REDE:
            self.t_env = 0.0
            j = self.mundo.jogador
            self.conn.enviar({"t": "in", "x": round(j.x, 3), "y": round(j.y, 3),
                              "a": round(j.ang, 3), "f": int(self.l_fogo),
                              "c": int(self.l_clique), "w": self.l_arma,
                              "r": int(ent["rec"]), "n": int(j.andando),
                              "h": round(j.pz, 2), "p": round(j.pit, 3),
                              "sp": int(j.correndo), "ad": int(j.mira),
                              "sd": int(j.deslizando)})
            self.l_clique = self.l_fogo = False
            self.l_arma = None

    def fechar(self):
        self.conn.fechar()


# ============================================================ sprites procedurais
# Os personagens são desenhados em código: uma grade de pixels (com sombreamento,
# contorno, capacete, óculos, colete, botas, arma...) vira colunas coloridas que o
# raycaster desenha. 3 vistas (frente, costas, perfil) x animação de caminhada.
SKIN = (226, 182, 142)
ESCURO = (34, 34, 38)
ARMA_COR, ARMA_CL = (52, 56, 66), (112, 118, 132)
EQUIP = {
    0: dict(capacete=(44, 62, 110), camisa=(48, 70, 122), colete=(60, 104, 186),
            calca=(34, 44, 78), bota=(24, 24, 28), luva=(26, 26, 30),
            acento=(130, 190, 255), lente=(110, 200, 255), mascara=(30, 36, 56)),
    1: dict(capacete=(104, 76, 44), camisa=(128, 98, 60), colete=(186, 118, 50),
            calca=(100, 84, 56), bota=(40, 30, 22), luva=(32, 28, 24),
            acento=(255, 176, 80), lente=(255, 196, 100), mascara=(52, 40, 30)),
}


def tom(c, f):
    f = round(f * 6) / 6.0       # poucos níveis de sombra => RLE compacto
    return (max(0, min(255, int(c[0] * f))), max(0, min(255, int(c[1] * f))),
            max(0, min(255, int(c[2] * f))))


class Tela:
    def __init__(self, w, h):
        self.w, self.h = w, h
        self.g = [[None] * w for _ in range(h)]

    def px(self, x, y, c):
        if 0 <= x < self.w and 0 <= y < self.h:
            self.g[y][x] = c

    def ret(self, x0, y0, x1, y1, c, cil=0.0):
        cx, rx = (x0 + x1 - 1) / 2.0, max(0.5, (x1 - x0) / 2.0)
        for y in range(y0, y1):
            for x in range(x0, x1):
                d = abs(x - cx) / rx
                self.px(x, y, tom(c, 1.06 - cil * d * d))

    def ell(self, cx, cy, rx, ry, c, cil=0.45):
        for y in range(int(cy - ry) - 1, int(cy + ry) + 2):
            for x in range(int(cx - rx) - 1, int(cx + rx) + 2):
                dx, dy = (x + 0.5 - cx) / rx, (y + 0.5 - cy) / ry
                d = dx * dx + dy * dy
                if d <= 1.0:
                    self.px(x, y, tom(c, 1.12 - cil * d - 0.10 * dx - 0.06 * dy))

    def perna(self, x0, y0, y1, larg, decl, c, cil):
        for y in range(y0, y1):
            dx = int(round(decl * (y - y0)))
            for i in range(larg):
                d = abs(i - (larg - 1) / 2.0) / (larg / 2.0)
                self.px(x0 + dx + i, y, tom(c, 1.06 - cil * d * d))

    def contorno(self):
        g, w, h = self.g, self.w, self.h
        novo = [l[:] for l in g]
        for y in range(h):
            for x in range(w):
                if g[y][x] is None:
                    for nx, ny in ((x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1)):
                        if 0 <= nx < w and 0 <= ny < h and g[ny][nx] is not None:
                            novo[y][x] = (14, 14, 18)
                            break
        self.g = novo

    def colunas(self):
        cols = []
        for x in range(self.w):
            runs, y = [], 0
            while y < self.h:
                c = self.g[y][x]
                if c is None:
                    y += 1
                    continue
                y1 = y + 1
                while y1 < self.h and self.g[y1][x] == c:
                    y1 += 1
                runs.append((y, y1, c))
                y = y1
            cols.append(runs)
        return cols


class Tex:
    def __init__(self, tela, muz):
        tela.contorno()
        self.w, self.h = tela.w, tela.h
        self.cols = tela.colunas()
        self.muz = muz            # posição do cano (para o clarão do tiro)
        self.esc = 1.0            # tamanho do texel em relação ao padrão (sprites 3D têm mais linhas)


def _fig_perfil(time_, fase, arma):
    E = EQUIP[time_]
    t = Tela(28, 40)

    def perna(x0, dec, k):
        t.perna(x0, 25, 35, 4, dec, tom(E["calca"], k), 0.5)
        xb = x0 + int(round(dec * 9))
        t.ret(xb, 35, xb + 6, 38, tom(E["bota"], k), 0.4)

    perna(10, -0.3 * fase, 0.7)
    perna(11, 0.3 * fase, 1.0)
    t.ret(9, 11, 16, 24, E["camisa"], 0.4)
    t.ret(9, 12, 16, 23, E["colete"], 0.5)
    t.ret(5, 12, 9, 21, E["mascara"], 0.3)                   # mochila
    t.ret(14, 18, 16, 21, tom(E["colete"], 0.6), 0.2)        # bolso
    t.ret(9, 14, 16, 15, E["acento"], 0.0)
    t.ret(9, 23, 16, 25, ESCURO, 0.3)                        # cinto
    t.ret(10, 10, 13, 12, tom(SKIN, 0.7), 0.2)               # pescoço
    t.ell(12, 5.5, 3.8, 3.8, E["capacete"], 0.5)
    t.ell(14, 8, 2.2, 2.5, SKIN, 0.4)
    t.ret(14, 6, 17, 8, (22, 22, 26))                        # óculos
    t.ret(15, 6, 17, 8, E["lente"])
    t.ret(13, 9, 16, 11, E["mascara"], 0.3)                  # máscara
    t.ret(9, 5, 16, 6, tom(E["capacete"], 0.7))              # aba
    if arma == 1:
        t.ret(6, 16, 10, 19, ARMA_COR, 0.2)
        t.ret(10, 16, 22, 18, ARMA_COR, 0.3)
        t.ret(22, 16, 27, 17, ARMA_CL)
        t.ret(14, 18, 16, 22, ARMA_COR, 0.3)
        muz, gx = (27, 16.5), 18
    else:
        t.ret(14, 16, 19, 18, ARMA_COR, 0.3)
        t.ret(14, 18, 16, 21, ARMA_COR, 0.2)
        muz, gx = (19, 16.5), 16
    t.ret(11, 12, 14, 17, E["camisa"], 0.5)                  # braço
    t.ret(13, 15, gx + 1, 18, E["camisa"], 0.5)              # antebraço
    t.ret(gx, 15, gx + 3, 18, E["luva"], 0.4)
    return Tex(t, muz)


def _fig_frontal(time_, frente, fase, arma):
    E = EQUIP[time_]
    t = Tela(20, 40)
    for i, x0 in enumerate((6, 11)):
        erg = 2 if (fase == 1 and i == 0) or (fase == -1 and i == 1) else 0
        fim = 38 - erg
        t.ret(x0, 25, x0 + 4, fim - 3, E["calca"], 0.5)
        t.ret(x0, 29, x0 + 4, 31, tom(E["colete"], 0.55), 0.5)   # joelheira
        t.ret(x0, fim - 3, x0 + 4, fim, E["bota"], 0.4)
    for x0 in (2, 15):
        t.ret(x0, 12, x0 + 3, 21, E["camisa"], 0.6)
        t.ret(x0, 20, x0 + 3, 24, E["luva"], 0.4)
    t.ret(5, 11, 15, 24, E["camisa"], 0.5)
    t.ret(6, 12, 14, 23, E["colete"], 0.55)
    if frente:
        t.ret(6, 18, 9, 21, tom(E["colete"], 0.6), 0.3)
        t.ret(11, 18, 14, 21, tom(E["colete"], 0.6), 0.3)
        t.ret(8, 13, 12, 17, tom(E["colete"], 1.25), 0.3)
        t.ret(6, 13, 8, 14, E["acento"])
    else:
        t.ret(7, 13, 13, 21, tom(E["colete"], 0.85), 0.3)
        t.ret(7, 14, 13, 15, E["acento"])
    t.ret(5, 23, 15, 25, ESCURO, 0.3)
    t.ret(9, 23, 11, 25, E["acento"])                         # fivela
    t.ret(9, 11, 11, 12, tom(SKIN, 0.7))                      # pescoço
    if frente:
        t.ell(10, 5.5, 3.8, 3.8, E["capacete"], 0.5)
        t.ell(10, 8, 2.8, 2.8, SKIN, 0.4)
        t.ret(7, 6, 13, 8, (22, 22, 26))
        t.ret(7, 6, 9, 8, E["lente"])
        t.ret(11, 6, 13, 8, E["lente"])
        t.ret(8, 9, 12, 11, E["mascara"], 0.3)
        if arma == 1:
            t.ret(13, 13, 16, 24, ARMA_COR, 0.4)
            t.ret(14, 12, 15, 14, ARMA_CL)
            muz = (14.5, 12.5)
        else:
            t.ret(13, 16, 15, 22, ARMA_COR, 0.3)
            muz = (14, 16)
        t.ret(13, 19, 17, 22, E["luva"], 0.4)
    else:
        t.ell(10, 6.5, 3.8, 4.4, E["capacete"], 0.5)
        t.ret(14, 16, 17, 23, ARMA_COR, 0.4)
        muz = (15.5, 16)
    return Tex(t, muz)


def _fig_morto(time_):
    E = EQUIP[time_]
    t = Tela(36, 10)
    t.ell(18, 8.5, 16, 1.6, (96, 18, 18), 0.2)               # poça de sangue
    t.ret(3, 5, 14, 9, E["calca"], 0.5)
    t.ret(0, 5, 3, 9, E["bota"], 0.4)
    t.ret(13, 3, 27, 9, E["colete"], 0.5)
    t.ret(12, 3, 14, 9, ESCURO, 0.2)
    t.ret(18, 6, 27, 8, E["camisa"], 0.3)
    t.ret(20, 8, 30, 9, ARMA_COR, 0.2)
    t.ell(30, 6, 3.4, 3.2, E["capacete"], 0.5)
    t.ell(31.5, 6.5, 1.6, 1.6, SKIN, 0.3)
    return Tex(t, None)


def _fig_slide(time_, arma):
    """Soldado deslizando: tronco inclinado para trás, pernas esticadas à frente, arma pronta."""
    E = EQUIP[time_]
    t = Tela(36, 22)
    t.ret(14, 17, 29, 20, tom(E["calca"], 0.7), 0.5)         # pernas
    t.ret(13, 19, 28, 22, E["calca"], 0.5)
    t.ret(28, 16, 34, 20, tom(E["bota"], 0.8), 0.4)
    t.ret(27, 18, 34, 22, E["bota"], 0.4)
    t.perna(2, 8, 17, 4, 0.30, E["mascara"], 0.3)            # mochila
    t.perna(5, 6, 20, 8, 0.30, E["camisa"], 0.5)             # tronco
    t.perna(6, 7, 19, 6, 0.30, E["colete"], 0.55)
    t.ret(8, 10, 13, 11, E["acento"])
    t.ret(9, 18, 16, 20, ESCURO, 0.3)                        # cinto
    t.ell(7.5, 3.6, 3.7, 3.5, E["capacete"], 0.5)            # cabeça
    t.ell(10.0, 5.0, 2.2, 2.4, SKIN, 0.4)
    t.ret(10, 3, 14, 5, (22, 22, 26))
    t.ret(12, 3, 14, 5, E["lente"])
    t.ret(11, 11, 29, 13, ARMA_COR, 0.3)                     # arma e braços
    t.ret(28, 11, 33, 12, ARMA_CL)
    t.ret(8, 11, 13, 14, ARMA_COR, 0.2)
    t.ret(10, 9, 19, 12, E["camisa"], 0.5)
    t.ret(18, 10, 22, 13, E["luva"], 0.4)
    t.ret(8, 17, 14, 20, E["camisa"], 0.5)                   # braço de apoio no chão
    t.ret(4, 19, 9, 22, E["luva"], 0.4)
    return Tex(t, (33, 11.5))


# ---- Soldado 3D (modelo CC0 "soldier", Grab3D) pré-renderizado em sprites paletizados.
# Chave: LOD(0..3) + vista(f/b/s/d/m) + fase(0..2 = -1..1) + arma(0/1). Dados: (larg, alt, cano_x, cano_y, zlib+base64).
# LOD0 = mais detalhado (perto) ... LOD3 = menor (longe); a escolha depende do tamanho do soldado na tela.
ALTS_LOD = (76, 52, 36, 24)
LIM_LOD = (190, 125, 80)       # altura do soldado na tela (px) a partir da qual usa cada nível; menores = mais detalhe, mais custo
PAL_MODELO = ((213,180,159),(164,156,137),(152,147,128),(147,141,122),(139,139,119),(136,136,116),(134,131,112),(129,129,110),(126,127,107),(123,123,104),(124,120,102),(119,119,101),(117,119,100),(117,117,100),(116,115,97),(113,114,98),(113,114,93),(111,112,93),(109,109,94),(108,109,87),(115,104,83),(106,106,88),(104,104,88),(102,103,89),(102,103,82),(101,100,83),(98,100,83),(97,98,82),(96,97,80),(94,94,83),(94,94,75),(95,90,73),(90,90,75),(88,89,74),(86,87,72),(83,83,68),(79,80,68),(75,75,64),(68,69,60),(54,55,50))
SPR_MODELO = {
    '0b00': (50, 76, 20.94, 31.21, "eNrFl9mypCgQhkdlLVS2QVGRQnF5/yc8Q5+u7qm+EStiIoa7iuCTXP/M+vr6v44kSkH8ARD7oqgKUN8n1rIERVGw28DOAIe4LOB8lzhmwx5NyZrbxLr6OcxzP/d3iTCG4ZEOo7cdGZ4oOf63+SC8j7/SKT/JIPpBFB8AQzO29IMMRjs3DFIAjVtuAW73BsKigmDwvs3fB9A6LkiFKW5HalmR87/BzLjRD4aruK69YBhUl4BqYd+GrdOEqUaaVVesqtAVQZIt4BExogAxUDgIYFVd2uWI0kBug0GMAKM1KeoGigvg6eXqhy64oLkUo2WUKS/EVcCin5bF++gWY5z2UqphsPrKKv9UAflondWm69rxUWlhL3NiPZ99F+MRty1uqyVUUH1Z886pcd/3GC2mYhldWJUUjyviaXmTXvB2FTI4HeOKa31p1WJUGNpz26PrFrccGgtMLiVF4Hb18lwXbfWow2GogCW4IuZ+2J07on+6FOCwR2EfDbkiOir2PZybi9auejxidLi4fMNNzRbG0zlv/aLbwxoDyLWiNCwsa4wpvjF6PfrRVNl2d5sPbee9EzJF1k93VDd4qUXPtRD6oW8Jie5SEkgFUU0RugHMqTdQVVKCISiTPtyQkrlvScWImqTkBN2Q3ji1aRIQsroBInZntC0NRQCUbG8pb5C5MadCEsSqKqrgHMWA5UfIOChMlaAqdFtgBIEsYdZJ14i2agsD4hLhnOtmDp1qma7drCjFipJcRvjCJOqYbJUZOFWGUZp5ZDKGcNpPPH4toVd1BXPx5R1tFAYwddEgGWLqQTJZ5xwjjmGlUnctXGGIcJMrEop4T3kaszZwShoydRmi66ce/Wzt2ZieUp4t3bFhbf19LUijSJklejwLBL47L0bJcS2zZcUQR8R+u5S2EyWybyQFUVTan4WvaVl12Tc8JPCV5qkhaUpnN6XQjVb9kqK6BCTreTKkek2+WaSuzQjcV1AAouJVr66d6tZk6sqrquD4JYPdlDL4ULkE0rLpXpd8h5BAmfBufUMwe0XUdBikrsr0x9I/FPplejfUAGY8X0Wn0O+RHxoAWMgViVTl7xT0m7c2s1/2iJRvdhxpVOeKhEMh/11dzvjcsrIryreUHbv3OeI8/NtX96d+5pb8Y3/GN8KbzBv7eUT79tVjW7Zr18/z2Hb//vs8csRu3zewRJy58J7rH4v0DeTc/zD8B3F+9j/vY+A/Of8AyRP/Nw=="),
    '0b01': (50, 76, 20.94, 25.54, "eNrFl2uPpCgUhlflKioIhaIiheLl///CHra7Z7ZmkxEr2WT5VJXUA+fynkt9fPxfpyVSQvQGEPosKzJQ3SfWPAdZlt0nDgY4xHkG59vE3LGyzll9m1hXN/t57uf+LuFHP5RlSRm97cjwRNHxx+ON8JZ/xZO/k0H0N5G9AUz12NA3MhjMXDNIAdR2uQXYzWkIswLDwbkbz0BoJi5Igfk5D8RUWcp/hqmeRjd0tT63pRcUA3AJ8Ab2jd86RZjstVpVwYriEqGUNKAMGBGAKpBZBGBRXNnlHNEKiDBoxAjQSpGsqpESfyYWx9fog7de8VaMJkpLOtFcENs6jsviXLCL1k451cphkkr9mXg+nfbIBWON0l3XjGWhtBbNBWFHtrkuhCNs27qthlBDhSivPNd83vfwDAZTsUyTXybWXBHRKOhCeDzMKlpvVQjrmAt1YdUiG7oOzeOxB9ut1u8KK4jxRSk2mMpgxePhTTzCHZq1FOQXSZ+7we52CE+/WrsYv62NYTW9eKOjVb/v/txsMGZV47EGq8nVG5NkfvP2tNYZt6jmMFrPCMNEs1qWsO4hHqcGN3bpknKb85VxzoqWVMpNN6p2965thYxSFIqqW+1NdQITUkDEKLozQ+YOMVzkhGAI8qyAN1qJ72NjYERObcsJutF6w9TESUDIaodoF8RpYqkpAiBne1PyGml2YxTEhlgUWeHHObYelh4h49BiJgWVvts8IwgkCb1OqkK0kbsfEG8xSbmu56WTDVOVnSWluKUklZF+YS2OVdFIPXIquyj1xCOj1oTTfuLhY/G9rABMxZfHEpEYQBLVwhlisqSJrEuOEcewkLG8Fi4xRLhOiYQi3lOuPz6M55TUJFkhXTf1qCafsNY9pTwp3almdfXZoXwbw5AniQ7PAgH7qckQxVslCc8QR8R86X6epUgSi24kbc2X8CXNi2Rr8A4RSH8uAiRO6eSm5LvRyK/PNatyQJKeR0OK7zE2C4JISrxeAoSyb73aZqoandCVk0XO8ffWE5NJaSkTCRxpXvffP3IaIYES4d36mmD2HVHdYUBx4o1p6UuJfpreDbFAEp6vopPo1zj2NSjYkhKJkPmvW/vNGZNIeo9I/tI5j33fUyLhULT/7CFneG7Jtivyl5Qdu3Mp4jzcy637Uz1TS/6xP8PrvNKJN/bzCObl1mNbtmvXz0hs7vX7eaSI3Rj1G3Gmwnuuvy3SN5BzX/d/Eed7//PeBv6T8wM6Lu7h"),
    '0b10': (50, 76, 20.94, 31.21, "eNrFV9m2nCoQjcoozSAER6RR1P7/LzyXPulkdV7Evi+pN9ZiW+zaNfn19a+sIVpD/AEgdkVRFeB2HbGWJSiKgl0GHAxIiMsCzpcRc1vXvGT8MiIubg7z3M7dVUQYw1AnY/QykfaOEvGfPz8Ib/0jWfmJguiJKD4ADHwU9AMFYz9zBimErVsuAdzmLYRFBcHgvcjfh9A6qUiFGRYD6VmR488xs270g5U6rmunKAbVKUAL2ImwtYYwfTNmMRUrK3SGIBQLUEeMCEAMFA4CWFWn73JUG9Bso0WMAGMMKRhH6gRw980ahja4YGQjxr6mXHulzgIW/bgs3ke3WOuNN40eht6cvcrfdUA+9q431rZiqiuj+lNNei9n38Z4xG2L29pjqqg5zXnn9Ljve4zPu8s0haVRqj5D3HvJkwffr6oJzsS4YnZK/GuxOkzise3R9YsLu8EKk9OWorBYnXmsi+nNYMJhqYIlOEPM3bA7d0R/dynAYYuqz1R7S9W+h8fmYt+vZjzW6HBx6sNNfAvDwznf+8WII8kCyHlH4WxZlhhTfGP0ZvSjBdly95sPovXeqQbfjJ8uVO3ufWNEJ41SpjaXGomxSQRSQcQoQhcAc4uepUoIqqqiOBfjJbsfWZ0AUlYI4duFGbI2GME0oGCaOiW8MtrWgTFxo1IyygklF/piqxueXiMHxytGqws8ttgKYZuw25ZiYpsLCNvOsubT1HLGIdL54DKNZdcp7Ya5QyUqstTXmadmNehtW1ZN5IXwdlJoVCESRnsD3ObDO0y1lRgVKcM7gFKDSwE+RySyRHd4tM8kFh0HyTKIkVJONUuIyT55YJJ7VjdIThhNZTEOgqT72ey1rrPkV8OJuql502ZjRcfE/HshmQVjusr6CAw1WH/X6qqlLEuZnbRKM8rG73xxRlLAsz56xNAvH2FlrKIyvynZ2b6+G8KihM1nYgXg69bGSAlIDqEBBsWrC1qCcHYDcB0oG/a61WiRlkWUW994aTV8+Wg5wLfMIjd3GmH54hFoDQnO5FUMM5foVdyODazpMuGdTTtK/ZqVdgo3SjISLrWSxW8fXiPAUEaQwDnF7vdppESzjCATSDPpTzMYBa7KDPOQ9GB/elSwZclyq3ho6Vu/GUTd57Lkcdy3t1Maidn/gsMffyFiFrH7+9tpdffs3Nzev3rszmdpuPedLXp1PyeyP3Y/9O+T2tz30wl9PB77sr3zmLdtPX3U046/zsf7+f/Zf33W5+I="),
    '0b11': (50, 76, 20.94, 25.54, "eNrFV9uWqygQHeUuERSCF0SCoub/v7AP3SvTK/1wxJ6XqTfWcqdq121XPj7+L2upUoj8AhD7ogAFvF1HrGUJi6K4jtg5lIiUBZqvIo6541Vd8voyIq5+DvPcTf1VxGzDWCXj7DKR8YET8bv5RXqrf5KVv6kg/kQUvwCMtRXsFxWMw1xzxBAybrkEcJs3CBWAoNF7kf8eocGphgIin7NlQ1Xk+HPCjLN+7Grz3Na+YQTCU4CsUS/C1mnKVW/MogEHEJ0hKCMCVpFgBjGHhcMQAXAWl/dMadhso8GcQqM1LXiNdfN3xOLlmjgEF7RshR04q5VvxAliW61dgvdxWozx2utW9ZPS+u+Ix8ObgH0c3KCN6YStgDa6OSnKw1m++S7GI27buq0DZQNrmuqMuZHzvscYDWHNaqewTvwUkYJCPsb7fVibNjgd42pBo0+iWpRg6yTu9z26bnVh10QjQk5GUVCmom/u9zAkax6H4S2D4KRP5m50u3PxEVbnliFsqxh4zU58dOzW7Xt4bi4Ow6rtsUZnaAlOZk/xsC326Zwf/KLFMRgzY4IyG3RZYvxMcPTaetvlR8pvfhGD965p6U376crWDb5thZJt0+hKX1ok2jSEEoAwZxhfWaEdTqMKKMMAFEUJ84gwjxUDlEgJMCY3fkFtWoJREigESliiK9K2jpzfbkyqNICU0Qt7cVBtnaKRo6sBZ+ACjy12Qpg27KZnhJr2AsJ0s6zqaepEXSOs8snlioi+b5Qb5x6XuMhSX+c6LatRbXFZFZUX0ts3UmGAabDqBmuTT+9ouZEEFzRhIU4LjrKMfCayVPXEJtEMm+hrCDO7/YNblgqneErRZD55YJoLq+9lTTlzHx92FDT1cLZ7jesNo18Jiqqt6jY7hD2zKZSvg2QWnPcAZZudY0XU16yuSsqylFmlbVLTcvvVL05LBuusjwEnL18+wso5YFkfcelm8xqKEJZGmHwnJnF95WfjtITZi0lBAovXV4YSkr0AXA/Llr++apVIx2KmhMHWZTp1Xz5SX5FbJqypV5jIF9uFMZQCy6QqzELi13C7auRtn0nvrLteqpdUmincGM2UcKmauvj2oRDiOFOQcKsZcf++LEujQjPMIaTsexlMkoAywzykevDvHRVMWfLcKR4Me9s3vaiGXJc8j8f29kqSmP1fcPjjByJmEbt/vL1W98jq5o9fPXbnszSG4U1f05HyOCeyP3c/vmVn8/qxnyr08Xzuy/bOY07H3GlQn3b8eB/v7/9mfwCdWNeL"),
    '0b20': (50, 76, 20.94, 31.21, "eNrNl9uWqygQhkflKCICg6IiQVDz/k+Y7e5Jz+4rMVcz5Ca9Vn+rqv465vX6r54kSkH0AZCGoqgK0NwnYlmCoijYbWBnQEBcFnC5SxyLrWteMn6bSNEvYVnGZbhLhCmM9fkYvR3I+EBn4H+bD+St/zpf+UkG0W+i+ACY+dTSDzKY7MIZpACaeb0FuN0bCIsKgtH7Nv//ENpZdKTCDLcTsazIxc8xM27yYy9UinHoGAbVJaBaOLRh7zVhqpEmasDK6rLqCcUtqBNGFCAGCgcBrKpLvxxRGshtMogRoLUmRcNRdwE8vIxnDMEFLWQ72Zpy5bvuSrDkp3X1Pk2rNl57LdU4Wn3llX+ogHyyzmpj+naqK93Zy5xYLxbfp3SkbUtbtIR2VF/WvHNq2vc9JYNpt04uRCm6+tIrK/hpwdvYyeB0ShEzeenValQYu+e2b66PLuwad5hcjpQOt9HJZ4zanp9wGNrCElwRyzDuzh3Jr86tJuypszUjV0RPu2MPz80la6Oejpg8Li5tuJlv6/R0zlu/6vawxgByPVF4E9Y1pVPflLye/GRAtt395tfWeu86SRrj5xtduwUvdTcI3XWq1nf6fNLmTAKpIGIU3dkhbiQtQYgyCKqiKOGN3TEyKTWXWFQQV/TG6PXKMDbaCcLy9I2QGzZWFQxlYwUAKBG8YWPrleKqm0FZMizIDWLgnAwL7RXDlJ3h8+yQnolhJZOp901BOG6zS8SZgQFU4pCUJAhARq5n4kt40S/n8mfjMveclqjgmUiUZKRRYlCvPcQZU4pgRl81mVlhBtX5lRFqAKCZ0MWsmKipHM+NyzEXHMNcHJ1REkHe/1btVLjKp3BQg2I0frWwwaan2VJcGFeUTe9RBEGbz+BUCzr4rwrjFA9FtkNCHGbTfBHJNLwoszYCPQWV/9Tk6RaBWUKVgIL3VvKMlEzkiL4uBXlvvhQW0cicU0OLUa/eVUlJCUCuA+MkBHofJIZiVAB8TaxdPxBF/z0HzmMxQ0QqVYXe+swClLAhOXExwPP7PlwpgYRmbtjAYS2/Be3FwpjKEGuPS9h/435gDGcO0nqN53T7/ssgJEnusn4+H+mPj7jEOa1ex+6PP8r5psp59dr3GH/8qgBwzF755wb84eO54LJEcPaHj+nxeGQCP/a4/SCifSSbkep8P4jDP/btEyL5zm3HB8DrCPP2+sTE67mtezblz9f/4P0CWEb9/A=="),
    '0b21': (50, 76, 20.94, 25.54, "eNrNl8mSozgQQAfQ6jQIhCUECCEkwP//hR6qpj1dl0b4NJMXcAQvcl/8ev1X0jApMf0AiF2WFRm6XydCnqMsy64TGyCBaZ7h6SqxTxpuZQ7lZSIEO/lp0mN3lfCD72+HAL/sSD+Tw/GH+iC8t78OyT/JIPkisg+AsRwqniG4nHEzlYA5xsoulwC3OYVxVlDcO1elv8fYWFGzgornNHADWcp/oKDs4Hol1HMNXQ0UoVNAVLir3KpbBrJTalHFvThHOKc1ukVKGCKAMosRLoozu5xjqkVNHBQBhlTbsuxekrb+M7G4Krhee+Nb0VSDAQ7S1dUJsS7DsCzOxXFRyraubWQ/Nm37Z2KenfLERWNNq5Su7K04nvVJUmY7wOp0jHtc17AGw7jhdX0781yJadtijIbyehlGH0aozojDKOxjfDxMqBtv2xhCn9ftiVWLrHjoq8djW60O1m8tbTGlJ61YMS6jqx8Pb4w29bwraDgqTpI+6d5uto+zD9Yuxq+xGqDkJzoUL/W++edqozGhHfYQrWL5iY5egj+y+LTWGbe01X6kZSIUJ4bVssTwFeDo2t4N+kILrs5XxjlbN/Su3Hhl6nrXNJUUTV1L3l7p86FVNWWswOTGCbkATAMVDBMOGBVZluMLY3o4Kqm9N1QUiBb8wuh1UgH0ZsA4P2xj7IKORXrFYDgmAsoJvqBj7aQsZT2iPIfDowtEV5asm7gWnHIAXIjkkB6ZghyaVbt7xkpWJ5fIqLs7Ijn1UTaMIAysOAeEE3qSmEA/jarkOcnKhCey+ZpRopNHsYSR8hvBifjKQY2SApbHKzCuEOKJhSBGCeLGmv5oeqClSM72l6i1bAguj7awo5ZQ4ORq62QngcevVy2p0jxZih5KyWH4nkVKYlSV6QzeBO/cd4WVnHZZskN86CZV2u+dq6DM8qQOzxHmza/d0EqGk4QsEH9XnweWQ7ISNc8F+7X5oh/FvUl1YFdRouU/PyxnWSqBxzE2CEHu76FKSYYSJ+lS647JXyumZHAciymCN7J46xgFyvGdpYJLEX3fhwtjmPFEYfkSQ/MOqBYTgEwQS0dz/G5t7zoAmjhIb8d2Mv/Oc0Vow1Ll/nzO8beNNKc4VYrPze2/s+PuRcqq17aF8KPKEE7e1duxAX9oDHFLbyhrfhBxnueEG/sW1h//EoKZo0mE6pAfxO7mLX5CHCeHXfcPgNfux/X1iYrXc122ZMqfr/+B/A2HaO2X"),
    '0d10': (83, 42, 41.34, -8.67, "eNrtltvOmzoQhRNjfIgDBHubGLAdn3n/J2Q7f1WprdqLkNxU6pKQEBcfM15z8L7/PdqKoR9GckDOnyW2mFJ6Op0+RzQUdhyfTn+ApgNIq2IYyLkSz+g3xLL7/CLRW5FKGQdzacyP3/GFfCGTydureUdVttyiE7BfQUomrDNyvhF8W/fibdpezjulbXO8R6hmTqRQ4sZGmaLWt1FcS0qvI/c1+CyX/5rTqQtCDAizHjKukoth5b6UI/70JmWJzmcQ5wkD0EDcnG9igH2glJj4PM9XDdp1rsac+y4ofGmwVgxy7NmVsY5PFffUofJcQk6WQTJpJQilokXMEmvWNbzRltkbPhk7K9WLC51tECx6Tik8zszO+THF+BDqcqOSsyt3yzKyFqLDyGiCzslHZXVHJojaaV5mBCAEAB9kBr8uOZcctPZ8vaBhFfeegBacGtgeDXNZbMox5RRXs2oz2hlBTOGZYoCOQXOSMcdgo154MM6tSqFmrGUK2VfBHhlK0WmllrJ5dZM2R+2rNx1EgGFWhyo4EqgVIljrypZ0ECoELXHPJDMQY95eh3oCB5iLLaW4WEqes41hmueFD1zSkYGWUDAS/Lr5eos5VIdKTiLIxc9+IPfLXbZdDbUTtCX4QKg1Sh/0820wnTOz83PPJgpRfRiiiBzy3ln9bUqNdFiNcUvNmA3PNTUQiNhby47ykd9nOdDJy35mhA5X2h+M89dBjfmk3brwO5eMgZ+7aTZHsfo+20qtHdo2P9boQ6Q3gpUuDReILwMgtUe//0qX9247xhEEIUUQdc23Va8ObLyfNNzXiXMMKADPnVTyw+a3rXJx5gZzyB4PG+ucyeV9+43TcqptWpIKeSvlEyW1j+PdpbjFUC8/eds/pXvZtpKj/yDyaxxkm/L+WVVvyv5pbfs/PfU/gpSzgA=="),
    '0d11': (83, 42, 55.1, -16.92, "eNrtltnOozoQhMExXuIkgImDAdsYr+//hBkns2jOf3MyJDcjTUkIhNBH09XV4n7/e5STZi8+Oo6vPccBqV+APaRDyvn/iQ2mlFZV9eV2vLtfOK31er1eU36tRkvhmeOq+goNSX8nrOsD99CrnTTSuxbXhVij/yA3lx/6wVtf92YzQ0ipP+vjQf9qWsjpmKx/In2p8s/stl6mHBtUAfMsUrDOWGdN18ew5Zx3TJDxIWfNLwiVLydykEPHehG90rMdCNw1lYvbopivh6pibhAtwuwCKZeG4Fkd6b5Jv+gQBapr4KcRgwOAGNTd0JJxCX7emR4VizH15ewkPjZHJRnk2NK2neaTeSeVs4veUEilHAZCiThQtknGyfAGk8dNc6HXSV7ZQMlkupsZaE8Z3M+Mm7U8eueGoesI73AbmOh61kC0F5m8dioF76QZLkQ0hDnWSQQgBADvQ4ZtW5YYU3RKeqrxsVWnwgYNqA6w2fnlfh6V9877EEY7GyPNhMqegjXBAO2DxiB89JvySnGnValWokOPDzVkGJQG7AqnLZQ55U12wpRQ2uINgwicG4YpAbuYnXDG2JSD2gbh3CLwhXGmG4x5c2phvSOgZjYpps2nFKdovLtN08zbVtCegYZQ0BH85+arXNoZQiwSm5jttJW005GjM8T4PNCG4B2lJuM2px5XvT5bPdlturAbhagcJ0QR2eW9Ncvz3HHKF63t3JMyp7ogWwIRe2eZ3Gnf83G6tXTcxGVmhLYnetlZ59dFjflNWT3zkYsj/ZKmSe/FqnEydplLQpsD+I25DuGNYoUN7RGWtoJHRn++SqW3OsC1pQjCcqDz4XnHy5Df62o7LTfOCaAAhFgmLq4mvm2V9RPXmEO2rsaXYMT0vv3aKnFre5GCdDGn9ImRuvf9aIPP3pWfn5jvn9JYfjVTWa8fRD7XQVxDuH9WxZt0/7Ty/Z8e+gbU6Y6p"),
    '0f00': (50, 76, 29.06, 31.21, "eNrNlst2pCoUhltULoUKQhRRoEDQvP8TVttJpZOeiDU6h5Gsxee+sn8ej/9qEchQUb4ALAS/p7KorxOGkm2nCF8Gkm3Z+zvEzF4lNssQhgi2lwmfbm/FL1hs4nLguvj1Z+nLxKMDH8TthfTCPwB4pYJLefg1vAB0b/pNvMHi6vl1sjdw2AB0DtcK7ifDICxA7aaxy58HaHYiWBstHTw3Hci5RqtaGiqhqOqZm4o3ZVWdZ7VuIUn73FQVLMs5mZKgcystgoAYynWPCeaYzKioqtO6aCKUv03OSCm5nAjuMav4CRBdL6yWKU5GDlJG0JGh44M8QYJukxvC6qfDxjh1+BaYPAMe96myuk+rDnxaZjcRFCg/8+rhbO1iOn7ub4OjshHOw/G0hY2rxZZojyStOWwKqWHFbxmvyLxJN4aJ+9nRGGokT71iRzXk3jnqJhmooTvFEJwOITubRe7GyajHdTLN3tc33J4RPZ3jEOPaRa0PTK5O9jd42og1IVAE0zt5hGK0KGtUn07Trl1mm3Zzk5xLKraFthicz98lLlvaUlzTdhRm2zy3S+5KMeHXFJxblphSiv7KNV8Ov/aU9s0nPV26586PKfgY1pR0cwGYIVWqAANqgTo0pMoTI+68AOWgOVYzLkmesJwUmHddg4taZFrkeQ8jB6WA9TYMEFX1hUAswp0KDdUVpaNQF5RNVQ1kGOOQFEGIIZoDhsQILWpAN00PJVRVNllWNW1dq55rsYISsYWwnMxSosSCgNbe93rkpMtE4tp2aCkR82PxI+loBcpMtqxou7YCqD8UV7GeDkxkQl8EbAkuUPt5g22NCMrY6OuRIsIOXW6tck7P2VeAMQED1n8+BI6Z2Lls6zJmefWRHxunQxCyFVzT6knPPgk/yi6rhJuT1U2OH7CPy9RnVT3M5FCnj8/JxXkYeLbZ/cCa539NXL0Zs6+xMKlh+IopWZOzcYwes5hnflRY10XmiCGuZnqWmdHoJAK5mq9+KZ4vMS9ajLpMtyuDcV08B4gNLlCcecgRNiD41XwhJD8zmPGKqnn+mlFG2QFhlen2ihL21d9qJgCgXLcrAoq/2VFj03qV60RGvkPV7bIuuYn1vu/bt8jtx1Zmie3+vTvwLddXx5n0Y/e+x0fWRor/+Jhs1kTcfxAf6/wKbtv9NeJupmn/GUeO2Jwz98e/NjJxr+6eXiIeh44//gfrN4HmA5w="),
    '0f01': (50, 76, 29.06, 25.54, "eNrNlluXoygQgEdULqKiEgRECAgm//8XZu1M92zPQwfztMuL4Zz6Qt2rHo//6hDIUFG+ARiC76ks6vPESmm6UYRPA8n27H6HmNmzxG4ZwhDBLpwlfGouxS9Y7ONZYtHFr4+jTxOPBjyJ5g33wg8AvBPBtTwI8QYwXvRlusDirPymbFMctgO6nnPvGpRjEBagckr2eXmAFseDtdFQ4ZnuQU41UkG+Ug6nqlqGtRr6snqdwrDq4JGEC60qWJYyrSVBr1/pIQRkpYMeMcEDJstRJdWruDiNZukb5VbB+cAVwSNmoB9+JsKVTlbzFNXKDyaCngiGFP+ZiFeBdyfC5hTn46wGTLex4y+I6xWzVY9pU2FY1sUrgvyM1IugrFdM9pjmMPiGu960o4uECvozoR1u0576nXFaDyzVfBEY8+aVr8rCzFvYfPCz99eoHSkIf+GrrgRmbvcYY0pps5fLjOFUV/BnYjZi2vyWpLT7nmLcPe3oEcufiYmyGAXTofdaaRF1jHJEBL3IQ6n3NBNvRs/noI32xm0GVi/sGHGTRNJLw4dBUNEmpfmydpn25mLY05aO7z4qp040q+hd6Iwzi2dSr8OZMl+dctyYXlOl9Kk6d15sh2yz0HFuTwAaUikLMMMO1Kwsqjwx495PoBR6wAPCJckTticFHvq+w0U9QnBiTsXIQDnVdRICoqo+YYhFuJeh7XRF6TzJE5NNVi1kGOMQJUGIoS4HiDQSWtSA7poek1BX2RltZdvVtRwHPW2gRMwQlhmzhhI5GQS09n5UYiR9xhLLOtFRMi0P4wXpaQXKjCF26vquAuiYmV6ykYphopn9YoIdwcWHh+xiVlu/rMDnG2M9U0TYdJSXlc4Zk90bzBowGMffi4BqUO+yBcWYHaqnf2w8Gi+h2XqKmycT+034mffZSbg7XjX8OcqDj6sas1N9W8gxnZ4/lYuLENlCj06w9vN/XdyCm7PbWFBSfEpte7LZZjL5bTVfLU2GbTM8R4i4rfNnmBlNjiOQy6voTTF97nJTh1GfWcukxbguPhuIDWugeMpsGUwg+JV8ISS/MJhJKyqX5atHrbMVCMsMUVHCvvJbLgQAlMt2eQj98Y6c29bLXJawb6bq3mw217Hut9v+50Jvx5Vnif367+3Ab7m8OmTSt9v9Fh/5N+JfOiabfSJ+0+P+PK9LcN+vt+9aZYmrVuotYndOXR9/a5Wxe3MuvUU8bik9/gfnH5pF8xo="),
    '0f10': (50, 76, 29.06, 31.21, "eNrFl9tyrSgQhreIHERBIIqiEgR0vf8TZkx2klq5GDE1F8OVVPnZB5q/27e3/2tRpHBR/gKYKXkkWFT3iYXR/WCY3AbSysXjgYhY7xL7KjBGGIntLuFT/VL8QcUu7hJ2Kv68r0neDoSDP+9M/Yv0oncT4DcnOJUn0f8CUC/Ti3xBxd33w7jW4IwDsOVeep0fF4FQAaAbB55/H2Dr9bauaWW9lwsHOdcYRHphGikIbbfAjpcQXme1ahFLu2UQorK0uyspvrbSYgTowrpJEko6Qi0uILw8l4kq4+vRLVrrTo+ESCJgdwFEJ9U66RTHSfdaR8BZz7teXyDb1O5Ob8GNWuph7AgLUl8Bb68jXCeZwug7u1g/Uryxrrs8vbVyMQ0j91Q7phvlPBouS9i5Su2JSaybqkNNoS2C3SXxOkFmd+2Gbey8Wdq4VVhfeiUAc/rgjp2hb/XCDkYQuBSh1S6zPhan43iaWfghq5q0V4RkNvYxBh6n0emgg9OSostCrOgpoGGWXvfbNI+qrDC6VFPeznaNx0J11/Wt2mfGCLjW3znOe9pDCmlfYjqSF+ucu1JC+ZA25+Y5ppSiv3PNF5eOI6Vj98lOt4Td+SEFn7aQ0tDc6R2YraoARg6lOXvIDZnrKYMS064oypMs0Y0wvARoJRWsYF0UTOWJWCmmKKEI1YTQguYJU+EGgIJYURIFwY1euAnMien51JSQYngjWZYYqlipPRIVxSrvlRW9Mk3b+ti3xjSiyjbcM2wOgAohRAMAE1U2vUY0DAJKhkEIAKjKNvXNtOrMKbDnY4Sw7eo2g1gFZUMZPwNeB9qL83a0maoauIdFI9lpY2a8whXLtWhj+oFTfnq1zn7iSmTT680cCEB/Ez14irOzSUinfMzmIwspaD1me/TmmqrWHxW7RU1JnZ004txRoj8+7PaRE9JmCWckl/LvTfGaX/eCD2JTwzB+Kn2ctcx29OSs/YrWngb7bBwhnlq1fD2HZckR7dmivPssJRXDvDQZNVF98E7ir83uJpIZezerLC0+z3kr54WiXCVOEsDKfFaMR5DRDNEqYVv1mat1DYEgmFFEMZitJ9+EMTLnFaS0+R5zDekxZdfEOjOAv4mZFwXKXBC7Cqq+5UPIhpnclTqO+DROnn3nyFXJY9/3p91jzxLHsccn4njm/8XGD+J4PG7YiOnZq2wc8RwxnuM4Yny9/rtxr84dP3x8HcdLn86eHH/YOMIaLuM+1/H4uX88/uvf5T9H2ezR"),
    '0f11': (50, 76, 29.06, 25.54, "eNrFl9typSoQhkdEDqIgGERFWSDoev8nzDiZJJVcjJjaF5srreKz6dPf+Pr6fy2KFC7KHwCWkmeCRXWfWBjdD4bJbSCtXDyfiIj1LrGvHcYIozbcJXyqX4pfqNjFXWKeil9/1qRuO8LBG1H/ILzoDwB+ksGpPAn9A4C/TC/yBRV392/jWoPTd8CWe+F1YXQSoQJUbhx4fj/Ak1dhXaNl2ncLB7mjMYjUwvpKQWi7BXa8hNcljKFANO2WQYjK0qSlpPjaSlshQBfWTZJQ0hE64wLCq7y4CWvj2egW3fddP1IiiSx5928iPJhaJ53iuPTnioAzLfDY/5uIXtPd9WHzYy+7YeSEBdH0F8TjcXbRJNM2hm6xsx8pDgMeL5KyPAg9YjK+87R33DbKRco0uyAcadOe+C56VnUiVf2sMe3rq1iVhR2204/gjfePuDha0P4iVrwEdmj2GGNKcbMvLwNBZ/bRv4nBarWtWxrMeuwpxt2zllF6oUKKibhpMW3cTeOk4xjjoDDFF+JpzJ4G6hbp9BAmO63WbRbBi7KSpE56n+fT204z3SQ96nlpM/Lmot/Ttu9L3OXkxhsqHb3bWuvsHMQ0Ld2dNl/c6Hpr+ciGcbwl7M7rbZqmemZybO7MDsxWUwAjhxIIWNyQOU0ZlJh2RVEqWpQ3ps7mJUArqSCCdVGwG2IdK9UISilCNSFnHeYJU+EGgILMvCQKghunCgK3xAx8asqKYngjWDMxVDWl9kichGJ5oFXKsLb1m26NaUSVHbiKKQ6ACHGLBgB2Sl7Wcd4wCCgZBikAoBLj3Jg1rTpjCuYzBBHCtqtZ5lhWQdlQxs80LAPVgoAy0x3rwD0sGnluCwvjFa6YzPlhtOGUTyc8h5ErkU26NzYR8BagmQ+eYptNeXK9tObvY+j7MTujg2tQ3b9VbIh9Ters3STajpL+7cN+P8cBabOEM5JL+bdTfM+7rDTEoIbhXQ9ctL3MTvTk5vnD2+k0qPts08bg3PLxvLmsYLU+Ju/es6ZisLbJqInSm3cSf7zsbiKZa2+YtaXFe55DuS4UZ1yfjQSwMu8V4xFkNJOQVomzQ95jta7bRjDM+CEGEzT5JIxRGRsWUtp8lpIhA6YZNVktA+iTsLwoUKZBZt9S8SkfQjbM5FrqOOKX62RKx56rkue+f9nzfO7Ha9bGHr8Qxw0b34jj+bxhI6ZvNnLEeYnZvvpxxPjIjP+Hc8e3Mz6uJ/SRwha/xeo470KXfp/reH5/fz7/69/lb35I3Ec="),
    '0f20': (50, 76, 29.06, 31.21, "eNrFl82SnSAQhaMiP6KCMCoiMCDoff8nnDiTm2SyEe8qrLSKr2g4zenm4+N/DQIFKqoXgJXgR6qK+j5hKEkHRfg2kGzPHg+Imb1L7JYhDBHsbhM+NW/FD1js7C6hl+LH51jE7Y305RfRvHC88BMoX1FwrU5ifAEQb8vb8AaLu/M3ZZvi3HtJdbgFOK8cg7Aoa6fmPj+/RKsTwdq00tFz05e50CiA0lBZCwA0d4D3FQDXpwo6SNOhKQCwqnQyFUHXq3QIlsRQvgyYYI6JRgUAl7osRMyeKmekklwqjAbMAb8AohPCLmOKyshRylj2dOz5KK+ydul2J8PmlRz4JDmm2yCvgI93BewypE0Fro12iqBAOb9Uz9Yupkn1gUrXynZwHk6XKWxcPe6JSiRpPcC2kBoC3mSionqXbgqKu9nRGGokL6Nipxry6B11Snpq6EExLC9NyK5mlYdxMi7Tpkz/4HWDuytioDrKGLc+LsrJTW5ODg28TMQanwYa1sHJKSxGiapG8NJNe7pqmw5DJOeSin2lFJfX/rtGe6Q9xS3tJp4fntk1d6WY8FsKzq1rOkf0d675esZ1pHTsIS3qlrE7P6XNpxBSUu0dC8V0FmU1jrqcU32n7FgmqMCwKctWzKAENwiMNaHkdKySggKRG6WAIUhEw0EBSFWw+YblUjtZVGpEGkzqCuY3LpaO1MI6UFNMuiJPCMoYKoXfNS0BA6jNVZ1OLBSiosTetjVAgHa5yuY1E6TFVDsLSce6oSKZRaJAFle468KHH+lZbiHI7MQaY1vE+lOGmdVACFRn+gC9MrENiJwpHjcAGo6aLifHtjkCqT6JGWN2OnWu13CBQ7p8KW2nAc8imybeDC1W7BexSISyXYB3Zuz7r4bEB2OVylbC5Iwep69SHqNCTZPtTZIZFzWaX+KMLUQ0R8QYzrieEfqh7bNRhZhS2J5EXNtrn/5ykm0bzVM0HZ2e+sxNZ4NfZvhMJeHCvOJMC7QFWtfls9tbQfITzGjuFzGPVj/TsiMYkgwhxKzZbzvwfmpInYlqrkln/5jzvG6CZAQZDSvp/DvBBTrdDuYa146J6c/JkaIAmTXmEBfxN117QnMWRx7Hsf+tGY/zN6f549i/zTnxPduzH/v2D58j9hTe4zfiDCsT0znS8X2NY49Z4vEvcdwgvkX+2J3JFc9P5NvvER2XLxGPw9n42jvvkdJ/eF3+BEPYAlw="),
    '0f21': (50, 76, 29.06, 25.54, "eNrFl8t2pCoUhltELlKKYqGCQiGg9f5PmCY5lZz0oMWMmhlr8S329Wfz9vavFkUcF+UPgIWSZyyL6jqxMrofDJPLQDQtfz4R4eYqsRuOCUKouUy4WN+LX6jY+6uEVsWv96XEZUda8EHUPwgvegfATzKoykTIHwDiru7ijoqr5/1sapB8B2zdLgF2my1HqADQ6qnLnwd4scNmTFiYdP3agpxpFFaDZUMlIFy6FXZtCc9LGEGOaDz0DUJUlnpfS4rPb2kqBOjKOtUTSjpCNS4gPMuLVXicHJvtOg9DN8yU9KQD7Yn724MJo4YY5nWQ3RBAS2WL5+HvRHhIGlOovH2/Yxw6wjxvhhPi8UhdpPro563Tq7YzxU7iuT3p1gehe4ij61w92G5phQ2USXZSgJbc4h7bnQ+s6nmsBjViOtRnsSqLZfSbd5sbN/cIq6UFHbqzTgLLeNtDCDEGv9zvI0Ep++jvxLRI4Y2P42T2PYawO9awlMuTvmA8eMnV1jo1KxnmEKYeU3xSh5Pa40jd2tth3NSijF69RvCkrHpSR7lrnbztBiZvMd2k1yYjbza4PW5xX8Pez3a+oNLB2a1Z7LI4rtTaXWnz1c5WLks7s3FWl4TdOunVPNWa9ep2RUIJmwQopdQAiOrKs2O4YIKgGgBGCQTwAoGJpozURQEYLDC98BRwjIioe1hAWhbtdCG6zIwGA41pTWhVorxGC3WjlTAWVqkGmyJPcMY5BsLtmgHIIW5zCt8IxRAuAHGGVRBD1vCc35oLeiNM2xXXDW/6kmaetiCwIYA0jX9zI8WYI5jxxKyraTBvUxomXkEhcZWZA/TChU9tt6TrPIR1h2mTS4f3liKmEzERwlEBc7OGdV06/5FpI3syiWyZpB6/kfkjpGZUEuPsFODsKtv2YyDZttXMZ6L7mnvsquX4kegQZlzXPEusUs1y/S85ww1hliNC8MmuTwv7W5u1yifJ9f5FhOU2ZMXEey8/JU0Hq8c20+m8d2pCr1Ka7DYtJDMCeceqCrymvQVGN+bqyikxSbO8yrKhBNEMIcSkOX/JgXFjTauMVVNFG2P01wvkRa52xcIBmz4PCZzUDuUGV87F+BU5WhQwk3TpghL/l2tLWU7i6PM4dve1faZtLufPY/92JuF7dmY/Dv8HnyPSC/gI34hkVsamtOLx/Y5j91ni+SdxhDzxzfLnngbAt7xd37ZHsN3wI+J5WON/9s97xvgPfpe/AZAJ8cQ="),
    '0m11': (83, 17, 0.0, 0.0, "eNrtz8FOxDAMBFClsWN73TSNEbTAthW7bfj/LyxFnAAJZY9IO0dr9DTe93vu+beZ3+q7vSiQB/u7tY1rPfloMQTnABABhD5PIr9aZVzfq8kxex8cJyGH0nhHfctHfq4830B2mT0fknQs0SZgbUlD0PY7Oa+lmnzIqAqNkJJ5QNCcJBEGVsTQAH79vV1K/cpZvQiDQUwihJoATdPQswMn5Fs6vHItpX7k/nwYbGaTTZwC6ETCgyVqRI6dBP56npfbyD3xyV6kf9JTFzVyttwNr4IgEmKjHpYyLltZt3rxAx/JlLY="),
    '0s00': (50, 76, 39.19, 31.21, "eNrFl9t2pCgUhiOCQKGIEBUPWMop7/+EaTpZK5PusUpyM+P952Yf+P/N+/v/8TFBKCp+ACghbgQAZGMm0PdDpw4EEfaZxCT9W4xSNnjMJI4xxBhNIwuWSQR7LNvEQAFyE6eG1wzJl5eX/GK93qdi+RFRgNfyVvyIeHm5WV5kE+NYJeQ1rNkR1nUcluoHR3KzXpXQhOYC896XqIBCmdz2ublGCJRQqzygi17KkhRlgdaszPvNDz2r2iJF6UjOWCm9j27TigleyXrIiML15sOmlOC643zZrolhXYO3WiuhGkEGe03Ybduc1ex2U5QwlXEHQ5z21akbJ2pu1Obwdb+DS6dK/8e8Uf1uBbki4hac9ZrfbjXnSrue8wvCH1NQru9xgTQWRAt11RMbFt8dS4kwc1jQMK3+kjjiMJmWAmbFrKye9wti9yEpyVwXBej1AKjsrjLfVuum3vdNWWAAMARmGeV8EcVtR5hbRtJcEQSPrjY+BU7fE0lct1UvujfOmCXugzThgvCb0kpPSun+9xD4YOarXHpSVYxRNX+kHePblZJQRGHSXFhQ+TFq4SrC3HWClIiAgncfzbgiFkm7FqFGlqjkc5YgGkE6WcKKDlWz58nVQGoKIYJ4t1OWQVFZSwmS/FQsGJNlmzUhmJIWMW9Nk2NQFI6owhQh03OYQUxJEJBEhMJBTJJdz+77yAAtIe5AM6YyS3wti8dMEClbgsdE0GW4rNY48AbCtm27g1Hct6W4JNYp/dtUzFjepKWBkKu2z0yOE2677t1IpTrcDBcussyyLIcZ/za05CNdgzvxPPdloBwJ8SHpvTdCjZzWT+/4KtuBkNunZ5pVC0HEs9xlN8mW4qr6FFvne60Fe5LI2KJCSoIo/yocp/zWP2s3BGiomFq/JKKmZjseC+hSAQSFmL/MT9RYJk946By+hawCSn+zOJyMHQ0PJaQZy5TJd3cNtKSSogcT36qB1riSf2odBbIzDy77WGNEQUX/0lPWju3yoNuUENT+te7YnjXr3J4fKkgIwN82uZiFGlPBU1c+VgnHfxkrnZaWQnRGvEV3306KkmamrE47EkN0Z2v9sR9Gnwlv9He9nj4E9t1F50/2tnQm92AniE5/hhffNqGw+ugebEbRrfe7vW/6Vf8zlDEZckz7xYOBsy49FZLT7f57Gj7Eu76fE9vdJjd0Pvx52JS7OL+gTm/7kaKc1HdPi9hpHb19cODo7WxOq/XYbN9y32b/xfcLORYChw=="),
    '0s01': (50, 76, 54.2, 25.54, "eNrFl9uWoygUhksFhKByKhUViMoh7/+ENfbU6u50tUmomxkus/Jln/+98/Hxf7yWYwKLbwCK8wspS7inTKDvB6VWCGAdMolJhltKTLb1mEnsY0wpWSoLmknEfVvcRMuizA2c2q6hSL69veUn6/06Fcu3iKJ8ry7Ft4i3t8veFdnEOKID6eI124Jx47Cgb7jkF20U14TkAnbtK1QArmx2+eYGoqICWuUBIgWpACrKAhqT1bYujEOLZQHLUuCctlJ6Hf3WqwsXUHZDhpVOuxCd0g2fRdctLsMrY2LcjeZKtR0efMZoOOf8ri+Xi6oxVRkzGNO0Gq+aDvdzq5zHr+sdfQwbx6jumNDrrrBS889u+/3uiOSi373mNW3aTvW95Gy5pdvt/fcLx7u3seuofM/qAoialmU7i14u6Z74GnlcgtinCkBqaIUACj4+F609bmnQltUl9RWmTM3ri8jXcJRjG5uiKAlezabEq1w5s/tpCAMFlXRbv6qMIdl2t8V1Xtw26SVTRTfjjO6JMsuSOVPB9VrNk1K5M/XheowQpRc1iUwlIZCAQ3NBQWSehUUIjitIyqJjaw6xSCI4hK2sYNVNOcRgBWbyaBPSozbLxrwOmGIAYFXbLcvGRmQjZVmAAtNobdbabI7NjGoBSfC2zSAIAeMBYAht34EMYiKYQokwBgOfJJWvizjSklSgZmU7HmmW9WtZ3GYMcMVwPR4EseP0ej11LYCMMbFSUves4i/DMNPx2xZRu3ftcTRgMr+qH5XjVDMhPqxUStTt8KLjl1lW1bDUP2Y1SCnaWvDnsS8j6SDn/0p6HyxXIyPNUyUxkg0YXz7lwBp99D1/FruUszzyitCnPvugtOb0SSCjgIWQGJLu5wemI92lf1ZuWMIBUWV+SURDrNseC+iCSgg4n38tP9EgSdVDGz4wSFGl9N041vCH1YcS0o7VyOB9iSOpiCTwQcczNZCmRn82dyClFPbBsI9NfQgOIl/0lLKRPdDShWAM2Rcl33vamomdOxUlKMuvm3W2hliLwOlWXhcJxr92MZkWRgA8I27JX91JUkgNK3RakRSTP9uQ27pZHc+AcNXmdKeum0/+71UV/eHTg6slJa8/zfO7SyiakPyDyyh5c73uV6ff9e+mTHG/puO+eNBw+3EEJMf1Gu7DCDFd9flF7N11j8c3QvzT2RSv/HxAvXbrdlg5ye+q6eU0j2F/4HAK+2xPs3V7OIa33P9m/8X7B8dx9vg="),
    '0s10': (50, 76, 39.19, 31.21, "eNrF18uinCAMANABRWBQVLgIKlKVx/3/L5zSx7rCqu6PSSAG/Hz+x8MmQhGoAHKa3gRCdKdCoNQyywu1CIdCsYrwnZIQA9aF4tIxpXQMArBCEe9rdyuDAJYWTg/eMyRer1f5Yn39WMFeJQD8at6gSrxe75uDYqF1l8lXtMURrNXL3lWk5Ddj5WQILQXbqRoE2kkepdvntx4h2LRGloE5BSEaAhqAbFHlyoVFsW4EOcpMStpKmlN7ZySbeCf6pSAKNy5EJ+XEzcz57p7FYm0MtzFyksNElvtZ3M45fxv2fktKmCz4BmNaT+vlmxO5DdJ5/Lzf0ees8vsxH6Q674k8ieSiv4Ph73fPuTRecf4gwrVG6ZXCABk8ETPJpz254x7ma28QZh5PNK42PIorLesxUsjuaZO32c4HcYaYJ8nWAwCVWSAV81Plzt5+VUENDcAQ4hYeuxbbQxTvrriNjOS+Iqi95v4IOXB+/jESrbNmN+rwx7GncxFHfBDBSSPNKqVRv5ogxGN7qkWRrmOMyu132Sl9PwCBG9LmmYsA+z3a/5XO39bSWuB8dkCA+z/d+bjAo+i7lo3dPBXOn01ozXNeBLaqTJyCED6jFrSAlAlxnB0dRghnpEqPwWsbNUIdw6VjdGW0HWDTdcXi3DjWFGNISsUxMkQIG1nxcP8IMmAEBWPFQrOmw3QgvFjYU+QuOTtdLC7FxYgF3YrFalctxFhe+GcbCMWbMuViWVWeopyUi3WZscComz7lmy40w4QtxcJ5JViHZXlWI8Vq7LitEBg0q6xYKpGnCaQ1Ia78OWFQEeJzq3x6sLlCBKUbgYYKYTkZGlSx459lFC3ra7JaaEMaiivERlHToL5C+JBbV1eAj7isdb7qfyVf83/EOhFvWyfivboqkbzP16waEp1P0RvnyoW/fUr54pfvS6WFh3xLCIc9jqN4rdJ3/vV6Psgrnp9yANz1"),
    '0s11': (50, 76, 54.2, 25.54, "eNrFl9uOrSgQhhcoBxeKCo2gIq0irvd/Qoebye7MxXSRTDJ1/6XOP8Xz/B/WDbwhqADQw/BuMCbnDQSMmbTeSU3YBSRmdX3uu1cds0DitOm+700oJIBEOo81zAIjDE1cbLIVVL1eL3ixvr5ntBYRCH9Vb1REvF7vUyIwYS3NiEzfYA8+2GmlBSHF1Xk9uKaBAttuKorqQW/g9i0toaiqnYYB430pXVOEEfEeNLbhslPHFSIYjxwyVtrtNh5Gv4eRKDkBvEgXrhS0a4dllHINgKi8T+n0btC6k3yKgNUIIcTTvd9vzbjQgB1M97z7qFvJzdLpEPnv/U4xXcfAKZP96PZTc62Xv6ftj/0g7pDiGd3ARNtJbYwa+vVzfz5ff+zK9tPH6ZKOpmeoHpnAuFtGo9b7J/HPzNN6jedc1UR4UdGaXjH9u2id6bgnt/UMi1hx0etl/yXz/crtOGyLEG747g89/lar4M84T9ck6kqFw+wasCTHGY60L2s4ZrcCVfTwwTvTaL+uwJ26gnF6mbWG7tQTDKdUiLeeRxigWMXrrLkECQWUEmUVz28HRqwFBtWNLa1FT/sBqD+LslbyquK4NjBiHzmXIyGoRhyY+bbTpmuzlhCgj2c5FqkwJYJBZXQWoha4JgRM7MvAbMM45mCp7gTJQtILsLg/ineMYCUEmLB5X3nT8f6BvyAqT8lGLZg4jFQ9U80CJhbvrFI9PPFn6VnDZufghFkMZ7LlcGKeRqoYoQM88zzwbe7hBCZCNEowpuFR9ZyZjkpfQDBUzbqgVCqrCW5KXBw2rwaaC67dU1H2FmMBcRlbKdIVEF7yriIFHX+mXtVdWxKVbSpWNayAWBpSVaQtIOKVR9cWAI86vA+xhHjymf+dyoh8L5UR6XShiLhjzGdWCZJCvFN0IcCJeF737fQgpYYmni+odG1+2zZwrfINlkt8f/67H+ZfikvRaA=="),
    '0s20': (50, 76, 39.19, 31.21, "eNrNl9l25CgMhuMFA8YGDIXBa9lsef8nzJDkdE/S7So7VzNc1qkPSUj6Jb+9/ReHcIRB9gNAcl6jPAc2XgSU6ju5gxJAf5EYhH+NUYgW6ovErkOMcWlFRi4Swe7TOpA8y68GjhfaECBeXl6uP9btPmTTj4gsvxV19iPi5aW2NLtMaF0l5BbmyxbmWfdT9QOX3GhmyQ3CV4FxUwXISi6Xq+lzYwNAXpRGXgO66IUoUFZkYL4UuVp9r0jFsmSlQ1fKSppNu9VIwmklmv6CFWpWH1YpOTUdpdN6TvTzHLw1RnLZctTbc8Ku6+qsIXUtMSLyQg+GOGyzkzVFcmzl6uB5voNLXqX7IW2l2ixHZ0Rcg7Pe0LpuKJXGKUpPCL8PQTqlYAYM5MhweZYTGybf7VMBIHGQ4zDM/pTYYz8sDOfE8lFaM24nxOZDUpKxybJcmT7HojuLfJ2tG5RXbZHBPIdlvkxajCdW3LqHkRGU6gqBcu+axSfD6TyRxHmdzWTU4pZlilsvlnBC+FUaaQYpjXovAh+W8SwWhaqKECzHj7BjfD0r36pAZdJckGHxUWrhrG3nXlCYUliAsq0+kDMpuStG6gKhAmY5u9Lp/axYKyCuqgxBdIWYpkGMqunTHCTXCCXGNM4gFhXDGLRXRlpQSz9jolnKe06veLURpZeNJDMVIhcUa1uUYGOPRKURxlScy7VbGk36ZewAKTLCy/P3HVK8lPAxGcAQTK06NTGneAnRQrEcgYSB07hFp9KAYlVyjLFeKHUipJ33SqQ+UurNap7ab+D1iTCMmiKoyuF9fk6kyjEBzx9435VZ8q7/mLiigQyX8GkSnTaSsl5+zjM9YiwQeqYmcpzoTHFqv88hPTKNUPVkHNqKsgYrXv/yfO2Vhtg8qVoIsNJNI3/9Zx+rSvHHNtxetjmZRvM7AwwURS6Hh5qz8ZyVlfmSMSFAWWTNw6KdWqYx2b/8JDpYYYIfFGOretxYVn1/C1KS1PLHBJo02djy3em9FwDmD2bhANUmtj+2Va8IxuzYK+0UQOLP25zpSVkcG/H7TrOi/Eu8cMmK9nBtisGa7SBEjQGAh30YXTxU5N3v8/1o34/v28WhIi+7jwdIuFtnH2wtr9Ea94nwr2+yOnd/sEWEdTXr/W44kb8L4jVsq4vOPtr70+B0aTldviwD0e82xvlYNsI9hBh26+N308H7200eE9b59D3yd4Tvq9vtMBDvH3xPJd/WI8eO7v/3urf/z/kHi90DHw=="),
    '0s21': (50, 76, 54.2, 25.54, "eNrNV1t3oyoYrSg3UVEIgjeiCPT//8Iee7o6zXRMQp9mWHnKyua77s3O29vfOHVLKMx+AJBtW1IAoIuJAKV6KVdYQOwTEYPwrzFyUWOdiHA6xBgXJjKWiAhum+zAQAZSC2dLUzEkXl5e0pt1uQ7Z9CNEBi55mf0I8fJSuiZLRmiNDkgTrskRZqv7Cf0gpX0ys2wNpamAZVU5yopWLsnjGyuIsrwwMg3QRS9kgTKQwXlOWlvrdV8TkUEAOpKyVtKset+ULNsOiqZPiNIY64OVpmrHrmkmm5DVPIfgZtNKWTek3xOoYa3dnSnLUmLCZAIHQxzWeZdVQ9RYS7uT5/MOe/BbSxBueGdWJ4mU4+e2fZ0bRLRhd7tpMavqRiolWj69xtfXy9fxx7mN4UyQu+I4KzrMAKjHTokp3iK+Vx4m37khLyCbWY4K5PfwWLRc2GJvFo4B23PCuBzXJ5Wv/hjHpqssA5Ss8ya7Z72ys9uH3vesyIXd1CoTSLI5u4V1nOw2mClRRbfZzkZROU9TIqe8VUaOg5SpnHqziiDEWCmHLg3Qo5wUh+bCjIo02k5aNDiHx6fgKAUxWiVYmROS4wzwpKRmxRuBj1IygpMka5oGMaiqJwAwRJLURIyiIZhxhBGFdcr8glrVTNlIOSOgSslqZUovK8OYIkITFGtdlOBjTwTShFIunte+L5Vm/TJ2kOUZa4vn/R04JZy14xGAYjjV6vnbcSAY053igMADBp/WLTql1dTgIzHOeyHUEyHl3quOwEKpwzi8b9jYls/8hT6mp4rhXdEmhgBl8HGDt02ZCXT9/xooKsJpgduHdWsjm+awSh87OVIqCHlEKzlMzdxQVn2MbR65JgQ9oK5DDa+oasvPzK1WGlPzgBkY0r6vKvn5m21ESMn7Mfa1qAEdR/NrAhzlOZDDXc1ZW8ALZG4mJgQs8uzuwq9TzTVl7uYr0R2kYvTOMtaip5X7Jh6OFeyg/DmCTpqtfBl/H2gvIAb4zpZjtYn1m1v1ih2sOs9K7woS8f223bw/C+dB/LbVh9/5Y0Ss4Hl9apticGY9KVFTCPGp/EYfQzhbZr/N17OnMzp7teGUlFcfTyDh6nbnzpv4Gp3ZPyDtbU8O+3LHq8ZgrbHXq2mZ3H5dE1br4u7uGcf3F/swp4u/rXtzMc7nshGuIcSwOR9/Dx28v7SX01EdRfrj/8ifFXpnzOW0EO/vWJPDWNmzxM7u/7ru7d85/wHEM/d6"),
    '1b00': (35, 52, 14.78, 21.28, "eNqdlNuSoyAURTuCXEIUgQFRlChG8/9faMdOpfqF49QMT1Sx2Bz2uez7vy/6N6BHuDiHVoaKC2pPEV0zRMczZBnGMdSnKn26FuiPPA3m+vX1Rc5/JNgr3DMgKckRZrGHXZtbgRQW1gBCFedxHBrbpaBwgXMILxVPZUn4pSMcZXV8I3nqeE2NwpQ1OSQO8xQHq5y/2XbII96ZpfPWWV/WTRbxPqRl7bRdvFbNNatidNzi9HJl9tzWOcSJSW3JKxMfvCHZLITm0W1zjL5blSmzSKfTtPl0j81qQl5lZ1Nc5seymGBNAabRKmPrWjRwplurKC0FwyARJCsxlwQhsAkWKyhugyQcLLz5qLnWioopCHGyEiT0iTFIZUydUM0UXiBieaRTQkvhAteCgogSldxT4Bwwd9dCUVztXS8ppGJr8aJe9nBKoTZpNbsdDmqJNGALr8ojO4uWNYTUmh/FFjXFFpocFT9sHQS5AInsKSbHaBk1g37kCoyO2047IfLIxEv+cxSwAFRmScntR46SEqgoLd7d03NoaLobeevrdXJ5RJakeu+2+woMXfMp2TXGPLJt90+zmJQnno8Psq35h55b9J/t8znkmcf4izyBYH5pCPn/9Q1/q1I1"),
    '1b01': (35, 52, 14.78, 17.47, "eNqdlN2WoyAQhJOA/IiKYFAURcWo7/+EmTiZnLlY2j273PpJV1c1/Xz++6F/AzqEb+fQStHtippTRBcM0eEMWfphcPL0liakN2TkqZj0crmQ844Ee8k9A0IpOcKsd7BrUyOQGkpdARfljPmpL80WnMK3KCSI5CFJCL92hKNbDLFFyUPHC1opTHkZc80P8+T7WhmbmWbKbKSb0bTV0lpjjE2UqtI/Ed+LKYTV6nqxumNFGtPCen+/T8x3s61xGe2omKv73aqqf7CS4QhhdP1ol3H0tl2rKk0iSXlZL/Nmw+jL1XqVsFglHvwyP5bFdKZmYIxGKVMUooSTro1iNEmjWt/HSZZgLglC4CNYjKC46XPCwcGbj5lrTJZzBUqRuSCuDYwlADGEVqhyci8QA023OtdS1I5rQQGkU0rk8rk4zgmgVwtFsXy2TlIC3GIKoQ9jHaekg56rZtlRUEsEdD1xmRzPedGy0ABSaF4cY6EpNkDO/dvWXpArEGRHMTlWy6AZ5Etzw+j4u9a1EJDchH9/clgA0zC/LMu+46QEyNFpUbxFcWhp1tmP72adaiCjhP6o3MY1jmzVR+TqPYBs48fEKsSJ/fFBtjVeaN/8Z+3s+97Hmcfwi+yAmF8aQv7/fAEfAkkN"),
    '1b10': (35, 52, 14.78, 21.28, "eNqVldF6oyAQhRMEYaQCwqIYlShG+/5PmNZt2r1h3K9ccfEznOEc4Pn8/eD/A24FJefQJgpyLbpTxCpR8OkMWcdpGsxplVuqSPFHn4qpLpdLed5RLciVngHJGCioiAN+aqmVRUOldQWyB8A8j43v09BQkt1NlhoSYyVc+xIIySHBaFhuoLhrKBcmh9zHZY5jaNrwZrsxi8TQurUP3vtQKpNFQjuktAXr12AbVWWrOBv3uIjYpwBO5ZBWzm5Pwbn4EKbMhmYwj35fYgz95lwe6W1a9pDu0WxuKPNeijmuy2Nd3dA6gpm0eOf8m5IGd7rzDRdMCjwOk60o5ZyQQqBxkcCugtCCovfkZqSqfS8FZ2iVqdbN4hWXClWrtTZTaznFEj62Vlqd5qnmDBDENLwQneWgGdJSC7KD7rna2+fNRqRYC2CfQwcgkK5ta0Eelisu6jzSS8nsoQmAIHLnWlf+iJ9V1CPIoEU4/G4AsCrAxLF6PXrH3jlOj9Vtza+ISQMwOJJiLWdI07Mu/8pddcWRjfpOiVfQATNAvRZ3pUAQzdjXofYlReTOJbVfGeYEeVfft/trti9rHtl/kO2OIY/0PYt3BBndz+Oar7K/P77/h23a5qzaz/Fvuv/qn/sAbI5EfA=="),
    '1b11': (35, 52, 14.78, 17.47, "eNqVldmWpCAMhqtEhGgLgoXiAu72+z9htU5V91wMcU5zlXP4SP4swPP5+8X+B7Qkjq6hjZPoTupLRBecMHeFLL1zTlx6aec0IkZeiklvt1tynVHKD7lXwFwUQGLuO7xqU50R7QpdIo5y4H7sC7PPnYqjIJQlCmZKE7g3CZAohFghYWpBJKWKGS9CVfNuOgJVytgPXY8fNpDNUDXl0lhjjKWFKtN/Ed9n4zxvVpvF6paLNKSF9/7xGLlvZ1tREcxITOXjYVXZr1DwOEAYVa3NMnhvm60wQAOd8rJapt3Og1db6RXloUgw+2Val6XsjOFoG41SRoi0wDtdG8UYTYNaX8vplMaMRRFB40wZ0DuPCKHoPemKTHyYJuMJRdW6XKqpylkmULVSSuVqzWLMi6tkptU8upxRCCO9Uozww0kmKZJSBVkN9XM5RiE8l4cUrQH0s2sAOJK1qSRkZ+6C8Ry50FlO9akJIELkjrlOzYloERsE6SRvzj5oSDEvQPkZaDlzR1oUJfF52uTsjpS3AwrnpGjNsFaPMvkjd5UpQwI1df7aaTTHGiDeh6sEQySlr6K26DQ4Fuu3ESHv6uc2vK19WsLI/oNsw4wg6/fG7gcEseXP4xoOtH+u3//D5tYxqPZYf839V//cF8jGOzs="),
    '1b20': (35, 52, 14.78, 21.28, "eNq1lFvTmyAQhr8gcghGBIpCFKKi5v//QmuaZjrTsnZ6UW725pl33z2w+/7vj/4NuBcYnUMrK9Cl6E4R3TBMwxmShhD65lSlm6+o+CZPzVy/vr7IeUWCHXbPgLmRvMAs3uGujZ0oNBbaAEI3zmMYlPZzrzDCWael5KksCbt4wguUQ9xhZL7zmhqFKWtyyGOYxnFwyvpKd0Meca1ZvLO2dWXdZBHX9WlevW6T06q55pBodNziyKKfHDdVDmnFZLbZKxMX3pDsFHq1+G2K0fnVmDKLeJ2mzc2P2KxmyKvsbIxpWlKyvTUIHKNVxla1aE42qlWUEsEwSIyCMX6lCCFwq3ovlNWYlJSDy33vxU1e0LFVoBXFQ93yw04J/UQrKanTUBEub3nEKn1sZbCaYQRk6mpJhd6HgymAf91pJSqzByFuBOiukoLW7R7aIxOg0tdatEcMkkD9HfqWvxBPGRJA/2+Eu1fUEgNFdxiXLw9zy3kFJLqxuj7iJEkBeJk6RV8tk5xegAnYhv6oNcgSA6NWhNr3AbhyAAmkfJ+wXjNgRv066PfIsQC6+1zTTzlWAipbenxcsQlAovsD/j3Rtn6OeExDVuT5fH723MxrVuQXsoRlB5D9P77vmldRgQ=="),
    '1b21': (35, 52, 14.78, 17.47, "eNq1lN2SoyAQhSfITyMqgoGgIlGJyfs/oZPMbGqrdsCtvVhuvPmqu0+fY+/7vz/2N2AoMDqGNijQqbgcIrqFgk1HSPTTNMrDKsNaouIsD4cpPz4+6LEiAeiEj4C1lbzA4If81mYrCjW1uivSQM15mL0y93VUGCUhQSVfCaH81FNeoBTiGsmXgTesU5jxJrW1EJY5eKesq8xlrlxCzdX0XeydscYRpbryJxK8mNd1c9pEpwdoytQs4MP5PEMYFmdJk1TUzPp87VU33kBBasVG21sfryG4fus6ThJOBWnjcnfrNbRbFxSBVCe+hrjcYjSjsZC10Shlqla0eaetVYzREvJxmAUALxlCKJuqsRfKaEwJ49lwD6Oo6xN6piobbsWnxsJzHJIheiOByugrCo1II0ZpjcVkNGCU6XRpJBN690+myPzXF61F1e2TEDVFaURpwaTdJ/vslKnipRb2+Z0khYwkP2r+SmzPAGUUzTX9QmYtcZ0xEWPymmG1vKwyjRpoXndjkbTIeL1cNHutTHJ2yoxrWvaldZQEZ6xWlJn3Acgomij5PmGjhoxH4+b1dyiwyGz3scVf5YBkqtzj9T0VLBkkuB/wn43u2/uIh+iTRR6PxzvnXdySRX4jt+m2Z5D9P75PUvpIWw=="),
    '1d10': (57, 29, 28.39, -5.49, "eNrFlEFzpCAQhUdBgRBHhykUBIzSNPP/f6ExW5tDTkH3sO9AcfmqH6/p3vd/Ud4ugl1bXeIIF9Xtdp5bdFAH+LNoLgA3nxNn7XJc9XPYByb2PcX0+hWM+PJdVd/qp76reV2eUs8JCkrqNU22uk1m4FzQd62XpdswFXjVaSU1WyWlg2y44Vz2NiFiUUIKQTFlhjcu5fs9hKm4tbAGB4sZ7kJbuY1C0FJyDRvChx26rhX20ZK6KkRhXgATROUe1vSkJYQ2TRlp0wbgbYjzLBpJa0kIKfJqvIk5Dn4FJ4RgkjLG6hLULBkj5giwzmGUUydJKxhnvIBFSAn2fXTePmzXCyqlaL/+YIFh/3WO/RSCG7mcqBS0jPyrfpz0wymvRa9425wdOd2HzTUNJd89NamYDU6TI96G/Zkkn0+UHYM68q0BM36kU4Y9uL6749FlfJ186zHgKUfEfGWnvTJs+doahXwR/L/6BE99GP4="),
    '1d11': (57, 29, 37.63, -11.03, "eNrVlMty4yAQRW1APIogIWIkhADLvPT/X+hRMjNZzSTYWeUuoCjqVHffru77/Tuq8UlQ4PO/P+ZDvu7/4yBl59Pp41nq7f3218vlUj6JF7RXB/gRNMe67/vltz5L9OZqpgSHt9T0XOJ0Kwd4vX5ZYSy7FwCcwKvuld2Cjs42WaO3PC3n02wkIQy9GCqcbDNVZw8B2ThCknfUjMq69o6okkaizCtllIvQM9lMps27FAyXTI5WSsZQK7mFWA5yFAy7XmIEzo1osiGVnKKyatEDxBCgrmsjlxxScouPzrCOI0AhhC1gMM7EmqTb0soYIwITQkALakItsdSY0mb9xKeBQ8wIJbSBLSnnY8Ym65ZxEYIhzhkmrMnc9e2chtn7VVM+I85QG/lHwzRrtSqn2aAp7h4dcTX429p1CP7tqcnNrPMaHvZ25H2SXH0g7OTV4S9IpZZrfihhl9Ze9PnoctkfrdX6XI8e12d24V5TrM+t0VTr/QfqFwaNCCs="),
    '1f00': (35, 52, 20.22, 21.28, "eNqtlNmSpCAQRVWUpVBRaBEUbFms/v8vdKqmenkBOyZi8kUfTpA3by7n+e/R/QZwFuvqkrDz8sERukIOhhiE9gpZ3kBRQnmZCBRFUepruWVR3K4rGt4ABFfAJnhVFkCZLEF2sUndGCkyD0EMVz5QPIlWAFCmEExqvY4QAKxbUCUt1mSeVqMGoTAmqE9qJd7ETSux3YaViBTyDh07lBaL1s0OhyTSLYGT8UYQkJwlka1mTulllIIGiJOIxDaaSRkjxohqnJ4mI4M2ziiz97RJekv56vp+HFvbPWxMT8Jy3GM4zHEEvuSatLvovY8+38ZTr9Y7b2N+YiS1dcloZ6vsgOuh7DuGKwaaHOJ5M6ORMIJpNlHTUiT9A8klWveWQCQtBpyQzBJ1jI2N3ufxhnEamTtG0HTuXDR1JpNlHFbs3BfLcolmJhv+KD3qYcqs9Srn7mmIVzTzyBn3sZ8eX+fUwDLOLQg/p3oLixwyfd6n8XkUXHCbSiMmrOopYnZRZ8RM3tL2KZtJ2uSsa/9usrcLydzNjtPu1at14mmk593L95nUGS0W1/VrXQYyp5F78J8Z73efRj7u4evvyCLxG3GZ0x2PL+QRKSK8b/4XJG4m/CDpgmL8kXX+9/gDjxFU7w=="),
    '1f01': (35, 52, 20.22, 17.47, "eNqtlN2SnCAQhXVUhEEFcflTUEScff8nNM5MsnsRcCtV4Uaq+Kq7T7enj+PfT/sTwEgob5eEleMnq+srZCc1qYG9QuRHkeWAXyYqsizL9WUxXZ5l92tF9KMAxRXgBnbLs0KbJIHcYIQGRg1lHAAQTIwixAc8lEUejYHK0TBQFFB3RREtSGHJJ6MoVRBiGJO1GeinMGs1zHdqEKV/I8tcB7IrNUxaV77uImHMDLeN2/6OxoobONyjjZ3M6p3Ty6LbnEYVNXbdXAj7sjCEYopabB0TQnutzCoIjDBsHIIau67vu86pmcNYptyvPmy78WKKA6/ezHIwnAmVnrSexl40LcFJgmNb5gSD+pb8wTXNu5bCGymrFOJZJSFDBMFkJgkaXAt/IqlEk2sQqIWFxdndODISQlilnTxHmeiL7Ag6beYYq8pEJksYuJHDjbZLJZJEVOyUHjTlCVtPQrbgqV3hRJAjuL57On5dFSWJzo01HM7vvI2CJuzqeP9cCuu2zolZm21SzyLkGnSiGO4tbl7iBU7MUbbNy8nejjixNwl7vxg7cZbYUKx9912iMlGLheV7r7AeyTjy2PxvSz0ePo58PrY/tz2J7F+3NbG69y/kPFGfLbP/AQmz2b6RuKAQvss6/vv5BdrvS54="),
    '1f10': (35, 52, 20.22, 21.28, "eNqllNuSnCAQhlUQQUQUV0EFRwVn3/8JJ1qT2puhTVLpG7j4qs9/v17/buJPgJIBZ7eE09O3Koo75JCFJMTdIfoLJSnp7xCLkiRJx/t00yQp7ytqvhBBd8DSqSxNsLEgwZbODiOxpsNxoKBkVg1jfcc7hNIYQjnWc0sQoqZCWbTFI9P9bEzXGUp50URzZbsNy8ksZWNZF0MeZJOHGbt5HPOVRL08xOQVa0tWoEHJeCCs1mGe2rEVntAoMlAXbG/s0rWBYhpDWrkMYbSbNXatWR7tLVfzVtdtWzlBKImv3HQ8gz/scXg1QUNa97DvIewLPGkzu33zLnCQ6EtdoAJRl4Irs/dYU5zRNAPdTDnDWJS0yjCEbJwxoVjGcgZLUancUSUkhUTEFSNn3aeTHBCkU4qkwmqeSg4gc6Eoky8vBcUEkOI4YHUiticSyHdVTlzVnkvONZDLXleX4oMpG6B3fuLsUrw3jAKB/Da0wzWHta8rANmn/tLG4uehBira/dJeb9hG4IAovzRX57X2IzDHc6mzayEdrTlQkVTsfeU2y4DuCqHfyKSVAjaqyt6ne8gzwMsm1BvpOznEke/n8fH7QPzv3/M/EP/4CeQfUeK5reHHn1ujcU77/P6d/QKcEEc9"),
    '1f11': (35, 52, 20.22, 17.47, "eNqVlNuWnCAQRUW8UI0KwiCoiDTYM///hZ2YzpqXBifhqR72qlOnLjyf///6nwDBjqq8JDatv0TbXiEPRljTblfI8oEL1KgrxOKiKNB8XS4qitu1I/6BG3wFOClKVGBjswQ46aa5sUZWaaBpm0VzIEpSiTFK5oBKr2ODMTEdxsmCDGi1WsO5IYSSlK1oSVgPZ6RxN26B83dkd+0xPoyRy2zq0A6JNNaRGNU23m5LrTYiU0oDWt09eK/3fe4RTzrqtnv0x/HYdwGQctTTzYtpMsEaGyZGEoxYZJwXPoxjN3jjFEkpoejDER42mDUN/OmN09KqcTL5SZtlHudhYPmNUaBbTDAGlD2CoCpNcElQSbPLXUNV9TfSl1UOuVOAXkAJNeRPUYy1A9GxnGdNBTQ+RKigbjLXKkSDeqspYjRzs2srCLBnZENbZbJYPVVCPOOmGpap14uNnW71NlKdqSUM3Xnxh7nxTO/iQuG8+GiAZITifRqncw5eDV0GCYuSZ01xnYaMoxDdeNZ0+DkjJKLjZ8smHefMHD2HcjlbSHqaccQETK+JW5rpbt9r8dobLTI/4tKVr69b12Wd2ahevBAh2ZRGvj4fb9EbEv9Gnz8j2Sxx/xaKe5L4vPvjO8vmkzq/33v4b+8XlbA90w=="),
    '1f20': (35, 52, 20.22, 21.28, "eNqtldGSqyAMhlUQoVQjuFgRtBVQ3/8J3fZse67AnTNzmGHIxTckJH/Ccfz7qn8DJARcnBLT7bbLqjpDVqiAkOkMGb9QlhN5hliUZVmuz8PNs+xy/qL2CxF0BsydLPIMaZsk2NzNqie273AcIBUZby1jquMdQnkMoRxrIwhCVF9REU2xZjdl7NC1A6W8aqKxMmfCPAzdfGkt62LInSywPgmjdfkgbRSpRy+ZuLAK9RKiiMVy6fUoesE9oVGkp1OY1WBtJ1aKaVxNtg/aLnawc8PLaG65NEvbCHGdakJJXHJm3YJf7bp5OaaK9HDBueee05XWZnoiU+BpAqDCvKqmPCmZqZQVLfIS5zSJyAZwg2leJD2B5NTUJWMo5UhKTpBwvKgxqDhiADhREwMOJNGQRigk2GFYycsyES1MouwPB0VDE7do11772+F6RXDKkb1eXno0AwcWR8Jiuv55etu2iUG0uFG9Ot53zxaII977eXjV+yHaRAVG/7DwCtubIYEoIfD19Xg160RejKx/1MYFT9wCIM0fw40sMRoUf0+5GiQklMvgBwFSJFLn9vAep8GHOLJt68da11QB/Nva9ziy7/v2Mbcksn8c3e9DivkbyzD89udsLhz/eX0DqUBT7A=="),
    '1f21': (35, 52, 20.22, 17.47, "eNqtldmSpCAQRUUUoVARKBHEFVz+/wvtrl7mZcCKiRhezIcTmTe5ZHpd/36qd4BgW5beEmPXnaIo7pCdFaxA4x3SP2ECkLpDBpgkCTC3YjhIksd9R/wJEbwDJilSkEA9RAmyyEEZZLXMwgAqkBUNIaotJYQgmINkxgoEIe5LmAYFadq1VmvZaIwpDrXlB+zsNhktp0djSdP8jcxTsfFdG2mNyV1RB9IME/a+HfmD9LkasAxVqoGdVrcs/TybCjTBjspx9Yvf9nkWhIQ6qum4CNUaN+jBKYYDjOil131dc16Wi55aHKoEvHO72z9zWIljJvmpk0MrlI47ra2RqmYNjRIdZ0VGixSD6JMZc1HgFOQZiEoZRc0ylmGQRisxQbGt8s97ixUSgiLIV5JWkEXmxDJGkRoJowxFBtJyATm5LMmrPI+oZSPP1eV4WuFIFuOasuuuVbUoixWy5UO+vpqySNfbarn6esVNE1lEq+vb18Q7iXEZ8dn76eXxOvEm4oD1y1C/ZHurI0jLRfaSObaTidyLFZXoXwHlNJKFMWG/AteTyGpoKRLfq5cJFkYWwr4RVqQkjLhz+1mn27aFkePYf6N9ixngf6Lz3IPEeZ7Hb3i8RY55fsaYP1q0fvfPOdx2/efzAfSbSos="),
    '1m11': (57, 13, 0.0, 0.0, "eNrtzcEOgjAQBNAI291tKimUtGilASnF//9CxJMezB48O9fJm9n3f35JEltjmOFrk2XYesKTgkrVQL3mj6bMmwT7HqhCy0wGzsyo33ARYWvQKoVECIo1HwNwnB/FVspDgqMH3dgwEIFF4zqq6TWTp7yJh3sMZnDad45MG3x0hIpBU5lyWWW5xPF6SfM830K655ica5y1peRpFd0TrClRMA=="),
    '1s00': (35, 52, 27.03, 21.28, "eNq1lNuyoyAQRWOUW1C5OHhFoiCc//9CT1Izk0pUPDUPwyO1upum9+51/ceT/gTIioBEniLK6AYie0KY8SvMMsMnyDT3dZFcTguhriwv58iaQPhDFplcoLudEbqX6vxjtEYIVuoMsQwmV1TFgW4aBEiSVND4z+rRqrIkkrcxJB+8rTjnjEYHYI1xFblxnC8xJDjnOEZKKENiyDybNsc5KW3JjxGnbSdhqjDUPNK4s4voUVop0rdTRCyL0wYnAKcp1XUX68kJimgBpJB28d4fJWqVqjoz+WXs54gWKMSEPucYQowg6TVNRLOu/pioZVFmBGWoic6xmTFDGSZsjCKjpBIlV6DjPmo4BgihZqJRI/WPGgBSLgmJIgBdCVCyYCgmTIlBTllXUAZjHlJ90eBBK4nZsTTrHmUNYatVihJ++Br9eGX51IntBCfigGC1ohA+g0dTVbeDSnWREox+x+q8FAeammCKxJ9QTguld8Rcg1v2V2gUQLB3pGIEv24twWo37OEhJfDq09Wk6Xd1WJa9pR7zhoKtyzoi3xBWomyHBLfZRXKjGX9vP5FpCXZDeLNZBuF+v7v2Vzu/VsISzM69Pug3hfqwVBujGz35Ty+FZfjcF2HZ76GvsP7v8w1HF1VF"),
    '1s01': (35, 52, 37.1, 17.47, "eNq1lN2WoyAQhEflN6ggBDWKRFHJ+z9hxmx2s4kJzNmL7UvPR5fQVX29/mOBnwCpCExkFNG2bxByEcIOFz9JQCLIOHY1T76iQqSuyq84ck0Q+qGLTL7QfIgRppM6i/YYDMFI1THEcZikWIWB09gJlKaZYOGXNcapsjxI0YaQ3KxzK4QoaXAAztpZkENJ8iWE+HneECIrbam+azX3+otMk20JZLQsq2pYL+fjrzovy6PrbFytIdQYpLKflsv5Vsfjs9DsFtHhVCPK9RwwyzIbS1N86kcRfl271K3RXdR1rVKqNVEv5IgSFrN3xSjIsqQKz1rLogQUA3wKIo0jHANC+RB2lGQcJyk04Rs1JYEQ4WZkwSA1mwaEVEhKQ0gHcUqhlAXHIWNKAnPGT5xxFLqz7oqG9EZLwj9bs+4waCi/TlpTKj7+jdn+srwFxLWVoNUHgteaInQ7PFilDh+UdJFRgu9nTV5W44eXRRlWv48KxvW7IaYaUvBnegwimL/r8M0nD/NRIps90TOE4WMwc02a7k2nAOAp7EPRMbgP4onKJ2QbEnhD/GtwjJG7JK3n9vXLuHi3I1a7WwZ+y6prj+30WAmrtzvp2a3ePDl09YvabThrxtX7l8ZL/5pjv7zvoYu//u/6BttsSbk="),
    '1s10': (35, 52, 27.03, 21.28, "eNqV1MuWgyAMANBS5DX4QDi0ikgVxP7/F3acfQlnWLG4J5CQ8Pn8c+Ea0EYQpEFig39SFgER1ve564YDZNvdo0M38CA29/0NJh9EaSWKRjeafiDhnbZwYbxnjBoLkThQdGemDOZtGQlCeJTlyvo12r4XWk0l0i45GqXUIIsPEENIRvwo3h4lcqaUFGd2tEGUyL6HqeWt6GOvvpPk46wptpx6VUg8xWN0DBsr3LQVmuVIPnBEOMbSP+ZSTmmUTHZEjzoeOedvgSZrzRy2fKxuL/SCpFzIv3c8z8IrSXG/1nBtc6m7Zd8wLgTQDIuUmjSIAOTpueRIMnDShuGOCXTQZ+mvnJoBJJLdhejBGZENHQg4ApsTVHcgmR/aaln5XzgxCiZPIQmDibvCwFF01w3cwYTi1sDneMKwh8nKO2nhyi0dayoJKUF07WcmuKmQ6MSjQs6czhpJPldIfr1eFZLSeUwT2A35GuQwTyt43fc1qrUbf12/VMm9dg=="),
    '1s11': (35, 52, 37.1, 17.47, "eNqdlNuyoyAQRSPKLSgiBIOIxIiX//9CJzOnas55samZ/bxqd9Ps7vP8R1U5QBuGCw0iNo5PQhaAiNOxv3XFAGSefd8WN7AQ6zt5g5GzICTjoosbSXeICF7bEvSYAqPE9BCytLhA1FwDw+wVQahU4nqyISxGyrtW7gqpw5acUkryyw9YYkyK3SWr1ytkT+mDMN3ZyO1XreeXvpH3OzqGBZey66bteD3+6LWuf11TWHqLsaUV0uN7PV6/9Xj8LJSWVXmKLOGtTRdhWVOIHNFhnNX1dOPau2A9mDpnjHEBzEJNOBNQvAfB0UctFF3RVpRxDiCjEJpUBQaQZ2CCFpyCm9Z0qMJQoXNstCAV1O7pBUOcS3AuoiItBldg9pzoGkSGXvdaZO4Lw0bByJMLTGHEf2xgF900knkYIWVt4DoBkzLAyMQaYeHJDQ2tMg9SHOvMZba4zF3v5HnOZd/SnkNS2DLI9ln0XC9pX50D07Ct2xadm8B2j3Pfj/M/9AseXbH7"),
    '1s20': (35, 52, 27.03, 21.28, "eNq1lNmSoyAUhmOUxaAgMIgLsZHFfv8ndEzN9GIids3FcEOV9XG2//yu6z+e/CdAyBJk4hRRk9EQuRNiur8vsyjwCWLnoa2zy2ki1FN6OUfWDMIfoojsAv3tjDCDUOeDMQYhKNUZ4hjMrkimgd6OHGRZzkl6subuFKWlaLoUUo3RyaZpGEkK4KbJy/LW4CqkkMV732CkuJrKFDLPU1fhqqSONseIN64XMFcYmibRuHeBDyiXqhw6m1iW4M2EM4DznJi2T/XkOUGkBoILF2KMR4E6pWQ/2Rjuw5zYBQJxSR46LktCAoyueZGTTaR4TLQzrwGARXaioxUtrzcCJpFWa4JLRnCRREbXarO1DDBLIfeRClExDEnSa5ZpMXIMC5FSem4ZIWIEoGCpKHYbO0PCci3UsdJ2VJhCs25XQSE9LLaTumwf46nJ5qYDglspMX3U2bcC4wMTzKgksvoTflaMDgcrVwDW/31KrvltfK1VAYbNx0pAkL+W25dMo0+egPpFSdHoQX+utO9rjF6KJYjV3/SsAXwOEywsdmnRVT8hcfH7MQ7t02b6zfC7Dzosb/s0nXd7ZH333eS6pvpoYXH26dEWOEbfma+/SAhx+vVkzDnGvZeWMO6FW8Kr15a4/u/zG/xEVss="),
    '1s21': (35, 52, 37.1, 17.47, "eNq1lNuWoyAQReOFWzCgGMQLMSho/v8LbTOZdCca6DUPU2+utT0U1Dm1LP9Y6W+AKDGIRBCRfacgHANEf7nNg0hxADGmrXh0CB6Eq4IdwsgSQfiLiogO0B5DhG6FTIIaF40RLKsQMnIQxaj0A41pcxjHSU79L6v1WDJ2FHntQzI92TrPc0a8Axj73ub4yHDmfMhs7YpgUcieyMdZ6lE/yDD0NQaUMFYUl+l2Pf+pq3PfqlaPlQRAojQW3eBu13udz68H2dHlLYolJFxaj1mc1T2JUdOZ3P+6vatqLdug6+qyLGsd9EIGCaEhe0sM4yRNssCQBnECAKZRADFite5KQL8blKKYcIT8iezGSmlKAcDc68uOCZFxDKk3a4Yr0RUYpoJ4iKE6USo6AFLuUzGiEByt11JCfra46SRmUC9dhVMG2cdm67oi9wyt5yEoPxCFKUvM7n02UiD8IQQDIrSgD/lBctbuEZsA3vz9lcZJ1u17lYDjp08EhMm+XUW4Qt88BafdJEWuWmWeX645YbRrliJ+epknB3Ar4wx4NUBDUKw2yDS/B+fSVtPmxmvg37t38/VdQ9txE7+brfuxzunzCvNoNj+twtO6bPTPFnFu6s+bYI7TNM9vu8Xp98HNbt4vILf87/oC15FLXQ=="),
    '2b00': (25, 36, 10.67, 14.66, "eNqNktt2gyAQRVMhAkFBcKHghaiY5P+/kNb4FIaudh7PntuZNTH+HXV9zeoBF186B3YnaZ8Dzt0Ez/ZCl0tWnxTDA5Rp11016VmR6IwKTwjVJUKfwCu+KlG1JROfYPNu9ca2wjVJhd7C1NrBiFsK2rAIu1FaJdOVf9y9DS04l17DT7PJYnhDa3jDDHSoCSoJhgVx4GVvCM1UMCxHzoC+OKFnzQhJwVhLNY8aA6BrTuLEGRjipBTRc6TgbGLi1vMmBTM/msiiBDbosWkPtzLoMN1R8CcLY++7gK2MOMBcgV+syfsaewAPehq4Tyl4nqmPHYAz9fWCz/4b+Hd8A60urYg="),
    '2b01': (25, 36, 10.67, 12.09, "eNqNkt2SgyAMhbtKBYyC4CLiD1ax7fs/oTvWKw07u1yeLyE5Z7Jtf7+yzKJ6IMmXjoHVCWZjoHO5gOhf6e0W1QfFSY9l1jR3M1qeXHSg4kGZVPc0PQOvYFaiqLOiOoPJuMWb1gh9AV4uk6/brinEGRiovyfRzjzjZ6CMD5NvQ51fhls7hyUMQwsoyNAaqLjBDjVNMkpIJEOgtqYs0pET2QFH+uiEHjWnFGVbSjX2miCgS6BbDxwBJ6XYPKQKdXBqtsVBhYbDvqlMkPGO7ZtabMSku+mGoTt5cP7JBXfIHYwC3aKknzTWcAXPw8A0XMHrKH2uCByl7zc+9t/Av98PmZupxQ=="),
    '2b10': (25, 36, 10.67, 14.66, "eNqFkmFzgyAMhlsRCKWi4oHCLCra9f//Qjfdl5VwW77k7n0ub0jCvv8flWRZfS2vV50Dm1PQ54B3NyWzXuRyyepjK0qPZbA91bwXRaILUIFzaBkh7yC0cumqe8eEegcxuBjMYJRvkgod12/gjbqloFvnZogA96R7E55TGNaWps/VyxrXMQwl3uFgZCMMntCKgpGiyAFGKclcxErdGwZIX7RSVgPnKfjQIGNf4RIrauGdpqiJqWWzjxVHFb3g9T5LIlIwC+72TVF09REOyVJkpctjS1VJsNVR4QH1MOoYzQK2YvWBGbqHg/o0RL/3tf184GcKPqczTQGBx5keEVm9fqe/4gtP86L2"),
    '2b11': (25, 36, 10.67, 12.09, "eNqFktlywyAMRVNjFpUY21A2x0sCafP/X+jGzUttMa1eNHPPSOgirev/0Uha1HNdvekSuEclfAnE+K5ksRc5nYr62EM9YFk4R+3koTqOytXERacpIXsw9/LWK2nYuduDxcY022BUfwBjm5bZhME1ag/s2XwsXUjAYA96M+dlDtnA4XHvU055HINk6A+DlR1Y7NBBxUhFSoBRRlgBSOstE0i/6VY5DRyRQQuZfINLHLQwRE3RI7aV3XppOByBB9auV0kQmASPa1YUbf0iNslRVKHreltkjaxfYasYBKqwim+tBPKhn0M9MUPnG8UGrhJd7+P+OuDPI/haflKaEZhePhNq9fid/opvHyCfJw=="),
    '2b20': (25, 36, 10.67, 14.66, "eNqdkttuwyAMhttAOBRBAhWEnFgKTfv+T8iW9qqYadJ8YaT/wza2yflvk6Kt6gk3Z1MD90GxoQam8aJENRc6nar6ojmeoMzc0BrqeFPonKmNUqYJQp8g9CJepbgSrj5BDGMMdrTK90WESWmxfrLqUgKdtt7fGJNF9T7sX8EnDcZlYoppWTyGM/RW9NzCDp0gFJ+bykSk7iihEAzGcITgqiZD6GoYYyUYeSfWQSACahveZSMwyOU4d3nWFFS/mW7OmyQwAh13VduVYKb8x1vCAdDHeyRGJdD0mLej4APNyry6Aake6fArrLGH12GXEjz391YiAM/37rdfwD3/374BL6OtPw=="),
    '2b21': (25, 36, 10.67, 12.09, "eNqdkluTgyAMhVtRLk1FwQW8YtV2+/9/oVvGJwk7O7N54OF8MznkJPv+d5VQJPUtz646BZ5OcpcCfXeTkOxFLpekPiqR91jm1hZ2ciKLdODywXitCkLOwCtYmvLe0Ht9BrPpVm86I1UExmqdvWl7W8ozMNB8zXW7CCrOoG78Nvt2a0Rk7ty6rds4tkBRhq2BWhg8oQPKyDXDYChVxShLhKs/WZEioVM2ac55DLpbBZMDgj5lNa92DTkGQth9UAy5L7oadw8UuVsSbGVRocWykJ6JM/zMp4JtmZMYKF6Ghgwd0CDDFXaABvzewjtRBF7+2OQYg/fr2MqKwPs4I/8LeO7/rx8aE6l3"),
    '2d10': (39, 21, 19.43, -3.37, "eNrFksGOwyAMRFNKCEQbUlxRNksTORjz/39IpZX2SJLbzs3Sk+zxTK2XBZcopbvunNrjeuvE38SpgRFnpYSxz+CtTak0ML+vtnuNWksHfs6cm2trRDU9rTZTWPd8cB9G2h7aza+Hkgc+CDmnMDmv5E22wYSIadneS2+EEaLJ/WDOtNDmAIbe3MehBeZEVJcQPWhphl4fPttDWMFNX2YcT4OJgO4uf6180zE5615CZSwnUb/B0MblvBRYOJcrHWOu/6gPREqL4A=="),
    '2d11': (39, 21, 25.65, -7.1, "eNrFktsOgjAMhpGNsaGCVCaHCWzrhu//hJMY75DpnX/S5E/zpYe0Ifws2KbabYrxJHlbt4aem8b5DWXUeEjSl0X3eDSrPrVE7xhLRXUdlLR2dzKpxyKRxzyndTlcIyuYoDQrpeDiduKxXY2+Y3fkNdQlyyKc1R7n9tyXjB4IjWBGYz9NfSZSQdJdTml0rrNTDZJnghT5HugsYujb4Qacipzx+OGgHQGqkyiKr0dWUl8IpWS1nY2TFc8oBD8v8YrmDgInv3x/MLN4t/zyid6HP+oJLYmFdw=="),
    '2f00': (25, 36, 14.33, 14.66, "eNqdkt2OgyAQhatFEbFTwfDTKgQpre//hGxsr8q42WTnApL5wplzgJz/Lsqrw/79snXdEUiyb80RmKvTCQ612up4xtKf6wm3ySQk8AnKQ5RcHafM0HNdeOU62HEERsdvEPn8sEIsAy+Ap0FPA6eK9d/AcWVnO4mxKaNI6b2yC7DSrl6TWnQyCOQYnymFFSeU90aBIxgowqBlNQbXQQIMHPWd7JqbJl2LRnDJtRMEDTHQ0BwcIC0jKcvB9roEDwtjjl6gx13FLhIXVQLvd5EY+hLcYrOvAv0syfbrW80FBe/2BIYiu+ntU8ZQgu353l6xBK8P2DZs9xewpg/I/68fnbWuUg=="),
    '2f01': (25, 36, 14.33, 12.09, "eNqdktGOgyAQRatFAakoEAUJUGRt/f8vZKN92sHNJjsvJHMyd+6dkPPfhVl12bfDTsgV2GTX6ivgqtuNX2q11fUO191rVbaREpIz9YBDGA2eYTrje/0TBDpHo0ZO8QhA75JRwj0YMBbwFj2bpCNgomfTtqXnk2IQXnq7LNZFKxsAuhiMMyaoGQb5MsqNwpYJpUWCEFSCCVHe0roEQy85f7Ci7yVpFo0ILlYwyWYvUAOB5k2bo+eFlpaY5mi6ixhc5BTECME6HiLJTRCEcIik2EGwrIefZSh+lqT0ENR9Efw8kyaF3dfpU6YAwf46n3eC4P0B+17a/QWs2wfk/9c338yqpQ=="),
    '2f10': (25, 36, 14.33, 14.66, "eNqF0tlyhCAQBdBxG8RWEaZYFLTQcfn/L3Q0eYm0SXiAKk5daJZ9/78RiG7nu2rL8zuYRfHUd9BGj0d9u9Yzut/DFUks8HT64qIGWYYhkrIeCFUkjq9gQXvTNDUlzRUmcG/z4q6EAAYyKlkCkbS4Qg9SOSM5z6pgdyGGQRpX07BcNc7KmkUj2KdpmWc/4hNyTUTZJxh0JuIkyTBUecJTihMtY4WFnKKIPm6q10n+RMAO8DRL0YtrgN23FNAxJMjdG+AhvCW0+9iVDUo4dfYKJezUHb336Ge58qyH1SQEJs7PNmqUkNlZqEgRTIqdbG0I2/I1rGsI6/wLTN9vt/Zoqe3n8Ff7AExCo/I="),
    '2f11': (25, 36, 14.33, 12.09, "eNqF0lFzgyAMAOBaVKCIVDwEBSxYp///F7qyvazEbbzkju+SEC7H8f/BrDi993wn5AxWiWt9BmNxufDTWnVx3sPe0LWH16XqZMtUmyfhUniGqcbo+g4z1cH0fUvxPQPunqbvXMNzwGvwTElHMuBUrevyeFCcDa+8HkfrwiSrd5B0no0zZu6HfJBXb9d2E5ywG2qBCYKgK4kQqiAIirqSwoxRiJtlhNWgEsXUa0QgiBcEWpU5TLphRxgZyyGqmzqiYR1YBcXGI07NPYfFpb9YBgB2Sb8RAtgs26T3tByDwXVatqhBhqrSQ2UJIA4isXU57B9fYdty2NZf4Bm/wYNS+8/w1/kEkjugSg=="),
    '2f20': (25, 36, 14.33, 14.66, "eNqdkl2vgyAMhqeiWFEEFhVFiJ/z//9CNt3VqMlJTi/apE9a+tJ6/7dRFt3mh+qA/A5sqsi6O9BHjwe/7ZVF92+YIokVTpNGKM4UD4soqS2j0NE4DvqwbtJCcKDiFyzMrPopXMkC4OjcPktGGyh+gWVNa/pGyjSUoqRzWo8cwnHbeWtGvXcI+GXZt22asUKpSlXZBIO6yuIovQGqBsgTggsgo4bkKeD9kcpWkKMSayX4gUAaAid4622bo62vRhrvRi4QmPTH6xxt3c3jx88atRrq7JQ/UazPnrMBAiY7LwQoApO7rtA4dKDrFV6vEBzfzLEhcFxh79H3fsEx+X/bG/0qre0="),
    '2f21': (25, 36, 14.33, 12.09, "eNqdktuOgyAQhmtFYWoRwWBRgdLq1vd/QtbaqzIkm+xcDMn/ZU7MxPi30abI6hPfgOXAqi71LQfG4nRqs7nqIl/DXsqzxDLppWob3aZBlAjXUBhoef4GvhmC6buW0S4B3D53YK88aczTNbirVpYlEbzR6/q834Emw2s3jeNsw6iqb6AgBDMb43udDrIM2nZywhNKBR2DEgPB67IgGaAEACsJ1qGmM2EVWtVNEO44MBTinIA4EahS4GU7RDcwlGqZ5Ry9bTsEgtm9YWjr/mF3/zAo1SzeZWWgeD737g0QmCq1e6AIBH9c4ejRgS7H83qlYPso24rAdjw/I/reD9hC/Lf9Ai2fqjY="),
    '2m11': (39, 10, 0.0, 0.0, "eNrNztEKgCAMBVAw5hyVgiBhZYWW//+HS6in2Ad0n8bdYYz5xyH4FIekBgsKu05ZMm+zXwJra0WEZIwmDe1yLVVga0+DdxpM71AjYC5VYiWuIUbvw5bGFlvPLDFe3JTCM+ZtTszSa3wDmEU2sQ=="),
    '2s00': (25, 36, 18.92, 14.66, "eNqdkutyhCAMhbvKJYjKbXTVra4L4vu/obXd1rXATGfKLyYfCck52ba/Tg1ZGvSGslTcLus1T2aYmrwlwSUvkuCmc5JMaACpVNyJ7MISpJtmWdYJ8G6dlDWfI+CtLQrVmfiLuWEEoKtDsDjDMsPNFCsytYhgNFytD8nQqH5exkc4eIUR2tVdw1JaAs0hMXnLWYbbMQaaYwxjFQOOCVaaR/FRYCZ0FQMNuhxvgoYyzpruYsydCiWpBKGfi6KCWj0C+dUzbQK74TmaxlCegQD6LOHZ8GvEPv9ZwbbCp/jqD0cbfW7LTf5kmNs34zvB+vvr1d25bjlK9fIA08OfLFmX13X7//kA6V2y7A=="),
    '2s01': (25, 36, 25.7, 12.09, "eNqdkttygyAQhmsEWTyBUBSNGgX1/d/QmqZVI8x0pnvBwH7siZ91/ctyuPlBIwn1+c20VMgbIfPowwuCMPOCuwgjn39QBBU+YPNbAB6i217mnLugNSOPMzo4YDImjoWWvN0OdV1X1W+JQTMaARXj8vm0I8IqCChwN5fpNeFD7+l3bKRUvsFTjFDiAaoAEoIHlAm9IdW5QCQIQ5e5IMERLoRbpGOYMsFcIECk3T0n8qqGIOm26iK/VmAReb5eccnVIPiWoiTqIje8RhOYvjXMgLxSzLR5G7He36LM8Mm/zLsKQpzbsv18EsxuP+MnwMyP49bDWj3tqerj3/TjvJyqTMd2/b99AWGTrWs="),
    '2s10': (25, 36, 18.92, 14.66, "eNqN0duSgyAQBNBVR2AksirlNeoSIO7/fyHJs/bWhsc+1VyGlP5bRuUYZisZ5T4eYwEb1ogvCFlRQbh3hYCFXlGL8vCdZwxk2l1zMwBWH5rGaHeBp/dV1U72eoTrWSg1mTPEYDm32u7XiewDiZKW0T/PsvTt7OL2OFc0UfGe7nHOXc2lkODlrmWRE5rJeJNSIdiYBIRVEmvYGGqYp64WDYS10/gHO9YGA8kJb4Uvm9KgSww1/dHw/YDh1wcMIfxgiCHOdsN2pI/WC/aV4Ek="),
    '2s11': (25, 36, 25.7, 12.09, "eNqN0d0SgiAQBeBUBFbEUFKxzBQce/8npLpouvA0tXfsN2f5i/FXVTLFcLaCUN+vW89gwlb8ACHJNIRLk3HUn1vBagShShMJxI2TrYzZw+gXU2iad7B6XxSNs2Z8LoZh6Pv3FrM7EpfULNvpVZ9EaGVC0uxn+ckJM0/gvMvZ2hZdRDGWKXRzTTkXCGriKXz2vuQCJeKVGJcQBFMaQqcV/MCmFAbCWCuOE1SWGJhweBQ+bIydyjFo9iXh2w7D3QcMIdwwrGEd7BXbFv+qB3CS2ss="),
    '2s20': (25, 36, 18.92, 14.66, "eNqdkuuOgyAQhbcCClouwop4rVXk/d/QJWnXWCDZZOcPk/MxYWYOx/FXMJylQacKktJX61qQrFAs/0qCGyiTYJAgTxY0GNYpfePZjSSImRdxZwkwrpsQrFoisK9rWdZGxU8sDckxNiwEdlMkU5Wa443MGuYI9u26h6Rv6m6x0zPQOYEQ0ONwUb+SIJQypNWcwpQhi9bENxyDXra0QEWkT5rWLUI0BgJXg+bsHuqm9suQ/pUACCZKf2gZtNUBqow/JfgEA+PVa5hgEq6n/rUvgj8mGQF6ZxJdwW7HczH8avvjsV0s9vnbYDfb7eKxHY39vbXP3yd47s5d/8iZuuP/8QMXk7IS"),
    '2s21': (25, 36, 25.7, 12.09, "eNqdkutyhCAMheuKCloBoYIXdBGV939D147destMZ5o/xPMZApwsy19B8QMGjUwIpLvJawRWSBp/gCAIcxC0Iowh3ZYJKiAw0keAAVKZXlLO78C4gac5sTcwOZemopLcrB91XWv9bmErRmJMxOC/vmOvGEscEMzve7m+SrjtgfMOjZQloBcEoTAHgClJFEGGKM0YigBDrFIZjjHgn9B5EiU3vStZoePo3r3jOGuVoJ8Xva8KuiyCkKtXnNN0XbS4HEuHTFbrKsIzaCnLtsug82gx1TXbSxJyAiaMfjJxusk8/b62Zsd5eD7H/Se35nLLvZ3GwxhNRk1vW+d+93iYvT902Uv88v94AaF3rKA="),
    '3b00': (17, 24, 7.33, 9.69, "eNqN0NsKgzAMAFDGnE2o6yU6dLVzqDD//wuz+tQE9rBAAz3QXMr8O3zTaHiB1zBcjIZoFNyjA2uuFZLPXY9dhSWv0xRCBer3sCAKSOuWnJwkWzQg26SWvAYb6aZWceNDTUYwkwKLpa4EBB5VjRb5qbcrN/khsyvpLeCzn0k+2co5Dv4vvrUGPUI="),
    '3b01': (17, 24, 7.33, 8.06, "eNqNz9EKgzAMBVDG1DboTJs6rNYpm6D//4VZfWoCe1ighRxIc8v8u6iqNLwsahhuRoM3ClrsPJl7geiWLoArkJYtRuoL9GFwK9QFcH3vcxDAqQULcs1cE1oJEyA1EhDHp0pGNpGOCvldCdbyKLdyAzypkUfuvMx1fWMTcOzXJUc++Zwn/1dfsNs9Ow=="),
    '3b10': (17, 24, 7.33, 9.69, "eNqNz9sKwjAMBmDU2qakp1WHW6lDV9j7v2F0oDQBL/yhF/1omoTod6JSEu7gJVwPIGEwhl/94AD1qUNJNVys67DUdZpS6pDHNS1oGdRnK4lPUhFA9J2NVppDCRnFIMXOUUD0dRQlDimLdRFJvtCWbmcOQb//5bDXHzm0z/lme+wrN/ovL5WkPOk="),
    '3b11': (17, 24, 7.33, 8.06, "eNqNz1EOwiAMANCoCFQ2GGxmhDHUkXj/G1b8ok38sAlN+tKmBfF3BCE47NpxWE43Dl4pWho3+CAvHaLNwwy2w7Y/YvQE7LxMBa4dXHnVbSKA2Wit6ZqklJAMbDDskKRXx8CN+c5GDLT/UgCDvEMCrvQMHCUmoPCdP1Oo7R2kfj9bKhX/iw+FYjzR"),
    '3b20': (17, 24, 7.33, 9.69, "eNqNz9EKwyAMBVBGWzSo03Sz65xz1MH6/1+Y2ScT2MMCCjkouSH6XfM4SnhqJ+F6UhJQCXBotVFDh3TO9gK2Q8l1XUNgQ+M7FAAGudYUeJKHBaVFLjSDmLuYKIN4SLNYxrvixQtEihMHBbSILy3UTQAS3YFDPVaODD7tvLbe73u7NvqzvrOrPTE="),
    '3b21': (17, 24, 7.33, 8.06, "eNqNz9sKwyAMAFBGO2xmq0Z7cZu1uMH6/1+Y+WYCe1gggRwSokS/w/a9hH2wEubLIAGV4q1Gg151DaJLYwDX4L4fMaJpYMLsMlzZK3J5PwMDSiPIMwl1J2DVXk5YeHjxGTtlKyYQaeFHSAGtYuUGtAlAog04vGpOC4NPzaO0/jxrKfRnfAGpVT0j"),
    '3d10': (26, 15, 12.95, -1.78, "eNqtz0kKgDAMBVDRaqN1DFTRWJQO3v+GFVza1pV/FXgk5Hv/kTYFm8qKZ9Bv0WcpAMaebLC0NqvoRT0rFR4keyBMLA/FkKETgTEWMatpQ84rHntSLhKHpkxU2Duo0JuokTTuSnV3/v/cfv5Bbw=="),
    '3d11': (26, 15, 16.91, -4.16, "eNr7/x8P4EUwxRWRJaRkGZiBlJK6sogIqhYlBTZuDg4BKUlM0yS5xLj5OHkFsdkkoywjwM3HwoQpoyylJCknxMnCwoJFTkVJWlKUHQiwmSkqLirEz8WCw28yvBxsQv+VscpJiyqrquEKFNX/1AcAdDY+vA=="),
    '3f00': (17, 24, 9.67, 9.69, "eNqNjtEOwjAIRY2xTTsy6krYZqzLGqf7/y9k9UlIfJCEB07gcEV+V8rOglsHFvjT2QL0Xo8BOPBFWYa0EMbuC+bMiKi0kYkI1Ul6rFxZa6/rczNBRh97EzUDQ9SgjzwFA1wu1gFSSYMyylLMhpP7oEH7wEb6av3Wkq31vqu5foD8WQeueD2H"),
    '3f01': (17, 24, 9.67, 8.06, "eNqNzsEOwjAIBmBjbC1Wi2tD28U6q1nc+z8hzpNgPEjCgS/kB+bfhWg0jAevwW62GoKxcvRALu7EzoBTCuA+cC79OKIAf+2PG4oUzDUTRZFaYw3qkWJhr16NngAknICKU2BiUxnZ8z1JaJmnJoEMXwYJ6wVSofPaz/QFyyLm/gb+s16vNz2A"),
    '3f10': (17, 24, 9.67, 9.69, "eNqNkEsKwzAMREtxnCgfK7ZIwAubpLjt/U+oprsRdFGBBPNAw0iqv4u5syCPkwX+drdg7TzKgbYhOXCJXCXQCJZpCyGALYlEWWGFy7E/EtrGs7XZBCVHJmrsJ2+CsCv9gCBRyRbMWglBFT3FgEXzjmBhLWzO/b4EwfPqN+p2jdeh/9UHdVY9LA=="),
    '3f11': (17, 24, 9.67, 8.06, "eNqNzsEOwiAMBmBjGNDhqEBgcgA3o/P9n7DO09rEg01o0i/NT4l+F8ZBwjw6Cfp0luAHzUeAbJNiOwF78gAHXOfFVbQHuLY+7shSQi4ll8BSa7w5cQiC0opDMM6IQ1A1YzlEaFXChfrIoSdaswBPtXKYJmrI4Rsovn3t783n5962hf6rD4MGPTQ="),
    '3f20': (17, 24, 9.67, 9.69, "eNqNzkEPgjAMBWAjMDaEjXUpclDiyJT//wurnnw1HOhhSb9kr09kfwI1Gq7dRYM5nTWMjcHVOrZUQ0oMS/Ku+8FM7L2HWMcxphG+hPtjyoyxKZeiivBQmUo1b4OtEaKdnEWgfo2q6sIy9wgrS076ihAhtE5kwMzyeV4A2/YH8oXnTY7NG4izPVw="),
    '3f21': (17, 24, 9.67, 8.06, "eNqNz90KwjAMBWBxP20dbWxLNio6Z1H3/k8Y55Un4oW5KPTjEE5Efg9Rp2E6DBr63V5D6Hr8Osc2t5BJNOfg7AeO0xIKAQyXW70SbIk8MnOCrSWdgirCvmkahGjItuoUM1qrEr5GVXVmKQGhsiwZIXlJWEPMttFj4L49T4B1/QJ5w+Ms/80LkSQ9XA=="),
    '3m11': (26, 8, 0.0, 0.0, "eNr7/5+agIePmZkRylZCkZHkY+VlZePgYGX9/18NRUZOSEial1uIn4ODW1kVRUZRQVQabJI0uh7cAAA92qzq"),
    '3s00': (17, 24, 12.58, 9.69, "eNqNz9sSgiAQBuCmQCBiUxwoOpiCvP8jYqWOuzNdtBfA/w2wUMrPaipFYYiMwhF2FAwHku/7A8nX4aRbDDFB3ToMHoQOeEvnObMubxCUdGNEO5wSmrQ5C3YhoJhp8Mus0QHwGVtB8TX+O3zu3UDL93CTds1PMXfiK6T0nfpuyXl8zItX6hdaJJc/awKvyT24"),
    '3s01': (17, 24, 16.9, 8.06, "eNqNkN0OwiAMhY3Kv4MNHIyom4zp+78hTmGGJl7YG3q+9JS2Kf2MjjAIwowg4HIHgUAS6Mv+APQQDDWgZeQnY9fEO/cBs5UI6RCn81Yy9rgdao/nVICumhEIFD46ABhqOlU7GuFV7dFYJttWu6869bTa7J17qjd9I/mn70VizNOORT+XMvQU7wU9rvlJf8YLXHA66A=="),
    '3s10': (17, 24, 12.58, 9.69, "eNqNkEsKgDAMRMX+rLH1R6MiCK16/yPWpU1w4ezmMQmT5PypUVsKYpIUtL6iwClP/F4L4tfYwVyCdPphDiVAb2ArIwcqOYX7BQhNuFKRQKtosR1EQ4tZyUAP7FrQDHQ8oQ316NjOxfKRk//0Orb8Ww8rmlF+"),
    '3s11': (17, 24, 16.9, 8.06, "eNqNkFEPgjAMhI3QsbI5xck2Y8SM+f//4iAkJl7DA33qfWkvvda6W0PHCPJMCHp3QmDIgX6dG9Ape+3BsvTWh7V5xriBOTiiey6fx29kGtUt/e8Eoy24jty2AN7caDyMSYCrEWmNEsCK9FV1qONFeEaWpkX+9DulergW2chOsg=="),
    '3s20': (17, 24, 12.58, 9.69, "eNqNkN0OwiAMRo0OEDvBbYFsMSo/4/0fsbqhrk28sDfNd3oCBcSf1UnNQUwNByez4+AsDMvX/YHlMbYwUJCyuQyOAm8UTFS5e9H0rmzAg/ZzIobXki9260AwMPVaAhO0AwrG1qBV5O3qtSYQYO1ykTp+T6h/syk5ry2Edy6xAnyE+FHqrOCf9QS9BT3K"),
    '3s21': (17, 24, 16.9, 8.06, "eNqNj9sOgjAMho26EyWbMB0jRtkhvP8jFmFC1sQLe9P+3/4ehvgzOqEoiIlR0OgTBcA00c/zhWgfrbRkZG5a6z7FOAwbSE4z1sc83XfL+8Fvvu5xIOkWB/xKwKtTFIy94kAM4KAGvtVoRPX39UyogDHrIiGPCaVShyXnLYXw1XMqAKcQd0t5m/HPWABt+TsC"),
}


def _tex_modelo(time_, lod, vista, fase, arma):
    import base64, zlib
    d = SPR_MODELO.get("%d%s%d%d" % (lod, vista, fase + 1, arma))
    if d is None:
        return None
    w, h, mx, my, b = d
    idx = zlib.decompress(base64.b64decode(b))
    tint = TIME_TINT[time_]
    pal = []
    for r, g, bl in PAL_MODELO:                 # desloca o matiz da camuflagem para a cor do time
        r, g, bl = ((v - 100) * 1.45 + 100 for v in (r, g, bl))          # realça o contraste da camuflagem
        pal.append((max(0, min(255, int(r * tint[0]))), max(0, min(255, int(g * tint[1]))),
                    max(0, min(255, int(bl * tint[2])))))
    t = Tela(w, h)
    if vista == "m":                            # poça de sangue sob o corpo caído
        t.ell(w / 2.0, h - 1.5, w * 0.46, 1.7, (96, 18, 18), 0.2)
    g = t.g
    for y in range(h):
        row = g[y]
        base = y * w
        for x in range(w):
            v = idx[base + x]
            if v != 255:
                row[x] = pal[v]
    tex = Tex(t, (mx, my) if vista != "m" else None)
    tex.esc = 40.0 / ALTS_LOD[lod]
    return tex


TIME_TINT = {0: (0.70, 1.0, 1.40), 1: (1.38, 1.0, 0.68)}


_TEX = {}


def textura(time_, vista, fase, arma, vivo=True, lod=0):
    k = (time_, vista, fase, arma, vivo, lod)
    t = _TEX.get(k)
    if t is None:
        t = _tex_modelo(time_, lod, "m" if not vivo else vista, 0 if not vivo else fase, 1 if not vivo else arma)
        if t is not None:
            _TEX[k] = t
            return t
        if not vivo:
            t = _fig_morto(time_)
        elif vista == "d":
            t = _fig_slide(time_, arma)
        elif vista == "s":
            t = _fig_perfil(time_, fase, arma)
        else:
            t = _fig_frontal(time_, vista == "f", fase, arma)
        _TEX[k] = t
    return t


_HC = {}


def cor_sprite(rgb, lvl, hit):
    k = (rgb, lvl, hit)
    v = _HC.get(k)
    if v is None:
        r, g, b = rgb
        if hit:
            r, g, b = min(255, r + 110), g * 0.55, b * 0.55
        v = hexcor(r, g, b, lvl / 16.0)
        _HC[k] = v
    return v


FASES_ANDAR = (0, 1, 0, -1)


# ============================================================ renderização
class Vista:
    """Desenha o mundo em 3D (raycasting) e o HUD num Canvas do tkinter."""

    RS, RX, RY = 4, 12, 12   # escala e posição do radar

    def __init__(self, canvas, mundo):
        self.c, self.m = canvas, mundo
        self.NSEG = 4                                   # faces por coluna (muro + o que se vê por cima)
        self.cache = [[] for _ in range(NCOL)]
        self.cortes = [[] for _ in range(NCOL)]         # por coluna: (distância, y do topo) das faces
        self.feed = []
        self.t = 0.0
        self.t_dano = self.t_acerto = 0.0
        self.info = ""
        self._ult = {}
        self._anda = {}
        self.pontos = {}
        self.zoom, self.ads_k, self.kc, self.sk = 1.0, 0.0, 0.0, 0.0
        self.tan_e, self.K, self.hor, self.eye = TAN, float(ALT), ALT / 2, 0.5
        self.t_head = 0.0
        self.passo_col = 1        # qualidade dos sprites (1 = máxima); ajusta sozinha
        self._dt_med = 0.016
        self._quadro = 0
        self._vis_radar = {}      # ator -> (quadro, visível?) cache da linha de visão
        self._montar()

    def _montar(self):
        c = self.c
        meio = ALT // 2
        n = self.NB = 12
        self.teto, self.piso = [], []
        for i in range(n):  # teto e piso em faixas (gradiente); reposicionadas com o horizonte
            f = 0.45 + 0.55 * i / (n - 1)
            self.teto.append(c.create_rectangle(0, 0, LARG, 1, fill=hexcor(48, 58, 84, f), outline=""))
            f2 = 1.0 - 0.55 * i / (n - 1)
            self.piso.append(c.create_rectangle(0, 0, LARG, 1, fill=hexcor(92, 82, 68, f2), outline=""))
        self.itens = [[c.create_rectangle(i * COL, 0, i * COL + COL, 0, fill="#000", outline="",
                                          state="hidden")
                       for _ in range(self.NSEG)] for i in range(NCOL)]
        # Pools dos soldados: em vez de criar/apagar centenas de itens por quadro, reaproveita os mesmos.
        # A ordem de empilhamento é a de criação: sombras < corpos (do mais longe ao mais perto) <
        # clarões < nomes < HUD. Cada quadro preenche os "slots" em ordem de pintura.
        self.pool_o = [c.create_oval(0, 0, 0, 0, fill="#17130f", outline="", state="hidden")
                       for _ in range(32)]
        # corpos: um GRUPO fixo de itens por soldado (criado sob demanda, reaproveitado). A ordem de
        # empilhamento entre grupos (pintura do mais longe ao mais perto) é ajustada com tag_raise
        # só quando muda; assim cada retângulo do soldado cai sempre no mesmo item.
        self.g_items, self.g_est, self.g_prev, self.g_dono = [], [], [], []
        self.g_de, self.pila, self.usados = {}, [], []
        self.pool_p = [c.create_polygon(0, 0, 0, 0, 0, 0, fill="#ffe36a", outline="#ff9a2a", state="hidden")
                       for _ in range(8)]
        self.pool_t = [c.create_text(0, 0, text="", font=("Courier", 9, "bold"), state="hidden")
                       for _ in range(16)]
        self.est_o = [None] * 32
        self.est_p, self.est_t = [None] * 8, [None] * 16
        self.n_o = self.n_p = self.n_t = 0                     # slots usados neste quadro
        self.a_o = self.a_p = self.a_t = 0                     # ... e no quadro anterior

        hud = dict(tags="hud")
        # arma em primeira pessoa
        self.g_braco = c.create_polygon(0, 0, 0, 0, 0, 0, fill="#27408b", outline="#162350", **hud)
        self.g_mao = c.create_oval(0, 0, 0, 0, fill=hexcor(*SKIN), outline="#a07850", **hud)
        self.g_arma = c.create_polygon(0, 0, 0, 0, 0, 0, fill="#2b2f38", outline="#101216", **hud)
        self.g_fogo = c.create_polygon(0, 0, 0, 0, 0, 0, fill="#ffd94a", outline="#ff9a2a",
                                       state="hidden", **hud)
        # mira e marcador de acerto
        self.mira = [c.create_line(0, 0, 0, 0, fill="#7CFF7C", width=2, **hud) for _ in range(4)]
        self.marca = [c.create_line(0, 0, 0, 0, fill="white", width=2, state="hidden", **hud)
                      for _ in range(4)]
        # vinheta de dano
        self.vig = [c.create_rectangle(a, b, d, e, fill="#b01010", outline="", state="hidden", **hud)
                    for a, b, d, e in ((0, 0, LARG, 36), (0, ALT - 36, LARG, ALT),
                                       (0, 0, 36, ALT), (LARG - 36, 0, LARG, ALT))]
        # textos
        fb = ("Courier", 22, "bold")
        self.t_hp = c.create_text(30, ALT - 34, anchor="w", fill="#5be37d", font=fb, **hud)
        self.b_st_bg = c.create_rectangle(30, ALT - 14, 170, ALT - 8, fill="#1c2236", outline="", **hud)
        self.b_st = c.create_rectangle(30, ALT - 14, 170, ALT - 8, fill="#e8c24a", outline="", **hud)
        self.ponto = c.create_oval(0, 0, 0, 0, fill="#7CFF7C", outline="", state="hidden", **hud)
        self.t_hs = c.create_text(LARG // 2, ALT // 2 + 58, fill="#ff4040",
                                  font=("Courier", 18, "bold"), **hud)
        self.t_mun = c.create_text(LARG - 30, ALT - 34, anchor="e", fill="#ffd24a", font=fb, **hud)
        self.t_arma = c.create_text(LARG - 30, ALT - 64, anchor="e", fill="#c8d2ee",
                                    font=("Courier", 13, "bold"), **hud)
        self.t_placar = c.create_text(LARG // 2, 22, fill="#e8eef9", font=("Courier", 20, "bold"), **hud)
        self.t_tempo = c.create_text(LARG // 2, 48, fill="#9fb3e8", font=("Courier", 14, "bold"), **hud)
        self.t_msg = c.create_text(LARG // 2, ALT // 2 - 70, fill="#ffd24a",
                                   font=("Courier", 30, "bold"), justify="center", **hud)
        self.t_pausa = c.create_text(LARG // 2, ALT // 2 + 40, fill="#ffffff", justify="center",
                                     font=("Courier", 14, "bold"), **hud)
        self.t_feed = [c.create_text(LARG - 14, 18 + i * 20, anchor="e", fill="#fff",
                                     font=("Courier", 13, "bold"), **hud) for i in range(5)]
        # radar
        RS, RX, RY = self.RS, self.RX, self.RY
        c.create_rectangle(RX - 2, RY - 2, RX + MW * RS + 2, RY + MH * RS + 2,
                           fill="#0a0f1a", outline="#3a4468", **hud)
        rcor = {"=": "#34456a", "a": "#3f5180", "b": "#3f5180", "c": "#3f5180", "2": "#6b5c40",
                "x": "#7a6648", "8": "#56624e", "6": "#8a4a44", "3": "#3f6a9c"}
        for y, linha in enumerate(GRADE):
            x = 0
            while x < MW:
                if linha[x] != ".":
                    ch, ini = linha[x], x
                    while x < MW and linha[x] == ch:
                        x += 1
                    c.create_rectangle(RX + ini * RS, RY + y * RS, RX + x * RS, RY + (y + 1) * RS,
                                       fill=rcor.get(ch, "#56608a"), outline="", **hud)
                else:
                    x += 1
        self.radar_dir = c.create_line(0, 0, 0, 0, fill="#fff", **hud)
        # placar (Tab)
        self.r_score = c.create_rectangle(160, 70, LARG - 160, ALT - 110, fill="#0a0f1a",
                                          outline="#3a4468", state="hidden", **hud)
        self.t_sc = [c.create_text(185 + k * 320, 86, anchor="nw", fill=cor, justify="left",
                                   font=("Courier", 12, "bold"), state="hidden", **hud)
                     for k, cor in enumerate(("#7ec8ff", "#ffb066"))]

    # ---------------------------------------------------------- utilidades
    def _set(self, item, **kw):
        chave = tuple(sorted(kw.items()))
        if self._ult.get(item) != chave:
            self.c.itemconfig(item, **kw)
            self._ult[item] = chave

    def _coords(self, item, *pts):
        if self._ult.get(("c", item)) != pts:
            self.c.coords(item, *pts)
            self._ult[("c", item)] = pts

    # ---------------------------------------------------------- quadro
    def _bandas(self):
        BH, n, hor = 48, self.NB, self.hor
        for i in range(n):
            y1 = hor - (n - 1 - i) * BH
            y0 = -4000 if i == 0 else y1 - BH
            self._coords(self.teto[i], 0, y0, LARG, y1)
            y0 = hor + i * BH
            y1 = ALT + 4000 if i == n - 1 else y0 + BH
            self._coords(self.piso[i], 0, y0, LARG, y1)

    def desenhar(self, dt, pausado, placar=False):
        self.t += dt
        self._quadro += 1
        j = self.m.jogador
        self.eventos(dt)
        # câmera: zoom (mirando), altura do olho (pulo) e horizonte (olhar vertical)
        self.sk += ((1.0 if (j.deslizando and j.vivo) else 0.0) - self.sk) * min(1.0, dt * 12.0)
        alvo = 1.0 + (0.38 if (j.mira and j.vivo) else 0.0) - 0.07 * self.sk
        self.zoom += (alvo - self.zoom) * min(1.0, dt * 14.0)
        self.ads_k = max(0.0, min(1.0, (self.zoom - 1.0) / 0.38))
        self.kc += ((1.0 if (j.correndo and j.vivo) else 0.0) - self.kc) * min(1.0, dt * 10.0)
        self.tan_e = TAN / self.zoom
        self.K = ALT * self.zoom
        alvo_olho = 0.5 + j.pz - 0.22 * self.sk
        self.eye += (alvo_olho - self.eye) * min(1.0, dt * 18.0)     # suaviza degraus e queda
        self.hor = ALT / 2 + max(-PIT_MAX, min(PIT_MAX, j.pit)) * self.K
        self._bandas()
        self.paredes(j)
        self.sprites(j, dt)
        self.arma(j)
        self.hud(j, pausado, placar)

    def eventos(self, dt):
        m = self.m
        for ev in m.eventos:
            if ev[0] == "dano":
                ev[2].hit = 0.15
                if ev[2] is m.jogador:
                    self.t_dano = 0.35
                if ev[1] is m.jogador:
                    self.t_acerto = 0.15
                    if ev[3]:
                        self.t_head = 0.7
            elif ev[0] == "morte":
                a, v = ev[1], ev[2]
                cor = "#7CFF7C" if a.time == m.jogador.time else "#ff8a6b"
                self.feed.append([f"{a.nome}  >>  {v.nome}" + ("  [HS]" if ev[3] else ""), 5.0, cor])
        m.eventos.clear()
        self.feed = [f for f in self.feed if f[1] > 0][-5:]
        for f in self.feed:
            f[1] -= dt
        for a in m.atores:
            if a.hit > 0:
                a.hit = max(0.0, a.hit - dt)
        self.t_dano = max(0.0, self.t_dano - dt)
        self.t_acerto = max(0.0, self.t_acerto - dt)
        self.t_head = max(0.0, self.t_head - dt)

    def paredes(self, j):
        c, px, py = self.c, j.x, j.y
        dirx, diry = math.cos(j.ang), math.sin(j.ang)
        plx, ply = -diry * self.tan_e, dirx * self.tan_e
        K, hor, eye, NS = self.K, self.hor, self.eye, self.NSEG
        itens, cache, cortes = self.itens, self.cache, self.cortes
        for i in range(NCOL):
            cx = CAMX[i]
            segs = segmentos(px, py, dirx + plx * cx, diry + ply * cx, eye, K, hor, NS)
            cortes[i] = [(s[0], s[3]) for s in segs]
            novo = []
            for (t, tipo, lado, ya, yb, fr) in segs:
                y0 = int(ya)
                if y0 < 0:
                    y0 = 0
                y1 = int(yb)
                if y1 <= y0:
                    continue
                f = 1.0 - t / 20.0
                if f < 0.15:
                    f = 0.15
                idx = int(f * (NSH - 1))
                if lado:
                    idx = int(idx * 0.75)
                if fr < 0.04 or fr > 0.96:
                    idx = max(0, idx - 4)
                novo.append((y0, y1, PAL[tipo][idx]))
            ant = cache[i]
            if novo != ant:
                it = itens[i]
                for k in range(NS):
                    if k < len(novo):
                        y0, y1, cor = novo[k]
                        old = ant[k] if k < len(ant) else None
                        if old is None or old[0] != y0 or old[1] != y1:
                            c.coords(it[k], i * COL, y0, i * COL + COL, y1)
                        if old is None:
                            c.itemconfig(it[k], fill=cor, state="normal")
                        elif old[2] != cor:
                            c.itemconfig(it[k], fill=cor)
                    elif k < len(ant):
                        c.itemconfig(it[k], state="hidden")
                cache[i] = novo

    def _radar_ve(self, j, a):
        """Linha de visão para o radar, recalculada só a cada 4 quadros por inimigo."""
        r = self._vis_radar.get(a)
        if r is None or self._quadro - r[0] >= 4:
            r = (self._quadro + (a.id % 4), ve(j.x, j.y, a.x, a.y, j.pz + 0.5, a.pz + 0.45))
            self._vis_radar[a] = r
        return r[1]

    def fase_andar(self, a, dt):
        reg = self._anda.get(a)
        if reg is None:
            self._anda[a] = [a.x, a.y, 0.0, 0.0]
            return 0
        dist = math.hypot(a.x - reg[0], a.y - reg[1])
        reg[0], reg[1] = a.x, a.y
        if dist > 0.003 and dist < 1.0:
            reg[3] = 0.18
            reg[2] += dist
        else:
            reg[3] = max(0.0, reg[3] - dt)
        return FASES_ANDAR[int(reg[2] / 0.3) % 4] if reg[3] > 0 else 0

    def _corte(self, col, ty):
        """Primeira linha da tela escondida por parede/bloco mais perto que 'ty' nessa coluna."""
        cr = ALT
        for tt, yy in self.cortes[col]:
            if tt < ty:
                cr = yy
            else:
                break
        return cr

    # ---- pools (cada helper só chama o Tk quando algo mudou)
    GR = 140            # retângulos iniciais por soldado (cresce sozinho se precisar)
    MAXG = 40           # soldados com corpo desenhado ao mesmo tempo

    def _novo_grupo(self):
        g = len(self.g_items)
        c, tag = self.c, "gs%d" % g
        self.g_items.append([c.create_rectangle(0, 0, 0, 0, fill="#000", outline="", state="hidden", tags=tag)
                             for _ in range(self.GR)])
        self.g_est.append([None] * self.GR)
        self.g_prev.append(0)
        self.g_dono.append(None)
        c.tag_raise(tag, self.pool_o[-1])         # logo acima das sombras, abaixo de clarões/nomes/HUD
        self.pila.insert(0, g)
        return g

    def _grupo(self, a):
        g = self.g_de.get(a)
        if g is not None and self.g_dono[g] is a:
            self.usados.append(g)
            return g
        em_uso = set(self.usados)
        livre = None
        for k, dono in enumerate(self.g_dono):                    # sem dono ou dono que saiu da partida
            if k not in em_uso and (dono is None or dono not in self.m.atores):
                livre = k
                break
        if livre is None and len(self.g_items) < self.MAXG:
            livre = self._novo_grupo()
        if livre is None:                                          # rouba um grupo que não está na tela
            for k in range(len(self.g_items)):
                if k not in em_uso and self.g_prev[k] == 0:
                    livre = k
                    break
        if livre is None:
            return None
        old = self.g_dono[livre]
        if old is not None and self.g_de.get(old) == livre:
            del self.g_de[old]
        self.g_dono[livre] = a
        self.g_de[a] = livre
        self.usados.append(livre)
        return livre

    def _rect(self, g, i, x0, y0, x1, y1, fill):
        items, ests = self.g_items[g], self.g_est[g]
        if i >= len(items):                                        # soldado grande: acrescenta itens
            tag = "gs%d" % g
            for _ in range(64):
                it = self.c.create_rectangle(0, 0, 0, 0, fill="#000", outline="", state="hidden", tags=tag)
                self.c.tag_raise(it, items[-1])
                items.append(it)
                ests.append(None)
        est = ests[i]
        it = items[i]
        if est is None:
            self.c.coords(it, x0, y0, x1, y1)
            self.c.itemconfig(it, fill=fill, state="normal")
        else:
            if est[0] != x0 or est[1] != y0 or est[2] != x1 or est[3] != y1:
                self.c.coords(it, x0, y0, x1, y1)
            if est[4] != fill:
                self.c.itemconfig(it, fill=fill)
        ests[i] = (x0, y0, x1, y1, fill)

    def _cerrar(self, g, n):
        """Esconde os itens do soldado usados no quadro anterior e não neste."""
        ests, items = self.g_est[g], self.g_items[g]
        for i in range(n, self.g_prev[g]):
            if ests[i] is not None:
                self.c.itemconfig(items[i], state="hidden")
                ests[i] = None
        self.g_prev[g] = n

    def _apilar(self):
        """Garante que os grupos desenhados estejam empilhados na ordem de pintura (longe -> perto)."""
        orden = self.usados
        em = set(orden)
        if [g for g in self.pila if g in em] == orden:
            return
        ref = self.pool_o[-1]
        for g in orden:
            tag = "gs%d" % g
            self.c.tag_raise(tag, ref)
            ref = tag
        self.pila = orden + [g for g in self.pila if g not in em]

    def _oval(self, x0, y0, x1, y1):
        i = self.n_o
        if i >= len(self.pool_o):
            return
        est = self.est_o[i]
        if est is None:
            self.c.itemconfig(self.pool_o[i], state="normal")
        if est != (x0, y0, x1, y1):
            self.c.coords(self.pool_o[i], x0, y0, x1, y1)
        self.est_o[i] = (x0, y0, x1, y1)
        self.n_o = i + 1

    def _poly(self, pts):
        i = self.n_p
        if i >= len(self.pool_p):
            return
        if self.est_p[i] is None:
            self.c.itemconfig(self.pool_p[i], state="normal")
        self.c.coords(self.pool_p[i], *pts)
        self.est_p[i] = True
        self.n_p = i + 1

    def _texto(self, x, y, txt, cor):
        i = self.n_t
        if i >= len(self.pool_t):
            return
        est = self.est_t[i]
        if est is None:
            self.c.itemconfig(self.pool_t[i], state="normal")
        if est is None or est[0] != x or est[1] != y:
            self.c.coords(self.pool_t[i], x, y)
        if est is None or est[2] != txt or est[3] != cor:
            self.c.itemconfig(self.pool_t[i], text=txt, fill=cor)
        self.est_t[i] = (x, y, txt, cor)
        self.n_t = i + 1

    def _ocultar(self):
        """Esconde os slots que foram usados no quadro anterior e não neste."""
        c = self.c
        for pool, est, n, ant in ((self.pool_o, self.est_o, self.n_o, self.a_o),
                                  (self.pool_p, self.est_p, self.n_p, self.a_p),
                                  (self.pool_t, self.est_t, self.n_t, self.a_t)):
            for i in range(n, ant):
                if est[i] is not None:
                    c.itemconfig(pool[i], state="hidden")
                    est[i] = None
        self.a_o, self.a_p, self.a_t = self.n_o, self.n_p, self.n_t
        em = set(self.usados)
        for g in range(len(self.g_items)):                     # soldados que saíram da tela
            if g not in em and self.g_prev[g]:
                self._cerrar(g, 0)
        self._apilar()

    def sprites(self, j, dt):
        c = self.c
        self.n_o = self.n_p = self.n_t = 0
        self.usados = []
        px, py = j.x, j.y
        dirx, diry = math.cos(j.ang), math.sin(j.ang)
        plx, ply = -diry * self.tan_e, dirx * self.tan_e
        inv = 1.0 / (plx * diry - dirx * ply)
        lista = []
        for a in self.m.atores:
            if a is j:
                continue
            dx, dy = a.x - px, a.y - py
            ty = inv * (-ply * dx + plx * dy)
            if ty > 0.15:
                lista.append((ty, inv * (diry * dx - dirx * dy), a))
        lista.sort(key=lambda t: -t[0])
        corte = self._corte
        for ty, tx_, a in lista:
            sx = (NCOL / 2) * (1 + tx_ / ty)
            alt = self.K / ty
            h = alt * 0.84
            baixo = self.hor + (self.eye - a.pz) * alt      # pés à altura absoluta a.pz
            s = h / 40.0
            lod = 0 if h >= LIM_LOD[0] else (1 if h >= LIM_LOD[1] else (2 if h >= LIM_LOD[2] else 3))
            lvl = int(max(0.2, 1.0 - ty / 20.0) * 16)
            hit = 1 if a.hit > 0 else 0
            espelha = False
            if a.vivo:
                dx, dy = a.x - px, a.y - py
                d = math.hypot(dx, dy)
                rx, ry = dx / d, dy / d
                ax, ay = math.cos(a.ang), math.sin(a.ang)
                fa = ax * rx + ay * ry          # >0: de costas p/ câmera
                fr = -ax * ry + ay * rx         # >0: virado p/ direita da tela
                arma = a.arma if a.arma in (0, 1) else 1
                if a.deslizando:
                    espelha = fr < 0
                    tex = textura(a.time, "d", 0, arma, True, lod)
                else:
                    v = "b" if fa > 0.6 else ("f" if fa < -0.6 else "s")
                    espelha = v == "s" and fr < 0
                    tex = textura(a.time, v, self.fase_andar(a, dt), arma, True, lod)
            else:
                tex = textura(a.time, "f", 0, 1, False, lod)
            s *= tex.esc
            W = tex.w
            larg = W * s / COL
            esq = sx - larg / 2
            topo = baixo - tex.h * s
            ys = [int(topo + r * s + 0.5) for r in range(tex.h + 1)]
            y_top = ys[0]
            c0, c1 = max(0, int(esq)), min(NCOL, int(esq + larg) + 1)
            # totalmente escondido atrás de paredes/blocos? nem processa
            if not any(corte(k2, ty) > y_top for k2 in range(c0, c1, 2)):
                continue
            cc = int(sx)
            cr_c = corte(cc, ty) if 0 <= cc < NCOL else 0
            if a.vivo and cr_c > baixo:      # sombra no chão
                self._oval(sx * COL - W * s * 0.35, baixo - s * 1.2, sx * COL + W * s * 0.35,
                           baixo + s * 1.8)
            cols = tex.cols
            grp = self._grupo(a)
            if grp is None:
                continue
            k = 1            # sempre qualidade máxima (1 fatia por coluna)
            abertos = {}     # (y0, y1, cor) -> [x0, x1, r0, r1]: funde colunas vizinhas iguais
            saida = []
            for col in range(c0, c1, k):
                cend = min(col + k, NCOL)
                cr = corte(col + (cend - col) // 2, ty)
                if cr <= y_top:
                    continue
                u = (col + (cend - col) / 2.0 - esq) / larg
                if u < 0 or u >= 1:
                    continue
                tx = int(u * W)
                if espelha:
                    tx = W - 1 - tx
                x0 = col * COL
                x1 = cend * COL
                cri = int(cr)
                for r0, r1, rgb in cols[tx]:
                    y0, y1 = ys[r0], ys[r1]
                    if y0 >= cri:
                        continue
                    if y1 > cri:
                        y1 = cri
                    if y1 <= y0:
                        continue
                    chave = (y0, y1, rgb)
                    seg = abertos.get(chave)
                    if seg is not None and seg[1] == x0:
                        seg[1] = x1
                    else:
                        if seg is not None:
                            saida.append((seg[2], seg[3], rgb, seg[0], seg[1], y0, y1))
                        abertos[chave] = [x0, x1, r0, r1]
            for (y0, y1, rgb), (xa, xb, ra, rb) in abertos.items():
                saida.append((ra, rb, rgb, xa, xb, y0, y1))
            # ordem canônica (independe da geometria): cada retângulo cai sempre no mesmo slot do
            # pool entre quadros, então quase só as coordenadas mudam (cor e visibilidade se mantêm)
            saida.sort()
            for i, (ra, rb, rgb, xa, xb, y0, y1) in enumerate(saida):
                self._rect(grp, i, xa, y0, xb, y1, cor_sprite(rgb, lvl, hit))
            self._cerrar(grp, len(saida))
            if a.vivo and a.flash > 0 and tex.muz:
                mx = tex.muz[0] if not espelha else W - tex.muz[0]
                px_ = (esq + mx / W * larg) * COL
                my = topo + tex.muz[1] * s
                col = int(px_ / COL)
                if 0 <= col < NCOL and corte(col, ty) > my:
                    r = max(4.0, s * 4)
                    pts = []
                    for k in range(12):
                        rr = r if k % 2 == 0 else r * 0.4
                        an = k * math.pi / 6
                        pts += [px_ + math.cos(an) * rr, my + math.sin(an) * rr]
                    self._poly(pts)
            if a.vivo and a.time == j.time and ty < 9 and cr_c > y_top + 4 and y_top > 10:
                self._texto(sx * COL, y_top - 7, a.nome, "#7ec8ff" if a.time == 0 else "#ffb066")
        self._ocultar()
        if len(self._anda) > len(self.m.atores) + 8:
            vivos = set(self.m.atores)
            self._anda = {k: v for k, v in self._anda.items() if k in vivos}

    def arma(self, j):
        ar = ARMAS[j.arma]
        cx = LARG / 2
        ox = oy = 0.0
        ak, kc = self.ads_k, self.kc
        if j.andando and j.vivo:
            vv = 1.6 if j.correndo else 1.0
            fa = 1.0 - 0.8 * ak
            ox = math.cos(self.t * 4.5 * vv) * 7 * fa * vv
            oy = abs(math.sin(self.t * 9 * vv)) * 6 * fa * vv
        ox += -30.0 * ak + 70.0 * kc + 26.0 * self.sk    # mirando: ao centro; correndo/deslizando: abaixada
        oy += -34.0 * ak + 85.0 * kc + 34.0 * self.sk
        if j.flash > 0:
            oy += 18 * (j.flash / 0.06)
        if j.rel > 0:
            prog = 1 - j.rel / ar["rel"]
            oy += math.sin(math.pi * prog) * 90
        L = ar["comp"]
        larg = 16 if j.arma == 1 else 12
        self._coords(self.g_arma,
                     cx + 24 + ox, ALT - L + oy, cx + 24 + larg + ox, ALT - L + oy,
                     cx + 160 + ox, ALT + 30 + oy, cx + 70 + ox, ALT + 30 + oy)
        self._coords(self.g_braco,
                     cx + 95 + ox, ALT - 65 + oy, cx + 240 + ox, ALT - 20 + oy,
                     cx + 270 + ox, ALT + 40 + oy, cx + 70 + ox, ALT + 40 + oy)
        self._coords(self.g_mao, cx + 92 + ox, ALT - 88 + oy, cx + 138 + ox, ALT - 44 + oy)
        if j.time == 0:
            self._set(self.g_braco, fill="#27408b", outline="#162350")
        else:
            self._set(self.g_braco, fill="#9a6428", outline="#5a3a14")
        if j.flash > 0 and j.vivo:
            tx, ty = cx + 28 + ox, ALT - L + oy
            pts = []
            for k in range(12):
                r = 26 if k % 2 == 0 else 11
                a = k * math.pi / 6
                pts += [tx + math.cos(a) * r, ty + math.sin(a) * r]
            self._coords(self.g_fogo, *pts)
            self._set(self.g_fogo, state="normal")
        else:
            self._set(self.g_fogo, state="hidden")
        est = "normal" if j.vivo else "hidden"
        self._set(self.g_arma, state=est)
        self._set(self.g_braco, state=est)
        self._set(self.g_mao, state=est)

    def _mensagem(self, j):
        m = self.m
        if m.fase == "congelado":
            return f"RODADA {m.rodada}\nPrepare-se!"
        if m.fase == "fim":
            r = m.res
            if r == j.time:
                return "VITÓRIA DO SEU TIME!"
            if r in (0, 1):
                return "SEU TIME FOI ELIMINADO"
            return "EMPATE" if r == "empate" else "TEMPO ESGOTADO"
        if m.fase == "partida":
            ganhou = m.placar[j.time] > m.placar[1 - j.time]
            txt = "VOCÊ VENCEU A PARTIDA!" if ganhou else "VOCÊ PERDEU A PARTIDA"
            if m.pode_reiniciar:
                txt += "\n\nENTER: jogar de novo   M: menu"
            else:
                txt += "\n\nM: menu"
            if m.auto:
                txt += f"\nNova partida em {max(0, int(m.t_partida))}s"
            return txt
        return "VOCÊ MORREU" if not j.vivo else ""

    def _tabela(self, time_):
        m = self.m
        nome = "AZUL" if time_ == 0 else "LARANJA"
        lin = [f"{nome}  {m.placar[time_]}", f"  {'JOGADOR':<12}{'K':>4}{'M':>4}"]
        mem = sorted((a for a in m.atores if a.time == time_), key=lambda a: (-a.k, a.m))
        for a in mem[:14]:
            marca = ">" if a is m.jogador else " "
            lin.append(f"{marca} {a.nome[:11]:<12}{a.k:>4}{a.m:>4}")
        return "\n".join(lin)

    def hud(self, j, pausado, placar):
        m, c = self.m, self.c
        cx, cy = LARG / 2, ALT / 2
        # mira (abre com imprecisão)
        gap = 5 + int((j.imp + (0.012 if j.andando else 0.0)) * 260)
        vis = "normal" if (j.vivo and self.ads_k < 0.5) else "hidden"
        self._coords(self.ponto, cx - 2, cy - 2, cx + 2, cy + 2)
        self._set(self.ponto, state="normal" if (j.vivo and self.ads_k >= 0.5) else "hidden")
        self._coords(self.b_st, 30, ALT - 14, 30 + 140.0 * j.stam / 100.0, ALT - 8)
        self._set(self.b_st, fill="#ff5a4a" if j.exausto else "#e8c24a")
        for k, (a, b, d, e) in enumerate(((-gap - 11, 0, -gap, 0), (gap, 0, gap + 11, 0),
                                          (0, -gap - 11, 0, -gap), (0, gap, 0, gap + 11))):
            self._coords(self.mira[k], cx + a, cy + b, cx + d, cy + e)
            self._set(self.mira[k], state=vis)
        est = "normal" if self.t_acerto > 0 else "hidden"
        for k, (sx, sy) in enumerate(((-1, -1), (1, -1), (-1, 1), (1, 1))):
            self._coords(self.marca[k], cx + sx * 7, cy + sy * 7, cx + sx * 15, cy + sy * 15)
            self._set(self.marca[k], state=est, fill="#ff4040" if self.t_head > 0 else "white")
        for v in self.vig:
            self._set(v, state="normal" if self.t_dano > 0 else "hidden")

        # textos
        self._set(self.t_hp, text=f"VIDA {j.hp}", fill="#5be37d" if j.hp > 30 else "#ff5050")
        ar = ARMAS[j.arma]
        mun = "RECARREGANDO..." if j.rel > 0 else f"{j.mags[j.arma]} / {j.res[j.arma]}"
        self._set(self.t_mun, text=mun)
        self._set(self.t_arma, text=ar["nome"])
        self._set(self.t_placar, text=f"AZUL {m.placar[0]}  x  {m.placar[1]} LARANJA")
        seg = max(0, int(m.tempo))
        self._set(self.t_tempo, text=f"Rodada {m.rodada}   {seg // 60}:{seg % 60:02d}")
        self._set(self.t_msg, text=self._mensagem(j))
        self._set(self.t_hs, text="HEADSHOT" if self.t_head > 0 else "")
        pausa = ""
        if pausado:
            pausa = ("CLIQUE PARA JOGAR\n\nWASD mover · Mouse mirar · Clique atirar\n"
                     "R recarregar · 1/2 armas · Tab placar · Esc pausa · M menu\n"
                     "Shift correr · C/Ctrl deslizar · Espaço pular · Botão direito mirar")
            if self.info:
                pausa += "\n\n" + self.info
        self._set(self.t_pausa, text=pausa)
        for i, item in enumerate(self.t_feed):
            if i < len(self.feed):
                self._set(item, text=self.feed[i][0], fill=self.feed[i][2])
            else:
                self._set(item, text="")

        # placar (Tab)
        est = "normal" if placar else "hidden"
        self._set(self.r_score, state=est)
        for k, item in enumerate(self.t_sc):
            self._set(item, state=est)
            if placar:
                self._set(item, text=self._tabela(k))

        # radar
        RS, RX, RY = self.RS, self.RX, self.RY
        atuais = set(m.atores)
        for a in list(self.pontos):
            if a not in atuais:
                c.delete(self.pontos.pop(a))
        for a in m.atores:
            item = self.pontos.get(a)
            if item is None:
                item = c.create_oval(0, 0, 0, 0, fill="#fff", outline="", state="hidden", tags="hud")
                self.pontos[a] = item
            if not a.vivo:
                self._set(item, state="hidden")
                continue
            if a.time == j.time:
                cor = "#ffffff" if a is j else "#5ab0ff"
            elif j.vivo and self._radar_ve(j, a):
                cor = "#ff5a4a"
            else:
                self._set(item, state="hidden")
                continue
            x, y = RX + a.x * RS, RY + a.y * RS
            self._coords(item, x - 2, y - 2, x + 2, y + 2)
            self._set(item, state="normal", fill=cor)
        jx, jy = RX + j.x * RS, RY + j.y * RS
        self._coords(self.radar_dir, jx, jy, jx + math.cos(j.ang) * 9, jy + math.sin(j.ang) * 9)


# ============================================================ aplicação (tkinter)
FUNDO, TEXTO = "#0b0f1a", "#e8eef9"


def entrada_vazia():
    return dict(mv=(0, 0), fogo=False, clique=False, rec=False, arma=None,
                correr=False, pular=False, mirar=False, deslizar=False)


PERIODO_MS = 1000.0 / 75.0      # alvo ~75 quadros/s (o ritmo real é limitado pelo desenho)


def timer_alta_resolucao(ligar):
    """No Windows o timer padrão tem passo de ~15,6 ms: o after() do tkinter fica irregular e o jogo
    parece 'engasgar'. Pedir 1 ms deixa o ritmo dos quadros estável."""
    if sys.platform == "win32":
        try:
            import ctypes
            (ctypes.windll.winmm.timeBeginPeriod if ligar else ctypes.windll.winmm.timeEndPeriod)(1)
        except Exception:
            pass


class Lienzo:
    """Mesma API de Canvas usada pela Vista, mas escala o desenho (LARG x ALT) para a tela cheia.
    Se a proporção da tela for diferente, centraliza e cobre as sobras com barras pretas."""

    def __init__(self, canvas, esc, ox, oy):
        self.c, self.e, self.ox, self.oy = canvas, esc, ox, oy

    def _kw(self, kw):
        f = kw.get("font")
        if f:
            kw["font"] = (f[0], max(1, int(round(f[1] * self.e)))) + tuple(f[2:])
        w = kw.get("width")
        if w is not None and not isinstance(w, str):
            kw["width"] = w * self.e
        return kw

    def _p(self, p):
        e, ox, oy = self.e, self.ox, self.oy
        return [v * e + (oy if i & 1 else ox) for i, v in enumerate(p)]

    def create_rectangle(self, x0, y0, x1, y1, **kw):
        e, ox, oy = self.e, self.ox, self.oy
        return self.c.create_rectangle(x0 * e + ox, y0 * e + oy, x1 * e + ox, y1 * e + oy, **kw)

    def create_oval(self, x0, y0, x1, y1, **kw):
        e, ox, oy = self.e, self.ox, self.oy
        return self.c.create_oval(x0 * e + ox, y0 * e + oy, x1 * e + ox, y1 * e + oy, **kw)

    def create_polygon(self, *p, **kw):
        return self.c.create_polygon(*self._p(p), **self._kw(kw))

    def create_line(self, *p, **kw):
        return self.c.create_line(*self._p(p), **self._kw(kw))

    def create_text(self, x, y, **kw):
        return self.c.create_text(x * self.e + self.ox, y * self.e + self.oy, **self._kw(kw))

    def coords(self, item, *p):
        return self.c.coords(item, *self._p(p))

    def itemconfig(self, item, **kw):
        return self.c.itemconfig(item, **self._kw(kw))

    def delete(self, *a):
        self.c.delete(*a)

    def tag_lower(self, *a):
        self.c.tag_lower(*a)

    def tag_raise(self, *a):
        self.c.tag_raise(*a)

    def barras(self, W, H):
        x1, y1 = self.ox + LARG * self.e, self.oy + ALT * self.e
        for r in ((0, 0, W, self.oy), (0, y1, W, H), (0, 0, self.ox, H), (x1, 0, W, H)):
            if r[2] - r[0] > 0.5 and r[3] - r[1] > 0.5:
                self.c.create_rectangle(*r, fill="#000", outline="")


class App:
    def __init__(self, root):
        self.root = root
        root.title("Mini CS 3D")
        root.resizable(False, False)
        root.configure(bg=FUNDO)
        root.protocol("WM_DELETE_WINDOW", self.sair)
        self.teclas = set()
        self.ativo = False
        self.servidor = self.cliente = None
        self.v_nome = tk.StringVar(value="Jogador")
        self.v_porta = tk.StringVar(value=str(PORTA_PADRAO))
        self.v_ip = tk.StringVar(value="")
        self.v_ali, self.v_ini = tk.IntVar(value=2), tk.IntVar(value=3)
        self.v_dif = tk.StringVar(value="Normal")
        self.v_tela = tk.BooleanVar(value=False)
        self.cw, self.ch, self.info = LARG, ALT, ""
        self._ult, self._ignora, self._win_ok = None, 0, True
        root.bind("<KeyPress>", self.tecla_press)
        root.bind("<KeyRelease>", lambda e: self.teclas.discard(e.keysym.lower()))
        self.menu()

    def sair(self):
        self.ativo = False
        timer_alta_resolucao(False)
        self.fechar_rede()
        self.root.destroy()

    def fechar_rede(self):
        if self.servidor:
            self.servidor.fechar()
        if self.cliente:
            self.cliente.fechar()
        self.servidor = self.cliente = None

    def limpar(self):
        self.ativo = False
        for w in self.root.winfo_children():
            w.destroy()

    def _tela_cheia(self, flag):
        try:
            self.root.attributes("-fullscreen", bool(flag))
        except tk.TclError:
            pass
        if flag:
            self.root.update_idletasks()

    def menu(self, erro=""):
        self.fechar_rede()
        self.limpar()
        self._tela_cheia(False)
        f = tk.Frame(self.root, padx=50, pady=26, bg=FUNDO)
        f.pack()
        tk.Label(f, text="MINI CS 3D", font=("Courier", 32, "bold"), fg="#ffd24a", bg=FUNDO).pack()
        tk.Label(f, text="você + bots + amigos na rede (LAN / Radmin)", fg="#9fb3e8",
                 bg=FUNDO).pack(pady=(0, 12))

        topo = tk.Frame(f, bg=FUNDO)
        topo.pack(pady=4)
        tk.Label(topo, text="Seu nome", fg=TEXTO, bg=FUNDO).grid(row=0, column=0, padx=8)
        tk.Entry(topo, textvariable=self.v_nome, width=14, justify="center").grid(row=1, column=0, padx=8)
        tk.Label(topo, text="Porta", fg=TEXTO, bg=FUNDO).grid(row=0, column=1, padx=8)
        tk.Entry(topo, textvariable=self.v_porta, width=7, justify="center").grid(row=1, column=1, padx=8)
        tk.Checkbutton(topo, text="Tela cheia (F11 alterna)", variable=self.v_tela, fg=TEXTO, bg=FUNDO,
                       selectcolor="#1c2236", activebackground=FUNDO, activeforeground=TEXTO
                       ).grid(row=0, column=2, rowspan=2, padx=14)

        cols = tk.Frame(f, bg=FUNDO)
        cols.pack(pady=12)
        esq = tk.LabelFrame(cols, text=" Criar partida ", fg="#ffd24a", bg=FUNDO, padx=18, pady=10)
        esq.grid(row=0, column=0, padx=10, sticky="n")
        for txt, w in (("Aliados (bots no seu time)",
                        tk.Spinbox(esq, from_=0, to=50, width=6, justify="center", textvariable=self.v_ali)),
                       ("Inimigos (bots)",
                        tk.Spinbox(esq, from_=0, to=50, width=6, justify="center", textvariable=self.v_ini)),
                       ("Dificuldade dos bots", tk.OptionMenu(esq, self.v_dif, *DIFIC.keys()))):
            tk.Label(esq, text=txt, fg=TEXTO, bg=FUNDO).pack(pady=(6, 2))
            w.pack()
        tk.Button(esq, text="JOGAR OFFLINE", width=26,
                  command=lambda: self.iniciar("solo")).pack(pady=(14, 4))
        tk.Button(esq, text="HOSPEDAR NA REDE", width=26,
                  command=lambda: self.iniciar("host")).pack(pady=4)

        dir_ = tk.LabelFrame(cols, text=" Entrar numa partida ", fg="#ffd24a", bg=FUNDO, padx=18, pady=10)
        dir_.grid(row=0, column=1, padx=10, sticky="n")
        tk.Label(dir_, text="IP do host\n(LAN ou Radmin)", fg=TEXTO, bg=FUNDO).pack(pady=(6, 2))
        tk.Entry(dir_, textvariable=self.v_ip, width=18, justify="center").pack()
        tk.Button(dir_, text="ENTRAR", width=26,
                  command=lambda: self.iniciar("cliente")).pack(pady=(14, 4))

        tk.Label(f, text="Seus IPs: " + rotular_ips(ips_locais()), fg="#9fb3e8", bg=FUNDO).pack()
        self.lbl_erro = tk.Label(f, text=erro, fg="#ff6a5a", bg=FUNDO, wraplength=620)
        self.lbl_erro.pack(pady=(6, 0))
        tk.Label(f, text="WASD mover · Mouse mirar · Clique atirar · R recarregar\n"
                         "1/2 trocar arma · Tab placar · Shift correr · C deslizar · Espaço pular · Botão dir. mirar · F11 tela cheia · Esc pausa",
                 fg="#7f8fb8", bg=FUNDO).pack(pady=(8, 0))

    def iniciar(self, modo):
        nome = self.v_nome.get().strip()[:12] or "Jogador"
        try:
            porta = int(self.v_porta.get())
            if not 1 <= porta <= 65535:
                raise ValueError
        except ValueError:
            self.lbl_erro.config(text="Porta inválida (use um número de 1 a 65535).")
            return
        try:
            aliados = max(0, min(50, self.v_ali.get()))
            inimigos = max(0, min(50, self.v_ini.get()))
        except tk.TclError:
            self.lbl_erro.config(text="Número de bots inválido.")
            return
        self.fechar_rede()
        info = ""
        if modo == "cliente":
            ip = self.v_ip.get().strip()
            if not ip:
                self.lbl_erro.config(text="Digite o IP do host.")
                return
            self.lbl_erro.config(text="Conectando...")
            self.root.update_idletasks()
            try:
                self.cliente = Cliente(ip, porta, nome)
            except (OSError, ConnectionError, ValueError) as e:
                self.lbl_erro.config(text=f"Não foi possível entrar: {e}")
                return
            self.mundo = self.cliente.mundo
            self.mundo.jogador.nome = nome
            info = f"Conectado a {ip}:{porta}"
        else:
            if modo == "host":
                inimigos = max(1, inimigos)
            else:
                inimigos = max(1, inimigos)
            self.mundo = Mundo(aliados, inimigos, self.v_dif.get(), rede=(modo == "host"))
            self.mundo.jogador.nome = nome
            if modo == "host":
                try:
                    self.servidor = Servidor(porta)
                except OSError as e:
                    self.lbl_erro.config(text=f"Não foi possível abrir a porta {porta}: {e}")
                    return
                info = f"Hospedando na porta {porta}\nIPs: {rotular_ips(ips_locais())}"
        self.limpar()
        self.info = info
        self.montar_tela()
        self.ativo = True
        self.t0 = time.perf_counter()
        self.loop()

    def montar_tela(self):
        """Cria canvas + Vista (janela 960x540 ou tela cheia escalada). Chamado ao iniciar e no F11."""
        for w in self.root.winfo_children():
            w.destroy()
        cheia = bool(self.v_tela.get())
        self._tela_cheia(cheia)
        if cheia:
            W, H = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
            esc = min(W / LARG, H / ALT)
            ox, oy = (W - LARG * esc) / 2, (H - ALT * esc) / 2
        else:
            W, H, esc, ox, oy = LARG, ALT, 1.0, 0.0, 0.0
        self.cw, self.ch = W, H
        self.canvas = c = tk.Canvas(self.root, width=W, height=H, bg="#000", highlightthickness=0)
        c.pack()
        lienzo = Lienzo(c, esc, ox, oy) if cheia else c
        self.vista = Vista(lienzo, self.mundo)
        self.vista.info = self.info
        if cheia:
            lienzo.barras(W, H)
        gc.collect()
        gc.freeze()          # estruturas fixas (mapa, texturas, itens do canvas) saem das coletas de lixo
        self.capturado = False
        self.atirando = self.clique = False
        self.mirando = self.pulo = self.desliza = False
        self.troca = None
        c.bind("<Motion>", self.mouse_mover)
        c.bind("<ButtonPress-1>", self.mouse_press)
        c.bind("<ButtonRelease-1>", lambda e: setattr(self, "atirando", False))
        for b in (2, 3):     # botão direito (no macOS pode ser o 2)
            c.bind(f"<ButtonPress-{b}>", lambda e: setattr(self, "mirando", self.capturado))
            c.bind(f"<ButtonRelease-{b}>", lambda e: setattr(self, "mirando", False))
        c.bind("<MouseWheel>", lambda e: setattr(self, "troca", (self.mundo.jogador.arma + 1) % 2))
        c.bind("<Button-4>", lambda e: setattr(self, "troca", (self.mundo.jogador.arma + 1) % 2))
        c.bind("<Button-5>", lambda e: setattr(self, "troca", (self.mundo.jogador.arma + 1) % 2))

    def alternar_tela(self):
        self.v_tela.set(not self.v_tela.get())
        self.montar_tela()

    # ---- entrada
    def tecla_press(self, e):
        k = e.keysym.lower()
        self.teclas.add(k)
        if not self.ativo or not hasattr(self, "mundo"):
            return "break" if k == "tab" else None
        if k == "f11":
            self.alternar_tela()
            return "break"
        if k == "1":
            self.troca = 0
        elif k == "2":
            self.troca = 1
        elif k == "space":
            self.pulo = True
        elif k in ("c", "control_l", "control_r"):
            self.desliza = True
        elif k == "escape":
            self.soltar()
        elif k == "return" and self.mundo.fase == "partida" and self.mundo.pode_reiniciar:
            self.mundo.reiniciar()
        elif k == "m" and (not self.capturado or self.mundo.fase == "partida"):
            self.menu()
        if k == "tab":
            return "break"

    def capturar(self):
        self.capturado = True
        try:
            self.canvas.config(cursor="none")
        except tk.TclError:
            pass
        self._ult, self._ignora = None, 0
        self.centrar()
        self._ignora = 6

    def soltar(self):
        self.capturado = False
        self.atirando = self.mirando = False
        try:
            self.canvas.config(cursor="arrow")
        except tk.TclError:
            pass

    def _centro_tela(self):
        return (self.canvas.winfo_rootx() + self.cw // 2, self.canvas.winfo_rooty() + self.ch // 2)

    def mira_win(self):
        """Windows: lê a posição real do cursor a cada quadro, aplica o deslocamento desde o centro e
        recoloca o cursor no centro com SetCursorPos. O cursor nunca sai da janela."""
        try:
            import ctypes
            from ctypes import wintypes
            pt = wintypes.POINT()
            ctypes.windll.user32.GetCursorPos(ctypes.byref(pt))
            cx, cy = self._centro_tela()
            dx, dy = pt.x - cx, pt.y - cy
            if dx or dy:
                if abs(dx) < 2000 and abs(dy) < 2000:
                    j = self.mundo.jogador
                    k = 0.6 if j.mira else 1.0
                    j.ang += dx * SENS * k
                    j.pit = max(-PIT_MAX, min(PIT_MAX, j.pit - dy * SENS_Y * k))
                ctypes.windll.user32.SetCursorPos(cx, cy)
        except Exception:
            self._win_ok = False

    def centrar(self):
        if sys.platform == "win32" and self._win_ok:
            try:
                import ctypes
                cx, cy = self._centro_tela()
                ctypes.windll.user32.SetCursorPos(cx, cy)
                return
            except Exception:
                self._win_ok = False
        self.canvas.event_generate("<Motion>", warp=True, x=self.cw // 2, y=self.ch // 2)

    def mouse_press(self, e):
        if not self.capturado:
            self.capturar()
            return
        self.atirando = True
        self.clique = True

    def mouse_mover(self, e):
        """Mira por delta entre eventos consecutivos (não em relação ao centro). Assim, eventos que se
        acumulam quando um quadro demora não são contados duas vezes nem descartados; o cursor só é
        reposicionado no centro quando se afasta bastante (e o evento do próprio reposicionamento é ignorado)."""
        if not self.capturado or (sys.platform == "win32" and self._win_ok):
            return                                        # no Windows a mira é lida em mira_win()
        cx, cy = self.cw // 2, self.ch // 2
        if self._ignora:                                  # espera o evento gerado pelo warp (ou expira)
            self._ignora -= 1
            if (e.x, e.y) == (cx, cy) or not self._ignora:
                self._ignora = 0
                self._ult = None                          # ressincroniza no próximo evento (sem salto)
            return
        if self._ult is None:
            self._ult = (e.x, e.y)
            return
        dx, dy = e.x - self._ult[0], e.y - self._ult[1]
        self._ult = (e.x, e.y)
        if abs(dx) > self.cw // 4 or abs(dy) > self.ch // 4:
            return                                        # salto impossível = artefato do warp: ignora
        if dx or dy:
            j = self.mundo.jogador
            k = 0.6 if j.mira else 1.0
            j.ang += dx * SENS * k
            j.pit = max(-PIT_MAX, min(PIT_MAX, j.pit - dy * SENS_Y * k))
        if abs(e.x - cx) > self.cw // 4 or abs(e.y - cy) > self.ch // 4:
            self._ignora = 4
            self._ult = None
            self.centrar()

    def ler_entrada(self):
        k = self.teclas
        f = (("w" in k) or ("up" in k)) - (("s" in k) or ("down" in k))
        s = ("d" in k) - ("a" in k)
        ent = dict(mv=(f, s), fogo=self.atirando, clique=self.clique, rec="r" in k, arma=self.troca,
                   correr=("shift_l" in k or "shift_r" in k), pular=self.pulo, mirar=self.mirando,
                   deslizar=self.desliza)
        self.clique, self.troca, self.pulo, self.desliza = False, None, False, False
        return ent

    # ---- loop
    def loop(self):
        if not self.ativo:
            return
        agora = time.perf_counter()
        dt = min(agora - self.t0, 0.05)
        self.t0 = agora
        if self.capturado:
            if sys.platform == "win32" and self._win_ok:
                self.mira_win()
            if "left" in self.teclas:
                self.mundo.jogador.ang -= 2.4 * dt
            if "right" in self.teclas:
                self.mundo.jogador.ang += 2.4 * dt
            ent = self.ler_entrada()
        else:
            ent = entrada_vazia()

        if self.cliente:
            self.cliente.passo(dt, ent)
            if not self.cliente.conn.vivo:
                self.menu("Conexão com o host perdida.")
                return
        else:
            # offline: Esc pausa o jogo; hospedando: o mundo continua rodando p/ os amigos
            if self.capturado or self.servidor:
                self.mundo.passo(dt, ent)
            if self.servidor:
                self.servidor.passo(self.mundo, dt)
        self.vista.desenhar(dt, not self.capturado, "tab" in self.teclas)
        trab = (time.perf_counter() - agora) * 1000.0
        self.root.after(max(1, int(PERIODO_MS - trab)), self.loop)


if __name__ == "__main__":
    gc.set_threshold(50000, 20, 100)     # menos coletas de lixo = menos "travadinhas" pontuais
    timer_alta_resolucao(True)
    janela = tk.Tk()
    App(janela)
    janela.mainloop()
