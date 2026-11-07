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


_TEX = {}


def textura(time_, vista, fase, arma, vivo=True):
    k = (time_, vista, fase, arma, vivo)
    t = _TEX.get(k)
    if t is None:
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
                    tex = textura(a.time, "d", 0, arma)
                else:
                    v = "b" if fa > 0.6 else ("f" if fa < -0.6 else "s")
                    espelha = v == "s" and fr < 0
                    tex = textura(a.time, v, self.fase_andar(a, dt), arma)
            else:
                tex = textura(a.time, "f", 0, 1, False)
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
        self.centrar()

    def soltar(self):
        self.capturado = False
        self.atirando = self.mirando = False
        try:
            self.canvas.config(cursor="arrow")
        except tk.TclError:
            pass

    def centrar(self):
        self.canvas.event_generate("<Motion>", warp=True, x=self.cw // 2, y=self.ch // 2)

    def mouse_press(self, e):
        if not self.capturado:
            self.capturar()
            return
        self.atirando = True
        self.clique = True

    def mouse_mover(self, e):
        cx, cy = self.cw // 2, self.ch // 2
        if not self.capturado or (e.x == cx and e.y == cy):
            return
        j = self.mundo.jogador
        k = 0.6 if j.mira else 1.0
        j.ang += (e.x - cx) * SENS * k
        j.pit = max(-PIT_MAX, min(PIT_MAX, j.pit - (e.y - cy) * SENS_Y * k))
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
