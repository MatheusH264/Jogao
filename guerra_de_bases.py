"""
GUERRA DE BASES  -  estilo Dead Ahead: Zombie Warfare (visual adulto / sombrio)
Guarnição (você)  x  Insurgentes (IA)

Requisitos:  pip install pygame
Controles:   1-6 enviar unidades (ou clique)  |  U melhorar renda  |  R reiniciar  |  ESC sair

Sprites opcionais: pasta "sprites" ao lado do arquivo com guarda.png, lanca-chamas.png,
atirador.png, artilheiro.png, blindado.png (viradas para a direita). Sem elas, o jogo
desenha tudo sozinho.
"""
import math, os, random, sys
import pygame

W, H = 1280, 720
HUD_H = 90
HORIZON = 420
GROUND_TOP, GROUND_BOT = 462, 612
BASE_GROUND = 598
FPS = 60
SS = 4            # supersampling dos sprites (suaviza as bordas)
N_WALK = 8
TANK_SCALE = 1.4   # tamanho do blindado
BASE_MG = dict(range=360, dmg=5, cd=0.28, spread=0.10)                                  # metralhadora do QG
BASE_CANNON = dict(range=520, min_range=130, dmg=22, aoe=48, cd=4.0, scatter=14)        # canhão do QG

OUT = (14, 14, 17)
SKIN = (205, 160, 128)
BOOT = (30, 28, 28)
GLOVE = (30, 29, 30)
GUNBLK = (34, 34, 38)
STEEL = (112, 116, 124)
STEEL_D = (62, 64, 70)
STEEL_L = (160, 164, 170)
GOLD = (222, 184, 70)

PAL = {
    0: dict(cloth=(66, 74, 60), cloth_d=(44, 50, 42), armor=(92, 100, 106), armor_d=(62, 68, 74),
            accent=(204, 170, 64), helmet=(78, 86, 90), lens=(240, 180, 70), mask=(60, 66, 62),
            fuel=(176, 112, 50), fuel_d=(120, 80, 40), camo=(70, 82, 58), hull=(76, 86, 66)),
    1: dict(cloth=(88, 62, 50), cloth_d=(58, 42, 36), armor=(66, 54, 52), armor_d=(44, 36, 36),
            accent=(182, 44, 38), helmet=(52, 46, 46), lens=(255, 70, 50), mask=(70, 72, 70),
            fuel=(130, 60, 40), fuel_d=(84, 40, 30), camo=(76, 64, 48), hull=(94, 62, 50)),
}

STANCES = ("stand", "crouch", "prone")
STANCE_SPREAD = {"stand": 1.0, "crouch": 0.75, "prone": 0.55}   # dispersão do atirador por postura
STANCE_DMG = {"stand": 1.0, "crouch": 0.85, "prone": 0.65}       # dano de explosão recebido por postura
HIT = {"stand": (9, 58), "crouch": (11, 42), "prone": (18, 16)}  # caixa de acerto (meia-largura, altura)
TOPS = {"stand": 62, "crouch": 50, "prone": 22}

UNITS = [
    dict(name="Guarda",       key="guarda",       cost=20,  hp=45,  speed=55, dmg=6,  range=170, cd=0.7,  aoe=0,  kind="rifle",  anim=0.21, stances=True,  spread=0.13,  pierce=0.10),
    dict(name="Lança-chamas", key="lanca-chamas", cost=45,  hp=60,  speed=48, dmg=3,  range=95,  cd=0.12, aoe=0,  kind="flame",  anim=0.21, stances=True,  spread=0.0,   pierce=0.0),
    dict(name="Atirador",     key="atirador",     cost=60,  hp=35,  speed=45, dmg=40, range=380, cd=2.5,  aoe=0,  kind="sniper", anim=0.21, stances=True,  spread=0.022, pierce=1.0),
    dict(name="Artilheiro",   key="artilheiro",   cost=85,  hp=80,  speed=34, dmg=28, range=280, cd=2.0,  aoe=55, kind="heavy",  anim=0.21, stances=True,  scatter=16),
    dict(name="Juggernaut",   key="juggernaut",   cost=130, hp=480, speed=26, dmg=3,  range=210, cd=0.09, aoe=0,  kind="jugg",   anim=0.26, stances=False, spread=0.17,  pierce=0.0),
    dict(name="Blindado",     key="blindado",     cost=170, hp=350, speed=30, dmg=16, range=240, cd=0.9,  aoe=30, kind="tank",   anim=0.95, stances=False, scatter=9),
]


# ====================================================================== utilidades
def lighten(c, n):
    return tuple(min(255, v + n) for v in c)


def darken(c, n):
    return tuple(max(0, v - n) for v in c)


def mix(a, b, t):
    return tuple(int(a[i] + (b[i] - a[i]) * t) for i in range(3))


def lerp(a, b, t):
    return (a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t)


def ik(a, b, l1, l2, flip=1):
    """IK de dois ossos: devolve (articulacao, ponta)."""
    dx, dy = b[0] - a[0], b[1] - a[1]
    dist = math.hypot(dx, dy) or 0.001
    ux, uy = dx / dist, dy / dist
    d = min(dist, l1 + l2 - 0.02)
    al = (l1 * l1 - l2 * l2 + d * d) / (2 * d)
    h = math.sqrt(max(0.0, l1 * l1 - al * al))
    px, py = (uy, -ux) if flip > 0 else (-uy, ux)
    mid = (a[0] + ux * al, a[1] + uy * al)
    return (mid[0] + px * h, mid[1] + py * h), (a[0] + ux * d, a[1] + uy * d)


def dome(c, r, steps=9):
    pts = []
    for i in range(steps + 1):
        a = math.radians(180 + 180 * i / steps)
        pts.append((c[0] + math.cos(a) * r, c[1] + math.sin(a) * r))
    return pts


_glow_cache, _soft_cache = {}, {}


def glow(r, col, level=1.0):
    """brilho para mistura aditiva (fogo, clarões)"""
    r = max(4, (int(r) // 4) * 4)
    lv = max(0.25, round(level * 4) / 4)
    key = (r, col, lv)
    if key not in _glow_cache:
        s = pygame.Surface((r * 2, r * 2))
        s.fill((0, 0, 0))
        steps = max(4, r // 2)
        for i in range(steps, 0, -1):
            f = i / steps
            k = (1 - f) ** 1.6 * lv
            pygame.draw.circle(s, (int(col[0] * k), int(col[1] * k), int(col[2] * k)), (r, r), max(1, int(r * f)))
        _glow_cache[key] = s.convert()
    return _glow_cache[key]


def soft(r, col):
    """circulo suave com alfa (fumaça, poeira)"""
    r = max(4, (int(r) // 4) * 4)
    key = (r, col)
    if key not in _soft_cache:
        s = pygame.Surface((r * 2, r * 2), pygame.SRCALPHA)
        steps = max(4, r // 2)
        for i in range(steps, 0, -1):
            f = i / steps
            a = int(255 * (1 - f) ** 1.2)
            pygame.draw.circle(s, (col[0], col[1], col[2], a), (r, r), max(1, int(r * f)))
        _soft_cache[key] = s
    return _soft_cache[key]


class Painter:
    """Desenha em alta resolução e reduz no final (bordas suaves, sem serrilhado)."""

    def __init__(self, w, h):
        self.w, self.h = w, h
        self.surf = pygame.Surface((int(w * SS), int(h * SS)), pygame.SRCALPHA)

    @staticmethod
    def _p(p):
        return (p[0] * SS, p[1] * SS)

    def poly(self, pts, col, ow=0.8, outline=OUT):
        q = [self._p(p) for p in pts]
        pygame.draw.polygon(self.surf, col, q)
        if ow:
            lw = max(1, int(ow * SS))
            pygame.draw.polygon(self.surf, outline, q, lw)
            for a in q:
                pygame.draw.circle(self.surf, outline, a, max(1, lw // 2))

    def cap(self, a, b, w, col, ow=0.8, outline=OUT, shade=True):
        a2, b2 = self._p(a), self._p(b)
        if ow:
            ww = max(2, int((w + ow * 2) * SS))
            pygame.draw.line(self.surf, outline, a2, b2, ww)
            pygame.draw.circle(self.surf, outline, a2, ww // 2)
            pygame.draw.circle(self.surf, outline, b2, ww // 2)
        ww = max(1, int(w * SS))
        pygame.draw.line(self.surf, col, a2, b2, ww)
        pygame.draw.circle(self.surf, col, a2, max(1, ww // 2))
        pygame.draw.circle(self.surf, col, b2, max(1, ww // 2))
        if shade and w >= 3:
            dx, dy = b[0] - a[0], b[1] - a[1]
            ln = math.hypot(dx, dy) or 1
            nx, ny = dy / ln, -dx / ln
            if ny > 0:
                nx, ny = -nx, -ny
            off = w * 0.22 * SS
            hw = max(1, int(w * 0.2 * SS))
            pygame.draw.line(self.surf, lighten(col, 26),
                             (a2[0] + nx * off, a2[1] + ny * off), (b2[0] + nx * off, b2[1] + ny * off), hw)

    def circ(self, c, r, col, ow=0.8, outline=OUT):
        cc = self._p(c)
        if ow:
            pygame.draw.circle(self.surf, outline, cc, max(1, int((r + ow) * SS)))
        pygame.draw.circle(self.surf, col, cc, max(1, int(r * SS)))

    def finish(self, scale=1.0):
        size = (max(1, int(self.w * scale)), max(1, int(self.h * scale)))
        return pygame.transform.smoothscale(self.surf, size).convert_alpha()


# ====================================================================== sprites
def draw_head(P, pal, kind, team, hc):
    hx, hy = hc
    P.circ(hc, 4.7, SKIN)
    if kind == "sniper":
        P.poly([(hx - 6.8, hy + 4.5)] + dome((hx - 0.4, hy - 0.2), 6.3) +
               [(hx + 6.2, hy + 0.4), (hx + 3.0, hy + 1.2), (hx - 3.5, hy + 1.0)], pal["camo"])
        P.poly([(hx - 1, hy + 2.0), (hx + 5.0, hy + 2.2), (hx + 4.6, hy + 5.2), (hx + 0.5, hy + 6.0)], pal["cloth_d"])
        P.cap((hx + 1.3, hy + 1.0), (hx + 4.9, hy + 0.9), 1.6, pal["lens"], ow=0.4, shade=False)
        return
    P.poly([(hx - 7.2, hy + 3.4)] + dome((hx - 0.4, hy - 0.6), 5.9) +
           [(hx + 6.8, hy - 0.2), (hx + 3.0, hy + 0.9), (hx - 3.6, hy + 0.6)], pal["helmet"])
    P.cap((hx - 3.2, hy - 4.9), (hx + 2.0, hy - 5.6), 1.1, lighten(pal["helmet"], 32), ow=0, shade=False)
    P.circ((hx - 1.0, hy - 2.6), 0.9, pal["accent"], ow=0)
    if kind == "flame" or team == 1:
        P.poly([(hx - 0.6, hy + 2.0), (hx + 5.2, hy + 2.2), (hx + 5.4, hy + 4.8), (hx + 1.8, hy + 5.8),
                (hx - 0.6, hy + 4.4)], pal["mask"])
        P.circ((hx + 5.6, hy + 3.9), 1.8, STEEL, ow=0.5)
        if kind == "flame":
            P.circ((hx + 2.0, hy + 0.8), 1.8, pal["lens"], ow=0.5)
            P.circ((hx + 4.8, hy + 0.8), 1.5, pal["lens"], ow=0.5)
        else:
            P.cap((hx + 1.2, hy + 0.9), (hx + 4.9, hy + 0.7), 1.7, pal["lens"], ow=0.4, shade=False)
    else:
        P.cap((hx + 1.2, hy + 1.2), (hx + 4.9, hy + 1.0), 1.8, pal["lens"], ow=0.4, shade=False)
        P.cap((hx - 1.0, hy + 4.6), (hx + 3.6, hy + 5.0), 1.0, pal["cloth_d"], ow=0, shade=False)
    if kind == "heavy":
        P.poly([(hx + 2.0, hy - 1.0), (hx + 6.4, hy - 0.5), (hx + 6.2, hy + 5.0), (hx + 2.6, hy + 6.2)],
               pal["armor_d"], ow=0.6)
        P.cap((hx + 3.2, hy + 1.6), (hx + 5.6, hy + 1.6), 0.8, pal["lens"], ow=0, shade=False)


def weapon_parts(P, pal, kind, x0, y0, hose_from=None):
    """Devolve (desenhar_arma, mao_proxima, mao_distante, ponta_do_cano)."""
    if kind == "rifle":
        hand_n, hand_f, tip = (x0 + 2.4, y0 + 3.6), (x0 + 15.5, y0 + 1.6), (x0 + 28.3, y0 - 0.9)

        def weapon():
            P.poly([(x0 - 10, y0 - 1.8), (x0 - 1.5, y0 - 2.6), (x0 - 1.5, y0 + 2.0), (x0 - 9, y0 + 3.8)], GUNBLK)
            P.poly([(x0 - 2.5, y0 - 3.4), (x0 + 11.5, y0 - 3.4), (x0 + 11.5, y0 + 2.4), (x0 - 2.5, y0 + 2.4)], STEEL_D)
            P.cap((x0 + 10.5, y0 - 0.4), (x0 + 20.5, y0 - 0.4), 4.0, GUNBLK)
            P.cap((x0 + 20.5, y0 - 0.9), (x0 + 26.5, y0 - 0.9), 1.7, STEEL)
            P.poly([(x0 + 25.5, y0 - 2.4), (x0 + 28.3, y0 - 2.4), (x0 + 28.3, y0 + 0.6), (x0 + 25.5, y0 + 0.6)],
                   STEEL_D, ow=0.5)
            P.cap((x0 + 2.5, y0 - 5.0), (x0 + 9.0, y0 - 5.0), 2.6, GUNBLK)
            P.circ((x0 + 9.2, y0 - 5.0), 1.2, pal["lens"], ow=0.3)
            P.poly([(x0 + 5.5, y0 + 2.2), (x0 + 9.8, y0 + 2.2), (x0 + 11.0, y0 + 8.8), (x0 + 7.2, y0 + 9.4)], GUNBLK)
            P.poly([(x0 + 0.8, y0 + 2.2), (x0 + 4.0, y0 + 2.2), (x0 + 3.2, y0 + 7.4), (x0 + 0.2, y0 + 6.8)], GUNBLK)
    elif kind == "flame":
        hand_n, hand_f, tip = (x0 + 1.5, y0 + 3.6), (x0 + 13.0, y0 + 1.2), (x0 + 25.5, y0 - 0.5)

        def weapon():
            if hose_from is not None:
                p0, p3 = hose_from, (x0 - 1, y0 - 3)
                top = min(p0[1], p3[1]) - 4
                p1 = (p0[0] + (p3[0] - p0[0]) * 0.33, top)
                p2 = (p0[0] + (p3[0] - p0[0]) * 0.66, top + 1)
                for a, b in ((p0, p1), (p1, p2), (p2, p3)):
                    P.cap(a, b, 1.8, (28, 28, 30), ow=0.4, shade=False)
            P.cap((x0 - 9, y0), (x0 - 5, y0), 3.4, GUNBLK)
            P.poly([(x0 - 6, y0 - 3.2), (x0 + 8, y0 - 3.6), (x0 + 9, y0 + 3), (x0 - 5, y0 + 3.2)], STEEL_D)
            P.cap((x0 + 8, y0 - 0.5), (x0 + 21, y0 - 0.5), 3.0, STEEL)
            P.poly([(x0 + 20.5, y0 - 2.8), (x0 + 25, y0 - 3.6), (x0 + 25, y0 + 2.6), (x0 + 20.5, y0 + 1.8)],
                   pal["fuel_d"], ow=0.6)
            P.circ((x0 + 25.5, y0 - 0.5), 1.4, (255, 200, 80), ow=0)
            P.circ((x0 + 3, y0 - 4.4), 1.4, STEEL_L, ow=0.4)
            P.poly([(x0 + 0.8, y0 + 3), (x0 + 3.8, y0 + 3), (x0 + 3.0, y0 + 7.6), (x0 + 0.2, y0 + 7.0)], GUNBLK)
    elif kind == "sniper":
        hand_n, hand_f, tip = (x0 + 0.5, y0 + 3.3), (x0 + 15.0, y0 + 0.8), (x0 + 38.0, y0 - 0.8)

        def weapon():
            P.poly([(x0 - 11, y0 - 2.4), (x0 - 1, y0 - 2.8), (x0 - 1, y0 + 1.8), (x0 - 9, y0 + 4.2)], GUNBLK)
            P.poly([(x0 - 2.5, y0 - 3.2), (x0 + 9, y0 - 3.2), (x0 + 9, y0 + 2.2), (x0 - 2.5, y0 + 2.2)], STEEL_D)
            P.cap((x0 + 9, y0 - 0.8), (x0 + 34, y0 - 0.8), 1.8, STEEL)
            P.cap((x0 + 27, y0 - 0.8), (x0 + 38, y0 - 0.8), 3.4, GUNBLK)
            P.cap((x0 + 0.5, y0 - 5.6), (x0 + 13, y0 - 5.6), 3.3, GUNBLK)
            P.circ((x0 + 13.6, y0 - 5.6), 1.8, pal["lens"], ow=0.4)
            P.cap((x0 + 3, y0 - 3.4), (x0 + 3, y0 - 5), 1.4, STEEL_D, ow=0.3, shade=False)
            P.cap((x0 + 10, y0 - 3.4), (x0 + 10, y0 - 5), 1.4, STEEL_D, ow=0.3, shade=False)
            P.cap((x0 + 17, y0 + 0.8), (x0 + 14, y0 + 7.8), 1.0, STEEL, ow=0.4, shade=False)
            P.cap((x0 + 17, y0 + 0.8), (x0 + 20.6, y0 + 7.8), 1.0, STEEL, ow=0.4, shade=False)
            P.poly([(x0 + 4, y0 + 2.2), (x0 + 7.6, y0 + 2.2), (x0 + 8, y0 + 6.4), (x0 + 4.6, y0 + 6.6)], GUNBLK)
    else:  # lançador pesado
        hand_n, hand_f, tip = (x0 + 6, y0 + 10), (x0 + 15.5, y0 + 10.4), (x0 + 30, y0 + 0.8)

        def weapon():
            P.poly([(x0 - 11.5, y0 - 4.9), (x0 - 8, y0 - 3.4), (x0 - 8, y0 + 4.6), (x0 - 11.5, y0 + 6.1)], STEEL_D)
            P.cap((x0 - 9, y0), (x0 + 23, y0 + 1.2), 7.4, pal["armor_d"])
            P.poly([(x0 + 22.5, y0 - 2.2), (x0 + 30, y0 + 0.8), (x0 + 22.5, y0 + 3.8)], pal["accent"], ow=0.6)
            P.cap((x0 + 8, y0 - 3.4), (x0 + 8, y0 + 3.8), 1.5, pal["accent"], ow=0, shade=False)
            P.cap((x0 + 3, y0 - 5.2), (x0 + 9, y0 - 5.2), 2.4, GUNBLK)
            P.circ((x0 + 9.4, y0 - 5.2), 1.1, pal["lens"], ow=0.3)
            P.poly([(x0 + 5, y0 + 4), (x0 + 8, y0 + 4), (x0 + 7.5, y0 + 10.6), (x0 + 4.5, y0 + 10.6)], GUNBLK)
            P.cap((x0 + 15, y0 + 4.6), (x0 + 15.5, y0 + 10.1), 2.4, GUNBLK)
    return weapon, hand_n, hand_f, tip


def _make_arm(P, pal, flip_clamp=None):
    def arm(sh, hand, col):
        elbow, end = ik(sh, hand, 9.2, 9.2, -1)
        if flip_clamp is not None and elbow[1] > flip_clamp:
            elbow = (elbow[0], flip_clamp)
        P.cap(sh, elbow, 4.8, col)
        P.cap(elbow, end, 4.2, col)
        mid = (elbow[0] + (end[0] - elbow[0]) * 0.35, elbow[1] + (end[1] - elbow[1]) * 0.35)
        P.cap(mid, end, 4.7, pal["armor_d"], ow=0.5)
    return arm


def draw_infantry(kind, team, ph, mode, stance="stand"):
    if stance == "prone":
        return draw_prone(kind, team, mode)
    pal = PAL[team]
    P = Painter(112, 84)
    cx, fy = 36.0, 78.0
    crouch = stance == "crouch"
    walking = mode == "walk" and not crouch
    bob = abs(math.cos(ph)) * 1.1 if walking else 0.0
    sy = fy - (16.5 if crouch else 25.0) + bob
    hip = (cx, sy)
    L = 1.0 if kind == "sniper" else (3.0 if crouch else 2.0)
    rec = 1.6 if mode == "fire" else 0.0
    heavy = kind == "heavy"

    for i in (0, 1):
        phi = ph + i * math.pi
        if walking:
            fx = cx + math.sin(phi) * 7.5
            fyy = fy - max(0.0, math.cos(phi)) * 4.0
        elif crouch:
            fx = cx + (-9.5 if i == 0 else 8.5)
            fyy = fy
        else:
            fx = cx + (-6.0 if i == 0 else 7.0)
            fyy = fy
        knee, foot = ik(hip, (fx, fyy), 13.2, 13.2, 1)
        shade = pal["cloth_d"] if i == 0 else pal["cloth"]
        P.cap(hip, knee, 7.0 if heavy else 6.2, shade)
        P.cap(knee, foot, 5.2, shade)
        P.circ(knee, 3.0, pal["armor"])
        bx, by = foot
        P.poly([(bx - 3.2, by - 6.5), (bx + 2.2, by - 6.5), (bx + 2.8, by - 3.5), (bx + 7.6, by - 1.8),
                (bx + 7.6, by), (bx - 3.6, by)], BOOT)

    bx0 = cx - 8.5 + L * 0.5
    if kind == "flame":
        P.cap((bx0 - 1, sy - 21), (bx0 - 1, sy - 7), 7.6, pal["fuel"])
        P.cap((bx0 - 1, sy - 17), (bx0 - 1, sy - 16), 7.8, pal["fuel_d"], ow=0, shade=False)
        P.cap((bx0 - 1, sy - 11), (bx0 - 1, sy - 10), 7.8, pal["fuel_d"], ow=0, shade=False)
        P.circ((bx0 - 1, sy - 24), 1.6, STEEL_L)
    elif kind == "sniper":
        P.poly([(cx - 6, sy - 20), (cx - 12.5, sy - 18.5), (cx - 13.5, sy - 6), (cx - 6, sy - 4)], pal["cloth_d"])
        P.cap((cx - 12.5, sy - 21), (cx - 5, sy - 22.5), 4.2, pal["camo"])
    elif heavy:
        P.poly([(cx - 6, sy - 21), (cx - 15, sy - 19), (cx - 16.5, sy - 4), (cx - 6, sy - 3)], pal["armor_d"])
        P.cap((cx - 13, sy - 22), (cx - 7, sy - 29), 3.6, STEEL)
        P.poly([(cx - 7, sy - 29.8), (cx - 4.4, sy - 29.2), (cx - 6.4, sy - 26.4)], pal["accent"], ow=0.4)
        P.cap((cx - 15.5, sy - 13), (cx - 15.5, sy - 8), 3.0, pal["cloth_d"])
    else:
        P.poly([(cx - 6, sy - 20), (cx - 12.5, sy - 18.5), (cx - 13.5, sy - 6), (cx - 6, sy - 4)], pal["cloth_d"])
        P.cap((cx - 12, sy - 21.5), (cx - 5.5, sy - 22.5), 3.6, pal["cloth"])
        P.circ((cx - 11, sy - 8), 2.3, STEEL_D)

    torso = [(cx - 5.3, sy - 0.5), (cx + 5.4, sy - 0.5), (cx + 7.4 + L * 0.5, sy - 10), (cx + 6.0 + L, sy - 20.5),
             (cx + 2.5 + L, sy - 22.5), (cx - 3 + L, sy - 22.5), (cx - 6.8 + L, sy - 19.5), (cx - 7.6, sy - 10)]
    P.poly(torso, pal["cloth"])
    if heavy:
        P.circ((cx - 4.0 + L, sy - 20), 4.6, pal["armor"])
    plate = [(cx - 5.6, sy - 4.5), (cx + 6.4, sy - 4.5), (cx + 7.0 + L * 0.5, sy - 11), (cx + 5.2 + L, sy - 19.5),
             (cx - 4.2 + L, sy - 19.5), (cx - 6.6 + L * 0.3, sy - 11)]
    P.poly(plate, pal["armor"])
    P.cap((cx - 6, sy - 8.8), (cx + 6.6, sy - 8.8), 0.9, pal["armor_d"], ow=0, shade=False)
    P.poly([(cx - 4.2, sy - 15), (cx + 5.8 + L * 0.5, sy - 15), (cx + 5.5 + L * 0.5, sy - 13.2), (cx - 4.5, sy - 13.2)],
           pal["accent"], ow=0)
    P.cap((cx - 5.4, sy - 1.2), (cx + 5.5, sy - 1.2), 3.0, BOOT)
    P.circ((cx + 1, sy - 1.2), 1.1, pal["accent"], ow=0)
    P.poly([(cx + 2.5, sy - 3.5), (cx + 6.3, sy - 3.5), (cx + 6.7, sy + 1.8), (cx + 2.8, sy + 2.2)], pal["cloth_d"])
    P.poly([(cx - 4.8, sy - 3.2), (cx - 1.0, sy - 3.2), (cx - 1.2, sy + 2), (cx - 4.9, sy + 1.6)], pal["cloth_d"])

    if kind == "sniper":
        P.poly([(cx - 8 + L, sy - 21), (cx + 4 + L, sy - 22), (cx + 3 + L, sy - 9), (cx - 3, sy - 2),
                (cx - 12, sy + 1), (cx - 14, sy - 8)], pal["camo"])
        for tx, ty, tc in [(-13, -6, (96, 86, 60)), (-11, -1, (58, 66, 46)), (-8, 1.5, (82, 92, 62)),
                           (-5, 0, (96, 86, 60)), (-2, -2, (58, 66, 46)), (1, -5, (82, 92, 62))]:
            P.poly([(cx + tx - 1.6, sy + ty), (cx + tx + 1.6, sy + ty), (cx + tx + 0.2, sy + ty + 5)], tc, ow=0.4)

    hc = (cx + 2.4 + L, sy - 28.0)
    P.cap((cx + 1.0 + L, sy - 21.5), (hc[0] - 0.4, hc[1] + 3.0), 3.8, SKIN)
    draw_head(P, pal, kind, team, hc)

    sh_n = (cx + 4.6 + L, sy - 19.0)
    sh_f = (cx - 0.8 + L, sy - 19.6)
    arm = _make_arm(P, pal)
    if kind == "sniper":
        x0, y0 = cx + 2.5 + L - rec, sy - 13.0
    elif heavy:
        x0, y0 = cx + L - rec, sy - 22.6
    else:
        x0, y0 = cx + 2.0 + L - rec, sy - 12.5
    hose = (bx0 - 1, sy - 23) if kind == "flame" else None
    weapon, hand_n, hand_f, tip = weapon_parts(P, pal, kind, x0, y0, hose)
    arm(sh_f, hand_f, pal["cloth_d"])
    weapon()
    P.circ(hand_f, 2.2, GLOVE, ow=0.5)
    arm(sh_n, hand_n, pal["cloth"])
    P.circ(hand_n, 2.2, GLOVE, ow=0.5)
    P.circ((sh_n[0], sh_n[1] - 0.4), 5.0 if heavy else 3.9, pal["armor"])
    P.cap((sh_n[0] - 1.8, sh_n[1] - 1.2), (sh_n[0] + 1.6, sh_n[1] - 1.8), 1.0, pal["accent"], ow=0, shade=False)
    return P.finish(), (tip[0] - cx, fy - tip[1])


def draw_prone(kind, team, mode):
    """Soldado deitado de bruços, mirando para a direita."""
    pal = PAL[team]
    P = Painter(112, 84)
    cx, fy = 36.0, 78.0
    o = 42.0
    rec = 1.4 if mode == "fire" else 0.0
    heavy = kind == "heavy"
    hip = (o - 19, fy - 6.8)

    for knee, foot, shade in (((o - 28, fy - 9.5), (o - 36, fy - 4.6), pal["cloth_d"]),
                              ((o - 29, fy - 5.2), (o - 37, fy - 3.2), pal["cloth"])):
        P.cap(hip, knee, 6.2, shade)
        P.cap(knee, foot, 5.0, shade)
        P.circ(knee, 2.7, pal["armor"])
        P.poly([(foot[0] - 3.5, foot[1] - 3.4), (foot[0] + 1.2, foot[1] - 3.8), (foot[0] + 2.2, foot[1] + 1.3),
                (foot[0] - 4.2, foot[1] + 1.3)], BOOT)

    # equipamento nas costas
    if kind == "flame":
        P.cap((o - 19, fy - 12.6), (o - 7, fy - 13.2), 6.8, pal["fuel"])
        for xx in (-16, -11):
            P.cap((o + xx, fy - 16), (o + xx, fy - 9.6), 1.0, pal["fuel_d"], ow=0, shade=False)
        hose = (o - 13, fy - 16.4)
    else:
        hose = None
        if heavy:
            P.poly([(o - 20, fy - 10.5), (o - 9, fy - 14.5), (o - 6, fy - 9), (o - 19, fy - 8)], pal["armor_d"])
            P.cap((o - 18, fy - 15.2), (o - 8, fy - 16.8), 3.4, STEEL)
        else:
            P.poly([(o - 19, fy - 10.5), (o - 9, fy - 13.5), (o - 6, fy - 9), (o - 18, fy - 8)], pal["cloth_d"])
            P.cap((o - 17, fy - 14.2), (o - 8, fy - 15.4), 3.4, pal["camo"] if kind == "sniper" else pal["cloth"])

    P.poly([(o - 20, fy - 2.2), (o + 1, fy - 2.6), (o + 4.5, fy - 6.5), (o + 3, fy - 11), (o - 4, fy - 12.6),
            (o - 19, fy - 11)], pal["cloth"])
    P.poly([(o - 17, fy - 4), (o + 0, fy - 4.4), (o + 2.2, fy - 7), (o + 1, fy - 10), (o - 14, fy - 10.6)], pal["armor"])
    P.poly([(o - 12, fy - 9.8), (o - 6, fy - 10.2), (o - 6, fy - 8.6), (o - 12, fy - 8.4)], pal["accent"], ow=0)
    P.cap((o - 16.5, fy - 2.8), (o - 16.8, fy - 10.8), 2.6, BOOT)
    if kind == "sniper":
        P.poly([(o - 21, fy - 11), (o - 5, fy - 13.4), (o - 3, fy - 6), (o - 12, fy - 1), (o - 24, fy - 2)], pal["camo"])
        for k, tc in enumerate(((96, 86, 60), (58, 66, 46), (82, 92, 62), (96, 86, 60))):
            P.poly([(o - 19 + k * 4.5, fy - 12), (o - 15.5 + k * 4.5, fy - 12.4), (o - 17 + k * 4.5, fy - 16)], tc, ow=0.4)

    sh_n, sh_f = (o + 3.0, fy - 9.4), (o + 1.0, fy - 10.2)
    if kind == "sniper":
        x0, y0 = o + 5.5 - rec, fy - 5.4
    elif heavy:
        x0, y0 = o + 4.0 - rec, fy - 11.0
    else:
        x0, y0 = o + 5.5 - rec, fy - 5.2
    weapon, hand_n, hand_f, tip = weapon_parts(P, pal, kind, x0, y0, hose)
    arm = _make_arm(P, pal, flip_clamp=fy - 1.0)
    P.cap((o + 1.5, fy - 8.6), (o + 6.5, fy - 11), 3.6, SKIN)
    arm(sh_f, hand_f, pal["cloth_d"])
    weapon()
    P.circ(hand_f, 2.2, GLOVE, ow=0.5)
    draw_head(P, pal, kind, team, (o + 7.0, fy - 12.8))
    arm(sh_n, hand_n, pal["cloth"])
    P.circ(hand_n, 2.2, GLOVE, ow=0.5)
    P.circ((sh_n[0], sh_n[1] - 0.4), 3.6, pal["armor"])
    return P.finish(), (tip[0] - cx, fy - tip[1])


def draw_juggernaut(team, ph, mode):
    """Brutamontes blindado com metralhadora rotativa (personagem original)."""
    pal = PAL[team]
    P = Painter(150, 116)
    cx, fy = 50.0, 110.0
    walking = mode == "walk"
    bob = abs(math.cos(ph)) * 1.0 if walking else 0.0
    sy = fy - 34.0 + bob
    hip = (cx, sy)
    L = 3.0
    jit = 0.0 if mode in ("walk", "idle") else (0.9 if mode == "fire" else -0.9)
    armor, armor_d = pal["armor"], pal["armor_d"]
    plate = lighten(armor, 10)

    for i in (0, 1):
        phi = ph + i * math.pi
        if walking:
            fx, fyy = cx + math.sin(phi) * 6.0, fy - max(0.0, math.cos(phi)) * 3.0
        else:
            fx, fyy = cx + (-7.5 if i == 0 else 8.5), fy
        knee, foot = ik(hip, (fx, fyy), 17.4, 17.4, 1)
        P.cap(hip, knee, 10.5, pal["cloth_d"] if i == 0 else pal["cloth"])
        P.cap(knee, foot, 8.8, armor_d if i == 0 else armor)
        P.circ(knee, 5.2, armor)
        P.poly([(knee[0] - 1.5, knee[1] - 4.5), (knee[0] + 5.5, knee[1] - 2), (knee[0] + 5, knee[1] + 4),
                (knee[0] - 2, knee[1] + 3.5)], plate)
        bx, by = foot
        P.poly([(bx - 5, by - 9), (bx + 3.5, by - 9), (bx + 4.5, by - 5), (bx + 11, by - 2.5), (bx + 11, by),
                (bx - 5.5, by)], BOOT)

    # mochila com tambor de munição
    P.poly([(cx - 9, sy - 34), (cx - 21, sy - 31), (cx - 23, sy - 8), (cx - 9, sy - 5)], armor_d)
    for k in range(3):
        P.cap((cx - 19, sy - 28 + k * 5), (cx - 12, sy - 28 + k * 5), 1.0, OUT, ow=0, shade=False)
    P.cap((cx - 16, sy - 34), (cx - 18, sy - 43), 3.6, STEEL)
    P.circ((cx - 17, sy - 18), 8.2, STEEL_D)
    P.circ((cx - 17, sy - 18), 4.6, STEEL)
    P.circ((cx - 17, sy - 18), 1.6, GUNBLK, ow=0.3)

    # tronco
    P.poly([(cx - 8, sy - 1), (cx + 8, sy - 1), (cx + 12 + L * 0.4, sy - 14), (cx + 11 + L, sy - 30),
            (cx + 4 + L, sy - 34), (cx - 5 + L, sy - 34), (cx - 11 + L, sy - 29), (cx - 12, sy - 14)], pal["cloth"])
    P.circ((cx - 6 + L, sy - 31), 8.2, armor_d)
    P.poly([(cx - 9, sy - 6), (cx + 10, sy - 6), (cx + 12.5 + L * 0.4, sy - 15), (cx + 9.5 + L, sy - 29),
            (cx - 7.5 + L, sy - 29), (cx - 11, sy - 15)], armor)
    for yy in (-12, -18, -24):
        P.cap((cx - 10 + L * 0.2, sy + yy), (cx + 11 + L * 0.4, sy + yy), 1.2, armor_d, ow=0, shade=False)
    P.cap((cx + 1 + L * 0.3, sy - 29), (cx + 1, sy - 6), 1.0, armor_d, ow=0, shade=False)
    P.poly([(cx - 6, sy - 20), (cx + 1 + L * 0.3, sy - 23), (cx + 8 + L * 0.4, sy - 20), (cx + 8 + L * 0.4, sy - 17.5),
            (cx + 1 + L * 0.3, sy - 20.5), (cx - 6, sy - 17.5)], pal["accent"], ow=0)
    P.cap((cx - 9, sy - 2), (cx + 9, sy - 2), 5.0, BOOT)
    P.circ((cx + 1, sy - 2), 2.4, pal["accent"], ow=0.4)
    P.poly([(cx - 8, sy - 1), (cx - 2, sy - 1), (cx - 3, sy + 7), (cx - 9, sy + 6)], armor_d)
    P.poly([(cx + 1, sy - 1), (cx + 8, sy - 1), (cx + 8.5, sy + 7), (cx + 1.5, sy + 7.5)], armor_d)

    # cabeça: elmo fechado com visor estreito
    hx, hy = cx + 3.0 + L, sy - 39.0
    P.cap((cx + L, sy - 33), (hx - 0.5, hy + 5), 5.6, pal["cloth_d"])
    P.poly([(hx - 8.5, hy + 4.5)] + dome((hx - 0.5, hy - 0.5), 8.2) +
           [(hx + 8.6, hy + 0.2), (hx + 8.2, hy + 7.5), (hx + 3, hy + 9), (hx - 4, hy + 6)], armor_d)
    P.cap((hx + 1.5, hy + 1.4), (hx + 7.6, hy + 1.2), 2.2, pal["lens"], ow=0.5, shade=False)
    for k in range(3):
        P.cap((hx + 3.0, hy + 4.4 + k * 1.5), (hx + 7.2, hy + 4.4 + k * 1.5), 0.7, OUT, ow=0, shade=False)
    P.cap((hx - 5.2, hy - 8.0), (hx + 4, hy - 8.8), 1.6, pal["accent"], ow=0, shade=False)

    # metralhadora rotativa
    x0, y0 = cx + 4 + L + jit, sy - 14.0
    offs = {"fire": (-2.6, 1.0, 3.8), "fire2": (-3.8, -1.0, 2.6)}.get(mode, (-3.4, 0.0, 3.4))
    p0, c, p2 = (cx - 17, sy - 18), (cx - 4, sy + 8), (x0 + 1, y0 + 6.5)
    prev = None
    for k in range(11):
        t = k / 10
        bxp = (1 - t) ** 2 * p0[0] + 2 * (1 - t) * t * c[0] + t * t * p2[0]
        byp = (1 - t) ** 2 * p0[1] + 2 * (1 - t) * t * c[1] + t * t * p2[1]
        if prev is not None:
            P.cap(prev, (bxp, byp), 2.2, (150, 120, 50), ow=0.4, shade=False)
        P.circ((bxp, byp), 1.5, (205, 168, 70), ow=0.3)
        prev = (bxp, byp)
    sh_n, sh_f = (cx + 8 + L, sy - 28.0), (cx - 5 + L, sy - 28.5)
    hand_n, hand_f = (x0 - 1, y0 + 6.5), (x0 + 6, y0 + 7.0)

    def jarm(sh, hand, col):
        elbow, end = ik(sh, hand, 13.0, 13.0, -1)
        P.cap(sh, elbow, 8.2, col)
        P.cap(elbow, end, 7.0, col)
        mid = (elbow[0] + (end[0] - elbow[0]) * 0.35, elbow[1] + (end[1] - elbow[1]) * 0.35)
        P.cap(mid, end, 8.4, armor_d, ow=0.6)

    jarm(sh_f, hand_f, pal["cloth_d"])
    P.cap((x0 - 12, y0), (x0 - 6, y0), 9, STEEL_D)
    for off in offs:
        P.cap((x0 + 14, y0 + off), (x0 + 46, y0 + off), 2.6, STEEL, ow=0.5)
    P.cap((x0 + 26, y0 - 5.5), (x0 + 26, y0 + 5.5), 2.2, STEEL_D, ow=0.5)
    P.cap((x0 + 43, y0 - 5.5), (x0 + 43, y0 + 5.5), 2.2, STEEL_D, ow=0.5)
    P.poly([(x0 - 6, y0 - 5.5), (x0 + 14, y0 - 6), (x0 + 14, y0 + 5.5), (x0 - 6, y0 + 6)], armor_d)
    P.cap((x0 - 4, y0 - 3), (x0 + 12, y0 - 3.2), 1.2, plate, ow=0, shade=False)
    P.cap((x0 + 2, y0 - 6), (x0 + 2, y0 - 10), 2.0, STEEL_D, ow=0.4)
    P.cap((x0 + 2, y0 - 10), (x0 + 10, y0 - 10), 2.0, STEEL_D, ow=0.4)
    P.circ(hand_f, 3.6, GLOVE, ow=0.5)
    jarm(sh_n, hand_n, pal["cloth"])
    P.circ(hand_n, 3.6, GLOVE, ow=0.5)
    P.circ((sh_n[0], sh_n[1] - 0.6), 8.8, armor)
    P.cap((sh_n[0] - 5.5, sh_n[1] - 4.0), (sh_n[0] + 5.5, sh_n[1] - 5.6), 2.2, pal["accent"], ow=0, shade=False)
    P.circ((sh_n[0] + 0.5, sh_n[1] - 0.2), 4.0, plate, ow=0.5)
    return P.finish(), (x0 + 46 - cx, fy - y0)


def draw_tank(team, ph, mode):
    pal = PAL[team]
    P = Painter(156, 104)
    cx, fy = 70.0, 98.0
    walking = mode == "walk"
    rec = 3.2 if mode == "fire" else 0.0
    yb = math.sin(ph * 2) * 0.6 if walking else 0.0
    hull, hull_d = pal["hull"], darken(pal["hull"], 22)

    # esteiras
    P.cap((cx - 40, fy - 9), (cx + 40, fy - 9), 16, (36, 36, 40), shade=False)
    off = (ph / (2 * math.pi)) * 6.6 if walking else 0.0
    for j in range(14):
        tx = cx - 44 + ((j * 6.6 + off) % 88)
        P.cap((tx, fy - 17.4), (tx, fy - 15.8), 1.1, (16, 16, 18), ow=0, shade=False)
        P.cap((tx, fy - 0.4), (tx, fy - 2.0), 1.1, (16, 16, 18), ow=0, shade=False)
    for i in range(7):
        wx = cx - 37 + i * 12.3
        P.circ((wx, fy - 9), 5.2, (62, 64, 68), ow=0.6)
        P.circ((wx, fy - 9), 1.8, (30, 30, 34), ow=0)
        a = ph * 1.27 + i
        P.cap((wx, fy - 9), (wx + math.cos(a) * 3.6, fy - 9 + math.sin(a) * 3.6), 0.9, (30, 30, 34), ow=0, shade=False)
    P.circ((cx - 44, fy - 10), 6.4, (58, 60, 64), ow=0.7)
    P.circ((cx + 44, fy - 10), 6.4, (58, 60, 64), ow=0.7)

    # saia lateral + casco
    P.poly([(cx - 41, fy - 15 + yb), (cx + 41, fy - 15 + yb), (cx + 46, fy - 20 + yb), (cx - 44, fy - 21 + yb)], pal["armor_d"])
    for i in range(8):
        P.circ((cx - 36 + i * 10, fy - 17.6 + yb), 0.8, STEEL_L, ow=0)
    P.poly([(cx - 46, fy - 20 + yb), (cx - 48, fy - 27 + yb), (cx - 36, fy - 33 + yb), (cx + 26, fy - 33 + yb),
            (cx + 51, fy - 24 + yb), (cx + 47, fy - 20 + yb)], hull)
    P.poly([(cx + 26, fy - 33 + yb), (cx + 51, fy - 24 + yb), (cx + 49, fy - 22.5 + yb), (cx + 25, fy - 30.5 + yb)],
           lighten(hull, 18), ow=0)
    for i in range(5):
        P.cap((cx - 42 + i * 3.6, fy - 32 + yb), (cx - 42 + i * 3.6, fy - 28 + yb), 1.2, hull_d, ow=0, shade=False)
    P.cap((cx - 48, fy - 30 + yb), (cx - 55, fy - 32 + yb), 3.2, STEEL_D)
    P.poly([(cx - 30, fy - 26 + yb), (cx + 20, fy - 26 + yb), (cx + 22, fy - 24.2 + yb), (cx - 31, fy - 24.2 + yb)],
           pal["accent"], ow=0)
    P.circ((cx + 47, fy - 23.5 + yb), 1.6, (255, 230, 150), ow=0.4)

    # torre
    P.poly([(cx - 26, fy - 34 + yb), (cx - 24, fy - 43 + yb), (cx - 17, fy - 45 + yb), (cx - 20, fy - 34 + yb)], hull_d)
    P.poly([(cx - 22, fy - 33 + yb), (cx - 17, fy - 45 + yb), (cx + 6, fy - 47 + yb), (cx + 20, fy - 41 + yb),
            (cx + 23, fy - 33 + yb)], hull)
    P.poly([(cx + 16, fy - 44 + yb), (cx + 23, fy - 43 + yb), (cx + 24, fy - 35 + yb), (cx + 16, fy - 34 + yb)], pal["armor_d"])
    P.cap((cx + 22 - rec * 0.5, fy - 35 + yb), (cx + 30 - rec * 0.5, fy - 35 + yb), 1.8, GUNBLK, ow=0.4, shade=False)
    P.cap((cx + 22 - rec * 0.5, fy - 39.5 + yb), (cx + 52 - rec, fy - 39.5 + yb), 5.0, STEEL_D)
    P.cap((cx + 34 - rec, fy - 39.5 + yb), (cx + 40 - rec, fy - 39.5 + yb), 6.6, STEEL_D)
    P.poly([(cx + 50 - rec, fy - 43 + yb), (cx + 55 - rec, fy - 43 + yb), (cx + 55 - rec, fy - 36 + yb),
            (cx + 50 - rec, fy - 36 + yb)], GUNBLK, ow=0.6)
    for i in range(3):
        P.cap((cx - 12 + i * 2.8, fy - 46.4 + yb), (cx - 11.2 + i * 2.8, fy - 49.4 + yb), 1.6, GUNBLK, ow=0.3, shade=False)

    # comandante na escotilha
    P.circ((cx - 5, fy - 47.5 + yb), 4.4, pal["armor_d"])
    P.poly([(cx - 9, fy - 47 + yb), (cx - 1, fy - 47 + yb), (cx - 2, fy - 51 + yb), (cx - 8, fy - 51.5 + yb)], pal["cloth"])
    hc = (cx - 4.8, fy - 54.6 + yb)
    P.circ(hc, 3.4, SKIN)
    P.poly([(hc[0] - 4.2, hc[1] + 2.0)] + dome((hc[0] - 0.2, hc[1] - 0.4), 3.9, 7) +
           [(hc[0] + 4.2, hc[1] + 0.0), (hc[0] + 1.5, hc[1] + 0.6)], pal["helmet"], ow=0.6)
    P.cap((hc[0] + 0.8, hc[1] + 0.9), (hc[0] + 3.2, hc[1] + 0.8), 1.2, pal["lens"], ow=0.3, shade=False)

    # antena
    P.cap((cx - 18, fy - 45 + yb), (cx - 21.5, fy - 80 + yb), 0.9, (22, 22, 24), ow=0, shade=False)
    P.poly([(cx - 21.5, fy - 80 + yb), (cx - 14, fy - 78 + yb), (cx - 21.2, fy - 75.5 + yb)], pal["accent"], ow=0.3)

    return P.finish(TANK_SCALE), (55 * TANK_SCALE, 39.5 * TANK_SCALE)


def draw_juggernaut_dead(team):
    """Juggernaut caído de bruços, com a metralhadora largada no chão."""
    pal = PAL[team]
    P = Painter(150, 116)
    o, fy = 66.0, 110.0
    armor, armor_d = pal["armor"], pal["armor_d"]
    hip = (o - 30, fy - 10)
    for knee, foot, shade in (((o - 46, fy - 16), (o - 62, fy - 8), pal["cloth_d"]),
                              ((o - 46, fy - 9), (o - 63, fy - 5), pal["cloth"])):
        P.cap(hip, knee, 10.5, shade)
        P.cap(knee, foot, 8.6, armor_d)
        P.circ(knee, 5.0, armor)
        P.poly([(foot[0] - 5, foot[1] - 6), (foot[0] + 3, foot[1] - 6), (foot[0] + 4, foot[1] + 3),
                (foot[0] - 6, foot[1] + 3)], BOOT)
    P.poly([(o - 34, fy - 24), (o - 14, fy - 32), (o - 8, fy - 18), (o - 32, fy - 14)], armor_d)
    P.circ((o - 22, fy - 26), 6.5, STEEL_D)
    P.circ((o - 22, fy - 26), 3.5, STEEL)
    P.poly([(o - 36, fy - 3), (o + 0, fy - 4), (o + 9, fy - 13), (o + 6, fy - 25), (o - 8, fy - 29), (o - 34, fy - 24)],
           pal["cloth"])
    P.poly([(o - 32, fy - 6), (o - 2, fy - 7), (o + 5, fy - 14), (o + 2.5, fy - 23), (o - 9, fy - 26), (o - 30, fy - 22)],
           armor)
    for xx in (-24, -14):
        P.cap((o + xx, fy - 24), (o + xx, fy - 6), 1.2, armor_d, ow=0, shade=False)
    P.poly([(o - 20, fy - 12), (o - 12, fy - 15), (o - 4, fy - 12), (o - 4, fy - 9.5), (o - 12, fy - 12.5), (o - 20, fy - 9.5)],
           pal["accent"], ow=0)
    P.cap((o - 30, fy - 4), (o - 30.5, fy - 24), 4.4, BOOT)
    hx, hy = o + 15, fy - 15
    P.cap((o + 5, fy - 14), (hx - 3, hy + 3), 5.0, pal["cloth_d"])
    P.poly([(hx - 8.5, hy + 4.5)] + dome((hx - 0.5, hy - 0.5), 8.2) +
           [(hx + 8.6, hy + 0.2), (hx + 8.2, hy + 7.5), (hx + 3, hy + 9), (hx - 4, hy + 6)], armor_d)
    P.cap((hx + 1.5, hy + 1.4), (hx + 7.6, hy + 1.2), 2.2, darken(pal["lens"], 150), ow=0.5, shade=False)
    P.cap((hx - 5.2, hy - 8.0), (hx + 4, hy - 8.8), 1.6, pal["accent"], ow=0, shade=False)
    x0, y0 = o + 30, fy - 6
    P.poly([(x0 - 6, y0 - 5), (x0 + 14, y0 - 5.5), (x0 + 14, y0 + 4.5), (x0 - 6, y0 + 5)], armor_d)
    for off in (-3.0, 0.0, 3.0):
        P.cap((x0 + 14, y0 + off - 0.5), (x0 + 46, y0 + off - 0.5), 2.6, STEEL, ow=0.5)
    P.cap((x0 + 26, y0 - 5), (x0 + 26, y0 + 4), 2.2, STEEL_D, ow=0.5)
    P.cap((o + 3, fy - 20), (o + 20, fy - 9), 8.0, pal["cloth_d"])
    P.cap((o + 20, fy - 9), (x0 + 4, y0 + 2), 7.0, pal["cloth_d"])
    P.circ((x0 + 4, y0 + 2), 3.6, GLOVE, ow=0.5)
    P.cap((o + 2, fy - 14), (o + 14, fy - 4), 8.0, pal["cloth"])
    P.cap((o + 14, fy - 4), (o + 24, fy - 3.5), 7.0, pal["cloth"])
    P.circ((o + 25, fy - 3.5), 3.6, GLOVE, ow=0.5)
    P.circ((o + 3, fy - 22), 8.5, armor)
    return P.finish()


class SpriteSet:
    def __init__(self, walk, poses, anchor, custom=False):
        flip = lambda s: pygame.transform.flip(s, True, False)
        self.anchor = anchor
        self.custom = custom
        self.walk_r, self.walk_l = walk, [flip(f) for f in walk]
        self.poses = {}
        for name, p in poses.items():
            fires = p["fire"] if isinstance(p["fire"], list) else [p["fire"]]
            self.poses[name] = dict(idle=(p["idle"], flip(p["idle"])),
                                    fire=[(f, flip(f)) for f in fires],
                                    tip=p["tip"], top=p["top"])
        self.w = poses["stand"]["idle"].get_width()


def load_custom(key):
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "sprites", key + ".png")
    if os.path.exists(path):
        try:
            return pygame.image.load(path).convert_alpha()
        except pygame.error:
            return None
    return None


def build_sprites():
    sprites = {}
    for idx, spec in enumerate(UNITS):
        for team in (0, 1):
            kind = spec["kind"]
            custom = load_custom(spec["key"])
            if custom is not None:
                w, h = custom.get_size()
                pose = dict(idle=custom, fire=custom, tip=(w * 0.5, h * 0.6), top=h)
                sprites[(idx, team)] = SpriteSet([custom] * N_WALK, {s: dict(pose) for s in STANCES}, (w / 2, h), custom=True)
                continue
            phases = [2 * math.pi * i / N_WALK for i in range(N_WALK)]
            if kind == "tank":
                walk = [draw_tank(team, p, "walk")[0] for p in phases]
                idle, tip = draw_tank(team, 0.0, "idle")
                poses = {"stand": dict(idle=idle, fire=draw_tank(team, 0.0, "fire")[0], tip=tip, top=int(60 * TANK_SCALE))}
                anchor = (70.0 * TANK_SCALE, 98.0 * TANK_SCALE)
            elif kind == "jugg":
                walk = [draw_juggernaut(team, p, "walk")[0] for p in phases]
                idle, tip = draw_juggernaut(team, 0.0, "idle")
                fires = [draw_juggernaut(team, 0.0, "fire")[0], draw_juggernaut(team, 0.0, "fire2")[0]]
                dead = draw_juggernaut_dead(team)
                poses = {"stand": dict(idle=idle, fire=fires, tip=tip, top=88),
                         "dead": dict(idle=dead, fire=dead, tip=(0, 0), top=30)}
                anchor = (50.0, 110.0)
            else:
                walk = [draw_infantry(kind, team, p, "walk", "stand")[0] for p in phases]
                poses = {}
                for st in STANCES:
                    idle, tip = draw_infantry(kind, team, 0.0, "idle", st)
                    poses[st] = dict(idle=idle, fire=draw_infantry(kind, team, 0.0, "fire", st)[0], tip=tip, top=TOPS[st])
                anchor = (36.0, 78.0)
            sprites[(idx, team)] = SpriteSet(walk, poses, anchor)
    return sprites


def build_base(team):
    P = Painter(232, 214)
    pal = PAL[team]
    conc = (104, 104, 100) if team == 0 else (88, 84, 82)
    conc_d, conc_l = darken(conc, 28), lighten(conc, 24)
    # torre traseira
    P.poly([(22, 200), (24, 74), (34, 60), (58, 64), (62, 200)], conc_d)
    P.poly([(18, 74), (30, 54), (62, 58), (68, 74)], darken(conc, 40))
    P.poly([(30, 86), (54, 88), (54, 98), (30, 96)], (18, 18, 22))
    P.circ((60, 92), 2.6, (255, 226, 140) if team == 0 else (255, 90, 70), ow=0.4)
    # bunker principal
    P.poly([(40, 200), (40, 124), (60, 106), (150, 102), (178, 124), (184, 200)], conc)
    P.poly([(36, 124), (60, 104), (150, 100), (181, 122), (186, 132), (36, 134)], conc_l)
    P.poly([(40, 134), (186, 134), (184, 142), (40, 142)], darken(conc, 12), ow=0)
    for i in range(4):
        P.cap((70 + i * 32, 134), (70 + i * 32, 200), 1.0, conc_d, ow=0, shade=False)
    P.poly([(40, 160), (183, 160), (184, 169), (40, 169)], pal["accent"], ow=0.5)
    P.poly([(66, 140 + 0), (100, 138), (100, 148), (66, 150)], (14, 14, 18), ow=0.6)
    P.poly([(70, 143), (96, 142), (96, 146), (70, 147)], (170, 120, 50) if team == 0 else (160, 40, 34), ow=0)
    P.poly([(112, 200), (112, 176), (122, 168), (146, 168), (156, 176), (156, 200)], (52, 54, 58), ow=0.9)
    for i in range(4):
        P.poly([(116 + i * 9, 200), (121 + i * 9, 200), (125 + i * 9, 192), (120 + i * 9, 192)],
               (206, 170, 50), ow=0)
    # torreta com canhão
    P.poly([(86, 104)] + [(100 + math.cos(math.radians(a)) * 15, 104 + math.sin(math.radians(a)) * 13)
                          for a in range(180, 361, 20)] + [(116, 104)], darken(conc, 20))
    P.cap((104, 96), (140, 90), 5.4, STEEL_D)
    P.poly([(138, 87), (144, 87), (144, 93), (138, 93)], GUNBLK, ow=0.6)
    # mastro e bandeira rasgada
    P.cap((50, 62), (50, 14), 1.8, (180, 180, 184), ow=0.4, shade=False)
    P.poly([(50, 16), (86, 20), (79, 26), (90, 34), (80, 40), (50, 38)], pal["accent"], ow=0.6)
    P.circ((64, 28), 4.2, darken(pal["accent"], 50), ow=0)
    # sacos de areia
    for row, (n, y0) in enumerate([(5, 198), (4, 189), (3, 180)]):
        for i in range(n):
            xx = 168 + i * 13 + row * 6
            P.poly([(xx - 7, y0), (xx - 5.5, y0 - 8), (xx + 5.5, y0 - 8), (xx + 7, y0), (xx + 2, y0 + 2), (xx - 2, y0 + 2)],
                   (150, 134, 98) if (i + row) % 2 else (136, 120, 88), ow=0.6)
    # arame farpado
    for i in range(3):
        P.cap((222 + i * 3, 200), (222 + i * 3, 168), 1.2, (50, 48, 46), ow=0, shade=False)
    pts = [(206 + (k % 2) * 22, 172 + k * 4) for k in range(8)]
    for a, b in zip(pts, pts[1:]):
        P.cap(a, b, 0.8, (70, 70, 74), ow=0, shade=False)
    for k in range(6):
        P.circ((208 + k * 4, 196 - (k % 3) * 2), 2.4, (0, 0, 0, 0) if False else (62, 62, 66), ow=0.3)
    img = P.finish(1.2)
    if team == 1:
        img = pygame.transform.flip(img, True, False)
    return img


# ====================================================================== cenário
def _lerp3(a, b, c, t):
    return mix(a, b, t / 0.6) if t < 0.6 else mix(b, c, (t - 0.6) / 0.4)


def _soft_ellipse(bg, cx, cy, rw, rh, col, alpha):
    img = pygame.transform.smoothscale(soft(64, col), (int(rw * 2), int(rh * 2)))
    img.set_alpha(alpha)
    bg.blit(img, (cx - rw, cy - rh))


def _city(bg, rnd, base_y, hmin, hmax, wmin, wmax, col, win_col, windows):
    x = -30
    while x < W + 30:
        w = rnd.randint(wmin, wmax)
        h = rnd.randint(hmin, hmax)
        top = base_y - h
        pts = [(x, base_y + 40), (x, top)]
        for i in range(1, 4):
            pts.append((x + w * i / 3, top + (rnd.randint(-8, 24) if rnd.random() < 0.6 else 0)))
        pts.append((x + w, base_y + 40))
        pygame.draw.polygon(bg, col, pts)
        if windows:
            for wy in range(int(top) + 12, int(base_y) - 6, 15):
                for wx in range(int(x) + 7, int(x + w) - 7, 13):
                    if rnd.random() < 0.3:
                        pygame.draw.ellipse(bg, win_col, (wx, wy, 5, 8))
        x += w + rnd.randint(-8, 8)


def build_background():
    rnd = random.Random(11)
    bg = pygame.Surface((W, H))
    for y in range(HORIZON):
        t = y / HORIZON
        pygame.draw.line(bg, _lerp3((22, 25, 34), (84, 62, 64), (196, 116, 74), t), (0, y), (W, y))
    g = pygame.transform.smoothscale(glow(240, (130, 66, 30), 1.0), (1000, 260))
    bg.blit(g, (W * 0.58 - 500, HORIZON - 170), special_flags=pygame.BLEND_RGB_ADD)
    for _ in range(18):
        _soft_ellipse(bg, rnd.randint(0, W), rnd.randint(20, HORIZON - 80), rnd.randint(120, 260),
                      rnd.randint(18, 44), (36, 32, 38), rnd.randint(40, 90))
    _city(bg, rnd, HORIZON, 40, 120, 36, 80, (86, 66, 66), (60, 48, 50), False)
    for x in (180, 520, 860, 1130):
        for i in range(12):
            _soft_ellipse(bg, x + math.sin(i * 0.7) * 14, HORIZON - 40 - i * 26, 22 + i * 5, 20 + i * 4, (46, 42, 44), 70)
    _city(bg, rnd, HORIZON + 8, 60, 170, 46, 100, (50, 42, 46), (178, 110, 60), True)

    # chão
    gh = H - HORIZON
    for y in range(HORIZON, H):
        t = (y - HORIZON) / gh
        pygame.draw.line(bg, mix((102, 88, 72), (44, 38, 33), t ** 0.8), (0, y), (W, y))
    for y in range(HORIZON, HORIZON + 26):
        t = 1 - (y - HORIZON) / 26
        c = mix(bg.get_at((0, y))[:3], (176, 120, 88), t * 0.55)
        pygame.draw.line(bg, c, (0, y), (W, y))
    for _ in range(11000):
        x, y = rnd.randint(0, W - 1), rnd.randint(HORIZON, H - 1)
        base = bg.get_at((x, y))[:3]
        j = rnd.randint(-16, 14)
        bg.set_at((x, y), (max(0, min(255, base[0] + j)), max(0, min(255, base[1] + j)), max(0, min(255, base[2] + j))))
    for _ in range(20):
        px, py = rnd.randint(0, W), rnd.randint(HORIZON + 20, H - 30)
        pts = [(px, py)]
        for _k in range(rnd.randint(4, 9)):
            px += rnd.randint(-40, 60)
            py += rnd.randint(-5, 8)
            pts.append((px, py))
        pygame.draw.lines(bg, (52, 45, 38), False, pts, rnd.randint(1, 2))
    for _ in range(8):
        x, y = rnd.randint(330, W - 330), rnd.randint(HORIZON + 40, H - 60)
        sc = 0.45 + (y - HORIZON) / gh
        w, h = int(rnd.randint(70, 130) * sc), int(rnd.randint(16, 26) * sc)
        pygame.draw.ellipse(bg, (126, 108, 88), (x - w // 2, y - h // 2 - 2, w, h))
        pygame.draw.ellipse(bg, (34, 29, 26), (x - w // 2 + 3, y - h // 2 + 1, w - 6, h - 3))
        pygame.draw.ellipse(bg, (24, 21, 19), (x - w // 3, y - h // 3 + 2, w * 2 // 3, h // 2))
    for _ in range(110):
        x, y = rnd.randint(0, W), rnd.randint(HORIZON + 6, H - 10)
        r = rnd.uniform(1.5, 5.5) * (0.5 + (y - HORIZON) / gh)
        gr = rnd.randint(60, 108)
        pts = [(x + math.cos(a) * r * rnd.uniform(0.6, 1.2), y + math.sin(a) * r * 0.6 * rnd.uniform(0.6, 1.2))
               for a in (0, 1.3, 2.5, 3.6, 4.9)]
        pygame.draw.polygon(bg, (gr, gr - 4, gr - 8), pts)
    for x in (260, 470, 700, 930, 1040):
        y = HORIZON + rnd.randint(18, 36)
        for ang in (0.5, 1.5, 2.5):
            dx, dy = math.cos(ang) * 16, math.sin(ang) * 16
            pygame.draw.line(bg, (28, 28, 32), (x - dx, y - dy), (x + dx, y + dy), 4)
            pygame.draw.line(bg, (74, 74, 80), (x - dx, y - dy - 1), (x + dx, y + dy - 1), 1)
    for x in (90, 330, 640, 960, 1190):
        y = HORIZON + rnd.randint(2, 10)
        pygame.draw.polygon(bg, (26, 22, 22), [(x - 5, y), (x - 2, y - 70), (x + 2, y - 70), (x + 5, y)])
        for k in range(5):
            bx, by = x + rnd.randint(-2, 2), y - 20 - k * 11
            pygame.draw.line(bg, (26, 22, 22), (bx, by), (bx + rnd.choice((-1, 1)) * rnd.randint(12, 28), by - rnd.randint(8, 18)), 3)
    return bg


def build_vignette():
    sw, sh = 160, 90
    v = pygame.Surface((sw, sh), pygame.SRCALPHA)
    for y in range(sh):
        for x in range(sw):
            nx, ny = (x - sw / 2) / (sw / 2), (y - sh / 2) / (sh / 2)
            d = math.sqrt(nx * nx + ny * ny)
            a = int(210 * max(0.0, (d - 0.55) / 0.65) ** 1.6)
            v.set_at((x, y), (0, 0, 0, min(235, a)))
    return pygame.transform.smoothscale(v, (W, H)).convert_alpha()


def make_shadow(w, h):
    s = pygame.Surface((w, h), pygame.SRCALPHA)
    for i in range(4):
        r = (i * w * 0.07, i * h * 0.12, w - 2 * i * w * 0.07, h - 2 * i * h * 0.12)
        pygame.draw.ellipse(s, (0, 0, 0, 34 + i * 24), r)
    return s


# ====================================================================== partículas
def blit_pivot(dst, img, ax, ay, px, py, ang):
    """Desenha img com o ponto (ax, ay) da imagem em (px, py), girada 'ang' graus (anti-horário)."""
    if abs(ang) < 0.5:
        dst.blit(img, (px - ax, py - ay))
        return
    w, h = img.get_size()
    rot = pygame.transform.rotate(img, ang)
    vx, vy = w / 2 - ax, h / 2 - ay
    th = math.radians(ang)
    nx = vx * math.cos(th) + vy * math.sin(th)
    ny = -vx * math.sin(th) + vy * math.cos(th)
    dst.blit(rot, rot.get_rect(center=(px + nx, py + ny)))


def dying_state(d, t):
    """Quadro, inclinação e posição da animação de morte no instante t."""
    prev, img, ang = 0.0, None, 0.0
    for k, (te, im, a0, a1) in enumerate(d["frames"]):
        if t <= te or k == len(d["frames"]) - 1:
            p = max(0.0, min(1.0, (t - prev) / max(te - prev, 1e-6)))
            img, ang = im, (a0 + (a1 - a0) * p) * d["dir"]
            break
        prev = te
    q = max(0.0, min(1.0, t / d["dur"]))
    e = q * q * (3 - 2 * q)
    return img, ang, d["x"] - d["dir"] * 12 * e, d["y"] - 5 * math.sin(math.pi * q)


class Particles:
    def __init__(self):
        self.items = []

    def add(self, k, x, y, vx=0.0, vy=0.0, life=1.0, s0=4, s1=4, col=(255, 255, 255), g=0.0, gy=None, a=255, drag=0.0):
        if len(self.items) > 750:
            return
        self.items.append(dict(k=k, x=x, y=y, vx=vx, vy=vy, life=life, max=life, s0=s0, s1=s1,
                               col=col, g=g, gy=gy, a=a, drag=drag))

    def update(self, dt, game):
        keep = []
        for p in self.items:
            p["life"] -= dt
            if p["life"] <= 0:
                continue
            p["x"] += p["vx"] * dt
            p["y"] += p["vy"] * dt
            p["vy"] += p["g"] * dt
            if p["drag"]:
                f = max(0.0, 1 - p["drag"] * dt)
                p["vx"] *= f
                p["vy"] *= f
            gy = p["gy"]
            if gy is not None and p["y"] >= gy and p["vy"] > 0:
                if p["k"] == "blood":
                    game.splat(p["x"], gy, 2, 6)
                    continue
                if p["k"] == "casing":
                    if abs(p["vy"]) < 40:
                        p["vy"], p["g"], p["vx"], p["gy"], p["y"] = 0, 0, 0, None, gy
                    else:
                        p["vy"] *= -0.35
                        p["vx"] *= 0.5
                        p["y"] = gy
                else:
                    continue
            keep.append(p)
        self.items = keep

    def draw_smoke(self, surf):
        for p in self.items:
            if p["k"] in ("smoke", "dust"):
                t = 1 - p["life"] / p["max"]
                size = p["s0"] + (p["s1"] - p["s0"]) * t
                img = soft(size, p["col"])
                img.set_alpha(int(p["a"] * min(1.0, t * 8) * (1 - t)))
                surf.blit(img, (p["x"] - img.get_width() / 2, p["y"] - img.get_height() / 2))

    def draw_solid(self, surf):
        for p in self.items:
            k = p["k"]
            if k == "blood":
                pygame.draw.circle(surf, p["col"], (int(p["x"]), int(p["y"])), 2)
            elif k == "debris":
                pygame.draw.circle(surf, p["col"], (int(p["x"]), int(p["y"])), max(1, int(p["s0"])))
            elif k == "casing":
                pygame.draw.rect(surf, p["col"], (int(p["x"]), int(p["y"]), 3, 2))
            elif k == "spark":
                pygame.draw.line(surf, p["col"], (p["x"], p["y"]), (p["x"] - p["vx"] * 0.03, p["y"] - p["vy"] * 0.03), 1)

    def draw_glow(self, surf):
        for p in self.items:
            k = p["k"]
            if k == "fire":
                t = 1 - p["life"] / p["max"]
                img = glow(p["s0"] + (p["s1"] - p["s0"]) * t, p["col"], 1 - t)
            elif k == "flash":
                img = glow(p["s0"], p["col"], 1.0)
            else:
                continue
            surf.blit(img, (p["x"] - img.get_width() / 2, p["y"] - img.get_height() / 2),
                      special_flags=pygame.BLEND_RGB_ADD)


# ====================================================================== entidades
class Base:
    def __init__(self, side):
        self.side = side
        self.x = 150 if side == 0 else W - 150
        self.maxhp = 1000
        self.hp = self.maxhp
        self.hit_y = BASE_GROUND - 12
        self.front = self.x + (140 if side == 0 else -140)   # linha das defesas
        self.fx_t = 0.0
        self.cd = 0.0
        self.cannon_cd = 2.0

    def draw(self, s, img):
        if self.side == 0:
            s.blit(img, (self.x - 133, BASE_GROUND - 240))
        else:
            s.blit(img, (self.x - 145, BASE_GROUND - 240))


def seg_rect_t(x0, y0, dx, dy, rect):
    """Parâmetro t (0..1) em que o segmento entra no retângulo, ou None."""
    tmin, tmax = 0.0, 1.0
    for p, d, lo, hi in ((x0, dx, rect[0], rect[2]), (y0, dy, rect[1], rect[3])):
        if abs(d) < 1e-9:
            if p < lo or p > hi:
                return None
        else:
            t1, t2 = (lo - p) / d, (hi - p) / d
            if t1 > t2:
                t1, t2 = t2, t1
            tmin, tmax = max(tmin, t1), min(tmax, t2)
            if tmin > tmax:
                return None
    return tmin


class Unit:
    def __init__(self, idx, side):
        self.idx = idx
        self.spec = UNITS[idx]
        self.side = side
        self.dir = 1 if side == 0 else -1
        self.x = 205 if side == 0 else W - 205
        self.y = random.uniform(512, BASE_GROUND - 6)      # sai de trás do bunker
        self.lane = random.uniform(GROUND_TOP, GROUND_BOT)
        self.lane_t = random.uniform(2, 5)
        self.hp = self.spec["hp"]
        self.cd = random.uniform(0, 0.5)
        self.anim = random.random() * 6
        self.moving = True
        self.flash = 0.0
        self.dust_t = random.random() * 0.3
        self.stance = "stand"      # postura atual (animação)
        self.want = "stand"        # postura desejada
        self.trans = 0.2
        self.stance_t = random.uniform(0.4, 1.8)

    def hitbox(self):
        k = self.spec["kind"]
        if k == "tank":
            hw, h = int(46 * TANK_SCALE), int(50 * TANK_SCALE)
        elif k == "jugg":
            hw, h = 15, 78
        else:
            hw, h = HIT[self.stance]
        return (self.x - hw, self.y - h, self.x + hw, self.y)

    def update(self, game, dt):
        sp = self.spec
        # troca de postura passo a passo: em pé <-> agachado <-> deitado
        if self.stance != self.want:
            self.trans -= dt
            if self.trans <= 0:
                i, j = STANCES.index(self.stance), STANCES.index(self.want)
                self.stance = STANCES[i + (1 if j > i else -1)]
                self.trans = 0.2

        target, best = None, 1e9
        for f in game.units:
            if f.side == self.side:
                continue
            d = math.hypot(f.x - self.x, (f.y - self.y) * 1.6)
            if d <= sp["range"] and d < best:
                target, best = f, d
        base = game.bases[1 - self.side]
        if target is None and abs(base.front - self.x) <= sp["range"]:
            target = base

        self.cd -= dt
        self.flash = max(0.0, self.flash - dt)
        if target is not None:
            # atirando: fica parado no lugar (sem andar nem derivar para os lados)
            self.moving = False
            self.lane = self.y
            self.lane_t = random.uniform(2, 5)
            if sp["stances"]:
                self.stance_t -= dt
                if self.stance_t <= 0:
                    new = random.choices(STANCES, weights=(0.34, 0.36, 0.30))[0]
                    self.stance_t = random.uniform(1.8, 4.2)
                    if new != self.want:
                        self.want = new
                        self.trans = 0.22
            if self.stance == self.want and self.cd <= 0:
                self.cd = sp["cd"]
                game.attack(self, target)
        else:
            if sp["stances"] and self.want != "stand":
                self.want = "stand"          # levanta antes de andar
                self.trans = 0.2
            if self.stance == "stand":
                self.moving = True
                self.x += self.dir * sp["speed"] * dt
                self.anim += dt * sp["speed"] * sp["anim"]
                self.dust_t -= dt
                if self.dust_t <= 0:
                    self.dust_t = 0.1 if sp["kind"] == "tank" else 0.24
                    game.parts.add("dust", self.x - self.dir * 8, self.y - 2, -self.dir * 12, -10, 0.8,
                                   6, 24 if sp["kind"] == "tank" else 11, (120, 104, 88), a=70, drag=1.0)
                self.lane_t -= dt
                if self.lane_t <= 0:
                    self.lane = random.uniform(GROUND_TOP, GROUND_BOT)
                    self.lane_t = random.uniform(2, 5)
                self.y += max(-25 * dt, min(25 * dt, self.lane - self.y))
                for a in game.units:
                    if a is not self and a.side == self.side and abs(a.x - self.x) < 18 and abs(a.y - self.y) < 9:
                        self.y += (1 if self.y >= a.y else -1) * 25 * dt
            else:
                self.moving = False
        self.y = max(GROUND_TOP, min(GROUND_BOT, self.y))

    def draw(self, s, game):
        ss = game.sprites[(self.idx, self.side)]
        right = self.dir == 1
        pose = ss.poses[self.stance if self.stance in ss.poses else "stand"]
        if self.moving:
            i = int(self.anim / (2 * math.pi) * N_WALK) % N_WALK
            frame = (ss.walk_r if right else ss.walk_l)[i]
        elif self.flash > 0:
            fires = pose["fire"]
            frame = fires[int(game.t_anim * 40) % len(fires)][0 if right else 1]
        else:
            frame = pose["idle"][0 if right else 1]
        ax = ss.anchor[0] if right else ss.w - ss.anchor[0]
        kind = self.spec["kind"]
        if kind == "tank":
            sh = game.shadow_tank
        elif kind == "jugg":
            sh = game.shadow_jugg
        elif self.stance == "prone":
            sh = game.shadow_prone
        else:
            sh = game.shadow_inf
        s.blit(sh, (self.x - sh.get_width() / 2, self.y - sh.get_height() / 2 + 1))
        s.blit(frame, (self.x - ax, self.y - ss.anchor[1]))
        bw = 30
        bx, by = int(self.x - bw / 2), int(self.y - pose["top"] - 8)
        pygame.draw.rect(s, (20, 20, 22), (bx - 1, by - 1, bw + 2, 6), border_radius=3)
        pygame.draw.rect(s, (110, 190, 120) if self.side == 0 else (214, 78, 62),
                         (bx, by, int(bw * max(0, self.hp) / self.spec["hp"]), 4), border_radius=2)


# ====================================================================== jogo
class Game:
    def __init__(self, sprites, base_imgs, bg, vignette):
        self.sprites = sprites
        self.base_imgs = base_imgs
        self.bg = bg
        self.vignette = vignette
        self.shadow_inf = make_shadow(34, 11)
        self.shadow_tank = make_shadow(int(100 * TANK_SCALE), int(17 * TANK_SCALE))
        self.shadow_jugg = make_shadow(52, 15)
        self.shadow_prone = make_shadow(64, 10)
        self.decals = pygame.Surface((W, H), pygame.SRCALPHA)
        self.reset()

    def reset(self):
        self.bases = [Base(0), Base(1)]
        self.units, self.fx, self.corpses, self.dying = [], [], [], []
        self.parts = Particles()
        self.decals.fill((0, 0, 0, 0))
        self.ambient = [[random.uniform(0, W), random.uniform(0, H - HUD_H), random.uniform(-14, -4),
                         random.uniform(8, 24), random.choice((1, 1, 2)), random.random() < 0.25] for _ in range(55)]
        self.money, self.income, self.income_lvl = 60.0, 12.0, 1
        self.elapsed = 0.0
        self.enemy_money, self.enemy_timer = 40.0, 2.0
        self.spawn_cd = 0.0
        self.shake = 0.0
        self.t_anim = 0.0
        self.state = "play"

    # ---- ações do jogador
    def spawn(self, idx, side):
        self.units.append(Unit(idx, side))

    def player_buy(self, idx):
        if self.state != "play" or self.spawn_cd > 0:
            return
        if self.money >= UNITS[idx]["cost"]:
            self.money -= UNITS[idx]["cost"]
            self.spawn(idx, 0)
            self.spawn_cd = 0.25

    def upgrade(self):
        cost = 100 * self.income_lvl
        if self.state == "play" and self.money >= cost:
            self.money -= cost
            self.income_lvl += 1
            self.income += 100

    # ---- efeitos
    def splat(self, x, y, n=7, spread=22):
        for _ in range(n):
            r = random.uniform(1.5, 5.0)
            ox, oy = random.gauss(0, spread * 0.5), random.gauss(0, spread * 0.18)
            pygame.draw.ellipse(self.decals, (84, 10, 10, random.randint(110, 185)),
                                (x + ox - r, y + oy - r * 0.5, r * 2, r))

    def scorch(self, x, y, r):
        for _ in range(5):
            rr = r * random.uniform(0.5, 1.0)
            pygame.draw.ellipse(self.decals, (0, 0, 0, 55),
                                (x + random.uniform(-r, r) * 0.4 - rr, y + random.uniform(-4, 4) - rr * 0.35, rr * 2, rr * 0.7))

    def explode(self, x, y, r, gy):
        P = self.parts
        P.add("flash", x, y, 0, 0, 0.14, r * 2.6, r * 2.6, (255, 190, 100))
        for _ in range(11):
            a = random.uniform(0, math.tau)
            sp = random.uniform(30, 160)
            P.add("fire", x, y, math.cos(a) * sp, math.sin(a) * sp * 0.7 - 30, random.uniform(0.4, 0.8),
                  r * 0.7, r * 0.2, (255, 140, 40), drag=2.0)
        for _ in range(8):
            P.add("smoke", x + random.uniform(-r, r) * 0.4, y, random.uniform(-25, 25), random.uniform(-80, -30),
                  random.uniform(1.2, 2.2), r * 0.5, r * 1.6, (60, 58, 58), a=170, drag=0.8)
        for _ in range(9):
            a = random.uniform(-math.pi, 0)
            sp = random.uniform(120, 300)
            P.add("debris", x, y, math.cos(a) * sp, math.sin(a) * sp, 1.6, random.uniform(1.5, 3), 0,
                  (58, 50, 44), g=620, gy=gy + 3)
        for _ in range(10):
            a = random.uniform(-math.pi, 0)
            sp = random.uniform(150, 360)
            P.add("spark", x, y, math.cos(a) * sp, math.sin(a) * sp, random.uniform(0.2, 0.5), 1, 1, (255, 220, 130), g=500)
        self.shake = max(self.shake, r * 0.14)
        self.scorch(x, gy, r)

    def hit_fx(self, e, px, py, d):
        if isinstance(e, Unit) and e.spec["kind"] not in ("tank", "jugg"):
            for _ in range(4):
                a = random.uniform(-math.pi * 0.9, -math.pi * 0.1)
                spd = random.uniform(40, 130)
                self.parts.add("blood", px, py, math.cos(a) * spd - d * 30, math.sin(a) * spd, 0.7, 2, 2,
                               (110, 12, 12), g=520, gy=e.y)
        else:
            for _ in range(4):
                a = random.uniform(-math.pi, 0)
                spd = random.uniform(80, 220)
                self.parts.add("spark", px, py, math.cos(a) * spd, math.sin(a) * spd, random.uniform(0.15, 0.35),
                               1, 1, (255, 220, 130), g=450)

    def attack(self, atk, tgt):
        sp = atk.spec
        ss = self.sprites[(atk.idx, atk.side)]
        pose = ss.poses[atk.stance if atk.stance in ss.poses else "stand"]
        d = atk.dir
        kind = sp["kind"]
        sx, sy = atk.x + d * pose["tip"][0], atk.y - pose["tip"][1]
        if isinstance(tgt, Base):
            tx, ty, gy = tgt.x, BASE_GROUND - 60, tgt.hit_y
        else:
            hb = tgt.hitbox()
            tx, ty, gy = tgt.x, (hb[1] + hb[3]) / 2, tgt.y
        mult = STANCE_SPREAD[atk.stance]
        atk.flash = 0.2 if kind == "flame" else 0.12
        P = self.parts
        if kind != "flame":
            P.add("flash", sx, sy, 0, 0, 0.06, 30 if kind in ("sniper", "heavy", "tank") else 22, 0, (255, 200, 110))

        if sp["aoe"]:
            # foguete / obus: cai perto do alvo, mas raramente exatamente nele
            sc = sp.get("scatter", 10) * mult
            ix = tx + random.gauss(0, sc)
            igy = gy + random.gauss(0, sc * 0.35)
            iy = ty + (igy - gy) + random.gauss(0, sc * 0.3)
            dist = math.hypot(ix - sx, iy - sy)
            t = max(0.1, min(0.45, dist / (900 if kind == "heavy" else 1500)))
            self.fx.append(dict(k="proj", x1=sx, y1=sy, x2=ix, y2=iy, t=t, m=t, trail=(kind == "heavy"),
                                bx=ix, by=iy, gy=igy, r=sp["aoe"], dmg=sp["dmg"], side=atk.side))
            if kind == "heavy":
                for _ in range(5):
                    P.add("smoke", sx, sy, -d * random.uniform(20, 80), random.uniform(-20, 20), 0.8, 5, 16,
                          (160, 160, 160), a=140)
            return

        if kind == "flame":
            tgt.hp -= sp["dmg"]
            ang0 = math.atan2(ty - sy, tx - sx)
            dist = math.hypot(tx - sx, ty - sy)
            for _ in range(4):
                ang = ang0 + random.uniform(-0.14, 0.14)
                spd = random.uniform(260, 360)
                P.add("fire", sx, sy, math.cos(ang) * spd, math.sin(ang) * spd, min(0.5, dist / spd + 0.12),
                      6, 20, (255, 150, 50), drag=0.6)
            if random.random() < 0.4:
                P.add("smoke", tx, ty, random.uniform(-15, 15), -40, 1.0, 6, 18, (50, 48, 48), a=130)
            return

        # armas de fogo: o tiro tem erro de mira e segue em linha reta,
        # então pode errar o primeiro inimigo e acertar quem está atrás
        sigma = sp.get("spread", 0.12) * mult
        ang = math.atan2(ty - sy, tx - sx) + random.gauss(0, sigma)
        length = sp["range"] + 140
        dx, dy = math.cos(ang) * length, math.sin(ang) * length
        hits = []
        for u in self.units:
            if u.side != atk.side:
                t = seg_rect_t(sx, sy, dx, dy, u.hitbox())
                if t is not None:
                    hits.append((t, u))
        eb = self.bases[1 - atk.side]
        t = seg_rect_t(sx, sy, dx, dy, (eb.x - 88, BASE_GROUND - 170, eb.x + 88, BASE_GROUND))
        if t is not None:
            hits.append((t, eb))
        hits.sort(key=lambda h: h[0])
        dmg, end_t, pierce = sp["dmg"], 1.0, sp.get("pierce", 0.0)
        for n, (t, e) in enumerate(hits):
            px, py = sx + dx * t, sy + dy * t
            e.hp -= dmg
            self.hit_fx(e, px, py, d)
            end_t = t
            if n >= 2 or random.random() >= pierce:
                break
            dmg *= 0.6                      # atravessou: perde força
        ex, ey = sx + dx * end_t, sy + dy * end_t
        if kind == "sniper":
            self.fx.append(dict(k="tracer", x1=sx, y1=sy, x2=ex, y2=ey, t=0.14, m=0.14, tail=0.5, col=(210, 235, 255)))
        else:
            self.fx.append(dict(k="tracer", x1=sx, y1=sy, x2=ex, y2=ey, t=0.08, m=0.08, tail=0.25, col=(255, 214, 120)))
        if not hits and GROUND_TOP - 40 <= ey <= H - HUD_H:
            P.add("dust", ex, ey, random.uniform(-10, 10), -15, 0.5, 4, 12, (130, 112, 94), a=90)
            P.add("spark", ex, ey, random.uniform(-80, 80), -random.uniform(40, 120), 0.25, 1, 1, (255, 220, 130), g=400)
        if kind != "jugg" or random.random() < 0.5:
            P.add("casing", sx - d * 8, sy + 3, -d * random.uniform(30, 70), -random.uniform(60, 120), 1.4, 2, 2,
                  (212, 172, 72), g=520, gy=atk.y)

    def detonate(self, f):
        for u in self.units:
            if u.side != f["side"] and math.hypot(u.x - f["bx"], (u.y - f["gy"]) * 1.6) <= f["r"]:
                u.hp -= f["dmg"] * STANCE_DMG.get(u.stance, 1.0)
        b = self.bases[1 - f["side"]]
        if abs(b.x - f["bx"]) <= f["r"] + 20:
            b.hp -= f["dmg"]
        self.explode(f["bx"], f["by"], f["r"], f["gy"])

    def on_death(self, u):
        ss = self.sprites[(u.idx, u.side)]
        right = u.dir == 1
        side = 0 if right else 1
        kind = u.spec["kind"]
        ax = ss.anchor[0] if right else ss.w - ss.anchor[0]
        ay = ss.anchor[1]

        def im(name):
            return ss.poses[name]["idle"][side]

        if kind == "tank":
            self.explode(u.x, u.y - 34, 60, u.y)
            img = im("stand").copy()
            img.fill((70, 66, 64), special_flags=pygame.BLEND_RGB_MULT)
            self.corpses.append(dict(img=img, pos=(u.x - ax, u.y - ay), x=u.x, y=u.y, t=0.0, life=12.0,
                                     tank=True, emit=0.0))
            return

        big = kind == "jugg"
        for _ in range(26 if big else 16):
            a = random.uniform(-math.pi, 0)
            spd = random.uniform(40, 190)
            self.parts.add("blood", u.x, u.y - (40 if big else 24), math.cos(a) * spd, math.sin(a) * spd, 1.0, 2, 2,
                           (104, 12, 12), g=560, gy=u.y)
        self.splat(u.x, u.y, 6, 20)
        # sequência da queda: cada quadro usa as poses já desenhadas (em pé -> agachado -> deitado)
        if ss.custom:
            frames = [(0.55, im("stand"), 0, 88)]
        elif big:
            frames = [(0.2, im("stand"), 0, 6), (0.42, im("stand"), 6, 14), (0.7, im("dead"), 4, 0)]
        elif u.stance == "stand":
            frames = [(0.14, im("stand"), 0, 8), (0.3, im("crouch"), 8, 14), (0.55, im("prone"), 10, 0)]
        elif u.stance == "crouch":
            frames = [(0.16, im("crouch"), 0, 10), (0.42, im("prone"), 10, 0)]
        else:
            frames = [(0.3, im("prone"), 0, 0)]
        dark = []
        for te, img, a0, a1 in frames:
            c = img.copy()
            c.fill((150, 142, 142), special_flags=pygame.BLEND_RGB_MULT)
            dark.append((te, c, a0, a1))
        self.dying.append(dict(frames=dark, ax=ax, ay=ay, x=u.x, y=u.y, dir=u.dir, t=0.0, dur=dark[-1][0]))

    def bake_corpse(self, d):
        """O corpo vira parte do chão: fica no cenário para sempre, sempre por baixo de tudo."""
        img, ang, px, py = dying_state(d, d["dur"])
        self.splat(px - d["dir"] * 16, d["y"], 9, 30)
        blit_pivot(self.decals, img, d["ax"], d["ay"], px, py, ang)
        self.parts.add("dust", px, d["y"] - 4, 0, -8, 0.6, 6, 16, (120, 104, 88), a=80, drag=1.0)

    def base_defend(self, b, dt):
        """A torreta do QG metralha inimigos próximos e dispara um canhão pesado de tempos em tempos."""
        d = 1 if b.side == 0 else -1
        sx, sy = b.x + d * 35, 466                       # boca do cano da torreta
        b.cd -= dt
        b.cannon_cd -= dt
        near, far = None, None
        for u in self.units:
            if u.side == b.side:
                continue
            dx = (u.x - sx) * d
            if dx < 0:
                continue
            if dx <= BASE_MG["range"] and (near is None or dx < (near.x - sx) * d):
                near = u
            if BASE_CANNON["min_range"] <= dx <= BASE_CANNON["range"] and (far is None or dx < (far.x - sx) * d):
                far = u
        P = self.parts
        if near is not None and b.cd <= 0:
            b.cd = BASE_MG["cd"]
            hb = near.hitbox()
            ty = (hb[1] + hb[3]) / 2
            ang = math.atan2(ty - sy, near.x - sx) + random.gauss(0, BASE_MG["spread"])
            length = BASE_MG["range"] + 120
            ddx, ddy = math.cos(ang) * length, math.sin(ang) * length
            hits = []
            for u in self.units:
                if u.side != b.side:
                    t = seg_rect_t(sx, sy, ddx, ddy, u.hitbox())
                    if t is not None:
                        hits.append((t, u))
            hits.sort(key=lambda h: h[0])
            end_t = 1.0
            if hits:
                end_t, e = hits[0]
                e.hp -= BASE_MG["dmg"]
                self.hit_fx(e, sx + ddx * end_t, sy + ddy * end_t, d)
            ex, ey = sx + ddx * end_t, sy + ddy * end_t
            self.fx.append(dict(k="tracer", x1=sx, y1=sy, x2=ex, y2=ey, t=0.08, m=0.08, tail=0.25, col=(255, 214, 120)))
            P.add("flash", sx, sy, 0, 0, 0.06, 24, 0, (255, 200, 110))
            if not hits and GROUND_TOP - 40 <= ey <= H - HUD_H:
                P.add("dust", ex, ey, random.uniform(-10, 10), -15, 0.5, 4, 12, (130, 112, 94), a=90)
                P.add("spark", ex, ey, random.uniform(-80, 80), -random.uniform(40, 120), 0.25, 1, 1, (255, 220, 130), g=400)
            if random.random() < 0.5:
                P.add("casing", sx - d * 6, sy + 3, -d * random.uniform(30, 70), -random.uniform(60, 120), 1.4, 2, 2,
                      (212, 172, 72), g=520, gy=BASE_GROUND - 10)
        if far is not None and b.cannon_cd <= 0:
            b.cannon_cd = BASE_CANNON["cd"]
            hb = far.hitbox()
            tx, gy = far.x, far.y
            ty = (hb[1] + hb[3]) / 2
            sc = BASE_CANNON["scatter"]
            ix, igy = tx + random.gauss(0, sc), gy + random.gauss(0, sc * 0.35)
            iy = ty + (igy - gy) + random.gauss(0, sc * 0.3)
            t = max(0.15, min(0.5, math.hypot(ix - sx, iy - sy) / 1000))
            self.fx.append(dict(k="proj", x1=sx, y1=sy - 6, x2=ix, y2=iy, t=t, m=t, trail=True,
                                bx=ix, by=iy, gy=igy, r=BASE_CANNON["aoe"], dmg=BASE_CANNON["dmg"], side=b.side))
            P.add("flash", sx, sy - 6, 0, 0, 0.1, 40, 0, (255, 190, 100))
            for _ in range(6):
                P.add("smoke", sx, sy - 6, d * random.uniform(10, 70), random.uniform(-30, 10), 1.0, 6, 22,
                      (150, 150, 150), a=150, drag=1.0)
            self.shake = max(self.shake, 2.0)

    # ---- IA inimiga
    def enemy_ai(self, dt):
        diff = 1 + self.elapsed / 90.0
        self.enemy_money += (10 + 3 * diff) * dt
        self.enemy_timer -= dt
        if self.enemy_timer <= 0:
            self.enemy_timer = random.uniform(1.2, 3.0) / min(diff, 2.5)
            options = [i for i, u in enumerate(UNITS) if u["cost"] <= self.enemy_money]
            if options:
                weights = [1 / (1 + UNITS[i]["cost"] / 40) for i in options]
                idx = random.choices(options, weights)[0]
                self.enemy_money -= UNITS[idx]["cost"]
                self.spawn(idx, 1)

    # ---- atualização
    def update(self, dt):
        self.t_anim += dt
        self.shake = max(0.0, self.shake - 60 * dt)
        if self.state == "play":
            self.elapsed += dt
            self.money += self.income * dt
            self.spawn_cd = max(0.0, self.spawn_cd - dt)
            self.enemy_ai(dt)
            for u in self.units:
                u.update(self, dt)
            for b in self.bases:
                self.base_defend(b, dt)
            dead = [u for u in self.units if u.hp <= 0]
            if dead:
                self.units = [u for u in self.units if u.hp > 0]
                for u in dead:
                    self.on_death(u)
            for b in self.bases:
                if b.hp <= 0 and self.state == "play":
                    self.state = "lose" if b.side == 0 else "win"
                    for _ in range(7):
                        self.explode(b.x + random.uniform(-70, 70), BASE_GROUND - random.uniform(30, 150),
                                     random.uniform(30, 55), BASE_GROUND)
                    self.shake = 14

        live = []
        for f in self.fx:
            f["t"] -= dt
            if f["k"] == "proj":
                prog = 1 - max(0.0, f["t"]) / f["m"]
                f["hx"] = f["x1"] + (f["x2"] - f["x1"]) * prog
                f["hy"] = f["y1"] + (f["y2"] - f["y1"]) * prog
                if f["trail"]:
                    self.parts.add("smoke", f["hx"], f["hy"], random.uniform(-8, 8), random.uniform(-8, 8), 0.7, 3, 11,
                                   (190, 190, 190), a=110)
                if f["t"] <= 0:
                    self.detonate(f)
                    continue
            elif f["t"] <= 0:
                continue
            live.append(f)
        self.fx = live

        # bases danificadas soltam fumaça e fogo
        for b in self.bases:
            ratio = b.hp / b.maxhp
            if ratio < 0.7:
                b.fx_t -= dt
                if b.fx_t <= 0:
                    b.fx_t = 0.12 if ratio < 0.35 else 0.25
                    px, py = b.x + random.uniform(-45, 45), BASE_GROUND - random.uniform(110, 150)
                    self.parts.add("smoke", px, py, random.uniform(-10, 10), -random.uniform(35, 70),
                                   random.uniform(1.5, 2.6), 12, 34, (46, 44, 44), a=170, drag=0.3)
                    if ratio < 0.35:
                        self.parts.add("fire", px, py + 6, random.uniform(-8, 8), -random.uniform(20, 50), 0.6, 18, 6,
                                       (255, 130, 40))

        for c in self.corpses:
            c["t"] += dt
            if c["tank"] and c["t"] < 12:
                c["emit"] -= dt
                if c["emit"] <= 0:
                    c["emit"] = 0.14
                    self.parts.add("smoke", c["x"] + random.uniform(-14, 14), c["y"] - 34, random.uniform(-8, 8),
                                   -random.uniform(30, 60), 1.8, 8, 26, (36, 36, 36), a=170, drag=0.3)
                    if random.random() < 0.6:
                        self.parts.add("fire", c["x"] + random.uniform(-16, 16), c["y"] - 30, 0, -25, 0.5, 14, 4,
                                       (255, 120, 40))
        keep = []
        for c in self.corpses:
            if c["t"] >= c["life"]:
                self.decals.blit(c["img"], c["pos"])     # destroço vira parte do chão
            else:
                keep.append(c)
        self.corpses = keep
        alive = []
        for dd in self.dying:
            dd["t"] += dt
            if dd["t"] >= dd["dur"]:
                self.bake_corpse(dd)
            else:
                alive.append(dd)
        self.dying = alive

        self.parts.update(dt, self)
        for a in self.ambient:
            a[0] += a[2] * dt
            a[1] += a[3] * dt if not a[5] else -a[3] * 0.5 * dt
            if a[0] < -5 or a[1] > H - HUD_H or a[1] < -5:
                a[0], a[1] = random.uniform(0, W + 80), (random.uniform(0, 30) if not a[5] else H - HUD_H - 5)

    # ---- desenho do mundo
    def draw_world(self, s):
        s.blit(self.bg, (0, 0))
        s.blit(self.decals, (0, 0))
        for c in self.corpses:
            s.blit(c["img"], c["pos"])
        for d in self.dying:
            img, ang, px, py = dying_state(d, d["t"])
            blit_pivot(s, img, d["ax"], d["ay"], px, py, ang)
        for u in sorted(self.units, key=lambda u: u.y):
            u.draw(s, self)
        for b in self.bases:                      # o QG fica por cima de todas as unidades
            b.draw(s, self.base_imgs[b.side])
        self.parts.draw_smoke(s)
        self.parts.draw_solid(s)
        for f in self.fx:
            if f["k"] == "tracer":
                p = 1 - f["t"] / f["m"]
                hx = f["x1"] + (f["x2"] - f["x1"]) * p
                hy = f["y1"] + (f["y2"] - f["y1"]) * p
                q = max(0.0, p - f["tail"])
                tx = f["x1"] + (f["x2"] - f["x1"]) * q
                ty = f["y1"] + (f["y2"] - f["y1"]) * q
                pygame.draw.line(s, f["col"], (tx, ty), (hx, hy), 2)
                pygame.draw.line(s, (255, 255, 255), (tx, ty), (hx, hy), 1)
            elif f["k"] == "proj":
                hx, hy = f.get("hx", f["x1"]), f.get("hy", f["y1"])
                pygame.draw.circle(s, (255, 220, 140), (int(hx), int(hy)), 3)
        self.parts.draw_glow(s)
        for a in self.ambient:
            if a[5]:
                pygame.draw.circle(s, (255, 150, 70), (int(a[0]), int(a[1])), 1)
            else:
                pygame.draw.circle(s, (170, 164, 156), (int(a[0]), int(a[1])), a[4] - 1 if a[4] > 1 else 1)
        s.blit(self.vignette, (0, 0))


# ====================================================================== HUD
def panel(s, rect, fill, border, cut=12, bw=2):
    x, y, w, h = rect
    pts = [(x, y), (x + w - cut, y), (x + w, y + cut), (x + w, y + h), (x + cut, y + h), (x, y + h - cut)]
    pygame.draw.polygon(s, fill, pts)
    pygame.draw.polygon(s, border, pts, bw)


def slant_bar(s, x, y, w, h, frac, col, mirror=False):
    k = 9
    pts = [(x + k, y), (x + w, y), (x + w - k, y + h), (x, y + h)]
    pygame.draw.polygon(s, (16, 17, 20), pts)
    fw = max(0, int(w * max(0.0, min(1.0, frac))))
    if fw > k + 1:
        if mirror:
            fp = [(x + w - fw + k, y), (x + w, y), (x + w - k, y + h), (x + w - fw, y + h)]
        else:
            fp = [(x + k, y), (x + fw, y), (x + fw - k, y + h), (x, y + h)]
        pygame.draw.polygon(s, col, fp)
        pygame.draw.polygon(s, lighten(col, 40), [fp[0], fp[1], (fp[1][0] - 2, y + h // 2), (fp[0][0] - 2, y + h // 2)])
    pygame.draw.polygon(s, (130, 134, 140), pts, 2)


def button_rects():
    n = len(UNITS)
    rects = [pygame.Rect(14 + i * 164, H - HUD_H + 11, 158, 68) for i in range(n)]
    rects.append(pygame.Rect(14 + n * 164 + 10, H - HUD_H + 11, 180, 68))
    return rects


def make_portrait(ss):
    img = ss.poses["stand"]["idle"][0]
    r = img.get_bounding_rect()
    crop = img.subsurface(r).copy()
    sc = min(56 / r.w, 54 / r.h)
    return pygame.transform.smoothscale(crop, (max(1, int(r.w * sc)), max(1, int(r.h * sc)))).convert_alpha()


def make_hud_panel():
    s = pygame.Surface((W, HUD_H))
    for y in range(HUD_H):
        pygame.draw.line(s, mix((30, 32, 36), (12, 13, 15), y / HUD_H), (0, y), (W, y))
    for y in range(0, HUD_H, 3):
        pygame.draw.line(s, (8, 9, 10), (0, y), (W, y))
    pygame.draw.line(s, (110, 114, 120), (0, 0), (W, 0), 2)
    pygame.draw.line(s, GOLD, (0, 3), (W, 3), 1)
    return s


def draw_hud(s, g, fonts, portraits, hud_panel):
    font, small, big, tiny = fonts
    mouse = pygame.mouse.get_pos()
    panel(s, (14, 10, 250, 60), (22, 24, 28), (120, 124, 130))
    pygame.draw.circle(s, (120, 90, 24), (46, 40), 17)
    pygame.draw.circle(s, GOLD, (46, 40), 15)
    pygame.draw.circle(s, (250, 226, 130), (46, 40), 9, 2)
    s.blit(big.render(f"{int(g.money)}", True, (244, 230, 170)), (74, 16))
    s.blit(small.render(f"renda +{g.income:.0f}/s  ·  nível {g.income_lvl}", True, (176, 180, 186)), (74, 46))
    slant_bar(s, 290, 30, 320, 18, g.bases[0].hp / g.bases[0].maxhp, (84, 150, 190))
    slant_bar(s, W - 290 - 320, 30, 320, 18, g.bases[1].hp / g.bases[1].maxhp, (200, 68, 56), mirror=True)
    s.blit(small.render("GUARNIÇÃO", True, (170, 200, 220)), (296, 10))
    t = small.render("INSURGENTES", True, (230, 150, 140))
    s.blit(t, (W - 296 - t.get_width(), 10))
    mm, ss_ = divmod(int(g.elapsed), 60)
    t = font.render(f"{mm:02d}:{ss_:02d}", True, (230, 230, 232))
    s.blit(t, (W // 2 - t.get_width() // 2, 26))
    hint = small.render("R reiniciar  ·  ESC sair", True, (150, 154, 160))
    s.blit(hint, (W - hint.get_width() - 14, H - HUD_H - 24))

    s.blit(hud_panel, (0, H - HUD_H))
    rects = button_rects()
    for i, spec in enumerate(UNITS):
        r = rects[i]
        ok = g.money >= spec["cost"]
        hover = r.collidepoint(mouse)
        panel(s, r, (44, 48, 54) if ok else (22, 24, 27),
              (210, 214, 220) if (ok and hover) else ((130, 134, 140) if ok else (58, 60, 64)), 14)
        if ok:
            pygame.draw.line(s, GOLD, (r.x + 16, r.y + 3), (r.right - 16, r.y + 3), 2)
        p = portraits[i]
        if not ok:
            p = p.copy()
            p.fill((110, 110, 110), special_flags=pygame.BLEND_RGB_MULT)
        s.blit(p, (r.x + 6 + (56 - p.get_width()) // 2, r.bottom - 6 - p.get_height()))
        s.blit(tiny.render(spec["name"], True, (232, 232, 234) if ok else (120, 122, 126)), (r.x + 66, r.y + 12))
        s.blit(font.render(f"{spec['cost']}", True, GOLD if ok else (120, 112, 80)), (r.x + 66, r.y + 34))
        pygame.draw.circle(s, (20, 22, 24), (r.x + 16, r.y + 16), 10)
        pygame.draw.circle(s, (150, 154, 160), (r.x + 16, r.y + 16), 10, 1)
        s.blit(small.render(str(i + 1), True, (230, 230, 232)), (r.x + 12, r.y + 7))
    r = rects[-1]
    cost = 100 * g.income_lvl
    ok = g.money >= cost
    hover = r.collidepoint(mouse)
    panel(s, r, (40, 52, 40) if ok else (22, 24, 27),
          (210, 214, 220) if (ok and hover) else ((130, 150, 130) if ok else (58, 60, 64)), 14)
    s.blit(small.render("[U] Reforçar renda", True, (232, 232, 234) if ok else (120, 122, 126)), (r.x + 14, r.y + 12))
    s.blit(font.render(f"{cost}", True, GOLD if ok else (120, 112, 80)), (r.x + 14, r.y + 36))
    s.blit(small.render("+6/s", True, (150, 190, 150) if ok else (90, 100, 90)), (r.x + 110, r.y + 40))


# ====================================================================== principal
def main():
    pygame.init()
    screen = pygame.display.set_mode((W, H))
    pygame.display.set_caption("Guerra de Bases")
    clock = pygame.time.Clock()
    names = "bahnschrift,segoeui,arial"
    font = pygame.font.SysFont(names, 22, bold=True)
    small = pygame.font.SysFont(names, 16, bold=True)
    tiny = pygame.font.SysFont(names, 14, bold=True)
    big = pygame.font.SysFont(names, 38, bold=True)
    huge = pygame.font.SysFont(names, 92, bold=True)

    screen.fill((14, 14, 17))
    t = big.render("Carregando campo de batalha...", True, (200, 200, 205))
    screen.blit(t, t.get_rect(center=(W // 2, H // 2)))
    pygame.display.flip()

    sprites = build_sprites()
    base_imgs = [build_base(0), build_base(1)]
    game = Game(sprites, base_imgs, build_background(), build_vignette())
    portraits = [make_portrait(sprites[(i, 0)]) for i in range(len(UNITS))]
    hud_panel = make_hud_panel()
    world = pygame.Surface((W, H))
    keys = [pygame.K_1, pygame.K_2, pygame.K_3, pygame.K_4, pygame.K_5, pygame.K_6]

    while True:
        dt = min(clock.tick(FPS) / 1000.0, 0.05)
        for e in pygame.event.get():
            if e.type == pygame.QUIT:
                pygame.quit()
                sys.exit()
            if e.type == pygame.KEYDOWN:
                if e.key == pygame.K_ESCAPE:
                    pygame.quit()
                    sys.exit()
                if e.key == pygame.K_r:
                    game.reset()
                if e.key in keys:
                    game.player_buy(keys.index(e.key))
                if e.key == pygame.K_u:
                    game.upgrade()
            if e.type == pygame.MOUSEBUTTONDOWN and e.button == 1:
                for i, r in enumerate(button_rects()):
                    if r.collidepoint(e.pos):
                        game.upgrade() if i == len(UNITS) else game.player_buy(i)

        game.update(dt)
        game.draw_world(world)
        screen.fill((0, 0, 0))
        sh = game.shake
        screen.blit(world, (random.uniform(-sh, sh) if sh else 0, random.uniform(-sh, sh) if sh else 0))
        draw_hud(screen, game, (font, small, big, tiny), portraits, hud_panel)

        if game.state != "play":
            veil = pygame.Surface((W, H), pygame.SRCALPHA)
            veil.fill((0, 0, 0, 140))
            screen.blit(veil, (0, 0))
            win = game.state == "win"
            col = (150, 230, 150) if win else (230, 110, 100)
            msg = "VITÓRIA" if win else "DERROTA"
            shadow = huge.render(msg, True, (0, 0, 0))
            txt = huge.render(msg, True, col)
            c = (W // 2, H // 2 - 50)
            screen.blit(shadow, shadow.get_rect(center=(c[0] + 3, c[1] + 4)))
            screen.blit(txt, txt.get_rect(center=c))
            t2 = font.render("Pressione R para jogar de novo", True, (230, 230, 232))
            screen.blit(t2, t2.get_rect(center=(W // 2, H // 2 + 20)))

        pygame.display.flip()


if __name__ == "__main__":
    main()
