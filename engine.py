import json, os, random, sys, urllib.error, urllib.request

# Tiny chess engine: 0x88 board, alpha-beta + quiescence, transposition
# table, killers + history ordering, null-move pruning, LMR, tapered
# piece-square evaluation. Searches to a FIXED node budget, never a
# clock, so a replay plays the same moves. No randomness at all.
VAL = [0, 100, 320, 330, 500, 900, 0]
MATE = 100000
INF = 1000000
NODES = 60000
START = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"
KN = [-33, -31, -18, -14, 14, 18, 31, 33]
KI = [-17, -16, -15, -1, 1, 15, 16, 17]
BD = [-17, -15, 15, 17]
RD = [-16, -1, 1, 16]
# Piece-square tables, a8 first, white's view. King has mg and eg tables.
PAWN = [0, 0, 0, 0, 0, 0, 0, 0, 50, 50, 50, 50, 50, 50, 50, 50,
 10, 10, 20, 30, 30, 20, 10, 10, 5, 5, 10, 25, 25, 10, 5, 5,
 0, 0, 0, 20, 20, 0, 0, 0, 5, -5, -10, 0, 0, -10, -5, 5,
 5, 10, 10, -20, -20, 10, 10, 5, 0, 0, 0, 0, 0, 0, 0, 0]
KNIGHT = [-50, -40, -30, -30, -30, -30, -40, -50, -40, -20, 0, 0, 0, 0, -20, -40,
 -30, 0, 10, 15, 15, 10, 0, -30, -30, 5, 15, 20, 20, 15, 5, -30,
 -30, 0, 15, 20, 20, 15, 0, -30, -30, 5, 10, 15, 15, 10, 5, -30,
 -40, -20, 0, 5, 5, 0, -20, -40, -50, -40, -30, -30, -30, -30, -40, -50]
BISHOP = [-20, -10, -10, -10, -10, -10, -10, -20, -10, 0, 0, 0, 0, 0, 0, -10,
 -10, 0, 5, 10, 10, 5, 0, -10, -10, 5, 5, 10, 10, 5, 5, -10,
 -10, 0, 10, 10, 10, 10, 0, -10, -10, 10, 10, 10, 10, 10, 10, -10,
 -10, 5, 0, 0, 0, 0, 5, -10, -20, -10, -10, -10, -10, -10, -10, -20]
ROOK = [0, 0, 0, 0, 0, 0, 0, 0, 5, 10, 10, 10, 10, 10, 10, 5,
 -5, 0, 0, 0, 0, 0, 0, -5, -5, 0, 0, 0, 0, 0, 0, -5,
 -5, 0, 0, 0, 0, 0, 0, -5, -5, 0, 0, 0, 0, 0, 0, -5,
 -5, 0, 0, 0, 0, 0, 0, -5, 0, 0, 0, 5, 5, 0, 0, 0]
QUEEN = [-20, -10, -10, -5, -5, -10, -10, -20, -10, 0, 0, 0, 0, 0, 0, -10,
 -10, 0, 5, 5, 5, 5, 0, -10, -5, 0, 5, 5, 5, 5, 0, -5,
 0, 0, 5, 5, 5, 5, 0, -5, -10, 5, 5, 5, 5, 5, 0, -10,
 -10, 0, 5, 0, 0, 0, 0, -10, -20, -10, -10, -5, -5, -10, -10, -20]
KMG = [-30, -40, -40, -50, -50, -40, -40, -30, -30, -40, -40, -50, -50, -40, -40, -30,
 -30, -40, -40, -50, -50, -40, -40, -30, -30, -40, -40, -50, -50, -40, -40, -30,
 -20, -30, -30, -40, -40, -30, -30, -20, -10, -20, -20, -20, -20, -20, -20, -10,
 20, 20, 0, 0, 0, 0, 20, 20, 20, 30, 10, 0, 0, 10, 30, 20]
KEG = [-50, -40, -30, -20, -20, -30, -40, -50, -30, -20, -10, 0, 0, -10, -20, -30,
 -30, -10, 20, 30, 30, 20, -10, -30, -30, -10, 30, 40, 40, 30, -10, -30,
 -30, -10, 30, 40, 40, 30, -10, -30, -30, -10, 20, 30, 30, 20, -10, -30,
 -30, -30, 0, 0, 0, 0, -30, -30, -50, -30, -30, -30, -30, -30, -30, -50]
PST = [None, PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KMG]
PSV = [[0] * 128 for _ in range(13)]
for _pc in range(1, 7):
    for _sq in range(128):
        if _sq & 0x88:
            continue
        _r, _f = _sq >> 4, _sq & 7
        _v = VAL[_pc] + PST[_pc][(7 - _r) * 8 + _f]
        PSV[_pc + 6][_sq] = _v
        PSV[-_pc + 6][_sq] = -(VAL[_pc] + PST[_pc][_r * 8 + _f])
PSV[12] = [0] * 128
PSV[0] = [0] * 128
CK = [15] * 128
CK[0] = 13
CK[7] = 14
CK[4] = 12
CK[112] = 7
CK[119] = 11
CK[116] = 3
_rnd = random.Random(20261117)
ZP = [[_rnd.getrandbits(64) for _ in range(128)] for _ in range(13)]
ZC = [_rnd.getrandbits(64) for _ in range(16)]
ZE = [_rnd.getrandbits(64) for _ in range(8)]
ZS = _rnd.getrandbits(64)
B = [0] * 128
S = 1
C = 0
E = -1
H = 0
Z = 0
SC = 0
KS = [4, 116]
U = []
PATH = []
CNT = [0] * 13
ND = 0
LIM = 0
ABT = False
TTK = [0] * 131072
TTD = [0] * 131072
TTF = [0] * 131072
TTS = [0] * 131072
TTM = [0] * 131072
KIL = [[0, 0] for _ in range(128)]
HST = [0] * 1664


def setup(fen):
    global S, C, E, H, Z, SC
    for i in range(128):
        B[i] = 0
    for i in range(13):
        CNT[i] = 0
    U.clear()
    PATH.clear()
    Z = 0
    SC = 0
    parts = fen.split()
    sq = 112
    for ch in parts[0]:
        if ch == "/":
            sq -= 24
        elif ch.isdigit():
            sq += int(ch)
        else:
            pc = "pnbrqk".index(ch.lower()) + 1
            if ch.isupper():
                B[sq] = pc
                KS[0] = sq if pc == 6 else KS[0]
            else:
                B[sq] = -pc
                KS[1] = sq if pc == 6 else KS[1]
            Z ^= ZP[B[sq] + 6][sq]
            CNT[B[sq] + 6] += 1
            if pc != 6:
                SC += PSV[B[sq] + 6][sq]
            sq += 1
    S = 1 if parts[1] == "w" else -1
    if S == -1:
        Z ^= ZS
    C = 0
    for ch in parts[2]:
        if ch == "K":
            C |= 1
        elif ch == "Q":
            C |= 2
        elif ch == "k":
            C |= 4
        elif ch == "q":
            C |= 8
    Z ^= ZC[C]
    if parts[3] == "-":
        E = -1
    else:
        E = (ord(parts[3][1]) - 49) * 16 + ord(parts[3][0]) - 97
        Z ^= ZE[E & 7]
    H = int(parts[4])
    PATH.append(Z)


def attacked(sq, by):
    if by == 1:
        for t in (sq - 15, sq - 17):
            if not t & 0x88 and B[t] == 1:
                return True
    else:
        for t in (sq + 15, sq + 17):
            if not t & 0x88 and B[t] == -1:
                return True
    for d in KN:
        t = sq + d
        if not t & 0x88 and B[t] == 2 * by:
            return True
    for d in KI:
        t = sq + d
        if not t & 0x88 and B[t] == 6 * by:
            return True
    for d in RD:
        t = sq + d
        while not t & 0x88:
            p = B[t]
            if p:
                if p == 4 * by or p == 5 * by:
                    return True
                break
            t += d
    for d in BD:
        t = sq + d
        while not t & 0x88:
            p = B[t]
            if p:
                if p == 3 * by or p == 5 * by:
                    return True
                break
            t += d
    return False


def make(m):
    global S, C, E, H, Z, SC
    f = m & 127
    t = m >> 7 & 127
    pr = m >> 14 & 7
    pc = B[f]
    cap = B[t]
    cs = t
    sd = 16 * S
    si = 0 if S == 1 else 1
    if (pc == 1 or pc == -1) and t == E and cap == 0:
        cs = t - sd
        cap = B[cs]
    U.append((m, cap, cs, C, E, H, Z, SC))
    if pc != 6 and pc != -6:
        SC += PSV[pc + 6][t] - PSV[pc + 6][f]
    if cap:
        SC -= PSV[cap + 6][cs]
    if pr:
        SC += PSV[pr * S + 6][t] - PSV[pc + 6][t]
    if cs != t:
        B[cs] = 0
    Z ^= ZP[pc + 6][f]
    if cap:
        Z ^= ZP[cap + 6][cs]
        CNT[cap + 6] -= 1
    if pr:
        Z ^= ZP[pr * S + 6][t]
        CNT[pr * S + 6] += 1
        CNT[pc + 6] -= 1
        B[t] = pr * S
    else:
        Z ^= ZP[pc + 6][t]
        B[t] = pc
    B[f] = 0
    if pc == 6 or pc == -6:
        KS[si] = t
        if t - f == 2:
            B[f + 1] = B[f + 3]
            B[f + 3] = 0
            SC += PSV[4 * S + 6][f + 1] - PSV[4 * S + 6][f + 3]
            Z ^= ZP[B[f + 1] + 6][f + 3] ^ ZP[B[f + 1] + 6][f + 1]
        elif f - t == 2:
            B[f - 1] = B[f - 4]
            B[f - 4] = 0
            SC += PSV[4 * S + 6][f - 1] - PSV[4 * S + 6][f - 4]
            Z ^= ZP[B[f - 1] + 6][f - 4] ^ ZP[B[f - 1] + 6][f - 1]
    nc = C & CK[f] & CK[t]
    if nc != C:
        Z ^= ZC[C] ^ ZC[nc]
        C = nc
    if E != -1:
        Z ^= ZE[E & 7]
    if (pc == 1 or pc == -1) and t - f == 2 * sd:
        E = f + sd
        Z ^= ZE[E & 7]
    else:
        E = -1
    H = 0 if pc == 1 or pc == -1 or cap else H + 1
    S = -S
    Z ^= ZS
    PATH.append(Z)
    if attacked(KS[si], S):
        unmake()
        return False
    return True


def unmake():
    global S, C, E, H, Z, SC
    m, cap, cs, C, E, H, Z, SC = U.pop()
    f = m & 127
    t = m >> 7 & 127
    pr = m >> 14 & 7
    S = -S
    si = 0 if S == 1 else 1
    pc = S if pr else B[t]
    B[f] = pc
    if cs != t:
        B[cs] = cap
        B[t] = 0
    else:
        B[t] = cap
    if pc == 6 or pc == -6:
        KS[si] = f
        if t - f == 2:
            B[f + 3] = B[f + 1]
            B[f + 1] = 0
        elif f - t == 2:
            B[f - 4] = B[f - 1]
            B[f - 1] = 0
    if pr:
        CNT[pr * S + 6] -= 1
        CNT[S + 6] += 1
    if cap:
        CNT[cap + 6] += 1
    PATH.pop()


def gen(caps):
    ms = []
    sd = 16 * S
    sr = 1 if S == 1 else 6
    prr = 6 if S == 1 else 1
    for r in range(8):
        for f in range(8):
            sq = r * 16 + f
            pc = B[sq]
            if not pc or (pc > 0) != (S == 1):
                continue
            t = pc if pc > 0 else -pc
            if t == 1:
                to = sq + sd
                if not to & 0x88 and B[to] == 0 and (not caps or sq >> 4 == prr):
                    if sq >> 4 == prr:
                        for p in (5, 4, 3, 2):
                            ms.append(sq | to << 7 | p << 14)
                    else:
                        ms.append(sq | to << 7)
                        if sq >> 4 == sr:
                            to2 = sq + 2 * sd
                            if B[to2] == 0:
                                ms.append(sq | to2 << 7)
                for to in (sq + sd - 1, sq + sd + 1):
                    if to & 0x88:
                        continue
                    q = B[to]
                    if q and (q > 0) != (S == 1):
                        if sq >> 4 == prr:
                            for p in (5, 4, 3, 2):
                                ms.append(sq | to << 7 | p << 14)
                        else:
                            ms.append(sq | to << 7)
                    elif to == E and not q:
                        ms.append(sq | to << 7)
            elif t == 2:
                for d in KN:
                    to = sq + d
                    if to & 0x88:
                        continue
                    q = B[to]
                    if not q or (q > 0) != (S == 1):
                        if not caps or q:
                            ms.append(sq | to << 7)
            elif t == 6:
                for d in KI:
                    to = sq + d
                    if to & 0x88:
                        continue
                    q = B[to]
                    if not q or (q > 0) != (S == 1):
                        if not caps or q:
                            ms.append(sq | to << 7)
                if not caps:
                    if S == 1:
                        if C & 1 and not B[5] and not B[6] and not attacked(4, -1) and not attacked(5, -1) and not attacked(6, -1):
                            ms.append(4 | 6 << 7)
                        if C & 2 and not B[3] and not B[2] and not B[1] and not attacked(4, -1) and not attacked(3, -1) and not attacked(2, -1):
                            ms.append(4 | 2 << 7)
                    else:
                        if C & 4 and not B[117] and not B[118] and not attacked(116, 1) and not attacked(117, 1) and not attacked(118, 1):
                            ms.append(116 | 118 << 7)
                        if C & 8 and not B[115] and not B[114] and not B[113] and not attacked(116, 1) and not attacked(115, 1) and not attacked(114, 1):
                            ms.append(116 | 114 << 7)
            else:
                ds = BD if t == 3 else RD if t == 4 else BD + RD
                for d in ds:
                    to = sq + d
                    while not to & 0x88:
                        q = B[to]
                        if not q:
                            if not caps:
                                ms.append(sq | to << 7)
                        else:
                            if (q > 0) != (S == 1):
                                ms.append(sq | to << 7)
                            break
                        to += d
    return ms


def legal():
    out = []
    for m in gen(False):
        if make(m):
            out.append(m)
            unmake()
    return out


def ev():
    s = SC
    if CNT[9] >= 2:
        s += 30
    if CNT[3] >= 2:
        s -= 30
    ph = 320 * (CNT[8] + CNT[4]) + 330 * (CNT[9] + CNT[3]) + 500 * (CNT[10] + CNT[2]) + 900 * (CNT[11] + CNT[1])
    if ph > 6400:
        ph = 6400
    r = KS[0] >> 4
    f = KS[0] & 7
    i = (7 - r) * 8 + f
    s += (KMG[i] * ph + KEG[i] * (6400 - ph)) // 6400
    r = KS[1] >> 4
    f = KS[1] & 7
    i = r * 8 + f
    s -= (KMG[i] * ph + KEG[i] * (6400 - ph)) // 6400
    return s if S == 1 else -s


def order(ms, ply, ttm):
    sc = []
    for m in ms:
        f = m & 127
        t = m >> 7 & 127
        pr = m >> 14 & 7
        pc = B[f]
        if m == ttm:
            s = 10000000
        elif pr:
            s = 900000 + VAL[pr]
        else:
            cap = B[t]
            v = 0
            if cap:
                v = VAL[cap] if cap > 0 else VAL[-cap]
            elif t == E and (pc == 1 or pc == -1):
                v = 100
            if v:
                s = 1000000 + 10 * v - (VAL[pc] if pc > 0 else VAL[-pc])
            elif m == KIL[ply][0]:
                s = 500000
            elif m == KIL[ply][1]:
                s = 400000
            else:
                s = HST[(pc + 6) * 128 + t]
        sc.append((-s, m))
    sc.sort()
    return [m for _, m in sc]


def quiesce(a, b, ply):
    global ND, ABT
    ND += 1
    if LIM and ND >= LIM:
        ABT = True
        return 0
    if ply >= 120:
        return ev()
    chk = attacked(KS[0 if S == 1 else 1], -S)
    if not chk:
        st = ev()
        if st >= b:
            return st
        best = st
        if st > a:
            a = st
    else:
        best = -MATE
        st = 0
    ms = order(gen(not chk), ply, 0)
    legal = 0
    for m in ms:
        if not chk:
            pr = m >> 14 & 7
            if not pr:
                t = m >> 7 & 127
                cap = B[t]
                v = (VAL[cap] if cap > 0 else VAL[-cap]) if cap else 100 if t == E else 0
                if v and st + v + 200 < a:
                    continue
        if not make(m):
            continue
        legal += 1
        sc = -quiesce(-b, -a, ply + 1)
        unmake()
        if ABT:
            return 0
        if sc > best:
            best = sc
        if sc >= b:
            return sc
        if sc > a:
            a = sc
    if chk and not legal:
        return -MATE + ply
    return best


def negamax(d, a, b, ply):
    global ND, ABT, C, E, H, Z, S
    if ply > 0 and (H >= 100 or PATH.count(Z) > 1):
        return 0
    if d <= 0:
        return quiesce(a, b, ply)
    ND += 1
    if LIM and ND >= LIM:
        ABT = True
        return 0
    if ply >= 120:
        return ev()
    slot = Z & 131071
    ttm = 0
    if TTK[slot] == Z:
        ttm = TTM[slot]
        if TTD[slot] >= d:
            s = TTS[slot]
            if s > 99000:
                s -= ply
            elif s < -99000:
                s += ply
            fl = TTF[slot]
            if fl == 1 or fl == 2 and s >= b or fl == 3 and s <= a:
                return s
    chk = attacked(KS[0 if S == 1 else 1], -S)
    a0 = a
    if d >= 3 and not chk:
        npc = CNT[8] + CNT[9] + CNT[10] + CNT[11] if S == 1 else CNT[4] + CNT[3] + CNT[2] + CNT[1]
        if npc:
            st = ev()
            if st >= b:
                oC, oE, oH, oZ, oS = C, E, H, Z, S
                if E != -1:
                    Z ^= ZE[E & 7]
                E = -1
                H = H + 1
                S = -S
                Z ^= ZS
                PATH.append(Z)
                sc = -negamax(d - 3, -b, -b + 1, ply + 1)
                PATH.pop()
                C, E, H, Z, S = oC, oE, oH, oZ, oS
                if ABT:
                    return 0
                if sc >= b:
                    return sc
    ms = order(gen(False), ply, ttm)
    best = -MATE
    bestm = 0
    legal = 0
    for i, m in enumerate(ms):
        f = m & 127
        t = m >> 7 & 127
        pr = m >> 14 & 7
        pc = B[f]
        cap = B[t]
        quiet = not cap and not pr and not (t == E and (pc == 1 or pc == -1))
        if not make(m):
            continue
        legal += 1
        if quiet and i >= 3 and d >= 3 and not chk:
            sc = -negamax(d - 2, -b, -a, ply + 1)
            if sc > a:
                sc = -negamax(d - 1, -b, -a, ply + 1)
        else:
            sc = -negamax(d - 1, -b, -a, ply + 1)
        unmake()
        if ABT:
            return 0
        if sc > best:
            best = sc
            bestm = m
        if sc > a:
            a = sc
        if a >= b:
            if quiet:
                if KIL[ply][0] != m:
                    KIL[ply][1] = KIL[ply][0]
                    KIL[ply][0] = m
                HST[(pc + 6) * 128 + t] += d * d
            break
    if not legal:
        return -MATE + ply if chk else 0
    TTK[slot] = Z
    TTD[slot] = d
    TTM[slot] = bestm
    s2 = best
    if s2 > 99000:
        s2 += ply
    elif s2 < -99000:
        s2 -= ply
    TTS[slot] = s2
    TTF[slot] = 3 if best <= a0 else 2 if best >= b else 1
    return best


def root():
    global ND, ABT, LIM
    ms = legal()
    if not ms:
        return 0
    if len(ms) == 1:
        return ms[0]
    ND = 0
    ABT = False
    LIM = NODES
    best = ms[0]
    for d in range(1, 65):
        a = -MATE
        bm = best
        for i, m in enumerate(order(ms, 0, best)):
            make(m)
            if i == 0:
                sc = -negamax(d - 1, -MATE, MATE, 1)
            else:
                sc = -negamax(d - 1, -MATE, -a, 1)
            unmake()
            if ABT:
                break
            if sc > a:
                a = sc
                bm = m
        if ABT:
            break
        best = bm
        if a > 99000:
            break
    return best


def uci(m):
    f = m & 127
    t = m >> 7 & 127
    pr = m >> 14 & 7
    s = "abcdefgh"[f & 7] + str((f >> 4) + 1) + "abcdefgh"[t & 7] + str((t >> 4) + 1)
    if pr:
        s += "  nbrq"[pr]
    return s


def parse_uci(u):
    f = (ord(u[1]) - 49) * 16 + ord(u[0]) - 97
    t = (ord(u[3]) - 49) * 16 + ord(u[2]) - 97
    pr = "nbrq".index(u[4]) + 2 if len(u) == 5 else 0
    return f | t << 7 | pr << 14


def choose(fen, gmv):
    setup(fen)
    fb = B[:]
    setup(START)
    ok = True
    for u in gmv:
        want = parse_uci(u)
        found = 0
        for cand in gen(False):
            if cand & 127 == want & 127 and cand >> 7 & 127 == want >> 7 & 127 and cand >> 14 & 7 == want >> 14 & 7:
                found = cand
                break
        if not found or not make(found):
            ok = False
            break
    if not ok or B != fb:
        setup(fen)
    return root()


# === driver ===
URL = os.environ.get("MAKEFUN_ENV_URL") or sys.exit("MAKEFUN_ENV_URL is not set")


def post(path, body):
    req = urllib.request.Request(URL + path, data=json.dumps(body).encode(),
                                 headers={"content-type": "application/json"})
    try:
        with urllib.request.urlopen(req, timeout=9) as r:
            return json.load(r)
    except urllib.error.HTTPError as e:
        return {"_http": e.code, "_body": e.read().decode(errors="replace")}
    except Exception as e:
        return {"_http": 0, "_body": str(e)}


while True:
    g = post("/game", {})
    if g.get("status") == "done":
        break
    if "_http" in g:
        print("game error", g, file=sys.stderr)
        break
    while g.get("status") == "your_move":
        mv = choose(g["fen"], g["moves"])
        g2 = post("/move", {"game": g["game"], "move": uci(mv)})
        if "_http" in g2:
            print("move refused", uci(mv), g2, file=sys.stderr)
            for alt in g["legal_moves"]:
                g2 = post("/move", {"game": g["game"], "move": alt})
                if "_http" not in g2:
                    break
            else:
                g2 = post("/resign", {"game": g["game"]})
        g = g2
    print(f"game {g.get('game')}: {g.get('outcome')} by {g.get('reason')}", file=sys.stderr)
print("done", file=sys.stderr)
