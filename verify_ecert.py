"""
verify_ecert.py (Hardened Release Copy — Erdős #634 ECERT_V1, e.g. T_2(5,6) N=332)
100% Independent Pure-Python Exact-Rational (fractions.Fraction) Verifier for .ecert certificates!
ZERO floating point, ZERO C++, arbitrary-precision Python integers!
Used as a second completely independent language/runtime cross-check alongside verify_ecert_hardened.cpp.
Includes strict malformed-input bounds checks and seen_apex[2][2] duplicate/completeness checks.
"""
import math, sys, time
from fractions import Fraction


class ExactQzetaVerifier:
    def __init__(self, e, f, M):
        assert e > 0 and f > e and M >= 1 and math.gcd(e, f) == 1
        self.e, self.f, self.M = e, f, M
        self.a = e * f
        self.b = f * f - e * e
        self.c = f * f
        self.ef = Fraction(e, f)
        self.KOFF = 24
        self.MAX_P = 24
        self.zpow = {}
        self.zpow[0] = (Fraction(1), Fraction(0))
        for k in range(1, self.KOFF + 1):
            px, py = self.zpow[k - 1]
            self.zpow[k] = (-py, px + py * self.ef)
        for k in range(1, self.KOFF + 1):
            px, py = self.zpow[-(k - 1)]
            self.zpow[-k] = (px * self.ef + py, -px)
        self.leg = M * f**3
        self.base = M * e * (3 * f * f - e * e)
        self.tgt_p = [
            (Fraction(0), Fraction(0)),
            (Fraction(self.leg), Fraction(0)),
            self.scale(self.dvec((-6, -1)), self.leg),
        ]
        self.tgt_ed = [(0, 1), (-3, 1), (-6, 1)]
        self.tgt_len = [self.leg, self.base, self.leg]
        assert self.norm2(self.sub(self.tgt_p[2], self.tgt_p[1])) == self.base * self.base
        assert self.sub(self.tgt_p[1], self.tgt_p[0]) == self.scale(self.dvec(self.tgt_ed[0]), self.leg)
        assert self.sub(self.tgt_p[2], self.tgt_p[1]) == self.scale(self.dvec(self.tgt_ed[1]), self.base)
        assert self.sub(self.tgt_p[0], self.tgt_p[2]) == self.scale(self.dvec(self.tgt_ed[2]), self.leg)
        assert self.orient(self.tgt_p[0], self.tgt_p[1], self.tgt_p[2]) > 0
        # Verify all 6 tile slots at startup
        for sl in range(6):
            self.make_tile((Fraction(0), Fraction(0)), (0, 1), sl)
        mx = max(self.tgt_len)
        sg = [False] * (mx + 1)
        sg[0] = True
        for i in range(mx + 1):
            if sg[i]:
                for s in (self.a, self.b, self.c):
                    if i + s <= mx:
                        sg[i + s] = True
        self.in_sg = sg
        self.max_side = mx
        # Precompute exact (A, B) table for all dir pairs using zero-float winding
        self._ab_cache = {}
        self._cross_cache = {}

    def dvec(self, d):
        k, s = d
        assert -self.KOFF <= k <= self.KOFF and s in (1, -1)
        vx, vy = self.zpow[k]
        return (vx, vy) if s > 0 else (-vx, -vy)

    @staticmethod
    def add(u, v): return (u[0] + v[0], u[1] + v[1])
    @staticmethod
    def sub(u, v): return (u[0] - v[0], u[1] - v[1])
    @staticmethod
    def scale(u, s): return (u[0] * s, u[1] * s)
    def norm2(self, u): return u[0]*u[0] + u[1]*u[1] + self.ef * u[0] * u[1]
    @staticmethod
    def cross(u, v): return u[0]*v[1] - u[1]*v[0]

    def orient(self, p0, p1, p2):
        c = (p1[0] - p0[0])*(p2[1] - p0[1]) - (p1[1] - p0[1])*(p2[0] - p0[0])
        return 1 if c > 0 else (-1 if c < 0 else 0)

    def dcross(self, d1, d2):
        key = (d1, d2)
        if key not in self._cross_cache:
            c = self.cross(self.dvec(d1), self.dvec(d2))
            self._cross_cache[key] = 1 if c > 0 else (-1 if c < 0 else 0)
        return self._cross_cache[key]

    def half(self, d):
        vx, vy = self.dvec(d)
        return 0 if (vy > 0 or (vy == 0 and vx > 0)) else 1

    def exact_ab(self, d1, d2):
        key = (d1, d2)
        if key in self._ab_cache:
            return self._ab_cache[key]
        if d1 == d2:
            res = (0, 0)
        elif d1[0] == d2[0]:
            res = (3, 2)
        else:
            dk = d2[0] - d1[0]
            wraps = 0
            cur = (0, 1)
            if dk > 0:
                for _ in range(dk):
                    nxt = (cur[0] + 1, 1)
                    if self.half(cur) == 1 and self.half(nxt) == 0:
                        wraps += 1
                    cur = nxt
            else:
                for _ in range(-dk):
                    nxt = (cur[0] - 1, 1)
                    if self.half(cur) == 0 and self.half(nxt) == 1:
                        wraps -= 1
                    cur = nxt
            n = -2 * wraps
            if d1[1] != d2[1]:
                n += (1 if self.half(cur) == 0 else -1)
            res = (3 * n + dk, 2 * n + dk)
        self._ab_cache[key] = res
        return res

    def between(self, d1, d2, d):
        if d == d1 or d == d2:
            return False
        c12 = self.dcross(d1, d2)
        c1d = self.dcross(d1, d)
        cd2 = self.dcross(d, d2)
        if c12 > 0:
            return c1d > 0 and cd2 > 0
        if c12 < 0:
            return c1d > 0 or cd2 > 0
        return c1d > 0

    def make_tile(self, v, d, slot):
        k, s = d
        a, b, c = self.a, self.b, self.c
        if slot == 0:   l1, l2, l3, d2, d12 = a, c, b, (k+3, -s), (k+1, s)
        elif slot == 1: l1, l2, l3, d2, d12 = c, a, b, (k+3, -s), (k+2, s)
        elif slot == 2: l1, l2, l3, d2, d12 = b, c, a, (k-2, -s), (k+1, s)
        elif slot == 3: l1, l2, l3, d2, d12 = c, b, a, (k-2, -s), (k-3, s)
        elif slot == 4: l1, l2, l3, d2, d12 = a, b, c, (k-1, -s), (k-3, s)
        elif slot == 5: l1, l2, l3, d2, d12 = b, a, c, (k-1, -s), (k+2, s)
        else: raise ValueError("bad slot")
        p0 = v
        p1 = self.add(v, self.scale(self.dvec(d), l1))
        p2 = self.add(v, self.scale(self.dvec(d2), l2))
        assert self.orient(p0, p1, p2) > 0
        assert self.norm2(self.sub(p1, p0)) == l1 * l1
        assert self.norm2(self.sub(p2, p1)) == l3 * l3
        assert self.norm2(self.sub(p0, p2)) == l2 * l2
        assert self.sub(p2, p1) == self.scale(self.dvec(d12), l3)
        return ((p0, p1, p2), (d, d12, (d2[0], -d2[1])), (l1, l3, l2))

    def tri_from_verts(self, q0, q1, q2):
        o = self.orient(q0, q1, q2)
        assert o != 0
        if o < 0:
            q1, q2 = q2, q1
        pts = (q0, q1, q2)
        eds = []
        lens = []
        for i in range(3):
            diff = self.sub(pts[(i + 1) % 3], pts[i])
            n2 = self.norm2(diff)
            if n2 == self.a * self.a: L = self.a
            elif n2 == self.b * self.b: L = self.b
            elif n2 == self.c * self.c: L = self.c
            else: raise AssertionError("non-congruent nogood tile")
            lens.append(L)
            fd = None
            for k in range(-self.KOFF, self.KOFF + 1):
                for s in (1, -1):
                    if self.scale(self.dvec((k, s)), L) == diff:
                        fd = (k, s)
                        break
                if fd:
                    break
            assert fd is not None
            eds.append(fd)
        assert sorted(lens) == sorted([self.a, self.b, self.c])
        return (pts, tuple(eds), tuple(lens))

    def in_tgt(self, q):
        tp = self.tgt_p
        return (self.orient(tp[0], tp[1], q) >= 0 and
                self.orient(tp[1], tp[2], q) >= 0 and
                self.orient(tp[2], tp[0], q) >= 0)

    def overlap(self, t1, t2):
        p1, p2 = t1[0], t2[0]
        for u, v in ((p1, p2), (p2, p1)):
            for i in range(3):
                a, b = u[i], u[(i + 1) % 3]
                if self.orient(a, b, v[0]) <= 0 and self.orient(a, b, v[1]) <= 0 and self.orient(a, b, v[2]) <= 0:
                    return False
        return True

    def verify_gap(self, eidx, C):
        if eidx < 0 or eidx > 2:
            return False
        P0 = self.tgt_p[eidx]
        P1 = self.tgt_p[(eidx + 1) % 3]
        dv = self.dvec(self.tgt_ed[eidx])
        L = Fraction(self.tgt_len[eidx])
        segs = []
        for t in C:
            pts = t[0]
            on = [j for j in range(3) if self.orient(P0, P1, pts[j]) == 0]
            if not on:
                continue
            vals = []
            for j in on:
                diff = self.sub(pts[j], P0)
                r = diff[0] / dv[0] if dv[0] != 0 else diff[1] / dv[1]
                vals.append(r)
            segs.append((min(vals), max(vals)))
        if not segs:
            return False
        segs.sort()
        cur = Fraction(0)
        for sa, sb in segs:
            if cur < sa:
                g = sa - cur
                if g.denominator != 1 or g.numerator < 0 or g.numerator > self.max_side or not self.in_sg[g.numerator]:
                    return True
            if cur < sb:
                cur = sb
        if cur < L:
            g = L - cur
            if g.denominator != 1 or g.numerator < 0 or g.numerator > self.max_side or not self.in_sg[g.numerator]:
                return True
        return False

    def free_arcs(self, v, C):
        iv = []
        for i in range(3):
            o = self.orient(self.tgt_p[i], self.tgt_p[(i + 1) % 3], v)
            if o < 0:
                return None
            if o == 0:
                ed = self.tgt_ed[i]
                iv.append(((ed[0], -ed[1]), ed))
        for t in C:
            p, ed, _ = t
            o0 = self.orient(p[0], p[1], v)
            if o0 < 0: continue
            o1 = self.orient(p[1], p[2], v)
            if o1 < 0: continue
            o2 = self.orient(p[2], p[0], v)
            if o2 < 0: continue
            if o0 > 0 and o1 > 0 and o2 > 0:
                return None
            if v == p[0]: iv.append((ed[0], (ed[2][0], -ed[2][1])))
            elif v == p[1]: iv.append((ed[1], (ed[0][0], -ed[0][1])))
            elif v == p[2]: iv.append((ed[2], (ed[1][0], -ed[1][1])))
            elif o0 == 0: iv.append((ed[0], (ed[0][0], -ed[0][1])))
            elif o1 == 0: iv.append((ed[1], (ed[1][0], -ed[1][1])))
            elif o2 == 0: iv.append((ed[2], (ed[2][0], -ed[2][1])))
        if not iv:
            return None
        from functools import cmp_to_key
        def cmp_d(d1, d2):
            if d1 == d2: return 0
            h1, h2 = self.half(d1), self.half(d2)
            if h1 != h2: return -1 if h1 < h2 else 1
            return -1 if self.dcross(d1, d2) > 0 else 1
        marks = sorted(set([x for a in iv for x in a]), key=cmp_to_key(cmp_d))
        k = len(marks)
        free_sec = []
        for i in range(k):
            d = marks[i]
            fr = True
            for s, e in iv:
                if d == s or self.between(s, e, d):
                    fr = False
                    break
            free_sec.append(fr)
        if all(free_sec):
            return None
        start = free_sec.index(False)
        farcs = []
        i = 0
        while i < k:
            idx = (start + i) % k
            if free_sec[idx]:
                ds = marks[idx]
                j = i
                while j < k and free_sec[(start + j) % k]:
                    j += 1
                de = marks[(start + j) % k]
                A, B = self.exact_ab(ds, de)
                farcs.append((ds, de, A, B))
                i = j
            else:
                i += 1
        return farcs

    def pointed_feas(self, v, d, C):
        farcs = self.free_arcs(v, C)
        if farcs is None:
            return None
        fi = next((i for i, fa in enumerate(farcs) if fa[0] == d), -1)
        if fi < 0:
            return None
        for fb in farcs:
            if self.dcross(d, fb[1]) <= 0:
                return None
            if fb[0] != d and self.dcross(d, fb[0]) <= 0:
                return None
        faA, faB = farcs[fi][2], farcs[fi][3]
        fm = 0
        for sl in range(6):
            dA = 0 if sl <= 1 else (1 if sl <= 3 else 2)
            dB = 1 if sl <= 1 else (0 if sl <= 3 else 1)
            if faA - dA < 0 or faB - dB < 0:
                continue
            cand = self.make_tile(v, d, sl)
            if not self.in_tgt(cand[0][1]) or not self.in_tgt(cand[0][2]):
                continue
            if any(self.overlap(u, cand) for u in C):
                continue
            fm |= (1 << sl)
        return fm

    def verify_file(self, path, max_apex=4):
        t0 = time.time()
        with open(path) as fh:
            lines = [l.strip() for l in fh if l.strip()]
        idx = 0
        hdr = lines[idx].split(); idx += 1
        assert hdr[0] == "ECERT_V1"
        e, f, M = int(hdr[1]), int(hdr[2]), int(hdr[3])
        assert (e, f, M) == (self.e, self.f, self.M)

        def parse_pt(toks, off):
            x, y, p = int(toks[off]), int(toks[off+1]), int(toks[off+2])
            assert 0 <= p <= self.MAX_P, f"p={p} out of range"
            den = self.f ** p
            return (Fraction(x, den), Fraction(y, den))

        def check_dir(d):
            assert -self.KOFF <= d[0] <= self.KOFF and d[1] in (1, -1), f"bad dir {d}"
            return d

        def parse_node(line):
            t = line.split()
            tp = t[0]
            if tp == 'B':
                v = parse_pt(t, 1)
                d = check_dir((int(t[4]), int(t[5])))
                nk = int(t[6])
                assert 0 <= nk <= 6, f"invalid B nkids={nk}"
                assert len(t) == 7 + 2 * nk
                kids = []
                for i in range(nk):
                    sl, ch = int(t[7 + 2*i]), int(t[8 + 2*i])
                    assert 0 <= sl < 6, f"invalid kslot={sl}"
                    kids.append((sl, ch))
                return ('B', v, d, kids)
            elif tp == 'C':
                return ('C', parse_pt(t, 1), check_dir((int(t[4]), int(t[5]))))
            elif tp == 'A':
                return ('A', parse_pt(t, 1), check_dir((int(t[4]), int(t[5]))), check_dir((int(t[6]), int(t[7]))))
            elif tp == 'G':
                eidx = int(t[1])
                assert 0 <= eidx <= 2
                return ('G', eidx)
            elif tp in ('R', 'F'):
                ref_id = int(t[1])
                assert ref_id >= 0
                return (tp, ref_id)
            raise ValueError(line)

        def tkey(tr): return tuple(sorted(tr[0]))

        dag_nodes = 0
        pref_nodes = 0
        total_ngs = 0
        apex_count = 0
        seen_apex = [[False, False], [False, False]]
        saw_end = False

        while idx < len(lines):
            if lines[idx] == "END":
                saw_end = True
                break
            if apex_count >= max_apex:
                break
            ap = lines[idx].split(); idx += 1
            assert ap[0] == "APEX"
            s1, s2, s3, npt, proot, nf = map(int, ap[1:])
            assert s1 in (2, 3) and s2 == 2 and s3 in (2, 3), f"Invalid apex ({s1},{s2},{s3})"
            assert not seen_apex[s1 - 2][s3 - 2], f"Duplicate apex ({s1},{s2},{s3})"
            seen_apex[s1 - 2][s3 - 2] = True
            assert npt > 0 and 0 <= proot < npt and nf >= 0
            ptree = [parse_node(lines[idx + i]) for i in range(npt)]; idx += npt
            subs = []
            for _ in range(nf):
                sp = lines[idx].split(); idx += 1
                assert sp[0] == "SUBPROOF"
                ntk, nnd, nng, sroot = map(int, sp[1:])
                assert ntk >= 0 and nnd > 0 and nng >= 0 and 0 <= sroot < nnd
                ktris, kkeys = [], []
                for _ in range(ntk):
                    kt = lines[idx].split(); idx += 1
                    assert kt[0] == 'K'
                    tr = self.tri_from_verts(parse_pt(kt, 1), parse_pt(kt, 4), parse_pt(kt, 7))
                    ktris.append(tr); kkeys.append(tkey(tr))
                nodes = [parse_node(lines[idx + i]) for i in range(nnd)]; idx += nnd
                ngs = []
                for _ in range(nng):
                    nt = lines[idx].split(); idx += 1
                    assert nt[0] == 'N'
                    r = int(nt[1]); cnt = int(nt[2])
                    assert 0 <= r < nnd and cnt >= 0 and len(nt) == 3 + cnt
                    tids = [int(nt[3 + j]) for j in range(cnt)]
                    for tid in tids:
                        assert 0 <= tid < ntk, f"nogood tid={tid} out of bounds [0,{ntk})"
                    ngs.append((r, tids))
                subs.append((sroot, ktris, kkeys, nodes, ngs))

            def check_dag(nid, nodes, ng_keys, max_ng, C):
                nonlocal dag_nodes
                if nid < 0 or nid >= len(nodes):
                    return False
                dag_nodes += 1
                nd = nodes[nid]
                tp = nd[0]
                if tp == 'G': return self.verify_gap(nd[1], C)
                elif tp == 'A':
                    farcs = self.free_arcs(nd[1], C)
                    return farcs is not None and any(fa[0] == nd[2] and fa[1] == nd[3] and (fa[2] < 0 or fa[3] < 0) for fa in farcs)
                elif tp == 'C':
                    fm = self.pointed_feas(nd[1], nd[2], C)
                    return fm == 0
                elif tp == 'R':
                    gid = nd[1]
                    if gid < 0 or gid >= max_ng: return False
                    cset = set(tkey(t) for t in C)
                    return all(rk in cset for rk in ng_keys[gid])
                elif tp == 'B':
                    fm = self.pointed_feas(nd[1], nd[2], C)
                    if fm is None: return False
                    cov = 0
                    for sl, _ in nd[3]: cov |= (1 << sl)
                    if (fm & ~cov) != 0: return False
                    for sl, ch in nd[3]:
                        if not (fm & (1 << sl)): continue
                        C.append(self.make_tile(nd[1], nd[2], sl))
                        ok = check_dag(ch, nodes, ng_keys, max_ng, C)
                        C.pop()
                        if not ok: return False
                    return True
                return False

            all_ng_keys = []
            for fi, (sroot, ktris, kkeys, nodes, ngs) in enumerate(subs):
                ng_ks = []
                for g, (gr, tids) in enumerate(ngs):
                    ngC = [ktris[tid] for tid in tids]
                    ng_ks.append([kkeys[tid] for tid in tids])
                    assert check_dag(gr, nodes, ng_ks, g, ngC), f"nogood {g} failed in subproof {fi}"
                    total_ngs += 1
                all_ng_keys.append(ng_ks)

            O = self.tgt_p[0]
            d0 = (0, 1); d1 = (-2, -1); d2 = (-4, 1)
            C = [self.make_tile(O, d0, s1), self.make_tile(O, d1, s2), self.make_tile(O, d2, s3)]

            def check_pref(pid):
                nonlocal pref_nodes
                if pid < 0 or pid >= len(ptree):
                    return False
                nd = ptree[pid]
                tp = nd[0]
                if tp == 'F':
                    fi = nd[1]
                    if fi < 0 or fi >= len(subs):
                        return False
                    sroot, _, _, nodes, ngs = subs[fi]
                    return check_dag(sroot, nodes, all_ng_keys[fi], len(ngs), C)
                pref_nodes += 1
                if tp == 'G': return self.verify_gap(nd[1], C)
                elif tp == 'A':
                    farcs = self.free_arcs(nd[1], C)
                    return farcs is not None and any(fa[0] == nd[2] and fa[1] == nd[3] and (fa[2] < 0 or fa[3] < 0) for fa in farcs)
                elif tp == 'C': return self.pointed_feas(nd[1], nd[2], C) == 0
                elif tp == 'B':
                    fm = self.pointed_feas(nd[1], nd[2], C)
                    if fm is None: return False
                    cov = 0
                    for sl, _ in nd[3]:
                        if sl < 0 or sl >= 6: return False
                        cov |= (1 << sl)
                    if (fm & ~cov) != 0: return False
                    for sl, ch in nd[3]:
                        if not (fm & (1 << sl)): continue
                        C.append(self.make_tile(nd[1], nd[2], sl))
                        ok = check_pref(ch)
                        C.pop()
                        if not ok: return False
                    return True
                return False

            assert check_pref(proot), f"prefix failed for apex ({s1},{s2},{s3})"
            apex_count += 1
            print(f"  [Python Fraction] Apex ({s1},{s2},{s3}) 100% VERIFIED! "
                  f"(cum_nodes={dag_nodes + pref_nodes}, dag={dag_nodes}, pref_nonF={pref_nodes}, "
                  f"cum_ngs={total_ngs}, sec={time.time()-t0:.2f}s)", flush=True)

        if max_apex >= 4:
            for i in range(2):
                for j in range(2):
                    assert seen_apex[i][j], f"Missing apex case ({i+2},2,{j+2})"
            assert saw_end, "Missing END sentinel"

        print(f">>> PURE-PYTHON FRACTION VERIFICATION PASSED ({apex_count} apex cases, "
              f"{dag_nodes + pref_nodes} nodes [dag={dag_nodes}, pref_nonF={pref_nodes}], "
              f"{total_ngs} nogoods, {time.time()-t0:.2f}s)!")


if __name__ == "__main__":
    path = sys.argv[1]
    with open(path) as fh:
        _, e, f, M = fh.readline().split()
    max_ap = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    v = ExactQzetaVerifier(int(e), int(f), int(M))
    v.verify_file(path, max_apex=max_ap)
