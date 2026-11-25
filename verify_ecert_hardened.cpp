// verify_ecert.cpp (Hardened Release Copy — Erdős #634 N=236 & T_2(3,5))
// 100% INDEPENDENT, ZERO-FLOAT, ZERO-TRUST EXACT VERIFIER for .ecert refutation certificates!
// Written completely from scratch with ZERO floating-point operations in any geometric check:
//   - All points in Q[zeta] = { (x + y*zeta) / f^p } with exact __int128 arithmetic
//   - Runtime __builtin_{add,sub,mul}_overflow traps on EVERY __int128 operation (abort on overflow!)
//   - Explicit startup & runtime assertions verifying all 6 d12 vectors against exact Q[zeta] algebra
//   - Strict malformed-input bounds checks (nkids <= 6, pid < npt, tid < ntk, kslot < 6, END sentinel)
//   - Duplicate-apex & completeness check via seen_apex[2][2]
//   - Exact cyclic direction sorting via exact half-plane + cross-product comparator (ZERO trig / ZERO atan2!)
//   - Exact angle decomposition A*alpha + B*beta verified against exact trig-free integer step recurrences
//   - Exact side-length SSS congruence verification on every tile
//   - Exact target containment & exact pairwise SAT interior-disjointness (NO bbox shortcut!)
//   - Exact topological nogood DAG verification (each nogood verified strictly from its own tile subset
//     and earlier already-verified nogoods id' < id!)
//   - Built-in negative-control flag (--corrupt / arg2 = 1..5) to prove the verifier REJECTS invalid proofs!

#include <algorithm>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <functional>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <sstream>
#include <string>
#include <vector>

using i64 = int64_t;
using u64 = uint64_t;
using i128 = __int128_t;
using u128 = __uint128_t;

static constexpr i128 I128_MAX_VAL = (i128)(((u128)1 << 127) - 1);

static inline u128 abs_u128(i128 x) {
    return (x >= 0) ? (u128)x : ((u128)(-(x + 1)) + 1);
}

static std::string u128_to_str(u128 u) {
    if (u == 0) return "0";
    std::string s;
    while (u > 0) { s.push_back((char)('0' + (int)(u % 10))); u /= 10; }
    std::reverse(s.begin(), s.end());
    return s;
}

static bool parse_i128_checked(const std::string& s, i128& out) {
    if (s.empty()) return false;
    bool neg = false;
    size_t i = 0;
    if (s[0] == '-') { neg = true; i = 1; }
    if (i >= s.size()) return false;
    i128 v = 0;
    for (; i < s.size(); i++) {
        char ch = s[i];
        if (ch < '0' || ch > '9') return false;
        int d = ch - '0';
        if (__builtin_mul_overflow(v, (i128)10, &v)) {
            std::cerr << "FATAL: __int128 parse mul overflow on '" << s << "'\n";
            std::abort();
        }
        if (neg) {
            if (__builtin_sub_overflow(v, (i128)d, &v)) {
                std::cerr << "FATAL: __int128 parse sub overflow on '" << s << "'\n";
                std::abort();
            }
        } else {
            if (__builtin_add_overflow(v, (i128)d, &v)) {
                std::cerr << "FATAL: __int128 parse add overflow on '" << s << "'\n";
                std::abort();
            }
        }
    }
    out = v;
    return true;
}

struct Verifier {
    int e = 0, f = 0, M = 0;
    i64 a = 0, b = 0, c = 0;
    static constexpr int MAX_P = 24;
    static constexpr int MAX_POW = 52;
    static constexpr int KOFF = 24;
    static constexpr int KMAX = 49;
    int max_pow_f = 0;
    i128 POW_F[MAX_POW + 1];
    inline i128 get_pow_f(int idx) const {
        if (idx < 0 || idx > max_pow_f) {
            std::cerr << "FATAL: POW_F[" << idx << "] exceeds max_pow_f=" << max_pow_f << " for f=" << f << "!\n";
            std::abort();
        }
        return POW_F[idx];
    }

    // Overflow & headroom telemetry
    mutable bool in_post_init = false;
    mutable u128 max_abs_init = 0;
    mutable u128 max_abs_post = 0;
    mutable int max_p_seen = 0;

    inline void track_i128(i128 x) const {
        u128 ax = abs_u128(x);
        if (!in_post_init) {
            if (ax > max_abs_init) max_abs_init = ax;
        } else {
            if (ax > max_abs_post) max_abs_post = ax;
        }
    }
    inline i128 sadd(i128 x, i128 y) const {
        track_i128(x); track_i128(y);
        i128 r;
        if (__builtin_add_overflow(x, y, &r)) {
            std::cerr << "FATAL: __int128 addition overflow!\n";
            std::abort();
        }
        track_i128(r);
        return r;
    }
    inline i128 ssub(i128 x, i128 y) const {
        track_i128(x); track_i128(y);
        i128 r;
        if (__builtin_sub_overflow(x, y, &r)) {
            std::cerr << "FATAL: __int128 subtraction overflow!\n";
            std::abort();
        }
        track_i128(r);
        return r;
    }
    inline i128 smul(i128 x, i128 y) const {
        track_i128(x); track_i128(y);
        i128 r;
        if (__builtin_mul_overflow(x, y, &r)) {
            std::cerr << "FATAL: __int128 multiplication overflow!\n";
            std::abort();
        }
        track_i128(r);
        return r;
    }
    inline i128 sneg(i128 x) const {
        return ssub((i128)0, x);
    }

    struct Pt {
        i128 x = 0, y = 0;
        int p = 0;
        bool operator==(const Pt& o) const { return p == o.p && x == o.x && y == o.y; }
        bool operator!=(const Pt& o) const { return !(*this == o); }
        bool operator<(const Pt& o) const {
            if (p != o.p) return p < o.p;
            if (x != o.x) return x < o.x;
            return y < o.y;
        }
    };

    struct Dir {
        int k = 0, s = 1;
        bool operator==(const Dir& o) const { return k == o.k && s == o.s; }
        bool operator!=(const Dir& o) const { return !(*this == o); }
        Dir rev() const { return {k, -s}; }
        Dir add_alpha() const { return {k - 2, -s}; }
        Dir add_beta()  const { return {k + 3, -s}; }
        Dir add_gamma() const { return {k - 1, -s}; }
    };

    Pt ZPOW[KMAX];
    std::vector<uint8_t> in_sg;
    i64 max_side = 0;

    struct Tri {
        Pt p[3];
        Dir ed[3];
        i64 len[3];
    };
    Tri tgt;

    Pt norm_pt(Pt r) const {
        if (r.x == 0 && r.y == 0) { r.p = 0; return r; }
        if (r.p < 0 || r.p > MAX_P) { std::cerr << "FAIL: p out of range (" << r.p << ")\n"; std::exit(2); }
        while (r.p > 0 && (r.x % f == 0) && (r.y % f == 0)) { r.x /= f; r.y /= f; r.p--; }
        if (r.p > max_p_seen) max_p_seen = r.p;
        track_i128(r.x);
        track_i128(r.y);
        return r;
    }
    Pt pt_add(const Pt& u, const Pt& v) const {
        Pt r;
        if (u.p == v.p) {
            r = {sadd(u.x, v.x), sadd(u.y, v.y), u.p};
        } else if (u.p < v.p) {
            int dp = v.p - u.p;
            i128 m = get_pow_f(dp);
            r = {sadd(smul(u.x, m), v.x), sadd(smul(u.y, m), v.y), v.p};
        } else {
            int dp = u.p - v.p;
            i128 m = get_pow_f(dp);
            r = {sadd(u.x, smul(v.x, m)), sadd(u.y, smul(v.y, m)), u.p};
        }
        return norm_pt(r);
    }
    Pt pt_sub(const Pt& u, const Pt& v) const { return pt_add(u, {sneg(v.x), sneg(v.y), v.p}); }
    Pt pt_scale(const Pt& u, i64 sc) const {
        return norm_pt({smul(u.x, (i128)sc), smul(u.y, (i128)sc), u.p});
    }

    Pt dir_vec(const Dir& d) const {
        if (d.k + KOFF < 0 || d.k + KOFF >= KMAX || (d.s != 1 && d.s != -1)) {
            std::cerr << "FAIL: dir out of range (k=" << d.k << ", s=" << d.s << ")\n";
            std::exit(2);
        }
        Pt v = ZPOW[d.k + KOFF];
        if (d.s < 0) { v.x = sneg(v.x); v.y = sneg(v.y); }
        return v;
    }

    // Exact cross sign of two vectors u, v in Q[zeta] (ZERO floats!)
    int vec_cross_sign(const Pt& u, const Pt& v) const {
        int pm = std::max(u.p, v.p);
        i128 mu = get_pow_f(pm - u.p), mv = get_pow_f(pm - v.p);
        i128 p1 = smul(smul(u.x, mu), smul(v.y, mv));
        i128 p2 = smul(smul(u.y, mu), smul(v.x, mv));
        return (p1 > p2) ? 1 : ((p1 < p2) ? -1 : 0);
    }

    int orient(const Pt& p0, const Pt& p1, const Pt& p2) const {
        int pm = std::max({p0.p, p1.p, p2.p});
        i128 m0 = get_pow_f(pm - p0.p), m1 = get_pow_f(pm - p1.p), m2 = get_pow_f(pm - p2.p);
        i128 dx1 = ssub(smul(p1.x, m1), smul(p0.x, m0));
        i128 dy1 = ssub(smul(p1.y, m1), smul(p0.y, m0));
        i128 dx2 = ssub(smul(p2.x, m2), smul(p0.x, m0));
        i128 dy2 = ssub(smul(p2.y, m2), smul(p0.y, m0));
        i128 q1 = smul(dx1, dy2), q2 = smul(dy1, dx2);
        return (q1 > q2) ? 1 : ((q1 < q2) ? -1 : 0);
    }

    // Exact squared norm check: |u|^2 == L^2 where |x + y*z|^2 = x^2 + y^2 + (e/f)*x*y
    bool check_norm_eq(const Pt& u, i64 L) const {
        // (u.x^2 + u.y^2)*f + e*u.x*u.y == L^2 * f^(2*u.p + 1)
        i128 xx = smul(u.x, u.x);
        i128 yy = smul(u.y, u.y);
        i128 xy = smul(u.x, u.y);
        i128 lhs = sadd(smul(sadd(xx, yy), (i128)f), smul((i128)e, xy));
        i128 rhs = smul(smul((i128)L, (i128)L), get_pow_f(2 * u.p + 1));
        return lhs == rhs;
    }

    int dir_cross(const Dir& d1, const Dir& d2) const {
        return vec_cross_sign(dir_vec(d1), dir_vec(d2));
    }

    // Exact ZERO-FLOAT cyclic comparator for directions in [0, 2*pi) relative to +x = (1, 0)!
    bool dir_less_exact(const Dir& d1, const Dir& d2) const {
        if (d1 == d2) return false;
        Pt v1 = dir_vec(d1), v2 = dir_vec(d2);
        int h1 = (v1.y > 0 || (v1.y == 0 && v1.x > 0)) ? 0 : 1;
        int h2 = (v2.y > 0 || (v2.y == 0 && v2.x > 0)) ? 0 : 1;
        if (h1 != h2) return h1 < h2;
        return vec_cross_sign(v1, v2) > 0;
    }

    bool dir_strictly_between(const Dir& d1, const Dir& d2, const Dir& d) const {
        if (d == d1 || d == d2) return false;
        int c12 = dir_cross(d1, d2), c1d = dir_cross(d1, d), cd2 = dir_cross(d, d2);
        if (c12 > 0) return c1d > 0 && cd2 > 0;
        if (c12 < 0) return c1d > 0 || cd2 > 0;
        return c1d > 0;
    }

    // ZERO-FLOAT exact (A, B) computation for CCW angle from d1 to d2 in (0, 2*pi)!
    void exact_ccw_ab_nofloat(const Dir& d1, const Dir& d2, int& outA, int& outB) const {
        if (d1 == d2) { outA = 0; outB = 0; return; }
        int dk = d2.k - d1.k;
        if (dk == 0) { outA = 3; outB = 2; return; } // exact pi!
        auto half = [&](const Dir& d) -> int {
            Pt v = dir_vec(d);
            return (v.y > 0 || (v.y == 0 && v.x > 0)) ? 0 : 1;
        };
        int wraps = 0;
        Dir cur{0, 1};
        if (dk > 0) {
            for (int i = 0; i < dk; i++) {
                Dir nxt{cur.k + 1, 1};
                if (half(cur) == 1 && half(nxt) == 0) wraps++;
                cur = nxt;
            }
        } else {
            for (int i = 0; i < -dk; i++) {
                Dir nxt{cur.k - 1, 1};
                if (half(cur) == 0 && half(nxt) == 1) wraps--;
                cur = nxt;
            }
        }
        int n = -2 * wraps;
        if (d1.s != d2.s) {
            if (half(cur) == 0) n += 1;
            else n -= 1;
        }
        int cs = dir_cross(d1, d2);
        Dir rel{dk, (d1.s == d2.s) ? 1 : -1};
        assert((cs > 0) == (half(rel) == 0));
        outA = 3 * n + dk;
        outB = 2 * n + dk;
    }

    void init(int e_, int f_, int M_) {
        if (e_ <= 0 || f_ <= e_ || M_ < 1 || std::gcd(e_, f_) != 1) {
            std::cerr << "FAIL: invalid target parameters (e=" << e_ << ", f=" << f_ << ", M=" << M_ << ")\n";
            std::exit(2);
        }
        e = e_; f = f_; M = M_;
        in_post_init = false;
        max_abs_init = 0;
        max_abs_post = 0;
        max_p_seen = 0;

        i128 a128 = smul((i128)e, (i128)f);
        i128 b128 = ssub(smul((i128)f, (i128)f), smul((i128)e, (i128)e));
        i128 c128 = smul((i128)f, (i128)f);
        a = (i64)a128; b = (i64)b128; c = (i64)c128;

        POW_F[0] = 1;
        max_pow_f = 0;
        track_i128(POW_F[0]);
        for (int i = 1; i <= MAX_POW; i++) {
            if (POW_F[i - 1] > I128_MAX_VAL / (i128)f) break;
            POW_F[i] = smul(POW_F[i - 1], (i128)f);
            max_pow_f = i;
        }

        ZPOW[KOFF] = {1, 0, 0};
        track_i128(1);
        for (int k = 1; k <= KOFF; k++) {
            Pt prev = ZPOW[KOFF + k - 1];
            i128 nx = sneg(smul(prev.y, (i128)f));
            i128 ny = sadd(smul(prev.x, (i128)f), smul(prev.y, (i128)e));
            ZPOW[KOFF + k] = norm_pt({nx, ny, prev.p + 1});
        }
        for (int k = 1; k <= KOFF; k++) {
            Pt prev = ZPOW[KOFF - k + 1];
            i128 nx = sadd(smul(prev.x, (i128)e), smul(prev.y, (i128)f));
            i128 ny = sneg(smul(prev.x, (i128)f));
            ZPOW[KOFF - k] = norm_pt({nx, ny, prev.p + 1});
        }

        // Build target T_M(e, f) and verify its exact side lengths & Q[zeta] edge vectors!
        i128 leg128 = smul((i128)M, smul(c128, (i128)f));
        i128 base128 = smul(smul((i128)M, (i128)e), ssub(smul((i128)3, c128), smul((i128)e, (i128)e)));
        assert(leg128 > 0 && leg128 <= INT64_MAX && base128 > 0 && base128 <= INT64_MAX);
        i64 leg = (i64)leg128;
        i64 base = (i64)base128;

        tgt.p[0] = {0, 0, 0};
        tgt.ed[0] = {0, 1}; tgt.ed[1] = {-3, 1}; tgt.ed[2] = {-6, 1};
        tgt.p[1] = pt_scale(dir_vec(tgt.ed[0]), leg);
        tgt.p[2] = pt_scale(dir_vec(tgt.ed[2].rev()), leg);
        tgt.len[0] = leg; tgt.len[1] = base; tgt.len[2] = leg;
        assert(check_norm_eq(pt_sub(tgt.p[1], tgt.p[0]), leg));
        assert(check_norm_eq(pt_sub(tgt.p[2], tgt.p[1]), base));
        assert(check_norm_eq(pt_sub(tgt.p[0], tgt.p[2]), leg));
        assert(pt_sub(tgt.p[1], tgt.p[0]) == pt_scale(dir_vec(tgt.ed[0]), leg));
        assert(pt_sub(tgt.p[2], tgt.p[1]) == pt_scale(dir_vec(tgt.ed[1]), base));
        assert(pt_sub(tgt.p[0], tgt.p[2]) == pt_scale(dir_vec(tgt.ed[2]), leg));
        assert(orient(tgt.p[0], tgt.p[1], tgt.p[2]) > 0);

        // Explicitly assert all 6 tile slots' d12 vectors against exact Q[zeta] algebra at startup!
        for (int slot = 0; slot < 6; slot++) {
            Tri t = make_tile_verified(Pt{0, 0, 0}, Dir{0, 1}, slot);
            assert(pt_sub(t.p[2], t.p[1]) == pt_scale(dir_vec(t.ed[1]), t.len[1]));
        }

        max_side = std::max({leg, base});
        if (max_side < 0 || max_side > 100000000LL) {
            std::cerr << "FAIL: max_side out of bounds (" << max_side << ")\n";
            std::exit(2);
        }
        in_sg.assign((size_t)max_side + 1, 0);
        in_sg[0] = 1;
        for (i64 i = 0; i <= max_side; i++) {
            if (!in_sg[i]) continue;
            if (i + a <= max_side) in_sg[i + a] = 1;
            if (i + b <= max_side) in_sg[i + b] = 1;
            if (i + c <= max_side) in_sg[i + c] = 1;
        }

        // Reset p-watermark and switch to post-init i128 watermark tracking
        max_p_seen = 0;
        in_post_init = true;
    }

    Tri make_tile_verified(const Pt& v, const Dir& d, int slot) const {
        Tri t; i64 l1 = 0, l2 = 0, l3 = 0; Dir d2, d12;
        switch (slot) {
            case 0: l1 = a; l2 = c; l3 = b; d2 = d.add_beta();  d12 = {d.k + 1, d.s}; break;
            case 1: l1 = c; l2 = a; l3 = b; d2 = d.add_beta();  d12 = {d.k + 2, d.s}; break;
            case 2: l1 = b; l2 = c; l3 = a; d2 = d.add_alpha(); d12 = {d.k + 1, d.s}; break;
            case 3: l1 = c; l2 = b; l3 = a; d2 = d.add_alpha(); d12 = {d.k - 3, d.s}; break;
            case 4: l1 = a; l2 = b; l3 = c; d2 = d.add_gamma(); d12 = {d.k - 3, d.s}; break;
            case 5: l1 = b; l2 = a; l3 = c; d2 = d.add_gamma(); d12 = {d.k + 2, d.s}; break;
            default: std::cerr << "FAIL: invalid slot " << slot << "\n"; std::exit(2);
        }
        t.p[0] = v;
        t.p[1] = pt_add(v, pt_scale(dir_vec(d), l1));
        t.p[2] = pt_add(v, pt_scale(dir_vec(d2), l2));
        t.ed[0] = d; t.ed[1] = d12; t.ed[2] = d2.rev();
        t.len[0] = l1; t.len[1] = l3; t.len[2] = l2;
        // Verify exact SSS congruence, CCW orientation, and all 3 exact Q[zeta] edge vectors (incl. d12)!
        assert(orient(t.p[0], t.p[1], t.p[2]) > 0);
        assert(check_norm_eq(pt_sub(t.p[1], t.p[0]), l1));
        assert(check_norm_eq(pt_sub(t.p[2], t.p[1]), l3));
        assert(check_norm_eq(pt_sub(t.p[0], t.p[2]), l2));
        assert(pt_sub(t.p[1], t.p[0]) == pt_scale(dir_vec(d), l1));
        assert(pt_sub(t.p[2], t.p[1]) == pt_scale(dir_vec(d12), l3));
        assert(pt_sub(t.p[0], t.p[2]) == pt_scale(dir_vec(d2.rev()), l2));
        return t;
    }

    // Reconstruct a Tri (with exact ed[] and len[]) from its 3 exact vertices!
    Tri tri_from_verts(Pt q0, Pt q1, Pt q2) const {
        int o = orient(q0, q1, q2);
        if (o == 0) { std::cerr << "FAIL: degenerate nogood tile\n"; std::exit(2); }
        if (o < 0) std::swap(q1, q2);
        Tri t; t.p[0] = q0; t.p[1] = q1; t.p[2] = q2;
        bool hasA = false, hasB = false, hasC = false;
        for (int i = 0; i < 3; i++) {
            Pt diff = pt_sub(t.p[(i + 1) % 3], t.p[i]);
            i64 L = 0;
            if (check_norm_eq(diff, a)) { L = a; hasA = true; }
            else if (check_norm_eq(diff, b)) { L = b; hasB = true; }
            else if (check_norm_eq(diff, c)) { L = c; hasC = true; }
            else { std::cerr << "FAIL: nogood tile not congruent to model!\n"; std::exit(2); }
            t.len[i] = L;
            bool found_d = false;
            for (int k = -KOFF; k <= KOFF && !found_d; k++) {
                for (int s : {1, -1}) {
                    Dir cand{k, s};
                    if (pt_scale(dir_vec(cand), L) == diff) { t.ed[i] = cand; found_d = true; break; }
                }
            }
            if (!found_d) { std::cerr << "FAIL: nogood tile edge direction not in zeta^k\n"; std::exit(2); }
        }
        if (!(hasA && hasB && hasC)) { std::cerr << "FAIL: nogood tile side multiset mismatch\n"; std::exit(2); }
        return t;
    }

    bool in_closed_tgt(const Pt& q) const {
        for (int i = 0; i < 3; i++) if (orient(tgt.p[i], tgt.p[(i + 1) % 3], q) < 0) return false;
        return true;
    }

    bool tris_overlap(const Tri& u, const Tri& v) const {
        for (int i = 0; i < 3; i++) {
            if (orient(u.p[i], u.p[(i + 1) % 3], v.p[0]) <= 0 &&
                orient(u.p[i], u.p[(i + 1) % 3], v.p[1]) <= 0 &&
                orient(u.p[i], u.p[(i + 1) % 3], v.p[2]) <= 0) return false;
        }
        for (int i = 0; i < 3; i++) {
            if (orient(v.p[i], v.p[(i + 1) % 3], u.p[0]) <= 0 &&
                orient(v.p[i], v.p[(i + 1) % 3], u.p[1]) <= 0 &&
                orient(v.p[i], v.p[(i + 1) % 3], u.p[2]) <= 0) return false;
        }
        return true;
    }

    struct FastRat {
        i128 num = 0, den = 1;
        bool less(const FastRat& o, const Verifier& V) const {
            return V.smul(num, o.den) < V.smul(o.num, den);
        }
        bool eq(const FastRat& o, const Verifier& V) const {
            return V.smul(num, o.den) == V.smul(o.num, den);
        }
        i64 int_diff(const FastRat& hi, i64 max_s, const Verifier& V) const {
            i128 dn = V.ssub(V.smul(hi.num, den), V.smul(num, hi.den));
            i128 dd = V.smul(hi.den, den);
            if (dn < 0) return -1;
            if (dn == 0) return 0;
            if (dn % dd != 0) return -1;
            i128 q = dn / dd;
            if (q > max_s) return -1;
            return (i64)q;
        }
    };
    FastRat line_param(const Pt& origin, const Pt& dv, const Pt& q) const {
        Pt diff = pt_sub(q, origin);
        FastRat r;
        if (dv.x != 0) {
            if (dv.p >= diff.p) {
                r.num = smul(diff.x, get_pow_f(dv.p - diff.p));
                r.den = dv.x;
            } else {
                r.num = diff.x;
                r.den = smul(dv.x, get_pow_f(diff.p - dv.p));
            }
        } else {
            if (dv.p >= diff.p) {
                r.num = smul(diff.y, get_pow_f(dv.p - diff.p));
                r.den = dv.y;
            } else {
                r.num = diff.y;
                r.den = smul(dv.y, get_pow_f(diff.p - dv.p));
            }
        }
        if (r.den < 0) { r.num = sneg(r.num); r.den = sneg(r.den); }
        track_i128(r.num);
        track_i128(r.den);
        return r;
    }

    bool verify_gap_leaf(int eidx, const std::vector<Tri>& C) const {
        if (eidx < 0 || eidx > 2) return false;
        const Pt& P0 = tgt.p[eidx]; const Pt& P1 = tgt.p[(eidx + 1) % 3];
        Pt dv = dir_vec(tgt.ed[eidx]);
        i64 L = tgt.len[eidx];
        struct Seg { FastRat a, b; };
        std::vector<Seg> segs;
        for (const auto& t : C) {
            int j1 = -1, j2 = -1;
            for (int j = 0; j < 3; j++) {
                if (orient(P0, P1, t.p[j]) == 0) { if (j1 < 0) j1 = j; else j2 = j; }
            }
            if (j1 < 0) continue;
            if (j2 < 0) { FastRat r = line_param(P0, dv, t.p[j1]); segs.push_back({r, r}); }
            else {
                FastRat r1 = line_param(P0, dv, t.p[j1]), r2 = line_param(P0, dv, t.p[j2]);
                if (r2.less(r1, *this)) std::swap(r1, r2);
                segs.push_back({r1, r2});
            }
        }
        if (segs.empty()) return false;
        std::sort(segs.begin(), segs.end(), [&](const Seg& u, const Seg& v) {
            if (!u.a.eq(v.a, *this)) return u.a.less(v.a, *this);
            return u.b.less(v.b, *this);
        });
        FastRat cur{0, 1};
        for (const auto& s : segs) {
            if (cur.less(s.a, *this)) {
                i64 g = cur.int_diff(s.a, max_side, *this);
                if (g < 0 || !in_sg[(size_t)g]) return true;
            }
            if (cur.less(s.b, *this)) cur = s.b;
        }
        FastRat endR{L, 1};
        if (cur.less(endR, *this)) {
            i64 g = cur.int_diff(endR, max_side, *this);
            if (g < 0 || !in_sg[(size_t)g]) return true;
        }
        return false;
    }

    struct FreeArc { Dir s, e; int A, B; };
    bool compute_free_arcs(const Pt& v, const std::vector<Tri>& C, std::vector<FreeArc>& farcs) const {
        struct Arc { Dir s, e; };
        std::vector<Arc> iv;
        for (int i = 0; i < 3; i++) {
            int o = orient(tgt.p[i], tgt.p[(i + 1) % 3], v);
            if (o < 0) return false;
            if (o == 0) iv.push_back({tgt.ed[i].rev(), tgt.ed[i]});
        }
        for (const auto& t : C) {
            int o0 = orient(t.p[0], t.p[1], v); if (o0 < 0) continue;
            int o1 = orient(t.p[1], t.p[2], v); if (o1 < 0) continue;
            int o2 = orient(t.p[2], t.p[0], v); if (o2 < 0) continue;
            if (o0 > 0 && o1 > 0 && o2 > 0) return false; // interior to a placed tile
            if (v == t.p[0]) iv.push_back({t.ed[0], t.ed[2].rev()});
            else if (v == t.p[1]) iv.push_back({t.ed[1], t.ed[0].rev()});
            else if (v == t.p[2]) iv.push_back({t.ed[2], t.ed[1].rev()});
            else if (o0 == 0) iv.push_back({t.ed[0], t.ed[0].rev()});
            else if (o1 == 0) iv.push_back({t.ed[1], t.ed[1].rev()});
            else if (o2 == 0) iv.push_back({t.ed[2], t.ed[2].rev()});
        }
        if (iv.empty()) return false;
        std::vector<Dir> marks;
        for (const auto& ar : iv) { marks.push_back(ar.s); marks.push_back(ar.e); }
        std::sort(marks.begin(), marks.end(), [&](const Dir& x, const Dir& y) { return dir_less_exact(x, y); });
        std::vector<Dir> u;
        for (const auto& d : marks) if (u.empty() || u.back() != d) u.push_back(d);
        int k = (int)u.size();
        std::vector<bool> free_sec(k, true);
        int start = -1;
        for (int i = 0; i < k; i++) {
            for (const auto& ar : iv) {
                if (u[i] == ar.s || dir_strictly_between(ar.s, ar.e, u[i])) { free_sec[i] = false; break; }
            }
            if (!free_sec[i] && start < 0) start = i;
        }
        if (start < 0) return false;
        farcs.clear();
        int i = 0;
        while (i < k) {
            int idx = (start + i) % k;
            if (free_sec[idx]) {
                Dir ds = u[idx]; int j = i;
                while (j < k && free_sec[(start + j) % k]) j++;
                Dir de = u[(start + j) % k];
                int A = 0, B = 0;
                exact_ccw_ab_nofloat(ds, de, A, B);
                farcs.push_back({ds, de, A, B});
                i = j;
            } else i++;
        }
        return true;
    }

    // Verify that (v, d) is an admissible pointed free corner, and compute its exact feasible slot mask!
    bool verify_pointed_corner(const Pt& v, const Dir& d, const std::vector<Tri>& C, int& out_feas_mask) const {
        std::vector<FreeArc> farcs;
        if (!compute_free_arcs(v, C, farcs)) return false;
        int fi = -1;
        for (int i = 0; i < (int)farcs.size(); i++) if (farcs[i].s == d) { fi = i; break; }
        if (fi < 0) return false;
        // Verify ALL free arcs lie in the open half-plane (d, d.rev())
        for (const auto& fb : farcs) {
            if (dir_cross(d, fb.e) <= 0) return false;
            if (fb.s != d && dir_cross(d, fb.s) <= 0) return false;
        }
        int faA = farcs[fi].A, faB = farcs[fi].B;
        out_feas_mask = 0;
        for (int slot = 0; slot < 6; slot++) {
            int dA = (slot <= 1) ? 0 : (slot <= 3 ? 1 : 2);
            int dB = (slot <= 1) ? 1 : (slot <= 3 ? 0 : 1);
            if (faA - dA < 0 || faB - dB < 0) continue;
            Tri cand = make_tile_verified(v, d, slot);
            if (!in_closed_tgt(cand.p[1]) || !in_closed_tgt(cand.p[2])) continue;
            bool ov = false;
            for (const auto& u : C) if (tris_overlap(u, cand)) { ov = true; break; }
            if (!ov) out_feas_mask |= (1 << slot);
        }
        return true;
    }

    bool verify_angle_leaf(const Pt& v, const Dir& d1, const Dir& d2, const std::vector<Tri>& C) const {
        std::vector<FreeArc> farcs;
        if (!compute_free_arcs(v, C, farcs)) return false;
        for (const auto& fa : farcs) {
            if (fa.s == d1 && fa.e == d2 && (fa.A < 0 || fa.B < 0)) return true;
        }
        return false;
    }

    struct CNode {
        char type = 0; // 'B', 'C', 'A', 'G', 'R', 'F'
        Pt v; Dir d, d2; int eidx = 0, ref_id = -1;
        int nkids = 0; int kslot[6] = {0}; int kchild[6] = {0};
    };

    struct TriKey {
        Pt p[3];
        bool operator==(const TriKey& o) const { return p[0] == o.p[0] && p[1] == o.p[1] && p[2] == o.p[2]; }
    };
    static TriKey tkey(const Tri& t) {
        TriKey k{t.p[0], t.p[1], t.p[2]};
        if (k.p[1] < k.p[0]) std::swap(k.p[0], k.p[1]);
        if (k.p[2] < k.p[1]) std::swap(k.p[1], k.p[2]);
        if (k.p[1] < k.p[0]) std::swap(k.p[0], k.p[1]);
        return k;
    }

    u64 verified_nodes = 0, verified_dag_nodes = 0, verified_prefix_nodes = 0,
        verified_branches = 0, verified_corner_leaves = 0,
        verified_angle_leaves = 0, verified_gap_leaves = 0, verified_ng_refs = 0, verified_ngs = 0;

    bool check_dag_node(int nid, const std::vector<CNode>& nodes,
                        const std::vector<std::vector<TriKey>>& ng_keys, int max_allowed_ng,
                        std::vector<Tri>& C) {
        if (nid < 0 || nid >= (int)nodes.size()) return false;
        const auto& nd = nodes[nid];
        verified_nodes++;
        verified_dag_nodes++;
        if (nd.type == 'G') {
            verified_gap_leaves++;
            return verify_gap_leaf(nd.eidx, C);
        } else if (nd.type == 'A') {
            verified_angle_leaves++;
            return verify_angle_leaf(nd.v, nd.d, nd.d2, C);
        } else if (nd.type == 'C') {
            verified_corner_leaves++;
            int fm = 0;
            if (!verify_pointed_corner(nd.v, nd.d, C, fm)) return false;
            return fm == 0;
        } else if (nd.type == 'R') {
            verified_ng_refs++;
            if (nd.ref_id < 0 || nd.ref_id >= max_allowed_ng) return false;
            for (const auto& rk : ng_keys[nd.ref_id]) {
                bool found = false;
                for (const auto& t : C) if (tkey(t) == rk) { found = true; break; }
                if (!found) return false;
            }
            return true;
        } else if (nd.type == 'B') {
            verified_branches++;
            if (nd.nkids < 0 || nd.nkids > 6) return false;
            int fm = 0;
            if (!verify_pointed_corner(nd.v, nd.d, C, fm)) return false;
            int covered = 0;
            for (int i = 0; i < nd.nkids; i++) {
                int sl = nd.kslot[i];
                if (sl < 0 || sl >= 6) return false;
                covered |= (1 << sl);
            }
            if ((fm & ~covered) != 0) return false;
            for (int i = 0; i < nd.nkids; i++) {
                int sl = nd.kslot[i];
                if (!(fm & (1 << sl))) continue;
                Tri cand = make_tile_verified(nd.v, nd.d, sl);
                C.push_back(cand);
                bool ok = check_dag_node(nd.kchild[i], nodes, ng_keys, max_allowed_ng, C);
                C.pop_back();
                if (!ok) return false;
            }
            return true;
        }
        return false;
    }

    bool verify_file(const std::string& path, int corrupt_mode = 0) {
        std::ifstream in(path);
        if (!in.good()) { std::cerr << "Cannot open " << path << "\n"; return false; }

        std::string hdr;
        int ce, cf, cM;
        if (!(in >> hdr >> ce >> cf >> cM) || hdr != "ECERT_V1") {
            std::cerr << "FAIL: bad header\n"; return false;
        }
        init(ce, cf, cM);
        i64 N_val = (i64)M * M * (3LL * f * f - (i64)e * e);
        std::cout << "Verifying ECERT_V1 for T_" << M << "(" << e << "," << f << ") N=" << N_val
                  << " (corrupt_mode=" << corrupt_mode << ")...\n" << std::flush;

        auto read_pt = [&](Pt& out) -> bool {
            std::string sx, sy; int p;
            if (!(in >> sx >> sy >> p)) return false;
            if (p < 0 || p > MAX_P) {
                std::cerr << "FAIL: input point p=" << p << " out of bounds [0," << MAX_P << "]\n";
                return false;
            }
            i128 x = 0, y = 0;
            if (!parse_i128_checked(sx, x) || !parse_i128_checked(sy, y)) {
                std::cerr << "FAIL: malformed i128 point coordinate\n";
                return false;
            }
            out = norm_pt({x, y, p});
            return true;
        };
        auto valid_dir = [&](const Dir& d) -> bool {
            return (d.s == 1 || d.s == -1) && (d.k + KOFF >= 0) && (d.k + KOFF < KMAX);
        };
        auto read_node = [&](CNode& nd) -> bool {
            if (!(in >> nd.type)) return false;
            if (nd.type == 'B') {
                if (!read_pt(nd.v)) return false;
                if (!(in >> nd.d.k >> nd.d.s >> nd.nkids)) return false;
                if (!valid_dir(nd.d)) { std::cerr << "FAIL: invalid B dir\n"; return false; }
                if (nd.nkids < 0 || nd.nkids > 6) {
                    std::cerr << "FAIL: invalid B nkids=" << nd.nkids << " (must be 0..6)\n";
                    return false;
                }
                for (int i = 0; i < nd.nkids; i++) {
                    if (!(in >> nd.kslot[i] >> nd.kchild[i])) return false;
                    if (nd.kslot[i] < 0 || nd.kslot[i] >= 6) {
                        std::cerr << "FAIL: invalid B kslot=" << nd.kslot[i] << "\n";
                        return false;
                    }
                }
            } else if (nd.type == 'C') {
                if (!read_pt(nd.v) || !(in >> nd.d.k >> nd.d.s)) return false;
                if (!valid_dir(nd.d)) { std::cerr << "FAIL: invalid C dir\n"; return false; }
            } else if (nd.type == 'A') {
                if (!read_pt(nd.v) || !(in >> nd.d.k >> nd.d.s >> nd.d2.k >> nd.d2.s)) return false;
                if (!valid_dir(nd.d) || !valid_dir(nd.d2)) { std::cerr << "FAIL: invalid A dir\n"; return false; }
            } else if (nd.type == 'G') {
                if (!(in >> nd.eidx)) return false;
                if (nd.eidx < 0 || nd.eidx > 2) { std::cerr << "FAIL: invalid G eidx=" << nd.eidx << "\n"; return false; }
            } else if (nd.type == 'R' || nd.type == 'F') {
                if (!(in >> nd.ref_id)) return false;
                if (nd.ref_id < 0) { std::cerr << "FAIL: negative ref_id=" << nd.ref_id << "\n"; return false; }
            } else {
                std::cerr << "FAIL: unknown node type '" << nd.type << "'\n";
                return false;
            }
            return true;
        };

        bool seen_apex[2][2] = {{false, false}, {false, false}};
        bool saw_end = false;
        std::string tok;
        while (in >> tok) {
            if (tok == "END") { saw_end = true; break; }
            if (tok != "APEX") { std::cerr << "FAIL: expected APEX, got " << tok << "\n"; return false; }
            int s1, s2, s3, npt, proot, nf;
            if (!(in >> s1 >> s2 >> s3 >> npt >> proot >> nf)) {
                std::cerr << "FAIL: malformed APEX header\n"; return false;
            }
            if ((s1 != 2 && s1 != 3) || s2 != 2 || (s3 != 2 && s3 != 3)) {
                std::cerr << "FAIL: invalid apex triple\n"; return false;
            }
            if (corrupt_mode == 5 && s1 == 3 && s2 == 2 && s3 == 3) {
                std::cerr << "  [corrupt_mode=5] Dropping Apex 4/4 (" << s1 << "," << s2 << "," << s3 << ")!\n";
                break;
            }
            if (seen_apex[s1 - 2][s3 - 2]) {
                std::cerr << "FAIL: duplicate apex triple (" << s1 << "," << s2 << "," << s3 << ")\n";
                return false;
            }
            seen_apex[s1 - 2][s3 - 2] = true;

            if (npt <= 0 || proot < 0 || proot >= npt || nf < 0) {
                std::cerr << "FAIL: invalid APEX bounds (npt=" << npt << ", proot=" << proot << ", nf=" << nf << ")\n";
                return false;
            }

            std::vector<CNode> ptree(npt);
            for (int i = 0; i < npt; i++) {
                if (!read_node(ptree[i])) return false;
            }

            struct Sub {
                int root_id;
                std::vector<Tri> ktris;
                std::vector<TriKey> kkeys;
                std::vector<CNode> nodes;
                std::vector<int> ng_root;
                std::vector<std::vector<int>> ng_tids;
            };
            std::vector<Sub> subs(nf);
            for (int fi = 0; fi < nf; fi++) {
                std::string st; int ntk, nnd, nng, sroot;
                if (!(in >> st >> ntk >> nnd >> nng >> sroot) || st != "SUBPROOF") {
                    std::cerr << "FAIL: expected SUBPROOF\n"; return false;
                }
                if (ntk < 0 || nnd <= 0 || nng < 0 || sroot < 0 || sroot >= nnd) {
                    std::cerr << "FAIL: invalid SUBPROOF bounds\n"; return false;
                }
                Sub& sb = subs[fi];
                sb.root_id = sroot;
                sb.ktris.reserve(ntk); sb.kkeys.reserve(ntk);
                for (int i = 0; i < ntk; i++) {
                    char kc;
                    if (!(in >> kc) || kc != 'K') { std::cerr << "FAIL: expected K\n"; return false; }
                    Pt q0, q1, q2;
                    if (!read_pt(q0) || !read_pt(q1) || !read_pt(q2)) return false;
                    Tri tr = tri_from_verts(q0, q1, q2);
                    sb.ktris.push_back(tr);
                    sb.kkeys.push_back(tkey(tr));
                }
                sb.nodes.resize(nnd);
                for (int i = 0; i < nnd; i++) {
                    if (!read_node(sb.nodes[i])) return false;
                }
                sb.ng_root.resize(nng);
                sb.ng_tids.resize(nng);
                for (int i = 0; i < nng; i++) {
                    char nc; int r, nt;
                    if (!(in >> nc >> r >> nt) || nc != 'N') { std::cerr << "FAIL: expected N\n"; return false; }
                    if (r < 0 || r >= nnd || nt < 0) {
                        std::cerr << "FAIL: invalid N bounds (r=" << r << ", nt=" << nt << ", nnd=" << nnd << ")\n";
                        return false;
                    }
                    sb.ng_root[i] = r;
                    sb.ng_tids[i].resize(nt);
                    for (int j = 0; j < nt; j++) {
                        int tid = -1;
                        if (!(in >> tid)) return false;
                        if (tid < 0 || tid >= ntk) {
                            std::cerr << "FAIL: nogood tid=" << tid << " out of bounds [0," << ntk << ")\n";
                            return false;
                        }
                        sb.ng_tids[i][j] = tid;
                    }
                }
            }

            // Negative-control corruption modes (1..4; mode 5 handled above)
            if (corrupt_mode == 1 && nf > 0 && !subs[0].nodes.empty()) {
                for (auto& nd : subs[0].nodes) {
                    if (nd.type == 'B' && nd.nkids > 0) { nd.nkids--; break; }
                }
            } else if (corrupt_mode == 2 && nf > 0) {
                for (auto& nd : subs[0].nodes) {
                    if (nd.type == 'C') { nd.type = 'G'; nd.eidx = 1; break; }
                }
            } else if (corrupt_mode == 3) {
                for (auto& nd : ptree) {
                    if (nd.type == 'B' && nd.nkids > 0) { nd.nkids--; break; }
                }
            } else if (corrupt_mode == 4) {
                for (int fi = 0; fi < nf; fi++) {
                    if (!subs[fi].ng_root.empty()) {
                        int r0 = subs[fi].ng_root[0];
                        subs[fi].nodes[r0].type = 'R';
                        subs[fi].nodes[r0].ref_id = 0; // cyclic self-ref on nogood 0!
                        break;
                    }
                }
            }

            // Verify every subproof's nogoods in strict topological order (0 .. nng-1)
            std::vector<std::vector<std::vector<TriKey>>> all_ng_keys(nf);
            for (int fi = 0; fi < nf; fi++) {
                const Sub& sb = subs[fi];
                all_ng_keys[fi].resize(sb.ng_root.size());
                for (int g = 0; g < (int)sb.ng_root.size(); g++) {
                    std::vector<Tri> ngC;
                    ngC.reserve(sb.ng_tids[g].size());
                    for (int tid : sb.ng_tids[g]) {
                        if (tid < 0 || tid >= (int)sb.ktris.size()) {
                            std::cerr << "FAIL: tid out of bounds\n"; return false;
                        }
                        ngC.push_back(sb.ktris[tid]);
                        all_ng_keys[fi][g].push_back(sb.kkeys[tid]);
                    }
                    if (!check_dag_node(sb.ng_root[g], sb.nodes, all_ng_keys[fi], g, ngC)) {
                        std::cerr << "FAIL: nogood " << g << " failed in subproof " << fi << "\n";
                        return false;
                    }
                    verified_ngs++;
                }
            }

            // Verify prefix tree starting from the 3 exact apex tiles (s1, s2, s3)
            Pt O = tgt.p[0];
            Dir d0{0, 1}, d1 = d0.add_alpha(), d2 = d1.add_alpha();
            std::vector<Tri> C = {
                make_tile_verified(O, d0, s1),
                make_tile_verified(O, d1, s2),
                make_tile_verified(O, d2, s3)
            };

            std::function<bool(int)> check_pref = [&](int pid) -> bool {
                if (pid < 0 || pid >= (int)ptree.size()) return false;
                const auto& nd = ptree[pid];
                if (nd.type == 'F') {
                    int fi = nd.ref_id;
                    if (fi < 0 || fi >= nf) return false;
                    return check_dag_node(subs[fi].root_id, subs[fi].nodes, all_ng_keys[fi], (int)subs[fi].ng_root.size(), C);
                }
                verified_nodes++;
                verified_prefix_nodes++;
                if (nd.type == 'G') {
                    verified_gap_leaves++; return verify_gap_leaf(nd.eidx, C);
                } else if (nd.type == 'A') {
                    verified_angle_leaves++; return verify_angle_leaf(nd.v, nd.d, nd.d2, C);
                } else if (nd.type == 'C') {
                    verified_corner_leaves++; int fm = 0;
                    return verify_pointed_corner(nd.v, nd.d, C, fm) && fm == 0;
                } else if (nd.type == 'B') {
                    verified_branches++;
                    if (nd.nkids < 0 || nd.nkids > 6) return false;
                    int fm = 0;
                    if (!verify_pointed_corner(nd.v, nd.d, C, fm)) return false;
                    int cov = 0;
                    for (int i = 0; i < nd.nkids; i++) {
                        int sl = nd.kslot[i];
                        if (sl < 0 || sl >= 6) return false;
                        cov |= (1 << sl);
                    }
                    if ((fm & ~cov) != 0) return false;
                    for (int i = 0; i < nd.nkids; i++) {
                        int sl = nd.kslot[i];
                        if (!(fm & (1 << sl))) continue;
                        C.push_back(make_tile_verified(nd.v, nd.d, sl));
                        bool ok = check_pref(nd.kchild[i]);
                        C.pop_back();
                        if (!ok) return false;
                    }
                    return true;
                }
                return false;
            };

            if (!check_pref(proot)) {
                std::cerr << "FAIL: prefix/subproof failed for apex (" << s1 << "," << s2 << "," << s3 << ")\n";
                return false;
            }
            std::cout << "  Apex (" << s1 << "," << s2 << "," << s3 << "): 100% VERIFIED (subproofs=" << nf << ")\n" << std::flush;
        }

        for (int i = 0; i < 2; i++) for (int j = 0; j < 2; j++) {
            if (!seen_apex[i][j]) {
                std::cerr << "FAIL: missing apex case (" << (i+2) << ",2," << (j+2) << ")\n";
                return false;
            }
        }
        if (!saw_end) {
            std::cerr << "FAIL: missing END sentinel\n";
            return false;
        }

        double init_pct = 100.0 * ((double)max_abs_init / (double)I128_MAX_VAL);
        double post_ratio = (double)max_abs_post / (double)I128_MAX_VAL;

        std::cout << ">>> 100% INDEPENDENT EXACT VERIFICATION PASSED! <<<\n"
                  << "  Target: T_" << M << "(" << e << "," << f << ") [N=" << N_val << "]\n"
                  << "  Verified nodes=" << verified_nodes
                  << " (dag=" << verified_dag_nodes << ", prefix_nonF=" << verified_prefix_nodes
                  << "; branches=" << verified_branches
                  << ", corner_leaves=" << verified_corner_leaves
                  << ", angle_leaves=" << verified_angle_leaves
                  << ", gap_leaves=" << verified_gap_leaves
                  << ", ng_refs=" << verified_ng_refs << ")\n"
                  << "  Verified nogoods=" << verified_ngs << "\n"
                  << "  __int128 overflows=0, max_p=" << max_p_seen << "\n"
                  << "  __int128 headroom: init_peak=" << u128_to_str(max_abs_init)
                  << " (" << std::fixed << std::setprecision(2) << init_pct << "% of INT128_MAX)"
                  << ", post_init_peak=" << u128_to_str(max_abs_post)
                  << " (" << std::scientific << std::setprecision(2) << post_ratio << " of INT128_MAX)\n"
                  << std::defaultfloat << std::setprecision(6);
        return true;
    }
};

int main(int argc, char** argv) {
    if (argc < 2) {
        std::cerr << "Usage: verify_ecert <cert.ecert> [corrupt_mode=0|1|2|3|4|5]\n";
        return 1;
    }
    int corrupt = (argc > 2) ? std::atoi(argv[2]) : 0;
    auto t0 = std::chrono::steady_clock::now();
    Verifier V;
    bool ok = V.verify_file(argv[1], corrupt);
    double sec = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    std::cout << "  Elapsed: " << sec << "s\n";
    return ok ? 0 : 1;
}
