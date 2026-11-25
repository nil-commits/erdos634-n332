// exact_tiler_lowmem.cpp
// Low-Memory, Disk-Spilling 32-Thread Exact-Arithmetic Q[zeta] Proof-DAG Generator!
// Identical ECERT_V1 output format (100% verifiable by verify_ecert.cpp & verify_ecert.py),
// but spills every solved subproof immediately to disk and caps per-thread nogood memory,
// keeping total RAM < 2-3 GB even on 50M-call apex cases!

#include <algorithm>
#include <array>
#include <atomic>
#include <cassert>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <functional>
#include <iostream>
#include <numeric>
#include <omp.h>
#include <sstream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using u32 = uint32_t;
using i64 = int64_t;
using u64 = uint64_t;
using i128 = __int128_t;
using u128 = __uint128_t;
static constexpr double PI = 3.1415926535897932384626433832795;

static std::string i128_to_str(i128 v) {
    if (v == 0) return "0";
    bool neg = v < 0;
    u128 u = neg ? (u128)(-v) : (u128)v;
    std::string s;
    while (u > 0) { s.push_back((char)('0' + (int)(u % 10))); u /= 10; }
    if (neg) s.push_back('-');
    std::reverse(s.begin(), s.end());
    return s;
}

static int G_E = 0, G_F = 0;
static i64 G_A = 0, G_B = 0, G_C = 0;
static double G_PHI = 0.0, G_COS_PHI = 0.0, G_SIN_PHI = 0.0;
static double G_ALPHA = 0.0, G_BETA = 0.0, G_GAMMA = 0.0;

static constexpr int MAX_P = 28;
static i128 POW_F[MAX_P + 1];
static double INV_POW_F[MAX_P + 1];
static constexpr int KOFF = 24;
static constexpr int KMAX = 49;

struct Pt {
    i128 x = 0, y = 0;
    int p = 0;
    double rx = 0.0, ry = 0.0;

    inline void compute_approx() {
        double inv = INV_POW_F[p];
        double fx = (double)x * inv, fy = (double)y * inv;
        rx = fx + fy * G_COS_PHI; ry = fy * G_SIN_PHI;
    }
    inline void normalize() {
        if (x == 0 && y == 0) { p = 0; rx = 0.0; ry = 0.0; return; }
        while (p > 0 && (x % G_F == 0) && (y % G_F == 0)) { x /= G_F; y /= G_F; p--; }
        if (p > MAX_P) { std::cerr << "FATAL: p=" << p << " > MAX_P=" << MAX_P << "\n"; std::exit(2); }
        compute_approx();
    }
    inline bool operator==(const Pt& o) const { return p == o.p && x == o.x && y == o.y; }
    inline bool operator<(const Pt& o) const {
        if (p != o.p) return p < o.p;
        if (x != o.x) return x < o.x;
        return y < o.y;
    }
};

static Pt ZPOW[KMAX];
static double ZANG[KMAX][2];
static int8_t DCROSS[KMAX][2][KMAX][2];
static int8_t DCCW_A[KMAX][2][KMAX][2];
static int8_t DCCW_B[KMAX][2][KMAX][2];

static inline Pt pt_add(const Pt& a, const Pt& b) {
    Pt r;
    if (a.p == b.p) { r.x = a.x + b.x; r.y = a.y + b.y; r.p = a.p; }
    else if (a.p < b.p) { i128 m = POW_F[b.p - a.p]; r.x = a.x * m + b.x; r.y = a.y * m + b.y; r.p = b.p; }
    else { i128 m = POW_F[a.p - b.p]; r.x = a.x + b.x * m; r.y = a.y + b.y * m; r.p = a.p; }
    r.normalize(); return r;
}
static inline Pt pt_sub(const Pt& a, const Pt& b) { Pt nb = b; nb.x = -nb.x; nb.y = -nb.y; return pt_add(a, nb); }
static inline Pt pt_scale(const Pt& a, i64 s) { Pt r{a.x * s, a.y * s, a.p}; r.normalize(); return r; }

static inline int orient_exact(const Pt& a, const Pt& b, const Pt& c) {
    int pm = std::max({a.p, b.p, c.p});
    i128 ma = POW_F[pm - a.p], mb = POW_F[pm - b.p], mc = POW_F[pm - c.p];
    i128 dx1 = b.x * mb - a.x * ma, dy1 = b.y * mb - a.y * ma;
    i128 dx2 = c.x * mc - a.x * ma, dy2 = c.y * mc - a.y * ma;
    i128 p1 = dx1 * dy2, p2 = dy1 * dx2;
    return (p1 > p2) ? 1 : ((p1 < p2) ? -1 : 0);
}

struct Dir {
    int16_t k = 0; int8_t s = 1;
    inline int si() const { return s > 0 ? 0 : 1; }
    inline int ki() const { return (int)k + KOFF; }
    inline bool operator==(const Dir& o) const { return k == o.k && s == o.s; }
    inline bool operator!=(const Dir& o) const { return !(*this == o); }
    inline Dir rev() const { return Dir{k, (int8_t)(-s)}; }
    inline Dir add_alpha() const { return Dir{(int16_t)(k - 2), (int8_t)(-s)}; }
    inline Dir add_beta()  const { return Dir{(int16_t)(k + 3), (int8_t)(-s)}; }
    inline Dir add_gamma() const { return Dir{(int16_t)(k - 1), (int8_t)(-s)}; }
    inline Pt vec() const {
        if (k + KOFF < 0 || k + KOFF >= KMAX) { std::cerr << "FATAL: k=" << k << " out of KMAX\n"; std::exit(3); }
        Pt v = ZPOW[k + KOFF];
        if (s < 0) { v.x = -v.x; v.y = -v.y; v.rx = -v.rx; v.ry = -v.ry; }
        return v;
    }
    inline double ang() const { return ZANG[k + KOFF][si()]; }
};

static inline int dir_cross_sign(const Dir& d1, const Dir& d2) { return DCROSS[d1.ki()][d1.si()][d2.ki()][d2.si()]; }
static inline void exact_ccw_ab(const Dir& d1, const Dir& d2, int& A, int& B) {
    A = DCCW_A[d1.ki()][d1.si()][d2.ki()][d2.si()];
    B = DCCW_B[d1.ki()][d1.si()][d2.ki()][d2.si()];
}
static inline bool dir_strictly_between(const Dir& d1, const Dir& d2, const Dir& d) {
    if (d == d1 || d == d2) return false;
    int c12 = dir_cross_sign(d1, d2), c1d = dir_cross_sign(d1, d), cd2 = dir_cross_sign(d, d2);
    if (c12 > 0) return c1d > 0 && cd2 > 0;
    if (c12 < 0) return c1d > 0 || cd2 > 0;
    return c1d > 0;
}

static void init_tables(int e, int f) {
    G_E = e; G_F = f;
    G_A = (i64)e * f; G_B = (i64)f * f - (i64)e * e; G_C = (i64)f * f;
    G_COS_PHI = (double)e / (2.0 * f);
    G_SIN_PHI = std::sqrt(4.0 * f * f - (double)e * e) / (2.0 * f);
    G_PHI = std::acos(G_COS_PHI);
    G_ALPHA = PI - 2.0 * G_PHI; G_BETA = 3.0 * G_PHI - PI; G_GAMMA = PI - G_PHI;

    POW_F[0] = 1; INV_POW_F[0] = 1.0;
    for (int i = 1; i <= MAX_P; i++) { POW_F[i] = POW_F[i - 1] * f; INV_POW_F[i] = 1.0 / (double)POW_F[i]; }
    ZPOW[KOFF] = Pt{1, 0, 0}; ZPOW[KOFF].compute_approx();
    for (int k = 1; k <= KOFF; k++) {
        Pt prev = ZPOW[KOFF + k - 1];
        Pt cur{-prev.y * f, prev.x * f + prev.y * e, prev.p + 1}; cur.normalize(); ZPOW[KOFF + k] = cur;
    }
    for (int k = 1; k <= KOFF; k++) {
        Pt prev = ZPOW[KOFF - k + 1];
        Pt cur{prev.x * e + prev.y * f, -prev.x * f, prev.p + 1}; cur.normalize(); ZPOW[KOFF - k] = cur;
    }
    for (int i = 0; i < KMAX; i++) {
        int k = i - KOFF;
        for (int si = 0; si < 2; si++) {
            double a = std::fmod(k * G_PHI + (si ? PI : 0.0), 2.0 * PI);
            if (a < 0.0) a += 2.0 * PI;
            ZANG[i][si] = a;
        }
    }
    for (int i1 = 0; i1 < KMAX; i1++) for (int s1 = 0; s1 < 2; s1++) {
        Dir d1{(int16_t)(i1 - KOFF), (int8_t)(s1 ? -1 : 1)}; Pt v1 = d1.vec();
        for (int i2 = 0; i2 < KMAX; i2++) for (int s2 = 0; s2 < 2; s2++) {
            Dir d2{(int16_t)(i2 - KOFF), (int8_t)(s2 ? -1 : 1)}; Pt v2 = d2.vec();
            int pm = std::max(v1.p, v2.p);
            i128 m1 = POW_F[pm - v1.p], m2 = POW_F[pm - v2.p];
            i128 c1 = (v1.x * m1) * (v2.y * m2), c2 = (v1.y * m1) * (v2.x * m2);
            int cs = (c1 > c2) ? 1 : ((c1 < c2) ? -1 : 0);
            DCROSS[i1][s1][i2][s2] = (int8_t)cs;
            if (d1 == d2) { DCCW_A[i1][s1][i2][s2] = 0; DCCW_B[i1][s1][i2][s2] = 0; }
            else if (i1 == i2) { DCCW_A[i1][s1][i2][s2] = 3; DCCW_B[i1][s1][i2][s2] = 2; }
            else {
                int dk = i2 - i1, p0 = (s1 == s2) ? 0 : 1;
                double raw = dk * G_PHI;
                int n = (int)std::floor(-raw / PI);
                if (((n & 1) + 2) % 2 != p0) n++;
                while (raw + n * PI < 0.0) n += 2;
                while (raw + n * PI >= 2.0 * PI) n -= 2;
                double ang = raw + n * PI;
                if (cs > 0) assert(ang > 0.0 && ang < PI);
                else if (cs < 0) assert(ang > PI && ang < 2.0 * PI);
                else assert(false);
                DCCW_A[i1][s1][i2][s2] = (int8_t)(3 * n + dk);
                DCCW_B[i1][s1][i2][s2] = (int8_t)(2 * n + dk);
            }
        }
    }
}

struct FastRat {
    i128 num = 0, den = 1;
    inline bool operator<(const FastRat& o) const { return num * o.den < o.num * den; }
    inline bool operator==(const FastRat& o) const { return num * o.den == o.num * den; }
    inline i64 int_diff_to(const FastRat& hi, i64 max_s) const {
        i128 dn = hi.num * den - num * hi.den; i128 dd = hi.den * den;
        if (dn < 0) return -1; if (dn == 0) return 0; if (dn % dd != 0) return -1;
        i128 q = dn / dd; return (q > max_s) ? -1 : (i64)q;
    }
};
static inline FastRat fast_line_param(const Pt& origin, const Pt& dv, const Pt& q) {
    Pt diff = pt_sub(q, origin); FastRat r;
    if (dv.x != 0) {
        if (dv.p >= diff.p) { r.num = diff.x * POW_F[dv.p - diff.p]; r.den = dv.x; }
        else { r.num = diff.x; r.den = dv.x * POW_F[diff.p - dv.p]; }
    } else {
        if (dv.p >= diff.p) { r.num = diff.y * POW_F[dv.p - diff.p]; r.den = dv.y; }
        else { r.num = diff.y; r.den = dv.y * POW_F[diff.p - dv.p]; }
    }
    if (r.den < 0) { r.num = -r.num; r.den = -r.den; }
    return r;
}

static constexpr int MW = 8;
static constexpr int MBITS = MW * 64;
struct Mk {
    u64 w[MW] = {0};
    inline bool is_zero() const { u64 z = 0; for (int i = 0; i < MW; i++) z |= w[i]; return z == 0; }
    inline int popcount() const { int c = 0; for (int i = 0; i < MW; i++) c += __builtin_popcountll(w[i]); return c; }
    inline int top() const { for (int i = MW - 1; i >= 0; i--) if (w[i]) return i * 64 + 64 - __builtin_clzll(w[i]); return 0; }
    static inline Mk bit(int idx) { if (idx >= MBITS) { std::cerr << "FATAL: idx=" << idx << " >= MBITS\n"; std::exit(4); } Mk m; m.w[idx / 64] = 1ULL << (idx % 64); return m; }
    inline Mk operator|(const Mk& o) const { Mk r; for (int i = 0; i < MW; i++) r.w[i] = w[i] | o.w[i]; return r; }
    inline Mk operator&(const Mk& o) const { Mk r; for (int i = 0; i < MW; i++) r.w[i] = w[i] & o.w[i]; return r; }
    inline Mk operator~() const { Mk r; for (int i = 0; i < MW; i++) r.w[i] = ~w[i]; return r; }
    inline Mk& operator|=(const Mk& o) { for (int i = 0; i < MW; i++) w[i] |= o.w[i]; return *this; }
};

struct Tri {
    Pt p[3]; Dir ed[3]; i64 len[3];
    double xmin, xmax, ymin, ymax;
    uint8_t on_tgt_edge[3] = {0, 0, 0};
    uint8_t touches_tgt_mask = 0;
    inline void finalize(const Tri* tgt = nullptr) {
        xmin = std::min({p[0].rx, p[1].rx, p[2].rx}); xmax = std::max({p[0].rx, p[1].rx, p[2].rx});
        ymin = std::min({p[0].ry, p[1].ry, p[2].ry}); ymax = std::max({p[0].ry, p[1].ry, p[2].ry});
        touches_tgt_mask = 0;
        if (tgt) {
            for (int j = 0; j < 3; j++) {
                uint8_t m = 0;
                for (int e = 0; e < 3; e++) if (orient_exact(tgt->p[e], tgt->p[(e + 1) % 3], p[j]) == 0) m |= (1u << e);
                on_tgt_edge[j] = m; touches_tgt_mask |= m;
            }
        }
    }
};
struct TriKey {
    Pt p[3];
    bool operator==(const TriKey& o) const { return p[0] == o.p[0] && p[1] == o.p[1] && p[2] == o.p[2]; }
};
struct TriKeyHash {
    size_t operator()(const TriKey& k) const {
        u64 h = 0x9e3779b97f4a7c15ULL;
        auto mix = [&](u64 v) {
            v ^= v >> 30; v *= 0xbf58476d1ce4e5b9ULL; v ^= v >> 27; v *= 0x94d049bb133111ebULL; v ^= v >> 31;
            h ^= v + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
        };
        for (int i = 0; i < 3; i++) {
            mix((u64)k.p[i].p); mix((u64)k.p[i].x); mix((u64)((u128)k.p[i].x >> 64));
            mix((u64)k.p[i].y); mix((u64)((u128)k.p[i].y >> 64));
        }
        return (size_t)h;
    }
};
static inline TriKey make_tri_key(const Tri& t) {
    TriKey k{t.p[0], t.p[1], t.p[2]};
    if (k.p[1] < k.p[0]) std::swap(k.p[0], k.p[1]);
    if (k.p[2] < k.p[1]) std::swap(k.p[1], k.p[2]);
    if (k.p[1] < k.p[0]) std::swap(k.p[0], k.p[1]);
    return k;
}
static inline bool point_in_closed_tri(const Tri& tgt, const Pt& q) {
    for (int i = 0; i < 3; i++) if (orient_exact(tgt.p[i], tgt.p[(i + 1) % 3], q) < 0) return false;
    return true;
}
static inline bool tris_overlap_exact(const Tri& a, const Tri& b) {
    if (a.xmax + 1e-2 < b.xmin || b.xmax + 1e-2 < a.xmin ||
        a.ymax + 1e-2 < b.ymin || b.ymax + 1e-2 < a.ymin) return false;
    for (int i = 0; i < 3; i++) {
        const Pt& p = a.p[i]; const Pt& q = a.p[(i + 1) % 3];
        if (orient_exact(p, q, b.p[0]) <= 0 && orient_exact(p, q, b.p[1]) <= 0 && orient_exact(p, q, b.p[2]) <= 0) return false;
    }
    for (int i = 0; i < 3; i++) {
        const Pt& p = b.p[i]; const Pt& q = b.p[(i + 1) % 3];
        if (orient_exact(p, q, a.p[0]) <= 0 && orient_exact(p, q, a.p[1]) <= 0 && orient_exact(p, q, a.p[2]) <= 0) return false;
    }
    return true;
}
static inline Tri make_tile(const Pt& v, const Dir& d, int slot, const Tri* tgt = nullptr) {
    Tri t; i64 l1 = 0, l2 = 0, l3 = 0; Dir d2, d12;
    switch (slot) {
        case 0: l1 = G_A; l2 = G_C; l3 = G_B; d2 = d.add_beta();  d12 = Dir{(int16_t)(d.k + 1), d.s}; break;
        case 1: l1 = G_C; l2 = G_A; l3 = G_B; d2 = d.add_beta();  d12 = Dir{(int16_t)(d.k + 2), d.s}; break;
        case 2: l1 = G_B; l2 = G_C; l3 = G_A; d2 = d.add_alpha(); d12 = Dir{(int16_t)(d.k + 1), d.s}; break;
        case 3: l1 = G_C; l2 = G_B; l3 = G_A; d2 = d.add_alpha(); d12 = Dir{(int16_t)(d.k - 3), d.s}; break;
        case 4: l1 = G_A; l2 = G_B; l3 = G_C; d2 = d.add_gamma(); d12 = Dir{(int16_t)(d.k - 3), d.s}; break;
        case 5: l1 = G_B; l2 = G_A; l3 = G_C; d2 = d.add_gamma(); d12 = Dir{(int16_t)(d.k + 2), d.s}; break;
        default: assert(false);
    }
    t.p[0] = v;
    t.p[1] = pt_add(v, pt_scale(d.vec(), l1));
    t.p[2] = pt_add(v, pt_scale(d2.vec(), l2));
    t.ed[0] = d; t.ed[1] = d12; t.ed[2] = d2.rev();
    t.len[0] = l1; t.len[1] = l3; t.len[2] = l2;
    t.finalize(tgt);
    return t;
}
static inline void slot_ab(int slot, int& dA, int& dB) {
    if (slot <= 1) { dA = 0; dB = 1; }
    else if (slot <= 3) { dA = 1; dB = 0; }
    else { dA = 2; dB = 1; }
}

struct ProofNode {
    uint8_t kind = 0;
    Pt v; Dir d, d2;
    int eidx = 0, ng_id = -1, nkids = 0;
    int kslot[6] = {0};
    int kchild[6] = {-1, -1, -1, -1, -1, -1};
};
struct DeadInfo {
    uint8_t kind = 0;
    Pt v; Dir d, d2; int eidx = 0; Mk mask;
};
struct Opt {
    Pt v; Dir d; double phi = 0.0, sy = 0.0;
    int nfeas = 0; int fslot[6]; Tri ftri[6]; Mk mask;
};

struct Solver {
    Tri tgt; Pt tgt_ed_vec[3];
    double sweep_cos = 0.0, sweep_sin = 1.0;
    int target_N = 0; int la = 1;
    bool use_cbj = true, use_ng = true, record_cert = true;
    double band = 10.0;
    u64 cap = 100000000ULL;
    size_t ng_cap = 400000;
    std::vector<uint8_t> in_sg; i64 max_side = 0;

    std::vector<Tri> placed; std::vector<u32> keys;
    std::unordered_map<u32, int> kset;
    std::unordered_map<TriKey, u32, TriKeyHash> kid_map;
    std::vector<TriKey> kid_list;
    std::vector<std::vector<u32>> nogoods;
    std::vector<int> ng_root;
    std::unordered_map<u32, std::vector<int>> ng_idx;
    std::unordered_set<u64> ng_seen;
    std::vector<ProofNode> pnodes;
    u64 calls = 0, jumps = 0, ng_hits = 0, sg_prunes = 0, ang_prunes = 0;
    int maxdepth = 0; bool found = false;

    inline double sweep_y(const Pt& v) const { return v.rx * sweep_cos + v.ry * sweep_sin; }
    void set_sweep_leg(int leg_idx) {
        if (leg_idx == 3) {
            double ang = 1.5 * G_ALPHA;
            sweep_cos = std::cos(ang); sweep_sin = std::sin(ang);
            return;
        }
        Pt ev = tgt.ed[leg_idx].vec();
        double norm = std::hypot(ev.rx, ev.ry);
        sweep_cos = -ev.ry / norm; sweep_sin = ev.rx / norm;
    }
    void init_semigroup() {
        for (int i = 0; i < 3; i++) tgt_ed_vec[i] = tgt.ed[i].vec();
        max_side = std::max({tgt.len[0], tgt.len[1], tgt.len[2]});
        in_sg.assign((size_t)max_side + 1, 0); in_sg[0] = 1;
        for (i64 i = 0; i <= max_side; i++) if (in_sg[i]) {
            if (i + G_A <= max_side) in_sg[i + G_A] = 1;
            if (i + G_B <= max_side) in_sg[i + G_B] = 1;
            if (i + G_C <= max_side) in_sg[i + G_C] = 1;
        }
    }
    inline u32 get_kid(const Tri& t) {
        TriKey k = make_tri_key(t);
        auto it = kid_map.find(k); if (it != kid_map.end()) return it->second;
        u32 id = (u32)kid_list.size(); kid_list.push_back(k); kid_map.emplace(k, id); return id;
    }
    inline void push_tile(const Tri& t) {
        if (use_ng) { u32 k = get_kid(t); kset[k] = (int)placed.size(); keys.push_back(k); }
        placed.push_back(t);
    }
    inline void pop_tile() {
        if (use_ng) { u32 k = keys.back(); keys.pop_back(); kset.erase(k); }
        placed.pop_back();
    }
    inline int add_leaf(const DeadInfo& di) {
        if (!record_cert) return -1;
        ProofNode n; n.kind = di.kind; n.v = di.v; n.d = di.d; n.d2 = di.d2; n.eidx = di.eidx;
        int id = (int)pnodes.size(); pnodes.push_back(n); return id;
    }
    inline int add_ref(int ng_id) {
        if (!record_cert) return -1;
        ProofNode n; n.kind = 4; n.ng_id = ng_id;
        int id = (int)pnodes.size(); pnodes.push_back(n); return id;
    }
    inline int add_branch(const Pt& v, const Dir& d, int nkids, const int* slots, const int* kids) {
        if (!record_cert) return -1;
        ProofNode n; n.kind = 0; n.v = v; n.d = d; n.nkids = nkids;
        for (int i = 0; i < nkids; i++) { n.kslot[i] = slots[i]; n.kchild[i] = kids[i]; }
        int id = (int)pnodes.size(); pnodes.push_back(n); return id;
    }
    static inline u64 hash_vec(const std::vector<u32>& v) {
        u64 h = 14695981039346656037ULL;
        for (u32 x : v) { h ^= x; h *= 1099511628211ULL; }
        return h;
    }
    void record_ng(u64 tot, const Mk& m, int root_nid) {
        if (!use_ng || tot < 2 || nogoods.size() >= ng_cap) return;
        std::vector<u32> ks; ks.reserve(32);
        for (int i = 0; i < (int)placed.size(); i++) if (!(m & Mk::bit(i)).is_zero()) ks.push_back(keys[i]);
        if (ks.empty()) return;
        std::sort(ks.begin(), ks.end());
        u64 h = hash_vec(ks); if (ng_seen.count(h)) return;
        int id = (int)nogoods.size();
        for (u32 k : ks) ng_idx[k].push_back(id);
        ng_seen.insert(h); nogoods.push_back(std::move(ks)); ng_root.push_back(root_nid);
    }
    bool lookup_ng(Mk& out_m, int& out_ng_id) {
        if (!use_ng || keys.empty()) return false;
        auto it = ng_idx.find(keys.back()); if (it == ng_idx.end()) return false;
        for (int id : it->second) {
            Mk m; bool ok = true;
            for (u32 kk : nogoods[id]) {
                auto jt = kset.find(kk); if (jt == kset.end()) { ok = false; break; }
                m |= Mk::bit(jt->second);
            }
            if (ok) { out_m = m; out_ng_id = id; return true; }
        }
        return false;
    }
    bool check_boundary_dead(DeadInfo& di, uint8_t edge_mask = 7) {
        if (edge_mask == 0) return false;
        struct Seg { FastRat a, b; int ti; };
        Seg segs[512];
        for (int eidx = 0; eidx < 3; eidx++) {
            const uint8_t emask = (uint8_t)(1u << eidx);
            if (!(edge_mask & emask)) continue;
            int nseg = 0;
            const Pt& P0 = tgt.p[eidx]; const Pt& dv = tgt_ed_vec[eidx]; i64 L = tgt.len[eidx];
            for (int ti = 0; ti < (int)placed.size(); ti++) {
                const Tri& t = placed[ti];
                if (!(t.touches_tgt_mask & emask)) continue;
                int j1 = -1, j2 = -1;
                for (int j = 0; j < 3; j++) if (t.on_tgt_edge[j] & emask) { if (j1 < 0) j1 = j; else j2 = j; }
                if (j2 < 0) { FastRat r = fast_line_param(P0, dv, t.p[j1]); segs[nseg++] = {r, r, ti}; }
                else {
                    FastRat r1 = fast_line_param(P0, dv, t.p[j1]), r2 = fast_line_param(P0, dv, t.p[j2]);
                    if (r2 < r1) std::swap(r1, r2);
                    segs[nseg++] = {r1, r2, ti};
                }
            }
            if (nseg == 0) continue;
            std::sort(segs, segs + nseg, [](const Seg& u, const Seg& v) {
                if (!(u.a == v.a)) return u.a < v.a; return u.b < v.b;
            });
            FastRat cur{0, 1}; int cur_ti = -1;
            for (int si = 0; si < nseg; si++) {
                const auto& s = segs[si];
                if (cur < s.a) {
                    i64 g = cur.int_diff_to(s.a, max_side);
                    if (g < 0 || !in_sg[(size_t)g]) {
                        Mk m; if (cur_ti >= 0) m |= Mk::bit(cur_ti); m |= Mk::bit(s.ti);
                        di.kind = 3; di.eidx = eidx; di.mask = m; sg_prunes++; return true;
                    }
                }
                if (cur < s.b || (cur == s.b && cur_ti < 0)) { cur = s.b; cur_ti = s.ti; }
            }
            FastRat endR{L, 1};
            if (cur < endR) {
                i64 g = cur.int_diff_to(endR, max_side);
                if (g < 0 || !in_sg[(size_t)g]) {
                    Mk m; if (cur_ti >= 0) m |= Mk::bit(cur_ti);
                    di.kind = 3; di.eidx = eidx; di.mask = m; sg_prunes++; return true;
                }
            }
        }
        return false;
    }
    bool corners_at(const Pt& v, std::vector<Opt>* out, DeadInfo& di, bool dead_only) {
        struct Arc { Dir s, e; Mk m; };
        Arc iv[24]; int niv = 0;
        for (int i = 0; i < 3; i++) {
            int o = orient_exact(tgt.p[i], tgt.p[(i + 1) % 3], v);
            if (o < 0) return true;
            if (o == 0) iv[niv++] = {tgt.ed[i].rev(), tgt.ed[i], Mk{}};
        }
        for (int ti = 0; ti < (int)placed.size(); ti++) {
            const Tri& t = placed[ti];
            if (v.rx < t.xmin - 1e-2 || v.rx > t.xmax + 1e-2 ||
                v.ry < t.ymin - 1e-2 || v.ry > t.ymax + 1e-2) continue;
            int o0 = orient_exact(t.p[0], t.p[1], v); if (o0 < 0) continue;
            int o1 = orient_exact(t.p[1], t.p[2], v); if (o1 < 0) continue;
            int o2 = orient_exact(t.p[2], t.p[0], v); if (o2 < 0) continue;
            if (o0 > 0 && o1 > 0 && o2 > 0) return true;
            Mk bit = Mk::bit(ti);
            if (v == t.p[0]) iv[niv++] = {t.ed[0], t.ed[2].rev(), bit};
            else if (v == t.p[1]) iv[niv++] = {t.ed[1], t.ed[0].rev(), bit};
            else if (v == t.p[2]) iv[niv++] = {t.ed[2], t.ed[1].rev(), bit};
            else if (o0 == 0) iv[niv++] = {t.ed[0], t.ed[0].rev(), bit};
            else if (o1 == 0) iv[niv++] = {t.ed[1], t.ed[1].rev(), bit};
            else if (o2 == 0) iv[niv++] = {t.ed[2], t.ed[2].rev(), bit};
        }
        if (niv == 0) return true;
        Mk cmask; Dir marks[48]; int nm = 0;
        for (int i = 0; i < niv; i++) { cmask |= iv[i].m; marks[nm++] = iv[i].s; marks[nm++] = iv[i].e; }
        std::sort(marks, marks + nm, [](const Dir& a, const Dir& b) { if (a == b) return false; return a.ang() < b.ang(); });
        Dir u[48]; int k = 0;
        for (int i = 0; i < nm; i++) if (k == 0 || u[k - 1] != marks[i]) u[k++] = marks[i];
        if (k == 0) return true;
        bool free_sec[48]; int start = -1;
        for (int i = 0; i < k; i++) {
            const Dir& a = u[i]; bool fr = true;
            for (int c = 0; c < niv; c++) if (a == iv[c].s || dir_strictly_between(iv[c].s, iv[c].e, a)) { fr = false; break; }
            free_sec[i] = fr; if (!fr && start < 0) start = i;
        }
        if (start < 0) return true;
        struct FreeArc { Dir s, e; int A, B; double phi; };
        FreeArc farcs[24]; int nf = 0, i = 0;
        while (i < k) {
            int idx = (start + i) % k;
            if (free_sec[idx]) {
                Dir ds = u[idx]; int j = i;
                while (j < k && free_sec[(start + j) % k]) j++;
                Dir de = u[(start + j) % k];
                int A = 0, B = 0; exact_ccw_ab(ds, de, A, B);
                if (A < 0 || B < 0) {
                    di.kind = 2; di.v = v; di.d = ds; di.d2 = de; di.mask = cmask;
                    ang_prunes++; return false;
                }
                farcs[nf++] = {ds, de, A, B, A * G_ALPHA + B * G_BETA};
                i = j;
            } else i++;
        }
        double sy = sweep_y(v);
        for (int fi = 0; fi < nf; fi++) {
            const auto& fa = farcs[fi];
            bool pointed = true;
            for (int fj = 0; fj < nf; fj++) {
                const auto& fb = farcs[fj];
                if (dir_cross_sign(fa.s, fb.e) <= 0) { pointed = false; break; }
                if (fb.s != fa.s && dir_cross_sign(fa.s, fb.s) <= 0) { pointed = false; break; }
            }
            if (!pointed) continue;
            if (dead_only) {
                Mk mask = cmask; bool any_feas = false;
                for (int slot = 0; slot < 6; slot++) {
                    int dA = 0, dB = 0; slot_ab(slot, dA, dB);
                    if (fa.A - dA < 0 || fa.B - dB < 0) continue;
                    Tri cand = make_tile(v, fa.s, slot, nullptr);
                    if (!point_in_closed_tri(tgt, cand.p[1]) || !point_in_closed_tri(tgt, cand.p[2])) continue;
                    int hit = -1; bool inmask = false;
                    for (int ui = 0; ui < (int)placed.size(); ui++) if (tris_overlap_exact(placed[ui], cand)) {
                        if (!(mask & Mk::bit(ui)).is_zero()) { inmask = true; hit = ui; break; }
                        if (hit < 0) hit = ui;
                    }
                    if (hit >= 0) { if (!inmask) mask |= Mk::bit(hit); }
                    else { any_feas = true; break; }
                }
                if (!any_feas) { di.kind = 1; di.v = v; di.d = fa.s; di.mask = mask; return false; }
            } else {
                Opt opt; opt.v = v; opt.d = fa.s; opt.phi = fa.phi; opt.sy = sy; opt.nfeas = 0; opt.mask = cmask;
                for (int slot = 0; slot < 6; slot++) {
                    int dA = 0, dB = 0; slot_ab(slot, dA, dB);
                    if (fa.A - dA < 0 || fa.B - dB < 0) continue;
                    Tri cand = make_tile(v, fa.s, slot, &tgt);
                    if (!point_in_closed_tri(tgt, cand.p[1]) || !point_in_closed_tri(tgt, cand.p[2])) continue;
                    int hit = -1; bool inmask = false;
                    for (int ui = 0; ui < (int)placed.size(); ui++) if (tris_overlap_exact(placed[ui], cand)) {
                        if (!(opt.mask & Mk::bit(ui)).is_zero()) { inmask = true; hit = ui; break; }
                        if (hit < 0) hit = ui;
                    }
                    if (hit >= 0) { if (!inmask) opt.mask |= Mk::bit(hit); }
                    else { opt.fslot[opt.nfeas] = slot; opt.ftri[opt.nfeas] = cand; opt.nfeas++; }
                }
                out->push_back(opt);
            }
        }
        return true;
    }
    bool is_dead_local(DeadInfo& di) {
        const Tri& t_new = placed.back();
        if (check_boundary_dead(di, t_new.touches_tgt_mask)) return true;
        double pad = (double)G_C + 1.0;
        double lx0 = t_new.xmin - pad, lx1 = t_new.xmax + pad, ly0 = t_new.ymin - pad, ly1 = t_new.ymax + pad;
        std::vector<Pt> pts; pts.reserve(placed.size() * 3 + 3);
        for (int i = 0; i < 3; i++) {
            const Pt& q = tgt.p[i];
            if (q.rx >= lx0 && q.rx <= lx1 && q.ry >= ly0 && q.ry <= ly1) pts.push_back(q);
        }
        for (const auto& t : placed) {
            if (t.xmax < lx0 || t.xmin > lx1 || t.ymax < ly0 || t.ymin > ly1) continue;
            for (int i = 0; i < 3; i++) {
                const Pt& q = t.p[i];
                if (q.rx >= lx0 && q.rx <= lx1 && q.ry >= ly0 && q.ry <= ly1) pts.push_back(q);
            }
        }
        std::sort(pts.begin(), pts.end());
        pts.erase(std::unique(pts.begin(), pts.end()), pts.end());
        for (int i = 0; i < 3; i++) if (!corners_at(t_new.p[i], nullptr, di, true)) return true;
        for (const auto& q : pts) {
            if (q == t_new.p[0] || q == t_new.p[1] || q == t_new.p[2]) continue;
            if (!corners_at(q, nullptr, di, true)) return true;
        }
        return false;
    }
    bool get_options(std::vector<Opt>& out, DeadInfo& di) {
        if (check_boundary_dead(di, 7)) return false;
        std::vector<Pt> pts; pts.reserve(placed.size() * 3 + 3);
        for (int i = 0; i < 3; i++) pts.push_back(tgt.p[i]);
        for (const auto& t : placed) for (int i = 0; i < 3; i++) pts.push_back(t.p[i]);
        std::sort(pts.begin(), pts.end());
        pts.erase(std::unique(pts.begin(), pts.end()), pts.end());
        out.clear();
        for (const auto& q : pts) if (!corners_at(q, &out, di, false)) return false;
        if (!out.empty()) {
            double ymin = 1e30;
            for (const auto& o : out) if (o.sy < ymin) ymin = o.sy;
            double thr = ymin + band;
            std::sort(out.begin(), out.end(), [&](const Opt& a, const Opt& b) {
                int ka = (a.nfeas == 0) ? 0 : (a.sy <= thr ? a.nfeas : a.nfeas + 1000);
                int kb = (b.nfeas == 0) ? 0 : (b.sy <= thr ? b.nfeas : b.nfeas + 1000);
                if (ka != kb) return ka < kb;
                return a.phi < b.phi;
            });
            if (out[0].nfeas > 0) out.erase(std::remove_if(out.begin(), out.end(), [&](const Opt& o) { return o.sy > thr; }), out.end());
        }
        return true;
    }
    bool solve(int limit, bool main_call, u64& out_tot, Mk& out_m, int& out_nid) {
        if (found) return false;
        if (main_call) {
            calls++;
            if (calls >= cap) return false;
            if ((int)placed.size() > maxdepth) maxdepth = (int)placed.size();
        }
        int depth = (int)placed.size();
        Mk bit = Mk::bit(depth); Mk clr = ~bit;
        Mk ng_m; int ng_id = -1;
        if (lookup_ng(ng_m, ng_id)) { ng_hits++; out_tot = 1; out_m = ng_m; out_nid = add_ref(ng_id); return true; }
        if (limit == 0 && !main_call) {
            DeadInfo di;
            if (is_dead_local(di)) { out_tot = 1; out_m = di.mask; out_nid = add_leaf(di); return true; }
            return false;
        }
        std::vector<Opt> opts; opts.reserve(32); DeadInfo di;
        if (!get_options(opts, di)) { out_tot = 1; out_m = di.mask; out_nid = add_leaf(di); return true; }
        if (opts.empty()) { if ((int)placed.size() == target_N && main_call) found = true; return false; }
        if (opts[0].nfeas == 0) {
            int best_i = 0;
            for (int i = 1; i < (int)opts.size() && opts[i].nfeas == 0; i++) {
                if (opts[i].mask.popcount() < opts[best_i].mask.popcount() ||
                    (opts[i].mask.popcount() == opts[best_i].mask.popcount() &&
                     opts[i].mask.top() < opts[best_i].mask.top())) best_i = i;
            }
            DeadInfo cdi; cdi.kind = 1; cdi.v = opts[best_i].v; cdi.d = opts[best_i].d; cdi.mask = opts[best_i].mask;
            out_tot = 1; out_m = cdi.mask; out_nid = add_leaf(cdi); return true;
        }
        if (limit == 0) return false;
        if (!main_call) {
            bool has_best = false; u64 best_tot = UINT64_MAX; Mk best_m; int best_nid = -1;
            for (const auto& o : opts) {
                u64 tot = 1; Mk m = o.mask; bool ok = true; int kkids[6];
                for (int j = 0; j < o.nfeas; j++) {
                    push_tile(o.ftri[j]); u64 cs = 0; Mk cm; int cnid = -1;
                    bool ref = solve(limit - 1, false, cs, cm, cnid);
                    pop_tile();
                    if (!ref) { ok = false; break; }
                    if (use_cbj && (cm & bit).is_zero()) { jumps++; out_tot = cs; out_m = cm; out_nid = cnid; return true; }
                    tot += cs; m |= (cm & clr); kkids[j] = cnid;
                }
                if (ok && (!has_best || tot < best_tot)) {
                    has_best = true; best_tot = tot; best_m = m;
                    best_nid = add_branch(o.v, o.d, o.nfeas, o.fslot, kkids);
                }
            }
            if (has_best) { record_ng(best_tot, best_m, best_nid); out_tot = best_tot; out_m = best_m; out_nid = best_nid; return true; }
            return false;
        }
        int bi = 0; u64 bscore = UINT64_MAX;
        struct Est { bool ref = false; u64 tot = 0; Mk m; int nid = -1; };
        Est bests[6]; int nbests = 0;
        if (la > 0) {
            for (int i = 0; i < (int)opts.size(); i++) {
                const auto& o = opts[i]; u64 sc = 0; Est ests[6];
                for (int j = 0; j < o.nfeas; j++) {
                    push_tile(o.ftri[j]); u64 cs = 0; Mk cm; int cnid = -1;
                    bool ref = solve(la - 1, false, cs, cm, cnid);
                    pop_tile();
                    if (ref) {
                        if (use_cbj && (cm & bit).is_zero()) { jumps++; out_tot = cs; out_m = cm; out_nid = cnid; return true; }
                        sc += cs; ests[j] = {true, cs, cm, cnid};
                    } else { sc += 1000000ULL; ests[j] = {false, 0, Mk{}, -1}; }
                }
                if (sc < bscore) { bscore = sc; bi = i; nbests = o.nfeas; for (int j = 0; j < nbests; j++) bests[j] = ests[j]; }
                if (sc < 1000000ULL) break;
            }
        }
        const auto& o = opts[bi]; u64 tot = 1; Mk m = o.mask; int kkids[6];
        for (int j = 0; j < o.nfeas; j++) {
            if (j < nbests && bests[j].ref) { tot += bests[j].tot; m |= (bests[j].m & clr); kkids[j] = bests[j].nid; continue; }
            push_tile(o.ftri[j]); u64 cs = 0; Mk cm; int cnid = -1;
            bool ref = solve(limit, true, cs, cm, cnid);
            pop_tile();
            if (!ref) return false;
            if (use_cbj && (cm & bit).is_zero()) { jumps++; out_tot = cs; out_m = cm; out_nid = cnid; return true; }
            tot += cs; m |= (cm & clr); kkids[j] = cnid;
        }
        int nid = add_branch(o.v, o.d, o.nfeas, o.fslot, kkids);
        record_ng(tot, m, nid); out_tot = tot; out_m = m; out_nid = nid; return true;
    }

    void export_subproof(int root_nid, std::ostream& os, u64& out_emitted_nodes, u64& out_emitted_ngs) const {
        std::vector<int> ng_order; std::vector<uint8_t> ng_vis(nogoods.size(), 0);
        std::vector<int> node_map(pnodes.size(), -1); std::vector<int> node_order;
        std::function<void(int)> dfs_node = [&](int nid) {
            if (node_map[nid] != -1) return;
            const auto& pn = pnodes[nid];
            if (pn.kind == 0) { for (int i = 0; i < pn.nkids; i++) dfs_node(pn.kchild[i]); }
            else if (pn.kind == 4) {
                int g = pn.ng_id;
                if (!ng_vis[g]) { ng_vis[g] = 1; dfs_node(ng_root[g]); ng_order.push_back(g); }
            }
            node_map[nid] = (int)node_order.size(); node_order.push_back(nid);
        };
        dfs_node(root_nid);
        std::vector<int> ng_map(nogoods.size(), -1);
        for (int i = 0; i < (int)ng_order.size(); i++) ng_map[ng_order[i]] = i;
        std::vector<int> tk_map(kid_list.size(), -1); std::vector<int> tk_order;
        for (int g : ng_order) for (u32 tk : nogoods[g]) if (tk_map[tk] == -1) { tk_map[tk] = (int)tk_order.size(); tk_order.push_back((int)tk); }

        os << "SUBPROOF " << tk_order.size() << " " << node_order.size() << " " << ng_order.size() << " " << node_map[root_nid] << "\n";
        for (int tk : tk_order) {
            const TriKey& k = kid_list[tk]; os << "K";
            for (int j = 0; j < 3; j++) os << " " << i128_to_str(k.p[j].x) << " " << i128_to_str(k.p[j].y) << " " << k.p[j].p;
            os << "\n";
        }
        for (int nid : node_order) {
            const auto& pn = pnodes[nid];
            if (pn.kind == 0) {
                os << "B " << i128_to_str(pn.v.x) << " " << i128_to_str(pn.v.y) << " " << pn.v.p
                   << " " << (int)pn.d.k << " " << (int)pn.d.s << " " << pn.nkids;
                for (int i = 0; i < pn.nkids; i++) os << " " << pn.kslot[i] << " " << node_map[pn.kchild[i]];
                os << "\n";
            } else if (pn.kind == 1) {
                os << "C " << i128_to_str(pn.v.x) << " " << i128_to_str(pn.v.y) << " " << pn.v.p
                   << " " << (int)pn.d.k << " " << (int)pn.d.s << "\n";
            } else if (pn.kind == 2) {
                os << "A " << i128_to_str(pn.v.x) << " " << i128_to_str(pn.v.y) << " " << pn.v.p
                   << " " << (int)pn.d.k << " " << (int)pn.d.s << " " << (int)pn.d2.k << " " << (int)pn.d2.s << "\n";
            } else if (pn.kind == 3) os << "G " << pn.eidx << "\n";
            else if (pn.kind == 4) os << "R " << ng_map[pn.ng_id] << "\n";
        }
        for (int g : ng_order) {
            os << "N " << node_map[ng_root[g]] << " " << nogoods[g].size();
            for (u32 tk : nogoods[g]) os << " " << tk_map[tk];
            os << "\n";
        }
        out_emitted_nodes = node_order.size(); out_emitted_ngs = ng_order.size();
    }
};

struct PrefNode {
    uint8_t kind = 0;
    Pt v; Dir d, d2; int eidx = 0; int task_id = -1;
    int nkids = 0; int kslot[6] = {0}; int kchild[6] = {-1,-1,-1,-1,-1,-1};
};

static int build_prefix(Solver& S, int rem_depth, std::vector<PrefNode>& ptree,
                        std::vector<std::vector<Tri>>& frontier, std::vector<int>& frontier_pnode) {
    DeadInfo di; std::vector<Opt> opts;
    if (!S.get_options(opts, di)) {
        PrefNode pn; pn.kind = di.kind; pn.v = di.v; pn.d = di.d; pn.d2 = di.d2; pn.eidx = di.eidx;
        int id = (int)ptree.size(); ptree.push_back(pn); return id;
    }
    if (opts.empty()) { std::cerr << "TILING FOUND IN PREFIX!\n"; std::exit(10); }
    if (opts[0].nfeas == 0) {
        PrefNode pn; pn.kind = 1; pn.v = opts[0].v; pn.d = opts[0].d;
        int id = (int)ptree.size(); ptree.push_back(pn); return id;
    }
    if (rem_depth == 0) {
        int tid = (int)frontier.size();
        frontier.push_back(S.placed);
        PrefNode pn; pn.kind = 5; pn.task_id = tid;
        int id = (int)ptree.size(); ptree.push_back(pn);
        frontier_pnode.push_back(id);
        return id;
    }
    int bi = 0; u64 bscore = UINT64_MAX;
    bool ref_kid[6] = {false}; DeadInfo ref_di[6];
    for (int i = 0; i < (int)opts.size(); i++) {
        const auto& o = opts[i]; u64 sc = 0; bool rk[6] = {false}; DeadInfo rdi[6];
        for (int j = 0; j < o.nfeas; j++) {
            S.push_tile(o.ftri[j]); DeadInfo ldi; bool r = S.is_dead_local(ldi); S.pop_tile();
            if (r) { sc += 1; rk[j] = true; rdi[j] = ldi; } else sc += 1000000ULL;
        }
        if (sc < bscore) { bscore = sc; bi = i; for (int j = 0; j < o.nfeas; j++) { ref_kid[j] = rk[j]; ref_di[j] = rdi[j]; } }
        if (sc < 1000000ULL) break;
    }
    const auto& o = opts[bi]; int kids[6];
    for (int j = 0; j < o.nfeas; j++) {
        if (ref_kid[j]) {
            PrefNode lpn; lpn.kind = ref_di[j].kind; lpn.v = ref_di[j].v; lpn.d = ref_di[j].d; lpn.d2 = ref_di[j].d2; lpn.eidx = ref_di[j].eidx;
            kids[j] = (int)ptree.size(); ptree.push_back(lpn);
        } else {
            S.push_tile(o.ftri[j]);
            kids[j] = build_prefix(S, rem_depth - 1, ptree, frontier, frontier_pnode);
            S.pop_tile();
        }
    }
    PrefNode pn; pn.kind = 0; pn.v = o.v; pn.d = o.d; pn.nkids = o.nfeas;
    for (int j = 0; j < o.nfeas; j++) { pn.kslot[j] = o.fslot[j]; pn.kchild[j] = kids[j]; }
    int id = (int)ptree.size(); ptree.push_back(pn); return id;
}

static Tri make_T_target(int e, int f, int M) {
    Tri T;
    i64 leg = (i64)M * f * f * f;
    i64 base = (i64)M * e * (3 * f * f - e * e);
    T.p[0] = Pt{0, 0, 0}; T.p[0].compute_approx();
    Dir d0{0, 1}, d1{-3, 1}, d2{-6, 1};
    T.p[1] = pt_scale(d0.vec(), leg);
    T.p[2] = pt_scale(d2.rev().vec(), leg);
    T.ed[0] = d0; T.ed[1] = d1; T.ed[2] = d2;
    T.len[0] = leg; T.len[1] = base; T.len[2] = leg;
    T.finalize();
    assert(pt_sub(T.p[2], T.p[1]) == pt_scale(d1.vec(), base));
    assert(orient_exact(T.p[0], T.p[1], T.p[2]) > 0);
    return T;
}

int main(int argc, char** argv) {
    if (argc < 5) {
        std::cerr << "Usage: exact_tiler_lowmem <e> <f> <M> <cert_out> [band=10] [split_d=10] [fast_cap=80000] [max_rounds=7] [extra_d=3] [apex_mask=15] [a3_sweep=2] [threads=24]\n";
        return 1;
    }
    int e = std::atoi(argv[1]), f = std::atoi(argv[2]), M = std::atoi(argv[3]);
    std::string cert_path = argv[4];
    double band = (argc > 5) ? std::atof(argv[5]) : 10.0;
    int split_d = (argc > 6) ? std::atoi(argv[6]) : 10;
    u64 fast_cap = (argc > 7) ? std::strtoull(argv[7], nullptr, 10) : 80000ULL;
    int max_rounds = (argc > 8) ? std::atoi(argv[8]) : 7;
    int extra_d = (argc > 9) ? std::atoi(argv[9]) : 3;
    int apex_mask = (argc > 10) ? std::atoi(argv[10]) : 15;
    int a3_sweep = (argc > 11) ? std::atoi(argv[11]) : 2;
    int threads = (argc > 12) ? std::atoi(argv[12]) : 24;
    omp_set_num_threads(threads);

    init_tables(e, f);
    Solver baseS;
    baseS.tgt = make_T_target(e, f, M);
    baseS.target_N = M * M * (3 * f * f - e * e);
    baseS.band = band; baseS.la = 1; baseS.record_cert = true;
    baseS.init_semigroup();

    std::cout << "=== EXACT_CERT_LOWMEM (" << threads << "T): T_" << M << "(" << e << "," << f
              << ") N=" << baseS.target_N << " band=" << band << " split_d=" << split_d
              << " fast_cap=" << fast_cap << " rounds=" << max_rounds << " extra_d=" << extra_d
              << " a3_sweep=" << a3_sweep << " out=" << cert_path << " ===\n" << std::flush;

    std::ofstream cert(cert_path);
    assert(cert.good());
    cert << "ECERT_V1 " << e << " " << f << " " << M << "\n";

    auto t0 = std::chrono::steady_clock::now();
    Pt O = baseS.tgt.p[0];
    Dir d0{0, 1}, d1 = d0.add_alpha(), d2 = d1.add_alpha();
    struct ApexSpec { int s1, s2, s3, sweep_leg; };
    std::vector<ApexSpec> cases = { {2,2,2,0}, {2,2,3,0}, {3,2,2,a3_sweep}, {3,2,3,2} };

    bool all_refuted = true;
    u64 total_emitted_nodes = 0, total_emitted_ngs = 0, grand_calls = 0;
    std::string spill_path = cert_path + ".spill";

    for (int ci = 0; ci < 4; ci++) {
        if (!(apex_mask & (1 << ci))) continue;
        auto sp = cases[ci];
        auto ct0 = std::chrono::steady_clock::now();
        Solver prefS = baseS;
        prefS.set_sweep_leg(sp.sweep_leg);
        prefS.use_ng = false;
        prefS.push_tile(make_tile(O, d0, sp.s1, &prefS.tgt));
        prefS.push_tile(make_tile(O, d1, sp.s2, &prefS.tgt));
        prefS.push_tile(make_tile(O, d2, sp.s3, &prefS.tgt));

        std::vector<PrefNode> ptree;
        std::vector<std::vector<Tri>> frontier;
        std::vector<int> frontier_pnode;
        int proot = build_prefix(prefS, split_d, ptree, frontier, frontier_pnode);

        // Spill file stores solved subproofs on disk; we only keep (offset, length) in RAM!
        std::ofstream spill_out(spill_path, std::ios::binary | std::ios::trunc);
        assert(spill_out.good());
        std::vector<std::pair<u64, u64>> sub_loc(frontier.size(), {0, 0});
        std::vector<uint8_t> solved(frontier.size(), 0);
        std::vector<int> active_tasks;
        for (int i = 0; i < (int)frontier.size(); i++) active_tasks.push_back(i);

        u64 apex_calls = 0, apex_enodes = 0, apex_engs = 0;
        bool tiling_found = false;

        for (int rd = 0; rd < max_rounds && !active_tasks.empty() && !tiling_found; rd++) {
            u64 rd_cap = (rd == max_rounds - 1) ? 20000000ULL : (fast_cap * (u64)(rd + 1));
            int na = (int)active_tasks.size();
            std::atomic<int> done_cnt{0}, ok_cnt{0}, strag_cnt{0};
            std::atomic<u64> rd_calls{0}, rd_enodes{0}, rd_engs{0};
            std::vector<uint8_t> rd_status(na, 0);

            #pragma omp parallel for schedule(dynamic, 1)
            for (int ai = 0; ai < na; ai++) {
                if (tiling_found) continue;
                int fi = active_tasks[ai];
                try {
                    Solver ws = baseS;
                    ws.cap = rd_cap;
                    ws.set_sweep_leg(sp.sweep_leg);
                    for (const auto& t : frontier[fi]) ws.push_tile(t);
                    u64 wt = 0; Mk wm; int wnid = -1;
                    bool wref = ws.solve(1000000, true, wt, wm, wnid);
                    rd_calls += ws.calls;
                    if (ws.found) {
                        rd_status[ai] = 3;
                        tiling_found = true;
                    } else if (wref) {
                        std::ostringstream oss; u64 en = 0, eg = 0;
                        ws.export_subproof(wnid, oss, en, eg);
                        std::string s = oss.str();
                        #pragma omp critical
                        {
                            u64 off = (u64)spill_out.tellp();
                            spill_out.write(s.data(), (std::streamsize)s.size());
                            sub_loc[fi] = {off, (u64)s.size()};
                        }
                        rd_status[ai] = 1;
                        ok_cnt++;
                        rd_enodes += en; rd_engs += eg;
                    } else {
                        rd_status[ai] = 2;
                        strag_cnt++;
                    }
                } catch (const std::exception& ex) {
                    #pragma omp critical
                    { std::cerr << "EXCEPTION in task " << fi << ": " << ex.what() << "\n" << std::flush; }
                    std::exit(9);
                }
                int dc = ++done_cnt;
                if (na >= 8 && (dc % std::max(1, na / 4) == 0 || dc == na)) {
                    double el = std::chrono::duration<double>(std::chrono::steady_clock::now() - ct0).count();
                    #pragma omp critical
                    {
                        std::cout << "    [Apex " << (ci + 1) << "/4 R" << rd << ": " << dc << "/" << na
                                  << " ok=" << ok_cnt.load() << " strag=" << strag_cnt.load()
                                  << " calls=" << (apex_calls + rd_calls.load())
                                  << " sec=" << el << "]\n" << std::flush;
                    }
                }
            }
            apex_calls += rd_calls.load();
            apex_enodes += rd_enodes.load();
            apex_engs += rd_engs.load();
            if (tiling_found) break;

            std::vector<int> next_active;
            for (int ai = 0; ai < na; ai++) {
                int fi = active_tasks[ai];
                if (rd_status[ai] == 1) {
                    solved[fi] = 1;
                    frontier[fi].clear(); frontier[fi].shrink_to_fit();
                } else if (rd_status[ai] == 2 && rd + 1 < max_rounds) {
                    Solver spS = baseS;
                    spS.set_sweep_leg(sp.sweep_leg);
                    spS.use_ng = false;
                    for (const auto& t : frontier[fi]) spS.push_tile(t);
                    frontier[fi].clear(); frontier[fi].shrink_to_fit();
                    int old_nf = (int)frontier.size();
                    int sub_root = build_prefix(spS, extra_d, ptree, frontier, frontier_pnode);
                    ptree[frontier_pnode[fi]] = ptree[sub_root];
                    if (ptree[sub_root].kind == 5) frontier_pnode[ptree[sub_root].task_id] = frontier_pnode[fi];
                    int new_nf = (int)frontier.size();
                    sub_loc.resize(new_nf, {0, 0});
                    solved.resize(new_nf, 0);
                    for (int nfi = old_nf; nfi < new_nf; nfi++) next_active.push_back(nfi);
                } else {
                    next_active.push_back(fi);
                }
            }
            active_tasks = std::move(next_active);
            if (!active_tasks.empty() && rd + 1 < max_rounds) {
                std::cout << "    [Apex " << (ci + 1) << "/4: split " << strag_cnt.load()
                          << " stragglers into " << active_tasks.size() << " child tasks for R" << (rd + 1) << "]\n" << std::flush;
            }
        }
        spill_out.close();

        double csec = std::chrono::duration<double>(std::chrono::steady_clock::now() - ct0).count();
        bool cref = active_tasks.empty() && !tiling_found;
        std::cout << "  Apex " << (ci + 1) << "/4 (" << sp.s1 << "," << sp.s2 << "," << sp.s3
                  << " leg=" << sp.sweep_leg << "): "
                  << (tiling_found ? "FOUND_TILING!!" : (cref ? "CERTIFIED" : "FAILED"))
                  << " calls=" << apex_calls << " sec=" << csec << "\n" << std::flush;
        if (!cref) { all_refuted = false; break; }

        std::vector<int> pmap(ptree.size(), -1);
        std::vector<PrefNode> compact_ptree;
        std::vector<int> used_fids;
        std::function<int(int)> dfs_p = [&](int nid) -> int {
            if (pmap[nid] != -1) return pmap[nid];
            PrefNode pn = ptree[nid];
            if (pn.kind == 0) { for (int i = 0; i < pn.nkids; i++) pn.kchild[i] = dfs_p(pn.kchild[i]); }
            else if (pn.kind == 5) {
                assert(solved[pn.task_id]);
                int new_tid = (int)used_fids.size();
                used_fids.push_back(pn.task_id);
                pn.task_id = new_tid;
            }
            int new_id = (int)compact_ptree.size();
            compact_ptree.push_back(pn);
            pmap[nid] = new_id;
            return new_id;
        };
        int compact_root = dfs_p(proot);
        int n_used = (int)used_fids.size();

        cert << "APEX " << sp.s1 << " " << sp.s2 << " " << sp.s3 << " "
             << compact_ptree.size() << " " << compact_root << " " << n_used << "\n";
        for (const auto& pn : compact_ptree) {
            if (pn.kind == 0) {
                cert << "B " << i128_to_str(pn.v.x) << " " << i128_to_str(pn.v.y) << " " << pn.v.p
                     << " " << (int)pn.d.k << " " << (int)pn.d.s << " " << pn.nkids;
                for (int i = 0; i < pn.nkids; i++) cert << " " << pn.kslot[i] << " " << pn.kchild[i];
                cert << "\n";
            } else if (pn.kind == 1) {
                cert << "C " << i128_to_str(pn.v.x) << " " << i128_to_str(pn.v.y) << " " << pn.v.p
                     << " " << (int)pn.d.k << " " << (int)pn.d.s << "\n";
            } else if (pn.kind == 2) {
                cert << "A " << i128_to_str(pn.v.x) << " " << i128_to_str(pn.v.y) << " " << pn.v.p
                     << " " << (int)pn.d.k << " " << (int)pn.d.s << " " << (int)pn.d2.k << " " << (int)pn.d2.s << "\n";
            } else if (pn.kind == 3) cert << "G " << pn.eidx << "\n";
            else if (pn.kind == 5) cert << "F " << pn.task_id << "\n";
        }
        std::ifstream spill_in(spill_path, std::ios::binary);
        std::vector<char> buf;
        for (int fid : used_fids) {
            auto [off, len] = sub_loc[fid];
            buf.resize(len);
            spill_in.seekg((std::streamoff)off);
            spill_in.read(buf.data(), (std::streamsize)len);
            cert.write(buf.data(), (std::streamsize)len);
        }
        spill_in.close();
        std::remove(spill_path.c_str());

        grand_calls += apex_calls;
        total_emitted_nodes += compact_ptree.size() + apex_enodes;
        total_emitted_ngs += apex_engs;
    }

    cert << "END\n";
    cert.close();
    double sec = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    std::cout << ">>> CERTIFICATE COMPLETE: " << (all_refuted ? "EXACT_CERTIFIED" : "FAILED")
              << " calls=" << grand_calls << " emitted_nodes=" << total_emitted_nodes
              << " emitted_ngs=" << total_emitted_ngs << " secs=" << sec << "\n";
    return all_refuted ? 0 : 1;
}
