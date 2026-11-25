# Wave 3 Frontier Push on Erdős Problem #634 (PPL 079): Complete Exact Certification & Independent Verification of $N = 332$ ($T_2(5, 6)$), Partial Certification of $N = 284$ ($T_2(2, 5)$), and 15-Branch Audit of $N = 280$

**Date:** 2026-11-25  
**Agent:** `prover-ppl079-frontier`  
**Prior Frontier:** Vico Bonfioli release v6.0 (`18 Nov 2026`, `27` undecided $N \le 1000$) + Denis Paliy (`DenisUkranian/erdos-634-tilings`, `19 Nov 2026`, settling **`N = 236`** impossible and **`N = 280`** tiled via `(90, 90, 140)` by `(5, 6, 9)`, reducing publicly undecided $N \le 1000$ to `25` with `#1` smallest publicly open integer **`284`**) + our independent Wave 2 exact-DAG confirmation of **`N = 236`** (`nil-commits/erdos634-n236`).

---

## Executive Summary

1. **FRONTIER SETTLEMENT — $N = 332$ (`¬ TileCount 332`, #2 Smallest Publicly Open Integer in Erdős #634):**
   - **Zero-Truncation 15-Branch Audit ([audit_frontier_15_leaves.py](audit_frontier_15_leaves.py)):** Verified exhaustively with zero parameter truncation that **14 of 15 branches** of the Laczkovich–Beeson–Bonfioli classification are rigorously closed for $N = 332 = 2^2 \cdot 83$ (in particular `NSq, R, HAr, A, B` via $83 \equiv 3 \pmod 4$; `E` via Theorem A; `F1, Iso, R8, S2, S3, S4`; `G(41, 42, g=2)` via Theorem D' since $2 \le 41$; and `theta_2(41, 42)` via Bonfioli's `Prop theta` `S5wChk` since $teb = 6806 < 42^3 = 74088$), leaving **`T_2(5, 6)`** (isosceles triangle with legs `432`, base `830`, apex $3\alpha$, tile `(30, 11, 36)`) as the **unique surviving branch**.
   - **Adaptive Multi-Round Straggler-Splitting Exact Prover ([exact_tiler_adaptive.cpp](exact_tiler_adaptive.cpp)):** Eliminated the 2 single-thread straggler tasks that blocked Wave 2 on `Apex 3/4` by introducing in-place recursive prefix re-splitting (`fast_cap = 150,000`, `extra_d = 4`, up to 6 rounds) producing 100% standard `ECERT_V1` certificates. Validated first on `T_2(2, 3)` ($N = 92$, `18,025` calls, `0.87s`, verified `PASS` in `0.15s`).
   - **Complete Unconditional 4-Apex Exact Proof Certificate (`cert_T2_5_6_N332.ecert`, excluded from git):**
     - **File:** `cert_T2_5_6_N332.ecert` (`594,287,329` bytes = `566.76 MiB`)
     - **SHA-256:** `0651E39102ABFAD757F02EBB967FF8CDBB7B5AE601F7637493760C985EE970B9`
     - **Generation:** `19,627,017` solver calls, `17,550,285` emitted DAG nodes, `1,558,706` nogoods in `2,959.68s` across all 4 reflection-reduced apex cases (zero external assumptions, `thmB=0`, zero floats, zero cache eviction).
   - **Independent Zero-Float Verification + Hardened Overflow Traps + Negative Controls:**
     - **Hardened Overflow-Trapped C++ Verifier ([verify_ecert_hardened.cpp](verify_ecert_hardened.cpp), `g++ 13.3.0`, Ubuntu 24.04 on `rh-lean-hub`):** **100% PASS** across ALL 4 apexes in `1,826.34s` (independent audit reproduction: `1,866.08s`): `44,841,481` total verified nodes (`44,840,088` DAG nodes + `1,393` non-`F` prefix nodes; `16,944,521` branches, `13,002,663` corner leaves, `67,454` angle leaves, `732,073` gap leaves, `14,094,770` nogood refs); `1,558,706` topologically verified nogoods; **`__int128 overflows=0`**, runtime $\mathbb{Q}[\zeta]$ `max_p = 24`, `init_peak=79.18%` of `INT128_MAX`, **`post_init_peak=2.62e-07` of `INT128_MAX`**.
     - **Baseline Zero-Float Zero-Trig C++ Verifier (`verify_ecert.exe`):** **100% PASS** across ALL 4 apexes in `224.098s` (`44,840,088` DAG nodes, `1,558,706` nogoods).
     - **`__int128` Overflow Headroom Audit ([audit_ecert_headroom_and_pycheck.py](audit_ecert_headroom_and_pycheck.py)):** Scanned every vertex in `cert_T2_5_6_N332.ecert`: stored-vertex `max_p = 15` (distinct from the C++ runtime $\mathbb{Q}[\zeta]$ ceiling `max_p = 24`), `max |x|, |y| = 109,859,760,456,041`, conservative `orient_exact` product bound `2.437e+30` vs `i128_max = 1.701e+38` (**headroom ratio `1.432e-08`**, ~70 million × safety margin).
     - **Negative Controls (`5/5` rejected by `verify_ecert_hardened.cpp` on `rh-lean-hub`, `EXIT_CODE=1`):** `corrupt_mode = 1` (dropped branch child, `119.06s`), `corrupt_mode = 2` (corrupted leaf, `120.99s`), `corrupt_mode = 3` (corrupted nogood, `121.70s`), `corrupt_mode = 4` (malformed/bounds corruption, `1.74s`), and `corrupt_mode = 5` (missing apex `(3,2,3)`, `1731.95s`).
   - **Honest Scope:** Combined with the 15-branch classification (14 branches closed analytically; 15th branch `T_2(5, 6)` closed by our independently verified zero-float overflow-trapped `.ecert` certificate), this settles **$N = 332$ as impossible (`¬ TileCount 332`)**, reducing the publicly undecided count $\le 1000$ from `25` to **`24`** (or `26 → 25` relative to Bonfioli v6.0 + `erdos634-n236` alone). *(Note: Verified by independent zero-float overflow-trapped C++ verifier with 5/5 negative controls; not Lean-kernel verified.)*

2. **Substantial Progress on $N = 284$ (`T_2(2, 5)`, Unique Surviving Branch — 2 of 4 Apexes Certified; Remains #1 Smallest Publicly OPEN):**
   - Confirmed `T_2(2, 5)` (tile `(10, 21, 25)`, legs `250`, base `284`, Theorem C: only 2 base words `(5, 4, 6)` and `(0, 4, 8)`) is the **unique surviving branch** of $N = 284 = 2^2 \cdot 71$.
   - **Certified `Apex 1/4 (2, 2, 2)`** (`1,424,525` calls, `444.56s`, `156` subproofs) and **`Apex 2/4 (2, 2, 3)`** (`1,411,009` calls, `546.34s`, `277` subproofs), preserved locally in `cert_T2_2_5_N284_apex12.ecert` (`71,623,683` bytes, excluded from git).
   - `Apex 3/4 (3, 2, 2)` completed `603/804` R2 tasks (`23.32M` calls) before local 11 GB RAM OOM; base-sweep `a3_sweep=1` showed promising speed (`118/236` tasks in `36s`). Built disk-spilling low-memory prover [exact_tiler_lowmem.cpp](exact_tiler_lowmem.cpp) (`< 2 GB` RAM, spill-to-disk subproofs). Subsequent remote attempt on `rh-lean-hub` hit the final-round `20,000,000`-call straggler cap on `Apex 3/4`, so **`$N = 284$ remains OPEN`**.

3. **Complete 15-Branch Decomposition & Independent Diagnostic Attack on $N = 280$ (Settled TILED by Denis Paliy, 19 Nov 2026):**
   - **Literature settlement:** **Denis Paliy** (`DenisUkranian/erdos-634-tilings`, 19 Nov 2026) exhibited an explicit 280-tile dissection of `(90, 90, 140)` by `(5, 6, 9)` (consistent with the third surviving branch `alpha_2(2, 3)` below).
   - **Independent Exhaustive 15-Leaf Audit ([audit_frontier_15_leaves.py](audit_frontier_15_leaves.py)):** Independently confirmed **12 of 15 branches are closed** for $N = 280 = 2^3 \cdot 5 \cdot 7$, leaving **EXACTLY 3 candidate branches**:
     1. **`Eq60(7, 40, 37, m=1, X=280)`** ($\gamma = \pi/3$ tile `(7, 40, 37)`, equilateral side `280`; unique single $\gamma$-tile per corner; only 6 boundary words; all 3 pairwise differences `3, 30, 33 ∉ ⟨7, 37, 40⟩`).
     2. **`F1(33, 7, 37, s=1)`** ($\gamma = 2\pi/3$ tile `(33, 7, 37)`, sides `(259, 231, 280)`, angles $(\alpha, \pi/3, \alpha+2\beta)$; passes exact signed-direction parity $f_+ = -252 = -4(c+a-b)$ and $f_- = 770 = 70(c+b-a)$; only 5/6/7 boundary words).
     3. **`alpha_2(2, 3)`** (Group-1 tile `(6, 5, 9)`, legs `90`, base `140`, angles $(\alpha, \alpha, \alpha+2\beta)$; paired with Bonfioli's **`theta_6(2, 3)`** at $N = 180$ via $\alpha_2(2, 3) = 10\tau(2,3) \cup \theta_6(2, 3)$).
   - **Internal Diagnostic Engines & Calibration Controls *(not bundled in this repo)*:**
     - `exact_f1_eq60.cpp` ($\mathbb{Z}[\frac{1}{c}, \omega]$ exact prover with necessary-and-sufficient $(A, B) = (m, m + 2\Delta k)$ angle-sum pruning for $\gamma = \pi/3$): refuted calibration controls **`Eq60(3, 8, 7)` at $X = 24$** (`14` calls, `0.77 ms`) and **`F1(3, 5, 7, s=1)` at $N = 40$** (`927` calls, `0.10s`).
     - `exact_group1_probe.cpp` ($\mathbb{Q}[\zeta]$ Group-1 `THETA`/`ALPHA` prover): refuted **`theta_3(1, 2)`** ($N = 27$, `324` calls, `0.032s`) and found Beeson's 48-tile tiling of **`theta_4(1, 2)`** (`139` calls, `0.018s`).
     - `hunt_theta_alpha.cpp` (macro-block $K\tau$ + randomized edge-matching hunter): showed **`theta_6(2, 3)`** misses Bonfioli's Band Theorem at `(M, k, n, s) = (3, 3, 2, 5)` exclusively on `(c)` $2 \nmid (6-5)$ and `(e)` $3 \mid 6$, reaching `173/180` tiles (`172/180` across all macro-seeds $K = 5..9$), while `alpha_2(2, 3)` reached `271/280` tiles (short of Paliy's full 280-tile `(5, 6, 9)` solution).

4. **Complete Zero-Truncation 15-Branch Map of All 27 Undecided $N \le 1000$:**
   - Mapped every single undecided $N \le 1000$ from Bonfioli v6.0, identifying all single-branch $T_M(e, f)$ targets and ranking boundary-word rigidity (highlighting `N = 423 = T_3(1,4)`, `N = 552 = T_2(3,7)`, `N = 732 = T_2(3,8)`, `N = 908 = T_2(4,9)` as the tightest next targets).

---

## 1. Detailed Per-Apex Breakdown for $N = 332$ (`T_2(5, 6)`)

| Apex Case $(s_1, s_2, s_3)$ | Sweep Leg | Adaptive Rounds | Subproofs | Solver Calls | Gen Time (32T) | Zero-Float C++ Verify (`verify_ecert`) |
|---|---|---:|---:|---:|---:|---|
| `Apex 1/4 (2, 2, 2)` | $OA$ ($b$-leg) | R0–R2 (29→22→37) | 85 | 2,147,359 | 361.19s | **100% PASS** |
| `Apex 2/4 (2, 2, 3)` | $OA$ ($b$-leg) | R0–R2 (29→14→42) | 81 | 2,950,203 | 419.29s | **100% PASS** |
| `Apex 3/4 (3, 2, 2)` | $OB$ ($c$-leg) | R0–R3 (45→71→199→80) | 374 | 13,292,556 | 1,986.01s | **100% PASS** |
| `Apex 4/4 (3, 2, 3)` | $OB$ ($b$-leg) | R0–R1 (45→9) | 53 | 1,236,899 | 192.13s | **100% PASS** |
| **TOTAL** | — | — | **593** | **19,627,017** | **2,959.68s** | **100% PASS (`44,840,088` DAG nodes / `44,841,481` total nodes, `1,558,706` nogoods, `224.10s` baseline)** |

**Independent Verification Summary (`cert_T2_5_6_N332.ecert`):**
- **File size:** `594,287,329` bytes (`566.76 MiB`)
- **SHA-256:** `0651E39102ABFAD757F02EBB967FF8CDBB7B5AE601F7637493760C985EE970B9`
- **Breakdown of verified nodes:** `44,841,481` total (`44,840,088` DAG nodes [`16,944,521` branches, `13,002,663` corner leaves, `67,454` angle leaves, `732,073` gap leaves, `14,094,770` nogood refs] + `1,393` non-`F` prefix nodes).
- **Overflow headroom:** stored-vertex `max_p = 15` (vs runtime C++ $\mathbb{Q}[\zeta]$ ceiling `max_p = 24`), `max |x|, |y| = 109,859,760,456,041`, conservative `orient_exact` product `2.437e+30` vs `i128_max = 1.701e+38` (ratio `1.432e-08`, zero overflow; hardened verifier `init_peak = 79.18%`, `post_init_peak = 2.62e-07` of `INT128_MAX`).
- **Negative controls (`5/5` rejected by `verify_ecert_hardened.cpp`, `EXIT_CODE=1`):** `corrupt_mode = 1` (`119.06s`), `corrupt_mode = 2` (`120.99s`), `corrupt_mode = 3` (`121.70s`), `corrupt_mode = 4` (`1.74s`), `corrupt_mode = 5` (`1731.95s`).

---

## 2. Exact 15-Branch Map of All 27 Bonfioli v6.0 Undecided $N \le 1000$

Generated with zero parameter truncation by [audit_frontier_15_leaves.py](audit_frontier_15_leaves.py):

| $N$ | Surviving Branch(es) | Base Words ($z \ge f$) / Notes | Status |
|---:|---|---|---|
| **236** | `T_2(4, 5)` | Unique branch | **SETTLED IMPOSSIBLE** (Denis Paliy 19 Nov 2026; Wave 2 `erdos634-n236` independent confirmation) |
| **280** | `Eq60(7,40,37,m=1)`, `F1(33,7,37,s=1)`, `alpha_2(2,3)` | 3 branches (`theta_6(2,3)` reaches `173/180`, `alpha_2` `271/280` in diagnostic search) | **SETTLED TILED** (Denis Paliy 19 Nov 2026: `(90, 90, 140)` by `(5, 6, 9)`) |
| **284** | `T_2(2, 5)` | Unique branch; Theorem C (2 base words `(5,4,6), (0,4,8)`) | **OPEN (#1 smallest publicly open; Apex 1–2 certified; Apex 3–4 open)** |
| **332** | `T_2(5, 6)` | Unique branch | **SETTLED IMPOSSIBLE (This Work — `cert_T2_5_6_N332.ecert` PASS!)** |
| **351** | `G(5, 8, g=3)`, `T_3(3, 4)` | 2 branches | OPEN |
| **423** | `T_3(1, 4)` | Unique branch; 3 base words `(8,3,4),(4,3,5),(0,3,6)`, $2Me/f=1.50$ | OPEN (high-priority next target) |
| **444** | `T_2(6, 7)` | Unique branch | OPEN |
| **524** | `T_2(4, 7)` | Unique branch; 8 base words | OPEN |
| **531** | `T_3(4, 5)` | Unique branch | OPEN |
| **552** | `T_2(3, 7)` | Unique branch; Theorem C (2 base words `(7,6,9), (0,6,12)`) | OPEN (high-priority next target) |
| **594** | `T_3(3, 5)` | Unique branch | OPEN |
| **644** | `alpha_2(3, 4)` | Unique branch | OPEN |
| **668** | `T_2(5, 8)` | Unique branch | OPEN |
| **716** | `T_2(8, 9)` | Unique branch | OPEN |
| **732** | `T_2(3, 8)` | Unique branch; Theorem C (2 base words `(8,6,9), (0,6,12)`), $2Me/f=1.50$ | OPEN (high-priority next target) |
| **747** | `T_3(5, 6)` | Unique branch | OPEN |
| **816** | `G(7, 10, g=4)` | Unique branch | OPEN |
| **840** | `Eq60(24,35,31,m=1)`, `F1(11,24,31,s=1)` | 2 paired Group-2 branches | OPEN |
| **855** | `G(7, 12, g=3)` | Unique branch | OPEN |
| **876** | `T_2(9, 10)` | Unique branch | OPEN |
| **880** | `Eq60(16,55,49,m=1)`, `F1(39,16,49,s=1)` | 2 paired Group-2 branches | OPEN |
| **908** | `T_2(4, 9)` | Unique branch; Theorem C (2 base words `(9,8,12), (0,8,16)`) | OPEN (high-priority next target) |
| **912** | `G(8, 11, g=4)` | Unique branch | OPEN |
| **924** | `Eq120(7, 33, 37, m=2)` | Unique branch ($X = 462$) | OPEN |
| **927** | `W_3(5, 8)` | Unique branch (bottom-rung $W_3$) | OPEN |
| **944** | `T_4(4, 5)` | Unique branch | OPEN |
| **999** | `T_3(6, 7)` | Unique branch | OPEN |

---

## 3. Reproducible Repository Artifacts & Remaining Open Frontier Work

### Included in This Repository
- [exact_tiler_adaptive.cpp](exact_tiler_adaptive.cpp) — 32-thread adaptive straggler-splitting `ECERT_V1` certificate generator.
- [exact_tiler_lowmem.cpp](exact_tiler_lowmem.cpp) — Disk-spilling low-memory adaptive `ECERT_V1` generator.
- [verify_ecert_hardened.cpp](verify_ecert_hardened.cpp) — Zero-float, zero-trig, `__int128` overflow-trapped C++ verifier with negative-control corruption modes `1..5` (already passed `corrupt_mode = 0` and rejected `5/5` corruption modes on `cert_T2_5_6_N332.ecert`).
- [verify_ecert.py](verify_ecert.py) — Standalone pure-Python `fractions.Fraction` cross-verifier.
- [audit_frontier_15_leaves.py](audit_frontier_15_leaves.py) — Zero-truncation 15-branch classification audit across all 27 Bonfioli v6.0 undecided $N \le 1000$.
- [audit_ecert_headroom_and_pycheck.py](audit_ecert_headroom_and_pycheck.py) — Streaming `__int128` overflow headroom scanner for large `.ecert` files.

### Excluded Large Certificates & Internal Diagnostic Prototypes *(Not Bundled in This Repo)*
- `cert_T2_5_6_N332.ecert` — Complete 4-apex zero-float exact proof certificate for `T_2(5, 6)` ($N = 332$, `594.29 MB`, SHA-256 `0651E391...`; excluded from git, reproducible via `exact_tiler_adaptive`).
- `cert_T2_2_5_N284_apex12.ecert` — Partial certificate (`Apex 1/4` and `Apex 2/4`) of `T_2(2, 5)` ($N = 284$, `71.62 MB`; local research artifact).
- `exact_f1_eq60.cpp`, `exact_group1_probe.cpp`, `hunt_theta_alpha.cpp` — Internal diagnostic prototypes used for calibration checks and Group-1/2 frontier exploration.

### Remaining Open Frontier Work
1. Run an optional dual-language pure-Python `verify_ecert.py` spot-check on `cert_T2_5_6_N332.ecert` (e.g., `Apex 4/4`) alongside the completed C++ `verify_ecert_hardened.cpp` verification and `5/5` negative controls.
2. Complete `N = 284` (`T_2(2, 5)`) `Apex 3/4` and `Apex 4/4` (e.g., via `a3_sweep=1` / deeper prefix splitting beyond the 20M-call round cap), merge with `Apex 1/4–2/4`, and verify cleanly.
3. Target the remaining tightest single-branch open cases (`N = 423` / `T_3(1, 4)`, `N = 552` / `T_2(3, 7)`, `N = 732` / `T_2(3, 8)`, `N = 908` / `T_2(4, 9)`), coordinated against Paliy's public ledger (`DenisUkranian/erdos-634-tilings`).
