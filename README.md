# Erdős Problem #634 — Exact-Arithmetic Refutation of $T_2(5, 6)$ ($N = 332$)

This repository contains the adaptive multi-threaded exact-arithmetic $\mathbb{Q}[\zeta]$ refutation prover, independent overflow-trapped verifier, and zero-truncation 15-branch classification audit settling $T_2(5, 6)$ ($N = 332$) for Erdős Problem #634 (congruent triangle dissections).

## Scope and Limitations

- **Full Erdős Problem #634 remains open.** This repository settles $N = 332$ (previously undecided in Vico Bonfioli's v6.0 release `ElVec1o/erdos634_primes_and_N200`, 18 Nov 2026), reducing the undecided count $\le 1000$ from `26` (after $N = 236$ in `nil-commits/erdos634-n236`) to `25`.
- **Not Lean-kernel verified:** The refutation of $T_2(5, 6)$ is an **exact-arithmetic computer-certified refutation (`ECERT_V1`)**, checked independently from scratch by our zero-float, zero-trig, `__int128` overflow-trapped C++ verifier (`verify_ecert_hardened.cpp`, with negative controls rejecting corrupted proofs). It has **not** been replayed inside the Lean 4 kernel.
- **Dependence on classification:** Concluding $\neg\operatorname{TileCount}(332)$ from the refutation of $T_2(5, 6)$ depends on the Laczkovich–Beeson–Bonfioli 15-branch classification of congruent triangle dissections (`audit_frontier_15_leaves.py` closes 14 of 15 branches analytically for $N = 332$, leaving $T_2(5, 6)$ as the unique surviving branch).

---

## Repository Contents

| File | Description |
|---|---|
| `exact_tiler_adaptive.cpp` | 32-thread exact $\mathbb{Q}[\zeta]$ prover with adaptive multi-round straggler splitting (`ECERT_V1` output) |
| `exact_tiler_lowmem.cpp` | Disk-spilling low-memory variant of the adaptive `ECERT_V1` prover |
| `verify_ecert_hardened.cpp` | Independent zero-float, zero-trig, `__int128` overflow-trapped C++ verifier (generalized for $f \ge 6$ via dynamic `max_pow_f`, with negative-control modes `1..5`) |
| `verify_ecert.py` | Independent pure-Python arbitrary-precision `fractions.Fraction` cross-verifier |
| `audit_frontier_15_leaves.py` | Zero-truncation 15-branch Laczkovich–Beeson–Bonfioli classification audit across all 27 undecided $N \le 1000$ |
| `audit_ecert_headroom_and_pycheck.py` | Streaming `__int128` coordinate & headroom scanner for large `.ecert` files |
| `REPORT.md` | Full technical report (including partial progress on $N = 284$ and 3-branch analysis of $N = 280$) |
| `LICENSE` | MIT License |

---

## Reproducing `cert_T2_5_6_N332.ecert` (Excluded from Git)

The `594.29 MB` certificate file `cert_T2_5_6_N332.ecert` is excluded from git to keep the repository lightweight. Regenerate it directly from `exact_tiler_adaptive.cpp`:

```bash
g++ -O3 -march=native -fopenmp -std=c++17 exact_tiler_adaptive.cpp -o exact_tiler_adaptive

# N = 332, T_2(5, 6) (~49.3 min on 32 threads):
./exact_tiler_adaptive 5 6 2 cert_T2_5_6_N332.ecert 16 10 150000 6 4 15 2

# Calibration control T_2(2, 3) [N = 92] (< 1s):
./exact_tiler_adaptive 2 3 2 test_N92.ecert 16 6 200 4 3 15 2
```

### Reference Certificate Details

- **Target:** $T_2(5, 6)$ (legs `432`, base `830`, apex $3\alpha$, tile `(30, 11, 36)`, $N = 332$)
- **File size:** `594,287,329` bytes (`566.76 MiB`)
- **SHA-256:** `0651E39102ABFAD757F02EBB967FF8CDBB7B5AE601F7637493760C985EE970B9`
- **Generation telemetry:** `19,627,017` solver calls, `17,550,285` emitted DAG nodes, `1,558,706` nogoods (`2,959.68s` on 32 threads).

---

## Independent Verification

Compile the hardened overflow-trapped verifier with zero warnings:

```bash
g++ -O3 -std=c++17 -Wall -Wextra verify_ecert_hardened.cpp -o verify_ecert_hardened
./verify_ecert_hardened cert_T2_5_6_N332.ecert 0
```

### Verbatim Hardened Verification Output (`g++ 13.3.0`, Ubuntu 24.04)

```text
Verifying ECERT_V1 for T_2(5,6) N=332 (corrupt_mode=0)...
  Apex (2,2,2): 100% VERIFIED (subproofs=85)
  Apex (2,2,3): 100% VERIFIED (subproofs=81)
  Apex (3,2,2): 100% VERIFIED (subproofs=374)
  Apex (3,2,3): 100% VERIFIED (subproofs=53)
>>> 100% INDEPENDENT EXACT VERIFICATION PASSED! <<<
  Target: T_2(5,6) [N=332]
  Verified nodes=44841481 (dag=44840088, prefix_nonF=1393; branches=16944521, corner_leaves=13002663, angle_leaves=67454, gap_leaves=732073, ng_refs=14094770)
  Verified nogoods=1558706
  __int128 overflows=0, max_p=24
  __int128 headroom: init_peak=134713546244127343440523266742756048896 (79.18% of INT128_MAX), post_init_peak=44643604652950781670001409064960 (2.62e-07 of INT128_MAX)
  Elapsed: 1826.34s
```

### Negative-Control Rejection

- `corrupt_mode = 1` (dropped branch child): `FAIL: prefix/subproof failed for apex (2,2,2)` (`102.81s`, `EXIT_CODE=1`)
- `corrupt_mode = 2` (corrupted leaf): `FAIL: prefix/subproof failed for apex (2,2,2)` (`103.48s`, `EXIT_CODE=1`)
- Unhardened baseline verifier (`verify_ecert` on Windows): `PASS` across all 4 apexes (`224.10s`, `44,840,088` DAG nodes, `1,558,706` nogoods; `corrupt_mode=1,2` rejected in `16.25s`, `16.26s`).

### 15-Branch Classification Audit

```bash
python3 audit_frontier_15_leaves.py
```

Confirms `TOTAL SURVIVING BRANCHES FOR N=332: ['T_2(5,6)']` (14 of 15 leaves closed analytically, including `G(41, 42, g=2)` by Theorem D' and `theta_2(41, 42)` by `Prop theta` `S5wChk` since $teb = 6806 < 42^3 = 74088$).
