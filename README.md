# Extended Intersection Attack on the UOV Family — experiment code

Scripts that produce the experiments of *An Extended Intersection Attack on the
UOV Family*: the toy-instance measurements of the reduced system (Section 3.2)
and the complexity tables for the third-round parameters (Section 4).

## Contents

| File | What it does | Paper |
|---|---|---|
| `uov_toy_independence.sage` | Rank and number of dependent relations of the $t$-block system, symmetric convention (UOV, MAYO, QR-UOV); 21 parameter sets over $\mathbb{F}_{16}$ and $\mathbb{F}_{127}$, a control run with $\mathcal{W}$ outside $\operatorname{span}\{B_k\}$, and repeated draws. | Table 2, symmetric |
| `uov_toy_attack_procedure.sage` | Geometry and procedure of Algorithm 1 on the same instances: dimensions, the relations on $\mathcal{O}$, intersection dimension, draws and success rate of the freshness test, and the returned solution. | Table 3 |
| `snova_toy_independence.sage` | Same rank measurement for the ordered convention (SNOVA), with a left-kernel analysis; $\ell=2,\dots,5$ and $t=\ell+1$. | Table 2, ordered |
| `snova_benchmark.sage` | End-to-end attack: builds the toy SNOVA system, solves it with M4GB, verifies the solution. | Table 4 |
| `mayo_complexity_calculation.sage` | Cost model on the four MAYO parameter sets. | Table 5 |
| `qr-uov_complexity_calculation.sage` | Cost model on QR-UOV, lifted representation. | Table 6 |
| `snova_complexity_calculation.sage` | Cost model on SNOVA, both equivalences. | Table 7 |
| `m4gb/` | Vendored solver sources — M4GB (<https://github.com/cr-marcstevens/m4gb>) and OpenF4; must be built. | — |

The complexity scripts print $N$, $M$, the guess exponent, $D$, $k'$,
$C_{\mathrm{FXL}}$, the total cost and $\Delta_1$, $\Delta_2$. Figure 1 follows
from the cost formulas of the paper and has no script here.

## Requirements

* SageMath ≥ 9.3 (tested with 9.3 and 10.8); no extra Python package, no network.
* M4GB for `snova_benchmark.sage` only: autotools and a C++11 compiler.

## Environment

| Component | Specification |
|---|---|
| Platform | VMware virtual machine (VMware Virtual Platform) |
| Operating system | Ubuntu 24.04.3 LTS, 64-bit; kernel 6.17.0-23-generic; GNOME 46 on Wayland |
| CPU | AMD Ryzen 7 5800H with Radeon Graphics, 8 vCPUs |
| Memory | 11.6 GiB |
| Disk | 85.9 GB |
| Software | SageMath 10.8 |

Running times in the paper are wall-clock times on this machine. The Sage
measurements are exact and machine-independent; only the M4GB times of Table 4
are not.

## Usage

Run the scripts from this directory: they write temporary files here, and
`snova_benchmark.sage` looks for the solver at `./m4gb`.

```bash
sage uov_toy_independence.sage          # ~20 s
sage uov_toy_attack_procedure.sage      # a few minutes
sage mayo_complexity_calculation.sage   # seconds
sage qr-uov_complexity_calculation.sage # seconds
sage snova_complexity_calculation.sage  # seconds
sage snova_toy_independence.sage        # minutes to tens of minutes
sage snova_benchmark.sage               # requires ./m4gb/solver.sh
```

## Building M4GB

```bash
cd m4gb/m4gb-master
autoreconf --install
./configure
make check
```

`snova_benchmark.sage` calls `"$M4GB_HOME/solver.sh"` with `M4GB_HOME=./m4gb`, so
`solver.sh` has to end up in `./m4gb`; here the sources sit one level deeper
(`m4gb/m4gb-master/`), which is why `m4gb/log.txt` holds a
`solver.sh: No such file or directory` error from an earlier run.

## Notes

* The toy instances are deliberately small — exact linear algebra and a Gröbner
  basis have to finish — and are not models of real parameter sets.
* Seeds are fixed in the scripts. About $1/q$ of random instances are degenerate
  for the freshness test; `uov_toy_attack_procedure.sage` detects and skips them.
* `m4gb/log.txt` is a stale log and can be deleted; `snova_benchmark.sage` writes
  `_bench_m4gb.in/.out` into the working directory.
