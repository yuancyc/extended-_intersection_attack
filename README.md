# Extended Intersection Attack on the UOV Family — experiment code

SageMath scripts for the experiments of *An Extended Intersection Attack on the
UOV Family*: toy-instance measurements of the reduced system and complexity
estimates for the third-round parameters.

## Contents

| File | What it does |
|---|---|
| `uov_toy_independence.sage` | Dependent relations of the $t$-block system, symmetric forms; 21 parameter sets, control run, repeated draws |
| `uov_toy_attack_procedure.sage` | Geometry and procedure of the attack: dimensions, intersection, success rate, returned solution |
| `snova_toy_independence.sage` | Same for the ordered forms (SNOVA), plus a left-kernel analysis |
| `snova_benchmark.sage` | End-to-end attack on a toy SNOVA system (M4GB) |
| `{mayo,qr-uov,snova}_complexity_calculation.sage` | Cost model on MAYO, QR-UOV (lifted), SNOVA (both equivalences) |
| `m4gb/` | Vendored solver sources (M4GB, OpenF4); must be built |

The complexity scripts print $N$, $M$, guess, $D$, $k'$, $C_{\mathrm{FXL}}$,
total and $\Delta_1$, $\Delta_2$.

## Requirements

* SageMath ≥ 9.3 (tested 9.3 and 10.8); no extra package, no network.
* M4GB for `snova_benchmark.sage` only: autotools and a C++11 compiler.

## Environment

| Component | Specification |
|---|---|
| Platform | VMware virtual machine |
| Operating system | Ubuntu 24.04.3 LTS, 64-bit; kernel 6.17.0-23-generic; GNOME 46 on Wayland |
| CPU | AMD Ryzen 7 5800H, 8 vCPUs |
| Memory | 11.6 GiB |
| Disk | 85.9 GB |
| Software | SageMath 10.8 |

Times in the paper are wall-clock on this machine; the Sage measurements are
exact, and only the M4GB times depend on it.

## Usage

```bash
sage uov_toy_independence.sage          # ~20 s
sage uov_toy_attack_procedure.sage      # minutes
sage mayo_complexity_calculation.sage   # seconds
sage qr-uov_complexity_calculation.sage # seconds
sage snova_complexity_calculation.sage  # seconds
sage snova_toy_independence.sage        # minutes to tens of minutes
sage snova_benchmark.sage               # needs ./m4gb/solver.sh
```

Run from this directory: the scripts write temporary files here, and
`snova_benchmark.sage` expects the solver at `./m4gb`.

## Building M4GB

```bash
cd m4gb/m4gb-master && autoreconf --install && ./configure && make check
```

`solver.sh` has to end up in `./m4gb`, because `snova_benchmark.sage` calls
`"$M4GB_HOME/solver.sh"` with `M4GB_HOME=./m4gb`; the sources here sit one level
deeper, which is why `m4gb/log.txt` records such an error.

## Notes

* Toy instances are deliberately small and are not models of real parameters.
* Seeds are fixed; about $1/q$ of instances are degenerate for the freshness
  test, and `uov_toy_attack_procedure.sage` skips them.
* `m4gb/log.txt` is a stale log; `snova_benchmark.sage` writes
  `_bench_m4gb.in/.out` into the working directory.
