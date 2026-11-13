# Evaluation output data

This directory contains the experimental outputs used for the evaluation.

| Directory | Contents |
|---|---|
| `timing/` | Multi-alignment timing campaign: four code alignments (32, 64, 128, 256), two builds per configuration, raw process outputs, run metadata, extracted observations, and statistical summaries. |
| `allocation-and-build/` | Earlier fixed-alignment campaign supplying allocation and build-cost measurements: raw process outputs, allocation-only measurements, extracted allocation data, native-image build logs, and follow-up runs. |
| `reference-tables/` | Saved result CSVs, including the earlier campaign tables from which allocation and build-cost values are reused. |

Timing comes from the multi-alignment campaign. Allocation and build costs come
from the earlier fixed-alignment campaign.

## Finding a benchmark

`BENCHMARKS.tsv` maps internal run names to the names used by the paper.
Original internal names and run labels are retained in filenames and outputs.

Raw process files are under `out/<run-label>/raw/`. Follow-up allocation campaign
runs are also under `allocation-and-build/fu/`. Native-image build outputs are
under `allocation-and-build/bld/<run-label>/work/build-*/`.
Allocation-only outputs are under `allocation-and-build/alloc/`.

`timing/welch-report.tsv` records the selected timing source for each table cell.
The reference tables record the allocation sources. Original, follow-up, rebuild,
pilot, and control runs provide supporting evidence.
