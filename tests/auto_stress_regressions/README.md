# Auto Stress Regressions

This folder stores minimized `.lrl` repros promoted from recurring failures found by:

- `scripts/backend_auto_stress.py --promote-recurring`

Each file is compiled with `--backend auto` and executed by
`cli/tests/auto_stress_regressions.rs`.
