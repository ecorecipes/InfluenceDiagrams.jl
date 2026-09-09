"""Use the common fail-closed checker from the existing own-prover BN dependency."""

from pathlib import Path
import runpy

runpy.run_path(
    str(Path(__file__).resolve().parents[3] / "BayesianNetworks.jl/proofs/scripts/audit.py"),
    run_name="__main__",
)
