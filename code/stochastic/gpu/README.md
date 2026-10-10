# GPU purification search

`gpusearch.py` runs a batched L-BFGS search for AFNB purifications using the reduced Theorem 4 from paper Appendix C.2. Each orbit gets a checkpoint, `results/<name>.json`, recording best residual, restarts done, time and status. Runs resume from these files. If the float64-verified residual is below 1e-10, the coefficients are saved to `results/<name>_purification_coeffs.npy`.

Validation on CPU (torch 2.14):
- Lugano: residual 1.9e-18 (found).
- E_ex1: stalls at 79.676 (matches the exact non-purifiability certificate).

Run: `pip install -r requirements.txt; ./run_sweep.sh` for all 49 open orbits in `open_orbits.txt`, or `./run_sweep.sh 8 10`.
