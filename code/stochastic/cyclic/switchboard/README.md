# Switchboard (family C) — Oct 22 2026 (lift.md H.8, H.9, Appendix I)
- pauli.py: Pauli form of Lemma H.7.1; numerical cross-check on stored solutions (H.8.1).
- pauli_exact.py / pauli_exact.log: exact (python-flint, rational) equality of the two kernels for every D.
- push.py: minimise the exact Pauli residual R subject to facet-82 violation >= v at the best source state.
  jobs.txt/curve.jsonl (v = 0.01..0.3, 84 runs), jobs2.txt/curve2.jsonl (v = 0.5..0.9, 24 runs). sb_*.npy endpoints.
