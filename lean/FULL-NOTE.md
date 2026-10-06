# What Lean checked, and what it did not

File: lean/Full.lean. Lean 4.34.1, no Mathlib, no sorry, exit status 0.

Checked:
- process_disagreement, for every number of parties on bits: a process function cannot have two distinct output strings that agree in w wherever they differ.
- extend_left_inv and extend_right_inv: the source-and-sink map (o, e) |-> (w(o) XOR e, o) is a bijection, with the inverse written down. That is the permutation unitary on the computational basis.
- hadamard_rows_orthogonal: the integer Hadamard rows (1,1) and (1,-1) have dot product 0.

Not checked:
- The gram contraction against a general complex local unitary.
- Stinespring, and the instrument condition as a theorem about completely positive maps.
- Alphabets other than bits.

Those three are the written proof. They are not in the kernel.
