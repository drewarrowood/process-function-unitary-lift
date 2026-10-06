# Kernel check of the cancellation

Lean 4.34.1, file lean/Cancellation.lean, no Mathlib, no sorry. Compile exit status 0.

The kernel accepted exclusivity: if w is a process function on Fin n to Bool and s differs from s', some party disagrees in the output bit and agrees in the function value. The proof builds the local intervention that would otherwise fix both strings.

The kernel accepted the gram cancellation: orthonormal local rows plus exclusivity give a source-to-sink entry of 1 on the diagonal and 0 off it. Off the diagonal the witness party contributes the inner product of two distinct rows.

Not checked, because not claimed: the identification of that gram entry with the concrete contraction of U|o, e> = |w(o)+e, o> against complex local unitaries. Row orthonormality is the RowFactor.ortho hypothesis.

The long article is paper/lift.html. The short PDF at paper/lift.pdf is not this version.
