# Finite global image, output range, prefix normalizers, and a limit that loses exclusivity

7 November 2026. Integrated as `lean/PFUL/FiniteGlobalRange.lean` (L-304, L-305), `GeneralRange.lean` (L-306–L-308), `PrefixNormalizers.lean` (L-309–L-316), `ExclusiveLimitFailure.lean` (L-317–L-320), and `GeneralProbe.lean` (L-321). Axioms: propext, Classical.choice, Quot.sound. No sorry.

The question "exclusive and Baire class 1 on Bool^ℕ ⇒ a fixed point" remains open. No exclusive Baire-one counterexample is obtained.

## 1. Finite global image

For any party set ι, an exclusive F : Bool^ι → Bool^ι with finite image has a fixed point (L-304). No continuity, Baire class, or countability of ι is used. More strongly, an exclusive w : Bool^ι → ∏_k A_k with finite global image is a process function for every family of local maps A_k → Bool (L-305). The input alphabets are arbitrary. The outputs of the reduced self-map are Boolean.

This is finiteness of the image of the whole vector. Each Boolean coordinate already has a two-point image, and that per-coordinate fact does not settle infinitely many parties.

Proof sketch. Patterns of coordinates on the finite range R are functions R → Bool. At most 2^|R| patterns occur. Coordinates with the same pattern are tied. F descends to an exclusive self-map of the finite cube of patterns, and the finite theorem lifts. For arbitrary local responses, s ↦ (f_k(w(s)_k))_k stays exclusive and finite-image.

## 2. Output range in one finite-difference class

If F is exclusive and every point of the closure of its range differs finitely from a fixed c, then F has a fixed point (L-306). No exceptional set and no Baire class are assumed. A uniform bound K on output Hamming weight relative to c is a corollary (L-307), as is a closed range contained in one finite-difference class with no uniform bound (L-308).

Prefix solutions x_n frozen to c satisfy F(x_n) → y whenever x_n → y along a subsequence with n → ∞, so y lies in the closure of the range. Finite defect of y and of F(y) from c, plus the prefix-agreement lemma, give F(y) = y.

This is a hypothesis on outputs. It is distinct from the earlier bounds on exceptional inputs (L-272, L-290). It does not say that a Baire-one range lies in one finite-difference class.

## 3. Prefix normalizers

P_n(b) is the unique history with tail b from n on that is consistent below n (L-309). Then P_m ∘ P_n = P_max(m,n) (L-310). If F is Baire class 1, so is P_n (L-311). The proof applies a continuous selector to the whole finite truth table of continuous approximants of F. Those approximants are not assumed exclusive.

If P_n converges pointwise to L, then L is invariant under finite changes of its input (L-312). A Boolean Baire-one map with that invariance is constant (L-313), because it has a continuity point and finite patches of any other input approach that point. So a Baire-one limit L is constant (L-314).

What is not proved: that P_n converges, and that a pointwise limit remains Baire class 1. Even a constant limit does not license exchanging P_m with the limit at a discontinuity of P_m.

Ambient continuity of every P_m at a cluster point of solved prefixes yields a fixed point (L-315). Continuity only on the cluster set does not. Prefix solutions can approach the set from outside it. For zfcF and the zero boundary the cluster set is the singleton of all ones, so every restriction there is continuous, and there is no fixed point. That map is class 2. The example diagnoses the gap. It is not a Baire-one counterexample. If P_n(p) → p and F(p) differs finitely from p, then p is fixed (L-316).

## 4. Exclusivity can fail in the limit

Y_N(s)_k is true when s_j = false for every k < j < N, and is the constant true for k ≥ N. Each Y_N is continuous and globally exclusive (L-317). The sequence converges pointwise to the Yablo map, which is Baire class 1, fixed-point-free, and not exclusive (L-318). This is not an exclusive Baire-one counterexample.

Finite-difference pairs do keep a witness in the limit (L-319, and for Yablo L-320). The witnesses that escape are those of pairs differing in infinitely many coordinates.

## 5. A rejected shortcut

The finite exclusive map (a, b) ↦ (¬b, true) has a maximal postfixed point, (true, false), that is not fixed (L-321, by `decide`). The fixed point is (false, true). Maximality of x ≤ F(x) does not become equality from exclusivity alone. This refutes that proposed proof. It does not refute every semicontinuity theorem.
