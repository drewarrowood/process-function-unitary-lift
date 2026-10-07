-- Complex conjugation as a compiled involution on the second factor.
-- Lean 4.34.1, no Mathlib, no sorry, no axiom.
-- A Gaussian integer is a pair of Int. conj flips the sign of the imaginary part.
-- Reindexing does not move conj. A zero factor still kills the product.
-- This file does not claim J†J = I for every w, and it does not define a metric.

namespace ComplexGram

structure G where
  re : Int
  im : Int

def conj (z : G) : G := ⟨z.re, -z.im⟩

theorem conj_involutive (z : G) : conj (conj z) = z := by
  cases z
  simp [conj, Int.neg_neg]

def add (z w : G) : G := ⟨z.re + w.re, z.im + w.im⟩
def mul (z w : G) : G := ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩

theorem conj_mul (z w : G) : conj (mul z w) = mul (conj z) (conj w) := by
  cases z; cases w
  simp [conj, mul, Int.neg_add, Int.neg_mul, Int.mul_neg, Int.neg_neg]

theorem conj_add (z w : G) : conj (add z w) = add (conj z) (conj w) := by
  cases z; cases w
  simp [conj, add, Int.neg_add]

def sum2 (f : Bool → G) : G := add (f false) (f true)

theorem add_comm (z w : G) : add z w = add w z := by
  cases z; cases w
  simp [add, Int.add_comm]

theorem sum2_xor (a : Bool) (g : Bool → G) :
    sum2 (fun e => g (xor a e)) = sum2 g := by
  cases a
  · rfl
  · simp [sum2, xor, add_comm]

def overlap (V : Bool → Bool → G) (r r' d : Bool) : G :=
  sum2 (fun i => mul (V r i) (conj (V r' (xor i d))))

theorem conj_sits_inside (V : Bool → Bool → G) (r r' d : Bool) :
    conj (overlap V r r' d) =
      sum2 (fun i => mul (conj (V r i)) (V r' (xor i d))) := by
  unfold overlap sum2
  rw [conj_add, conj_mul, conj_mul, conj_involutive, conj_involutive]

theorem zero_kills (z : G) : mul ⟨0, 0⟩ z = ⟨0, 0⟩ := by
  cases z
  simp [mul]

theorem reindex_keeps_conj (a : Bool) (g : Bool → G) :
    sum2 (fun e => conj (g (xor a e))) = conj (sum2 g) := by
  cases a
  · simp [sum2, conj_add]
  · simp [sum2, xor, conj_add, add_comm]

end ComplexGram
