-- General gram identification, every finite number of parties.
-- Lean 4.34.1, no Mathlib, no sorry, no axiom.

namespace GramGeneral

def sum2 (f : Bool → Int) : Int := f false + f true

theorem sum2_mul_right (f : Bool → Int) (c : Int) :
    sum2 (fun b => f b * c) = sum2 f * c := by
  unfold sum2
  exact (Int.add_mul (f false) (f true) c).symm

theorem sum2_xor (a : Bool) (g : Bool → Int) :
    sum2 (fun e => g (xor a e)) = sum2 g := by
  cases a
  · unfold sum2; rfl
  · unfold sum2
    change g (xor true false) + g (xor true true) = g false + g true
    rw [show xor true false = true by rfl, show xor true true = false by rfl, Int.add_comm]

def sumProd : List (Bool → Int) → Int
  | [] => 1
  | f :: fs => sum2 (fun b => f b * sumProd fs)

def prodSum : List (Bool → Int) → Int
  | [] => 1
  | f :: fs => sum2 f * prodSum fs

theorem sumProd_eq_prodSum (fs : List (Bool → Int)) :
    sumProd fs = prodSum fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    unfold sumProd prodSum
    rw [ih]
    exact sum2_mul_right f (prodSum fs)

def sumAll : Nat → (List Bool → Int) → Int
  | 0, f => f []
  | n + 1, f => sumAll n (fun t => f (false :: t)) + sumAll n (fun t => f (true :: t))

theorem sumAll_mul_left (n : Nat) (c : Int) (f : List Bool → Int) :
    sumAll n (fun e => c * f e) = c * sumAll n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [sumAll]
    rw [ih (fun t => f (false :: t)), ih (fun t => f (true :: t)), Int.mul_add]

theorem sumAll_congr {n : Nat} {f g : List Bool → Int} (h : ∀ e, f e = g e) :
    sumAll n f = sumAll n g := by
  induction n generalizing f g with
  | zero => exact h []
  | succ n ih =>
    simp only [sumAll]
    rw [ih (fun t => h (false :: t)), ih (fun t => h (true :: t))]

abbrev Row := Bool → Bool → Int

def amp : List Row → List Bool → List Bool → List Bool → Int
  | [], _, _, _ => 1
  | V :: Vs, s, ws, e =>
      V (s.headD false) (xor (ws.headD false) (e.headD false)) *
        amp Vs s.tail ws.tail e.tail

def overlap (V : Row) (r r' d : Bool) : Int :=
  sum2 (fun i => V r i * V r' (xor i d))

def overlaps : List Row → List Bool → List Bool → List Bool → List Bool → Int
  | [], _, _, _, _ => 1
  | V :: Vs, s, ws, ws2, s2 =>
      overlap V (s.headD false) (s2.headD false)
          (xor (ws2.headD false) (ws.headD false)) *
        overlaps Vs s.tail ws.tail ws2.tail s2.tail

theorem xor_cancel (a b : Bool) : xor a (xor a b) = b := by
  cases a <;> cases b <;> rfl

theorem xor_comm (a b : Bool) : xor a b = xor b a := by
  cases a <;> cases b <;> rfl

theorem mul_left_comm (a b c : Int) : a * (b * c) = b * (a * c) := by
  rw [← Int.mul_assoc, Int.mul_comm a b, Int.mul_assoc]

theorem rearrange (a p c q : Int) : (a * p) * (c * q) = (a * c) * (p * q) := by
  calc
    (a * p) * (c * q) = a * (p * (c * q)) := by rw [Int.mul_assoc]
    _ = a * (c * (p * q)) := by rw [mul_left_comm p c q]
    _ = (a * c) * (p * q) := by rw [← Int.mul_assoc]

@[simp] theorem amp_on_bit (Vk : Row) (Vs : List Row) (s ws : List Bool) (b : Bool) (t : List Bool) :
    amp (Vk :: Vs) s ws (b :: t) =
      Vk (s.headD false) (xor (ws.headD false) b) * amp Vs s.tail ws.tail t := rfl

theorem head_overlap (Vk : Row) (sk sk' wk wk' : Bool) :
    Vk sk (xor wk false) * Vk sk' (xor wk' false) +
      Vk sk (xor wk true) * Vk sk' (xor wk' true) =
    overlap Vk sk sk' (xor wk' wk) := by
  unfold overlap sum2
  cases wk
  · simp [xor_cancel]
  · rw [Int.add_comm]
    simp [xor_cancel, xor_comm]

theorem gram_factors (V : List Row) (s s2 ws ws2 : List Bool) :
    sumAll V.length (fun e => amp V s ws e * amp V s2 ws2 e) =
      overlaps V s ws ws2 s2 := by
  induction V generalizing s s2 ws ws2 with
  | nil => rfl
  | cons Vk Vs ih =>
    simp only [List.length, sumAll, amp_on_bit]
    rw [sumAll_congr (fun t => rearrange
          (Vk (s.headD false) (xor (ws.headD false) false))
          (amp Vs s.tail ws.tail t)
          (Vk (s2.headD false) (xor (ws2.headD false) false))
          (amp Vs s2.tail ws2.tail t))]
    rw [sumAll_congr (fun t => rearrange
          (Vk (s.headD false) (xor (ws.headD false) true))
          (amp Vs s.tail ws.tail t)
          (Vk (s2.headD false) (xor (ws2.headD false) true))
          (amp Vs s2.tail ws2.tail t))]
    rw [sumAll_mul_left, sumAll_mul_left, ← Int.add_mul]
    rw [ih s.tail s2.tail ws.tail ws2.tail]
    congr 1
    exact head_overlap Vk (s.headD false) (s2.headD false) (ws.headD false) (ws2.headD false)

def gram (V : List Row) (w : List Bool → List Bool) (s s2 : List Bool) : Int :=
  sumAll V.length (fun e => amp V s (w s) e * amp V s2 (w s2) e)

theorem gram_eq_shifted (V : List Row) (w : List Bool → List Bool) (s s2 : List Bool) :
    gram V w s s2 = overlaps V s (w s) (w s2) s2 :=
  gram_factors V s s2 (w s) (w s2)

def RowOrtho (V : Row) : Prop :=
  ∀ r r', overlap V r r' false = if r = r' then 1 else 0

theorem xor_self (a : Bool) : xor a a = false := by cases a <;> rfl

theorem overlaps_same (V : List Row) (s ws : List Bool)
    (hV : ∀ Vk, Vk ∈ V → RowOrtho Vk) :
    overlaps V s ws ws s = 1 := by
  induction V generalizing s ws with
  | nil => rfl
  | cons Vk Vs ih =>
    unfold overlaps
    rw [xor_self]
    have hhead : overlap Vk (s.headD false) (s.headD false) false = 1 := by
      have h := hV Vk (List.Mem.head _) (s.headD false) (s.headD false)
      simpa using h
    rw [hhead, Int.one_mul]
    exact ih s.tail ws.tail (fun U hU => hV U (List.Mem.tail _ hU))

theorem gram_diag (V : List Row) (w : List Bool → List Bool) (s : List Bool)
    (hV : ∀ Vk, Vk ∈ V → RowOrtho Vk) :
    gram V w s s = 1 := by
  rw [gram_eq_shifted]
  exact overlaps_same V s (w s) hV

theorem getD_zero (b : Bool) (t : List Bool) : (b :: t).getD 0 false = b := rfl

theorem getD_succ (b : Bool) (t : List Bool) (k : Nat) :
    (b :: t).getD (k + 1) false = t.getD k false := rfl

theorem getD_head (xs : List Bool) : xs.getD 0 false = xs.headD false := by
  cases xs <;> rfl

theorem overlaps_zero_at (V : List Row) (s ws ws2 s2 : List Bool)
    (hV : ∀ Vk, Vk ∈ V → RowOrtho Vk)
    (k : Nat) (hk : k < V.length)
    (hbit : s.getD k false ≠ s2.getD k false)
    (hws : ws.getD k false = ws2.getD k false) :
    overlaps V s ws ws2 s2 = 0 := by
  induction V generalizing s ws ws2 s2 k with
  | nil =>
    simp at hk
  | cons Vk Vs ih =>
    unfold overlaps
    cases k with
    | zero =>
      have hws' : ws2.headD false = ws.headD false := by
        rw [← getD_head ws2, ← getD_head ws]; exact hws.symm
      have hbit' : s.headD false ≠ s2.headD false := by
        rw [← getD_head s, ← getD_head s2]; exact hbit
      have hd : xor (ws2.headD false) (ws.headD false) = false := by
        rw [hws', xor_self]
      rw [hd]
      have hz : overlap Vk (s.headD false) (s2.headD false) false = 0 := by
        have h := hV Vk (List.Mem.head _) (s.headD false) (s2.headD false)
        cases hs : s.headD false <;> cases hs2 : s2.headD false
        · exact absurd (hs.trans hs2.symm) hbit'
        · rw [hs, hs2] at h; exact h
        · rw [hs, hs2] at h; exact h
        · exact absurd (hs.trans hs2.symm) hbit'
      rw [hz, Int.zero_mul]
    | succ k =>
      rw [ih s.tail ws.tail ws2.tail s2.tail
            (fun U hU => hV U (List.Mem.tail _ hU)) k
            (by simpa using hk)
            (by simpa [getD_succ] using hbit)
            (by simpa [getD_succ] using hws),
          Int.mul_zero]

theorem gram_off (V : List Row) (w : List Bool → List Bool) (s s2 : List Bool)
    (hV : ∀ Vk, Vk ∈ V → RowOrtho Vk)
    (k : Nat) (hk : k < V.length)
    (hbit : s.getD k false ≠ s2.getD k false)
    (hws : (w s).getD k false = (w s2).getD k false) :
    gram V w s s2 = 0 := by
  rw [gram_eq_shifted]
  exact overlaps_zero_at V s (w s) (w s2) s2 hV k hk hbit hws

theorem gram_unitary (V : List Row) (w : List Bool → List Bool) (s s2 : List Bool)
    (hV : ∀ Vk, Vk ∈ V → RowOrtho Vk)
    (h : s = s2 ∨ ∃ k, k < V.length ∧ s.getD k false ≠ s2.getD k false ∧
        (w s).getD k false = (w s2).getD k false) :
    gram V w s s2 = if s = s2 then 1 else 0 := by
  cases h with
  | inl heq =>
    cases heq
    rw [gram_diag V w s hV]
    simp
  | inr hwit =>
    rcases hwit with ⟨k, hk, hbit, hws⟩
    have hneq : s ≠ s2 := by
      intro heq
      apply hbit
      simpa [heq]
    rw [gram_off V w s s2 hV k hk hbit hws]
    simp [hneq]

end GramGeneral
