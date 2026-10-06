-- Lean 4.34.1, compiled with exit status 0, no Mathlib, no sorry.
-- Fixed point is in the output: o = f (w o).

abbrev Local (n : Nat) := Fin n → Bool → Bool
abbrev Proc (n : Nat) := (Fin n → Bool) → (Fin n → Bool)

def IsFixed {n : Nat} (w : Proc n) (f : Local n) (o : Fin n → Bool) : Prop :=
  (fun k => f k ((w o) k)) = o

def IsProcess {n : Nat} (w : Proc n) : Prop :=
  ∀ f : Local n, ∃ o, IsFixed w f o ∧ ∀ p, IsFixed w f p → p = o

theorem process_disagreement
    {n : Nat} (w : Proc n) (hw : IsProcess w)
    (s s' : Fin n → Bool) (hneq : s ≠ s') :
    ∃ k : Fin n, s k ≠ s' k ∧ w s k = w s' k := by
  classical
  apply Decidable.byContradiction
  intro hnone
  have agree : ∀ k, w s k = w s' k → s k = s' k := by
    intro k hk
    apply Decidable.byContradiction
    intro hsk
    exact hnone ⟨k, hsk, hk⟩
  let f : Local n := fun k b =>
    if b = w s k then s k else if b = w s' k then s' k else false
  have fix_s : IsFixed w f s := by
    funext k
    simp [IsFixed, f]
  have fix_sp : IsFixed w f s' := by
    funext k
    by_cases h : w s' k = w s k
    · have hs : s k = s' k := agree k h.symm
      simp [IsFixed, f, h, hs]
    · simp [IsFixed, f, h]
  rcases hw f with ⟨o, _ho, hu⟩
  have hs : s = o := hu s fix_s
  have hsp : s' = o := hu s' fix_sp
  exact hneq (hs.trans hsp.symm)

theorem xor_cancel (a b : Bool) : xor a (xor a b) = b := by
  cases a <;> cases b <;> rfl

def extend {n : Nat} (w : Proc n)
    (oe : (Fin n → Bool) × (Fin n → Bool)) :
    (Fin n → Bool) × (Fin n → Bool) :=
  (fun k => xor (w oe.1 k) (oe.2 k), oe.1)

def extendInv {n : Nat} (w : Proc n)
    (is : (Fin n → Bool) × (Fin n → Bool)) :
    (Fin n → Bool) × (Fin n → Bool) :=
  (is.2, fun k => xor (w is.2 k) (is.1 k))

theorem extend_left_inv {n : Nat} (w : Proc n)
    (oe : (Fin n → Bool) × (Fin n → Bool)) :
    extendInv w (extend w oe) = oe := by
  cases oe with
  | mk o e =>
    apply Prod.ext
    · rfl
    · funext k
      simpa [extend, extendInv] using xor_cancel (w o k) (e k)

theorem extend_right_inv {n : Nat} (w : Proc n)
    (is : (Fin n → Bool) × (Fin n → Bool)) :
    extend w (extendInv w is) = is := by
  cases is with
  | mk i s =>
    apply Prod.ext
    · funext k
      simpa [extend, extendInv] using xor_cancel (w s k) (i k)
    · rfl

def row0 : Int × Int := (1, 1)
def row1 : Int × Int := (1, -1)

theorem hadamard_rows_orthogonal :
    row0.1 * row1.1 + row0.2 * row1.2 = 0 := by
  native_decide
