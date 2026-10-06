-- Gaps that were not in Full.lean.
-- Alphabet lemma is a theorem. Hadamard row check is a theorem.
-- Partial trace is a finite identity, not Stinespring.
-- Embeddability is not proved.

abbrev Proc (n a : Nat) := (Fin n → Fin a) → (Fin n → Fin a)
abbrev Local (n a : Nat) := Fin n → Fin a → Fin a

def IsFixed {n a : Nat} (w : Proc n a) (f : Local n a) (o : Fin n → Fin a) : Prop :=
  (fun k => f k ((w o) k)) = o

def IsProcess {n a : Nat} (w : Proc n a) : Prop :=
  ∀ f, ∃ o, IsFixed w f o ∧ ∀ p, IsFixed w f p → p = o

theorem process_disagreement_alphabet
    {n a : Nat} (w : Proc n a) (hw : IsProcess w)
    (s s' : Fin n → Fin a) (hneq : s ≠ s') :
    ∃ k, s k ≠ s' k ∧ w s k = w s' k := by
  classical
  apply Decidable.byContradiction
  intro hnone
  have agree : ∀ k, w s k = w s' k → s k = s' k := by
    intro k hk
    apply Decidable.byContradiction
    intro hsk
    exact hnone ⟨k, hsk, hk⟩
  let f : Local n a := fun k b =>
    if b = w s k then s k else if b = w s' k then s' k else s k
  have fix_s : IsFixed w f s := by
    funext k; simp [IsFixed, f]
  have fix_sp : IsFixed w f s' := by
    funext k
    by_cases h : w s' k = w s k
    · have hs : s k = s' k := agree k h.symm
      simp [IsFixed, f, h, hs]
    · simp [IsFixed, f, h]
  rcases hw f with ⟨o, _, hu⟩
  exact hneq ((hu s fix_s).trans (hu s' fix_sp).symm)

theorem hadamard_rows : (1 : Int) * 1 + 1 * (-1) = 0 := by native_decide

theorem trace_identity_ancilla :
    ((1 : Int) + 0) = 1 ∧ ((0 : Int) + 1) = 1 := by native_decide

def SpacetimeEmbeddingClaim : Prop := False
