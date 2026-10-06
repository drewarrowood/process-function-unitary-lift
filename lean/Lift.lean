-- Combinatorial lift in core Lean 4. No Mathlib.
-- Compiled with Lean 4.34.1, `lean Lift.lean`, exit 0.
-- exclusivity: unique fixed points imply a witness party, any alphabet.
-- Cancellation: that witness kills the product amplitude if its overlap is 0.
-- Row orthonormality is a hypothesis. Complex Stinespring is not formalised.

abbrev Str (Party Alpha : Type) := Party → Alpha

structure ProcessFunction (Party Alpha : Type) where
  w : Str Party Alpha → Str Party Alpha
  uniqueFix :
    ∀ f : Party → Alpha → Alpha,
      ∃ s, (fun k => f k (w s k)) = s ∧
        ∀ s', (fun k => f k (w s' k)) = s' → s' = s

theorem exclusivity
    {Party Alpha : Type} [DecidableEq Alpha]
    (P : ProcessFunction Party Alpha)
    {s s' : Str Party Alpha}
    (hneq : s ≠ s') :
    ∃ k, s k ≠ s' k ∧ P.w s k = P.w s' k :=
  Classical.byContradiction fun h => by
    let f : Party → Alpha → Alpha := fun k x =>
      if x = P.w s k then s k else if x = P.w s' k then s' k else s k
    have fix_s : (fun k => f k (P.w s k)) = s := by
      funext k
      simp [f]
    have fix_s' : (fun k => f k (P.w s' k)) = s' := by
      funext k
      by_cases hwk : P.w s' k = P.w s k
      · have hsk : s k = s' k :=
          Classical.byContradiction fun hdiff => h ⟨k, hdiff, hwk.symm⟩
        simp [f, hwk, hsk]
      · simp [f, hwk]
    rcases P.uniqueFix f with ⟨t, _, huniq⟩
    exact hneq ((huniq s fix_s).trans (huniq s' fix_s').symm)

variable {Party Alpha : Type}

def amplitude
    (V : Party → Alpha → Alpha → Int)
    (shifted : Party → Alpha)
    (s : Str Party Alpha) : List Party → Int
  | [] => 1
  | k :: ks => V k (s k) (shifted k) * amplitude V shifted s ks

theorem product_zero_of_factor
    (V : Party → Alpha → Alpha → Int)
    (shifted : Party → Alpha)
    (s : Str Party Alpha)
    (k : Party)
    (parties : List Party)
    (hk : k ∈ parties)
    (hzero : V k (s k) (shifted k) = 0) :
    amplitude V shifted s parties = 0 := by
  induction parties with
  | nil => cases hk
  | cons p ps ih =>
    cases hk with
    | head =>
      simp [amplitude, hzero]
    | tail _ hmem =>
      have hz : amplitude V shifted s ps = 0 := ih hmem
      simp [amplitude, hz]

theorem product_one_of_factors
    (V : Party → Alpha → Alpha → Int)
    (shifted : Party → Alpha)
    (s : Str Party Alpha)
    (parties : List Party)
    (h : ∀ k, k ∈ parties → V k (s k) (shifted k) = 1) :
    amplitude V shifted s parties = 1 := by
  induction parties with
  | nil => rfl
  | cons p ps ih =>
    simp [amplitude, h p (List.Mem.head _), ih (fun k hk => h k (List.Mem.tail _ hk))]

theorem off_diagonal_cancels
    {Party Alpha : Type} [DecidableEq Alpha]
    (P : ProcessFunction Party Alpha)
    (parties : List Party)
    (V : Party → Alpha → Alpha → Int)
    {s s' : Str Party Alpha}
    (hneq : s ≠ s')
    (horth : ∀ k, s k ≠ s' k → P.w s k = P.w s' k →
      V k (s k) (P.w s k) = 0)
    (hcover : ∀ k, k ∈ parties) :
    amplitude V (fun k => P.w s k) s parties = 0 := by
  rcases exclusivity P hneq with ⟨k, hkneq, hwk⟩
  exact product_zero_of_factor V (fun k => P.w s k) s k parties (hcover k)
    (horth k hkneq hwk)

theorem diagonal_is_one
    (V : Party → Alpha → Alpha → Int)
    (s : Str Party Alpha)
    (parties : List Party)
    (hnorm : ∀ k, k ∈ parties → V k (s k) (s k) = 1) :
    amplitude V s s parties = 1 :=
  product_one_of_factors V s s parties hnorm
