/-
  Lemma H (rigid directions) and Theorem H.17.17 (class bound) of lift.md, H.17.17.

  Model.
  * A Pauli string on three qubits, modulo phase, is `PStr := Fin 3 → ZMod 2 × ZMod 2`
    (site value (x, z): I = (0,0), X = (1,0), Z = (0,1), Y = (1,1)); the product of Pauli
    strings is, up to a phase, the sum of their (x, z) vectors.
  * An operator is given by its Pauli expansion, a finitely supported `PStr →₀ ℂ`.
    Multiplication of expansions is the twisted convolution `tmul φ` with a phase
    function `φ`: σ_t σ_s = φ t s σ_(t+s).  For Pauli strings φ takes values in {±1, ±i};
    every theorem below only assumes `φ t s ≠ 0`, so it holds for that φ in particular.
  * Two strings anticommute iff the symplectic form Σ_p (x_p z'_p + z_p x'_p) is 1 in ZMod 2.
  * Qubit p is rigid for a support S if the qubit-p parts of the strings of S are pairwise
    distinct (`Rigid p S`).

  Proved here (no sorry, no new axioms):
  * `rigid_two`, `rigid_three`  (Lemma H(i)).
  * `card_support_tmul`, `lemmaH_ii`  (Lemma H(ii), the counting step |supp V_y| = |supp W|·m).
  * `even_card_class`, `card_class_ge_two`, `card_image_le_four`, `card_class_eq_two_of_four`,
    `class_eq_edge_of_four`, `rigid_unique_of_four`  (Theorem H.17.17, abstract cube form).
  * `classBound`  (end-to-end: Lemma H + class bound, from the hypotheses listed there).

  Hypotheses that are NOT proved here (they come from the paper): the factorisation
  V_y = W · V_x with all strings of W having the same qubit-p part (Lemma B plus unitarity,
  H.17.16), the shapes of ≤3-term class supports (H.17.12), and that labels are classes, i.e.
  two labels whose operators differ by a left Pauli (times a phase) are equal.
-/
import Mathlib

namespace PFUL.LemmaH

open Finset

/-! ## Twisted products of Pauli expansions -/

section Twisted

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

/-- Product of two Pauli expansions, with σ_t σ_s = φ t s σ_(t+s). -/
noncomputable def tmul [DecidableEq G] (φ : G → G → ℂ) (W V : G →₀ ℂ) : G →₀ ℂ :=
  ∑ t ∈ W.support, ∑ s ∈ V.support, Finsupp.single (t + s) (φ t s * W t * V s)

lemma tmul_apply [DecidableEq G] (φ : G → G → ℂ) (W V : G →₀ ℂ) (u : G) :
    tmul φ W V u = ∑ x ∈ W.support ×ˢ V.support,
      if x.1 + x.2 = u then φ x.1 x.2 * W x.1 * V x.2 else 0 := by
  unfold tmul
  rw [Finset.sum_product]
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply]

/-- If all strings of `W` have the same `π`-part and `π` is injective on `supp V`,
then `(t, s) ↦ t + s` is injective on `supp W × supp V`. -/
lemma add_injOn (π : G →+ H) (a0 : H) (W V : G →₀ ℂ)
    (hW : ∀ t ∈ W.support, π t = a0) (hV : Set.InjOn π V.support) :
    Set.InjOn (fun x : G × G => x.1 + x.2) (W.support ×ˢ V.support : Finset (G × G)) := by
  rintro ⟨t, s⟩ h ⟨t', s'⟩ h' heq
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at h h'
  simp only at heq
  have hp : π s = π s' := by
    have := congrArg π heq
    rw [map_add, map_add, hW t h.1, hW t' h'.1] at this
    exact add_left_cancel this
  have hs : s = s' := hV h.2 h'.2 hp
  subst hs
  have : t = t' := add_right_cancel heq
  subst this
  rfl

theorem support_tmul [DecidableEq G] (φ : G → G → ℂ) (hφ : ∀ t s, φ t s ≠ 0) (π : G →+ H) (a0 : H)
    (W V : G →₀ ℂ) (hW : ∀ t ∈ W.support, π t = a0) (hV : Set.InjOn π V.support) :
    (tmul φ W V).support = (W.support ×ˢ V.support).image (fun x => x.1 + x.2) := by
  ext u
  rw [Finsupp.mem_support_iff, tmul_apply, Finset.mem_image]
  constructor
  · intro h
    by_contra hne
    push Not at hne
    apply h
    apply Finset.sum_eq_zero
    intro x hx
    simp only [hne x hx, ↓reduceIte]
  · rintro ⟨x0, hx0, rfl⟩
    rw [Finset.sum_eq_single_of_mem x0 hx0]
    · simp only [↓reduceIte]
      simp only [Finset.mem_product, Finsupp.mem_support_iff] at hx0
      exact mul_ne_zero (mul_ne_zero (hφ _ _) hx0.1) hx0.2
    · intro x hx hne
      have hs : ¬ x.1 + x.2 = x0.1 + x0.2 := fun hsum => hne (add_injOn π a0 W V hW hV hx hx0 hsum)
      simp only [hs, ↓reduceIte]

/-- The counting step of Lemma H(ii): |supp (W·V)| = |supp W| · |supp V|. -/
theorem card_support_tmul [DecidableEq G] (φ : G → G → ℂ) (hφ : ∀ t s, φ t s ≠ 0) (π : G →+ H) (a0 : H)
    (W V : G →₀ ℂ) (hW : ∀ t ∈ W.support, π t = a0) (hV : Set.InjOn π V.support) :
    #(tmul φ W V).support = #W.support * #V.support := by
  rw [support_tmul φ hφ π a0 W V hW hV, Finset.card_image_of_injOn (add_injOn π a0 W V hW hV),
    Finset.card_product]

end Twisted

/-! ## Pauli strings on three qubits -/

/-- One site: (x, z) bits. -/
abbrev Site := ZMod 2 × ZMod 2
/-- A three-qubit Pauli string modulo phase. -/
abbrev PStr := Fin 3 → Site

/-- The qubit-p part of a string, as an additive map. -/
def part (p : Fin 3) : PStr →+ Site where
  toFun s := s p
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Single-site symplectic form; `sympl a b = 1` iff the site Paulis anticommute. -/
def sympl (a b : Site) : ZMod 2 := a.1 * b.2 + a.2 * b.1

/-- Two strings anticommute iff they anticommute on an odd number of sites. -/
def Anticomm (A B : PStr) : Prop := ∑ p, sympl (A p) (B p) = 1

/-- Qubit p is rigid for the support S: the qubit-p parts of its strings are pairwise distinct. -/
def Rigid (p : Fin 3) (S : Finset PStr) : Prop := Set.InjOn (fun s : PStr => s p) (S : Set PStr)

lemma sympl_self (a : Site) : sympl a a = 0 := by
  revert a; decide

lemma sympl_zero_left (b : Site) : sympl 0 b = 0 := by
  simp [sympl]

lemma sympl_zero_right (a : Site) : sympl a 0 = 0 := by
  simp [sympl]

/-- Lemma H(i), two-term classes α + iβA: every qubit on which A acts is rigid. -/
theorem rigid_two (A : PStr) (hA : A ≠ 0) : ∃ p, Rigid p {0, A} := by
  obtain ⟨p, hp⟩ : ∃ p, A p ≠ 0 := by
    by_contra h
    push Not at h
    exact hA (funext h)
  refine ⟨p, ?_⟩
  unfold Rigid
  intro a ha b hb hab
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at ha hb
  simp only at hab
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rfl
  · exact absurd hab.symm hp
  · exact absurd hab hp
  · rfl

/-- Lemma H(i), three-term classes α + i(βA + γB) with A, B anticommuting:
a qubit on which A and B anticommute is rigid. -/
theorem rigid_three (A B : PStr) (h : Anticomm A B) : ∃ p, Rigid p {0, A, B} := by
  obtain ⟨p, -, hp⟩ : ∃ p ∈ (Finset.univ : Finset (Fin 3)), sympl (A p) (B p) ≠ 0 :=
    Finset.exists_ne_zero_of_sum_ne_zero (by unfold Anticomm at h; rw [h]; decide)
  have hA : A p ≠ 0 := fun h0 => hp (by rw [h0]; exact sympl_zero_left _)
  have hB : B p ≠ 0 := fun h0 => hp (by rw [h0]; exact sympl_zero_right _)
  have hAB : A p ≠ B p := fun h0 => hp (by rw [h0]; exact sympl_self _)
  refine ⟨p, ?_⟩
  unfold Rigid
  intro a ha b hb hab
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at ha hb
  simp only at hab
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    first
    | rfl
    | exact absurd hab.symm hA
    | exact absurd hab hA
    | exact absurd hab.symm hB
    | exact absurd hab hB
    | exact absurd hab hAB
    | exact absurd hab.symm hAB

/-- Lemma H(ii).  Hypotheses: `V_y = W · V_x` where all strings of `W` have the same qubit-p
part (this is `W = σ ⊗ T`; it comes from Lemma B and unitarity and is assumed here), qubit p
is rigid for `V_x`, `|supp V_x| ≥ 2`, `|supp V_y| ≤ 3` and `V_y ≠ 0`.  Conclusion: `W` is a
single Pauli string times a nonzero scalar, i.e. `V_y` is `V_x` up to a left Pauli. -/
theorem lemmaH_ii (φ : PStr → PStr → ℂ) (hφ : ∀ t s, φ t s ≠ 0) (p : Fin 3)
    (Vx W : PStr →₀ ℂ) (hW : ∃ a0, ∀ t ∈ W.support, t p = a0) (hrig : Rigid p Vx.support)
    (hm : 2 ≤ #Vx.support) (hy3 : #(tmul φ W Vx).support ≤ 3) (hy0 : tmul φ W Vx ≠ 0) :
    ∃ t0 c0, c0 ≠ 0 ∧ W = Finsupp.single t0 c0 := by
  obtain ⟨a0, ha0⟩ := hW
  have hcard := card_support_tmul φ hφ (part p) a0 W Vx ha0
    (fun a ha b hb h => hrig ha hb h)
  have hpos : 0 < #(tmul φ W Vx).support :=
    Finset.card_pos.2 (Finsupp.support_nonempty_iff.2 hy0)
  have h1 : #W.support = 1 := by
    rw [hcard] at hy3 hpos
    generalize #W.support = w at hy3 hpos ⊢
    generalize #Vx.support = m at hm hy3 hpos
    rcases w with _ | _ | w
    · simp at hpos
    · rfl
    · nlinarith
  obtain ⟨t0, ht0, hW1⟩ := Finsupp.card_support_eq_one.1 h1
  exact ⟨t0, W t0, ht0, hW1⟩

/-! ## The class bound on the cube -/

/-- Vertices of the cube (outputs o ∈ {0,1}³). -/
abbrev Vert := Fin 3 → ZMod 2

/-- The unit vector in direction p. -/
def e (p : Fin 3) : Vert := Pi.single p 1

lemma add_self_vert (v : Vert) : v + v = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize v i = a
  revert a; decide

lemma e_self (p : Fin 3) : e p p = 1 := by simp [e]

lemma e_ne_zero (p : Fin 3) : e p ≠ 0 := by
  intro h
  have := congrFun h p
  rw [e_self] at this
  exact one_ne_zero this

lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

/-- A set of vertices closed under `o ↦ o + e d` has even size. -/
theorem even_card_of_closed (S : Finset Vert) (d : Fin 3) (hS : ∀ o ∈ S, o + e d ∈ S) :
    Even #S := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) (fun o : Vert => o d = 0)
  have hbij : #(S.filter (fun o : Vert => o d = 0)) = #(S.filter (fun o : Vert => ¬ o d = 0)) := by
    apply Finset.card_nbij' (fun o => o + e d) (fun o => o + e d)
    · intro o ho
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ho ⊢
      refine ⟨hS o ho.1, ?_⟩
      simp [ho.2, e_self]
    · intro o ho
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ho ⊢
      refine ⟨hS o ho.1, ?_⟩
      have h1 : o d = 1 := (zmod2_cases (o d)).resolve_left ho.2
      simp only [Pi.add_apply, h1, e_self]
      decide
    · intro o _
      simp only [add_assoc, add_self_vert, add_zero]
    · intro o _
      simp only [add_assoc, add_self_vert, add_zero]
  rw [← hsplit, hbij]
  exact ⟨_, rfl⟩

variable {L : Type*} [DecidableEq L]

/-- The vertex set of a class. -/
def cls (κ : Vert → L) (x : L) : Finset Vert := Finset.univ.filter (fun o => κ o = x)

/-- Abstract board for Theorem H.17.17: a labelling `κ` of the cube by classes, a distinguished
identity class `idl`, and for each class a predicate `Rg x p` ("p is a rigid qubit of x").
Lemma H says: every non-identity class has a rigid qubit, and the neighbour along a rigid
direction carries the same class. -/
structure RigidBoard (L : Type*) where
  κ : Vert → L
  idl : L
  Rg : L → Fin 3 → Prop
  exists_rigid : ∀ x, x ≠ idl → ∃ p, Rg x p
  closed : ∀ o p, κ o ≠ idl → Rg (κ o) p → κ (o + e p) = κ o

namespace RigidBoard

variable (b : RigidBoard L)

lemma card_univ_vert : #(Finset.univ : Finset Vert) = 8 := by
  rw [Finset.card_univ]; simp

theorem even_card_class_ne (x : L) (hx : x ≠ b.idl) : Even #(cls b.κ x) := by
  obtain ⟨d, hd⟩ := b.exists_rigid x hx
  apply even_card_of_closed _ d
  intro o ho
  simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and] at ho ⊢
  subst ho
  exact b.closed o d hx hd

/-- Every class, the identity class included, occupies an even number of vertices. -/
theorem even_card_class (x : L) : Even #(cls b.κ x) := by
  by_cases hx : x = b.idl
  · subst hx
    -- the non-identity vertices split into non-identity classes, each even
    set T := Finset.univ.filter (fun o => b.κ o ≠ b.idl) with hT
    have hTe : Even #T := by
      rw [Finset.card_eq_sum_card_fiberwise (f := b.κ) (t := T.image b.κ)
        (fun o ho => Finset.mem_coe.2 (Finset.mem_image_of_mem _ ho))]
      apply Finset.even_sum
      intro y hy
      obtain ⟨o, ho, rfl⟩ := Finset.mem_image.1 hy
      have hne : b.κ o ≠ b.idl := (Finset.mem_filter.1 ho).2
      have : T.filter (fun a => b.κ a = b.κ o) = cls b.κ (b.κ o) := by
        ext a
        simp only [hT, cls, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact fun h => h.2
        · intro h; exact ⟨h ▸ hne, h⟩
      rw [this]
      exact b.even_card_class_ne _ hne
    have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Vert))
      (fun o => b.κ o = b.idl)
    rw [card_univ_vert] at hsum
    have h8 : Even (8 : ℕ) := ⟨4, rfl⟩
    rw [← hsum] at h8
    exact (Nat.even_add.1 h8).2 hTe
  · exact b.even_card_class_ne x hx

/-- Every class that occurs occupies at least two vertices. -/
theorem card_class_ge_two (x : L) (hx : x ∈ Finset.univ.image b.κ) : 2 ≤ #(cls b.κ x) := by
  obtain ⟨o, -, rfl⟩ := Finset.mem_image.1 hx
  have hpos : 0 < #(cls b.κ (b.κ o)) :=
    Finset.card_pos.2 ⟨o, by simp [cls]⟩
  obtain ⟨r, hr⟩ := b.even_card_class (b.κ o)
  omega

lemma sum_card_class : ∑ x ∈ Finset.univ.image b.κ, #(cls b.κ x) = 8 := by
  rw [← card_univ_vert, Finset.card_eq_sum_card_fiberwise (f := b.κ)
    (t := Finset.univ.image b.κ) (fun o _ => Finset.mem_coe.2 (Finset.mem_image_of_mem _
      (Finset.mem_univ o)))]
  rfl

/-- Theorem H.17.17: at most four classes. -/
theorem card_image_le_four : #(Finset.univ.image b.κ) ≤ 4 := by
  have h := Finset.sum_le_sum (fun x hx => b.card_class_ge_two x hx)
  rw [b.sum_card_class, Finset.sum_const, smul_eq_mul] at h
  omega

/-- With exactly four classes, every class occupies exactly two vertices. -/
theorem card_class_eq_two_of_four (h4 : #(Finset.univ.image b.κ) = 4) (x : L)
    (hx : x ∈ Finset.univ.image b.κ) : #(cls b.κ x) = 2 := by
  by_contra hne
  have hlt : ∑ _y ∈ Finset.univ.image b.κ, 2 < ∑ y ∈ Finset.univ.image b.κ, #(cls b.κ y) :=
    Finset.sum_lt_sum (fun y hy => b.card_class_ge_two y hy)
      ⟨x, hx, lt_of_le_of_ne (b.card_class_ge_two x hx) (Ne.symm hne)⟩
  rw [b.sum_card_class, Finset.sum_const, smul_eq_mul, h4] at hlt
  omega

/-- With exactly four classes, a non-identity class is one edge along each of its rigid
directions. -/
theorem class_eq_edge_of_four (h4 : #(Finset.univ.image b.κ) = 4) (o : Vert)
    (hx : b.κ o ≠ b.idl) (p : Fin 3) (hp : b.Rg (b.κ o) p) :
    cls b.κ (b.κ o) = {o, o + e p} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with h | h
    · rw [h]
    · rw [h]; exact b.closed o p hx hp
  · rw [b.card_class_eq_two_of_four h4 _ (Finset.mem_image_of_mem _ (Finset.mem_univ o))]
    rw [Finset.card_pair]
    intro h
    have : e p = 0 := by
      have := congrArg (fun v => v + o) h
      simpa [add_comm o, add_assoc, add_self_vert] using this.symm
    exact e_ne_zero p this

/-- With exactly four classes, a non-identity class has exactly one rigid qubit. -/
theorem rigid_unique_of_four (h4 : #(Finset.univ.image b.κ) = 4) (o : Vert)
    (hx : b.κ o ≠ b.idl) (p q : Fin 3) (hp : b.Rg (b.κ o) p) (hq : b.Rg (b.κ o) q) :
    p = q := by
  have hcls := b.class_eq_edge_of_four h4 o hx p hp
  have hmem : o + e q ∈ cls b.κ (b.κ o) := by
    simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and]
    exact b.closed o q hx hq
  rw [hcls, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h
  · exfalso
    apply e_ne_zero q
    have := congrArg (fun v => v + o) h
    simpa [add_comm o, add_assoc, add_self_vert] using this
  · by_contra hpq
    have := congrFun h q
    simp [e, Ne.symm hpq] at this

end RigidBoard

/-! ## End to end: Lemma H gives a rigid board -/

lemma card_ge_two_of_shape (S : Finset PStr)
    (h : (∃ A, A ≠ 0 ∧ S = {0, A}) ∨ (∃ A B, Anticomm A B ∧ S = {0, A, B})) : 2 ≤ #S := by
  rcases h with ⟨A, hA, rfl⟩ | ⟨A, B, hAB, rfl⟩
  · rw [Finset.card_pair (Ne.symm hA)]
  · have hA : A ≠ 0 := by
      rintro rfl
      unfold Anticomm at hAB
      simp [sympl_zero_left] at hAB
    calc 2 = #({0, A} : Finset PStr) := (Finset.card_pair (Ne.symm hA)).symm
      _ ≤ #({0, A, B} : Finset PStr) := by
        apply Finset.card_le_card
        intro a ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha ⊢
        tauto

lemma exists_rigid_of_shape (S : Finset PStr)
    (h : (∃ A, A ≠ 0 ∧ S = {0, A}) ∨ (∃ A B, Anticomm A B ∧ S = {0, A, B})) :
    ∃ p, Rigid p S := by
  rcases h with ⟨A, hA, rfl⟩ | ⟨A, B, hAB, rfl⟩
  · exact rigid_two A hA
  · exact rigid_three A B hAB

/-- **End-to-end class bound.**  Data: class operators `V x` (Pauli expansions), a labelling
`κ` of the cube by classes, the identity class `idl`, and a nonvanishing phase function `φ`.
Hypotheses (from the paper, not proved here):
* `hshape` (H.12/H.17.12): a non-identity class has support {1, A} with A ≠ 1, or {1, A, B}
  with A, B anticommuting;
* `hle3`: every class has at most three terms; `hne`: every class operator is nonzero;
* `hB` (Lemma B + unitarity): across a class-changing edge in direction p,
  `V (κ (o + e p)) = W · V (κ o)` with all strings of `W` having the same qubit-p part;
* `hcls` (labels are classes): if `V y` is `V x` times a single Pauli string and a nonzero
  scalar, then `y = x`.
Conclusion: at most four classes occur, and if exactly four occur, each occupies exactly two
vertices. -/
theorem classBound {L : Type*} [DecidableEq L] (φ : PStr → PStr → ℂ) (hφ : ∀ t s, φ t s ≠ 0)
    (V : L → PStr →₀ ℂ) (κ : Vert → L) (idl : L)
    (hshape : ∀ x, x ≠ idl → (∃ A, A ≠ 0 ∧ (V x).support = {0, A}) ∨
      (∃ A B, Anticomm A B ∧ (V x).support = {0, A, B}))
    (hle3 : ∀ x, #(V x).support ≤ 3) (hne : ∀ x, V x ≠ 0)
    (hB : ∀ o p, κ (o + e p) ≠ κ o → ∃ W : PStr →₀ ℂ, (∃ a0, ∀ t ∈ W.support, t p = a0) ∧
      V (κ (o + e p)) = tmul φ W (V (κ o)))
    (hcls : ∀ x y t c, c ≠ 0 → V y = tmul φ (Finsupp.single t c) (V x) → y = x) :
    #(Finset.univ.image κ) ≤ 4 ∧
      (#(Finset.univ.image κ) = 4 → ∀ x ∈ Finset.univ.image κ, #(cls κ x) = 2) := by
  let b : RigidBoard L :=
    { κ := κ, idl := idl, Rg := fun x p => Rigid p (V x).support
      exists_rigid := fun x hx => exists_rigid_of_shape _ (hshape x hx)
      closed := by
        intro o p ho hp
        by_contra hneq
        obtain ⟨W, hW, hVy⟩ := hB o p hneq
        obtain ⟨t0, c0, hc0, rfl⟩ := lemmaH_ii φ hφ p (V (κ o)) W hW hp
          (card_ge_two_of_shape _ (hshape _ ho)) (hVy ▸ hle3 _) (hVy ▸ hne _)
        exact hneq (hcls _ _ t0 c0 hc0 hVy) }
  exact ⟨b.card_image_le_four, b.card_class_eq_two_of_four⟩

end PFUL.LemmaH
