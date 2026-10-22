import PFUL.Isometry
import Mathlib.Analysis.Matrix.PosDef

/-!
# Gap 3: the process matrix (Choi form) and the generalised Born rule

For the unitary lift `U|o,e⟩ = |w o + e, o⟩` we define its Choi vector and process matrix
`W = |U⟩⟩⟨⟨U|` on `P ⊗ F ⊗ ⨂_k (I_k ⊗ O_k)`, Choi matrices `C_k = ∑ j |K_j⟩⟩⟨⟨K_j|` of local CP maps
in Kraus form, and the generalised Born rule
`p = Tr[ W (ρ_P ⊗ 1_F ⊗ ⨂_k C_k)ᵀ ] = ∑_{x,x'} W x x' (ρ ⊗ 1 ⊗ ⨂ C) x x'`.
We prove `p = Tr[M ρ Mᴴ]` for the induced map `M`, hence `p = 1` for every source state and every
choice of local CPTP maps (in Kraus form): the AFNB/OCB normalisation condition.
-/

open Matrix Finset
open scoped ComplexOrder

namespace PFUL.Choi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {I O J : ι → Type*}
variable [∀ k, AddCommGroup (I k)] [∀ k, Fintype (I k)] [∀ k, DecidableEq (I k)]
variable [∀ k, Fintype (O k)] [∀ k, DecidableEq (O k)]
variable [∀ k, Fintype (J k)] [∀ k, DecidableEq (J k)]

/-- Index of the process matrix: source `P`, sink `F`, and each party's input/output wires. -/
abbrev Idx (I O : ι → Type*) := (∀ k, I k) × ((∀ k, O k) × (∀ k, I k × O k))

/-- Choi vector of the lift: amplitude 1 exactly on `(e, o, (w o + e, o))`. -/
def liftVec (w : (∀ k, O k) → (∀ k, I k)) (x : Idx I O) : ℂ :=
  if x.2.2 = (fun k => (w x.2.1 k + x.1 k, x.2.1 k)) then 1 else 0

/-- Process matrix of the lift, `W = |U⟩⟩⟨⟨U|`. -/
def procMat (w : (∀ k, O k) → (∀ k, I k)) : Matrix (Idx I O) (Idx I O) ℂ :=
  fun x x' => liftVec w x * star (liftVec w x')

/-- Choi matrix of the CP map with Kraus operators `K j : O ← I`. -/
def choi {I' O' J' : Type*} [Fintype J'] (K : J' → Matrix O' I' ℂ) : Matrix (I' × O') (I' × O') ℂ :=
  fun p p' => ∑ j, K j p.2 p.1 * star (K j p'.2 p'.1)

/-- Generalised Born rule `Tr[W (ρ ⊗ 1_F ⊗ ⨂ C_k)ᵀ]`. -/
def born (w : (∀ k, O k) → (∀ k, I k)) (ρ : Matrix (∀ k, I k) (∀ k, I k) ℂ)
    (K : ∀ k, J k → Matrix (O k) (I k) ℂ) : ℂ :=
  ∑ x : Idx I O, ∑ x' : Idx I O, procMat w x x' *
    (ρ x.1 x'.1 * ((if x.2.1 = x'.2.1 then 1 else 0) * ∏ k, choi (K k) (x.2.2 k) (x'.2.2 k)))

/-- The source-to-(sink ⊗ Kraus-record) map. -/
def indM (w : (∀ k, O k) → (∀ k, I k)) (K : ∀ k, J k → Matrix (O k) (I k) ℂ) :
    Matrix ((∀ k, O k) × (∀ k, J k)) (∀ k, I k) ℂ :=
  fun r e => ∏ k, K k (r.2 k) (r.1 k) (w r.1 k + e k)

theorem born_eq_trace (w : (∀ k, O k) → (∀ k, I k)) (ρ : Matrix (∀ k, I k) (∀ k, I k) ℂ)
    (K : ∀ k, J k → Matrix (O k) (I k) ℂ) :
    born w ρ K = (indM w K * ρ * (indM w K)ᴴ).trace := by
  simp only [born, procMat, liftVec, Fintype.sum_prod_type, ite_mul, one_mul, zero_mul,
    apply_ite star, star_one, star_zero, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  simp only [choi]
  simp_rw [Fintype.prod_sum (fun k (j : J k) => K k j _ _ * star (K k j _ _))]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, indM, conjTranspose_apply, star_prod,
    Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  rw [Finset.sum_congr rfl (fun e _ => Finset.sum_comm)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun e' _ => Finset.sum_congr rfl (fun e _ => ?_))
  rw [Finset.prod_mul_distrib]
  ring

theorem indM_isometry (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    (K : ∀ k, J k → Matrix (O k) (I k) ℂ) (hK : ∀ k, ∑ j, (K k j)ᴴ * K k j = 1) :
    (indM w K)ᴴ * indM w K = 1 := by
  classical
  let V : ∀ k, Matrix (O k × J k) (I k × PUnit.{1}) ℂ := fun k => Matrix.of fun p c => K k p.2 p.1 c.1
  have hV : ∀ k, (V k)ᴴ * V k = 1 := by
    intro k
    ext c c'
    have h := congrFun (congrFun (hK k) c.1) c'.1
    simp only [Matrix.mul_apply, conjTranspose_apply, V, Matrix.of_apply, Fintype.sum_prod_type, Matrix.sum_apply] at h ⊢
    rw [Finset.sum_comm, h, Matrix.one_apply, Matrix.one_apply]
    congr 1
    apply propext
    exact ⟨fun h => Prod.ext h (Subsingleton.elim _ _), fun h => congrArg Prod.fst h⟩
  have h := induced_isometry w hw V hV
  ext e e'
  have h2 := congrFun (congrFun h (e, fun _ => PUnit.unit)) (e', fun _ => PUnit.unit)
  simp only [Matrix.mul_apply, conjTranspose_apply, induced, V, Matrix.of_apply] at h2 ⊢
  simp only [indM]
  rw [h2, Matrix.one_apply, Matrix.one_apply]
  congr 1
  apply propext
  exact ⟨fun h => congrArg Prod.fst h, fun h => by rw [h]⟩

/-- **Gap 3: AFNB/OCB normalisation.** For the lift of every process function, every source
state `ρ` (trace one) and all local CPTP maps given by Kraus operators, the generalised Born rule
`Tr[W (ρ ⊗ 1_F ⊗ ⨂ C_k)ᵀ]` equals one. -/
theorem born_eq_one (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    (ρ : Matrix (∀ k, I k) (∀ k, I k) ℂ) (hρ : ρ.trace = 1)
    (K : ∀ k, J k → Matrix (O k) (I k) ℂ) (hK : ∀ k, ∑ j, (K k j)ᴴ * K k j = 1) :
    born w ρ K = 1 := by
  rw [born_eq_trace, Matrix.trace_mul_comm, ← Matrix.mul_assoc, indM_isometry w hw K hK,
    Matrix.one_mul, hρ]

/-- Trace preservation in Choi form: `∑ j, (K j)ᴴ K j` is the partial trace of the Choi matrix. -/
theorem sum_kraus_apply {I' O' J' : Type*} [Fintype O'] [Fintype J']
    (K : J' → Matrix O' I' ℂ) (i i' : I') :
    (∑ j, (K j)ᴴ * K j) i i' = ∑ o, choi K (i', o) (i, o) := by
  simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, choi]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun o _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

/-- **Kraus operators from the Choi matrix.** Every positive semidefinite matrix on `I' × O'`
(a completely positive map, by Choi's theorem) is the Choi matrix of a Kraus family, obtained from
its spectral decomposition; if its partial trace over `O'` is the identity (trace preservation),
the Kraus family is complete. -/
theorem kraus_of_choi {I' O' : Type*} [Fintype I'] [Fintype O'] [DecidableEq I'] [DecidableEq O']
    (C : Matrix (I' × O') (I' × O') ℂ) (hC : C.PosSemidef) :
    ∃ K : (I' × O') → Matrix O' I' ℂ, choi K = C ∧
      ((∀ i i', ∑ o, C (i', o) (i, o) = if i = i' then 1 else 0) → ∑ j, (K j)ᴴ * K j = 1) := by
  classical
  set U := (hC.1.eigenvectorUnitary : Matrix (I' × O') (I' × O') ℂ)
  set lam := hC.1.eigenvalues
  set K : (I' × O') → Matrix O' I' ℂ := fun j => Matrix.of fun o i => (Real.sqrt (lam j) : ℂ) * U (i, o) j
  have hK : choi K = C := by
    have hspec := hC.1.spectral_theorem
    ext p p'
    conv_rhs => rw [hspec]
    simp only [choi, K, map_mul, Matrix.of_apply, Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.diagonal_apply,
      Function.comp_apply, star_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, Finset.sum_mul, star_mul', Complex.star_def, Complex.conj_ofReal]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hs : ((Real.sqrt (lam j) : ℂ)) * (Real.sqrt (lam j) : ℂ) = (lam j : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hC.eigenvalues_nonneg j)]
    linear_combination (U p j * (starRingEnd ℂ) (U p' j)) * hs
  refine ⟨K, hK, fun htp => ?_⟩
  ext i i'
  rw [sum_kraus_apply, hK, htp, Matrix.one_apply]

/-- Generalised Born rule with arbitrary local Choi matrices `C k` on `I k × O k`. -/
def bornC (w : (∀ k, O k) → (∀ k, I k)) (ρ : Matrix (∀ k, I k) (∀ k, I k) ℂ)
    (C : ∀ k, Matrix (I k × O k) (I k × O k) ℂ) : ℂ :=
  ∑ x : Idx I O, ∑ x' : Idx I O, procMat w x x' *
    (ρ x.1 x'.1 * ((if x.2.1 = x'.2.1 then 1 else 0) * ∏ k, C k (x.2.2 k) (x'.2.2 k)))

/-- **Gap 3, Choi form: AFNB/OCB normalisation for all local CPTP maps.** For every process function,
every source state of trace one, and all local Choi matrices that are positive semidefinite (CP) with
identity partial trace over the output (TP), `Tr[W (ρ ⊗ 1_F ⊗ ⨂ C_k)ᵀ] = 1`. -/
theorem bornC_eq_one (w : (∀ k, O k) → (∀ k, I k)) (hw : IsProcessFunction w)
    (ρ : Matrix (∀ k, I k) (∀ k, I k) ℂ) (hρ : ρ.trace = 1)
    (C : ∀ k, Matrix (I k × O k) (I k × O k) ℂ) (hC : ∀ k, (C k).PosSemidef)
    (htp : ∀ k i i', ∑ o, C k (i', o) (i, o) = if i = i' then 1 else 0) :
    bornC w ρ C = 1 := by
  classical
  choose K hK using fun k => kraus_of_choi (C k) (hC k)
  have h := born_eq_one (J := fun k => I k × O k) w hw ρ hρ K (fun k => (hK k).2 (htp k))
  have : bornC w ρ C = born w ρ K := by
    simp only [bornC, born, (fun k => (hK k).1)]
  rw [this, h]

end PFUL.Choi

#print axioms PFUL.Choi.born_eq_trace
#print axioms PFUL.Choi.born_eq_one
#print axioms PFUL.Choi.kraus_of_choi
#print axioms PFUL.Choi.bornC_eq_one
