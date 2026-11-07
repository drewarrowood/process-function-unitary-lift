import PFUL.CountablePerturbation

open Set Filter Topology

namespace PFUL.Infinite.PerfectPad
open PFUL.Infinite

/-- The perfect nowhere-dense set: all odd coordinates off. -/
def P : Set (ℕ → Bool) := {s | ∀ j, s (2*j+1) = false}
def ev (s : ℕ → Bool) : ℕ → Bool := fun j => s (2*j)
def emb (t : ℕ → Bool) : ℕ → Bool := fun k => decide (k % 2 = 0) && t (k/2)

open Classical in
/-- Pad `G` onto `P`: `G` on the even coordinates over `P`, all-false elsewhere. -/
noncomputable def pad (G : (ℕ → Bool) → (ℕ → Bool)) (s : ℕ → Bool) (k : ℕ) : Bool :=
  (decide (s ∈ P) && decide (k % 2 = 0)) && G (ev s) (k/2)

variable {G : (ℕ → Bool) → (ℕ → Bool)}

lemma pad_odd (G : (ℕ → Bool) → (ℕ → Bool)) (s : ℕ → Bool) (j : ℕ) : pad G s (2*j+1) = false := by
  simp [pad]

lemma pad_even (G : (ℕ → Bool) → (ℕ → Bool)) {s : ℕ → Bool} (hs : s ∈ P) (j : ℕ) :
    pad G s (2*j) = G (ev s) j := by
  simp [pad, hs]

lemma pad_notP (G : (ℕ → Bool) → (ℕ → Bool)) {s : ℕ → Bool} (hs : s ∉ P) :
    pad G s = fun _ => false := by
  funext k; simp [pad, hs]

theorem isClosed_P : IsClosed P := by
  have : P = ⋂ j : ℕ, {s : ℕ → Bool | s (2*j+1) = false} := by ext s; simp [P]
  rw [this]; exact isClosed_iInter fun j => isClosed_eq (continuous_apply _) continuous_const

lemma tendsto_update (x : ℕ → Bool) (e : ℕ → ℕ) (he : Tendsto e atTop atTop) (b : ℕ → Bool) :
    Tendsto (fun n => Function.update x (e n) (b n)) atTop (𝓝 x) :=
  tendsto_pi_nhds.2 fun k => tendsto_const_nhds.congr'
    ((he.eventually_gt_atTop k).mono fun n hn => by
      simp [Function.update_of_ne (show k ≠ e n by omega)])

theorem interior_P : interior P = ∅ := by
  rw [interior_eq_empty_iff_dense_compl, dense_iff_closure_eq, eq_univ_iff_forall]
  intro x
  refine mem_closure_of_tendsto (tendsto_update x (fun n => 2*n+1)
    (tendsto_atTop_mono (fun n => show n ≤ 2*n+1 by omega) tendsto_id) fun _ => true) (Eventually.of_forall
    fun n h => ?_)
  have := h n; simp at this

theorem perfect_P : Perfect P := by
  refine ⟨isClosed_P, fun x hx => ?_⟩
  rw [accPt_iff_frequently]
  refine (tendsto_update x (fun n => 2*n) (tendsto_atTop_mono (fun n => show n ≤ 2*n by omega) tendsto_id)
    fun n => !x (2*n)).frequently (Frequently.of_forall fun n => ⟨fun h => ?_, fun j => ?_⟩)
  · have := congrFun h (2*n); simp at this
  · simp only [Function.update_apply, show 2*j+1 ≠ 2*n by omega, ite_false]; exact hx j

theorem pad_ne (hG : ∀ t, G t ≠ t) (s : ℕ → Bool) : pad G s ≠ s := by
  intro h
  by_cases hs : s ∈ P
  · exact hG (ev s) (funext fun j => by have := congrFun h (2*j); rwa [pad_even G hs] at this)
  · exact hs fun j => by have := congrFun h (2*j+1); rw [pad_odd] at this; exact this.symm

lemma odd_wit {s s' : ℕ → Bool} (hs : s ∉ P) (hs' : s' ∈ P) :
    ∃ k, s k ≠ s' k ∧ pad G s k = pad G s' k := by
  simp only [P, mem_ofPred_eq, not_forall] at hs
  obtain ⟨j, hj⟩ := hs
  exact ⟨2*j+1, by rw [hs' j]; exact hj, by rw [pad_odd, pad_odd]⟩

theorem pad_exclusive (hG : Exclusive G) : Exclusive (pad G) := by
  intro s s' hne
  by_cases hs : s ∈ P <;> by_cases hs' : s' ∈ P
  · have hev : ev s ≠ ev s' := fun h => hne (funext fun k => by
      obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
      · exact congrFun h j
      · rw [hs j, hs' j])
    obtain ⟨j, hj, hw⟩ := hG _ _ hev
    exact ⟨2*j, hj, by rw [pad_even G hs, pad_even G hs', hw]⟩
  · obtain ⟨k, hk, hw⟩ := odd_wit (G := G) hs' hs
    exact ⟨k, Ne.symm hk, hw.symm⟩
  · exact odd_wit hs hs'
  · obtain ⟨k, hk⟩ := Function.ne_iff.1 hne
    exact ⟨k, hk, by rw [pad_notP G hs, pad_notP G hs']⟩

theorem pad_continuousAt (G : (ℕ → Bool) → (ℕ → Bool)) {s : ℕ → Bool} (hs : s ∉ P) :
    ContinuousAt (pad G) s :=
  (continuousAt_const (y := fun _ : ℕ => false)).congr
    (Filter.mem_of_superset (isClosed_P.isOpen_compl.mem_nhds hs) fun x (hx : x ∉ P) =>
      (pad_notP G hx).symm)

lemma continuous_ev : Continuous ev := continuous_pi fun _ => continuous_apply _
lemma continuous_emb : Continuous emb := continuous_pi fun _ =>
  (continuous_of_discreteTopology (f := fun p : Bool × Bool => p.1 && p.2)).comp
    (continuous_const.prodMk (continuous_apply _))

lemma ev_emb (t : ℕ → Bool) : ev (emb t) = t := funext fun j => by simp [ev, emb]
lemma emb_mem (t : ℕ → Bool) : emb t ∈ P := fun j => by simp [emb]

theorem pad_baireOne (hG : BaireOne G) : BaireOne (pad G) := by
  classical
  obtain ⟨g, hg, hlim⟩ := hG
  let f : ℕ → (ℕ → Bool) → ℕ → Bool := fun n s k =>
    (decide (∀ j < n, s (2*j+1) = false) && decide (k % 2 = 0)) && g n (ev s) (k/2)
  refine ⟨f, fun n => continuous_pi fun k => ?_, fun s => tendsto_pi_nhds.2 fun k => ?_⟩
  · have h1 : Continuous fun s : ℕ → Bool => decide (∀ j < n, s (2*j+1) = false) :=
      continuous_of_finset_dep ((Finset.range n).image fun j => 2*j+1) fun x y hxy => by
        simp only [decide_eq_decide]
        exact forall₂_congr fun j hj => by
          rw [hxy _ (Finset.mem_image.2 ⟨j, Finset.mem_range.2 hj, rfl⟩)]
    have h2 : Continuous fun s => g n (ev s) (k/2) :=
      (continuous_apply _).comp ((hg n).comp continuous_ev)
    have hand : Continuous fun p : Bool × Bool => p.1 && p.2 := continuous_of_discreteTopology
    exact hand.comp ((hand.comp (h1.prodMk continuous_const)).prodMk h2)
  · by_cases hs : s ∈ P
    · have := ((continuous_apply (k/2)).tendsto _).comp (hlim (ev s))
      have hpk : pad G s k = (decide (k % 2 = 0) && G (ev s) (k/2)) := by simp [pad, hs]
      rw [hpk]
      cases hk : decide (k % 2 = 0)
      · exact tendsto_const_nhds.congr fun n => by simp at hk; simp [f, hk]
      · refine this.congr fun n => ?_
        have : ∀ j < n, s (2*j+1) = false := fun j _ => hs j
        simp at hk; simp [f, hk]; exact fun _ => this
    · refine tendsto_bool_of_eventually ?_
      simp only [P, mem_ofPred_eq, not_forall] at hs
      obtain ⟨j, hj⟩ := hs
      refine (eventually_gt_atTop j).mono fun n hn => ?_
      have : ¬ ∀ i < n, s (2*i+1) = false := fun h => hj (h j hn)
      have hnp : s ∉ P := fun h => hj (h j)
      simp [f, pad, this, hnp]

theorem baireOne_of_pad (h : BaireOne (pad G)) : BaireOne G := by
  obtain ⟨g, hg, hlim⟩ := h
  refine ⟨fun n t j => g n (emb t) (2*j), fun n => continuous_pi fun j =>
    (continuous_apply _).comp ((hg n).comp continuous_emb), fun t => tendsto_pi_nhds.2 fun j => ?_⟩
  have := ((continuous_apply (2*j)).tendsto _).comp (hlim (emb t))
  rwa [Function.comp_def, pad_even G (emb_mem t), ev_emb] at this

theorem baireOne_pad_iff : BaireOne (pad G) ↔ BaireOne G := ⟨baireOne_of_pad, pad_baireOne⟩

/-- **Perfect nowhere-dense counterexample (ZFC).** An exclusive fixed-point-free self-map of
`ℕ → Bool`, constant (all-false) — hence continuous — off a closed, perfect, nowhere-dense set. It
is not Baire class 1. -/
theorem exists_exclusive_fpf_const_off_perfect :
    ∃ (F : (ℕ → Bool) → (ℕ → Bool)) (Q : Set (ℕ → Bool)), Perfect Q ∧ interior Q = ∅ ∧
      Exclusive F ∧ (∀ s, F s ≠ s) ∧ (∀ s, s ∉ Q → F s = fun _ => false) ∧
      (∀ s, s ∉ Q → ContinuousAt F s) ∧ ¬ BaireOne F :=
  ⟨pad zfcF, P, perfect_P, interior_P, pad_exclusive zfcF_exclusive, pad_ne zfcF_ne,
    fun _ hs => pad_notP _ hs, fun _ hs => pad_continuousAt _ hs,
    fun h => zfcF_not_baireOne (baireOne_of_pad h)⟩

/-- **Reduction.** Any exclusive fixed-point-free Baire-one `G` yields one that is moreover
continuous (indeed constant) off the perfect nowhere-dense `P`, and conversely trivially. -/
theorem reduction (G : (ℕ → Bool) → (ℕ → Bool)) (hex : Exclusive G) (hfp : ∀ t, G t ≠ t)
    (hb : BaireOne G) :
    Exclusive (pad G) ∧ (∀ s, pad G s ≠ s) ∧ BaireOne (pad G) ∧
      (∀ s, s ∉ P → pad G s = fun _ => false) :=
  ⟨pad_exclusive hex, pad_ne hfp, pad_baireOne hb, fun _ hs => pad_notP _ hs⟩

end PFUL.Infinite.PerfectPad

#print axioms PFUL.Infinite.PerfectPad.isClosed_P
#print axioms PFUL.Infinite.PerfectPad.interior_P
#print axioms PFUL.Infinite.PerfectPad.perfect_P
#print axioms PFUL.Infinite.PerfectPad.pad_exclusive
#print axioms PFUL.Infinite.PerfectPad.pad_ne
#print axioms PFUL.Infinite.PerfectPad.pad_continuousAt
#print axioms PFUL.Infinite.PerfectPad.baireOne_pad_iff
#print axioms PFUL.Infinite.PerfectPad.exists_exclusive_fpf_const_off_perfect
#print axioms PFUL.Infinite.PerfectPad.reduction
