import ShortTime.Nonlinear.SmoothRepEuclid

/-!
# `SpC` is closed under composition with maps smooth on a relatively open set

`SpC.comp` requires `Ψ` to be smooth on `S ×ˢ O` with `O ⊆ E × V` open and independent of `t`. The
nonlinearity of the equation is only defined on a set that is open in `(t, y, ζ)`, intersected
with the time slab. `SpC.comp_rel` allows `Ψ` smooth on `(S ×ˢ univ) ∩ Wo`, `Wo ⊆ ℝ × E × V` open;
`SpC.of_contDiffOn` shows that jointly smooth functions are in the class.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set Filter Topology Metric Asymptotics
open scoped ContDiff Convex

namespace ShortTime

namespace SpatialReg

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ} {S : Set ℝ} {U : Set E}

theorem contDiffOn_comp_rel {V W : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {φ : ℝ → E → V} {Wo : Set (ℝ × E × V)}
    {Ψ : ℝ × E × V → W} (hΨ : ContDiffOn ℝ ∞ Ψ ((S ×ˢ (univ : Set (E × V))) ∩ Wo))
    (hO : ∀ t ∈ S, ∀ y ∈ U, (t, y, φ t y) ∈ Wo)
    (hφ : ContDiffOn ℝ k (fun q : ℝ × E => φ q.1 q.2) (S ×ˢ U)) :
    ContDiffOn ℝ k (fun q : ℝ × E => Ψ (q.1, q.2, φ q.1 q.2)) (S ×ˢ U) :=
  (hΨ.of_le (natCast_le_infty k)).comp (contDiffOn_fst.prodMk (contDiffOn_snd.prodMk hφ))
    fun q hq => ⟨⟨hq.1, trivial⟩, hO q.1 hq.1 q.2 hq.2⟩

theorem hasFDerivAt_comp_rel {V W : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {φ : ℝ → E → V} {Wo : Set (ℝ × E × V)}
    {Ψ : ℝ × E × V → W} (hWo : IsOpen Wo)
    (hΨ : ContDiffOn ℝ ∞ Ψ ((S ×ˢ (univ : Set (E × V))) ∩ Wo)) {t : ℝ} (ht : t ∈ S)
    {y : E} (hyO : (t, y, φ t y) ∈ Wo) (hφd : DifferentiableAt ℝ (φ t) y) :
    HasFDerivAt (fun y => Ψ (t, y, φ t y))
      ((fderivWithin ℝ Ψ ((S ×ˢ (univ : Set (E × V))) ∩ Wo) (t, y, φ t y)).comp
          ((ContinuousLinearMap.inr ℝ ℝ (E × V)).comp (ContinuousLinearMap.inl ℝ E V)) +
        ((fderivWithin ℝ Ψ ((S ×ˢ (univ : Set (E × V))) ∩ Wo) (t, y, φ t y)).comp
          ((ContinuousLinearMap.inr ℝ ℝ (E × V)).comp (ContinuousLinearMap.inr ℝ E V))).comp
          (fderiv ℝ (φ t) y)) y := by
  have hι : HasFDerivAt (fun y' : E => ((t, y', φ t y') : ℝ × E × V))
      ((0 : E →L[ℝ] ℝ).prod ((ContinuousLinearMap.id ℝ E).prod (fderiv ℝ (φ t) y))) y :=
    (hasFDerivAt_const t y).prodMk ((hasFDerivAt_id y).prodMk hφd.hasFDerivAt)
  have hΨd : HasFDerivWithinAt Ψ
      (fderivWithin ℝ Ψ ((S ×ˢ (univ : Set (E × V))) ∩ Wo) (t, y, φ t y))
      ((S ×ˢ (univ : Set (E × V))) ∩ Wo) (t, y, φ t y) :=
    ((hΨ.differentiableOn (by simp)) _ ⟨⟨ht, trivial⟩, hyO⟩).hasFDerivWithinAt
  have hnhds : (fun y' : E => ((t, y', φ t y') : ℝ × E × V)) ⁻¹'
      ((S ×ˢ (univ : Set (E × V))) ∩ Wo) ∈ 𝓝 y := by
    have hc : ContinuousAt (fun y' : E => ((t, y', φ t y') : ℝ × E × V)) y :=
      continuousAt_const.prodMk (continuousAt_id.prodMk hφd.continuousAt)
    filter_upwards [hc.preimage_mem_nhds (hWo.mem_nhds hyO)] with y' hy' using
      ⟨⟨ht, trivial⟩, hy'⟩
  have h := (hΨd.comp y hι.hasFDerivWithinAt (mapsTo_preimage _ _)).hasFDerivAt hnhds
  refine h.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply, ContinuousLinearMap.inl_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.id_apply, ← map_add, Prod.mk_add_mk,
    add_zero, zero_add]

theorem SpC.comp_rel (hS : UniqueDiffOn ℝ S) (hU : IsOpen U) (n : ℕ) :
    ∀ {V W : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
      [NormedSpace ℝ W] {φ : ℝ → E → V} {Wo : Set (ℝ × E × V)} {Ψ : ℝ × E × V → W},
      IsOpen Wo → ContDiffOn ℝ ∞ Ψ ((S ×ˢ (univ : Set (E × V))) ∩ Wo) →
      (∀ t ∈ S, ∀ y ∈ U, (t, y, φ t y) ∈ Wo) →
      SpC k S U n V φ → SpC k S U n W (fun t y => Ψ (t, y, φ t y)) := by
  induction n with
  | zero =>
    intro V W _ _ _ _ φ Wo Ψ _ hΨ hO h
    exact contDiffOn_comp_rel hΨ hO h
  | succ n ih =>
    intro V W _ _ _ _ φ Wo Ψ hWo hΨ hO h
    have hdiff : ∀ t ∈ S, ∀ y ∈ U, DifferentiableAt ℝ (φ t) y := h.2.1
    set Ω : Set (ℝ × E × V) := (S ×ˢ (univ : Set (E × V))) ∩ Wo with hΩ
    set A₀ : E →L[ℝ] ℝ × E × V :=
      (ContinuousLinearMap.inr ℝ ℝ (E × V)).comp (ContinuousLinearMap.inl ℝ E V) with hA₀
    set B₀ : V →L[ℝ] ℝ × E × V :=
      (ContinuousLinearMap.inr ℝ ℝ (E × V)).comp (ContinuousLinearMap.inr ℝ E V) with hB₀
    obtain ⟨D, hD⟩ : ∃ D : ℝ × E × V → (ℝ × E × V →L[ℝ] W), D = fderivWithin ℝ Ψ Ω :=
      ⟨_, rfl⟩
    have hΩu : UniqueDiffOn ℝ Ω := (hS.prod uniqueDiffOn_univ).inter hWo
    have hDs : ContDiffOn ℝ ∞ D Ω := by
      rw [hD]; exact hΨ.fderivWithin hΩu (by simp)
    let Wo' : Set (ℝ × E × (V × (E →L[ℝ] V))) := {q | (q.1, q.2.1, q.2.2.1) ∈ Wo}
    have hWo'o : IsOpen Wo' :=
      hWo.preimage (continuous_fst.prodMk ((continuous_fst.comp continuous_snd).prodMk
        (continuous_fst.comp (continuous_snd.comp continuous_snd))))
    let Ψ' : ℝ × E × (V × (E →L[ℝ] V)) → (E →L[ℝ] W) := fun q =>
      (D (q.1, q.2.1, q.2.2.1)).comp A₀ + ((D (q.1, q.2.1, q.2.2.1)).comp B₀).comp q.2.2.2
    have hπ : ContDiffOn ℝ ∞ (fun q : ℝ × E × (V × (E →L[ℝ] V)) => D (q.1, q.2.1, q.2.2.1))
        ((S ×ˢ (univ : Set (E × (V × (E →L[ℝ] V))))) ∩ Wo') :=
      hDs.comp (contDiff_fst.prodMk ((contDiff_fst.comp contDiff_snd).prodMk
        (contDiff_fst.comp (contDiff_snd.comp contDiff_snd)))).contDiffOn
        fun q hq => ⟨⟨hq.1.1, trivial⟩, hq.2⟩
    have hΨ' : ContDiffOn ℝ ∞ Ψ' ((S ×ˢ (univ : Set (E × (V × (E →L[ℝ] V))))) ∩ Wo') :=
      (hπ.clm_comp contDiffOn_const).add ((hπ.clm_comp contDiffOn_const).clm_comp
        (contDiff_snd.comp (contDiff_snd.comp contDiff_snd)).contDiffOn)
    have key : ∀ t ∈ S, ∀ y ∈ U, HasFDerivAt (fun y => Ψ (t, y, φ t y))
        (Ψ' (t, y, (φ t y, fderiv ℝ (φ t) y))) y := by
      intro t ht y hy
      have h := hasFDerivAt_comp_rel hWo hΨ ht (hO t ht y hy) (hdiff t ht y hy)
      rw [← hΩ, ← hD] at h
      exact h
    refine ⟨contDiffOn_comp_rel hΨ hO h.1, fun t ht y hy => (key t ht y hy).differentiableAt, ?_⟩
    have hpair : SpC k S U n (V × (E →L[ℝ] V)) (fun t y => (φ t y, fderiv ℝ (φ t) y)) :=
      SpC.pair hS hU (SpC.mono_n n h) h.2.2
    have hcomp := ih (φ := fun t y => (φ t y, fderiv ℝ (φ t) y)) (Wo := Wo') (Ψ := Ψ') hWo'o hΨ'
      (fun t ht y hy => show (t, y, φ t y) ∈ Wo from hO t ht y hy) hpair
    exact SpC.congr hU n (fun t ht y hy => (key t ht y hy).fderiv.symm) hcomp

/-- Jointly smooth functions are in `SpC k` of every order, given any element of the class to
compose with (so that the universe and the type `V` are fixed). -/
theorem SpC.of_contDiffOn (hS : UniqueDiffOn ℝ S) (hU : IsOpen U) (n : ℕ) {V W : Type u}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {φ₀ : ℝ → E → V} (h0 : SpC k S U n V φ₀) {ψ : ℝ → E → W}
    (hψ : ContDiffOn ℝ ∞ (fun q : ℝ × E => ψ q.1 q.2) (S ×ˢ U)) : SpC k S U n W ψ := by
  have hc := SpC.comp_rel (k := k) hS hU n (φ := φ₀) (Wo := univ ×ˢ (U ×ˢ univ))
    (Ψ := fun q : ℝ × E × V => ψ q.1 q.2.1) (isOpen_univ.prod (hU.prod isOpen_univ))
    (hψ.comp (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)).contDiffOn
      (fun q hq => ⟨hq.1.1, hq.2.2.1⟩))
    (fun t _ y hy => ⟨trivial, hy, trivial⟩) h0
  exact hc

end SpatialReg

end ShortTime
