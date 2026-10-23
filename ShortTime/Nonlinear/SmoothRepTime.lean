import ShortTime.Nonlinear.SmoothRepTimeCore

/-!
# The time bootstrap for the representative of a solution (`prop:regularity`, time part)

**`EquationData.smoothRep_time`** (the interface `htime'` of `exists_smooth_rep`). In the setting of
`parabolicSpace_solution_smooth`, there is a neighbourhood `V` of `0` in `𝒫^m_0`, uniform in the chart
centre, such that for every frame patch `(α, r, B)` and every `v ∈ V` with
`existenceMap … v = ofSmooth f` there is `G` with

* `∂ₜ v̂(·, φ⁻¹ y) = G(t, y)` within `[0, T₁]` for `y` in the ball of radius `r` (so `εt = r`);
* for every `ε ≤ r` and `k`: if `repChart` is in `SpC k n` on the `ε`-ball for all `n`, so is `G`.

The proof: `G` is a smooth Euclidean function of `(t, y, chart readings of the jets of v̂)`
(`htime_core`): the equation `∂ₜ(w + v) = 𝒩(w + v) + f` holds pointwise for the continuous
representatives (`jetChart_timeDerivExt`, `jetChart_nonlin`, by density), the jets of `v̂` lie in the
domain of the nonlinearity because `‖v‖` is small (`exists_small_dom`), and the jets of `v̂` inherit
`SpC` regularity from `v̂` by the chart recursion (`spC_jetChart`).
-/

noncomputable section

open Bundle Manifold Set Filter Topology Metric
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 3200000

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

variable {g : SmoothRiemannianMetric I M} {s p : ℕ}

open ParabolicSpace HFlow SmoothRep

/-- The index arithmetic: `m ≥ ⌊n/2p⌋ + 4` gives the Sobolev-in-time bounds used throughout. -/
theorem hk_of_hm (hp : 1 ≤ p) {m : ℕ} (hm : Module.finrank ℝ E / (2 * p) + 4 ≤ m) :
    Module.finrank ℝ E / 2 + 1 + 2 * p ≤ 2 * p * (m - 2) := by
  have h1 := Nat.lt_mul_div_succ (Module.finrank ℝ E) (show 0 < 2 * p by omega)
  have h2 : Module.finrank ℝ E / (2 * p) + 2 ≤ m - 2 := by omega
  have h3 := Nat.mul_le_mul_left (2 * p) h2
  have h4 : 2 * p * (Module.finrank ℝ E / (2 * p) + 2) =
      2 * p * (Module.finrank ℝ E / (2 * p) + 1) + 2 * p := by ring
  rw [h4] at h3
  generalize 2 * p * (Module.finrank ℝ E / (2 * p) + 1) = X at h1 h3
  generalize 2 * p * (m - 2) = Y at h3 ⊢
  omega

namespace EquationData

theorem smoothRep_time (D : EquationData I M 0 s p) (hp : 1 ≤ p)
    {m : ℕ} (hm : Module.finrank ℝ E / (2 * p) + 4 ≤ m) (hm1 : 1 ≤ m)
    {T₁ : ℝ} (hT₁ : 0 < T₁) (hT₁D : T₁ ≤ D.T₀) {lam : ℝ} (hlam : 0 < lam)
    {w : ℝ → SmoothCcTensor g 0 s} (hw : JointlySmoothOn g 0 s (Icc 0 T₁) w)
    (hleg : ∀ t ∈ Icc (0 : ℝ) T₁, ∀ x : M, covJet g 0 s (2 * p) (w t) x ∈ D.dom t x ∧
      LegendreAt g 0 s p x (D.principal t x (covJet g 0 s (2 * p) (w t) x)) lam)
    {δ : ℝ} (hδ : 0 < δ)
    {𝒩 : ParabolicSpace g s p m T₁ → ParabolicSpace g s p (m - 1) T₁}
    (h𝒩 : ContDiffAt ℝ ∞ 𝒩 (ofSmooth w hw))
    (hagree : ∀ u (hu : JointlySmoothOn g 0 s (Icc 0 T₁) u),
      dist (ofSmooth (p := p) (m := m) u hu) (ofSmooth w hw) < δ →
      (∀ t ∈ Icc (0 : ℝ) T₁, ∀ x : M, covJet g 0 s (2 * p) (u t) x ∈ D.dom t x) ∧
      ∃ hF, 𝒩 (ofSmooth u hu) = ofSmooth (D.nonlinFamily u) hF)
    (hL : ∃ L : LinearOp g s p T₁, L.IsParabolic lam ∧
      (∀ k t, t ∈ Icc (0 : ℝ) T₁ → ∀ x,
        opFieldHom ((L.coeff k t).toSection x) =
          D.partialDeriv k t x (covJet g 0 s (2 * p) (w t) x)) ∧
      ∀ h (hh : JointlySmoothOn g 0 s (Icc 0 T₁) h), ∃ hL,
        fderiv ℝ 𝒩 (ofSmooth w hw) (ofSmooth h hh) =
          ofSmooth (fun t => L.apply t (h t)) hL) :
    ∃ V ∈ 𝓝 (0 : zeroAtStart g s p m T₁),
      ∀ (α : M) (r : ℝ) (_ : 0 < r)
        (B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
        (_ : Metric.closedBall (extChartAt I α α) r ⊆ (extChartAt I α).target)
        (_ : ∀ y ∈ Metric.closedBall (extChartAt I α α) r, ∀ k,
          trivToE I α ((extChartAt I α).symm y) (B k ((extChartAt I α).symm y)) =
            Module.finBasis ℝ E k),
      ∃ εt ∈ Ioc 0 r, ∀ v ∈ V, ∀ (f : ℝ → SmoothCcTensor g 0 s)
        (hf : JointlySmoothOn g 0 s (Icc 0 T₁) f),
        existenceMap hT₁ hm1 𝒩 (ofSmooth w hw) v = ofSmooth f hf →
        ∃ G : ℝ → E → TensorRSModel 0 s ℝ E,
          (∀ t ∈ Icc (0 : ℝ) T₁, ∀ y ∈ Metric.ball (extChartAt I α α) εt,
            HasDerivWithinAt
              (fun τ => repChart g s p m T₁ α (v : ParabolicSpace g s p m T₁) τ y)
              (G t y) (Icc 0 T₁) t) ∧
          ∀ ε ≤ εt, ∀ k, (∀ n, SpatialReg.SpC k (Icc 0 T₁)
              (Metric.ball (extChartAt I α α) ε) n (TensorRSModel 0 s ℝ E)
              (repChart g s p m T₁ α (v : ParabolicSpace g s p m T₁))) →
            ∀ n, SpatialReg.SpC k (Icc 0 T₁) (Metric.ball (extChartAt I α α) ε) n
              (TensorRSModel 0 s ℝ E) G := by
  have hk := hk_of_hm (E := E) hp hm
  have hm2 : 2 ≤ m := by
    have := Nat.zero_le (Module.finrank ℝ E / (2 * p))
    omega
  have hwdom : ∀ t ∈ Icc (0 : ℝ) T₁, ∀ x : M, covJet g 0 s (2 * p) (w t) x ∈ D.dom t x :=
    fun t ht x => (hleg t ht x).1
  obtain ⟨ρ, hρ, hsmall⟩ := exists_small_dom D hT₁ hT₁D (by omega) hk hw hwdom
  set c : ℝ := min δ ρ with hc
  have hc0 : 0 < c := lt_min hδ hρ
  have hev : ∀ᶠ y in 𝓝 (ofSmooth w hw), ContinuousAt 𝒩 y :=
    ((h𝒩.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)).eventually (by simp)).mono
      fun y hy => hy.continuousAt
  have hcoe : Continuous fun v : zeroAtStart g s p m T₁ =>
      ofSmooth w hw + (v : ParabolicSpace g s p m T₁) :=
    continuous_const.add continuous_subtype_val
  have hV1 : {v : zeroAtStart g s p m T₁ | ‖(v : ParabolicSpace g s p m T₁)‖ < c} ∈
      𝓝 (0 : zeroAtStart g s p m T₁) :=
    (isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const).mem_nhds
      (by simpa using hc0)
  have hV2 : {v : zeroAtStart g s p m T₁ |
      ContinuousAt 𝒩 (ofSmooth w hw + (v : ParabolicSpace g s p m T₁))} ∈
      𝓝 (0 : zeroAtStart g s p m T₁) := by
    have h0 : Tendsto (fun v : zeroAtStart g s p m T₁ =>
        ofSmooth w hw + (v : ParabolicSpace g s p m T₁)) (𝓝 0) (𝓝 (ofSmooth w hw)) := by
      have := (hcoe.tendsto (0 : zeroAtStart g s p m T₁))
      simpa using this
    exact h0.eventually hev
  refine ⟨_, inter_mem hV1 hV2, fun α r hr B hball hB => ⟨r, ⟨hr, le_rfl⟩, ?_⟩⟩
  rintro v ⟨hv1, hv2⟩ f hf heq
  have hvn : ‖(v : ParabolicSpace g s p m T₁)‖ < c := hv1
  have hdist : dist (ofSmooth w hw + (v : ParabolicSpace g s p m T₁)) (ofSmooth w hw) < δ := by
    rw [dist_eq_norm, add_sub_cancel_left]
    exact lt_of_lt_of_le hvn (min_le_left _ _)
  have hdom : ∀ t ∈ Icc (0 : ℝ) T₁, ∀ x : M,
      jetTuple g s p m T₁ (ofSmooth w hw + (v : ParabolicSpace g s p m T₁)) t x ∈
        D.toFibreMap.dom 0 t x := by
    refine hsmall _ ?_
    rw [add_sub_cancel_left]
    exact lt_of_lt_of_le hvn (min_le_right _ _)
  exact htime_core D hT₁ hT₁D hm1 hm2 hk hw hf hagree hdist hv2 hdom heq hball hB

end EquationData

end ShortTime
