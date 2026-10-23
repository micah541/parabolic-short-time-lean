import ShortTime.Nonlinear.FlowsNaturalParamIter
import ShortTime.Linear.LimitSmooth

/-!
# Flows of constant-coordinate vector fields in a chart

On a chart patch where the vector field `B` has constant chart coordinates `b`, its flow is the
translation by `σ b` in chart coordinates (`flow_chart_line`, `flow_chart_ball`): the line
`τ ↦ chart⁻¹(y + τ b)` is an integral curve of `B`, and integral curves are unique.

The base map of the composite pullback `iterPull` is the composite flow `iterFlow`
(`iterPull_toSection`). For a frame `B` with constant chart coordinates `b i` (as given by
`exists_chart_patch`), `iterFlow B σ (chart⁻¹ y) = chart⁻¹(y + ∑ σ_i b_i)` for small `σ`
(`iterFlow_chart`, `iterFlow_chart_patch`).
-/

noncomputable section

open Bundle Manifold Set Filter
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

namespace ShortTime

namespace HFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

/-! ### One vector field -/

/-- **The flow of a field with constant chart coordinates is a translation in the chart**: if
`trivToE α (B z) = b` along the chart line `τ ↦ y + τ b`, `τ ∈ (-T, T)`, then
`φ_σ(chart⁻¹ y) = chart⁻¹(y + σ b)` for `σ ∈ (-T, T)`. -/
theorem flow_chart_line (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (α : M) {U : Set E}
    (hU : U ⊆ (extChartAt I α).target) {b : E}
    (hB : ∀ z ∈ U, trivToE I α ((extChartAt I α).symm z) (B ((extChartAt I α).symm z)) = b)
    {y : E} {T : ℝ} (hline : ∀ τ ∈ Ioo (-T) T, y + τ • b ∈ U) {σ : ℝ}
    (hσ : σ ∈ Ioo (-T) T) :
    flow B σ ((extChartAt I α).symm y) = (extChartAt I α).symm (y + σ • b) := by
  have hT : (0 : ℝ) ∈ Ioo (-T) T := ⟨by linarith [hσ.1, hσ.2], by linarith [hσ.1, hσ.2]⟩
  have hγ : IsMIntegralCurveOn (fun τ => (extChartAt I α).symm (y + τ • b)) (fun z => B z)
      (Ioo (-T) T) := by
    intro τ hτ
    set z := y + τ • b with hz
    have hzt : z ∈ (extChartAt I α).target := hU (hline τ hτ)
    set D := mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (range I) z with hD
    have h1 : HasMFDerivWithinAt 𝓘(ℝ, E) I (extChartAt I α).symm (range I) z D :=
      (mdifferentiableWithinAt_extChartAt_symm hzt).hasMFDerivWithinAt
    rw [ModelWithCorners.Boundaryless.range_eq_univ, hasMFDerivWithinAt_univ] at h1
    have h2' : HasDerivAt (fun τ : ℝ => y + τ • b) b τ := by
      simpa using ((hasDerivAt_id' τ).smul_const b).const_add y
    have h2 : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun τ : ℝ => y + τ • b) τ
        ((1 : ℝ →L[ℝ] ℝ).smulRight b) :=
      hasMFDerivAt_iff_hasFDerivAt.2 h2'.hasFDerivAt
    have h3 := h1.comp τ h2
    have hp : (extChartAt I α).symm z ∈ (chartAt H α).source := by
      rw [← extChartAt_source (I := I)]
      exact (extChartAt I α).map_target hzt
    have hBz := hB z (hline τ hτ)
    rw [trivToE, TangentBundle.continuousLinearMapAt_trivializationAt hp] at hBz
    have hinv := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := I) (x := α) hzt
    have hDb : D b = B ((extChartAt I α).symm z) := by
      calc D b = D (mfderiv I 𝓘(ℝ, E) (extChartAt I α) ((extChartAt I α).symm z)
            (B ((extChartAt I α).symm z))) := (congrArg D hBz).symm
        _ = B ((extChartAt I α).symm z) := ContinuousLinearMap.ext_iff.1 hinv _
    have hcomp : D.comp ((1 : ℝ →L[ℝ] ℝ).smulRight b) =
        (1 : ℝ →L[ℝ] ℝ).smulRight (B ((extChartAt I α).symm z)) := by
      refine ContinuousLinearMap.ext_ring ?_
      have h1 : D ((1 : ℝ) • b) = (1 : ℝ) • B ((extChartAt I α).symm z) := by
        rw [one_smul, one_smul]
        exact hDb
      exact h1
    exact (h3.congr_mfderiv hcomp).hasMFDerivWithinAt
  have hφ := (isMIntegralCurve_flow B ((extChartAt I α).symm y)).isMIntegralCurveOn (Ioo (-T) T)
  have h0 : (extChartAt I α).symm (y + (0 : ℝ) • b) = flow B 0 ((extChartAt I α).symm y) := by
    rw [zero_smul, add_zero, flow_zero]
  have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless hT
    (B.contMDiff.of_le (by exact_mod_cast le_top)) hγ hφ h0
  exact (heq hσ).symm

theorem line_aux {d nb sg r τ : ℝ} (hnb : 0 ≤ nb) (h : d + sg * nb < r)
    (hτ : |τ| < sg + (r - d - sg * nb) / (nb + 1)) : d + |τ| * nb < r := by
  set ε := (r - d - sg * nb) / (nb + 1) with hεdef
  have hε : ε * (nb + 1) = r - d - sg * nb := div_mul_cancel₀ _ (by linarith)
  have hεpos : 0 < ε := div_pos (by linarith) (by linarith)
  have h1 : |τ| * nb ≤ sg * nb + ε * nb := by
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right hτ.le hnb
  have h2 : ε * nb + ε = r - d - sg * nb := by rw [← hε]; ring
  linarith

/-- The flow of a field with constant chart coordinates `b` on a ball `B(c, r)` of the chart:
`φ_σ(chart⁻¹ y) = chart⁻¹(y + σ b)` when `|y - c| + |σ| |b| < r`. -/
theorem flow_chart_ball (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (α : M) {c : E} {r : ℝ}
    (hball : Metric.ball c r ⊆ (extChartAt I α).target) {b : E}
    (hB : ∀ z ∈ Metric.ball c r,
      trivToE I α ((extChartAt I α).symm z) (B ((extChartAt I α).symm z)) = b)
    {y : E} {σ : ℝ} (hy : dist y c + |σ| * ‖b‖ < r) :
    flow B σ ((extChartAt I α).symm y) = (extChartAt I α).symm (y + σ • b) := by
  set T := |σ| + (r - dist y c - |σ| * ‖b‖) / (‖b‖ + 1) with hT
  have hεpos : 0 < (r - dist y c - |σ| * ‖b‖) / (‖b‖ + 1) :=
    div_pos (by linarith) (by linarith [norm_nonneg b])
  refine flow_chart_line B α hball hB (T := T) (fun τ hτ => ?_) ?_
  · have hτ' : |τ| < T := abs_lt.2 hτ
    have h := line_aux (norm_nonneg b) hy hτ'
    rw [Metric.mem_ball]
    calc dist (y + τ • b) c ≤ dist (y + τ • b) y + dist y c := dist_triangle _ _ _
      _ = |τ| * ‖b‖ + dist y c := by
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      _ < r := by linarith
  · exact abs_lt.1 (by linarith)

/-! ### The composite flow -/

/-- **The composite flow** `φ^{B (n-1)}_{σ (n-1)} ∘ ⋯ ∘ φ^{B 0}_{σ 0}`, the base map of
`iterPull B σ`. -/
def iterFlow : {n : ℕ} → (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) →
    (σ : Fin n → ℝ) → M → M
  | 0, _, _, x => x
  | _ + 1, B, σ, x => iterFlow (fun i => B i.succ) (fun i => σ i.succ) (flow (B 0) (σ 0) x)

theorem iterFlow_succ {n : ℕ} (B : Fin (n + 1) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (σ : Fin (n + 1) → ℝ) (x : M) :
    iterFlow B σ x = iterFlow (fun i => B i.succ) (fun i => σ i.succ) (flow (B 0) (σ 0) x) :=
  rfl

/-- `Π_σ u (x)` is a linear image of `u (iterFlow B σ x)` (the composite parallel transport). -/
theorem iterPull_toSection (g : SmoothRiemannianMetric I M) (s : ℕ) {n : ℕ}
    (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (σ : Fin n → ℝ) (x : M) :
    ∃ L : TensorRSSpace 0 s I (iterFlow B σ x) ≃L[ℝ] TensorRSSpace 0 s I x,
      ∀ u : SmoothCcTensor g 0 s, (iterPull B g s σ u).toSection x =
        L (u.toSection (iterFlow B σ x)) := by
  induction n generalizing x with
  | zero => exact ⟨ContinuousLinearEquiv.refl ℝ _, fun u => rfl⟩
  | succ n ih =>
    obtain ⟨L, hL⟩ := ih (B := fun i => B i.succ) (σ := fun i => σ i.succ)
      (x := flow (B 0) (σ 0) x)
    refine ⟨L.trans (pt (B 0) g s (σ 0) x).symm, fun u => ?_⟩
    rw [iterPull_succ, hpull_toSection]
    change (pt (B 0) g s (σ 0) x).symm
      ((iterPull (fun i => B i.succ) g s (fun i => σ i.succ) u).toSection
        (flow (B 0) (σ 0) x)) = _
    rw [hL]
    rfl

/-- **The composite flow of a frame with constant chart coordinates** `b i` on a ball `B(c, r)`:
`iterFlow B σ (chart⁻¹ y) = chart⁻¹(y + ∑ σ_i b_i)` when `|y - c| + ∑ |σ_i| |b_i| < r`. -/
theorem iterFlow_chart (α : M) {n : ℕ}
    (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b : Fin n → E) {c : E} {r : ℝ}
    (hball : Metric.ball c r ⊆ (extChartAt I α).target)
    (hB : ∀ i, ∀ z ∈ Metric.ball c r,
      trivToE I α ((extChartAt I α).symm z) (B i ((extChartAt I α).symm z)) = b i)
    {y : E} {σ : Fin n → ℝ} (hy : dist y c + ∑ i, |σ i| * ‖b i‖ < r) :
    iterFlow B σ ((extChartAt I α).symm y) = (extChartAt I α).symm (y + ∑ i, σ i • b i) := by
  induction n generalizing y with
  | zero => simp [iterFlow]
  | succ n ih =>
    rw [Fin.sum_univ_succ] at hy
    have hrest : 0 ≤ ∑ i : Fin n, |σ i.succ| * ‖b i.succ‖ :=
      Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)
    rw [iterFlow_succ, flow_chart_ball (B 0) α hball (hB 0) (y := y) (σ := σ 0) (by linarith),
      ih (B := fun i => B i.succ) (b := fun i => b i.succ) (hB := fun i => hB i.succ)
        (σ := fun i => σ i.succ),
      Fin.sum_univ_succ, add_assoc]
    have hd : dist (y + σ 0 • b 0) c ≤ dist y c + |σ 0| * ‖b 0‖ := by
      calc dist (y + σ 0 • b 0) c ≤ dist (y + σ 0 • b 0) y + dist y c := dist_triangle _ _ _
        _ = dist y c + |σ 0| * ‖b 0‖ := by
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
          ring
    linarith

/-- **The composite flow from the centre of a chart patch** (`exists_chart_patch`):
`iterFlow B σ α = chart⁻¹(chart α + ∑ σ_k e_k)` for `∑ |σ_k| |e_k| < r`. -/
theorem iterFlow_chart_patch (α : M) {r : ℝ}
    (B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hball : Metric.closedBall (extChartAt I α α) r ⊆ (extChartAt I α).target)
    (hB : ∀ y ∈ Metric.closedBall (extChartAt I α α) r, ∀ k,
      trivToE I α ((extChartAt I α).symm y) (B k ((extChartAt I α).symm y)) =
        Module.finBasis ℝ E k)
    {σ : Fin (Module.finrank ℝ E) → ℝ}
    (hσ : ∑ k, |σ k| * ‖Module.finBasis ℝ E k‖ < r) :
    iterFlow B σ α =
      (extChartAt I α).symm (extChartAt I α α + ∑ k, σ k • Module.finBasis ℝ E k) := by
  have h := iterFlow_chart α B (fun k => Module.finBasis ℝ E k)
    ((Metric.ball_subset_closedBall).trans hball)
    (fun k z hz => hB z (Metric.ball_subset_closedBall hz) k)
    (y := extChartAt I α α) (σ := σ) (by rw [dist_self, zero_add]; exact hσ)
  rw [extChartAt_to_inv] at h
  exact h

end HFlow

end ShortTime
