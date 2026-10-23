import ShortTime.Nonlinear.SmoothRepTimeLimit

/-!
# Regularity classes for the jets of the continuous representative

Stage 2 of the derivation of `htime`. On a frame patch (`hball`, `hB`):

* `repChart_eq_jetChart`: `repChart = jetChart 0 0`;
* `spC_jetChart_succ`: `SpC k (n+1)` of `jetChart j i` gives `SpC k n` of `jetChart j (i+1)`
  (from `hasFDerivAt_jetChart`: `jetChart (i+1) = slotUnins (D jetChart i - kerL jetChart i)`);
* `spC_jetChart`: if `repChart` is in `SpC k n` for all `n`, so is `jetChart 0 i` for every
  admissible `i`.
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
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

variable {g : SmoothRiemannianMetric I M} {s p m : ℕ} {T : ℝ}

open ParabolicSpace HFlow

namespace SmoothRep

theorem repChart_eq_jetChart (α : M) (v : ParabolicSpace g s p m T) (t : ℝ) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    repChart g s p m T α v t y = jetChart g s p m T α 0 0 v t y := by
  have hs : (extChartAt I α).symm y ∈ (chartAt H α).source := by
    rw [← extChartAt_source (I := I)]; exact (extChartAt I α).map_target hy
  unfold repChart repTriv jetChart
  rw [triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel 0 s α hs,
    TensorRSSpace.toModel_ofModel]
  rfl

theorem spC_jetChart_succ (hT : 0 < T) {j i : ℕ} (hj : j < m)
    (hk : Module.finrank ℝ E / 2 + 1 + (i + 1) ≤ 2 * p * (m - j - 1)) {α : M} {r ε : ℝ}
    {B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (hball : Metric.closedBall (extChartAt I α α) r ⊆ (extChartAt I α).target)
    (hB : ∀ y ∈ Metric.closedBall (extChartAt I α α) r, ∀ k,
      trivToE I α ((extChartAt I α).symm y) (B k ((extChartAt I α).symm y)) =
        Module.finBasis ℝ E k)
    (hεr : ε ≤ r) (v : ParabolicSpace g s p m T) {k n : ℕ}
    (h : SpatialReg.SpC k (Icc 0 T) (Metric.ball (extChartAt I α α) ε) (n + 1)
      (TensorRSModel 0 (s + i) ℝ E) (jetChart g s p m T α j i v)) :
    SpatialReg.SpC k (Icc 0 T) (Metric.ball (extChartAt I α α) ε) n
      (TensorRSModel 0 (s + (i + 1)) ℝ E) (jetChart g s p m T α j (i + 1) v) := by
  set U := Metric.ball (extChartAt I α α) ε with hU
  have hUo : IsOpen U := Metric.isOpen_ball
  have hUr : U ⊆ Metric.ball (extChartAt I α α) r := Metric.ball_subset_ball hεr
  have hUt : U ⊆ (extChartAt I α).target :=
    hUr.trans (Metric.ball_subset_closedBall.trans hball)
  have hpair := SpatialReg.SpC.pair (uniqueDiffOn_Icc hT) hUo h.2.2
    (SpatialReg.SpC.mono_n n h)
  set O : Set (E × ((E →L[ℝ] TensorRSModel 0 (s + i) ℝ E) × TensorRSModel 0 (s + i) ℝ E)) :=
    U ×ˢ univ with hO
  have hOo : IsOpen O := hUo.prod isOpen_univ
  set Ψ : ℝ × E × ((E →L[ℝ] TensorRSModel 0 (s + i) ℝ E) × TensorRSModel 0 (s + i) ℝ E) →
      TensorRSModel 0 (s + (i + 1)) ℝ E :=
    fun q => slotUnins E (s + i) (q.2.2.1 - kerL g α (s + i) B q.2.1 q.2.2.2) with hΨ
  have hK : ContDiffOn ℝ ∞ (fun q : ℝ × E × ((E →L[ℝ] TensorRSModel 0 (s + i) ℝ E) ×
      TensorRSModel 0 (s + i) ℝ E) => kerL g α (s + i) B q.2.1) (Icc 0 T ×ˢ O) := by
    have h1 := ((contDiffOn_kerL (g := g) α (s + i) B).mono hUt).comp
      (f := fun q : ℝ × E × ((E →L[ℝ] TensorRSModel 0 (s + i) ℝ E) ×
        TensorRSModel 0 (s + i) ℝ E) => q.2.1)
      (contDiff_fst.comp contDiff_snd).contDiffOn (t := U)
      (s := Icc 0 T ×ˢ O) (fun q hq => hq.2.1)
    simp only [Function.comp_def] at h1
    exact h1
  have hΨc : ContDiffOn ℝ ∞ Ψ (Icc 0 T ×ˢ O) := by
    have h2 : ContDiffOn ℝ ∞ (fun q : ℝ × E × ((E →L[ℝ] TensorRSModel 0 (s + i) ℝ E) ×
        TensorRSModel 0 (s + i) ℝ E) => q.2.2.1) (Icc 0 T ×ˢ O) :=
      (contDiff_fst.comp (contDiff_snd.comp contDiff_snd)).contDiffOn
    have h4 : ContDiffOn ℝ ∞ (fun q : ℝ × E × ((E →L[ℝ] TensorRSModel 0 (s + i) ℝ E) ×
        TensorRSModel 0 (s + i) ℝ E) => q.2.2.2) (Icc 0 T ×ˢ O) :=
      (contDiff_snd.comp (contDiff_snd.comp contDiff_snd)).contDiffOn
    have h3 := hK.clm_apply h4
    exact (slotUnins E (s + i)).contDiff.comp_contDiffOn (h2.sub h3)
  have hc := SpatialReg.SpC.comp (uniqueDiffOn_Icc hT) hUo (O := O) (Ψ := Ψ) hOo hΨc
    (fun t _ y hy => ⟨hy, trivial⟩) hpair
  refine SpatialReg.SpC.congr hUo n (fun t ht y hy => ?_) hc
  have hd := hasFDerivAt_jetChart (g := g) (s := s) (p := p) (m := m) hT hj hk hball hB v ht
    (hUr hy)
  rw [hd.fderiv]
  simp only [hΨ, add_sub_cancel_right]
  exact slotUnins_slotIns _

/-- **Regularity transfers along the jets**: if the representative is in `SpC k n` for all `n`, so
is `jetChart 0 i`, for `n/2 + 1 + i ≤ 2p(m-1)`. -/
theorem spC_jetChart (hT : 0 < T) (hm : 0 < m) {α : M} {r ε : ℝ}
    {B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (hball : Metric.closedBall (extChartAt I α α) r ⊆ (extChartAt I α).target)
    (hB : ∀ y ∈ Metric.closedBall (extChartAt I α α) r, ∀ k,
      trivToE I α ((extChartAt I α).symm y) (B k ((extChartAt I α).symm y)) =
        Module.finBasis ℝ E k)
    (hεr : ε ≤ r) (v : ParabolicSpace g s p m T) {k : ℕ}
    (h0 : ∀ n, SpatialReg.SpC k (Icc 0 T) (Metric.ball (extChartAt I α α) ε) n
      (TensorRSModel 0 s ℝ E) (repChart g s p m T α v)) :
    ∀ i, Module.finrank ℝ E / 2 + 1 + i ≤ 2 * p * (m - 0 - 1) → ∀ n,
      SpatialReg.SpC k (Icc 0 T) (Metric.ball (extChartAt I α α) ε) n
        (TensorRSModel 0 (s + i) ℝ E) (jetChart g s p m T α 0 i v) := by
  have hUt : Metric.ball (extChartAt I α α) ε ⊆ (extChartAt I α).target :=
    (Metric.ball_subset_ball hεr).trans (Metric.ball_subset_closedBall.trans hball)
  intro i
  induction i with
  | zero =>
    intro _ n
    exact SpatialReg.SpC.congr Metric.isOpen_ball n
      (fun t _ y hy => repChart_eq_jetChart α v t (hUt hy)) (h0 n)
  | succ i ih =>
    intro hk n
    exact spC_jetChart_succ hT hm hk hball hB hεr v
      (ih (le_trans (by omega) hk) (n + 1))

end SmoothRep

end ShortTime
