import ShortTime.Nonlinear.SmoothRepTimeChart
import ShortTime.Nonlinear.Existence

/-!
# The time derivative on `𝒫^m` and the jets of the representative

* `evalJet_timeDerivExt`: `evalJet (m-1) 0 0 (∂ₜ U) = evalJet m 1 0 U`.
* `jetChart_timeDerivExt`: the same in the chart readings.
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

/-- `evalJet 0 0` of `∂ₜ U` is `evalJet 1 0` of `U`. -/
theorem evalJet_timeDerivExt (hT : 0 < T) (hm1 : 1 ≤ m) (hm2 : 2 ≤ m)
    (hk : Module.finrank ℝ E / 2 + 1 ≤ 2 * p * (m - 2)) {t : ℝ} (ht : t ∈ Icc 0 T) (x : M)
    (U : ParabolicSpace g s p m T) :
    evalJet g s p (m - 1) T 0 0 t x (timeDerivExt hT hm1 U) = evalJet g s p m T 1 0 t x U := by
  have hk1 : Module.finrank ℝ E / 2 + 1 + 0 ≤ 2 * p * (m - 1 - 0 - 1) := by
    have : m - 1 - 0 - 1 = m - 2 := by omega
    rw [this]; omega
  have hk2 : Module.finrank ℝ E / 2 + 1 + 0 ≤ 2 * p * (m - 1 - 1) := by
    have : m - 1 - 1 = m - 2 := by omega
    rw [this]; omega
  refine UniformSpace.Completion.induction_on U
    (isClosed_eq ((evalJet g s p (m - 1) T 0 0 t x).continuous.comp
      (timeDerivExt hT hm1).continuous) (evalJet g s p m T 1 0 t x).continuous) fun u => ?_
  have e : (u : ParabolicSpace g s p m T) = ofSmooth u.family u.2 := rfl
  have h1 := timeDerivExt_ofSmooth (g := g) (p := p) hT hm1 u.2
  have h2 := evalJet_ofSmooth (g := g) (p := p) hT (j := 0) (i := 0) (m := m - 1) (by omega) hk1 ht x
    (jointlySmoothOn_timeDeriv hT u.2)
  have h3 := evalJet_ofSmooth (g := g) (p := p) hT (j := 1) (i := 0) (m := m) (by omega) hk2 ht x u.2
  rw [e]
  erw [h1, h2, h3]
  rfl

theorem jetChart_timeDerivExt (hT : 0 < T) (hm1 : 1 ≤ m) (hm2 : 2 ≤ m)
    (hk : Module.finrank ℝ E / 2 + 1 ≤ 2 * p * (m - 2)) (α : M) {t : ℝ} (ht : t ∈ Icc 0 T)
    (y : E) (U : ParabolicSpace g s p m T) :
    jetChart g s p (m - 1) T α 0 0 (timeDerivExt hT hm1 U) t y = jetChart g s p m T α 1 0 U t y := by
  unfold jetChart
  rw [evalJet_timeDerivExt hT hm1 hm2 hk ht]

end SmoothRep

end ShortTime
