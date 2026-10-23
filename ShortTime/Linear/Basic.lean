import ShortTime.Setting.LinearData

/-!
# Sobolev norms of smooth tensor fields (`def:sobolev`)

Positive orders by covariant derivatives, negative orders by duality. The linear operators live in
`ShortTime.Linear.Operator`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open scoped Manifold ContDiff

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-! ### Sobolev norms (`def:sobolev`) -/

/-- `‖u‖²_{H^k} = Σ_{i ≤ k} ‖∇^i u‖²_{L²}`. -/
def sobolevNormSq (g : SmoothRiemannianMetric I M) (r s k : ℕ) (u : SmoothCcTensor g r s) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), tensorL2Norm g r (s + i) (iteratedCovGrad g r s i u).toFun ^ 2

/-- `‖u‖_{H^k}`. -/
def sobolevNorm (g : SmoothRiemannianMetric I M) (r s k : ℕ) (u : SmoothCcTensor g r s) : ℝ :=
  Real.sqrt (sobolevNormSq g r s k u)

/-- The negative-order norm `‖f‖_{H^{-k}} = sup {⟨f, φ⟩ : ‖φ‖_{H^k} ≤ 1}`. -/
def negSobolevNorm (g : SmoothRiemannianMetric I M) (r s k : ℕ) (f : SmoothCcTensor g r s) : ℝ :=
  sSup ((fun φ : SmoothCcTensor g r s => tensorL2Inner g r s f.toFun φ.toFun) ''
    {φ | sobolevNorm g r s k φ ≤ 1})

/-- The squared `H^k` norm for an integer order `k`: positive orders by covariant derivatives,
negative orders by duality. -/
def hNormSq (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℤ) (u : SmoothCcTensor g r s) : ℝ :=
  if 0 ≤ k then sobolevNormSq g r s k.toNat u else negSobolevNorm g r s (-k).toNat u ^ 2

end ShortTime
