import ShortTime.Linear.Parabolic

/-!
# Pointwise squared jets of time-dependent tensor fields

`jetSq g T V j i t x = |∂ₜ^j ∇^i V(t, x)|²`, the pointwise quantity whose integrals make up the norm
of the parabolic spaces `𝒫^m` (`def:parabolic`).
-/

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Elliptic
open scoped Manifold ContDiff

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- `|∂ₜ^j ∇^i V(t, x)|²`, with time derivatives taken within `[0,T]`. -/
def jetSq (g : SmoothRiemannianMetric I M) {a : ℕ} (T : ℝ) (V : ℝ → SmoothCcTensor g 0 a) (j i : ℕ) (t : ℝ) (x : M) : ℝ :=
  riemannianFiberNormSq (I := I) (M := M) g 0 (a + i) x
    ((iteratedCovGrad g 0 a i (timeDerivIter T V j t)).toSection x)

end ShortTime
