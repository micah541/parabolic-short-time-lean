import ShortTime.Nonlinear.ContinuousDependenceLower
import ShortTime.Nonlinear.ContinuousDependenceCov
import ShortTime.Nonlinear.RegularityTraceFinal

/-!
# Continuous dependence (`cor:C`) on `T^r_s M`

`solution_continuous_dependence'` has the statement of `ShortTime.solution_continuous_dependence`
(`MainTheorems.lean`); it is the covariant case `continuous_dependence_cov`, with regularity from
`EquationData.traceRegularity`, carried to `T^r_s` by lowering indices.
-/

noncomputable section

open Bundle Manifold Set Filter
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open scoped Manifold ContDiff Topology

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable {r s p : ℕ}

theorem solution_continuous_dependence' (D : EquationData I M r s p) (hp : 1 ≤ p)
    (g : SmoothRiemannianMetric I M) {u₀ : SmoothCcTensor g r s} {T : ℝ}
    {u : ℝ → SmoothCcTensor g r s} (hu : D.IsParabolicSolution g u₀ T u)
    (a : ℕ → SmoothCcTensor g r s)
    (ha : ∀ j : ℕ, ∀ ε > 0, ∀ᶠ n in atTop, ∀ x : M,
      fiberNorm g r (s + j) x ((iteratedCovGrad g r s j (a n - u₀)).toSection x) ≤ ε) :
    ∃ w : ℕ → ℝ → SmoothCcTensor g r s,
      (∀ᶠ n in atTop, D.IsParabolicSolution g (a n) T (w n)) ∧
      ∀ j : ℕ, ∀ ε > 0, ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        fiberNorm g r (s + j) x ((iteratedCovGrad g r s j (w n t - u t)).toSection x) ≤ ε := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact solution_continuous_dependence_of_covariant g
    (fun s' D' _ _ _ hu' a' ha' => D'.continuous_dependence_cov hp (D'.traceRegularity g) hu' a' ha')
    D hu a ha

end ShortTime
