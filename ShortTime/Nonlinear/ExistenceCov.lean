import ShortTime.Nonlinear.ExistenceAssembly

/-!
# Theorem A on covariant bundles

`EquationData.exists_solution_cov` is Theorem A for `T⁰_s M`. It is assembled from
`prop:existence` and `prop:regularity` in `ExistenceAssembly.lean`; the regularity statement
`parabolicSpace_solution_smooth` is still `sorry`. Theorem A for `T^r_s M`
follows by lowering indices (`exists_solution_of_covariant`, `Raising.lean`).
-/

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open scoped Manifold ContDiff

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

namespace EquationData

/-- **Theorem A on covariant bundles** (`thm:A`, `r = 0`). -/
theorem exists_solution_cov {s p : ℕ} (D : EquationData I M 0 s p) (hp : 1 ≤ p)
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothCcTensor g 0 s)
    (h₀ : ∀ x : M, D.IsParabolicAt g 0 x (covJet g 0 s (2 * p) u₀ x)) :
    ∃ T > 0, ∃ u : ℝ → SmoothCcTensor g 0 s, D.IsParabolicSolution g u₀ T u :=
  D.exists_solution_cov' hp g u₀ h₀

end EquationData

end ShortTime
