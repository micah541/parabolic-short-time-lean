import ShortTime.Nonlinear.ContinuousDependenceMain
import ShortTime.Setting.Equation
import ShortTime.Nonlinear.UniquenessB
import ShortTime.Nonlinear.Raising
import ShortTime.Nonlinear.ExistenceCov

/-!
# Main theorems (paper: Theorems A, B, C)

These are the statements the project exists to prove. They mention only smooth tensor fields,
covariant derivatives, time derivatives and the pointwise Legendre condition. The parabolic
Sobolev spaces of the paper are internal to the proofs.

Status: statements drafted; to be reviewed and then pinned with
`python scripts/blueprint.py pin ShortTime.exists_solution ...`.
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

/-- **Theorem A** (existence and regularity, `thm:A`). If the equation is parabolic at the
initial datum, there is a smooth parabolic solution on some `[0,T]`. -/
theorem exists_solution (D : EquationData I M r s p) (hp : 1 ≤ p)
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothCcTensor g r s)
    (h₀ : ∀ x : M, D.IsParabolicAt g 0 x (covJet g r s (2 * p) u₀ x)) :
    ∃ T > 0, ∃ u : ℝ → SmoothCcTensor g r s, D.IsParabolicSolution g u₀ T u :=
  exists_solution_of_covariant g (fun _ D' u₀' h => D'.exists_solution_cov hp g u₀' h) D u₀ h₀

/-- **Theorem B** (uniqueness, `thm:B`). Two parabolic solutions on `[0,T]` with the same initial
datum coincide on `[0,T]`. -/
theorem solution_unique (D : EquationData I M r s p) (hp : 1 ≤ p)
    (g : SmoothRiemannianMetric I M) {u₀ : SmoothCcTensor g r s} {T : ℝ}
    {u v : ℝ → SmoothCcTensor g r s}
    (hu : D.IsParabolicSolution g u₀ T u) (hv : D.IsParabolicSolution g u₀ T v) :
    ∀ t ∈ Icc (0 : ℝ) T, u t = v t :=
  solution_unique_of_covariant g (fun _ D' _ _ _ _ hu' hv' => D'.solution_unique_cov g hu' hv')
    D hu hv

/-- **Theorem C** (continuous dependence, sequential form of `thm:C`). Let `u` be a parabolic
solution on `[0,T]`, and let `aₙ → u₀` in `C^∞`, i.e. every covariant derivative converges
uniformly. Then for large `n` the parabolic solution with datum `aₙ` exists on the same `[0,T]`,
and it converges to `u` in `C^∞`. More precisely, every covariant derivative converges uniformly on
`M × [0,T]`; convergence of time derivatives then follows from the equation. -/
theorem solution_continuous_dependence (D : EquationData I M r s p) (hp : 1 ≤ p)
    (g : SmoothRiemannianMetric I M) {u₀ : SmoothCcTensor g r s} {T : ℝ}
    {u : ℝ → SmoothCcTensor g r s} (hu : D.IsParabolicSolution g u₀ T u)
    (a : ℕ → SmoothCcTensor g r s)
    (ha : ∀ j : ℕ, ∀ ε > 0, ∀ᶠ n in atTop, ∀ x : M,
      fiberNorm g r (s + j) x ((iteratedCovGrad g r s j (a n - u₀)).toSection x) ≤ ε) :
    ∃ w : ℕ → ℝ → SmoothCcTensor g r s,
      (∀ᶠ n in atTop, D.IsParabolicSolution g (a n) T (w n)) ∧
      ∀ j : ℕ, ∀ ε > 0, ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        fiberNorm g r (s + j) x ((iteratedCovGrad g r s j (w n t - u t)).toSection x) ≤ ε := by
  exact solution_continuous_dependence' D hp g hu a ha

end ShortTime
