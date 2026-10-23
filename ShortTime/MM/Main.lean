import ShortTime.MM.Rearranged
import ShortTime.MainTheorems

/-!
# The Mantegazza–Martinazzi theorem (paper: `cor:MM`)

For the scalar quasilinear equation `∂ₜu = (-1)^{p-1} E₁^{i₁j₁}⋯E_p^{i_pj_p} ∇_{i₁j₁⋯i_pj_p}u + b`
with positive definite `E_ℓ`, every point of the domain is parabolic after the rearrangement of
`rem:rewrite`, which does not change the solutions (`MMData.rearranged_isSolution_iff`). Theorems
A, B and C therefore apply to the rearranged equation and, through the equivalence of solutions,
to the equation as written.
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
variable [CompleteSpace E]
variable {p : ℕ}

/-- Every solution of the MM equation is a *parabolic* solution of its rearrangement. -/
theorem MMData.isParabolicSolution_rearranged (d : MMData I M p) (hp : 1 ≤ p)
    (g : SmoothRiemannianMetric I M) {u₀ : SmoothCcTensor g 0 0} {T : ℝ}
    {u : ℝ → SmoothCcTensor g 0 0} (hu : d.toEquationData.IsSolution g u₀ T u) :
    (d.rearranged g).IsParabolicSolution g u₀ T u :=
  ⟨(d.rearranged_isSolution_iff g).2 hu, fun t ht x =>
    d.rearranged_isParabolicAt g hp ⟨ht.1, ht.2.trans hu.le_T₀⟩ (hu.jets_mem t ht x)⟩

/-- **Mantegazza–Martinazzi** (`cor:MM`). For the MM equation `d` (positive definite product
coefficients `E_ℓ`, smooth data, domain `d.dom`), with `solution` meaning
`d.toEquationData.IsSolution`:
* existence: every smooth initial datum whose jet lies in the domain has a smooth solution on some
  `[0,T]`;
* uniqueness: two solutions with the same datum coincide on `[0,T]`;
* continuous dependence: if `aₙ → u₀` in `C^∞` and `u` solves with datum `u₀` on `[0,T]`, then for
  large `n` the solution with datum `aₙ` exists on `[0,T]` and converges to `u` in `C^∞`. -/
theorem mantegazza_martinazzi (d : MMData I M p) (hp : 1 ≤ p)
    (g : SmoothRiemannianMetric I M) :
    (∀ u₀ : SmoothCcTensor g 0 0, (∀ x : M, covJet g 0 0 (2 * p) u₀ x ∈ d.dom 0 x) →
      ∃ T > 0, ∃ u : ℝ → SmoothCcTensor g 0 0, d.toEquationData.IsSolution g u₀ T u) ∧
    (∀ (u₀ : SmoothCcTensor g 0 0) (T : ℝ) (u v : ℝ → SmoothCcTensor g 0 0),
      d.toEquationData.IsSolution g u₀ T u → d.toEquationData.IsSolution g u₀ T v →
      ∀ t ∈ Icc (0 : ℝ) T, u t = v t) ∧
    (∀ (u₀ : SmoothCcTensor g 0 0) (T : ℝ) (u : ℝ → SmoothCcTensor g 0 0),
      d.toEquationData.IsSolution g u₀ T u →
      ∀ a : ℕ → SmoothCcTensor g 0 0,
      (∀ j : ℕ, ∀ ε > 0, ∀ᶠ n in atTop, ∀ x : M,
        fiberNorm g 0 (0 + j) x ((iteratedCovGrad g 0 0 j (a n - u₀)).toSection x) ≤ ε) →
      ∃ w : ℕ → ℝ → SmoothCcTensor g 0 0,
        (∀ᶠ n in atTop, d.toEquationData.IsSolution g (a n) T (w n)) ∧
        ∀ j : ℕ, ∀ ε > 0, ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
          fiberNorm g 0 (0 + j) x ((iteratedCovGrad g 0 0 j (w n t - u t)).toSection x) ≤ ε) := by
  refine ⟨fun u₀ h₀ => ?_, fun u₀ T u v hu hv => ?_, fun u₀ T u hu a ha => ?_⟩
  · obtain ⟨T, hT, u, hu⟩ := exists_solution (d.rearranged g) hp g u₀
      (fun x => d.rearranged_isParabolicAt g hp ⟨le_rfl, d.T₀_pos.le⟩ (h₀ x))
    exact ⟨T, hT, u, (d.rearranged_isSolution_iff g).1 hu.1⟩
  · exact solution_unique (d.rearranged g) hp g (d.isParabolicSolution_rearranged hp g hu)
      (d.isParabolicSolution_rearranged hp g hv)
  · obtain ⟨w, hw, hc⟩ := solution_continuous_dependence (d.rearranged g) hp g
      (d.isParabolicSolution_rearranged hp g hu) a ha
    exact ⟨w, hw.mono fun n hn => (d.rearranged_isSolution_iff g).1 hn.1, hc⟩

end ShortTime
