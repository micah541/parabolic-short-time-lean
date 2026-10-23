import ShortTime.Nonlinear.Raising

/-!
# Continuous dependence: reduction to covariant bundles

Paper: `cor:C`, with `lem:lowering`.

`solution_continuous_dependence_of_covariant` derives the statement of `cor:C` on `T^r_s M` from the
statement on the covariant bundles `T⁰_{s'} M`. As for Theorem A (`exists_solution_of_covariant`),
lower the equation with `EquationData.flatData`, lower `u` and the data `aₙ` with `flatCc`, apply the
covariant statement, and raise the solutions with `sharpCc`. Lowering is an isometry on fibres and
commutes with the covariant derivative up to a fixed slot permutation (`covJet_flatCc`), so the
convergence hypothesis and conclusion transfer.
-/

noncomputable section

open Bundle Manifold Set Filter
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

variable [CompleteSpace E] (g : SmoothRiemannianMetric I M)

/-- Lowering is additive on subtraction. -/
theorem flatCc_sub {r s : ℕ} (A B : SmoothCcTensor g r s) :
    flatCc g r s (A - B) = flatCc g r s A - flatCc g r s B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  change (flatCc g r s (A - B)).toSection x = (flatCc g r s A).toSection x - (flatCc g r s B).toSection x
  rw [flatCc_toSection, flatCc_toSection, flatCc_toSection]
  exact map_sub _ _ _

/-- The fibre norm of `∇^j(♭T)` equals that of `∇^j T`. -/
theorem fiberNorm_iteratedCovGrad_flatCc {r s : ℕ} (T : SmoothCcTensor g r s) (j : ℕ) (x : M) :
    fiberNorm g 0 ((r + s) + j) x ((iteratedCovGrad g 0 (r + s) j (flatCc g r s T)).toSection x) =
      fiberNorm g r (s + j) x ((iteratedCovGrad g r s j T).toSection x) := by
  have h := covJet_flatCc g j T x ⟨j, Nat.lt_succ_self j⟩
  simp only [covJet] at h
  unfold fiberNorm
  congr 1
  rw [h, fiberInner_slotPerm, fiberInner_flat]

/-- **`cor:C` reduces to covariant bundles.** -/
theorem solution_continuous_dependence_of_covariant {p : ℕ}
    (hcov : ∀ (s' : ℕ) (D' : EquationData I M 0 s' p) {u₀ : SmoothCcTensor g 0 s'} {T : ℝ}
      {u : ℝ → SmoothCcTensor g 0 s'}, D'.IsParabolicSolution g u₀ T u →
      ∀ (a : ℕ → SmoothCcTensor g 0 s'),
      (∀ j : ℕ, ∀ ε > 0, ∀ᶠ n in atTop, ∀ x : M,
        fiberNorm g 0 (s' + j) x ((iteratedCovGrad g 0 s' j (a n - u₀)).toSection x) ≤ ε) →
      ∃ w : ℕ → ℝ → SmoothCcTensor g 0 s',
        (∀ᶠ n in atTop, D'.IsParabolicSolution g (a n) T (w n)) ∧
        ∀ j : ℕ, ∀ ε > 0, ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
          fiberNorm g 0 (s' + j) x ((iteratedCovGrad g 0 s' j (w n t - u t)).toSection x) ≤ ε)
    {r s : ℕ} (D : EquationData I M r s p) {u₀ : SmoothCcTensor g r s} {T : ℝ}
    {u : ℝ → SmoothCcTensor g r s} (hu : D.IsParabolicSolution g u₀ T u)
    (a : ℕ → SmoothCcTensor g r s)
    (ha : ∀ j : ℕ, ∀ ε > 0, ∀ᶠ n in atTop, ∀ x : M,
      fiberNorm g r (s + j) x ((iteratedCovGrad g r s j (a n - u₀)).toSection x) ≤ ε) :
    ∃ w : ℕ → ℝ → SmoothCcTensor g r s,
      (∀ᶠ n in atTop, D.IsParabolicSolution g (a n) T (w n)) ∧
      ∀ j : ℕ, ∀ ε > 0, ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        fiberNorm g r (s + j) x ((iteratedCovGrad g r s j (w n t - u t)).toSection x) ≤ ε := by
  obtain ⟨w', hw'sol, hw'conv⟩ := hcov (r + s) (D.flatData g)
    ((D.isParabolicSolution_flatData g (u := u) (u₀ := u₀) hu))
    (fun n => flatCc g r s (a n)) (fun j ε hε => by
      filter_upwards [ha j ε hε] with n hn x
      rw [← flatCc_sub, fiberNorm_iteratedCovGrad_flatCc]
      exact hn x)
  refine ⟨fun n t => sharpCc g r s (w' n t), ?_, ?_⟩
  · filter_upwards [hw'sol] with n hn
    refine D.isParabolicSolution_of_flatData g ?_
    simp only [flatCc_sharpCc]
    exact hn
  · intro j ε hε
    filter_upwards [hw'conv j ε hε] with n hn t ht x
    have h := hn t ht x
    have e : w' n t - flatCc g r s (u t) = flatCc g r s (sharpCc g r s (w' n t) - u t) := by
      rw [flatCc_sub, flatCc_sharpCc]
    rw [e, fiberNorm_iteratedCovGrad_flatCc] at h
    exact h

end ShortTime
