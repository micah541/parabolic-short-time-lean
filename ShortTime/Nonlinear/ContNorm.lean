import ShortTime.Nonlinear.ParabolicBound
import ShortTime.Sanity.HeatEquation

/-!
# The norm of a time-independent family in `𝒫^m` (`cor:C`)

A family `t ↦ h` that does not depend on `t` has no time derivatives, so
`‖h‖²_{𝒫^m} = Σ_{i ≤ 2pm} T ∫ |∇^i h|²`. Hence it is small in `𝒫^m` as soon as `∇^i h` is small
uniformly for `i ≤ 2pm`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter Topology MeasureTheory Metric
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Spectral
open scoped Manifold ContDiff BigOperators

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

variable {g : SmoothRiemannianMetric I M} {s : ℕ} {T : ℝ}

/-- The time derivative of a time-independent family vanishes. -/
theorem timeDeriv_const (hT : 0 < T) (h : SmoothCcTensor g 0 s) :
    timeDeriv T (fun _ => h) = fun _ => 0 := by
  funext t
  by_cases ht : t ∈ Icc (0 : ℝ) T
  · apply SmoothCcTensor.ext
    apply ContMDiffSection.ext
    intro x
    change (timeDeriv T (fun _ => h) t).toSection x = (0 : SmoothCcTensor g 0 s).toSection x
    have h1 := hasDerivWithinAt_timeDeriv hT (jointlySmoothOn_const (g := g) (Icc 0 T) h) ht x
    have h2 : HasDerivWithinAt (fun _ : ℝ => TensorRSSpace.toModel (h.toSection x)) 0 (Icc 0 T) t :=
      hasDerivWithinAt_const _ _ _
    have h3 := ((uniqueDiffOn_Icc hT) t ht).eq_deriv _ h1 h2
    refine TensorRSSpace.toModel_injective (I := I) (r := 0) (s := s) (x := x) ?_
    show TensorRSSpace.toModel ((timeDeriv T (fun _ => h) t).toSection x) =
      TensorRSSpace.toModel ((SmoothCcTensor.toSection (0 : SmoothCcTensor g 0 s)) x)
    rw [h3]
    simp [SmoothCcTensor.toSection_zero]
  · exact timeDeriv_of_not_mem ht

theorem timeDerivIter_const_succ (hT : 0 < T) (h : SmoothCcTensor g 0 s) (j : ℕ) :
    timeDerivIter T (fun _ => h) (j + 1) = fun _ => 0 := by
  induction j with
  | zero => exact timeDeriv_const hT h
  | succ j ih =>
    change timeDeriv T (timeDerivIter T (fun _ => h) (j + 1)) = _
    rw [ih]
    exact timeDeriv_const hT 0

/-- **The `𝒫^m` norm of a time-independent family.** -/
theorem parabolicInner_const_le (hT : 0 < T) (p m : ℕ) (h : SmoothCcTensor g 0 s) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hh : ∀ i ≤ 2 * p * m, ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
        ((iteratedCovGrad g 0 s i h).toSection x) ≤ ε) :
    parabolicInner g s p m T (fun _ => h) (fun _ => h) ≤
      ε * parabolicCount p m * (T * (riemannianVolumeMeasure (I := I) (M := M) g).real univ + 1) := by
  have key := parabolicInner_le_of_jetSq_le (g := g) (T := T) (p := p) (N := m) (ι := Empty)
    (b := fun e => nomatch e) hT (φ := fun _ => h) (jointlySmoothOn_const (g := g) (Icc 0 T) h)
    (V := fun e => nomatch e) (hV := fun e => nomatch e) (C := ε) hε ?_
  · simpa using key
  · intro j i hj hi t ht x
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, mul_one]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact hh i (by have : 2 * p * (m - 0) = 2 * p * m := by simp
                     omega) x
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      unfold jetSq
      rw [timeDerivIter_const_succ hT h j']
      simp only [iteratedCovGrad_zero_tensor, SmoothCcTensor.toSection_zero]
      exact (riemannianFiberNormSq_zero (I := I) (M := M) g 0 (s + i) x).le.trans hε

end ShortTime
