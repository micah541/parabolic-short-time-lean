import ShortTime.Setting.LinearData
import ShortTime.Sanity.LegendreTrace

/-!
# The heat equation as a parabolic `EquationData` (task T0, part 3)

For scalar functions, the heat equation `∂ₜu = tr_g ∇²u` is the linear equation whose coefficient
is `traceCLM`. Assuming only that `traceCLM` is a smooth section of `Hom(T^0_2, T^0_0)`
(`traceSmooth`, the one remaining piece of T0), this file shows:

* the heat equation is valid `EquationData`, and it is parabolic at every jet;
* `u ≡ 0` is a *parabolic* solution on `[0,T₀]`.

So every pinned definition entering Theorems A–C has a genuine instance.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set
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

/-- `∇^j 0 = 0`. -/
theorem iteratedCovGrad_zero_tensor (g : SmoothRiemannianMetric I M) (r s j : ℕ) :
    iteratedCovGrad g r s j (0 : SmoothCcTensor g r s) = 0 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g r (s + j)
      (iteratedCovGrad g r s j 0) = 0
    rw [ih]
    have h := Analysis.Parabolic.TensorSpectral.covGrad_add (I := I) (M := M) g r (s + j) 0 0
    rw [add_zero] at h
    exact left_eq_add.mp h

/-- The statement that the metric trace is a smooth bundle map: the one remaining piece of T0. -/
def TraceSmooth (g : SmoothRiemannianMetric I M) : Prop :=
  SmoothHomSection I M 0 (0 + 2 * 1) 0 (fun x => traceCLM I M g 0 0 x)

/-- The heat equation `∂ₜu = tr_g ∇²u` on functions. -/
def heatData (g : SmoothRiemannianMetric I M) (hg : TraceSmooth g) (T₀ : ℝ) (hT₀ : 0 < T₀) :
    EquationData I M 0 0 1 :=
  linearData I M 0 0 1 T₀ hT₀ (fun x => traceCLM I M g 0 0 x) hg

/-- The heat equation is parabolic at every jet. -/
theorem heatData_isParabolicAt (g : SmoothRiemannianMetric I M) (hg : TraceSmooth g) (T₀ : ℝ)
    (hT₀ : 0 < T₀) (t : ℝ) (x : M) (ζ : CovJetFiber I 0 0 (2 * 1) x) :
    (heatData g hg T₀ hT₀).IsParabolicAt g t x ζ := by
  refine ⟨Set.mem_univ _, 1, ?_⟩
  have hP : (heatData g hg T₀ hT₀).principal t x ζ = traceCLM I M g 0 0 x := by
    refine ContinuousLinearMap.ext fun ξ => ?_
    exact (linearData_principal (I := I) (M := M) 0 0 1 T₀ hT₀ _ hg t x ζ ξ).trans rfl
  rw [hP]
  exact legendreAt_traceCLM g 0 x

/-- **Non-vacuity of `IsParabolicSolution`.** `u ≡ 0` is a parabolic solution of the heat
equation on `[0,T₀]`, with initial datum `0`. -/
theorem heatData_zero_isParabolicSolution (g : SmoothRiemannianMetric I M) (hg : TraceSmooth g)
    (T₀ : ℝ) (hT₀ : 0 < T₀) :
    (heatData g hg T₀ hT₀).IsParabolicSolution g 0 T₀ (fun _ => 0) := by
  refine ⟨⟨hT₀, le_rfl, ?_, rfl, fun _ _ _ => Set.mem_univ _, ?_⟩,
    fun t _ x => heatData_isParabolicAt g hg T₀ hT₀ t x _⟩
  · exact ((0 : SmoothCcTensor g 0 0).toSection.contMDiff.comp contMDiff_fst).contMDiffOn
  · intro t _ x
    have hjet : covJet g 0 0 (2 * 1) (0 : SmoothCcTensor g 0 0) x = 0 := by
      funext k
      simp [covJet, iteratedCovGrad_zero_tensor, SmoothCcTensor.toSection_zero]
    have hF : (heatData g hg T₀ hT₀).F t x (covJet g 0 0 (2 * 1) 0 x) = 0 := by
      rw [hjet]
      exact map_zero (traceCLM I M g 0 0 x)
    rw [hF, TensorRSSpace.toModel_zero]
    exact hasDerivWithinAt_const t (Icc 0 T₀) _

end ShortTime
