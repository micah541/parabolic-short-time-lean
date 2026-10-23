import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Bounds.Contraction
import DifferentialGeometry.Analysis.Integration.L2.Pairing.CauchySchwarz
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Integrability
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Inner

/-!
# `L²` bounds for operator fields

If an operator field `Φ : T⁰_a → T⁰_b` satisfies `|Φ(x)|² ≤ K` pointwise (fibre norm of the
`T^a_b`-tensor), then `‖Φ W‖² ≤ K ‖W‖²` and `|⟨S, Φ W⟩| ≤ √K ‖S‖ ‖W‖`. These are the estimates
behind every lower-order term in Gårding's inequality.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Spectral DifferentialGeometry.Analysis.Elliptic
open scoped Manifold ContDiff BigOperators

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

variable (g : SmoothRiemannianMetric I M)

/-- `‖S‖² = ∫ |S|²`, with the pointwise square norm written as a fibre norm. -/
theorem tensorL2Inner_self_eq_integral (r s : ℕ) (S : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  unfold tensorL2Inner
  congr 1
  funext x
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise]
  rfl

theorem integrable_riemannianFiberNormSq_cc (r s : ℕ) (S : SmoothCcTensor g r s) :
    Integrable (fun x => riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  have h := SmoothCcTensor.integrable_inner_cross (I := I) (M := M) S S
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  exact (riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x
    (S.toSection x)).symm

/-- `‖Φ W‖² ≤ K ‖W‖²` if `|Φ|² ≤ K` pointwise. -/
theorem normSq_operatorFieldApply_le (a b : ℕ) (Φ : SmoothCcTensor g a b) {K : ℝ}
    (hK : ∀ x, riemannianFiberNormSq (I := I) (M := M) g a b x (Φ.toSection x) ≤ K)
    (W : SmoothCcTensor g 0 a) :
    tensorL2Inner (I := I) (M := M) g 0 b (operatorFieldApply (I := I) (M := M) g a b Φ W).toFun
        (operatorFieldApply (I := I) (M := M) g a b Φ W).toFun ≤
      K * tensorL2Inner (I := I) (M := M) g 0 a W.toFun W.toFun := by
  rw [tensorL2Inner_self_eq_integral, tensorL2Inner_self_eq_integral, ← integral_const_mul]
  refine integral_mono (integrable_riemannianFiberNormSq_cc g 0 b _)
    ((integrable_riemannianFiberNormSq_cc g 0 a W).const_mul K) fun x => ?_
  rw [operatorFieldApplication_toSection]
  refine (riemannianFiberNormSq_comp_le_mul (I := I) (M := M) g a b x
    (Φ.toSection x) (W.toSection x)).trans ?_
  exact mul_le_mul_of_nonneg_right (hK x)
    (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 a x (W.toSection x))

/-- Cauchy–Schwarz for smooth covariant tensor fields. -/
theorem abs_inner_le_norm_mul_norm (r s : ℕ) (S T : SmoothCcTensor g r s) :
    |tensorL2Inner (I := I) (M := M) g r s S.toFun T.toFun| ≤
      tensorL2Norm (I := I) (M := M) g r s S.toFun * tensorL2Norm (I := I) (M := M) g r s T.toFun :=
  abs_tensorL2Inner_le (I := I) (M := M) g r s S.toFun T.toFun
    (SmoothCcTensor.memL2_toFun S) (SmoothCcTensor.memL2_toFun T)
    (SmoothCcTensor.integrable_inner_cross S T)

/-- `|⟨S, Φ W⟩| ≤ √K ‖S‖ ‖W‖` if `|Φ|² ≤ K` pointwise. -/
theorem abs_inner_operatorFieldApply_le (a b : ℕ) (Φ : SmoothCcTensor g a b) {K : ℝ}
    (hK0 : 0 ≤ K) (hK : ∀ x, riemannianFiberNormSq (I := I) (M := M) g a b x (Φ.toSection x) ≤ K)
    (S : SmoothCcTensor g 0 b) (W : SmoothCcTensor g 0 a) :
    |tensorL2Inner (I := I) (M := M) g 0 b S.toFun
        (operatorFieldApply (I := I) (M := M) g a b Φ W).toFun| ≤
      Real.sqrt K * tensorL2Norm (I := I) (M := M) g 0 b S.toFun *
        tensorL2Norm (I := I) (M := M) g 0 a W.toFun := by
  refine (abs_inner_le_norm_mul_norm g 0 b S _).trans ?_
  have hW : tensorL2Norm (I := I) (M := M) g 0 b
      (operatorFieldApply (I := I) (M := M) g a b Φ W).toFun ≤
      Real.sqrt K * tensorL2Norm (I := I) (M := M) g 0 a W.toFun := by
    unfold tensorL2Norm
    rw [← Real.sqrt_mul hK0]
    exact Real.sqrt_le_sqrt (normSq_operatorFieldApply_le g a b Φ hK W)
  calc tensorL2Norm (I := I) (M := M) g 0 b S.toFun *
        tensorL2Norm (I := I) (M := M) g 0 b (operatorFieldApply (I := I) (M := M) g a b Φ W).toFun
      ≤ tensorL2Norm (I := I) (M := M) g 0 b S.toFun *
          (Real.sqrt K * tensorL2Norm (I := I) (M := M) g 0 a W.toFun) :=
        mul_le_mul_of_nonneg_left hW (tensorL2Norm_nonneg (I := I) (M := M) g 0 b _)
    _ = _ := by ring

end ShortTime
