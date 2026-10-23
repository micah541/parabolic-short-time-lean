import ShortTime.Sanity.HeatEquation
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Inverse
import DifferentialGeometry.Geometry.Operator.Laplacian.Rough
import DifferentialGeometry.Tensor.RSTensor.Coordinates.BundleBasis

/-!
# The metric trace is a smooth bundle map (task T0, last part)

`traceSmooth g : TraceSmooth g`: the trace `traceCLM` of the first two slots is a smooth section
of `Hom(T^0_2, T^0_0)`. Read in the trivializations at `x₀`, it becomes
`z ↦ Σ_{kl} g^{kl} z(b_k, b_l)`, with smooth inverse-metric components.

Consequence: `heatData_zero_isParabolicSolution'` holds unconditionally. Every pinned definition
entering Theorems A–C has a genuine instance.
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

theorem evalSlot_apply_apply {s : ℕ} {x : M} (w : TangentSpace I x)
    (B : TensorRSSpace 0 (s + 1) I x) (D : Tensor0SSpace 0 I x) (v : Fin s → TangentSpace I x) :
    (evalSlot 0 s x w B) D v = B D (Fin.cons w v) := by
  rfl

theorem traceCLM_apply_apply (g : SmoothRiemannianMetric I M) {x : M}
    (B : TensorRSSpace 0 (0 + 1 + 1) I x) (D : Tensor0SSpace 0 I x) (v : Fin 0 → TangentSpace I x) :
    (traceCLM I M g 0 0 x B) D v =
      ∑ j, B D ![tangentFrame g x j, tangentFrame g x j] := by
  simp only [traceCLM, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.comp_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [evalSlot_apply_apply, evalSlot_apply_apply]
  have hv : v = ![] := Subsingleton.elim _ _
  subst hv
  rfl

/-- The trace, read in the trivializations at `x₀`. -/
theorem trace_inCoords_apply (g : SmoothRiemannianMetric I M) (x₀ x : M)
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hx0 : x ∈ (trivAt I M 0 0 x₀).baseSet) (hx2 : x ∈ (trivAt I M 0 (0 + 2 * 1) x₀).baseSet)
    (z : TensorRSModel 0 (0 + 2 * 1) ℝ E) (β : Tensor0SModel 0 ℝ E) (v : Fin 0 → E) :
    ((trivAt I M 0 0 x₀).continuousLinearMapAt ℝ x
        (traceCLM I M g 0 0 x ((trivAt I M 0 (0 + 2 * 1) x₀).symmL ℝ x z))) β v =
      ∑ j, z β ![(trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x
                  (tangentFrame g x j),
                (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x
                  (tangentFrame g x j)] := by
  rw [Trivialization.continuousLinearMapAt_apply, Trivialization.coe_linearMapAt_of_mem _ hx0]
  rw [TensorRSSpace.trivializationAt_apply (𝕜 := ℝ) (I := I) (x₀ := x₀) (x := x) 0 0 hx,
    traceCLM_apply_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hz : z = ((trivAt I M 0 (0 + 2 * 1) x₀)
      ⟨x, (trivAt I M 0 (0 + 2 * 1) x₀).symmL ℝ x z⟩).2 := by
    rw [Trivialization.symmL_apply _ hx2, Trivialization.apply_mk_symm _ hx2]
  conv_rhs => rw [hz]
  rw [TensorRSSpace.trivializationAt_apply (𝕜 := ℝ) (I := I) (x₀ := x₀) (x := x) 0 (0 + 2 * 1) hx]
  congr 1
  funext a
  fin_cases a <;>
    simp [Trivialization.continuousLinearMapAt_apply, Trivialization.symmL_apply _ hx,
      Trivialization.symm_linearMapAt _ hx]

theorem tangentFrame_linearIndependent (g : SmoothRiemannianMetric I M) (x : M) :
    LinearIndependent ℝ (tangentFrame g x) := by
  rw [linearIndependent_iff']
  intro fs c hsum k hk
  have h0 : g.inner x (tangentFrame g x k) (∑ j ∈ fs, c j • tangentFrame g x j) = 0 := by
    rw [hsum]; simp
  rw [map_sum] at h0
  simp only [map_smul, smul_eq_mul, tangentFrame_inner, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, if_pos hk] at h0
  exact h0

/-- `tangentFrame g x` as a basis of `T_xM`. -/
def tangentFrameBasis (g : SmoothRiemannianMetric I M) (x : M) :
    Module.Basis (Fin (Module.finrank ℝ (TangentSpace I x))) ℝ (TangentSpace I x) :=
  haveI : Nonempty (Fin (Module.finrank ℝ (TangentSpace I x))) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  basisOfLinearIndependentOfCardEqFinrank (tangentFrame_linearIndependent g x) (by simp)

theorem tangentFrameBasis_apply (g : SmoothRiemannianMetric I M) (x : M) (i) :
    tangentFrameBasis g x i = tangentFrame g x i := by
  simp [tangentFrameBasis]

theorem tangentFrameBasis_metricInverse (g : SmoothRiemannianMetric I M) (x : M) :
    MetricInverseInBasis (I := I) g x (tangentFrameBasis g x)
      (fun i j => if i = j then (1 : ℝ) else 0) := by
  intro i j
  constructor <;> simp [tangentFrameBasis_apply, tangentFrame_inner, mul_ite]

open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Geometry.Operator in
/-- Change of basis for the trace: an orthonormal frame versus the coordinate frame at `x₀`. -/
theorem trace_basis_change (g : SmoothRiemannianMetric I M) (x₀ x : M)
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (Z : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ) :
    ∑ j, Z ![(trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x (tangentFrame g x j),
            (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x (tangentFrame g x j)] =
      ∑ k : CoordinateIdx (𝕜 := ℝ) E, ∑ l : CoordinateIdx (𝕜 := ℝ) E,
        inverseMetricFlatModelInChartComponent (I := I) g x₀ k l (extChartAt I x₀ x) *
          Z ![Module.finBasis ℝ E k, Module.finBasis ℝ E l] := by
  classical
  have hx' : x ∈ coordinateFrameSet (I := I) x₀ := hx
  set τ := (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x
  let B₀ : Tensor0SSpace 2 I x :=
    Tensor0SSpace.ofModel (Z.compContinuousLinearMap (fun _ => τ))
  have hB : ∀ a b : TangentSpace I x, B₀ (DifferentialGeometry.Geometry.Curvature.vec2 a b) = Z ![τ a, τ b] := by
    intro a b
    show Z (fun i => τ (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) a b i)) = _
    congr 1; funext i; fin_cases i <;> rfl
  have horth := metricTracePair0SAt_eq_sum_basis g (tangentFrameBasis g x) _
    (tangentFrameBasis_metricInverse g x) B₀
  have hcoord := metricTracePair0SAt_eq_sum_basis g (coordinateFrameAtBasis (I := I) x₀ hx') _
    (gInvBasisAt (I := I) g x₀ hx') B₀
  rw [horth] at hcoord
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    tangentFrameBasis_apply, hB] at hcoord
  rw [hcoord]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have hτ : ∀ i, τ (coordinateFrameAtBasis (I := I) x₀ hx' i) = Module.finBasis ℝ E i := by
    intro i
    rw [coordinateFrameAt_basis_apply]
    simp only [coordinateFrameAt, Trivialization.localFrame_apply_of_mem_baseSet _ _ hx,
      Trivialization.basisAt, Module.Basis.map_apply, τ, Trivialization.continuousLinearMapAt_apply,
      Trivialization.coe_linearMapAt_of_mem _ hx]
    rw [Trivialization.linearEquivAt_symm_apply, Trivialization.apply_mk_symm _ hx]
  rw [hτ, hτ]

/-- The constant map `z ↦ (β ↦ z β (b_k, b_l))`, from `(0,2)`-model tensors to scalars. -/
def traceCoordCLM (k l : Fin (Module.finrank ℝ E)) :
    TensorRSModel 0 (0 + 2 * 1) ℝ E →L[ℝ] TensorRSModel 0 0 ℝ E :=
  ContinuousLinearMap.compL ℝ (Tensor0SModel 0 ℝ E) (Tensor0SModel (0 + 2 * 1) ℝ E)
      (Tensor0SModel 0 ℝ E)
    ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ))).comp
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (0 + 2 * 1) => E) ℝ
        ![Module.finBasis ℝ E k, Module.finBasis ℝ E l]))

theorem traceCoordCLM_apply (k l : Fin (Module.finrank ℝ E)) (z : TensorRSModel 0 (0 + 2 * 1) ℝ E)
    (β : Tensor0SModel 0 ℝ E) (v : Fin 0 → E) :
    traceCoordCLM k l z β v = z β ![Module.finBasis ℝ E k, Module.finBasis ℝ E l] := by
  simp [traceCoordCLM]

open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Geometry.Operator in
/-- **The metric trace is a smooth bundle map** (the last piece of T0). -/
theorem traceSmooth (g : SmoothRiemannianMetric I M) : TraceSmooth g := by
  intro x₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  have hG : ContMDiffAt I 𝓘(ℝ, TensorRSModel 0 (0 + 2 * 1) ℝ E →L[ℝ] TensorRSModel 0 0 ℝ E) ∞
      (fun x => ∑ k : CoordinateIdx (𝕜 := ℝ) E, ∑ l : CoordinateIdx (𝕜 := ℝ) E,
        inverseMetricFlatModelInChartComponent (I := I) g x₀ k l (extChartAt I x₀ x) •
          traceCoordCLM (E := E) k l) x₀ := by
    refine ContMDiffAt.sum fun k _ => ContMDiffAt.sum fun l _ => ?_
    exact (gInvComp_contMDiffAt (I := I) g x₀ k l).smul contMDiffAt_const
  refine hG.congr_of_eventuallyEq ?_
  have hx₀ : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) x₀
  filter_upwards [(trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hx₀,
    (trivAt I M 0 0 x₀).open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ x₀),
    (trivAt I M 0 (0 + 2 * 1) x₀).open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ x₀)]
    with x hx hx0 hx2
  ext z β v
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
  rw [trace_inCoords_apply g x₀ x hx hx0 hx2, trace_basis_change g x₀ x hx]
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  congr 1
  exact (traceCoordCLM_apply k l z β v).symm

/-- **Non-vacuity of `IsParabolicSolution`, unconditionally.** On any closed Riemannian manifold,
`u ≡ 0` is a parabolic solution of the heat equation on `[0,T₀]`. -/
theorem heatData_zero_isParabolicSolution' (g : SmoothRiemannianMetric I M) (T₀ : ℝ)
    (hT₀ : 0 < T₀) :
    (heatData g (traceSmooth g) T₀ hT₀).IsParabolicSolution g 0 T₀ (fun _ => 0) :=
  heatData_zero_isParabolicSolution g (traceSmooth g) T₀ hT₀

end ShortTime
