import ShortTime.Setting.Legendre
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.Lowering
import DifferentialGeometry.Geometry.Metric.PointwiseInner.SlotPermutation

/-!
# Lowering indices fibrewise

Paper: Lemma `lem:lowering`, the fibrewise part.

Lowering all indices with `g` is a linear isometry `♭ : T^r_s|_x ≃ T⁰_{r+s}|_x`
(`flat`). Slot permutations of covariant tensors, more generally relabellings along
`Fin a ≃ Fin b`, are linear isometries (`slotPerm`). Both are built in the model spaces from the
library's `lowerAllUpperIndicesEquiv` and `domDomCongr`. The model of `T⁰_n` is `Hom(T⁰_0, T⁰_n)`, identified with `n`-forms by
evaluation at the unit scalar (`unitEquiv`).
-/

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff

set_option linter.unusedSectionVars false

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-! ### Covariant tensors as `n`-forms -/

section Model

variable (E) in
/-- The unit model `0`-tensor. -/
def unit0M : Tensor0SModel 0 ℝ E := ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) 1

variable (E) in
/-- The scalar of a model `0`-tensor. -/
def scalar0M : Tensor0SModel 0 ℝ E →L[ℝ] ℝ :=
  ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => E) ℝ Fin.elim0

theorem scalar0M_apply (D : Tensor0SModel 0 ℝ E) : scalar0M E D = D Fin.elim0 := rfl

theorem scalar0M_unit0M : scalar0M E (unit0M E) = 1 := rfl

theorem eq_scalar0M_smul_unit0M (D : Tensor0SModel 0 ℝ E) : D = scalar0M E D • unit0M E := by
  refine ContinuousMultilinearMap.ext fun v => ?_
  have hv : v = Fin.elim0 := Subsingleton.elim _ _
  subst hv
  simp [scalar0M_apply, unit0M]

variable (E) in
/-- The model of `T⁰_n` is `Hom(T⁰_0, T⁰_n) ≅ T⁰_n`, by evaluation at the unit scalar. -/
def unitEquiv (n : ℕ) : TensorRSModel 0 n ℝ E ≃L[ℝ] Tensor0SModel n ℝ E :=
  ContinuousLinearEquiv.equivOfInverse
    (ContinuousLinearMap.apply ℝ (Tensor0SModel n ℝ E) (unit0M E))
    (ContinuousLinearMap.smulRightL ℝ (Tensor0SModel 0 ℝ E) (Tensor0SModel n ℝ E) (scalar0M E))
    (fun T => by
      refine ContinuousLinearMap.ext fun D => ?_
      change scalar0M E D • T (unit0M E) = T D
      conv_rhs => rw [eq_scalar0M_smul_unit0M D, map_smul])
    (fun A => by
      change scalar0M E (unit0M E) • A = A
      rw [scalar0M_unit0M, one_smul])

theorem unitEquiv_apply {n : ℕ} (T : TensorRSModel 0 n ℝ E) : unitEquiv E n T = T (unit0M E) :=
  rfl

/-- Reindexing the slots of a form along `a = b` does not change its pointwise norm. -/
theorem covariantTensorInnerPointwise_finCongr (g : SmoothRiemannianMetric I M) (x : M) {a b : ℕ}
    (h : a = b) (A B : ContinuousMultilinearMap ℝ (fun _ : Fin a => E) ℝ) :
    covariantTensorInnerPointwise (I := I) (M := M) b g x
        (A.domDomCongr (finCongr h)) (B.domDomCongr (finCongr h)) =
      covariantTensorInnerPointwise (I := I) (M := M) a g x A B := by
  subst h
  rfl

/-- On `T⁰_n` the pointwise inner product is that of the `n`-forms `unitEquiv`. -/
theorem tensorInnerPointwise_zero_eq (g : SmoothRiemannianMetric I M) (x : M) (n : ℕ)
    (S T : TensorRSModel 0 n ℝ E) :
    tensorInnerPointwise (I := I) (M := M) g 0 n x S T =
      covariantTensorInnerPointwise (I := I) (M := M) n g x (unitEquiv E n S) (unitEquiv E n T) := by
  have key : ∀ U : TensorRSModel 0 n ℝ E,
      lowerAllUpperIndices (I := I) (M := M) g 0 n x U =
        (unitEquiv E n U).domDomCongr (finCongr (Nat.zero_add n).symm) := by
    intro U
    refine ContinuousMultilinearMap.ext fun v => ?_
    rw [lowerAllUpperIndices_apply, separableFormAt_zero, ContinuousMultilinearMap.domDomCongr_apply,
      unitEquiv_apply]
    exact congrArg (U (unit0M E)) (funext fun j => congrArg v (Fin.ext (by simp)))
  rw [tensorInnerPointwise, key, key, covariantTensorInnerPointwise_finCongr]

end Model

/-! ### Lowering and slot permutations in the model -/

section ModelMaps

variable (g : SmoothRiemannianMetric I M)

/-- Lowering all indices, in the model: `T^r_s ≃ T⁰_{r+s}`. -/
def flatModel (r s : ℕ) (x : M) : TensorRSModel r s ℝ E ≃L[ℝ] TensorRSModel 0 (r + s) ℝ E :=
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  (lowerAllUpperIndicesEquiv (I := I) (M := M) g r s x).trans (unitEquiv E (r + s)).symm

theorem unitEquiv_flatModel {r s : ℕ} (x : M) (S : TensorRSModel r s ℝ E) :
    unitEquiv E (r + s) (flatModel g r s x S) = lowerAllUpperIndices (I := I) (M := M) g r s x S := by
  simp [flatModel]

/-- Lowering preserves the pointwise inner product, in the model. -/
theorem tensorInnerPointwise_flatModel {r s : ℕ} (x : M) (S T : TensorRSModel r s ℝ E) :
    tensorInnerPointwise (I := I) (M := M) g 0 (r + s) x (flatModel g r s x S) (flatModel g r s x T) =
      tensorInnerPointwise (I := I) (M := M) g r s x S T := by
  rw [tensorInnerPointwise_zero_eq, unitEquiv_flatModel, unitEquiv_flatModel]
  rfl

variable (E) in
/-- Relabelling the slots of covariant tensors along `e : Fin a ≃ Fin b`, in the models of `T⁰_a`
and `T⁰_b`: `(e·A)(v) = A(v ∘ e)` for the `a`-form `A` (Mathlib's `domDomCongr e`). Since `a = b`,
this is a slot permutation up to reindexing. -/
def permModel {a b : ℕ} (e : Fin a ≃ Fin b) : TensorRSModel 0 a ℝ E ≃L[ℝ] TensorRSModel 0 b ℝ E :=
  (unitEquiv E a).trans
    (((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ e).toContinuousLinearEquiv.trans
      (unitEquiv E b).symm))

theorem unitEquiv_permModel {a b : ℕ} (e : Fin a ≃ Fin b) (S : TensorRSModel 0 a ℝ E) :
    unitEquiv E b (permModel E e S) = (unitEquiv E a S).domDomCongr e := by
  simp [permModel]
  rfl

/-- Slot relabellings preserve the pointwise inner product, in the model. -/
theorem tensorInnerPointwise_permModel (x : M) {a b : ℕ} (e : Fin a ≃ Fin b)
    (S T : TensorRSModel 0 a ℝ E) :
    tensorInnerPointwise (I := I) (M := M) g 0 b x (permModel E e S) (permModel E e T) =
      tensorInnerPointwise (I := I) (M := M) g 0 a x S T := by
  obtain rfl : a = b := by simpa using Fintype.card_congr e
  rw [tensorInnerPointwise_zero_eq, tensorInnerPointwise_zero_eq, unitEquiv_permModel,
    unitEquiv_permModel, tensorInnerPointwise_0s_domDomCongr]

end ModelMaps

/-! ### Lowering and slot permutations on the fibres -/

section Fibres

variable (g : SmoothRiemannianMetric I M)

theorem fiberInner_eq_tensorInnerPointwise {r s : ℕ} (x : M) (v w : TensorRSSpace r s I x) :
    fiberInner g r s x v w =
      tensorInnerPointwise (I := I) (M := M) g r s x (TensorRSSpace.toModel v)
        (TensorRSSpace.toModel w) :=
  Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_apply (I := I) (M := M) g r s x v w

variable (I) in
/-- Transport a model equivalence to the fibres over `x`. -/
def fibreCongr {r s r' s' : ℕ} (x : M) (e : TensorRSModel r s ℝ E ≃L[ℝ] TensorRSModel r' s' ℝ E) :
    TensorRSSpace r s I x ≃L[ℝ] TensorRSSpace r' s' I x :=
  (tensorRSSpaceContinuousLinearEquiv (I := I) r s x).trans
    (e.trans (tensorRSSpaceContinuousLinearEquiv (I := I) r' s' x).symm)

theorem toModel_fibreCongr {r s r' s' : ℕ} {x : M}
    (e : TensorRSModel r s ℝ E ≃L[ℝ] TensorRSModel r' s' ℝ E) (v : TensorRSSpace r s I x) :
    TensorRSSpace.toModel (fibreCongr I x e v) = e (TensorRSSpace.toModel v) := by
  simp [fibreCongr, TensorRSSpace.toModel]

/-- **Lowering all indices** at `x`: the linear isometry `♭ : T^r_s|_x ≃ T⁰_{r+s}|_x`,
`(♭T)(v₁, …, v_{r+s}) = T(v₁♭ ⊗ ⋯ ⊗ v_r♭)(v_{r+1}, …, v_{r+s})`. -/
def flat (r s : ℕ) (x : M) : TensorRSSpace r s I x ≃L[ℝ] TensorRSSpace 0 (r + s) I x :=
  fibreCongr I x (flatModel g r s x)

theorem toModel_flat {r s : ℕ} {x : M} (v : TensorRSSpace r s I x) :
    TensorRSSpace.toModel (flat g r s x v) = flatModel g r s x (TensorRSSpace.toModel v) :=
  toModel_fibreCongr _ v

/-- `♭` is an isometry. -/
theorem fiberInner_flat {r s : ℕ} (x : M) (v w : TensorRSSpace r s I x) :
    fiberInner g 0 (r + s) x (flat g r s x v) (flat g r s x w) = fiberInner g r s x v w := by
  rw [fiberInner_eq_tensorInnerPointwise, fiberInner_eq_tensorInnerPointwise, toModel_flat,
    toModel_flat, tensorInnerPointwise_flatModel]

variable (I) in
/-- The **slot relabelling** `T⁰_a|_x ≃ T⁰_b|_x` along `e : Fin a ≃ Fin b`, `(e·A)(v) = A(v ∘ e)`.
For `a = b` this is a slot permutation. -/
def slotPerm {a b : ℕ} (e : Fin a ≃ Fin b) (x : M) :
    TensorRSSpace 0 a I x ≃L[ℝ] TensorRSSpace 0 b I x :=
  fibreCongr I x (permModel E e)

theorem toModel_slotPerm {a b : ℕ} (e : Fin a ≃ Fin b) {x : M} (v : TensorRSSpace 0 a I x) :
    TensorRSSpace.toModel (slotPerm I e x v) = permModel E e (TensorRSSpace.toModel v) :=
  toModel_fibreCongr _ v

/-- Slot relabellings are isometries. -/
theorem fiberInner_slotPerm {a b : ℕ} (e : Fin a ≃ Fin b) (x : M) (v w : TensorRSSpace 0 a I x) :
    fiberInner g 0 b x (slotPerm I e x v) (slotPerm I e x w) = fiberInner g 0 a x v w := by
  rw [fiberInner_eq_tensorInnerPointwise, fiberInner_eq_tensorInnerPointwise, toModel_slotPerm,
    toModel_slotPerm, tensorInnerPointwise_permModel]

end Fibres

end ShortTime
