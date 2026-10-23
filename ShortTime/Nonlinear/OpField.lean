import ShortTime.Linear.Operator
import DifferentialGeometry.Tensor.RSTensor.Coordinates.BundleBasis
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.OrthonormalFrame.Tensor02

/-!
# Operator fields from maps between fibres of covariant tensors

An operator field value `Φ : T⁰_a|_x → T⁰_b|_x` acts on the fibres `T⁰_a = Hom(T⁰_0, T⁰_a)` of the
nonlinear setting by `opFieldHom Φ ξ = Φ ∘ ξ`. Conversely every linear map
`P : Hom(T⁰_0, T⁰_a) → Hom(T⁰_0, T⁰_b)` is of this form: `opFieldOf P` sends `Y` to `P(1 ⊗ Y)(1)`,
where `1` is the unit `0`-tensor (`opFieldHom_opFieldOf`).

In the trivializations at `x₀`, the coordinates of `opFieldOf P` are a fixed linear function `Λ` of
the coordinates of `P` (`trivAt_opFieldOf`). This is how the smoothness of an operator field is read
off the smoothness of the corresponding maps between fibres.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Elliptic DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- `Y ↦ 1 ⊗ Y`, from `T⁰_a` to `Hom(T⁰_0, T⁰_a)`. -/
def liftUnit (a : ℕ) (x : M) : Tensor0SSpace a I x →L[ℝ] TensorRSSpace 0 a I x :=
  ContinuousLinearMap.smulRightL ℝ (Tensor0SSpace 0 I x) (Tensor0SSpace a I x)
    (tensor00Scalar (I := I) (M := M) x)

theorem liftUnit_apply {a : ℕ} {x : M} (Y : Tensor0SSpace a I x) (D : Tensor0SSpace 0 I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace a I x from liftUnit a x Y) D =
      tensor00Scalar (I := I) (M := M) x D • Y := rfl

/-- Every `0`-tensor is a multiple of the unit. -/
theorem eq_tensor00Scalar_smul_unit {x : M} (D : Tensor0SSpace 0 I x) :
    D = tensor00Scalar (I := I) (M := M) x D • unitZeroSec (I := I) (M := M) x := by
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext fun v => ?_
  have hv : v = 0 := Subsingleton.elim _ _
  subst hv
  simp only [Tensor0SSpace.toModel_smul, smul_apply, unitZeroSec_apply,
    Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.constOfIsEmpty_apply, smul_eq_mul,
    mul_one]
  rfl

/-- The operator field value with `opFieldHom (opFieldOf P) = P`. -/
def opFieldOf {a b : ℕ} {x : M} (P : TensorRSSpace 0 a I x →L[ℝ] TensorRSSpace 0 b I x) :
    TensorRSSpace a b I x :=
  show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from
    (ContinuousLinearMap.apply ℝ (Tensor0SSpace b I x) (unitZeroSec (I := I) (M := M) x)).comp
      (P.comp (liftUnit a x))

theorem opFieldHom_opFieldOf {a b : ℕ} {x : M}
    (P : TensorRSSpace 0 a I x →L[ℝ] TensorRSSpace 0 b I x) :
    opFieldHom (opFieldOf P) = P := by
  refine ContinuousLinearMap.ext fun ξ => ?_
  -- the lift of a value of `ξ` is a multiple of `ξ`
  have hlift : ∀ D : Tensor0SSpace 0 I x,
      liftUnit a x ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace a I x from ξ) D) =
        tensor00Scalar (I := I) (M := M) x D • ξ := by
    intro D
    refine ContinuousLinearMap.ext fun D' => ?_
    rw [liftUnit_apply]
    change _ = tensor00Scalar (I := I) (M := M) x D •
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace a I x from ξ) D'
    conv_lhs => rw [eq_tensor00Scalar_smul_unit D, map_smul]
    conv_rhs => rw [eq_tensor00Scalar_smul_unit D', map_smul]
    rw [smul_comm]
  change (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from opFieldOf P).comp
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace a I x from ξ) = P ξ
  refine ContinuousLinearMap.ext fun D => ?_
  change (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace b I x from
      P (liftUnit a x ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace a I x from ξ) D)))
      (unitZeroSec (I := I) (M := M) x) = (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace b I x from P ξ) D
  rw [hlift, map_smul]
  conv_rhs => rw [eq_tensor00Scalar_smul_unit D, map_smul]
  rfl

/-! ### Coordinates -/

/-- The scalar of a model `0`-tensor. -/
def scalarM : Tensor0SModel 0 ℝ E →L[ℝ] ℝ :=
  (continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearMap

/-- The unit model `0`-tensor. -/
def unitM : Tensor0SModel 0 ℝ E := ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) 1

/-- The coordinates of a map between fibres `Hom(T⁰_0, T⁰_a) → Hom(T⁰_0, T⁰_b)` at `y`, in the
trivializations at `x₀`. -/
def coordP {a b : ℕ} (x₀ y : M) (P : TensorRSSpace 0 a I y →L[ℝ] TensorRSSpace 0 b I y) :
    TensorRSModel 0 a ℝ E →L[ℝ] TensorRSModel 0 b ℝ E :=
  ((trivAt I M 0 b x₀).continuousLinearMapAt ℝ y).comp (P.comp ((trivAt I M 0 a x₀).symmL ℝ y))

/-- The fixed linear map from coordinates of `P` to coordinates of `opFieldOf P`. -/
def opFieldCoord (a b : ℕ) (Q : TensorRSModel 0 a ℝ E →L[ℝ] TensorRSModel 0 b ℝ E) :
    TensorRSModel a b ℝ E :=
  (ContinuousLinearMap.apply ℝ (Tensor0SModel b ℝ E) (unitM (E := E))).comp
    (Q.comp (ContinuousLinearMap.smulRightL ℝ (Tensor0SModel 0 ℝ E) (Tensor0SModel a ℝ E)
      (scalarM (E := E))))

theorem trivAt_opFieldOf {a b : ℕ} {x₀ y : M}
    (hy : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (P : TensorRSSpace 0 a I y →L[ℝ] TensorRSSpace 0 b I y) :
    (trivAt I M a b x₀ ⟨y, opFieldOf P⟩).2 = opFieldCoord a b (coordP x₀ y P) := by
  let := tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0
  let := tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) a
  have hcl : ∀ {c d : ℕ} (T : TensorRSSpace c d I y),
      (trivAt I M c d x₀).continuousLinearMapAt ℝ y T = (trivAt I M c d x₀ ⟨y, T⟩).2 := by
    intro c d T
    rw [Trivialization.continuousLinearMapAt_apply,
      Trivialization.coe_linearMapAt_of_mem _ (show y ∈ (trivAt I M c d x₀).baseSet from ⟨hy, hy⟩)]
  -- the unit `0`-tensor in coordinates
  have hunit : (trivializationAt (Tensor0SModel 0 ℝ E) (fun x => Tensor0SSpace 0 I x) x₀).symmL ℝ y
      unitM = unitZeroSec (I := I) (M := M) y := by
    have h : (trivializationAt (Tensor0SModel 0 ℝ E) (fun x => Tensor0SSpace 0 I x)
        x₀).continuousLinearMapAt ℝ y (unitZeroSec (I := I) (M := M) y) = unitM := by
      refine ContinuousMultilinearMap.ext fun w => ?_
      rw [Tensor0SSpace.continuousLinearMapAt_apply (𝕜 := ℝ) (I := I) 0 hy]
      simp [unitM]
      rfl
    rw [← h, (trivializationAt (Tensor0SModel 0 ℝ E) (fun x => Tensor0SSpace 0 I x)
      x₀).symmL_continuousLinearMapAt (R := ℝ) hy]
  -- scalars of `0`-tensors in coordinates
  have hscal : ∀ c : Tensor0SModel 0 ℝ E, tensor00Scalar (I := I) (M := M) y
      ((trivializationAt (Tensor0SModel 0 ℝ E) (fun x => Tensor0SSpace 0 I x) x₀).symmL ℝ y c) =
        scalarM c := by
    intro c
    have h := congrArg (fun A : Tensor0SModel 0 ℝ E => A 0)
      ((trivializationAt (Tensor0SModel 0 ℝ E) (fun x => Tensor0SSpace 0 I x)
        x₀).continuousLinearMapAt_symmL (R := ℝ) hy c)
    simp only [Tensor0SSpace.continuousLinearMapAt_apply (𝕜 := ℝ) (I := I) 0 hy] at h
    change (Tensor0SSpace.toModel ((trivializationAt (Tensor0SModel 0 ℝ E)
      (fun x => Tensor0SSpace 0 I x) x₀).symmL ℝ y c)) 0 = c 0
    rw [← h]
    exact (Tensor0SSpace.toModel_apply (𝕜 := ℝ) _ _).trans (congrArg _ (funext fun i => i.elim0))
  -- the lift in coordinates
  have hw : ∀ β : Tensor0SModel a ℝ E, (trivAt I M 0 a x₀).symmL ℝ y
      (ContinuousLinearMap.smulRightL ℝ (Tensor0SModel 0 ℝ E) (Tensor0SModel a ℝ E) scalarM β) =
      liftUnit a y ((trivializationAt (Tensor0SModel a ℝ E) (fun x => Tensor0SSpace a I x)
        x₀).symmL ℝ y β) := by
    intro β
    rw [← (trivAt I M 0 a x₀).symmL_continuousLinearMapAt (R := ℝ)
      (show y ∈ (trivAt I M 0 a x₀).baseSet from ⟨hy, hy⟩) (liftUnit a y _)]
    congr 1
    refine ContinuousLinearMap.ext fun c => ContinuousMultilinearMap.ext fun w => ?_
    rw [hcl, TensorRSSpace.trivializationAt_apply (𝕜 := ℝ) (I := I) 0 a hy, liftUnit_apply, hscal]
    have hβ := congrArg (fun A : Tensor0SModel a ℝ E => A w)
      ((trivializationAt (Tensor0SModel a ℝ E) (fun x => Tensor0SSpace a I x)
        x₀).continuousLinearMapAt_symmL (R := ℝ) hy β)
    simp only [Tensor0SSpace.continuousLinearMapAt_apply (𝕜 := ℝ) (I := I) a hy] at hβ
    have hL : ((ContinuousLinearMap.smulRightL ℝ (Tensor0SModel 0 ℝ E) (Tensor0SModel a ℝ E)
        scalarM β) c) w = scalarM c • β w := rfl
    rw [hL, smul_apply, hβ]
  refine ContinuousLinearMap.ext fun β => ContinuousMultilinearMap.ext fun v => ?_
  rw [TensorRSSpace.trivializationAt_apply (𝕜 := ℝ) (I := I) a b hy]
  simp only [opFieldCoord, coordP, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.apply_apply]
  rw [hcl, TensorRSSpace.trivializationAt_apply (𝕜 := ℝ) (I := I) 0 b hy, hunit, hw]
  rfl

end ShortTime
