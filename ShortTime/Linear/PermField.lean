import ShortTime.Linear.NegSobolev
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Calculus.DifferentiatedTower

/-!
# Slot relabellings and Hom-fields as operator fields

* For `e : Fin a ≃ Fin b`, `permField g e : T⁰_a → T⁰_b` is the operator field `D ↦ D(· ∘ e)`
  (Mathlib's `domDomCongr e`). For `a = b` it is a slot permutation; for `e = finCongr h` it
  identifies `T⁰_a` with `T⁰_b` along `h : a = b`. On sections it is the library's
  `domDomCongrSection` (`operatorFieldApply_permField`).
* The library states some identities (e.g. the Ricci identity) with Hom-fields
  `Hom(T⁰_a, T⁰_c)` acting on `T⁰_a = Hom(T⁰_0, T⁰_a)`. `homField g Q` is the same operator as an
  operator field (`operatorFieldApply_homField`).
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.Multilinear
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open scoped Manifold ContDiff

set_option linter.unusedSectionVars false

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

/-! ### Slot relabellings -/

variable (I) in
/-- Fibrewise slot relabelling `T⁰_a|_x → T⁰_b|_x`, `D ↦ D(· ∘ e)`. -/
def permFib {a b : ℕ} (e : Fin a ≃ Fin b) (x : M) :
    Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace a I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D => Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.domDomCongr e (Tensor0SSpace.toModel D))
      map_add' := fun D₁ D₂ => by
        apply Tensor0SSpace.toModel_injective
        simp only [Tensor0SSpace.toModel_add, Tensor0SSpace.toModel_ofModel]
        rfl
      map_smul' := fun c D => by
        apply Tensor0SSpace.toModel_injective
        simp only [Tensor0SSpace.toModel_smul, Tensor0SSpace.toModel_ofModel, RingHom.id_apply]
        rfl }

theorem toModel_permFib {a b : ℕ} (e : Fin a ≃ Fin b) {x : M} (D : Tensor0SSpace a I x) :
    Tensor0SSpace.toModel (permFib I e x D) =
      ContinuousMultilinearMap.domDomCongr e (Tensor0SSpace.toModel D) :=
  Tensor0SSpace.toModel_ofModel _

theorem contMDiff_permFib_apply {a b : ℕ} (e : Fin a ≃ Fin b)
    (Y : Cₛ^∞⟮I; Tensor0SModel a ℝ E, fun x : M => Tensor0SSpace a I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel b ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel b ℝ E) (E := fun z : M => Tensor0SSpace b I z) x
        (permFib I e x (Y x))) := by
  classical
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (permFib I e x (Y x) : Tensor0SSpace b I x))).mpr ?_
  have hS := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
    (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
    (fun x => (Y x : Tensor0SSpace a I x))).mp Y.contMDiff
  intro τ x₀
  refine (hS (τ ∘ e) x₀).congr_of_eventuallyEq ?_
  filter_upwards [Filter.univ_mem] with x _
  rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
  conv_rhs => rw [← Tensor0SSpace.ofModel_toModel (Y x)]
  change (ContinuousMultilinearMap.domDomCongr e (Tensor0SSpace.toModel (Y x))).compContinuousLinearMap
        (fun _ : Fin b =>
          (tangentSpaceModelContinuousLinearEquiv (I := I) x).toContinuousLinearMap.comp
            ((trivializationAt E (TangentSpace I) x₀).symmL ℝ x))
        (fun j => (Module.finBasis ℝ E) (τ j)) =
    (Tensor0SSpace.toModel (Y x)).compContinuousLinearMap
        (fun _ : Fin a =>
          (tangentSpaceModelContinuousLinearEquiv (I := I) x).toContinuousLinearMap.comp
            ((trivializationAt E (TangentSpace I) x₀).symmL ℝ x))
        (fun j => (Module.finBasis ℝ E) ((τ ∘ e) j))
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rfl

/-- The slot relabelling `D ↦ D(· ∘ e)` as an operator field `T⁰_a → T⁰_b`. -/
def permField (g : SmoothRiemannianMetric I M) {a b : ℕ} (e : Fin a ≃ Fin b) :
    SmoothCcTensor g a b where
  toSection :=
    { toFun := fun x => (show TensorRSSpace a b I x from permFib I e x)
      contMDiff_toFun := Geometry.Connection.Realization.contMDiff_clm_section_of_pointwise
        (I := I) (M := M)
        (F₁ := Tensor0SModel a ℝ E) (V₁ := fun x : M => Tensor0SSpace a I x)
        (F₂ := Tensor0SModel b ℝ E) (V₂ := fun x : M => Tensor0SSpace b I x)
        (fun x => permFib I e x) (contMDiff_permFib_apply e) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

variable (g : SmoothRiemannianMetric I M)

theorem unitModel_permField {a b : ℕ} (e : Fin a ≃ Fin b) (X : SmoothCcTensor g 0 a) (x : M) :
    unitModel (I := I) (M := M) g b (operatorFieldApply (I := I) (M := M) g a b (permField g e) X) x =
      ContinuousMultilinearMap.domDomCongr e (unitModel (I := I) (M := M) g a X x) :=
  toModel_permFib e _

/-- On sections, `permField σ` is the library's slot permutation `domDomCongrSection σ`. -/
theorem operatorFieldApply_permField {a : ℕ} (σ : Equiv.Perm (Fin a)) (X : SmoothCcTensor g 0 a) :
    operatorFieldApply (I := I) (M := M) g a a (permField g σ) X = domDomCongrSection (I := I) g σ X :=
  smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => by
    rw [domDomCongrSection_unitModel, unitModel_permField]

/-! ### Hom-fields as operator fields -/

theorem tensor0Iso_unitTensor (x : M) :
    Tensor0SNabla.tensor0Iso I M x (unitTensor (I := I) (M := M) x) = (1 : ℝ) := by
  have h := Tensor0SNabla.scalarFn_unitZero (I := I) (M := M)
  have hx := congrFun h x
  change Tensor0SNabla.tensor0Iso I M x (unitTensor (I := I) (M := M) x) = 1 at hx
  exact hx

theorem eq_tensor0Iso_smul_unitTensor {x : M} (D : Tensor0SSpace 0 I x) :
    D = (Tensor0SNabla.tensor0Iso I M x D) • unitTensor (I := I) (M := M) x := by
  apply (Tensor0SNabla.tensor0Iso I M x).injective
  rw [map_smul, tensor0Iso_unitTensor, smul_eq_mul, mul_one]

/-- Maps out of the line `T⁰_0|_x` are determined by their value at the unit. -/
theorem clm_ext_unitTensor {s : ℕ} {x : M} {φ ψ : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x}
    (h : φ (unitTensor (I := I) (M := M) x) = ψ (unitTensor (I := I) (M := M) x)) : φ = ψ := by
  ext D
  rw [eq_tensor0Iso_smul_unitTensor D, map_smul, map_smul, h]

/-- The identification `T⁰_a|_x ≅ Hom(T⁰_0, T⁰_a)|_x`, `D ↦ (λ ↦ λ D)`. -/
def liftFib {a : ℕ} (x : M) :
    Tensor0SSpace a I x →L[ℝ] (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace a I x) :=
  ContinuousLinearMap.smulRightL ℝ (Tensor0SSpace 0 I x) (Tensor0SSpace a I x)
    (Tensor0SNabla.tensor0Iso I M x).toContinuousLinearMap

theorem liftFib_apply_unit {a : ℕ} {x : M} (w : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace a I x) :
    liftFib x (w (unitTensor (I := I) (M := M) x)) = w := by
  refine clm_ext_unitTensor ?_
  change (Tensor0SNabla.tensor0Iso I M x (unitTensor (I := I) (M := M) x)) •
    w (unitTensor (I := I) (M := M) x) = w (unitTensor (I := I) (M := M) x)
  rw [tensor0Iso_unitTensor, one_smul]

/-- A smooth section of `T⁰_s`, as a field `SmoothCcTensor g 0 s`. -/
def ccOfSection {s : ℕ} (Y : Cₛ^∞⟮I; Tensor0SModel s ℝ E, (fun x : M => Tensor0SSpace s I x)⟯) :
    SmoothCcTensor g 0 s where
  toSection := MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
    (E := (TangentSpace I : M → Type _)) ∞ Y
  hasCompactSupport := HasCompactSupport.of_compactSpace _

theorem ccOfSection_apply_unitTensor {s : ℕ}
    (Y : Cₛ^∞⟮I; Tensor0SModel s ℝ E, (fun x : M => Tensor0SSpace s I x)⟯) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from (ccOfSection g Y).toSection x)
      (unitTensor (I := I) (M := M) x) = Y x := by
  have h := congrArg (fun Z => Z x)
    (MixedSection.toMultilinearSection_fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ Y)
  with_unfolding_all exact h

theorem ccOfSection_toSection {s : ℕ}
    (Y : Cₛ^∞⟮I; Tensor0SModel s ℝ E, (fun x : M => Tensor0SSpace s I x)⟯) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from (ccOfSection g Y).toSection x) =
      liftFib x (Y x) := by
  rw [← ccOfSection_apply_unitTensor g Y x, liftFib_apply_unit]

/-- Fibre value of a Hom-field `Q : Hom(T⁰_a, T⁰_c)` as an operator `T⁰_a|_x → T⁰_c|_x`. -/
def homFib {a c : ℕ} (Q : Geometry.Connection.HomTensorRSField (E := E) (M := M) 0 a c I)
    (x : M) : Tensor0SSpace a I x →L[ℝ] Tensor0SSpace c I x :=
  (ContinuousLinearMap.apply ℝ (Tensor0SSpace c I x) (unitTensor (I := I) (M := M) x)).comp
    ((show (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace a I x) →L[ℝ]
        (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace c I x) from Q x).comp (liftFib x))

theorem homFib_apply {a c : ℕ}
    (Q : Geometry.Connection.HomTensorRSField (E := E) (M := M) 0 a c I) {x : M}
    (D : Tensor0SSpace a I x) :
    homFib Q x D = (show TensorRSSpace 0 a I x →L[ℝ] TensorRSSpace 0 c I x from Q x)
      (liftFib x D) (unitTensor (I := I) (M := M) x) := rfl

theorem homFib_apply_section {a c : ℕ}
    (Q : Geometry.Connection.HomTensorRSField (E := E) (M := M) 0 a c I)
    (Y : Cₛ^∞⟮I; Tensor0SModel a ℝ E, (fun x : M => Tensor0SSpace a I x)⟯) (x : M) :
    homFib Q x (Y x) = Geometry.Connection.unitEvalSection (I := I) (M := M) g c
      (Geometry.Connection.homTensorRSFieldApply (I := I) (M := M) g 0 a c Q (ccOfSection g Y))
        x := by
  change (show TensorRSSpace 0 a I x →L[ℝ] TensorRSSpace 0 c I x from Q x) (liftFib x (Y x))
      (unitTensor (I := I) (M := M) x) = _
  rw [← ccOfSection_toSection g Y x]
  rfl

include g in
theorem contMDiff_homFib_apply {a c : ℕ}
    (Q : Geometry.Connection.HomTensorRSField (E := E) (M := M) 0 a c I)
    (Y : Cₛ^∞⟮I; Tensor0SModel a ℝ E, (fun x : M => Tensor0SSpace a I x)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel c ℝ E) (E := fun z : M => Tensor0SSpace c I z) x
        (homFib Q x (Y x))) := by
  simp_rw [homFib_apply_section g Q Y]
  exact Geometry.Connection.contMDiff_unitEvalSection (I := I) (M := M) g c
    (Geometry.Connection.homTensorRSFieldApply (I := I) (M := M) g 0 a c Q (ccOfSection g Y))

/-- A Hom-field `Hom(T⁰_a, T⁰_c)` as an operator field. -/
def homField {a c : ℕ} (Q : Geometry.Connection.HomTensorRSField (E := E) (M := M) 0 a c I) :
    SmoothCcTensor g a c where
  toSection :=
    { toFun := fun x => (show TensorRSSpace a c I x from homFib Q x)
      contMDiff_toFun := Geometry.Connection.Realization.contMDiff_clm_section_of_pointwise
        (I := I) (M := M)
        (F₁ := Tensor0SModel a ℝ E) (V₁ := fun x : M => Tensor0SSpace a I x)
        (F₂ := Tensor0SModel c ℝ E) (V₂ := fun x : M => Tensor0SSpace c I x)
        (fun x => homFib Q x) (contMDiff_homFib_apply g Q) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

/-- On sections, `homField g Q` acts as the Hom-field `Q`. -/
theorem operatorFieldApply_homField {a c : ℕ}
    (Q : Geometry.Connection.HomTensorRSField (E := E) (M := M) 0 a c I)
    (W : SmoothCcTensor g 0 a) :
    operatorFieldApply (I := I) (M := M) g a c (homField g Q) W =
      Geometry.Connection.homTensorRSFieldApply (I := I) (M := M) g 0 a c Q W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  refine clm_ext_unitTensor ?_
  rw [operatorFieldApplication_toSection, ContinuousLinearMap.comp_apply]
  change homFib Q x _ = _
  rw [homFib_apply, liftFib_apply_unit]
  rfl

end ShortTime
