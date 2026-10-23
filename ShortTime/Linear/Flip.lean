import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Metric.CometricDoubleTrace
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Calculus.TensorRS
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Field

/-!
# Moving a slot of a coefficient from the input to the output

Let `A` be an operator field `T⁰_{m+1} → T⁰_n` (a smooth section of `Hom(T⁰_{m+1}M, T⁰_nM)`). Its
*flip* is the operator field `Ǎ : T⁰_m → T⁰_{n+1}` given by

  `Ǎ(W)(v, …) = A(v♭ ⊗ W)(…)`,

where `v♭ = g(v, ·)`. It is what one integration by parts does to the principal coefficient:

* `tr₁₂ ∘ slotExtend Ǎ = A` (`trace_slotExtend_flip`), hence `A(∇W) = div(Ǎ W) - (tr ∇Ǎ) W`;
* for `p = 1` the Legendre form of `A` is `⟨ξ, Ǎ ξ⟩`.

The construction only uses the metric and the curry isomorphism `T⁰_{m+1} ≅ Hom(TM, T⁰_m)` (the
first slot is the one that gets curried, matching the convention that `∇` adds the first slot).
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Geometry.Connection.Realization
open scoped Manifold ContDiff BigOperators

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

variable (g : SmoothRiemannianMetric I M)

/-! ### Pointwise construction -/

/-- `v♭ ⊗ W ∈ T⁰_{m+1}`: prepend the covector `g(v, ·)` to `W ∈ T⁰_m`. -/
def flatPrepend (m : ℕ) (x : M) (v : TangentSpace I x) (W : Tensor0SSpace m I x) :
    Tensor0SSpace (m + 1) I x :=
  (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) m x).symm ((g.inner x v).smulRight W)

theorem tensor0SCurry_flatPrepend (m : ℕ) (x : M) (v : TangentSpace I x)
    (W : Tensor0SSpace m I x) :
    tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) m x (flatPrepend g m x v W) =
      (g.inner x v).smulRight W := by
  rw [flatPrepend, ContinuousLinearEquiv.apply_symm_apply]

theorem flatPrepend_add_left (m : ℕ) (x : M) (v₁ v₂ : TangentSpace I x)
    (W : Tensor0SSpace m I x) :
    flatPrepend g m x (v₁ + v₂) W = flatPrepend g m x v₁ W + flatPrepend g m x v₂ W := by
  apply (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) m x).injective
  rw [map_add, tensor0SCurry_flatPrepend, tensor0SCurry_flatPrepend, tensor0SCurry_flatPrepend]
  ext w
  simp [add_smul]

theorem flatPrepend_smul_left (m : ℕ) (x : M) (c : ℝ) (v : TangentSpace I x)
    (W : Tensor0SSpace m I x) :
    flatPrepend g m x (c • v) W = c • flatPrepend g m x v W := by
  apply (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) m x).injective
  rw [map_smul, tensor0SCurry_flatPrepend, tensor0SCurry_flatPrepend]
  ext w
  simp [smul_smul]

theorem flatPrepend_add_right (m : ℕ) (x : M) (v : TangentSpace I x)
    (W₁ W₂ : Tensor0SSpace m I x) :
    flatPrepend g m x v (W₁ + W₂) = flatPrepend g m x v W₁ + flatPrepend g m x v W₂ := by
  apply (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) m x).injective
  rw [map_add, tensor0SCurry_flatPrepend, tensor0SCurry_flatPrepend, tensor0SCurry_flatPrepend]
  ext w
  simp [smul_add]

theorem flatPrepend_smul_right (m : ℕ) (x : M) (c : ℝ) (v : TangentSpace I x)
    (W : Tensor0SSpace m I x) :
    flatPrepend g m x v (c • W) = c • flatPrepend g m x v W := by
  apply (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) m x).injective
  rw [map_smul, tensor0SCurry_flatPrepend, tensor0SCurry_flatPrepend]
  ext w
  simp [smul_comm c]

/-- For fixed `W`, the map `v ↦ A(v♭ ⊗ W)`. -/
def flipCurried (m n : ℕ) (x : M) (A : Tensor0SSpace (m + 1) I x →L[ℝ] Tensor0SSpace n I x)
    (W : Tensor0SSpace m I x) : TangentSpace I x →L[ℝ] Tensor0SSpace n I x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => A (flatPrepend g m x v W)
      map_add' := fun v₁ v₂ => by rw [flatPrepend_add_left, map_add]
      map_smul' := fun c v => by rw [flatPrepend_smul_left, map_smul]; rfl }

theorem flipCurried_apply (m n : ℕ) (x : M)
    (A : Tensor0SSpace (m + 1) I x →L[ℝ] Tensor0SSpace n I x) (W : Tensor0SSpace m I x)
    (v : TangentSpace I x) :
    flipCurried g m n x A W v = A (flatPrepend g m x v W) := rfl

/-- The flip `Ǎ : T⁰_m → T⁰_{n+1}`, `Ǎ(W)(v, …) = A(v♭ ⊗ W)(…)`, of `A : T⁰_{m+1} → T⁰_n`. -/
def flipFib (m n : ℕ) (x : M) (A : Tensor0SSpace (m + 1) I x →L[ℝ] Tensor0SSpace n I x) :
    Tensor0SSpace m I x →L[ℝ] Tensor0SSpace (n + 1) I x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun W => (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) n x).symm
        (flipCurried g m n x A W)
      map_add' := fun W₁ W₂ => by
        rw [← map_add]
        congr 1
        ext v
        simp only [flipCurried_apply, flatPrepend_add_right, map_add,
          FunLike.coe_add, Pi.add_apply]
      map_smul' := fun c W => by
        rw [RingHom.id_apply, ← map_smul]
        congr 1
        ext v
        simp only [flipCurried_apply, flatPrepend_smul_right, map_smul,
          FunLike.coe_smul, Pi.smul_apply] }

theorem tensor0SCurry_flipFib (m n : ℕ) (x : M)
    (A : Tensor0SSpace (m + 1) I x →L[ℝ] Tensor0SSpace n I x) (W : Tensor0SSpace m I x) :
    tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) n x (flipFib g m n x A W) =
      flipCurried g m n x A W := by
  change tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) n x
      ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) n x).symm (flipCurried g m n x A W)) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]

theorem flipFib_toModel_cons (m n : ℕ) (x : M)
    (A : Tensor0SSpace (m + 1) I x →L[ℝ] Tensor0SSpace n I x) (W : Tensor0SSpace m I x)
    (v : E) (vs : Fin n → E) :
    Tensor0SSpace.toModel (flipFib g m n x A W) (Fin.cons v vs) =
      Tensor0SSpace.toModel
        (A (flatPrepend g m x ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v) W)) vs := by
  rw [← TensorMultilinear.tensor0S_curry_toModel_apply (I := I) (M := M) (flipFib g m n x A W) v vs,
    tensor0SCurry_flipFib]
  rfl

/-! ### The trace of the flip -/

/-- Resolution of a vector in the model basis `bₖ` and the dual vectors `g♯(bᵏ)`:
`∑ₖ g(bₖ, w) g♯(bᵏ) = w`. -/
theorem sum_inner_basis_smul_cometric (x : M) (w : TangentSpace I x) :
    ∑ k : Fin (Module.finrank ℝ E),
        g.inner x ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm ((Module.finBasis ℝ E) k)) w •
          (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (cometricLmodel (I := I) g x
            (modelCovectorOfCLM (𝕜 := ℝ) (E := E) ((Module.finBasis ℝ E).cDualBasis k))) = w := by
  set b := Module.finBasis ℝ E
  set S : TangentSpace I x := ∑ k : Fin (Module.finrank ℝ E),
    g.inner x ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (b k)) w • (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (cometricLmodel (I := I) g x
      (modelCovectorOfCLM (𝕜 := ℝ) (E := E) (b.cDualBasis k)))
  have key : ∀ u : TangentSpace I x, g.inner x S u = g.inner x w u := by
    intro u
    have hL : ∀ k, g.inner x ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (cometricLmodel (I := I) g x
        (modelCovectorOfCLM (𝕜 := ℝ) (E := E) (b.cDualBasis k)))) u =
          b.repr (tangentSpaceModelContinuousLinearEquiv (I := I) x u) k := by
      intro k
      rw [tangentSpaceModelContinuousLinearEquiv_symm_apply, cometricLmodel_covectorOfCLM_inner]
      simp [b, Module.Basis.cDualBasis]
    simp only [S, map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
      Pi.smul_apply, smul_eq_mul, hL]
    have hu : u = ∑ k : Fin (Module.finrank ℝ E),
        b.repr (tangentSpaceModelContinuousLinearEquiv (I := I) x u) k • (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (b k) := by
      conv_lhs => rw [← (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm_apply_apply u,
        ← b.sum_repr (tangentSpaceModelContinuousLinearEquiv (I := I) x u)]
      rw [map_sum]
      simp only [map_smul]
    conv_rhs => rw [g.symm, hu]
    simp only [map_sum, map_smul, smul_eq_mul, FunLike.coe_sum, Finset.sum_apply,
      FunLike.coe_smul, Pi.smul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
  by_contra hne
  have hpos := g.pos x (S - w) (sub_ne_zero.mpr hne)
  have h0 : g.inner x (S - w) (S - w) = 0 := by
    rw [show g.inner x (S - w) = g.inner x S - g.inner x w from map_sub _ _ _,
      FunLike.coe_sub, Pi.sub_apply, key, sub_self]
  linarith

/-- `v ↦ ∑ₖ bₖ♭ ⊗ D(g♯bᵏ, …)` is the identity: a tensor is recovered from its first-slot
contractions against the model basis. -/
theorem sum_flatPrepend_curry (m : ℕ) (x : M) (D : Tensor0SSpace (m + 1) I x) :
    ∑ k : Fin (Module.finrank ℝ E),
        flatPrepend g m x ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm ((Module.finBasis ℝ E) k))
          (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) m x D
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (cometricLmodel (I := I) g x
              (modelCovectorOfCLM (𝕜 := ℝ) (E := E) ((Module.finBasis ℝ E).cDualBasis k))))) =
      D := by
  apply (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) m x).injective
  rw [map_sum]
  simp_rw [tensor0SCurry_flatPrepend]
  refine ContinuousLinearMap.ext fun w => ?_
  simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRight_apply]
  conv_rhs => rw [← sum_inner_basis_smul_cometric g x w]
  simp only [map_sum, map_smul]

/-- `tr₁₂ ∘ slotExtend Ǎ = A`: tracing the moved slot against the derivative slot recovers `A`. -/
theorem cometricDoubleTraceFib_comp_slotExtend_flipFib (m n : ℕ) (x : M)
    (A : Tensor0SSpace (m + 1) I x →L[ℝ] Tensor0SSpace n I x) :
    (cometricDoubleTraceFib (I := I) g n x).comp
        (slotExtendPointwise (I := I) (M := M) m (n + 1) x (flipFib g m n x A)) = A := by
  refine ContinuousLinearMap.ext fun D => ?_
  apply Tensor0SSpace.toModel_injective
  beta_reduce
  refine ContinuousMultilinearMap.ext fun mm => ?_
  rw [ContinuousLinearMap.comp_apply, cometricDoubleTraceFib_toModel, modelDoubleTrace_apply]
  simp only [slotExtendFib_apply_eval, flipFib_toModel_cons]
  conv_rhs => rw [← sum_flatPrepend_curry g m x D]
  rw [map_sum, ← Tensor0SSpace.toModelL_apply, map_sum, FunLike.coe_sum, Finset.sum_apply]
  rfl

/-! ### Smoothness -/

section Smooth

variable [CompleteSpace E]

theorem flatPrepend_contMDiff (m : ℕ) (Z : Cₛ^∞⟮I; E, fun x : M => TangentSpace I x⟯)
    (Y : Cₛ^∞⟮I; Tensor0SModel m ℝ E, fun x : M => Tensor0SSpace m I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (m + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel (m + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (m + 1) I z) x (flatPrepend g m x (Z x) (Y x))) := by
  apply contMDiff_uncurriedSection_of_contMDiff_homSection (I := I) (M := M)
    (fun x => (g.inner x (Z x)).smulRight (Y x))
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
    (F₂ := Tensor0SModel m ℝ E) (V₂ := fun x : M => Tensor0SSpace m I x)
    (φ := fun x => (g.inner x (Z x)).smulRight (Y x))
  intro U
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => g.inner x (Z x) (U x)) := fun x =>
    Geometry.Curvature.CovariantDerivative.metric_inner_contMDiffAt g
      (Z.contMDiff x) (U.contMDiff x) le_rfl
  exact hf.smul_section Y.contMDiff

theorem flipFib_contMDiff (m n : ℕ) (Φ : SmoothCcTensor g (m + 1) n) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel m (n + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel m (n + 1) ℝ E)
        (E := fun z : M => TensorRSSpace m (n + 1) I z) x
        (flipFib g m n x
          (show Tensor0SSpace (m + 1) I x →L[ℝ] Tensor0SSpace n I x from Φ.toSection x))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel m ℝ E) (V₁ := fun x : M => Tensor0SSpace m I x)
    (F₂ := Tensor0SModel (n + 1) ℝ E) (V₂ := fun x : M => Tensor0SSpace (n + 1) I x)
    (φ := fun x => flipFib g m n x
      (show Tensor0SSpace (m + 1) I x →L[ℝ] Tensor0SSpace n I x from Φ.toSection x))
  intro Y
  apply contMDiff_uncurriedSection_of_contMDiff_homSection (I := I) (M := M)
    (fun x => flipCurried g m n x
      (show Tensor0SSpace (m + 1) I x →L[ℝ] Tensor0SSpace n I x from Φ.toSection x) (Y x))
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
    (F₂ := Tensor0SModel n ℝ E) (V₂ := fun x : M => Tensor0SSpace n I x)
    (φ := fun x => flipCurried g m n x
      (show Tensor0SSpace (m + 1) I x →L[ℝ] Tensor0SSpace n I x from Φ.toSection x) (Y x))
  intro Z
  have h := ContMDiff.clm_bundle_apply (b := id) Φ.toSection.contMDiff
    (flatPrepend_contMDiff g m Z Y)
  exact h

/-- The flip of an operator field, `Ǎ(W)(v, …) = A(v♭ ⊗ W)(…)`. -/
def flipField (m n : ℕ) (Φ : SmoothCcTensor g (m + 1) n) : SmoothCcTensor g m (n + 1) where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace m (n + 1) I x from flipFib g m n x
          (show Tensor0SSpace (m + 1) I x →L[ℝ] Tensor0SSpace n I x from Φ.toSection x))
      contMDiff_toFun := flipFib_contMDiff g m n Φ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

@[simp] theorem flipField_toSection (m n : ℕ) (Φ : SmoothCcTensor g (m + 1) n) (x : M) :
    (show Tensor0SSpace m I x →L[ℝ] Tensor0SSpace (n + 1) I x from
        (flipField g m n Φ).toSection x) =
      flipFib g m n x (show Tensor0SSpace (m + 1) I x →L[ℝ] Tensor0SSpace n I x from
        Φ.toSection x) := rfl

end Smooth

end ShortTime
