import ShortTime.Linear.Uniqueness
import ShortTime.Sanity.LegendreTrace
import ShortTime.Setting.LegendreBasic

/-!
# The Legendre condition for second-order operators, in flip form

For `p = 1` the Legendre form of the principal coefficient `A` is `⟨ξ, Ǎ ξ⟩`, where `Ǎ` is the flip
(`legendreForm_one_eq`). Hence a parabolic second-order operator in the sense of the paper
(`LinearOp.IsParabolic`) has a flip-coercive principal part (`LinearOp.FlipCoercive`), which is the
form used in Gårding's inequality.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open scoped Manifold ContDiff BigOperators

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

variable (g : SmoothRiemannianMetric I M)

theorem fiberInner_add_left {r s : ℕ} (x : M) (v v' w : TensorRSSpace r s I x) :
    fiberInner g r s x (v + v') w = fiberInner g r s x v w + fiberInner g r s x v' w := by
  simp only [fiberInner, map_add, FunLike.coe_add, Pi.add_apply]

theorem fiberInner_symm {r s : ℕ} (x : M) (v w : TensorRSSpace r s I x) :
    fiberInner g r s x v w = fiberInner g r s x w v :=
  (Tensor.TensorRSRiemannianBundle.tensorRSRiemannianMetric (I := I) (M := M) g r s).symm x v w

/-- Polarized form of `fiberInner_self_eq_sum_evalSlot`: the inner product on `T⁰_{s+1}` is the sum
over an orthonormal frame of the inner products of first-slot evaluations. -/
theorem fiberInner_eq_sum_evalSlot (s : ℕ) (x : M) (ξ η : TensorRSSpace 0 (s + 1) I x) :
    fiberInner g 0 (s + 1) x ξ η =
      ∑ a : Fin (Module.finrank ℝ (TangentSpace I x)),
        fiberInner g 0 s x (evalSlot 0 s x (tangentFrame g x a) ξ)
          (evalSlot 0 s x (tangentFrame g x a) η) := by
  have h := fiberInner_self_eq_sum_evalSlot g s x (ξ + η)
  have hξ := fiberInner_self_eq_sum_evalSlot g s x ξ
  have hη := fiberInner_self_eq_sum_evalSlot g s x η
  simp only [map_add, fiberInner_add_left, fiberInner_add_right, Finset.sum_add_distrib] at h
  rw [fiberInner_symm g x η ξ] at h
  simp only [fiberInner_symm g x (evalSlot 0 s x _ η) (evalSlot 0 s x _ ξ)] at h
  linarith

variable [CompleteSpace E]

/-- `v♭ ⊗ ξ`, formed in the nonlinear setting's fibres, is `flatPrepend` applied to the value. -/
theorem prependCovectors_one_apply {t : ℕ} (x : M) (v : TangentSpace I x)
    (ξ : TensorRSSpace 0 t I x) (D : Tensor0SSpace 0 I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 1) I x from
        prependCovectors 1 (fun _ => g.inner x v) ξ) D =
      flatPrepend g t x v ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from ξ) D) := by
  apply (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) t x).injective
  rw [tensor0SCurry_flatPrepend]
  refine ContinuousLinearMap.ext fun w => ?_
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext fun vs => ?_
  rw [TensorMultilinear.tensor0S_curry_toModel_apply_tangent]
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 1) I x from
        covGradBundleEquiv (I := I) (M := M) 0 t x ((g.inner x v).smulRight ξ)) D) _ = _
  rw [covGradBundleEquiv_apply_toModel]
  simp [ContinuousLinearMap.smulRight_apply]
  left
  congr 1

/-- Evaluating the first slot of a `T⁰_{t+1}`-valued fibre element, value by value. -/
theorem evalSlot_apply {t : ℕ} (x : M) (v : TangentSpace I x) (T : TensorRSSpace 0 (t + 1) I x)
    (D : Tensor0SSpace 0 I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from evalSlot 0 t x v T) D =
      tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) t x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (t + 1) I x from T) D) v := by
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext fun vs => ?_
  rw [TensorMultilinear.tensor0S_curry_toModel_apply_tangent]
  rfl

theorem evalSlot_opFieldHom_flipFib (s : ℕ) (x : M)
    (A : Tensor0SSpace (s + 1 + 1) I x →L[ℝ] Tensor0SSpace s I x) (v : TangentSpace I x)
    (ξ : TensorRSSpace 0 (s + 1) I x) :
    evalSlot 0 s x v
        (opFieldHom (show TensorRSSpace (s + 1) (s + 1) I x from flipFib g (s + 1) s x A) ξ) =
      opFieldHom (show TensorRSSpace (s + 1 + 1) s I x from A)
        (prependCovectors 1 (fun _ => g.inner x v) ξ) := by
  refine ContinuousLinearMap.ext fun D => ?_
  rw [evalSlot_apply]
  change tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) s x (flipFib g (s + 1) s x A
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from ξ) D)) v =
    A ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
      prependCovectors 1 (fun _ => g.inner x v) ξ) D)
  rw [tensor0SCurry_flipFib, flipCurried_apply, prependCovectors_one_apply]

/-- **For `p = 1` the Legendre form is `⟨ξ, Ǎ ξ⟩`.** -/
theorem legendreForm_one_eq (s : ℕ) (x : M)
    (A : Tensor0SSpace (s + 1 + 1) I x →L[ℝ] Tensor0SSpace s I x)
    (ξ : TensorRSSpace 0 (s + 1) I x) :
    legendreForm g 0 s 1 x (opFieldHom (show TensorRSSpace (s + 1 + 1) s I x from A)) ξ ξ =
      fiberInner g 0 (s + 1) x ξ
        (opFieldHom (show TensorRSSpace (s + 1) (s + 1) I x from flipFib g (s + 1) s x A) ξ) := by
  classical
  rw [legendreForm_eq, fiberInner_eq_sum_evalSlot]
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) _) _ _ (fun K => ?_)
  have hK : (fun i : Fin 1 => g.inner x (tangentFrame g x (K i))) =
      fun _ => g.inner x (tangentFrame g x (K 0)) := by
    funext i; rw [Subsingleton.elim i 0]
  rw [evalFirst_one, hK, ← evalSlot_opFieldHom_flipFib]
  rfl

namespace LinearOp

variable {g} {s : ℕ} {T : ℝ}

/-- A parabolic second-order operator has a flip-coercive principal part. -/
theorem flipCoercive_of_isParabolic (L : LinearOp g s 1 T) {lam : ℝ} (h : L.IsParabolic lam) :
    L.FlipCoercive lam := by
  refine ⟨h.1, fun t ht x ξ => ?_⟩
  have hL := (h.2 t ht x).2 ξ
  have heq : legendreForm g 0 s 1 x (L.principal t x) ξ ξ =
      fiberInner g 0 (s + 1) x ξ
        (opFieldHom (show TensorRSSpace (s + 1) (s + 1) I x from
          flipFib g (s + 1) s x ((L.coeff 2 t).toSection x)) ξ) :=
    legendreForm_one_eq g s x _ ξ
  rw [heq] at hL
  norm_num at hL
  exact hL

end LinearOp

end ShortTime
