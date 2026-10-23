import ShortTime.MM.PairingRel
import ShortTime.MM.PairingAlg

/-!
# The MM pairing in an arbitrary dual basis

`mmPairing_eq_basis`: for any dual families `(b_i)`, `(b'_i)` of `T_xM` and `T*_xM` (`n = dim`), the
frame sum defining `mmPairing` may be computed in `(b, b')` instead of the `g`-orthonormal frame.
This is the metric-free contraction of `E_1 ⊗ ⋯ ⊗ E_p` with the `2p`-tensor, usable in the
trivialisations at `x₀`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Elliptic DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff BigOperators

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- The slots `(ℓ, c)` as the positions `2ℓ + c` of `Fin (2p)`. -/
def slotEquiv (p : ℕ) : MMAlg.Slot p ≃ Fin (2 * p) where
  toFun q := ⟨2 * q.1.val + q.2.val, by have := q.1.isLt; have := q.2.isLt; omega⟩
  invFun m := (⟨m.val / 2, by have := m.isLt; omega⟩, ⟨m.val % 2, by omega⟩)
  left_inv q := by
    obtain ⟨l, c⟩ := q
    have := c.isLt
    ext <;> simp <;> omega
  right_inv m := by
    ext
    simp only
    omega

/-- The scalar value of a `T^0_0`-tensor: its model at the unit section. -/
def lam (x : M) : TensorRSSpace 0 0 I x →ₗ[ℝ] ℝ where
  toFun ξ := Tensor0SSpace.toModel
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 0 I x from ξ) (unitZeroSec (I := I) (M := M) x))
    (fun i => i.elim0)
  map_add' ξ η := by
    simp [Tensor0SSpace.toModel]
  map_smul' c ξ := by
    simp [Tensor0SSpace.toModel]

theorem lam_injective (x : M) : Function.Injective (lam (I := I) x) := by
  intro ξ η h
  apply tensorRS_ext_unit
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext fun vs => ?_
  have hvs : vs = fun i => i.elim0 := funext fun i => i.elim0
  rw [hvs]
  exact h

theorem lam_evalFirst (x : M) (q : ℕ) (v : Fin q → TangentSpace I x)
    (ζ : TensorRSSpace 0 (0 + q) I x) :
    lam x (evalFirst (r := 0) (s := 0) q v ζ) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + q) I x from ζ)
          (unitZeroSec (I := I) (M := M) x))
        (appendIdx (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (v k))
          (fun i => i.elim0)) :=
  evalFirst_toModel x q v ζ _ _

/-- The multilinear form `(w_{(ℓ,c)}) ↦ ζ(w_{(0,0)}, w_{(0,1)}, w_{(1,0)}, …)` of a `2p`-tensor. -/
def phiOf (p : ℕ) (x : M) (ζ : TensorRSSpace 0 (0 + 2 * p) I x) :
    MultilinearMap ℝ (fun _ : MMAlg.Slot p => TangentSpace I x) ℝ :=
  ((Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2 * p) I x from ζ)
        (unitZeroSec (I := I) (M := M) x))).toMultilinearMap.compLinearMap
    (fun _ => (tangentSpaceModelContinuousLinearEquiv (I := I) x).toLinearEquiv.toLinearMap)).domDomCongr
    ((finCongr (Nat.zero_add (2 * p))).trans (slotEquiv p).symm)

theorem lam_evalFirst_phiOf (p : ℕ) (x : M) (v : Fin (2 * p) → TangentSpace I x)
    (ζ : TensorRSSpace 0 (0 + 2 * p) I x) :
    lam x (evalFirst (r := 0) (s := 0) (2 * p) v ζ) = phiOf p x ζ (fun q => v (slotEquiv p q)) := by
  rw [lam_evalFirst]
  simp only [phiOf, MultilinearMap.domDomCongr_apply, MultilinearMap.compLinearMap_apply]
  refine congrArg (fun f => Tensor0SSpace.toModel
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2 * p) I x from ζ)
      (unitZeroSec (I := I) (M := M) x)) f) (funext fun k => ?_)
  have hk := k.isLt
  simp only [appendIdx, dif_pos (show (k : ℕ) < 2 * p by omega), Equiv.trans_apply,
    Equiv.apply_symm_apply, LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv]
  rfl

variable (g : SmoothRiemannianMetric I M)

/-- The MM frame sum in an arbitrary pair of families `(b_i)`, `(b'_i)`. -/
def frameSum (p : ℕ) (x : M)
    (Ef : Fin p → (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (b : Fin (Module.finrank ℝ (TangentSpace I x)) → TangentSpace I x)
    (b' : Fin (Module.finrank ℝ (TangentSpace I x)) → (TangentSpace I x →L[ℝ] ℝ))
    (ζ : TensorRSSpace 0 (0 + 2 * p) I x) : TensorRSSpace 0 0 I x :=
  (-1 : ℝ) ^ (p + 1) • ∑ K : Fin p → Fin (Module.finrank ℝ (TangentSpace I x)),
    ∑ K' : Fin p → Fin (Module.finrank ℝ (TangentSpace I x)),
      (∏ l, Ef l (b' (K l)) (b' (K' l))) •
        evalFirst (r := 0) (s := 0) (2 * p) (interleave (fun i => b (K i)) (fun i => b (K' i))) ζ

theorem mmPairing_apply_eq_frameSum (p : ℕ) (x : M)
    (Ef : Fin p → (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (ζ : TensorRSSpace 0 (0 + 2 * p) I x) :
    mmPairing g p x Ef ζ = frameSum p x Ef (tangentFrame g x) (coframe g x) ζ := by
  simp only [mmPairing, frameSum, smul_apply, sum_apply, evalFirstCLM_apply]

/-- `(K, K') ↦ r` with `r(ℓ,0) = K ℓ`, `r(ℓ,1) = K' ℓ`. -/
def pairsEquiv (p n : ℕ) : ((Fin p → Fin n) × (Fin p → Fin n)) ≃ (MMAlg.Slot p → Fin n) where
  toFun KK q := if q.2 = 0 then KK.1 q.1 else KK.2 q.1
  invFun r := (fun l => r (l, 0), fun l => r (l, 1))
  left_inv KK := by
    ext l <;> simp
  right_inv r := by
    funext ⟨l, c⟩
    fin_cases c <;> simp

theorem lam_frameSum (p : ℕ) (x : M)
    (Ef : Fin p → (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (b : Fin (Module.finrank ℝ (TangentSpace I x)) → TangentSpace I x)
    (b' : Fin (Module.finrank ℝ (TangentSpace I x)) → (TangentSpace I x →L[ℝ] ℝ))
    (ζ : TensorRSSpace 0 (0 + 2 * p) I x) :
    lam x (frameSum p x Ef b b' ζ) =
      (-1 : ℝ) ^ (p + 1) * MMAlg.contr (phiOf p x ζ) Ef b b' := by
  classical
  simp only [frameSum, map_smul, map_sum, smul_eq_mul]
  congr 1
  rw [MMAlg.contr, ← Finset.sum_product']
  refine Fintype.sum_equiv (pairsEquiv p _) _ _ (fun KK => ?_)
  obtain ⟨K, K'⟩ := KK
  rw [lam_evalFirst_phiOf]
  have h1 : (∏ l, Ef l (b' (K l)) (b' (K' l))) =
      ∏ l, Ef l (b' (pairsEquiv p _ (K, K') (l, 0))) (b' (pairsEquiv p _ (K, K') (l, 1))) := by
    simp [pairsEquiv]
  have h2 : (fun q => interleave (fun i => b (K i)) (fun i => b (K' i)) (slotEquiv p q)) =
      fun q => b (pairsEquiv p _ (K, K') q) := by
    funext ⟨l, c⟩
    fin_cases c <;> simp [interleave, slotEquiv, pairsEquiv] <;> (congr 2; ext; simp only; omega)
  rw [h2, h1]

/-- **Basis independence of the MM pairing.** The frame sum defining `mmPairing` (over the
`g`-orthonormal frame) may be computed in any pair of families `(b_i)`, `(b'_i)` with
`b'_i(b_j) = δ_ij`. This is the metric-free contraction of `E_1 ⊗ ⋯ ⊗ E_p` with the `2p`-tensor. -/
theorem mmPairing_eq_basis (p : ℕ) (x : M)
    (Ef : Fin p → (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (b : Fin (Module.finrank ℝ (TangentSpace I x)) → TangentSpace I x)
    (b' : Fin (Module.finrank ℝ (TangentSpace I x)) → (TangentSpace I x →L[ℝ] ℝ))
    (hd : ∀ i j, b' i (b j) = if i = j then 1 else 0)
    (ζ : TensorRSSpace 0 (0 + 2 * p) I x) :
    mmPairing g p x Ef ζ = frameSum p x Ef b b' ζ := by
  apply lam_injective x
  rw [mmPairing_apply_eq_frameSum, lam_frameSum, lam_frameSum]
  congr 1
  haveI : NeZero (Module.finrank ℝ (TangentSpace I x)) :=
    inferInstanceAs (NeZero (Module.finrank ℝ E))
  let ev : (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
    ContinuousLinearMap.coeLM ℝ
  have hW : ∀ w w' : (TangentSpace I x →L[ℝ] ℝ), (∀ v, ev w v = ev w' v) → w = w' :=
    fun w w' h => ContinuousLinearMap.ext h
  have hb := MMAlg.isDual_of_dual rfl ev hW b b' hd
  have hc := MMAlg.isDual_of_dual rfl ev hW (tangentFrame g x) (coframe g x)
    (fun i j => coframe_apply g x i j)
  exact MMAlg.contr_indep hb hc _ _

end ShortTime
