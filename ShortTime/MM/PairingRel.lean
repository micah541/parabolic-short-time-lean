import ShortTime.MM.PairingDef

/-!
# The MM pairing versus the split pairing

`mmPairing_eq_productCLM_perm`: for a `2p`-tensor `ζ`,
`mmPairing ζ = productCLM (ζ with slots permuted by mmSlotPerm p)`.
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

/-- `castIdx` in the model: precomposition of the argument vector with `Fin.cast`. -/
theorem mm_toModel_castIdx {a b : ℕ} (h : a = b) (x : M) (ξ : TensorRSSpace 0 a I x)
    (D : Tensor0SSpace 0 I x) (u : Fin b → E) :
    Tensor0SSpace.toModel ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace b I x from
      EquationData.castIdx h x ξ) D) u =
      Tensor0SSpace.toModel ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace a I x from ξ) D)
        (fun k => u (Fin.cast h k)) := by
  subst h
  rfl

/-- Evaluating the first `p` slots, then the next `p`, is evaluating the split vector. -/
theorem evalFirst_split (x : M) (p : ℕ) (w w' : Fin p → TangentSpace I x)
    (ζ : TensorRSSpace 0 (0 + 2 * p) I x) :
    evalFirst (r := 0) (s := 0) p w'
        (evalFirst (r := 0) (s := 0 + p) p w
          (EquationData.castIdx (show 0 + 2 * p = 0 + p + p by omega) x ζ)) =
      evalFirst (r := 0) (s := 0) (2 * p) (splitVec w w') ζ := by
  apply tensorRS_ext_unit
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext fun vs => ?_
  simp only [evalFirst_toModel, mm_toModel_castIdx]
  congr 1
  funext k
  have hk := k.isLt
  simp only [appendIdx, splitVec, Fin.val_cast]
  split_ifs <;> first | rfl | (exfalso; omega)

variable (g : SmoothRiemannianMetric I M)

/-- Evaluating the first `q` slots of a slot-permuted section precomposes the vector with `σ`. -/
theorem evalFirst_domDomCongrSection (q : ℕ) (σ : Equiv.Perm (Fin q))
    (Ψ : SmoothCcTensor g 0 (0 + q)) (x : M) (w : Fin q → TangentSpace I x) :
    evalFirst (r := 0) (s := 0) q w
        ((domDomCongrSection (I := I) g (extPerm 0 q σ) Ψ).toSection x) =
      evalFirst (r := 0) (s := 0) q (w ∘ σ) (Ψ.toSection x) := by
  apply tensorRS_ext_unit
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext fun vs => ?_
  rw [evalFirst_toModel, evalFirst_toModel]
  change unitModel (I := I) (M := M) g (0 + q)
      (domDomCongrSection (I := I) g (extPerm 0 q σ) Ψ) x _ =
    unitModel (I := I) (M := M) g (0 + q) Ψ x _
  rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext k
  by_cases hk : (k : ℕ) < q
  · have h1 := extPerm_apply_lt 0 q σ k hk
    simp only [appendIdx, h1, Function.comp_apply, dif_pos hk,
      dif_pos (show ((σ ⟨k, hk⟩ : Fin q) : ℕ) < q from (σ ⟨k, hk⟩).isLt)]
  · rw [extPerm_apply_ge 0 q _ k (by omega)]
    simp only [appendIdx, dif_neg hk]

/-- **The MM pairing is the split pairing of the slot-permuted tensor** (`rem:rewrite`). -/
theorem mmPairing_eq_productCLM (p : ℕ) (x : M)
    (Ef : Fin p → (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (Ψ : SmoothCcTensor g 0 (0 + 2 * p)) :
    mmPairing g p x Ef (Ψ.toSection x) =
      productCLM g 0 0 p x Ef
        (EquationData.castIdx (show 0 + 2 * p = 0 + p + p by omega) x
          ((domDomCongrSection (I := I) g (extPerm 0 (2 * p) (mmSlotPerm p)) Ψ).toSection x)) := by
  simp only [mmPairing, productCLM, smul_apply, sum_apply,
    ContinuousLinearMap.comp_apply, evalFirstCLM_apply]
  congr 1
  refine Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun K' _ => ?_
  congr 1
  rw [evalFirst_split, evalFirst_domDomCongrSection, splitVec_slotPerm]

/-- **Rewriting the top-order term** (`rem:rewrite`). Along the `N`-jet of a smooth function, the MM
pairing of `∇^{2p}u` equals the split pairing of `∇^{2p}u` plus the split pairing of a smooth jet map
`Qj`, which does not depend on the coefficients `E_ℓ`. -/
theorem mmPairing_eq_productCLM_add (p N : ℕ) (hN : 2 * p - 2 ≤ N) :
    ∃ Qj : ∀ x : M, CovJetFiber I 0 0 N x → TensorRSSpace 0 (0 + 2 * p) I x,
      SmoothJetMap I M 0 N (0 + 2 * p) Qj ∧
      ∀ (u : SmoothCcTensor g 0 0) (x : M)
        (Ef : Fin p → (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] ℝ),
        mmPairing g p x Ef ((iteratedCovGrad g 0 0 (2 * p) u).toSection x) =
          productCLM g 0 0 p x Ef
              (EquationData.castIdx (show 0 + 2 * p = 0 + p + p by omega) x
                ((iteratedCovGrad g 0 0 (2 * p) u).toSection x)) +
            productCLM g 0 0 p x Ef
              (EquationData.castIdx (show 0 + 2 * p = 0 + p + p by omega) x
                (Qj x (covJet g 0 0 N u x))) := by
  obtain ⟨Qj, hQ, e⟩ := exists_ricci_jetMap (g := g) 0 (2 * p) N hN (mmSlotPerm p)
  refine ⟨Qj, hQ, fun u x Ef => ?_⟩
  rw [mmPairing_eq_productCLM, e u x, map_add, map_add]

end ShortTime
