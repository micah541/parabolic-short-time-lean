import ShortTime.Linear.Commute
import ShortTime.Nonlinear.FlatAlgebra

/-!
# The Legendre condition for the differentiated operator (`lem:commute`)

The principal coefficient `P^{(1)} = P_• ∘ γ` of the differentiated operator satisfies the
Legendre condition with the same constant as `P` (`LinearOp.isParabolic_comm`).

Decompose `ξ ∈ T⁰_{(s+1)+p}` along its slot `p`, the slot of the extra factor:
`ξ^{(a)} = ξ(·, e_a, ·)` for an orthonormal frame `e_a` (`evalSlotP`). Then
`|ξ|² = Σ_a |ξ^{(a)}|²` (`fiberInner_eq_sum_evalSlotP`) and
`B_{P^{(1)}}(ξ, ξ) = Σ_a B_P(ξ^{(a)}, ξ^{(a)})` (`legendreForm_comm`).
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open scoped Manifold ContDiff BigOperators

set_option linter.unusedSectionVars false

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

/-! ### Index bookkeeping -/

theorem cycleCast_val {n m q : ℕ} (h : n = m) (hq : q < m) (i : Fin n) :
    (((finCongr h).trans (Fin.cycleRange (⟨q, hq⟩ : Fin m))) i : ℕ) =
      if (i : ℕ) < q then (i : ℕ) + 1 else if (i : ℕ) = q then 0 else (i : ℕ) := by
  subst h
  have : NeZero n := ⟨by omega⟩
  change ((Fin.cycleRange (⟨q, hq⟩ : Fin n)) i : ℕ) = _
  split_ifs with h1 h2
  · exact Fin.coe_cycleRange_of_lt (Fin.lt_def.mpr h1)
  · rw [show i = ⟨q, hq⟩ from Fin.ext h2, Fin.cycleRange_self, Fin.val_zero]
  · rw [Fin.cycleRange_of_gt (Fin.lt_def.mpr (by simp only; omega))]

theorem cons_of_val_zero {n : ℕ} (V : E) (f : Fin n → E) {k : Fin (n + 1)} (hk : (k : ℕ) = 0) :
    (Fin.cons V f : Fin (n + 1) → E) k = V := by
  rw [show k = 0 from Fin.ext hk, Fin.cons_zero]

theorem cons_of_val_succ {n : ℕ} (V : E) (f : Fin n → E) {k : Fin (n + 1)} {j : ℕ} (hj : j < n)
    (hk : (k : ℕ) = j + 1) : (Fin.cons V f : Fin (n + 1) → E) k = f ⟨j, hj⟩ := by
  rw [show k = Fin.succ ⟨j, hj⟩ from Fin.ext hk, Fin.cons_succ]

/-- Moving slot `p` of `T⁰_{(s+1)+p}` to the front. -/
def slotPEquiv (s p : ℕ) : Fin (s + 1 + p) ≃ Fin (s + p + 1) :=
  (finCongr (by omega)).trans (Fin.cycleRange (⟨p, by omega⟩ : Fin (s + p + 1)))

theorem slotPEquiv_val (s p : ℕ) (i : Fin (s + 1 + p)) :
    (slotPEquiv s p i : ℕ) = if (i : ℕ) < p then (i : ℕ) + 1 else if (i : ℕ) = p then 0 else (i : ℕ) :=
  cycleCast_val _ _ i

theorem gammaEquiv_val (s p : ℕ) (i : Fin (s + 1 + 2 * p)) :
    (gammaEquiv s p i : ℕ) =
      if (i : ℕ) < 2 * p then (i : ℕ) + 1 else if (i : ℕ) = 2 * p then 0 else (i : ℕ) :=
  cycleCast_val _ _ i

/-! ### Evaluating slot `p` -/

/-- `ξ ↦ ξ(·, v, ·)`: evaluate slot `p` of `ξ ∈ T⁰_{(s+1)+p}` on `v`. -/
def evalSlotP (s p : ℕ) (x : M) (v : TangentSpace I x) :
    TensorRSSpace 0 (s + 1 + p) I x →L[ℝ] TensorRSSpace 0 (s + p) I x :=
  (evalSlot 0 (s + p) x v).comp (slotPerm I (slotPEquiv s p) x).toContinuousLinearMap

theorem toModel_evalSlot {t : ℕ} {x : M} (v : TangentSpace I x) (T : TensorRSSpace 0 (t + 1) I x)
    (β : Tensor0SModel 0 ℝ E) (w : Fin t → E) :
    TensorRSSpace.toModel (evalSlot 0 t x v T) β w =
      TensorRSSpace.toModel T β (Fin.cons (toE v) w) :=
  toModel_covGradBundleEquiv_symm T v β w

theorem toModel_evalSlotP {s p : ℕ} {x : M} (v : TangentSpace I x)
    (ξ : TensorRSSpace 0 (s + 1 + p) I x) (β : Tensor0SModel 0 ℝ E) (w : Fin (s + p) → E) :
    TensorRSSpace.toModel (evalSlotP s p x v ξ) β w =
      scalar0M E β * TensorRSSpace.toModel ξ (unit0M E)
        (fun i => (Fin.cons (toE v) w : Fin (s + p + 1) → E) (slotPEquiv s p i)) := by
  rw [evalSlotP, ContinuousLinearMap.comp_apply, toModel_evalSlot]
  exact toModel_slotPerm_apply _ _ β _

variable (g : SmoothRiemannianMetric I M)

/-- `|ξ|² = Σ_a |ξ(·, e_a, ·)|²`, polarized. -/
theorem fiberInner_eq_sum_evalSlotP (s p : ℕ) (x : M) (ξ η : TensorRSSpace 0 (s + 1 + p) I x) :
    fiberInner g 0 (s + 1 + p) x ξ η =
      ∑ a : Fin (Module.finrank ℝ (TangentSpace I x)),
        fiberInner g 0 (s + p) x (evalSlotP s p x (tangentFrame g x a) ξ)
          (evalSlotP s p x (tangentFrame g x a) η) := by
  rw [← fiberInner_slotPerm g (slotPEquiv s p) x ξ η, fiberInner_eq_sum_evalSlot]
  rfl

/-- Evaluating the first `p` slots commutes with evaluating slot `p`. -/
theorem evalSlot_evalFirst {s p : ℕ} {x : M} (v : TangentSpace I x) (w : Fin p → TangentSpace I x)
    (ξ : TensorRSSpace 0 (s + 1 + p) I x) :
    evalSlot 0 s x v (evalFirst p w ξ) = evalFirst p w (evalSlotP s p x v ξ) := by
  refine rsToModel_injective (ContinuousLinearMap.ext fun β =>
    ContinuousMultilinearMap.ext fun u => ?_)
  rw [toModel_evalSlot, toModel_evalFirst, toModel_evalFirst, toModel_evalSlotP,
    modelRS0_apply_eq, smul_apply, smul_eq_mul]
  congr 2
  funext i
  have hv := slotPEquiv_val s p i
  rw [appendFirst_apply]
  by_cases h1 : (i : ℕ) < p
  · rw [if_pos h1] at hv
    rw [dif_pos h1, cons_of_val_succ _ _ (by omega) hv, appendFirst_apply, dif_pos h1]
  · rw [dif_neg h1]
    by_cases h2 : (i : ℕ) = p
    · rw [if_neg h1, if_pos h2] at hv
      rw [cons_of_val_zero _ _ hv, cons_of_val_zero _ _ (by simp only; omega)]
    · rw [if_neg h1, if_neg h2] at hv
      rw [cons_of_val_succ _ _ (by omega) (by simp only; omega : (⟨(i : ℕ) - p, _⟩ : Fin (s + 1)).val = (i - p - 1) + 1),
        cons_of_val_succ _ _ (by omega) (by omega : ((slotPEquiv s p) i : ℕ) = (i - 1) + 1),
        appendFirst_apply, dif_neg (by simp only; omega)]
      exact congrArg _ (Fin.ext (by simp only; omega))

theorem toModel_opFieldHom {a b : ℕ} {x : M} (Φ : TensorRSSpace a b I x)
    (ξ : TensorRSSpace 0 a I x) (β : Tensor0SModel 0 ℝ E) :
    TensorRSSpace.toModel (opFieldHom Φ ξ) β =
      Tensor0SSpace.toModel ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from Φ)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace a I x from ξ) (Tensor0SSpace.ofModel β))) :=
  rfl

theorem toModel_tensorRS_apply {a : ℕ} {x : M} (ξ : TensorRSSpace 0 a I x)
    (β : Tensor0SModel 0 ℝ E) :
    TensorRSSpace.toModel ξ β =
      Tensor0SSpace.toModel ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace a I x from ξ)
        (Tensor0SSpace.ofModel β)) :=
  rfl

namespace LinearOp

variable {g} {s p : ℕ} {T : ℝ}

/-- **The principal symbol of `P^{(1)}`**: evaluating the extra slot of `P^{(1)}(θ ⊗ ξ)` on `v`
gives `P(θ ⊗ ξ(·, v, ·))`. -/
theorem evalSlot_principal_comm (L : LinearOp g s p T) (L' : LinearOp g (s + 1) p T)
    (hL' : ∀ t, L'.coeff (Fin.last (2 * p)) t = L.commTop t) (t : ℝ) {x : M}
    (v : TangentSpace I x) (θ : Fin p → (TangentSpace I x →L[ℝ] ℝ))
    (ξ : TensorRSSpace 0 (s + 1 + p) I x) :
    evalSlot 0 s x v (L'.principal t x (prependCovectors p θ ξ)) =
      L.principal t x (prependCovectors p θ (evalSlotP s p x v ξ)) := by
  refine rsToModel_injective (ContinuousLinearMap.ext fun β =>
    ContinuousMultilinearMap.ext fun u => ?_)
  rw [toModel_evalSlot]
  simp only [principal, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [toModel_opFieldHom, toModel_opFieldHom]
  rw [show L'.coeff ⟨2 * p, Nat.lt_succ_self _⟩ t = L.commTop t from hL' t, commTop,
    operatorFieldComposition_toSection, ContinuousLinearMap.comp_apply, slotExtend_toSection]
  erw [slotExtendFib_apply_eval]
  show Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 2 * p) I x →L[ℝ] Tensor0SSpace s I x from
        (L.coeff (Fin.last (2 * p)) t).toSection x)
        (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) (s + 2 * p) x
          (permFib I (gammaEquiv s p) x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1 + 2 * p) I x from
              EquationData.castIdx (by omega) x (prependCovectors p θ ξ)) (Tensor0SSpace.ofModel β)))
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (toE v)))) u =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 2 * p) I x →L[ℝ] Tensor0SSpace s I x from
        (L.coeff (Fin.last (2 * p)) t).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2 * p) I x from
          EquationData.castIdx (by omega) x (prependCovectors p θ (evalSlotP s p x v ξ)))
          (Tensor0SSpace.ofModel β))) u
  congr 3
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext fun w => ?_
  beta_reduce
  rw [TensorMultilinear.tensor0S_curry_toModel_apply_tangent, toModel_permFib,
    ContinuousMultilinearMap.domDomCongr_apply, ← toModel_tensorRS_apply, ← toModel_tensorRS_apply,
    toModel_castIdx, toModel_castIdx, toModel_prependCovectors, toModel_prependCovectors,
    toModel_evalSlotP, ContinuousLinearEquiv.apply_symm_apply,
    modelRS0_apply_eq (TensorRSSpace.toModel ξ) β, smul_apply, smul_eq_mul]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    have hv := gammaEquiv_val s p (Fin.cast (show s + 1 + p + p = s + 1 + 2 * p by omega) ⟨i, by omega⟩)
    simp only [Fin.val_cast] at hv
    rw [if_pos (by omega)] at hv
    rw [cons_of_val_succ _ _ (by omega) hv]
    rfl
  · congr 2
    funext j
    have hv := gammaEquiv_val s p
      (Fin.cast (show s + 1 + p + p = s + 1 + 2 * p by omega) ⟨j + p, by omega⟩)
    have hv' := slotPEquiv_val s p j
    simp only [Fin.val_cast] at hv
    by_cases h1 : (j : ℕ) < p
    · rw [if_pos (by omega)] at hv
      rw [if_pos h1] at hv'
      rw [cons_of_val_succ _ _ (by omega) hv, cons_of_val_succ _ _ (by omega) hv']
      exact congrArg w (Fin.ext (by simp only [Fin.val_cast]))
    · by_cases h2 : (j : ℕ) = p
      · rw [if_neg (by omega), if_pos (by omega)] at hv
        rw [if_neg h1, if_pos h2] at hv'
        rw [cons_of_val_zero _ _ hv, cons_of_val_zero _ _ hv']
      · rw [if_neg (by omega), if_neg (by omega)] at hv
        rw [if_neg h1, if_neg h2] at hv'
        have hk : ((gammaEquiv s p) (Fin.cast (show s + 1 + p + p = s + 1 + 2 * p by omega)
            ⟨(j : ℕ) + p, by omega⟩) : ℕ) = (j + p - 1) + 1 := by rw [hv]; omega
        rw [cons_of_val_succ _ _ (by omega) hk,
          cons_of_val_succ _ _ (by omega) (by omega : ((slotPEquiv s p) j : ℕ) = (j - 1) + 1)]
        exact congrArg w (Fin.ext (by simp only [Fin.val_cast]; omega))

/-- **The Legendre form of `P^{(1)}` splits along the extra slot**:
`B_{P^{(1)}}(ξ, ξ) = Σ_a B_P(ξ(·, e_a, ·), ξ(·, e_a, ·))`. -/
theorem legendreForm_comm (L : LinearOp g s p T) (L' : LinearOp g (s + 1) p T)
    (hL' : ∀ t, L'.coeff (Fin.last (2 * p)) t = L.commTop t) (t : ℝ) (x : M)
    (ξ : TensorRSSpace 0 (s + 1 + p) I x) :
    legendreForm g 0 (s + 1) p x (L'.principal t x) ξ ξ =
      ∑ a : Fin (Module.finrank ℝ (TangentSpace I x)),
        legendreForm g 0 s p x (L.principal t x) (evalSlotP s p x (tangentFrame g x a) ξ)
          (evalSlotP s p x (tangentFrame g x a) ξ) := by
  simp only [legendreForm_eq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [fiberInner_eq_sum_evalSlot]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [evalSlot_evalFirst, evalSlot_principal_comm L L' hL']

/-- **`P^{(1)}` satisfies the Legendre condition with the constant of `P`.** -/
theorem legendreAt_comm (L : LinearOp g s p T) (L' : LinearOp g (s + 1) p T)
    (hL' : ∀ t, L'.coeff (Fin.last (2 * p)) t = L.commTop t) {t : ℝ} {x : M} {lam : ℝ}
    (h : LegendreAt g 0 s p x (L.principal t x) lam) :
    LegendreAt g 0 (s + 1) p x (L'.principal t x) lam := by
  refine ⟨h.1, fun ξ => ?_⟩
  rw [legendreForm_comm L L' hL', fiberInner_eq_sum_evalSlotP, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ => h.2 _

/-- The differentiated operator is parabolic with the same constant. -/
theorem isParabolic_comm (L : LinearOp g s p T) (L' : LinearOp g (s + 1) p T)
    (hL' : ∀ t, L'.coeff (Fin.last (2 * p)) t = L.commTop t) {lam : ℝ} (h : L.IsParabolic lam) :
    L'.IsParabolic lam :=
  ⟨h.1, fun t ht x => legendreAt_comm L L' hL' (h.2 t ht x)⟩

end LinearOp

end ShortTime
