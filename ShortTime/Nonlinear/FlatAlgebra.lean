import ShortTime.Nonlinear.FlatData

/-!
# Lowering, first slots, and prepended covectors

Paper: Lemma `lem:lowering`, the algebra behind the Legendre condition.

Write `Λ_k = σ_k ♭ : T^r_{s+k} → T⁰_{(r+s)+k}` for the `k`-th component of the jet map. The proof
of `lem:lowering` uses two compatibilities:

* evaluating the first `p` slots commutes with lowering: `(Λ_p ξ)(v, ·) = ♭(ξ(v, ·))`
  (`evalFirst_jetFlat`);
* prepending covectors commutes with lowering: `θ ⊗ Λ_p η = Λ_{2p}(θ ⊗ η)`, up to reindexing
  (`castIdx_prepend_jetFlat`).

Both are checked on model coordinates: every map involved has an explicit formula
(`toModel_flat_apply`, `toModel_slotPerm_apply`, `toModel_evalFirst`, `toModel_prependCovectors`,
`toModel_castIdx`), and `jetPerm` moves the `k` derivative slots in front of the `r` lowered ones
(`jetPerm_val_lt`, `jetPerm_val_mid`, `jetPerm_val_ge`).
-/

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff BigOperators

set_option linter.unusedSectionVars false

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-! ### The relabelling `jetPerm` -/

/-- `jetPerm r s k` sends the slots of `♭(∇^k u)`, ordered `[r lowered | k derivative | s]`, to
those of `∇^k(♭u)`, ordered `[k derivative | r lowered | s]`. -/
theorem jetPerm_val (r s : ℕ) : ∀ (k : ℕ) (i : Fin (r + (s + k))),
    ((jetPerm r s k i : Fin ((r + s) + k)) : ℕ) =
      if (i : ℕ) < r then i + k else if (i : ℕ) < r + k then i - r else i
  | 0, i => by
    simp only [jetPerm, Equiv.refl_apply]
    split_ifs <;> omega
  | k + 1, i => by
    simp only [jetPerm, Equiv.trans_apply]
    rcases lt_trichotomy (i : ℕ) r with h | h | h
    · have hl : lowerGradPerm r (s + k) i = Fin.succ ⟨i, by omega⟩ := by
        apply Fin.ext
        rw [lowerGradPerm, Fin.coe_cycleRange_of_lt (by rw [Fin.lt_def]; exact h)]
        rfl
      rw [hl, succCongr_succ, Fin.val_succ, jetPerm_val r s k]
      simp only [Fin.val_mk]
      split_ifs <;> omega
    · have hi : i = ⟨r, by omega⟩ := Fin.ext h
      conv_lhs => rw [hi]
      rw [lowerGradPerm, Fin.cycleRange_self, succCongr_zero]
      simp only [Fin.val_zero]
      split_ifs <;> omega
    · have hlt := i.isLt
      have hl : lowerGradPerm r (s + k) i = i :=
        Fin.cycleRange_of_gt (by rw [Fin.lt_def]; exact h)
      have hlt' : (i : ℕ) < r + (s + (k + 1)) := hlt
      have hi : i = Fin.succ (⟨(i : ℕ) - 1, by omega⟩ : Fin (r + (s + k))) :=
        Fin.ext (by simp only [Fin.val_succ]; omega)
      rw [hl]
      conv_lhs => rw [hi]
      rw [succCongr_succ, Fin.val_succ, jetPerm_val r s k]
      simp only [Fin.val_mk]
      split_ifs <;> omega

theorem jetPerm_val_lt {r s k : ℕ} (i : Fin (r + (s + k))) (h : (i : ℕ) < r) :
    ((jetPerm r s k i : Fin ((r + s) + k)) : ℕ) = i + k := by
  rw [jetPerm_val, if_pos h]

theorem jetPerm_val_mid {r s k : ℕ} (i : Fin (r + (s + k))) (h₁ : r ≤ (i : ℕ)) (h₂ : (i : ℕ) < r + k) :
    ((jetPerm r s k i : Fin ((r + s) + k)) : ℕ) = i - r := by
  rw [jetPerm_val, if_neg (by omega), if_pos h₂]

theorem jetPerm_val_ge {r s k : ℕ} (i : Fin (r + (s + k))) (h : r + k ≤ (i : ℕ)) :
    ((jetPerm r s k i : Fin ((r + s) + k)) : ℕ) = i := by
  rw [jetPerm_val, if_neg (by omega), if_neg (by omega)]

/-! ### Tuples with prescribed first slots -/

/-- A tangent vector as a model vector (the identity; it fixes the type for rewriting). -/
def toE {x : M} (w : TangentSpace I x) : E := w

variable (I) in
/-- A model vector as a tangent vector (the identity). -/
def ofE (x : M) (v : E) : TangentSpace I x := v

/-- The tuple with `w` in the first `p` slots and `v` in the remaining ones. -/
def appendFirst {s : ℕ} : ∀ p : ℕ, (Fin p → E) → (Fin s → E) → Fin (s + p) → E
  | 0, _, v => v
  | p + 1, w, v => Fin.cons (w 0) (appendFirst p (Fin.tail w) v)

theorem appendFirst_apply {s : ℕ} (p : ℕ) : ∀ (w : Fin p → E) (v : Fin s → E) (i : Fin (s + p)),
    appendFirst p w v i = if h : (i : ℕ) < p then w ⟨i, h⟩ else v ⟨i - p, by omega⟩ := by
  induction p with
  | zero =>
    intro w v i
    simp only [appendFirst, Nat.not_lt_zero, dite_false, Nat.sub_zero]
    rfl
  | succ p ih =>
    intro w v i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [appendFirst, Fin.cons_zero, Fin.val_zero, Nat.zero_lt_succ, dite_true]
      rfl
    · simp only [appendFirst, Fin.cons_succ, ih, Fin.tail, Fin.val_succ]
      by_cases h : (j : ℕ) < p
      · rw [dif_pos h, dif_pos (by omega)]
        rfl
      · rw [dif_neg h, dif_neg (by omega)]
        exact congrArg v (Fin.ext (by simp only [Fin.val_mk]; omega))

/-! ### Formulas in model coordinates -/

section Formulas

variable (g : SmoothRiemannianMetric I M)

theorem toModel_covGradBundleEquiv_symm {r n : ℕ} {x : M} (W : TensorRSSpace r (n + 1) I x)
    (w : TangentSpace I x) (β : Tensor0SModel r ℝ E) (v : Fin n → E) :
    TensorRSSpace.toModel ((covGradBundleEquiv (I := I) (M := M) r n x).symm W w) β v =
      TensorRSSpace.toModel W β (Fin.cons (toE w) v) := by
  rw [covGradBundleEquiv_symm_apply]
  change tensorRSSpaceContinuousLinearEquiv (I := I) r n x
      ((tensorRSSpaceContinuousLinearEquiv (I := I) r n x).symm
        ((covGradModelEquiv (E := E) r n).symm (TensorRSSpace.toModel W) w)) β v = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem toModel_covGradBundleEquiv {r n : ℕ} {x : M}
    (Φ : TangentSpace I x →L[ℝ] TensorRSSpace r n I x) (β : Tensor0SModel r ℝ E)
    (v : Fin (n + 1) → E) :
    TensorRSSpace.toModel (covGradBundleEquiv (I := I) (M := M) r n x Φ) β v =
      TensorRSSpace.toModel (Φ (ofE I x (v 0))) β (Matrix.vecTail v) := by
  rw [covGradBundleEquiv_apply]
  change tensorRSSpaceContinuousLinearEquiv (I := I) r (n + 1) x
      ((tensorRSSpaceContinuousLinearEquiv (I := I) r (n + 1) x).symm _) β v = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem toModel_evalFirst {r s : ℕ} {x : M} (p : ℕ) :
    ∀ (w : Fin p → TangentSpace I x) (ξ : TensorRSSpace r (s + p) I x) (β : Tensor0SModel r ℝ E)
      (v : Fin s → E),
      TensorRSSpace.toModel (evalFirst p w ξ) β v =
        TensorRSSpace.toModel ξ β (appendFirst p (fun i => toE (w i)) v) := by
  induction p with
  | zero => intro w ξ β v; rfl
  | succ p ih =>
    intro w ξ β v
    rw [evalFirst, ih, toModel_covGradBundleEquiv_symm]
    rfl

theorem toModel_prependCovectors {r t : ℕ} {x : M} (p : ℕ) :
    ∀ (θ : Fin p → (TangentSpace I x →L[ℝ] ℝ)) (η : TensorRSSpace r t I x)
      (β : Tensor0SModel r ℝ E) (v : Fin (t + p) → E),
      TensorRSSpace.toModel (prependCovectors p θ η) β v =
        (∏ i : Fin p, θ i (ofE I x (v ⟨i, by omega⟩))) *
          TensorRSSpace.toModel η β (fun j : Fin t => v ⟨j + p, by omega⟩) := by
  induction p with
  | zero =>
    intro θ η β v
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul, Nat.add_zero]
    rfl
  | succ p ih =>
    intro θ η β v
    rw [prependCovectors, toModel_covGradBundleEquiv]
    change tensorRSSpaceContinuousLinearEquiv (I := I) r (t + p) x
      (θ 0 (ofE I x (v 0)) • prependCovectors p (Fin.tail θ) η) β (Matrix.vecTail v) = _
    rw [map_smul, ContinuousLinearMap.smul_apply, ContinuousMultilinearMap.smul_apply]
    change θ 0 (ofE I x (v 0)) * TensorRSSpace.toModel (prependCovectors p (Fin.tail θ) η) β
      (Matrix.vecTail v) = _
    rw [ih, Fin.prod_univ_succ, mul_assoc]
    rfl

theorem toModel_castIdx {r a b : ℕ} (h : a = b) {x : M} (W : TensorRSSpace r a I x)
    (β : Tensor0SModel r ℝ E) (v : Fin b → E) :
    TensorRSSpace.toModel (EquationData.castIdx h x W) β v =
      TensorRSSpace.toModel W β (fun i => v (Fin.cast h i)) := by
  subst h
  rfl

theorem toModel_flat_apply {r s : ℕ} {x : M} (W : TensorRSSpace r s I x) (β : Tensor0SModel 0 ℝ E)
    (v : Fin (r + s) → E) :
    TensorRSSpace.toModel (flat g r s x W) β v =
      scalar0M E β * TensorRSSpace.toModel W
        (separableFormAt (I := I) (M := M) g x r (fun i => v (Fin.castAdd s i)))
        (fun j => v (Fin.natAdd r j)) := by
  rw [toModel_flat, modelRS0_apply_eq, ContinuousMultilinearMap.smul_apply, ← unitEquiv_apply,
    unitEquiv_flatModel, lowerAllUpperIndices_apply, smul_eq_mul]

theorem toModel_slotPerm_apply {a b : ℕ} (e : Fin a ≃ Fin b) {x : M} (W : TensorRSSpace 0 a I x)
    (β : Tensor0SModel 0 ℝ E) (v : Fin b → E) :
    TensorRSSpace.toModel (slotPerm I e x W) β v =
      scalar0M E β * TensorRSSpace.toModel W (unit0M E) (fun i => v (e i)) := by
  rw [toModel_slotPerm, modelRS0_apply_eq, ContinuousMultilinearMap.smul_apply, ← unitEquiv_apply,
    unitEquiv_permModel, ContinuousMultilinearMap.domDomCongr_apply, unitEquiv_apply, smul_eq_mul]

end Formulas

/-! ### The two compatibilities -/

section Compat

variable (g : SmoothRiemannianMetric I M)

/-- **Evaluating the first `p` slots commutes with lowering**: `(Λ_p ξ)(v, ·) = ♭(ξ(v, ·))`. -/
theorem evalFirst_jetFlat {r s p : ℕ} {x : M} (w : Fin p → TangentSpace I x)
    (ξ : TensorRSSpace r (s + p) I x) :
    evalFirst p w (slotPerm I (jetPerm r s p) x (flat g r (s + p) x ξ)) =
      flat g r s x (evalFirst p w ξ) := by
  refine rsToModel_injective (ContinuousLinearMap.ext fun β => ContinuousMultilinearMap.ext fun v => ?_)
  rw [toModel_evalFirst, toModel_slotPerm_apply, toModel_flat_apply, toModel_flat_apply,
    toModel_evalFirst, scalar0M_unit0M, one_mul]
  have h1 : (fun i : Fin r =>
      appendFirst p (fun i => toE (w i)) v (jetPerm r s p (Fin.castAdd (s + p) i))) =
      fun i => v (Fin.castAdd s i) := by
    funext i
    have hv := jetPerm_val_lt (s := s) (k := p) (Fin.castAdd (s + p) i) (by simp)
    rw [appendFirst_apply, dif_neg (by omega)]
    exact congrArg v (Fin.ext (by simp only [Fin.val_mk, Fin.coe_castAdd] at hv ⊢; omega))
  have h2 : (fun j : Fin (s + p) =>
      appendFirst p (fun i => toE (w i)) v (jetPerm r s p (Fin.natAdd r j))) =
      appendFirst p (fun i => toE (w i)) (fun j => v (Fin.natAdd r j)) := by
    funext j
    rw [appendFirst_apply, appendFirst_apply]
    by_cases hj : (j : ℕ) < p
    · have hv := jetPerm_val_mid (s := s) (k := p) (Fin.natAdd r j) (by simp) (by simp; omega)
      simp only [Fin.val_natAdd] at hv
      rw [dif_pos (by omega), dif_pos hj]
      exact congrArg (fun a => toE (w a)) (Fin.ext (by simp only [Fin.val_mk]; omega))
    · have hv := jetPerm_val_ge (s := s) (k := p) (Fin.natAdd r j) (by simp; omega)
      simp only [Fin.val_natAdd] at hv
      rw [dif_neg (by omega), dif_neg hj]
      exact congrArg v (Fin.ext (by simp only [Fin.val_mk, Fin.val_natAdd]; omega))
  rw [h1, h2]

/-- **Prepending covectors commutes with lowering**: `θ ⊗ Λ_p η = Λ_{2p}(θ ⊗ η)`, up to the
reindexings `(r + s) + p + p = (r + s) + 2p` and `s + p + p = s + 2p`. -/
theorem castIdx_prepend_jetFlat {r s p : ℕ} {x : M} (θ : Fin p → (TangentSpace I x →L[ℝ] ℝ))
    (η : TensorRSSpace r (s + p) I x) (h0 : (r + s) + p + p = (r + s) + 2 * p)
    (h : s + p + p = s + 2 * p) :
    EquationData.castIdx h0 x
        (prependCovectors p θ (slotPerm I (jetPerm r s p) x (flat g r (s + p) x η))) =
      slotPerm I (jetPerm r s (2 * p)) x
        (flat g r (s + 2 * p) x (EquationData.castIdx h x (prependCovectors p θ η))) := by
  refine rsToModel_injective (ContinuousLinearMap.ext fun β => ContinuousMultilinearMap.ext fun v => ?_)
  rw [toModel_castIdx, toModel_prependCovectors, toModel_slotPerm_apply, toModel_flat_apply,
    toModel_slotPerm_apply, toModel_flat_apply, toModel_castIdx, toModel_prependCovectors,
    scalar0M_unit0M, one_mul, one_mul, mul_left_comm]
  congr 2
  · refine Finset.prod_congr rfl fun i _ => congrArg (fun a => θ i (ofE I x a)) (congrArg v (Fin.ext ?_))
    have hv := jetPerm_val_mid (s := s) (k := 2 * p) (Fin.natAdd r (Fin.cast h ⟨i, by omega⟩))
      (by simp) (by simp; omega)
    simp only [Fin.val_natAdd, Fin.val_cast] at hv
    simp only [Fin.val_cast, Fin.val_mk, Fin.val_natAdd]
    omega
  · congr 1
    · congr 2
      funext i
      have hv := jetPerm_val_lt (s := s) (k := p) (Fin.castAdd (s + p) i) (by simp)
      have hv' := jetPerm_val_lt (s := s) (k := 2 * p) (Fin.castAdd (s + 2 * p) i) (by simp)
      refine congrArg v (Fin.ext ?_)
      simp only [Fin.val_cast, Fin.val_mk, Fin.coe_castAdd] at hv hv' ⊢
      omega
    · funext j
      refine congrArg v (Fin.ext ?_)
      by_cases hj : (j : ℕ) < p
      · have hv := jetPerm_val_mid (s := s) (k := p) (Fin.natAdd r j) (by simp) (by simp; omega)
        have hv' := jetPerm_val_mid (s := s) (k := 2 * p)
          (Fin.natAdd r (Fin.cast h ⟨j + p, by omega⟩)) (by simp) (by simp; omega)
        simp only [Fin.val_natAdd, Fin.val_cast, Fin.val_mk] at hv hv' ⊢
        omega
      · have hv := jetPerm_val_ge (s := s) (k := p) (Fin.natAdd r j) (by simp; omega)
        have hv' := jetPerm_val_ge (s := s) (k := 2 * p)
          (Fin.natAdd r (Fin.cast h ⟨j + p, by omega⟩)) (by simp; omega)
        simp only [Fin.val_natAdd, Fin.val_cast, Fin.val_mk] at hv hv' ⊢
        omega

end Compat

end ShortTime
