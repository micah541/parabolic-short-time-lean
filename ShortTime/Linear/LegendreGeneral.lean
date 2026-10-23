import ShortTime.Linear.LegendreOne
import ShortTime.Linear.PrincipalIter
import ShortTime.Linear.RicciEstimate

/-!
# The Legendre form through iterated flips (`lem:garding`, general order)

After `p` integrations by parts the principal coefficient `P : T⁰_{s+2p} → T⁰_s` has become the
iterated flip `P^{(p)} = flipIter p p P : T⁰_{s+p} → T⁰_{s+p}`, with

  `P^{(p)}(ξ)(v_0, …, v_{p-1}, ·) = P(v_{p-1}♭ ⊗ ⋯ ⊗ v_0♭ ⊗ ξ)`        (`evalFirst_flipIter`).

The covectors come out in reverse order. Expanding `⟨ξ', P^{(p)} η⟩` in an orthonormal frame
over the first `p` slots (`fiberInner_eq_sum_evalFirst`) therefore gives the Legendre form
`B_P(ξ, η)` of the paper, where `ξ'` is `ξ` with its first `p` slots reversed
(`legendreForm_eq_fiberInner_flipIter`). For `ξ = ∇^p u` the reversal is the slot permutation
`extPerm s p Fin.revPerm` (`evalFirst_rev_domDomCongrSection`), which `exists_perm_bound` controls.
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

variable (g : SmoothRiemannianMetric I M)

/-! ### The frame expansion over the first `p` slots -/

/-- `⟨ξ, η⟩ = Σ_K ⟨ξ(e_K, ·), η(e_K, ·)⟩`, the sum over all `K : Fin p → Fin n` of an orthonormal
frame. -/
theorem fiberInner_eq_sum_evalFirst (s : ℕ) (x : M) (p : ℕ) : ∀ (ξ η : TensorRSSpace 0 (s + p) I x),
    fiberInner g 0 (s + p) x ξ η =
      ∑ K : Fin p → Fin (Module.finrank ℝ (TangentSpace I x)),
        fiberInner g 0 s x (evalFirst p (fun i => tangentFrame g x (K i)) ξ)
          (evalFirst p (fun i => tangentFrame g x (K i)) η) := by
  induction p with
  | zero =>
    intro ξ η
    rw [Fintype.sum_unique]
    rfl
  | succ p ih =>
    intro ξ η
    refine (fiberInner_eq_sum_evalSlot g (s + p) x ξ η).trans ?_
    simp_rw [ih]
    rw [← (Fin.consEquiv fun _ => Fin (Module.finrank ℝ (TangentSpace I x))).sum_comp,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun K _ => ?_
    simp only [Fin.consEquiv_apply, evalFirst, Fin.cons_zero]
    rfl

/-! ### Transport of ranks -/

omit [NeZero (Module.finrank ℝ E)] in
theorem castIdx_castIdx {r a b c : ℕ} (h₁ : a = b) (h₂ : b = c) (x : M)
    (y : TensorRSSpace r a I x) :
    EquationData.castIdx (r := r) h₂ x (EquationData.castIdx (r := r) h₁ x y) =
      EquationData.castIdx (r := r) (h₁.trans h₂) x y := by
  subst h₁
  subst h₂
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem castIdx_covGradBundleEquiv {r a b : ℕ} (h : a = b) (h' : a + 1 = b + 1) (x : M)
    (Φ : TangentSpace I x →L[ℝ] TensorRSSpace r a I x) :
    EquationData.castIdx (r := r) h' x (covGradBundleEquiv (I := I) (M := M) r a x Φ) =
      covGradBundleEquiv (I := I) (M := M) r b x
        ((EquationData.castIdx (r := r) h x).toContinuousLinearMap.comp Φ) := by
  subst h
  rfl

theorem castIn_opFieldHom {a a' b : ℕ} (h : a = a') (P : SmoothCcTensor g a b) (x : M)
    (ξ : TensorRSSpace 0 a' I x) :
    opFieldHom ((castIn g h P).toSection x) ξ =
      opFieldHom (P.toSection x) (EquationData.castIdx (r := 0) h.symm x ξ) := by
  subst h
  rfl

/-- Prepending `θ_0, …, θ_{j-1}` to `θ_j ⊗ η` is prepending all of `θ`. -/
theorem prependCovectors_init {t : ℕ} (x : M) (η : TensorRSSpace 0 t I x) : ∀ (j : ℕ)
    (θ : Fin (j + 1) → (TangentSpace I x →L[ℝ] ℝ)),
    EquationData.castIdx (r := 0) (by omega : t + 1 + j = t + (j + 1)) x
        (prependCovectors j (Fin.init θ) (prependCovectors 1 (fun _ => θ (Fin.last j)) η)) =
      prependCovectors (j + 1) θ η
  | 0, θ => by
    change prependCovectors 1 (fun _ => θ (Fin.last 0)) η = prependCovectors 1 θ η
    congr 1
    funext i
    rw [Subsingleton.elim i (Fin.last 0)]
  | j + 1, θ => by
    have ih := prependCovectors_init x η j (Fin.tail θ)
    have h1 : Fin.tail (Fin.init θ) = Fin.init (Fin.tail θ) := Fin.tail_init_eq_init_tail θ
    have h2 : θ (Fin.last (j + 1)) = Fin.tail θ (Fin.last j) := by simp [Fin.tail, Fin.succ_last]
    have h3 : Fin.init θ 0 = θ 0 := by simp [Fin.init]
    change EquationData.castIdx (r := 0) _ x
        (covGradBundleEquiv (I := I) (M := M) 0 (t + 1 + j) x
          ((Fin.init θ 0).smulRight
            (prependCovectors j (Fin.tail (Fin.init θ))
              (prependCovectors 1 (fun _ => θ (Fin.last (j + 1))) η)))) =
      covGradBundleEquiv (I := I) (M := M) 0 (t + (j + 1)) x
        ((θ 0).smulRight (prependCovectors (j + 1) (Fin.tail θ) η))
    refine (castIdx_covGradBundleEquiv (a := t + 1 + j) (b := t + (j + 1)) (by omega) _ x _).trans ?_
    rw [← ih, h1, h2, h3]
    congr 1
    refine ContinuousLinearMap.ext fun w => ?_
    simp [ContinuousLinearMap.smulRight_apply]

/-! ### Iterated flips evaluate as reversed prepending -/

variable [CompleteSpace E]

theorem evalSlot_opFieldHom_flipFib' (m n : ℕ) (x : M)
    (A : Tensor0SSpace (m + 1) I x →L[ℝ] Tensor0SSpace n I x) (v : TangentSpace I x)
    (ξ : TensorRSSpace 0 m I x) :
    evalSlot 0 n x v
        (opFieldHom (show TensorRSSpace m (n + 1) I x from flipFib g m n x A) ξ) =
      opFieldHom (show TensorRSSpace (m + 1) n I x from A)
        (prependCovectors 1 (fun _ => g.inner x v) ξ) := by
  refine ContinuousLinearMap.ext fun D => ?_
  rw [evalSlot_apply]
  change tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) n x (flipFib g m n x A
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from ξ) D)) v =
    A ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
      prependCovectors 1 (fun _ => g.inner x v) ξ) D)
  rw [tensor0SCurry_flipFib, flipCurried_apply, prependCovectors_one_apply]

/-- **The iterated flip, evaluated.** `P^{(j)}(ξ)(v_0, …, v_{j-1}, ·) = P(v_{j-1}♭ ⊗ ⋯ ⊗ v_0♭ ⊗ ξ)`. -/
theorem evalFirst_flipIter (s p : ℕ) (x : M) : ∀ (j i : ℕ) (h : i + j = 2 * p)
    (P : SmoothCcTensor g (s + 2 * p) s) (v : Fin j → TangentSpace I x)
    (ξ : TensorRSSpace 0 (s + i) I x),
    evalFirst j v (opFieldHom ((flipIter g s p j i h P).toSection x) ξ) =
      opFieldHom (P.toSection x) (EquationData.castIdx (r := 0) (by omega) x
        (prependCovectors j (fun k => g.inner x (v (Fin.rev k))) ξ))
  | 0, i, h, P, v, ξ => castIn_opFieldHom g _ P x ξ
  | j + 1, i, h, P, v, ξ => by
    have ih := evalFirst_flipIter s p x j (i + 1) (by omega) P (Fin.tail v)
      (prependCovectors 1 (fun _ => g.inner x (v 0)) ξ)
    change evalFirst j (Fin.tail v) (evalSlot 0 (s + j) x (v 0)
        (opFieldHom (show TensorRSSpace (s + i) (s + j + 1) I x from
          flipFib g (s + i) (s + j) x
            ((flipIter g s p j (i + 1) (by omega) P).toSection x)) ξ)) = _
    rw [evalSlot_opFieldHom_flipFib', ih]
    congr 1
    have hθ := prependCovectors_init (I := I) x ξ j (fun k => g.inner x (v (Fin.rev k)))
    have hinit : Fin.init (fun k : Fin (j + 1) => g.inner x (v (Fin.rev k))) =
        fun k => g.inner x (Fin.tail v (Fin.rev k)) := by
      funext k
      simp [Fin.init, Fin.tail, Fin.rev_castSucc]
    rw [hinit, Fin.rev_last] at hθ
    rw [← hθ, castIdx_castIdx]

/-! ### The Legendre form through the `p`-th flip -/

/-- **Legendre form through flips.** If `ξ'` is `ξ` with its first `p` slots reversed, then
`B_P(ξ, η) = ⟨ξ', P^{(p)} η⟩`. -/
theorem legendreForm_eq_fiberInner_flipIter (s p : ℕ) (x : M) (P : SmoothCcTensor g (s + 2 * p) s)
    (hc : s + p + p = s + 2 * p) (ξ ξ' η : TensorRSSpace 0 (s + p) I x)
    (hξ : ∀ w : Fin p → TangentSpace I x, evalFirst p (fun k => w (Fin.rev k)) ξ' = evalFirst p w ξ) :
    legendreForm g 0 s p x
        ((opFieldHom (P.toSection x)).comp
          (EquationData.castIdx (r := 0) hc x).toContinuousLinearMap) ξ η =
      fiberInner g 0 (s + p) x ξ'
        (opFieldHom ((flipIter g s p p p (by omega) P).toSection x) η) := by
  rw [legendreForm_eq, fiberInner_eq_sum_evalFirst]
  simp_rw [evalFirst_flipIter]
  have hinv : Function.Involutive
      (fun K : Fin p → Fin (Module.finrank ℝ (TangentSpace I x)) => K ∘ Fin.rev) := by
    intro K
    funext k
    simp
  refine Fintype.sum_bijective _ hinv.bijective _ _ fun K => ?_
  simp only [Function.comp_apply, Fin.rev_rev, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe]
  rw [← hξ (fun i => tangentFrame g x (K i))]

/-! ### Reversing the first `p` slots of a section -/

omit [CompleteSpace E] in
/-- Two fibre elements of `T⁰_a = Hom(T⁰_0, T⁰_a)` agree if they agree on the unit. -/
theorem tensorRS_ext_unit {a : ℕ} {x : M} {ξ ξ' : TensorRSSpace 0 a I x}
    (h : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace a I x from ξ)
        (unitZeroSec (I := I) (M := M) x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace a I x from ξ')
        (unitZeroSec (I := I) (M := M) x)) : ξ = ξ' := by
  change (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace a I x from ξ) =
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace a I x from ξ')
  refine ContinuousLinearMap.ext fun D => ?_
  rw [zeroTensor_eq_smul_unitZeroSec x D, map_smul, map_smul, h]

/-- The model vector `(w_0, …, w_{p-1}, vs_0, …, vs_{s-1})`. -/
def appendIdx {s p : ℕ} (w : Fin p → E) (vs : Fin s → E) : Fin (s + p) → E :=
  fun k => if h : (k : ℕ) < p then w ⟨k, h⟩ else vs ⟨k - p, by omega⟩

omit [CompleteSpace E] in
/-- `evalFirst` in the model: evaluate the first `p` slots on `w`. -/
theorem evalFirst_toModel {s : ℕ} (x : M) : ∀ (p : ℕ) (w : Fin p → TangentSpace I x)
    (ξ : TensorRSSpace 0 (s + p) I x) (D : Tensor0SSpace 0 I x) (vs : Fin s → E),
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from evalFirst p w ξ) D) vs =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + p) I x from ξ) D)
        (appendIdx (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (w k)) vs)
  | 0, w, ξ, D, vs => by
    change _ = Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from ξ) D) _
    congr 1
  | p + 1, w, ξ, D, vs => by
    change Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          evalFirst p (Fin.tail w) (evalSlot 0 (s + p) x (w 0) ξ)) D) vs = _
    rw [evalFirst_toModel x p, evalSlot_apply, TensorMultilinear.tensor0S_curry_toModel_apply_tangent]
    congr 1
    funext k
    refine Fin.cases ?_ (fun k => ?_) k
    · simp [appendIdx]
    · simp only [Fin.cons_succ, appendIdx, Fin.val_succ, Fin.tail]
      by_cases hk : (k : ℕ) < p
      · rw [dif_pos hk, dif_pos (by omega)]
        rfl
      · rw [dif_neg hk, dif_neg (by omega)]
        congr 2
        omega

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem extPerm_apply_lt (s p : ℕ) (σ : Equiv.Perm (Fin p)) (k : Fin (s + p)) (hk : (k : ℕ) < p) :
    (extPerm s p σ k : ℕ) = σ ⟨k, hk⟩ := by
  have hc : (finSumFinEquiv.trans (finCongr (Nat.add_comm p s))).symm k = Sum.inl ⟨k, hk⟩ := by
    rw [Equiv.symm_apply_eq]
    ext
    simp
  change ((finSumFinEquiv.trans (finCongr (Nat.add_comm p s)))
      (Equiv.sumCongr σ (1 : Equiv.Perm (Fin s))
        ((finSumFinEquiv.trans (finCongr (Nat.add_comm p s))).symm k)) : ℕ) = _
  rw [hc]
  simp

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem extPerm_apply_ge (s p : ℕ) (σ : Equiv.Perm (Fin p)) (k : Fin (s + p)) (hk : p ≤ (k : ℕ)) :
    extPerm s p σ k = k := by
  have hc : (finSumFinEquiv.trans (finCongr (Nat.add_comm p s))).symm k =
      Sum.inr ⟨k - p, by omega⟩ := by
    rw [Equiv.symm_apply_eq]
    ext
    simp
    omega
  change (finSumFinEquiv.trans (finCongr (Nat.add_comm p s)))
      (Equiv.sumCongr σ (1 : Equiv.Perm (Fin s))
        ((finSumFinEquiv.trans (finCongr (Nat.add_comm p s))).symm k)) = _
  rw [hc]
  ext
  simp
  omega

/-- **The reversal.** Reversing the first `p` slots of a section is `extPerm s p Fin.revPerm`. -/
theorem evalFirst_rev_domDomCongrSection {s p : ℕ} (Ψ : SmoothCcTensor g 0 (s + p)) (x : M)
    (w : Fin p → TangentSpace I x) :
    evalFirst p (fun k => w (Fin.rev k))
        ((domDomCongrSection (I := I) g (extPerm s p Fin.revPerm) Ψ).toSection x) =
      evalFirst p w (Ψ.toSection x) := by
  apply tensorRS_ext_unit
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext fun vs => ?_
  rw [evalFirst_toModel, evalFirst_toModel]
  change unitModel (I := I) (M := M) g (s + p)
      (domDomCongrSection (I := I) g (extPerm s p Fin.revPerm) Ψ) x _ =
    unitModel (I := I) (M := M) g (s + p) Ψ x _
  rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext k
  by_cases hk : (k : ℕ) < p
  · have h1 := extPerm_apply_lt s p Fin.revPerm k hk
    simp only [appendIdx, h1, Fin.revPerm_apply, Fin.val_rev, dif_pos hk,
      dif_pos (show p - (k + 1) < p by omega)]
    congr 3
    ext
    simp only [Fin.val_rev]
    omega
  · rw [extPerm_apply_ge s p _ k (by omega)]
    simp only [appendIdx, dif_neg hk]

end ShortTime
