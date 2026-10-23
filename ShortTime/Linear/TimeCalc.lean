import ShortTime.Linear.EnergyHigher

/-!
# Time derivatives of operators

Calculus for the time derivatives `∂ₜ^j` (`timeDerivIter`) of jointly smooth families, used by the
a priori estimate in parabolic norms (`prop:apriori`).

* `timeDerivIter_iteratedCovGrad`: `∂ₜ^j ∇^i u = ∇^i ∂ₜ^j u`.
* `timeDeriv_operatorFieldApply`, `LinearOp.timeDeriv_apply`: the Leibniz rule
  `∂ₜ(L u) = (∂ₜL) u + L ∂ₜu`, where `∂ₜL` has the time-differentiated coefficients (`LinearOp.dt`).
* `LinearOp.exists_sobolevNormSq_timeDerivIter_apply_le`:
  `‖∂ₜ^n(L u)‖²_{H^l} ≤ C Σ_{b ≤ n} ‖∂ₜ^b u‖²_{H^{l+2p}}`, uniformly in `t`.
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

variable {g : SmoothRiemannianMetric I M}

/-! ### Identifying time derivatives -/

section General

variable {a b : ℕ} {T : ℝ}

/-- A derivative within `[0,T]` identifies the time derivative. -/
theorem timeDeriv_eq (hT : 0 < T) {u : ℝ → SmoothCcTensor g a b}
    (hu : JointlySmoothOn g a b (Icc 0 T) u) {t : ℝ} (ht : t ∈ Icc 0 T) {v : SmoothCcTensor g a b}
    (hd : ∀ x : M, HasDerivWithinAt (fun τ => (u τ).toFun x) (v.toFun x) (Icc 0 T) t) :
    timeDeriv T u t = v :=
  smoothCcTensor_eq_of_toFun fun x =>
    (uniqueDiffOn_Icc hT t ht).eq_deriv _ (hasDerivWithinAt_timeDeriv hT hu ht x) (hd x)

/-- The time derivative on `[0,T]` only depends on the values on `[0,T]`. -/
theorem timeDeriv_congr (hT : 0 < T) {u v : ℝ → SmoothCcTensor g a b}
    (hu : JointlySmoothOn g a b (Icc 0 T) u) (hv : JointlySmoothOn g a b (Icc 0 T) v)
    (h : EqOn u v (Icc 0 T)) {t : ℝ} (ht : t ∈ Icc 0 T) : timeDeriv T u t = timeDeriv T v t :=
  timeDeriv_eq hT hu ht fun x => (hasDerivWithinAt_timeDeriv hT hv ht x).congr
    (fun τ hτ => by rw [h hτ]; rfl) (by rw [h ht]; rfl)

theorem timeDerivIter_congr (hT : 0 < T) {u v : ℝ → SmoothCcTensor g a b}
    (hu : JointlySmoothOn g a b (Icc 0 T) u) (hv : JointlySmoothOn g a b (Icc 0 T) v)
    (h : EqOn u v (Icc 0 T)) : ∀ j, EqOn (timeDerivIter T u j) (timeDerivIter T v j) (Icc 0 T)
  | 0 => h
  | j + 1 => fun _ ht => timeDeriv_congr hT (jointlySmoothOn_timeDerivIter hT hu j)
      (jointlySmoothOn_timeDerivIter hT hv j) (timeDerivIter_congr hT hu hv h j) ht

theorem timeDerivIter_succ' (u : ℝ → SmoothCcTensor g a b) :
    ∀ j, timeDerivIter T u (j + 1) = timeDerivIter T (timeDeriv T u) j
  | 0 => rfl
  | j + 1 => by
    change timeDeriv T (timeDerivIter T u (j + 1)) = timeDeriv T (timeDerivIter T (timeDeriv T u) j)
    rw [timeDerivIter_succ' u j]

theorem timeDeriv_const_zero (hT : 0 < T) (t : ℝ) :
    timeDeriv T (fun _ => (0 : SmoothCcTensor g a b)) t = 0 := by
  have h := timeDeriv_smul hT (0 : ℝ) (jointlySmoothOn_const g (Icc 0 T) (0 : SmoothCcTensor g a b))
  simp only [zero_smul] at h
  exact congrFun h t

theorem timeDeriv_sum (hT : 0 < T) {ι : Type*} (S : Finset ι) {F : ι → ℝ → SmoothCcTensor g a b}
    (hF : ∀ i ∈ S, JointlySmoothOn g a b (Icc 0 T) (F i)) (t : ℝ) :
    timeDeriv T (fun τ => ∑ i ∈ S, F i τ) t = ∑ i ∈ S, timeDeriv T (F i) t := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using timeDeriv_const_zero hT t
  | insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    have hS : JointlySmoothOn g a b (Icc 0 T) (fun τ => ∑ j ∈ S, F j τ) :=
      jointlySmoothOn_sum S fun j hj => hF j (Finset.mem_insert_of_mem hj)
    rw [timeDeriv_add hT (hF i (Finset.mem_insert_self i S)) hS]
    dsimp only
    rw [ih fun j hj => hF j (Finset.mem_insert_of_mem hj)]

/-- **Leibniz rule** for coefficient fields. -/
theorem timeDeriv_operatorFieldApply (hT : 0 < T) {b' : ℕ} {A : ℝ → SmoothCcTensor g a b'}
    {W : ℝ → SmoothCcTensor g 0 a} (hA : JointlySmoothOn g a b' (Icc 0 T) A)
    (hW : JointlySmoothOn g 0 a (Icc 0 T) W) {t : ℝ} (ht : t ∈ Icc 0 T) :
    timeDeriv T (fun τ => operatorFieldApply (I := I) (M := M) g a b' (A τ) (W τ)) t =
      operatorFieldApply (I := I) (M := M) g a b' (timeDeriv T A t) (W t) +
        operatorFieldApply (I := I) (M := M) g a b' (A t) (timeDeriv T W t) :=
  timeDeriv_eq hT (jointlySmoothOn_operatorFieldApply hA hW) ht fun x => by
    have h := (hasDerivWithinAt_timeDeriv hT hA ht x).clm_comp (hasDerivWithinAt_timeDeriv hT hW ht x)
    rw [SmoothCcTensor.toFun_add, Pi.add_apply]
    exact h

end General

/-! ### Time derivatives commute with `∇` -/

section Commute

variable {s : ℕ} {T : ℝ}

theorem timeDeriv_covGrad (hT : 0 < T) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) {t : ℝ} (ht : t ∈ Icc 0 T) :
    timeDeriv T (fun τ => covGrad (I := I) (M := M) g 0 s (u τ)) t =
      covGrad (I := I) (M := M) g 0 s (timeDeriv T u t) :=
  timeDeriv_eq hT (jointlySmoothOn_covGrad hu) ht fun x =>
    hasDerivWithinAt_covGrad hT hu (jointlySmoothOn_timeDeriv hT hu)
      (fun _ ht' x => hasDerivWithinAt_timeDeriv hT hu ht' x) t ht x

theorem timeDeriv_iteratedCovGrad (hT : 0 < T) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) :
    ∀ (i : ℕ) {t : ℝ}, t ∈ Icc 0 T →
      timeDeriv T (fun τ => iteratedCovGrad g 0 s i (u τ)) t =
        iteratedCovGrad g 0 s i (timeDeriv T u t)
  | 0, _, _ => rfl
  | i + 1, t, ht => by
    change timeDeriv T (fun τ => covGrad (I := I) (M := M) g 0 (s + i)
        (iteratedCovGrad g 0 s i (u τ))) t =
      covGrad (I := I) (M := M) g 0 (s + i) (iteratedCovGrad g 0 s i (timeDeriv T u t))
    rw [timeDeriv_covGrad hT (jointlySmoothOn_iteratedCovGrad hu i) ht,
      timeDeriv_iteratedCovGrad hT hu i ht]

/-- **`∂ₜ^j ∇^i u = ∇^i ∂ₜ^j u`** on `[0,T]`. -/
theorem timeDerivIter_iteratedCovGrad (hT : 0 < T) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (i : ℕ) :
    ∀ (j : ℕ) {t : ℝ}, t ∈ Icc 0 T →
      timeDerivIter T (fun τ => iteratedCovGrad g 0 s i (u τ)) j t =
        iteratedCovGrad g 0 s i (timeDerivIter T u j t)
  | 0, _, _ => rfl
  | j + 1, t, ht => by
    change timeDeriv T (timeDerivIter T (fun τ => iteratedCovGrad g 0 s i (u τ)) j) t =
      iteratedCovGrad g 0 s i (timeDeriv T (timeDerivIter T u j) t)
    have hj := jointlySmoothOn_timeDerivIter hT hu j
    rw [timeDeriv_congr hT
      (jointlySmoothOn_timeDerivIter hT (jointlySmoothOn_iteratedCovGrad hu i) j)
      (jointlySmoothOn_iteratedCovGrad hj i)
      (fun τ hτ => timeDerivIter_iteratedCovGrad hT hu i j hτ) ht,
      timeDeriv_iteratedCovGrad hT hj i ht]

end Commute

/-! ### Sobolev bounds for operators -/

section Bounds

variable {s : ℕ}

theorem sobolevNormSq_iteratedCovGrad_le (l : ℕ) (u : SmoothCcTensor g 0 s) :
    ∀ k, sobolevNormSq g 0 (s + k) l (iteratedCovGrad g 0 s k u) ≤ sobolevNormSq g 0 s (l + k) u
  | 0 => le_rfl
  | k + 1 => (sobolevNormSq_covGrad_le (s + k) l (iteratedCovGrad g 0 s k u)).trans
      (sobolevNormSq_iteratedCovGrad_le (l + 1) u k |>.trans_eq (by rw [show l + 1 + k = l + (k + 1) by omega]))

theorem sobolevNormSq_sum_le {ι : Type*} (S : Finset ι) (l : ℕ) (F : ι → SmoothCcTensor g 0 s) :
    sobolevNormSq g 0 s l (∑ i ∈ S, F i) ≤ 2 ^ S.card * ∑ i ∈ S, sobolevNormSq g 0 s l (F i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.card_empty, pow_zero, one_mul]
    have h := sobolevNormSq_smul (g := g) s l 0 0
    rw [zero_smul, zero_pow two_ne_zero, zero_mul] at h
    rw [h]
  | insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.card_insert_of_notMem hi]
    have h1 := sobolevNormSq_add_le s l (F i) (∑ j ∈ S, F j)
    have h2 : 0 ≤ ∑ j ∈ S, sobolevNormSq g 0 s l (F j) :=
      Finset.sum_nonneg fun j _ => sobolevNormSq_nonneg s l (F j)
    have h3 := sobolevNormSq_nonneg s l (F i)
    have h4 : (2 : ℝ) ≤ 2 ^ (S.card + 1) := by
      calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (S.card + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h5 : (2 : ℝ) * 2 ^ S.card = 2 ^ (S.card + 1) := by rw [pow_succ]; ring
    nlinarith

end Bounds

namespace LinearOp

variable {s p : ℕ} {T : ℝ}

/-- `L` maps `H^{l+2p}` to `H^l`, uniformly in `t ∈ [0,T]`. -/
theorem exists_sobolevNormSq_apply_le (L : LinearOp g s p T) (l : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ v : SmoothCcTensor g 0 s,
      sobolevNormSq g 0 s l (L.apply t v) ≤ C * sobolevNormSq g 0 s (l + 2 * p) v := by
  have hk : ∀ k : Fin (2 * p + 1), ∃ C, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ W : SmoothCcTensor g 0 (s + k),
      sobolevNormSq g 0 s l (operatorFieldApply (I := I) (M := M) g (s + k) s (L.coeff k t) W) ≤
        C * sobolevNormSq g 0 (s + k) l W :=
    fun k => exists_sobolevNormSq_opField_le (g := g) (T := T) l (s + k) s (L.coeff k) (L.smooth k)
  choose C hC0 hC using hk
  refine ⟨2 ^ (2 * p + 1) * ∑ k, C k, mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => hC0 k),
    fun t ht v => ?_⟩
  refine (sobolevNormSq_sum_le _ l _).trans ?_
  rw [Finset.card_univ, Fintype.card_fin, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => (hC k t ht _).trans ?_
  refine mul_le_mul_of_nonneg_left ((sobolevNormSq_iteratedCovGrad_le l v k).trans ?_) (hC0 k)
  exact sobolevNormSq_mono s (by omega) v

/-- The operator with the time-differentiated coefficients `∂ₜA_k`. -/
def dt (hT : 0 < T) (L : LinearOp g s p T) : LinearOp g s p T where
  coeff k := timeDeriv T (L.coeff k)
  smooth k := jointlySmoothOn_timeDeriv hT (L.smooth k)

/-- **Leibniz rule**: `∂ₜ(L u) = (∂ₜL) u + L ∂ₜu` on `[0,T]`. -/
theorem timeDeriv_apply (hT : 0 < T) (L : LinearOp g s p T) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) {t : ℝ} (ht : t ∈ Icc 0 T) :
    timeDeriv T (fun τ => L.apply τ (u τ)) t = (L.dt hT).apply t (u t) + L.apply t (timeDeriv T u t) := by
  unfold apply
  rw [timeDeriv_sum hT _ (fun k _ => jointlySmoothOn_operatorFieldApply (L.smooth k)
    (jointlySmoothOn_iteratedCovGrad hu k)) t, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [timeDeriv_operatorFieldApply hT (L.smooth k) (jointlySmoothOn_iteratedCovGrad hu k) ht,
    timeDeriv_iteratedCovGrad hT hu k ht]
  rfl

/-- **`‖∂ₜ^n(L u)‖²_{H^l} ≤ C Σ_{b ≤ n} ‖∂ₜ^b u‖²_{H^{l+2p}}`**, uniformly in `t ∈ [0,T]`. -/
theorem exists_sobolevNormSq_timeDerivIter_apply_le (hT : 0 < T) (l : ℕ) :
    ∀ (n : ℕ) (L : LinearOp g s p T), ∃ C, 0 ≤ C ∧ ∀ u : ℝ → SmoothCcTensor g 0 s,
      JointlySmoothOn g 0 s (Icc 0 T) u → ∀ t ∈ Icc (0 : ℝ) T,
        sobolevNormSq g 0 s l (timeDerivIter T (fun τ => L.apply τ (u τ)) n t) ≤
          C * ∑ b ∈ Finset.range (n + 1), sobolevNormSq g 0 s (l + 2 * p) (timeDerivIter T u b t)
  | 0, L => by
    obtain ⟨C, hC, h⟩ := L.exists_sobolevNormSq_apply_le l
    exact ⟨C, hC, fun u _ t ht => by rw [zero_add, Finset.sum_range_one]; exact h t ht (u t)⟩
  | n + 1, L => by
    obtain ⟨C₁, hC₁, h₁⟩ := exists_sobolevNormSq_timeDerivIter_apply_le hT l n (L.dt hT)
    obtain ⟨C₂, hC₂, h₂⟩ := exists_sobolevNormSq_timeDerivIter_apply_le hT l n L
    refine ⟨2 * (C₁ + C₂), by positivity, fun u hu t ht => ?_⟩
    have hdu := jointlySmoothOn_timeDeriv hT hu
    have hLu : JointlySmoothOn g 0 s (Icc 0 T) (fun τ => L.apply τ (u τ)) := L.jointlySmoothOn_apply hu
    have hA : JointlySmoothOn g 0 s (Icc 0 T) (fun τ => (L.dt hT).apply τ (u τ)) :=
      (L.dt hT).jointlySmoothOn_apply hu
    have hB : JointlySmoothOn g 0 s (Icc 0 T) (fun τ => L.apply τ (timeDeriv T u τ)) :=
      L.jointlySmoothOn_apply hdu
    -- `∂ₜ^{n+1}(Lu) = ∂ₜ^n((∂ₜL)u) + ∂ₜ^n(L ∂ₜu)` on `[0,T]`
    have hsplit : timeDerivIter T (fun τ => L.apply τ (u τ)) (n + 1) t =
        timeDerivIter T (fun τ => (L.dt hT).apply τ (u τ)) n t +
          timeDerivIter T (fun τ => L.apply τ (timeDeriv T u τ)) n t := by
      rw [timeDerivIter_succ', timeDerivIter_congr hT (jointlySmoothOn_timeDeriv hT hLu)
        (jointlySmoothOn_add hA hB) (fun τ hτ => L.timeDeriv_apply hT hu hτ) n ht,
        timeDerivIter_add hT hA hB n]
    rw [hsplit]
    refine (sobolevNormSq_add_le s l _ _).trans ?_
    have e₁ := h₁ u hu t ht
    have e₂ := h₂ (timeDeriv T u) hdu t ht
    simp only [← timeDerivIter_succ'] at e₂
    have hs₁ : ∑ b ∈ Finset.range (n + 1), sobolevNormSq g 0 s (l + 2 * p) (timeDerivIter T u b t) ≤
        ∑ b ∈ Finset.range (n + 1 + 1), sobolevNormSq g 0 s (l + 2 * p) (timeDerivIter T u b t) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
        fun b _ _ => sobolevNormSq_nonneg s _ _
    have hs₂ : ∑ b ∈ Finset.range (n + 1),
        sobolevNormSq g 0 s (l + 2 * p) (timeDerivIter T u (b + 1) t) ≤
        ∑ b ∈ Finset.range (n + 1 + 1), sobolevNormSq g 0 s (l + 2 * p) (timeDerivIter T u b t) := by
      rw [Finset.sum_range_succ' _ (n + 1)]
      exact le_add_of_nonneg_right (sobolevNormSq_nonneg s _ _)
    have hS : 0 ≤ ∑ b ∈ Finset.range (n + 1 + 1),
        sobolevNormSq g 0 s (l + 2 * p) (timeDerivIter T u b t) :=
      Finset.sum_nonneg fun b _ => sobolevNormSq_nonneg s _ _
    nlinarith [mul_le_mul_of_nonneg_left hs₁ hC₁, mul_le_mul_of_nonneg_left hs₂ hC₂]

end LinearOp

end ShortTime
