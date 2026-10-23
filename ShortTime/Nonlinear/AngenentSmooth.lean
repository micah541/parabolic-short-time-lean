import ShortTime.Nonlinear.AngenentFlow
import ShortTime.Nonlinear.Evaluation

/-!
# Smooth dependence of the composite pullback on `σ ∈ ℝⁿ`

Paper: Lemma `lem:flows` (a), for the composite `Π_σ = Π^{B 0}_{σ 0} ∘ ⋯` over a frame.

* `covAlongExt`: `∇_X : 𝒫^{m+1} → 𝒫^m`, the continuous extension of `u ↦ ∇_X u`
  (`∂ₜ - (∂ₜ - ∇_X)` for the first-order operator `covOp`).
* `hasDerivAt_hpullExt_levelIncl`: for **every** `x ∈ 𝒫^{m+1}`, `d/dτ Π_τ x = Π_τ ∇_X x` in `𝒫^m`
  (from the smooth case by a uniform Lipschitz bound and density).
* `contDiff_hpullExt_family`: if `λ ↦ R_m(λ) ∈ 𝒫^m` is `C^∞` for every level `m`, compatibly with
  the inclusions, then `(τ, λ) ↦ Π_τ R_m(λ)` is `C^∞` (partial derivatives, Mathlib's
  `hasStrictFDerivAt_uncurry_coprod`, induction on the order).
* `contDiff_iterPullExt_ofSmooth`: for a smooth family `u`, `σ ↦ Π_σ u` is `C^∞` from `ℝⁿ` into
  `𝒫^m`.
-/

noncomputable section

open Bundle Manifold Set Filter Asymptotics
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Spectral
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

namespace ShortTime

namespace HFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

open ParabolicSpace

variable (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
variable (g : SmoothRiemannianMetric I M) (s : ℕ) {p : ℕ} {T : ℝ}

/-! ### `∇_X` on the parabolic spaces -/

/-- The coefficients of `∇_X`: `ι_X` in degree `1`, zero otherwise. -/
def covCoeff (k : Fin (2 * p + 1)) : SmoothCcTensor g (s + k) s :=
  if h : (k : ℕ) = 1 then cast (by rw [h]) (insField g X : SmoothCcTensor g (s + 1) s) else 0

/-- `∇_X` as a linear operator of order `1 ≤ 2p` (coefficient `ι_X` in front of `∇`). -/
def covOp (hp : 1 ≤ p) : LinearOp g s p T where
  coeff k _ := covCoeff X g s k
  smooth k := _root_.ShortTime.jointlySmoothOn_const g _ _

theorem covOp_apply (hp : 1 ≤ p) (t : ℝ) (u : SmoothCcTensor g 0 s) :
    (covOp X g s (T := T) hp).apply t u = covAlong X g s u := by
  unfold LinearOp.apply
  rw [Finset.sum_eq_single (⟨1, by omega⟩ : Fin (2 * p + 1))]
  · rfl
  · intro k _ hk
    have hk1 : (k : ℕ) ≠ 1 := fun h => hk (Fin.ext h)
    simp only [covOp, covCoeff, dif_neg hk1, operatorFieldApplication_zero_left]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **`∇_X : 𝒫^{m+1} → 𝒫^m`**. -/
def covAlongExt (hp : 1 ≤ p) (hT : 0 < T) (m : ℕ) :
    ParabolicSpace g s p (m + 1) T →L[ℝ] ParabolicSpace g s p m T :=
  timeDerivExt hT (Nat.le_add_left 1 m) - (covOp X g s hp).heatExt hT (Nat.le_add_left 1 m)

theorem covAlongExt_ofSmooth (hp : 1 ≤ p) (hT : 0 < T) (m : ℕ) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) :
    covAlongExt X g s hp hT m (ofSmooth u hu) =
      ofSmooth (fun t => covAlong X g s (u t)) (jointlySmoothOn_covAlong X g s hu) := by
  change timeDerivExt hT (Nat.le_add_left 1 m) (ofSmooth u hu) -
    (covOp X g s hp).heatExt hT (Nat.le_add_left 1 m) (ofSmooth u hu) = _
  rw [timeDerivExt_ofSmooth, LinearOp.heatExt_ofSmooth, ← ofSmooth_sub]
  refine ofSmooth_congr hT _ _ fun t _ => ?_
  simp only [LinearOp.heatOp, covOp_apply]
  abel

theorem levelIncl_covAlongExt (hp : 1 ≤ p) (hT : 0 < T) (m : ℕ)
    (x : ParabolicSpace g s p (m + 2) T) :
    levelIncl g s p T m (m + 1) (covAlongExt X g s hp hT (m + 1) x) =
      covAlongExt X g s hp hT m (levelIncl g s p T (m + 1) (m + 2) x) := by
  have h : (levelIncl g s p T m (m + 1)).comp (covAlongExt X g s hp hT (m + 1)) =
      (covAlongExt X g s hp hT m).comp (levelIncl g s p T (m + 1) (m + 2)) :=
    clm_ext_ofSmooth fun u hu => by
      simp only [ContinuousLinearMap.comp_apply]
      rw [covAlongExt_ofSmooth, levelIncl_ofSmooth hT (Nat.le_succ m),
        levelIncl_ofSmooth hT (Nat.le_succ (m + 1)), covAlongExt_ofSmooth]
  exact DFunLike.congr_fun h x

/-! ### The derivative in `τ` for all data in `𝒫^{m+1}` -/

theorem hasDerivAt_hpullExt_levelIncl_ofSmooth (hp : 1 ≤ p) (hT : 0 < T) (m : ℕ)
    {u : ℝ → SmoothCcTensor g 0 s} (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (τ₀ : ℝ) :
    HasDerivAt (fun τ => hpullExt X g s p m T τ (levelIncl g s p T m (m + 1) (ofSmooth u hu)))
      (hpullExt X g s p m T τ₀ (covAlongExt X g s hp hT m (ofSmooth u hu))) τ₀ := by
  rw [levelIncl_ofSmooth hT (Nat.le_succ m), covAlongExt_ofSmooth]
  exact hasDerivAt_hpullExt_ofSmooth X g s hT hu τ₀

section Abstract

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G] {α : Type*}

/-- A Lipschitz bound `‖S h x - S 0 x‖ ≤ C₀ C_D |h| ‖x‖`, from the derivative on a dense set. -/
theorem norm_sub_le_of_denseRange {φ : α → F} (hφ : DenseRange φ) (S : ℝ → F →L[ℝ] G)
    (Tf : ℝ → G →L[ℝ] G) (D : F →L[ℝ] G) {C₀ CD : ℝ} (hC₀0 : 0 ≤ C₀)
    (hT : ∀ τ, |τ| ≤ 1 → ∀ y, ‖Tf τ y‖ ≤ C₀ * ‖y‖) (hD : ∀ x, ‖D x‖ ≤ CD * ‖x‖)
    (hsm : ∀ a τ, HasDerivAt (fun h => S h (φ a)) (Tf τ (D (φ a))) τ)
    (x : F) (h : ℝ) (hh : |h| ≤ 1) : ‖S h x - S 0 x‖ ≤ C₀ * CD * |h| * ‖x‖ := by
  have hcl : IsClosed {x : F | ‖S h x - S 0 x‖ ≤ C₀ * CD * |h| * ‖x‖} :=
    isClosed_le (((S h).continuous.sub (S 0).continuous).norm)
      (continuous_const.mul continuous_norm)
  refine hφ.induction_on x hcl fun a => ?_
  have hS : Convex ℝ (Icc (-1 : ℝ) 1) := convex_Icc _ _
  have h0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hh' : h ∈ Icc (-1 : ℝ) 1 := abs_le.mp hh
  have hmv := hS.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun τ => S τ (φ a)) (f' := fun τ => Tf τ (D (φ a))) (C := C₀ * (CD * ‖φ a‖))
    (fun τ _ => (hsm a τ).hasDerivWithinAt)
    (fun τ hτ => (hT τ (abs_le.mpr hτ) _).trans (mul_le_mul_of_nonneg_left (hD _) hC₀0)) h0 hh'
  simp only [sub_zero] at hmv
  refine hmv.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs]
  ring

theorem le_aux_angenent {C CD c K a b e : ℝ} (hC0 : 0 ≤ C) (hCD0 : 0 ≤ CD) (hc : 0 < c)
    (hK : K = C + CD + 1) (ha : 0 ≤ a) (he : 0 ≤ e) (he' : e ≤ c / (2 * K))
    (hb : b ≤ c / 2 * a) :
    C * a * e + b + a * (CD * e) ≤ c * a := by
  have hK0 : 0 < K := by rw [hK]; positivity
  have h1 : (C + CD) * e ≤ c / 2 := by
    have h2 : (C + CD) * e ≤ (C + CD) * (c / (2 * K)) :=
      mul_le_mul_of_nonneg_left he' (add_nonneg hC0 hCD0)
    have h3 : (C + CD) * (c / (2 * K)) ≤ c / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) two_pos, hK]
      nlinarith
    linarith
  nlinarith

/-- The derivative at `0` of `h ↦ S h x` for all `x`, from a dense set and a Lipschitz bound. -/
theorem hasDerivAt_zero_of_denseRange {φ : α → F} (hφ : DenseRange φ) (S : ℝ → F →L[ℝ] G)
    (D : F →L[ℝ] G) {C CD : ℝ} (hC0 : 0 ≤ C) (hCD0 : 0 ≤ CD)
    (hL : ∀ x h, |h| ≤ 1 → ‖S h x - S 0 x‖ ≤ C * |h| * ‖x‖) (hD : ∀ x, ‖D x‖ ≤ CD * ‖x‖)
    (hsm : ∀ a, HasDerivAt (fun h => S h (φ a)) (D (φ a)) 0) (x : F) :
    HasDerivAt (fun h => S h x) (D x) 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro c hc
  obtain ⟨K, hK⟩ : ∃ K, K = C + CD + 1 := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; positivity
  obtain ⟨a, ha⟩ := Metric.denseRange_iff.mp hφ x (c / (2 * K)) (by positivity)
  have hxu : ‖x - φ a‖ < c / (2 * K) := by rw [← dist_eq_norm]; exact ha
  have hsm' := hsm a
  rw [hasDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff] at hsm'
  filter_upwards [hsm' (half_pos hc), Metric.ball_mem_nhds (0 : ℝ) one_pos] with h hh1 hh2
  simp only [zero_add] at hh1 ⊢
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hh2
  have hsplit : S h x - S 0 x - h • D x =
      (S h (x - φ a) - S 0 (x - φ a)) + (S h (φ a) - S 0 (φ a) - h • D (φ a)) -
        h • D (x - φ a) := by
    simp only [map_sub, smul_sub]
    abel
  have e1 : ‖S h (x - φ a) - S 0 (x - φ a)‖ ≤ C * |h| * ‖x - φ a‖ := hL (x - φ a) h hh2.le
  have e2 : ‖h • D (x - φ a)‖ ≤ |h| * (CD * ‖x - φ a‖) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hD _) (abs_nonneg h)
  rw [hsplit, Real.norm_eq_abs]
  rw [Real.norm_eq_abs] at hh1
  have e3 := le_aux_angenent hC0 hCD0 hc hK (abs_nonneg h) (norm_nonneg _) hxu.le hh1
  calc ‖(S h (x - φ a) - S 0 (x - φ a)) + (S h (φ a) - S 0 (φ a) - h • D (φ a)) -
        h • D (x - φ a)‖
      ≤ ‖S h (x - φ a) - S 0 (x - φ a)‖ + ‖S h (φ a) - S 0 (φ a) - h • D (φ a)‖ +
        ‖h • D (x - φ a)‖ := (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ C * |h| * ‖x - φ a‖ + ‖S h (φ a) - S 0 (φ a) - h • D (φ a)‖ +
        |h| * (CD * ‖x - φ a‖) := add_le_add (add_le_add e1 le_rfl) e2
    _ ≤ c * |h| := e3

end Abstract

/-- **The derivative at `τ = 0`** for every `x ∈ 𝒫^{m+1}`: `d/dh|₀ Π_h x = ∇_X x` in `𝒫^m`. -/
theorem hasDerivAt_hpullExt_levelIncl_zero (hp : 1 ≤ p) (hT : 0 < T) (m : ℕ)
    (x : ParabolicSpace g s p (m + 1) T) :
    HasDerivAt (fun τ => hpullExt X g s p m T τ (levelIncl g s p T m (m + 1) x))
      (covAlongExt X g s hp hT m x) 0 := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_norm_hpullExt_le X g s (p := p) (m := m) hT 1
  obtain ⟨CD, hCD0, hCD⟩ := (covAlongExt X g s hp hT m).bound
  obtain ⟨S, hS⟩ : ∃ S : ℝ → ParabolicSpace g s p (m + 1) T →L[ℝ] ParabolicSpace g s p m T,
      S = fun h => (hpullExt X g s p m T h).comp (levelIncl g s p T m (m + 1)) := ⟨_, rfl⟩
  have hSa : ∀ h y, S h y = hpullExt X g s p m T h (levelIncl g s p T m (m + 1) y) := by
    intro h y; rw [hS]; rfl
  have hφ := UniformSpace.Completion.denseRange_coe (α := ParabolicPre g s p (m + 1) T)
  have hsm : ∀ (a : ParabolicPre g s p (m + 1) T) τ,
      HasDerivAt (fun h => S h (a : ParabolicSpace g s p (m + 1) T))
        (hpullExt X g s p m T τ (covAlongExt X g s hp hT m (a : ParabolicSpace g s p (m + 1) T)))
        τ := by
    intro a τ
    simp only [hSa]
    exact hasDerivAt_hpullExt_levelIncl_ofSmooth X g s hp hT m a.2 τ
  have hL := norm_sub_le_of_denseRange hφ S (fun τ => hpullExt X g s p m T τ)
    (covAlongExt X g s hp hT m) hC₀0 hC₀ hCD hsm
  have hsm0 : ∀ a : ParabolicPre g s p (m + 1) T,
      HasDerivAt (fun h => S h (a : ParabolicSpace g s p (m + 1) T))
        (covAlongExt X g s hp hT m (a : ParabolicSpace g s p (m + 1) T)) 0 := by
    intro a
    have h := hsm a 0
    rw [hpullExt_zero X g s hT, ContinuousLinearMap.id_apply] at h
    exact h
  have h := hasDerivAt_zero_of_denseRange hφ S (covAlongExt X g s hp hT m)
    (mul_nonneg hC₀0 hCD0.le) hCD0.le hL hCD hsm0 x
  simp only [hSa] at h
  exact h

/-- **The derivative in `τ`** for every `x ∈ 𝒫^{m+1}`: `d/dτ Π_τ x = Π_τ ∇_X x` in `𝒫^m`. -/
theorem hasDerivAt_hpullExt_levelIncl (hp : 1 ≤ p) (hT : 0 < T) (m : ℕ)
    (x : ParabolicSpace g s p (m + 1) T) (τ₀ : ℝ) :
    HasDerivAt (fun τ => hpullExt X g s p m T τ (levelIncl g s p T m (m + 1) x))
      (hpullExt X g s p m T τ₀ (covAlongExt X g s hp hT m x)) τ₀ := by
  have h0 := (hpullExt X g s p m T τ₀).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_hpullExt_levelIncl_zero X g s hp hT m x)
  have h2 : HasDerivAt (fun h => hpullExt X g s p m T (τ₀ + h) (levelIncl g s p T m (m + 1) x))
      (hpullExt X g s p m T τ₀ (covAlongExt X g s hp hT m x)) (τ₀ - τ₀) := by
    rw [sub_self]
    refine h0.congr_of_eventuallyEq (Eventually.of_forall fun h => ?_)
    simp only [Function.comp_apply]
    rw [← hpullExt_comp X g s hT τ₀ h, ContinuousLinearMap.comp_apply]
  refine (h2.comp_sub_const τ₀ τ₀).congr_of_eventuallyEq (Eventually.of_forall fun τ => ?_)
  simp only [add_sub_cancel]

/-! ### Smoothness for families of data -/

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [FiniteDimensional ℝ Λ]

/-- **Smooth dependence of `Π_τ R(λ)` on `(τ, λ)`** for families `R` that are `C^∞` into every
`𝒫^m`, compatibly with the level inclusions. -/
theorem contDiff_hpullExt_family_nat (hp : 1 ≤ p) (hT : 0 < T) (k : ℕ) :
    ∀ (R : (m : ℕ) → Λ → ParabolicSpace g s p m T),
      (∀ m l, R m l = levelIncl g s p T m (m + 1) (R (m + 1) l)) →
      (∀ m, ContDiff ℝ ∞ (R m)) →
      ∀ m, ContDiff ℝ k (fun q : ℝ × Λ => hpullExt X g s p m T q.1 (R m q.2)) := by
  induction k with
  | zero =>
    intro R _ hRs m
    rw [Nat.cast_zero, contDiff_zero]
    have hin : Continuous fun q : ℝ × Λ => (q.1, R m q.2) :=
      continuous_fst.prodMk ((hRs m).continuous.comp continuous_snd)
    have h := (continuous_hpullExt_uncurry g s p m X hT).comp hin
    simp only [Function.comp_def] at h
    exact h
  | succ k ih =>
    intro R hR hRs m
    have hdR : ∀ m, Differentiable ℝ (R m) := fun m => (hRs m).differentiable (by simp)
    have hcR : ∀ m, Continuous (fderiv ℝ (R m)) := fun m => (hRs m).continuous_fderiv (by simp)
    have hjc : Continuous fun q : ℝ × ParabolicSpace g s p m T => hpullExt X g s p m T q.1 q.2 :=
      continuous_hpullExt_uncurry g s p m X hT
    -- the partial derivatives
    obtain ⟨f₁, hf₁⟩ : ∃ f₁ : ℝ → Λ → ℝ →L[ℝ] ParabolicSpace g s p m T, f₁ = fun τ l =>
        ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
          (hpullExt X g s p m T τ (covAlongExt X g s hp hT m (R (m + 1) l))) := ⟨_, rfl⟩
    obtain ⟨f₂, hf₂⟩ : ∃ f₂ : ℝ → Λ → Λ →L[ℝ] ParabolicSpace g s p m T, f₂ = fun τ l =>
        (hpullExt X g s p m T τ).comp (fderiv ℝ (R m) l) := ⟨_, rfl⟩
    have hc₁ : Continuous fun q : ℝ × Λ => f₁ q.1 q.2 := by
      rw [continuous_clm_apply]
      intro y
      have hin : Continuous fun q : ℝ × Λ =>
          (q.1, covAlongExt X g s hp hT m (R (m + 1) q.2)) :=
        continuous_fst.prodMk (((covAlongExt X g s hp hT m).continuous.comp
          (hRs (m + 1)).continuous).comp continuous_snd)
      have h := hjc.comp hin
      simp only [Function.comp_def] at h
      simp only [hf₁, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply]
      exact (continuous_const : Continuous fun _ : ℝ × Λ => y).smul h
    have hc₂ : Continuous fun q : ℝ × Λ => f₂ q.1 q.2 := by
      rw [continuous_clm_apply]
      intro y
      have hin : Continuous fun q : ℝ × Λ => (q.1, fderiv ℝ (R m) q.2 y) :=
        continuous_fst.prodMk (((hcR m).clm_apply continuous_const).comp continuous_snd)
      have h := hjc.comp hin
      simp only [Function.comp_def] at h
      simp only [hf₂, ContinuousLinearMap.comp_apply]
      exact h
    have hstrict : ∀ q : ℝ × Λ, HasStrictFDerivAt
        (fun q : ℝ × Λ => hpullExt X g s p m T q.1 (R m q.2))
        ((f₁ q.1 q.2).coprod (f₂ q.1 q.2)) q := by
      intro q
      refine hasStrictFDerivAt_uncurry_coprod (f := fun τ l => hpullExt X g s p m T τ (R m l))
        (f₁ := f₁) (f₂ := f₂)
        (Eventually.of_forall fun v => ?_) (Eventually.of_forall fun v => ?_)
        hc₁.continuousAt hc₂.continuousAt
      · have h := (hasDerivAt_hpullExt_levelIncl X g s hp hT m (R (m + 1) v.2) v.1).hasFDerivAt
        rw [← hR m v.2] at h
        rw [hf₁]
        exact h
      · have h := (hpullExt X g s p m T v.1).hasFDerivAt.comp v.2 (hdR m v.2).hasFDerivAt
        rw [hf₂]
        exact h
    have hfd : fderiv ℝ (fun q : ℝ × Λ => hpullExt X g s p m T q.1 (R m q.2)) =
        fun q => (f₁ q.1 q.2).coprod (f₂ q.1 q.2) :=
      funext fun q => (hstrict q).hasFDerivAt.fderiv
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
    refine ⟨fun q => (hstrict q).hasFDerivAt.differentiableAt, fun h => absurd h (by simp), ?_⟩
    rw [hfd, contDiff_clm_apply_iff]
    rintro ⟨a, b⟩
    simp only [ContinuousLinearMap.coprod_apply, hf₁, hf₂, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply]
    refine ContDiff.add ?_ ?_
    · -- `∇_X R_{m+1}` is again a compatible family
      have h1 := ih (fun m l => covAlongExt X g s hp hT m (R (m + 1) l))
        (fun m l => by rw [levelIncl_covAlongExt, ← hR (m + 1) l])
        (fun m => (covAlongExt X g s hp hT m).contDiff.comp (hRs (m + 1))) m
      exact h1.const_smul a
    · -- the derivative `DR(λ) b` is again a compatible family
      have hDR : ∀ m l, fderiv ℝ (R m) l b =
          levelIncl g s p T m (m + 1) (fderiv ℝ (R (m + 1)) l b) := by
        intro m l
        have hfun : R m = fun l => levelIncl g s p T m (m + 1) (R (m + 1) l) := funext (hR m)
        have h := ((levelIncl g s p T m (m + 1)).hasFDerivAt.comp l
          (hdR (m + 1) l).hasFDerivAt).fderiv
        have hfun' : (⇑(levelIncl g s p T m (m + 1)) ∘ R (m + 1)) = R m := by
          rw [hfun]; rfl
        rw [hfun'] at h
        rw [h, ContinuousLinearMap.comp_apply]
      have hDRs : ∀ m, ContDiff ℝ ∞ (fun l => fderiv ℝ (R m) l b) := fun m =>
        ((contDiff_infty_iff_fderiv.mp (hRs m)).2).clm_apply contDiff_const
      exact ih (fun m l => fderiv ℝ (R m) l b) hDR hDRs m

theorem contDiff_hpullExt_family (hp : 1 ≤ p) (hT : 0 < T)
    (R : (m : ℕ) → Λ → ParabolicSpace g s p m T)
    (hR : ∀ m l, R m l = levelIncl g s p T m (m + 1) (R (m + 1) l))
    (hRs : ∀ m, ContDiff ℝ ∞ (R m)) (m : ℕ) :
    ContDiff ℝ ∞ (fun q : ℝ × Λ => hpullExt X g s p m T q.1 (R m q.2)) :=
  contDiff_infty.mpr fun k => contDiff_hpullExt_family_nat X g s hp hT k R hR hRs m

/-! ### The composite pullback of smooth data -/

/-- **`σ ↦ Π_σ u` is `C^∞` from `ℝⁿ` into `𝒫^m`** for every jointly smooth family `u`
(`lem:flows` (a), composite form). -/
theorem contDiff_iterPullExt_ofSmooth (hp : 1 ≤ p) (hT : 0 < T) {n : ℕ}
    (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (m : ℕ) :
    ContDiff ℝ ∞ (fun σ => iterPullExt g s p m T B σ (ofSmooth u hu)) := by
  induction n generalizing m with
  | zero => exact contDiff_const
  | succ n ih =>
    obtain ⟨R, hRdef⟩ : ∃ R : (m : ℕ) → (Fin n → ℝ) → ParabolicSpace g s p m T, R = fun m σ' =>
        iterPullExt g s p m T (fun i => B i.succ) σ' (ofSmooth u hu) := ⟨_, rfl⟩
    have hR : ∀ m l, R m l = levelIncl g s p T m (m + 1) (R (m + 1) l) := by
      intro m l
      rw [hRdef]
      simp only
      rw [iterPullExt_ofSmooth g s p m hT, iterPullExt_ofSmooth g s p (m + 1) hT,
        levelIncl_ofSmooth hT (Nat.le_succ m)]
    have hRs : ∀ m, ContDiff ℝ ∞ (R m) := fun m => by
      rw [hRdef]
      exact ih (fun i => B i.succ) m
    have h := contDiff_hpullExt_family (B 0) g s hp hT R hR hRs m
    have hψ : ContDiff ℝ ∞ (fun σ : Fin (n + 1) → ℝ => (σ 0, fun i : Fin n => σ i.succ)) :=
      (contDiff_apply ℝ ℝ (0 : Fin (n + 1))).prodMk
        (contDiff_pi.2 fun i => contDiff_apply ℝ ℝ i.succ)
    have hc := h.comp hψ
    simp only [Function.comp_def] at hc
    have e : (fun σ => iterPullExt g s p m T B σ (ofSmooth u hu)) =
        fun σ : Fin (n + 1) → ℝ => hpullExt (B 0) g s p m T (σ 0) (R m fun i => σ i.succ) := by
      funext σ
      rw [iterPullExt_succ_apply, hRdef]
    rw [e]
    exact hc

end HFlow

end ShortTime
