import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# A Grönwall-type inequality for energy estimates

If `e(0) = 0`, `e ≥ 0` and `e' + a N ≤ b e + c F` on `(0, T)` with `N, F ≥ 0`, then
`sup_{[0,T]} e ≤ c e^{bT} ∫₀ᵀ F` and `a ∫₀ᵀ N ≤ c (1 + bT e^{bT}) ∫₀ᵀ F` (`energy_ode`).

This is the form in which Grönwall's inequality enters the energy estimates (`prop:energy`).
-/

noncomputable section

open Set Filter Topology Real MeasureTheory

namespace ShortTime

theorem hasDerivAt_primitive {G : ℝ → ℝ} {T : ℝ} (hG : ContinuousOn G (Icc 0 T)) {t : ℝ}
    (ht : t ∈ Ioo 0 T) : HasDerivAt (fun x => ∫ τ in (0 : ℝ)..x, G τ) (G t) t :=
  intervalIntegral.integral_hasDerivAt_right
    ((hG.mono (by rw [uIcc_of_le ht.1.le]; exact Icc_subset_Icc_right ht.2.le)).intervalIntegrable)
    ((hG.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht)
    (hG.continuousAt (Icc_mem_nhds ht.1 ht.2))

theorem continuousOn_primitive {G : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (hG : ContinuousOn G (Icc 0 T)) :
    ContinuousOn (fun x => ∫ τ in (0 : ℝ)..x, G τ) (Icc 0 T) := by
  have h := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := T)
    (f := G) (by rw [uIcc_of_le hT]; exact hG.integrableOn_Icc)
  rwa [uIcc_of_le hT] at h

/-- A function with nonpositive derivative on `(0,T)`, continuous on `[0,T]`, is antitone there. -/
theorem le_of_deriv_nonpos {ψ ψ' : ℝ → ℝ} {T : ℝ} (hc : ContinuousOn ψ (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt ψ (ψ' t) t) (hle : ∀ t ∈ Ioo 0 T, ψ' t ≤ 0) :
    ∀ t ∈ Icc 0 T, ψ t ≤ ψ 0 := by
  intro t ht
  have hanti : AntitoneOn ψ (Icc 0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hc ?_ ?_
    · rw [interior_Icc]
      exact fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      rw [(hd x hx).deriv]
      exact hle x hx
  exact hanti ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1

/-- **Grönwall's inequality, in the form used by the energy estimates.** -/
theorem energy_ode {T a b c : ℝ} (hT : 0 ≤ T) (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    {e e' N F : ℝ → ℝ} (he : ContinuousOn e (Icc 0 T)) (hN : ContinuousOn N (Icc 0 T))
    (hF : ContinuousOn F (Icc 0 T)) (he0 : e 0 = 0) (hen : ∀ t ∈ Icc 0 T, 0 ≤ e t) (hNnn : ∀ t ∈ Icc 0 T, 0 ≤ N t)
    (hFnn : ∀ t ∈ Icc 0 T, 0 ≤ F t)
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt e (e' t) t)
    (hineq : ∀ t ∈ Ioo 0 T, e' t + a * N t ≤ b * e t + c * F t) :
    (∀ t ∈ Icc 0 T, e t ≤ c * exp (b * T) * ∫ τ in (0 : ℝ)..T, F τ) ∧
      a * ∫ τ in (0 : ℝ)..T, N τ ≤ c * (1 + b * T * exp (b * T)) * ∫ τ in (0 : ℝ)..T, F τ := by
  have hIF : 0 ≤ ∫ τ in (0 : ℝ)..T, F τ :=
    intervalIntegral.integral_nonneg hT fun τ hτ => hFnn τ hτ
  -- part 1: `e^{-bt} e(t) - c ∫₀ᵗ e^{-bτ} F` is antitone
  have hexpF : ContinuousOn (fun τ => exp (-b * τ) * F τ) (Icc 0 T) :=
    (continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hF
  have hsup : ∀ t ∈ Icc 0 T, e t ≤ c * exp (b * T) * ∫ τ in (0 : ℝ)..T, F τ := by
    have hφ := le_of_deriv_nonpos (T := T)
      (ψ := fun t => exp (-b * t) * e t - c * ∫ τ in (0 : ℝ)..t, exp (-b * τ) * F τ)
      (ψ' := fun t => exp (-b * t) * (e' t - b * e t - c * F t))
      (((continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul he).sub
        (continuousOn_const.mul (continuousOn_primitive hT hexpF)))
      (fun t ht => by
        have h0 : HasDerivAt (fun x => exp (-b * x)) (exp (-b * t) * (-b)) t :=
          (((hasDerivAt_id t).const_mul (-b)).exp).congr_deriv (by simp)
        exact ((h0.mul (hd t ht)).sub ((hasDerivAt_primitive hexpF ht).const_mul c)).congr_deriv
          (by ring))
      (fun t ht => by
        have h := hineq t ht
        have hN0 := hNnn t (Ioo_subset_Icc_self ht)
        have : e' t - b * e t - c * F t ≤ 0 := by nlinarith
        exact mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le this)
    intro t ht
    have h := hφ t ht
    simp only [mul_zero, neg_zero, exp_zero, one_mul, he0, intervalIntegral.integral_same,
      sub_zero] at h
    -- `∫₀ᵗ e^{-bτ} F ≤ ∫₀ᵀ F`
    have hsubt : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
    have hint : ∫ τ in (0 : ℝ)..t, exp (-b * τ) * F τ ≤ ∫ τ in (0 : ℝ)..T, F τ := by
      calc ∫ τ in (0 : ℝ)..t, exp (-b * τ) * F τ ≤ ∫ τ in (0 : ℝ)..t, F τ := by
            refine intervalIntegral.integral_mono_on ht.1
              ((hexpF.mono hsubt).intervalIntegrable_of_Icc ht.1)
              ((hF.mono hsubt).intervalIntegrable_of_Icc ht.1) fun x hx => ?_
            have hx1 : exp (-b * x) ≤ 1 := exp_le_one_iff.mpr (by nlinarith [hx.1])
            have := hFnn x (hsubt hx)
            nlinarith
        _ ≤ ∫ τ in (0 : ℝ)..T, F τ :=
            intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
              (ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => hFnn x (Ioc_subset_Icc_self hx))
              (hF.intervalIntegrable_of_Icc hT)
    have hint0 : 0 ≤ ∫ τ in (0 : ℝ)..t, exp (-b * τ) * F τ :=
      intervalIntegral.integral_nonneg ht.1 fun x hx =>
        mul_nonneg (exp_pos _).le (hFnn x (hsubt hx))
    have hexp : exp (b * t) ≤ exp (b * T) := exp_le_exp.mpr (by nlinarith [ht.1, ht.2])
    have hmul : e t ≤ exp (b * t) * (c * ∫ τ in (0 : ℝ)..t, exp (-b * τ) * F τ) := by
      have h' : exp (-b * t) * e t ≤ c * ∫ τ in (0 : ℝ)..t, exp (-b * τ) * F τ := by linarith
      have := mul_le_mul_of_nonneg_left h' (exp_pos (b * t)).le
      rwa [← mul_assoc, ← exp_add, show b * t + -b * t = 0 by ring, exp_zero, one_mul] at this
    calc e t ≤ exp (b * t) * (c * ∫ τ in (0 : ℝ)..t, exp (-b * τ) * F τ) := hmul
      _ ≤ exp (b * T) * (c * ∫ τ in (0 : ℝ)..T, F τ) :=
          mul_le_mul hexp (mul_le_mul_of_nonneg_left hint hc) (mul_nonneg hc hint0) (exp_pos _).le
      _ = c * exp (b * T) * ∫ τ in (0 : ℝ)..T, F τ := by ring
  refine ⟨hsup, ?_⟩
  -- part 2: `e + a ∫₀ᵗ N - b ∫₀ᵗ e - c ∫₀ᵗ F` is antitone
  have hψ := le_of_deriv_nonpos (T := T)
    (ψ := fun t => e t + a * (∫ τ in (0 : ℝ)..t, N τ) - b * (∫ τ in (0 : ℝ)..t, e τ) -
      c * ∫ τ in (0 : ℝ)..t, F τ)
    (ψ' := fun t => e' t + a * N t - b * e t - c * F t)
    (((he.add (continuousOn_const.mul (continuousOn_primitive hT hN))).sub
      (continuousOn_const.mul (continuousOn_primitive hT he))).sub
      (continuousOn_const.mul (continuousOn_primitive hT hF)))
    (fun t ht => (((hd t ht).add ((hasDerivAt_primitive hN ht).const_mul a)).sub
      ((hasDerivAt_primitive he ht).const_mul b)).sub ((hasDerivAt_primitive hF ht).const_mul c))
    (fun t ht => by have := hineq t ht; linarith)
  have hT' := hψ T ⟨hT, le_rfl⟩
  simp only [he0, intervalIntegral.integral_same, mul_zero, sub_zero, add_zero] at hT'
  have heT := hsup T ⟨hT, le_rfl⟩
  have heT0 : 0 ≤ e T := hen T ⟨hT, le_rfl⟩
  have hie : ∫ τ in (0 : ℝ)..T, e τ ≤ T * (c * exp (b * T) * ∫ τ in (0 : ℝ)..T, F τ) := by
    have h := intervalIntegral.integral_mono_on hT (he.intervalIntegrable_of_Icc hT)
      (intervalIntegrable_const (μ := volume) (c := c * exp (b * T) * ∫ τ in (0 : ℝ)..T, F τ))
      fun x hx => hsup x hx
    rwa [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
  nlinarith [mul_le_mul_of_nonneg_left hie hb, exp_pos (b * T)]

end ShortTime
