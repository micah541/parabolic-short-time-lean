import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.PerMode.Basic

/-!
# Scalar calculus on `[0,T]`

* `hasDerivWithinAt_Icc_of_interior`: a function continuous on `[0,T]` with a derivative on `(0,T)`
  that extends continuously to `[0,T]` has that derivative within `[0,T]` at every point.
* `contDiffOn_Icc_of_hasDerivWithinAt`: if `a' = d` on `[0,T]` and `d` is `C^n` there, `a` is
  `C^{n+1}`.
* `modeSol T μ c`: the solution of `a' = c - μ a`, `a(0) = 0` (the per-mode Duhamel integral), and
  its smoothness on `[0,T]` (`contDiffOn_modeSol`).
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace ShortTime

/-- A derivative on `(0,T)` with a continuous extension to `[0,T]` is a derivative within `[0,T]`. -/
theorem hasDerivWithinAt_Icc_of_interior {c d : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hc : ContinuousOn c (Icc 0 T)) (hd : ContinuousOn d (Icc 0 T))
    (h : ∀ t ∈ Ioo 0 T, HasDerivAt c (d t) t) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt c (d t) (Icc 0 T) t := by
  set d' : ℝ → ℝ := IccExtend hT.le ((Icc 0 T).domRestrict d) with hd'
  have hd'c : Continuous d' := hd.domRestrict.Icc_extend'
  have hd'eq : ∀ τ ∈ Icc 0 T, d' τ = d τ := fun τ hτ => by
    rw [hd', IccExtend_of_mem hT.le _ hτ]
    rfl
  have hFTC : ∀ τ ∈ Icc 0 T, c τ = c 0 + ∫ s in (0 : ℝ)..τ, d' s := by
    intro τ hτ
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hτ.1
      (hc.mono (Icc_subset_Icc le_rfl hτ.2))
      (fun s hs => by
        rw [hd'eq s ⟨hs.1.le, hs.2.le.trans hτ.2⟩]
        exact h s ⟨hs.1, hs.2.trans_le hτ.2⟩)
      (hd'c.intervalIntegrable 0 τ)]
    ring
  have hG : HasDerivAt (fun τ => c 0 + ∫ s in (0 : ℝ)..τ, d' s) (d' t) t :=
    (intervalIntegral.integral_hasDerivAt_right (hd'c.intervalIntegrable 0 t)
      hd'c.aestronglyMeasurable.stronglyMeasurableAtFilter hd'c.continuousAt).const_add (c 0)
  rw [← hd'eq t ht]
  exact hG.hasDerivWithinAt.congr (fun τ hτ => hFTC τ hτ) (hFTC t ht)

/-- If `a' = d` within `[0,T]` and `d` is `C^n` on `[0,T]`, then `a` is `C^{n+1}` there. -/
theorem contDiffOn_Icc_of_hasDerivWithinAt {a d : ℝ → ℝ} {T : ℝ} (hT : 0 < T) {n : ℕ}
    (hd : ContDiffOn ℝ n d (Icc 0 T))
    (h : ∀ t ∈ Icc 0 T, HasDerivWithinAt a (d t) (Icc 0 T) t) :
    ContDiffOn ℝ (n + 1 : ℕ) a (Icc 0 T) := by
  rw [Nat.cast_succ, contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hT)]
  refine ⟨fun t ht => (h t ht).differentiableWithinAt, fun hn => ?_, hd.congr fun t ht => ?_⟩
  · exact absurd hn (by simp)
  · exact (h t ht).derivWithin (uniqueDiffOn_Icc hT t ht)

/-- `C^∞` on `[0,T]` from derivatives: if `a' = d` within `[0,T]` and `d` is `C^n` whenever `a` is,
then `a` is `C^∞`. -/
theorem contDiffOn_Icc_infty_of_bootstrap {a d : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (h : ∀ t ∈ Icc 0 T, HasDerivWithinAt a (d t) (Icc 0 T) t)
    (hboot : ∀ n : ℕ, ContDiffOn ℝ n a (Icc 0 T) → ContDiffOn ℝ n d (Icc 0 T)) :
    ContDiffOn ℝ ∞ a (Icc 0 T) := by
  rw [contDiffOn_infty]
  intro n
  induction n with
  | zero =>
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun t ht => (h t ht).continuousWithinAt
  | succ n ih => exact contDiffOn_Icc_of_hasDerivWithinAt hT (hboot n ih) h

/-- Clamp to `[0,T]`. -/
def clampIcc (T t : ℝ) : ℝ := max 0 (min t T)

theorem continuous_clampIcc (T : ℝ) : Continuous (clampIcc T) :=
  continuous_const.max (continuous_id.min continuous_const)

theorem clampIcc_mem {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : clampIcc T t ∈ Icc 0 T :=
  ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩

theorem clampIcc_of_mem {T t : ℝ} (ht : t ∈ Icc 0 T) : clampIcc T t = t := by
  rw [clampIcc, min_eq_left ht.2, max_eq_right ht.1]

/-- The solution of `a' = c - μ a`, `a(0) = 0` on `[0,T]` (Duhamel's formula). -/
def modeSol (T μ : ℝ) (c : ℝ → ℝ) : ℝ → ℝ :=
  DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.perModeConvolution μ
    (fun s => c (clampIcc T s))

theorem modeSol_zero (T μ : ℝ) (c : ℝ → ℝ) : modeSol T μ c 0 = 0 :=
  DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.perModeConvolution_zero_left _ _

theorem hasDerivWithinAt_modeSol {T μ : ℝ} {c : ℝ → ℝ} (hT : 0 < T) (hc : ContinuousOn c (Icc 0 T))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (modeSol T μ c) (c t - μ * modeSol T μ c t) (Icc 0 T) t := by
  have hcc : Continuous fun s => c (clampIcc T s) :=
    hc.comp_continuous (continuous_clampIcc T) (clampIcc_mem hT.le)
  have h := DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.perModeConvolution_hasDerivWithinAt
    μ hcc T t
  rw [clampIcc_of_mem ht] at h
  exact h

theorem contDiffOn_modeSol {T μ : ℝ} {c : ℝ → ℝ} (hT : 0 < T) (hc : ContDiffOn ℝ ∞ c (Icc 0 T)) :
    ContDiffOn ℝ ∞ (modeSol T μ c) (Icc 0 T) :=
  contDiffOn_Icc_infty_of_bootstrap hT
    (fun t ht => hasDerivWithinAt_modeSol hT hc.continuousOn ht)
    (fun n ha => (hc.of_le (by exact_mod_cast le_top)).sub (contDiffOn_const.mul ha))

/-! ### A one-dimensional Sobolev inequality -/

/-- If `|φ'| ≤ b` on `[0,T]`, then `|φ(t) - φ(s)| ≤ ∫₀ᵀ b`. -/
theorem abs_sub_le_integral_of_deriv {φ d b : ℝ → ℝ} {T : ℝ} (hφ : ContinuousOn φ (Icc 0 T))
    (hd : ContinuousOn d (Icc 0 T)) (hb : ContinuousOn b (Icc 0 T))
    (hder : ∀ t ∈ Ioo 0 T, HasDerivAt φ (d t) t) (hdb : ∀ t ∈ Icc 0 T, |d t| ≤ b t)
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
    |φ t - φ s| ≤ ∫ τ in (0 : ℝ)..T, b τ := by
  have hT : 0 ≤ T := hs.1.trans hs.2
  have key : ∀ a c, a ∈ Icc 0 T → c ∈ Icc 0 T → a ≤ c → |φ c - φ a| ≤ ∫ τ in (0 : ℝ)..T, b τ := by
    intro a c ha hc hac
    have hsub : Icc a c ⊆ Icc 0 T := Icc_subset_Icc ha.1 hc.2
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hac (hφ.mono hsub)
      (fun x hx => hder x ⟨ha.1.trans_lt hx.1, hx.2.trans_le hc.2⟩)
      ((hd.mono hsub).intervalIntegrable_of_Icc hac)]
    refine (intervalIntegral.abs_integral_le_integral_abs hac).trans ?_
    refine (intervalIntegral.integral_mono_on hac ((hd.mono hsub).abs.intervalIntegrable_of_Icc hac)
      ((hb.mono hsub).intervalIntegrable_of_Icc hac) fun x hx => hdb x (hsub hx)).trans ?_
    refine intervalIntegral.integral_mono_interval ha.1 hac hc.2 ?_ (hb.intervalIntegrable_of_Icc hT)
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx => ?_)
    exact (abs_nonneg _).trans (hdb x ⟨hx.1.le, hx.2⟩)
  rcases le_total s t with hst | hts
  · exact key s t hs ht hst
  · rw [abs_sub_comm]
    exact key t s ht hs hts

/-- If `φ(t) ≤ φ(s) + B` for all `s, t ∈ [0,T]`, then `φ(t) ≤ T⁻¹ ∫₀ᵀ φ + B`. -/
theorem le_average_add {φ : ℝ → ℝ} {T B : ℝ} (hT : 0 < T) (hφ : ContinuousOn φ (Icc 0 T))
    (h : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, φ t ≤ φ s + B) {t : ℝ} (ht : t ∈ Icc 0 T) :
    φ t ≤ T⁻¹ * (∫ τ in (0 : ℝ)..T, φ τ) + B := by
  have hint : T * φ t ≤ (∫ τ in (0 : ℝ)..T, φ τ) + T * B := by
    have hc1 : IntervalIntegrable (fun _ : ℝ => φ t) volume 0 T := intervalIntegrable_const
    have hc2 : IntervalIntegrable (fun _ : ℝ => B) volume 0 T := intervalIntegrable_const
    have h1 := intervalIntegral.integral_mono_on hT.le hc1
      ((hφ.intervalIntegrable_of_Icc hT.le).add hc2) fun s hs => h s hs t ht
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h1
    rw [intervalIntegral.integral_add (hφ.intervalIntegrable_of_Icc hT.le) hc2,
      intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h1
    linarith
  have hTi : 0 < T⁻¹ := inv_pos.mpr hT
  calc φ t = T⁻¹ * (T * φ t) := by field_simp
    _ ≤ T⁻¹ * ((∫ τ in (0 : ℝ)..T, φ τ) + T * B) := mul_le_mul_of_nonneg_left hint hTi.le
    _ = T⁻¹ * (∫ τ in (0 : ℝ)..T, φ τ) + B := by field_simp

end ShortTime
