import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.TangentCone.Prod

/-!
# Smooth dependence of `∫₀¹ f(q, σ) dσ` on a parameter in a convex set

If `f` is smooth on `U × [0, 1]`, with `U` convex and uniquely differentiable (for example a ball
times a closed interval), then `q ↦ ∫₀¹ f(q, σ) dσ` is smooth on `U`, and its derivative is the
integral of the partial derivative (`contDiffOn_integral_Icc`).

Mathlib differentiates under the integral sign at interior points. The point here is that `U` may
contain boundary points, such as the initial time `t = 0` of an evolution equation; there all
derivatives are one-sided (`fderivWithin`).
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set Filter Topology Metric
open scoped ContDiff

namespace ShortTime

universe u

variable {P : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Uniform continuity in `σ ∈ [0, 1]`: if `g` is continuous on `U × [0, 1]`, then `g(q, σ)` is
close to `g(q₀, σ)` for all `σ`, once `q ∈ U` is close to `q₀`. -/
theorem eventually_forall_Icc_norm_sub_le {G : Type*} [NormedAddCommGroup G] {U : Set P}
    {g : P × ℝ → G} (hg : ContinuousOn g (U ×ˢ Icc (0 : ℝ) 1)) {q₀ : P} (hq₀ : q₀ ∈ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q in 𝓝 q₀, ∀ σ ∈ Icc (0 : ℝ) 1, q ∈ U → ‖g (q, σ) - g (q₀, σ)‖ ≤ ε := by
  have key := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).eventually_forall_of_forall_eventually
    (P := fun q σ => σ ∈ Icc (0 : ℝ) 1 → q ∈ U → ‖g (q, σ) - g (q₀, σ)‖ ≤ ε) (x₀ := q₀) ?_
  · exact key.mono fun q hq σ hσ => hq σ hσ hσ
  intro y hy
  have hc := hg (q₀, y) ⟨hq₀, hy⟩
  have h1 : ∀ᶠ z in 𝓝 (q₀, y), z ∈ U ×ˢ Icc (0 : ℝ) 1 → ‖g z - g (q₀, y)‖ < ε / 2 := by
    obtain ⟨δ, hδ, hδ'⟩ := Metric.tendsto_nhdsWithin_nhds.mp hc (ε / 2) (half_pos hε)
    filter_upwards [Metric.ball_mem_nhds (q₀, y) hδ] with z hz hzU
    have := hδ' hzU hz
    rwa [dist_eq_norm] at this
  have h2 : ∀ᶠ z in 𝓝 (q₀, y), ((q₀, z.2) : P × ℝ) ∈ U ×ˢ Icc (0 : ℝ) 1 →
      ‖g (q₀, z.2) - g (q₀, y)‖ < ε / 2 := by
    have hcont : ContinuousAt (fun z : P × ℝ => ((q₀, z.2) : P × ℝ)) (q₀, y) :=
      (continuous_const.prodMk continuous_snd).continuousAt
    exact hcont.eventually h1
  filter_upwards [h2, h1] with z hz2 hz1 hσ hq
  have a := hz1 ⟨hq, hσ⟩
  have b := hz2 ⟨hq₀, hσ⟩
  calc ‖g (z.1, z.2) - g (q₀, z.2)‖ = ‖(g z - g (q₀, y)) - (g (q₀, z.2) - g (q₀, y))‖ := by
        congr 1
        abel
    _ ≤ ‖g z - g (q₀, y)‖ + ‖g (q₀, z.2) - g (q₀, y)‖ := norm_sub_le _ _
    _ ≤ ε := by linarith

section Integral

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Differentiation under `∫₀¹`, one-sided.** -/
theorem hasFDerivWithinAt_integral_Icc {U : Set P} (hU : Convex ℝ U) {f : P → ℝ → F}
    {f' : P → ℝ → P →L[ℝ] F}
    (hd : ∀ q ∈ U, ∀ σ ∈ Icc (0 : ℝ) 1, HasFDerivWithinAt (fun q => f q σ) (f' q σ) U q)
    (hf : ContinuousOn (fun z : P × ℝ => f z.1 z.2) (U ×ˢ Icc (0 : ℝ) 1))
    (hf' : ContinuousOn (fun z : P × ℝ => f' z.1 z.2) (U ×ˢ Icc (0 : ℝ) 1))
    {q₀ : P} (hq₀ : q₀ ∈ U) :
    HasFDerivWithinAt (fun q => ∫ σ in (0 : ℝ)..1, f q σ) (∫ σ in (0 : ℝ)..1, f' q₀ σ) U q₀ := by
  have hint : ∀ q ∈ U, IntervalIntegrable (fun σ => f q σ) MeasureTheory.volume 0 1 := by
    intro q hq
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact hf.comp (continuousOn_const.prodMk continuousOn_id) fun σ hσ => ⟨hq, hσ⟩
  have hf'q₀ : ContinuousOn (fun σ => f' q₀ σ) (Icc (0 : ℝ) 1) :=
    hf'.comp (continuousOn_const.prodMk continuousOn_id) fun σ hσ => ⟨hq₀, hσ⟩
  have hint' : IntervalIntegrable (fun σ => f' q₀ σ) MeasureTheory.volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact hf'q₀
  rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  -- a ball around `q₀` on which the partial derivative is `ε`-close to its value at `q₀`
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (eventually_forall_Icc_norm_sub_le hf' hq₀ hε)
  have hconv : Convex ℝ (U ∩ ball q₀ δ) := hU.inter (convex_ball q₀ δ)
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds q₀ hδ] with q hqb hqU
  have hq : q ∈ U ∩ ball q₀ δ := ⟨hqU, hqb⟩
  -- the pointwise estimate, from the mean value inequality
  have hpt : ∀ σ ∈ Icc (0 : ℝ) 1, ‖f q σ - f q₀ σ - f' q₀ σ (q - q₀)‖ ≤ ε * ‖q - q₀‖ := by
    intro σ hσ
    have hmv := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun q => f q σ - f' q₀ σ q) (f' := fun q => f' q σ - f' q₀ σ) (C := ε)
      (fun q hq => ((hd q hq.1 σ hσ).mono inter_subset_left).sub (f' q₀ σ).hasFDerivWithinAt)
      (fun q hq => hball q hq.2 σ hσ hq.1) ⟨hq₀, mem_ball_self hδ⟩ hq
    calc ‖f q σ - f q₀ σ - f' q₀ σ (q - q₀)‖
        = ‖(f q σ - f' q₀ σ q) - (f q₀ σ - f' q₀ σ q₀)‖ := by
          rw [map_sub]
          congr 1
          abel
      _ ≤ ε * ‖q - q₀‖ := hmv
  -- integrate
  have hint'h : IntervalIntegrable (fun σ => f' q₀ σ (q - q₀)) MeasureTheory.volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact hf'q₀.clm_apply continuousOn_const
  have hsplit : (∫ σ in (0 : ℝ)..1, f q σ) - (∫ σ in (0 : ℝ)..1, f q₀ σ) -
      (∫ σ in (0 : ℝ)..1, f' q₀ σ) (q - q₀) =
      ∫ σ in (0 : ℝ)..1, (f q σ - f q₀ σ - f' q₀ σ (q - q₀)) := by
    rw [ContinuousLinearMap.intervalIntegral_apply hint' (q - q₀),
      ← intervalIntegral.integral_sub (hint _ hqU) (hint _ hq₀),
      ← intervalIntegral.integral_sub ((hint _ hqU).sub (hint _ hq₀)) hint'h]
  rw [hsplit]
  calc ‖∫ σ in (0 : ℝ)..1, (f q σ - f q₀ σ - f' q₀ σ (q - q₀))‖ ≤ ε * ‖q - q₀‖ * |1 - 0| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun σ hσ => hpt σ ?_
        rw [uIoc_of_le zero_le_one] at hσ
        exact Ioc_subset_Icc_self hσ
    _ = ε * ‖q - q₀‖ := by simp

/-- The partial derivative of `f` in the parameter, taken within `U × [0, 1]`. -/
def partialFst (U : Set P) (f : P → ℝ → F) (q : P) (σ : ℝ) : P →L[ℝ] F :=
  (fderivWithin ℝ (fun z : P × ℝ => f z.1 z.2) (U ×ˢ Icc (0 : ℝ) 1) (q, σ)).comp
    (ContinuousLinearMap.inl ℝ P ℝ)

theorem contDiffOn_partialFst {U : Set P} (hUD : UniqueDiffOn ℝ U) {f : P → ℝ → F}
    (hf : ContDiffOn ℝ ∞ (fun z : P × ℝ => f z.1 z.2) (U ×ˢ Icc (0 : ℝ) 1)) :
    ContDiffOn ℝ ∞ (fun z : P × ℝ => partialFst U f z.1 z.2) (U ×ˢ Icc (0 : ℝ) 1) :=
  (hf.fderivWithin (UniqueDiffOn.prod hUD (uniqueDiffOn_Icc zero_lt_one)) (by simp)).clm_comp
    contDiffOn_const

theorem hasFDerivWithinAt_partialFst {U : Set P} {f : P → ℝ → F}
    (hf : ContDiffOn ℝ ∞ (fun z : P × ℝ => f z.1 z.2) (U ×ˢ Icc (0 : ℝ) 1))
    {q : P} (hq : q ∈ U) {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) :
    HasFDerivWithinAt (fun q => f q σ) (partialFst U f q σ) U q := by
  have hdiff : DifferentiableWithinAt ℝ (fun z : P × ℝ => f z.1 z.2) (U ×ˢ Icc (0 : ℝ) 1) (q, σ) :=
    hf.differentiableOn (by simp) (q, σ) ⟨hq, hσ⟩
  exact HasFDerivWithinAt.comp (f := fun e : P => ((e, σ) : P × ℝ)) q hdiff.hasFDerivWithinAt
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) q σ).hasFDerivWithinAt fun q' hq' => ⟨hq', hσ⟩

end Integral

/-- **Smoothness of `∫₀¹ f(q, σ) dσ` on a convex set**, to every finite order. -/
theorem contDiffOn_integral_Icc_nat {U : Set P} (hU : Convex ℝ U) (hUD : UniqueDiffOn ℝ U) :
    ∀ (n : ℕ) (F : Type u) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (f : P → ℝ → F), ContDiffOn ℝ ∞ (fun z : P × ℝ => f z.1 z.2) (U ×ˢ Icc (0 : ℝ) 1) →
      ContDiffOn ℝ n (fun q => ∫ σ in (0 : ℝ)..1, f q σ) U := by
  have hderiv : ∀ (F : Type u) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (f : P → ℝ → F), ContDiffOn ℝ ∞ (fun z : P × ℝ => f z.1 z.2) (U ×ˢ Icc (0 : ℝ) 1) →
      ∀ q ∈ U, HasFDerivWithinAt (fun q => ∫ σ in (0 : ℝ)..1, f q σ)
        (∫ σ in (0 : ℝ)..1, partialFst U f q σ) U q := by
    intro F _ _ _ f hf q hq
    exact hasFDerivWithinAt_integral_Icc hU
      (fun q hq σ hσ => hasFDerivWithinAt_partialFst hf hq hσ) hf.continuousOn
      (contDiffOn_partialFst hUD hf).continuousOn hq
  intro n
  induction n with
  | zero =>
    intro F _ _ _ f hf
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun q hq => (hderiv F f hf q hq).continuousWithinAt
  | succ n ih =>
    intro F _ _ _ f hf
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderivWithin hUD]
    refine ⟨fun q hq => (hderiv F f hf q hq).differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    have heq : EqOn (fderivWithin ℝ (fun q => ∫ σ in (0 : ℝ)..1, f q σ) U)
        (fun q => ∫ σ in (0 : ℝ)..1, partialFst U f q σ) U :=
      fun q hq => (hderiv F f hf q hq).fderivWithin (hUD q hq)
    exact (ih (P →L[ℝ] F) (partialFst U f) (contDiffOn_partialFst hUD hf)).congr heq

/-- **Smoothness of `∫₀¹ f(q, σ) dσ` on a convex set.** -/
theorem contDiffOn_integral_Icc {U : Set P} (hU : Convex ℝ U) (hUD : UniqueDiffOn ℝ U)
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {f : P → ℝ → F}
    (hf : ContDiffOn ℝ ∞ (fun z : P × ℝ => f z.1 z.2) (U ×ˢ Icc (0 : ℝ) 1)) :
    ContDiffOn ℝ ∞ (fun q => ∫ σ in (0 : ℝ)..1, f q σ) U :=
  contDiffOn_infty.mpr fun n => contDiffOn_integral_Icc_nat hU hUD n F f hf

end ShortTime
