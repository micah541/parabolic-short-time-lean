import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Smoothness of uniform limits on convex sets

Mathlib proves that uniform limits with uniformly converging derivatives are differentiable on open
sets. For the regularity of parabolic solutions we need the same on sets such as `U × [0,T]`, with
derivatives taken *within* the set.

* `hasFDerivWithinAt_of_tendstoUniformlyOn_convex`: on a convex set, if `fₘ → g` pointwise and
  `Dfₘ → g'` uniformly with `g'` continuous, then `Dg = g'` within the set.
* `contDiffOn_of_tendstoUniformlyOn_iteratedFDerivWithin`: if moreover every iterated derivative
  converges uniformly, the limit is `C^∞` on the set, with the limits as its iterated derivatives.
-/

open Set Filter Topology Asymptotics
open scoped ContDiff

namespace ShortTime

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **Derivative of a uniform limit, within a convex set.** -/
theorem hasFDerivWithinAt_of_tendstoUniformlyOn_convex {s : Set E} (hs : Convex ℝ s)
    {f : ℕ → E → F} {f' : ℕ → E → E →L[ℝ] F} {g : E → F} {g' : E → E →L[ℝ] F}
    (hf : ∀ m, ∀ x ∈ s, HasFDerivWithinAt (f m) (f' m x) s x)
    (hlim : ∀ x ∈ s, Tendsto (fun m => f m x) atTop (𝓝 (g x)))
    (hunif : TendstoUniformlyOn f' g' atTop s) (hcont : ContinuousOn g' s) {x : E} (hx : x ∈ s) :
    HasFDerivWithinAt g (g' x) s x := by
  refine HasFDerivWithinAt.of_isLittleO (IsLittleO.of_bound fun c hc => ?_)
  obtain ⟨δ, hδ, hcδ⟩ := Metric.continuousWithinAt_iff.mp (hcont x hx) (c / 2) (by positivity)
  filter_upwards [inter_mem_nhdsWithin s (Metric.ball_mem_nhds x hδ)] with y hy
  have hs' : Convex ℝ (s ∩ Metric.ball x δ) := hs.inter (convex_ball x δ)
  have hxs' : x ∈ s ∩ Metric.ball x δ := ⟨hx, Metric.mem_ball_self hδ⟩
  have hev : ∀ᶠ m in atTop, ‖f m y - f m x - g' x (y - x)‖ ≤ c * ‖y - x‖ := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hunif (c / 2) (by positivity)] with m hm
    have hder : ∀ z ∈ s ∩ Metric.ball x δ,
        HasFDerivWithinAt (fun z => f m z - g' x z) (f' m z - g' x) (s ∩ Metric.ball x δ) z :=
      fun z hz => ((hf m z hz.1).mono inter_subset_left).sub (g' x).hasFDerivWithinAt
    have hbound : ∀ z ∈ s ∩ Metric.ball x δ, ‖f' m z - g' x‖ ≤ c := by
      intro z hz
      have h1 : ‖f' m z - g' z‖ < c / 2 := by
        rw [← dist_eq_norm, dist_comm]
        exact hm z hz.1
      have h2 : ‖g' z - g' x‖ < c / 2 := by
        rw [← dist_eq_norm]
        exact hcδ hz.1 hz.2
      calc ‖f' m z - g' x‖ = ‖(f' m z - g' z) + (g' z - g' x)‖ := by abel_nf
        _ ≤ ‖f' m z - g' z‖ + ‖g' z - g' x‖ := norm_add_le _ _
        _ ≤ c := by linarith
    have h := hs'.norm_image_sub_le_of_norm_hasFDerivWithin_le hder hbound hxs' hy
    calc ‖f m y - f m x - g' x (y - x)‖ = ‖f m y - g' x y - (f m x - g' x x)‖ := by
          congr 1; rw [map_sub]; abel
      _ ≤ c * ‖y - x‖ := h
  have hconv : Tendsto (fun m => ‖f m y - f m x - g' x (y - x)‖) atTop
      (𝓝 ‖g y - g x - g' x (y - x)‖) :=
    (((hlim y hy.1).sub (hlim x hx)).sub tendsto_const_nhds).norm
  exact le_of_tendsto hconv hev

/-- **Smoothness of a uniform limit, within a convex set**: if every iterated derivative of `fₘ`
converges uniformly on `s`, then the pointwise limit `g` is `C^∞` on `s`, and its iterated derivatives
are the limits. -/
theorem contDiffOn_of_tendstoUniformlyOn_iteratedFDerivWithin {s : Set E} (hs : Convex ℝ s)
    (hs' : UniqueDiffOn ℝ s) {f : ℕ → E → F} {g : E → F} (hf : ∀ m, ContDiffOn ℝ ∞ (f m) s)
    (hlim : ∀ x ∈ s, Tendsto (fun m => f m x) atTop (𝓝 (g x)))
    (G : (n : ℕ) → E → ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F)
    (hG : ∀ n, TendstoUniformlyOn (fun m => iteratedFDerivWithin ℝ n (f m) s) (G n) atTop s) :
    ContDiffOn ℝ ∞ g s ∧ ∀ n, ∀ x ∈ s, iteratedFDerivWithin ℝ n g s x = G n x := by
  have hp : ∀ m, HasFTaylorSeriesUpToOn ∞ (f m) (ftaylorSeriesWithin ℝ (f m) s) s :=
    fun m => (hf m).ftaylorSeriesWithin hs'
  have hGc : ∀ n, ContinuousOn (G n) s := fun n =>
    (hG n).continuousOn (Frequently.of_forall fun m =>
      (hf m).continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) hs')
  have hT : HasFTaylorSeriesUpToOn ∞ g (fun x n => G n x) s := by
    refine ⟨fun x hx => ?_, fun n _ x hx => ?_, fun n _ => hGc n⟩
    · -- the zeroth term
      have h1 : Tendsto (fun m => (iteratedFDerivWithin ℝ 0 (f m) s x).curry0) atTop
          (𝓝 (G 0 x).curry0) :=
        ((continuousMultilinearCurryFin0 ℝ E F).continuous.tendsto _).comp
          ((hG 0).tendsto_at hx)
      have h2 : Tendsto (fun m => (iteratedFDerivWithin ℝ 0 (f m) s x).curry0) atTop (𝓝 (g x)) := by
        simpa using hlim x hx
      exact tendsto_nhds_unique h1 h2
    · -- the derivative of the `n`-th term
      have hcl := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F).isometry
      refine hasFDerivWithinAt_of_tendstoUniformlyOn_convex hs
        (f := fun m y => iteratedFDerivWithin ℝ n (f m) s y)
        (f' := fun m y => (iteratedFDerivWithin ℝ (n + 1) (f m) s y).curryLeft)
        (fun m y hy => ((hp m).fderivWithin n (by exact_mod_cast WithTop.coe_lt_top _) y hy))
        (fun y hy => (hG n).tendsto_at hy)
        (hcl.uniformContinuous.comp_tendstoUniformlyOn (hG (n + 1)))
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F).continuous.comp_continuousOn
          (hGc (n + 1))) hx
  refine ⟨hT.contDiffOn, fun n x hx => ?_⟩
  exact (hT.eq_iteratedFDerivWithin_of_uniqueDiffOn (by exact_mod_cast le_top) hs' hx).symm

/-- **Smooth limits of uniformly Cauchy sequences**: if every iterated derivative of `fₘ` is uniformly
Cauchy on the convex set `s`, then `fₘ` converges to a function `g` that is `C^∞` on `s`, and every
iterated derivative converges uniformly to that of `g`. -/
theorem exists_contDiffOn_of_uniformCauchySeqOn [CompleteSpace F] {s : Set E} (hs : Convex ℝ s)
    (hs' : UniqueDiffOn ℝ s) {f : ℕ → E → F} (hf : ∀ m, ContDiffOn ℝ ∞ (f m) s)
    (hC : ∀ n, UniformCauchySeqOn (fun m => iteratedFDerivWithin ℝ n (f m) s) atTop s) :
    ∃ g : E → F, ContDiffOn ℝ ∞ g s ∧ (∀ x ∈ s, Tendsto (fun m => f m x) atTop (𝓝 (g x))) ∧
      ∀ n, TendstoUniformlyOn (fun m => iteratedFDerivWithin ℝ n (f m) s)
        (iteratedFDerivWithin ℝ n g s) atTop s := by
  classical
  set G : (n : ℕ) → E → ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F := fun n x =>
    limUnder atTop (fun m => iteratedFDerivWithin ℝ n (f m) s x) with hGdef
  have hGlim : ∀ n, ∀ x ∈ s, Tendsto (fun m => iteratedFDerivWithin ℝ n (f m) s x) atTop (𝓝 (G n x)) :=
    fun n x hx => tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete ((hC n).cauchySeq hx))
  have hG : ∀ n, TendstoUniformlyOn (fun m => iteratedFDerivWithin ℝ n (f m) s) (G n) atTop s :=
    fun n => (hC n).tendstoUniformlyOn_of_tendsto (hGlim n)
  set g : E → F := fun x => (G 0 x).curry0 with hg
  have hlim : ∀ x ∈ s, Tendsto (fun m => f m x) atTop (𝓝 (g x)) := by
    intro x hx
    have h := ((continuousMultilinearCurryFin0 ℝ E F).continuous.tendsto _).comp (hGlim 0 x hx)
    have e : ∀ m, f m x = continuousMultilinearCurryFin0 ℝ E F (iteratedFDerivWithin ℝ 0 (f m) s x) :=
      fun m => by simp
    simp only [e]
    exact h
  obtain ⟨hg1, hg2⟩ := contDiffOn_of_tendstoUniformlyOn_iteratedFDerivWithin hs hs' hf hlim G hG
  exact ⟨g, hg1, hlim, fun n => (hG n).congr_right fun x hx => (hg2 n x hx).symm⟩

end ShortTime
