import ShortTime.Analysis.ParamIntegralManifold

/-!
# Time derivatives of smooth functions on `M × [0,T]`

If `f` is smooth on `W × S`, with `W` open in a boundaryless manifold `M` and `S ⊆ ℝ` a set of
unique differentiability (for example `[0,T]` with `T > 0`), then the time derivative
`(y, τ) ↦ ∂_τ f(y, τ)`, taken within `S`, is smooth on `W × S` (`contMDiffOn_derivWithin_snd`),
and it is a genuine derivative within `S` (`hasDerivWithinAt_snd`). In a chart, the time
derivative is the full derivative applied to the vector `(0, 1)`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set Filter Topology Metric
open scoped Manifold ContDiff

namespace ShortTime

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A function smooth on `W × S` is differentiable in time within `S`. -/
theorem hasDerivWithinAt_snd {W : Set M} {S : Set ℝ} (hSU : UniqueDiffOn ℝ S) {f : M → ℝ → F}
    (hf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞ (fun q : M × ℝ => f q.1 q.2) (W ×ˢ S))
    {y : M} {τ : ℝ} (hy : y ∈ W) (hτ : τ ∈ S) :
    HasDerivWithinAt (f y) (derivWithin (f y) S τ) S τ := by
  have hsl : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞ (fun τ' : ℝ => (y, τ')) :=
    contMDiff_const.prodMk contMDiff_id
  have h := hf.comp hsl.contMDiffOn (fun τ' hτ' => ⟨hy, hτ'⟩)
  have hd : ContDiffOn ℝ ∞ (f y) S := contMDiffOn_iff_contDiffOn.mp h
  exact ((hd.differentiableOn (by simp)) τ hτ).hasDerivWithinAt

/-- **The time derivative of a smooth function on `M × S` is smooth on `M × S`.** -/
theorem contMDiffOn_derivWithin_snd {W : Set M} (hW : IsOpen W) {S : Set ℝ} (hSU : UniqueDiffOn ℝ S)
    {f : M → ℝ → F}
    (hf : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞ (fun q : M × ℝ => f q.1 q.2) (W ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞ (fun q : M × ℝ => derivWithin (f q.1) S q.2)
      (W ×ˢ S) := by
  rintro ⟨y₀, τ₀⟩ ⟨hy₀, hτ₀⟩
  -- an open ball around the chart image of `y₀`, inside the chart target and the preimage of `W`
  have hVopen : IsOpen ((extChartAt I y₀).target ∩ (extChartAt I y₀).symm ⁻¹' W) :=
    (continuousOn_extChartAt_symm y₀).isOpen_inter_preimage (isOpen_extChartAt_target y₀) hW
  have hV0 : extChartAt I y₀ y₀ ∈ (extChartAt I y₀).target ∩ (extChartAt I y₀).symm ⁻¹' W :=
    ⟨mem_extChartAt_target y₀, by rw [mem_preimage, extChartAt_to_inv]; exact hy₀⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hVopen _ hV0
  set B := ball (extChartAt I y₀ y₀) ρ with hB
  -- the function in the chart
  set gc : E × ℝ → F := fun p => f ((extChartAt I y₀).symm p.1) p.2 with hgc_def
  have hUD : UniqueDiffOn ℝ (B ×ˢ S) := isOpen_ball.uniqueDiffOn.prod hSU
  have hg : ContDiffOn ℝ ∞ gc (B ×ˢ S) := by
    have h1 : ContMDiffOn 𝓘(ℝ, E × ℝ) I ∞ (fun p : E × ℝ => (extChartAt I y₀).symm p.1) (B ×ˢ S) :=
      (contMDiffOn_extChartAt_symm y₀).comp contDiff_fst.contMDiff.contMDiffOn
        fun p hp => (hball hp.1).1
    have hΦ : ContMDiffOn 𝓘(ℝ, E × ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun p : E × ℝ => ((extChartAt I y₀).symm p.1, p.2)) (B ×ˢ S) :=
      h1.prodMk contDiff_snd.contMDiff.contMDiffOn
    exact contMDiffOn_iff_contDiffOn.mp (hf.comp hΦ fun p hp => ⟨(hball hp.1).2, hp.2⟩)
  -- its time derivative: the full derivative applied to `(0, 1)`
  set D : E × ℝ → F := fun p => fderivWithin ℝ gc (B ×ˢ S) p ((0 : E), (1 : ℝ)) with hD_def
  have hDsmooth : ContDiffOn ℝ ∞ D (B ×ˢ S) :=
    (hg.fderivWithin hUD (by simp)).clm_apply contDiffOn_const
  have hDeq : ∀ e ∈ B, ∀ τ ∈ S, derivWithin (fun τ' => gc (e, τ')) S τ = D (e, τ) := by
    intro e he τ hτ
    have hfd : HasFDerivWithinAt gc (fderivWithin ℝ gc (B ×ˢ S) (e, τ)) (B ×ˢ S) (e, τ) :=
      ((hg.differentiableOn (by simp)) _ ⟨he, hτ⟩).hasFDerivWithinAt
    have hline : HasDerivWithinAt (fun τ' : ℝ => (e, τ')) ((0 : E), (1 : ℝ)) S τ :=
      (hasDerivWithinAt_const τ S e).prodMk (hasDerivWithinAt_id τ S)
    exact (hfd.comp_hasDerivWithinAt τ hline fun τ' hτ' => ⟨he, hτ'⟩).derivWithin (hSU τ hτ)
  -- back on the manifold
  have hκ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E × ℝ) ∞
      (fun q : M × ℝ => (extChartAt I y₀ q.1, q.2)) ((chartAt H y₀).source ×ˢ univ) :=
    (contMDiffOn_extChartAt.comp contMDiff_fst.contMDiffOn fun q hq => hq.1).prodMk_space
      contMDiff_snd.contMDiffOn
  set T : Set (M × ℝ) := ((chartAt H y₀).source ×ˢ univ) ∩
    (fun q : M × ℝ => (extChartAt I y₀ q.1, q.2)) ⁻¹' (B ×ˢ S) with hT
  have hcomp := hDsmooth.contMDiffOn.comp (hκ.mono inter_subset_left) fun q hq => hq.2
  have hO : (chartAt H y₀).source ∩ extChartAt I y₀ ⁻¹' B ∈ 𝓝 y₀ := by
    refine inter_mem ((chartAt H y₀).open_source.mem_nhds (mem_chart_source H y₀)) ?_
    exact (continuousAt_extChartAt y₀).preimage_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hρ))
  have hTmem : T ∈ 𝓝[W ×ˢ S] (y₀, τ₀) := by
    have : ((chartAt H y₀).source ∩ extChartAt I y₀ ⁻¹' B) ×ˢ univ ∩ (W ×ˢ S) ⊆ T := by
      rintro ⟨y, τ⟩ ⟨⟨⟨hys, hyB⟩, -⟩, -, hτ⟩
      exact ⟨⟨hys, mem_univ _⟩, hyB, hτ⟩
    refine mem_of_superset (inter_mem_nhdsWithin _ (prod_mem_nhds hO univ_mem)) ?_
    rw [inter_comm]
    exact this
  have hq₀T : ((y₀, τ₀) : M × ℝ) ∈ T :=
    ⟨⟨mem_chart_source H y₀, mem_univ _⟩, mem_ball_self hρ, hτ₀⟩
  -- on `T`, `f y = gc (φ y, ·)`, so the two time derivatives agree
  have hfg : ∀ q ∈ T, derivWithin (f q.1) S q.2 = D (extChartAt I y₀ q.1, q.2) := by
    intro q hq
    have hfy : f q.1 = fun τ' => gc (extChartAt I y₀ q.1, τ') := by
      funext τ'
      simp only [hgc_def]
      rw [(extChartAt I y₀).left_inv (by rw [extChartAt_source]; exact hq.1.1)]
    rw [hfy]
    exact hDeq _ hq.2.1 _ hq.2.2
  refine ((hcomp _ hq₀T).mono_of_mem_nhdsWithin hTmem).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hTmem] with q hq
    exact hfg q hq
  · exact hfg _ hq₀T

end ShortTime
