import ShortTime.Analysis.ParamIntegral
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smooth dependence of `∫₀¹ f(y, τ, σ) dσ` on a point of a manifold and a time

If `f` is smooth on `(W × S) × [0, 1]`, with `W` open in a boundaryless manifold `M` and `S ⊆ ℝ`
convex (for example a closed time interval), then `(y, τ) ↦ ∫₀¹ f(y, τ, σ) dσ` is smooth on `W × S`,
up to the endpoints of `S`. In a chart this is `contDiffOn_integral_Icc`.
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
variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Smoothness of `∫₀¹ f(y, τ, σ) dσ` on a manifold**, up to the boundary of the time set. -/
theorem contMDiffOn_integral_Icc {W : Set M} (hW : IsOpen W) {S : Set ℝ} (hS : Convex ℝ S)
    (hSU : UniqueDiffOn ℝ S) {f : M → ℝ → ℝ → F}
    (hf : ContMDiffOn ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞
      (fun q : (M × ℝ) × ℝ => f q.1.1 q.1.2 q.2) ((W ×ˢ S) ×ˢ Icc (0 : ℝ) 1)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞ (fun q : M × ℝ => ∫ σ in (0 : ℝ)..1, f q.1 q.2 σ)
      (W ×ˢ S) := by
  rintro ⟨y₀, τ₀⟩ ⟨hy₀, hτ₀⟩
  -- an open ball around the chart image of `y₀`, inside the chart target and the preimage of `W`
  have hVopen : IsOpen ((extChartAt I y₀).target ∩ (extChartAt I y₀).symm ⁻¹' W) :=
    (continuousOn_extChartAt_symm y₀).isOpen_inter_preimage (isOpen_extChartAt_target y₀) hW
  have hV0 : extChartAt I y₀ y₀ ∈ (extChartAt I y₀).target ∩ (extChartAt I y₀).symm ⁻¹' W :=
    ⟨mem_extChartAt_target y₀, by rw [mem_preimage, extChartAt_to_inv]; exact hy₀⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hVopen _ hV0
  set B := ball (extChartAt I y₀ y₀) ρ with hB
  -- the integrand in the chart
  set g : E × ℝ → ℝ → F := fun p σ => f ((extChartAt I y₀).symm p.1) p.2 σ with hg_def
  have hU : Convex ℝ (B ×ˢ S) := (convex_ball _ _).prod hS
  have hUD : UniqueDiffOn ℝ (B ×ˢ S) := isOpen_ball.uniqueDiffOn.prod hSU
  have hg : ContDiffOn ℝ ∞ (fun z : (E × ℝ) × ℝ => g z.1 z.2) ((B ×ˢ S) ×ˢ Icc (0 : ℝ) 1) := by
    have h11 : ContMDiff 𝓘(ℝ, (E × ℝ) × ℝ) 𝓘(ℝ, E) ∞ (fun z : (E × ℝ) × ℝ => z.1.1) :=
      (contDiff_fst.comp contDiff_fst).contMDiff
    have h12 : ContMDiff 𝓘(ℝ, (E × ℝ) × ℝ) 𝓘(ℝ, ℝ) ∞ (fun z : (E × ℝ) × ℝ => z.1.2) :=
      (contDiff_snd.comp contDiff_fst).contMDiff
    have h2 : ContMDiff 𝓘(ℝ, (E × ℝ) × ℝ) 𝓘(ℝ, ℝ) ∞ (fun z : (E × ℝ) × ℝ => z.2) :=
      contDiff_snd.contMDiff
    have h1 : ContMDiffOn 𝓘(ℝ, (E × ℝ) × ℝ) I ∞
        (fun z : (E × ℝ) × ℝ => (extChartAt I y₀).symm z.1.1) ((B ×ˢ S) ×ˢ Icc (0 : ℝ) 1) :=
      (contMDiffOn_extChartAt_symm y₀).comp h11.contMDiffOn fun z hz => (hball hz.1.1).1
    have hΦ : ContMDiffOn 𝓘(ℝ, (E × ℝ) × ℝ) ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) ∞
        (fun z : (E × ℝ) × ℝ => (((extChartAt I y₀).symm z.1.1, z.1.2), z.2))
        ((B ×ˢ S) ×ˢ Icc (0 : ℝ) 1) :=
      (h1.prodMk h12.contMDiffOn).prodMk h2.contMDiffOn
    exact contMDiffOn_iff_contDiffOn.mp
      (hf.comp hΦ fun z hz => ⟨⟨(hball hz.1.1).2, hz.1.2⟩, hz.2⟩)
  have hφ : ContDiffOn ℝ ∞ (fun p : E × ℝ => ∫ σ in (0 : ℝ)..1, g p σ) (B ×ˢ S) :=
    contDiffOn_integral_Icc hU hUD hg
  -- back on the manifold
  have hκ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E × ℝ) ∞
      (fun q : M × ℝ => (extChartAt I y₀ q.1, q.2)) ((chartAt H y₀).source ×ˢ univ) :=
    (contMDiffOn_extChartAt.comp contMDiff_fst.contMDiffOn fun q hq => hq.1).prodMk_space
      contMDiff_snd.contMDiffOn
  have hφ' : ContMDiffOn 𝓘(ℝ, E × ℝ) 𝓘(ℝ, F) ∞
      (fun p : E × ℝ => ∫ σ in (0 : ℝ)..1, g p σ) (B ×ˢ S) :=
    hφ.contMDiffOn
  set T : Set (M × ℝ) := ((chartAt H y₀).source ×ˢ univ) ∩
    (fun q : M × ℝ => (extChartAt I y₀ q.1, q.2)) ⁻¹' (B ×ˢ S) with hT
  have hcomp := hφ'.comp (hκ.mono inter_subset_left) fun q hq => hq.2
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
  refine ((hcomp _ hq₀T).mono_of_mem_nhdsWithin hTmem).congr_of_eventuallyEq
    ?_ ?_
  · filter_upwards [hTmem] with q hq
    simp only [Function.comp_apply, hg_def]
    rw [(extChartAt I y₀).left_inv (by rw [extChartAt_source]; exact hq.1.1)]
  · simp only [Function.comp_apply, hg_def, extChartAt_to_inv]

end ShortTime
