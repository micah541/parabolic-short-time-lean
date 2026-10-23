import ShortTime.Nonlinear.AngenentSmooth
import ShortTime.Nonlinear.AngenentIFT
import ShortTime.Nonlinear.Nemytskii
import ShortTime.Nonlinear.FlowsNaturalParamIter

/-!
# Naturality of the composition operator on `𝒫^m`

`natural_concrete`: for the parametric operator `𝒩'` (agreeing on smooth families within `δ'` of `W`
with the composition operator of `iterFM B`) and the operator `𝒩` (agreeing with `F[u]` on smooth
families), `𝒩'(σ, Π_σ u) = Π_σ 𝒩(u)` for small `σ` and `u` near `W`. Smooth families by
`iterPull_nonlinFamily`, the rest by density and continuity.
-/

noncomputable section

open Bundle Manifold Set Filter Topology Metric
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open scoped Manifold ContDiff

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

variable (g : SmoothRiemannianMetric I M) {s p : ℕ} {T : ℝ}

/-- The smooth families are dense in `𝒫^m`. -/
theorem dense_ofSmooth (m : ℕ) :
    Dense {x : ParabolicSpace g s p m T | ∃ (u : ℝ → SmoothCcTensor g 0 s)
      (hu : JointlySmoothOn g 0 s (Icc 0 T) u), x = ofSmooth u hu} := by
  refine (show Dense (range (UniformSpace.Completion.coe' : ParabolicPre g s p m T → _)) from
    UniformSpace.Completion.denseRange_coe).mono ?_
  rintro _ ⟨a, rfl⟩
  exact ⟨a.family, a.2, rfl⟩

theorem natural_concrete (D : EquationData I M 0 s p) (hT : 0 < T) (hTD : T ≤ D.T₀) {m : ℕ}
    {n : ℕ} (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {w : ℝ → SmoothCcTensor g 0 s} (hw : JointlySmoothOn g 0 s (Icc 0 T) w)
    {δ : ℝ} (𝒩 : ParabolicSpace g s p m T → ParabolicSpace g s p (m - 1) T)
    (h𝒩 : ContDiffAt ℝ ∞ 𝒩 (ofSmooth w hw))
    (hagree : ∀ u (hu : JointlySmoothOn g 0 s (Icc 0 T) u),
      dist (ofSmooth (p := p) (m := m) u hu) (ofSmooth w hw) < δ →
      (∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (u t) x ∈ D.dom t x) ∧
      ∃ hF, 𝒩 (ofSmooth u hu) = ofSmooth (D.nonlinFamily u) hF)
    {δ' : ℝ} (hδ' : 0 < δ') (𝒩' : (Fin n → ℝ) × ParabolicSpace g s p m T →
      ParabolicSpace g s p (m - 1) T)
    (hball : ContDiffOn ℝ ∞ 𝒩' (ball ((0 : Fin n → ℝ), ofSmooth (p := p) (m := m) w hw) δ'))
    (hpar : ∀ (σ : Fin n → ℝ) u (hu : JointlySmoothOn g 0 s (Icc 0 T) u), ‖σ‖ < δ' →
      dist (ofSmooth (p := p) (m := m) u hu) (ofSmooth w hw) < δ' →
      (∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        covJet g 0 s (2 * p) (u t) x ∈ (iterFM B g D).dom σ t x) ∧
      ∃ hF, 𝒩' (σ, ofSmooth u hu) =
        ofSmooth ((iterFM B g D).apply σ (EquationData.jetFamily (p := p) u)) hF)
    (hδ : 0 < δ) :
    ∃ ρ₁ > 0, ∃ r₁ > 0, ∀ σ : Fin n → ℝ, ‖σ‖ < ρ₁ → ∀ u : ParabolicSpace g s p m T,
      dist u (ofSmooth w hw) < r₁ →
      𝒩' (σ, iterPullExt g s p m T B σ u) = iterPullExt g s p (m - 1) T B σ (𝒩 u) := by
  classical
  obtain ⟨W, hWdef⟩ : ∃ W : ParabolicSpace g s p m T, W = ofSmooth w hw := ⟨_, rfl⟩
  rw [← hWdef] at h𝒩 hagree hpar hball ⊢
  -- continuity of `𝒩` near `W`
  have h1 : ContDiffAt ℝ 1 𝒩 W := h𝒩.of_le (by exact_mod_cast le_top)
  have hev1 : ∀ᶠ y in 𝓝 W, ContinuousAt 𝒩 y :=
    (h1.eventually (by simp)).mono fun y hy => hy.continuousAt
  obtain ⟨rc, hrc, hrcP⟩ := Metric.eventually_nhds_iff.1 hev1
  obtain ⟨C, hC0, hC⟩ := exists_norm_iterPullExt_le g s p m (T := T) hT 1 B
  obtain ⟨r₁, hr₁⟩ : ∃ r₁, r₁ = min (min δ rc) (δ' / (2 * (C + 1))) := ⟨_, rfl⟩
  have hr₁0 : 0 < r₁ := by
    rw [hr₁]; exact lt_min (lt_min hδ hrc) (by positivity)
  have hr₁δ : r₁ ≤ δ := hr₁ ▸ (min_le_left _ _).trans (min_le_left _ _)
  have hr₁c : r₁ ≤ rc := hr₁ ▸ (min_le_left _ _).trans (min_le_right _ _)
  have hr₁C : r₁ ≤ δ' / (2 * (C + 1)) := hr₁ ▸ min_le_right _ _
  -- the radius in `σ`
  have hS : ∀ᶠ σ in 𝓝 (0 : Fin n → ℝ), IterSmall g B s (2 * p) σ := by
    refine Filter.eventually_all.2 fun i => ?_
    exact ((continuous_abs.comp (continuous_apply i)).continuousAt).eventually_lt
      continuousAt_const (by simpa using natδ_pos (B i) g s (2 * p) (I := I))
  have hDist : ∀ᶠ σ in 𝓝 (0 : Fin n → ℝ), dist (iterPullExt g s p m T B σ W) W < δ' / 2 := by
    refine ((Continuous.dist (continuous_iterPullExt_apply g s p m hT B W)
      continuous_const).continuousAt).eventually_lt continuousAt_const ?_
    simp only [iterPullExt_zero g s p m hT B, ContinuousLinearMap.id_apply, dist_self]
    positivity
  have hBall : ∀ᶠ σ in 𝓝 (0 : Fin n → ℝ), dist σ 0 < min 1 δ' :=
    Metric.ball_mem_nhds (0 : Fin n → ℝ) (lt_min one_pos hδ')
  obtain ⟨ρ₁, hρ₁, hρP⟩ := Metric.eventually_nhds_iff.1 (hS.and (hDist.and hBall))
  refine ⟨ρ₁, hρ₁, r₁, hr₁0, fun σ hσ => ?_⟩
  obtain ⟨hσS, hσD, hσB⟩ := hρP (y := σ) (by rwa [dist_zero_right])
  rw [dist_zero_right] at hσB
  have hσ1 : ‖σ‖ ≤ 1 := (lt_min_iff.1 hσB).1.le
  have hσδ : ‖σ‖ < δ' := (lt_min_iff.1 hσB).2
  -- `Π_σ` keeps the ball in the domain of `𝒩'`
  have hdist : ∀ u : ParabolicSpace g s p m T, dist u W < r₁ →
      dist (iterPullExt g s p m T B σ u) W < δ' := by
    intro u hu
    have e1 : dist (iterPullExt g s p m T B σ u) (iterPullExt g s p m T B σ W) ≤ C * dist u W := by
      rw [dist_eq_norm, dist_eq_norm, ← map_sub]
      exact hC σ hσ1 _
    have e2 : C * dist u W ≤ δ' / 2 := by
      have h3 : C * dist u W ≤ C * (δ' / (2 * (C + 1))) :=
        mul_le_mul_of_nonneg_left (hu.le.trans hr₁C) hC0
      refine h3.trans ?_
      rw [show C * (δ' / (2 * (C + 1))) = δ' / 2 * (C / (C + 1)) by field_simp]
      calc δ' / 2 * (C / (C + 1)) ≤ δ' / 2 * 1 :=
            mul_le_mul_of_nonneg_left ((div_le_one (by positivity)).2 (by linarith)) (by positivity)
        _ = δ' / 2 := mul_one _
    calc dist (iterPullExt g s p m T B σ u) W
        ≤ dist (iterPullExt g s p m T B σ u) (iterPullExt g s p m T B σ W) +
          dist (iterPullExt g s p m T B σ W) W := dist_triangle _ _ _
      _ < δ' / 2 + δ' / 2 := add_lt_add_of_le_of_lt (e1.trans e2) hσD
      _ = δ' := add_halves _
  -- both sides are continuous on the ball
  have hcL : ContinuousOn (fun u => 𝒩' (σ, iterPullExt g s p m T B σ u)) (ball W r₁) := by
    refine hball.continuousOn.comp (f := fun u => (σ, iterPullExt g s p m T B σ u))
      (continuous_const.prodMk (iterPullExt g s p m T B σ).continuous).continuousOn ?_
    intro u hu
    rw [mem_ball, Prod.dist_eq]
    exact max_lt (by rw [dist_zero_right]; exact hσδ) (hdist u hu)
  have hcR : ContinuousOn (fun u => iterPullExt g s p (m - 1) T B σ (𝒩 u)) (ball W r₁) := by
    refine (iterPullExt g s p (m - 1) T B σ).continuous.comp_continuousOn ?_
    intro y hy
    exact (hrcP (lt_of_lt_of_le hy hr₁c)).continuousWithinAt
  have hEq : EqOn (fun u => 𝒩' (σ, iterPullExt g s p m T B σ u))
      (fun u => iterPullExt g s p (m - 1) T B σ (𝒩 u)) (ball W r₁ ∩ {x : ParabolicSpace g s p m T |
      ∃ (u : ℝ → SmoothCcTensor g 0 s) (hu : JointlySmoothOn g 0 s (Icc 0 T) u),
        x = ofSmooth u hu}) := by
    rintro _ ⟨hx, u, hu, rfl⟩
    have hd : dist (ofSmooth (p := p) (m := m) u hu) W < r₁ := mem_ball.1 hx
    obtain ⟨hdomu, hF, h𝒩u⟩ := hagree u hu (lt_of_lt_of_le hd hr₁δ)
    have hit := iterPullExt_ofSmooth g s p m hT B σ hu
    obtain ⟨-, hF', h𝒩'u⟩ := hpar σ _ (jointlySmoothOn_iterPull g s B σ hu) hσδ
      (by rw [← hit]; exact hdist _ hd)
    show 𝒩' (σ, iterPullExt g s p m T B σ (ofSmooth u hu)) =
      iterPullExt g s p (m - 1) T B σ (𝒩 (ofSmooth u hu))
    rw [hit, h𝒩'u, h𝒩u, iterPullExt_ofSmooth g s p (m - 1) hT B σ hF]
    refine ofSmooth_congr hT _ _ fun t ht => ?_
    exact (iterPull_nonlinFamily g D B hTD hu hdomu hσS ht).symm
  have key := Set.EqOn.of_subset_closure hEq hcL hcR Set.inter_subset_left
    ((dense_ofSmooth g m).open_subset_closure_inter (isOpen_ball (x := W) (ε := r₁)))
  intro u hu
  exact key (mem_ball.2 hu)

end HFlow

end ShortTime
