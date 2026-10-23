import ShortTime.Nonlinear.IterPullExt

/-!
# The composite pullback on `𝒫^m`: basic properties

Paper: Lemma `lem:flows` (b), for the composite `Π_σ = Π^{B 0}_{σ 0} ∘ ⋯` (`iterPullExt`).

* `continuous_hpullExt_uncurry`: `(τ, v) ↦ Π_τ v` is jointly continuous on `ℝ × 𝒫^m`.
* `iterPullExt_zero`: `Π_0 = id`; `iterPullExt_mem_zeroAtStart`: `Π_σ` preserves `𝒫^m_0`;
  `exists_norm_iterPullExt_le`: `‖Π_σ‖` is bounded on bounded sets of `σ`;
  `iterPullExt_timeDerivExt`: `Π_σ ∘ ∂ₜ = ∂ₜ ∘ Π_σ`; `continuous_iterPullExt_apply`: `σ ↦ Π_σ v`
  is continuous.
-/

noncomputable section

open Bundle Manifold Set Filter
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
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

variable (g : SmoothRiemannianMetric I M) (s p m : ℕ) {T : ℝ}

theorem mul_lt_half_aux {C a ε : ℝ} (hC : 0 ≤ C) (ha0 : 0 ≤ a) (ha : a < ε / (2 * (C + 1))) :
    C * a < ε / 2 := by
  have hC1 : 0 < 2 * (C + 1) := by positivity
  rw [lt_div_iff₀ hC1] at ha
  nlinarith

/-- **Joint continuity** of `(τ, v) ↦ Π_τ v` on `ℝ × 𝒫^m`. -/
theorem continuous_hpullExt_uncurry (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (hT : 0 < T) :
    Continuous fun q : ℝ × ParabolicSpace g s p m T => hpullExt X g s p m T q.1 q.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨τ₀, x₀⟩
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨C, hC0, hC⟩ := exists_norm_hpullExt_le X g s (p := p) (m := m) hT (|τ₀| + 1)
  have hc := (continuous_hpullExt_apply X g s (p := p) (m := m) hT x₀).continuousAt (x := τ₀)
  obtain ⟨δ₁, hδ₁, h1⟩ := Metric.continuousAt_iff.mp hc (ε / 2) (half_pos hε)
  have hη : 0 < ε / (2 * (C + 1)) := by positivity
  refine ⟨min 1 (min δ₁ (ε / (2 * (C + 1)))), lt_min one_pos (lt_min hδ₁ hη), fun q hq => ?_⟩
  rw [Prod.dist_eq] at hq
  have hτ : dist q.1 τ₀ < min 1 (min δ₁ (ε / (2 * (C + 1)))) := (le_max_left _ _).trans_lt hq
  have hx : dist q.2 x₀ < min 1 (min δ₁ (ε / (2 * (C + 1)))) := (le_max_right _ _).trans_lt hq
  have hτ1 : dist q.1 τ₀ < 1 := hτ.trans_le (min_le_left _ _)
  have hτδ : dist q.1 τ₀ < δ₁ := hτ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hxη : dist q.2 x₀ < ε / (2 * (C + 1)) :=
    hx.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hq1 : |q.1| ≤ |τ₀| + 1 := by
    have h := abs_sub_abs_le_abs_sub q.1 τ₀
    rw [← Real.dist_eq] at h
    linarith
  have e1 : dist (hpullExt X g s p m T q.1 q.2) (hpullExt X g s p m T q.1 x₀) < ε / 2 := by
    rw [dist_eq_norm, ← map_sub]
    refine (hC q.1 hq1 _).trans_lt ?_
    rw [← dist_eq_norm]
    exact mul_lt_half_aux hC0 dist_nonneg hxη
  have e2 : dist (hpullExt X g s p m T q.1 x₀) (hpullExt X g s p m T τ₀ x₀) < ε / 2 := h1 hτδ
  calc dist (hpullExt X g s p m T q.1 q.2) (hpullExt X g s p m T τ₀ x₀)
      ≤ dist (hpullExt X g s p m T q.1 q.2) (hpullExt X g s p m T q.1 x₀) +
        dist (hpullExt X g s p m T q.1 x₀) (hpullExt X g s p m T τ₀ x₀) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add e1 e2
    _ = ε := add_halves ε

theorem iterPullExt_succ_apply {n : ℕ} (B : Fin (n + 1) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (σ : Fin (n + 1) → ℝ) (x : ParabolicSpace g s p m T) :
    iterPullExt g s p m T B σ x = hpullExt (B 0) g s p m T (σ 0)
      (iterPullExt g s p m T (fun i => B i.succ) (fun i => σ i.succ) x) := rfl

/-- **`Π_0 = id`** on `𝒫^m`. -/
theorem iterPullExt_zero (hT : 0 < T) :
    ∀ {n : ℕ} (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      iterPullExt g s p m T B 0 = ContinuousLinearMap.id ℝ (ParabolicSpace g s p m T)
  | 0, _ => rfl
  | n + 1, B => ContinuousLinearMap.ext fun x => by
    rw [iterPullExt_succ_apply]
    have h0 : (fun i : Fin n => (0 : Fin (n + 1) → ℝ) i.succ) = 0 := rfl
    rw [h0, iterPullExt_zero hT (fun i => B i.succ), Pi.zero_apply, hpullExt_zero _ g s hT]
    rfl

/-- **`Π_σ` preserves `𝒫^m_0`.** -/
theorem iterPullExt_mem_zeroAtStart (hT : 0 < T) :
    ∀ {n : ℕ} (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (σ : Fin n → ℝ)
      {v : ParabolicSpace g s p m T}, v ∈ zeroAtStart g s p m T →
        iterPullExt g s p m T B σ v ∈ zeroAtStart g s p m T
  | 0, _, _, _, hv => hv
  | _ + 1, B, σ, _, hv => by
    rw [iterPullExt_succ_apply]
    exact hpullExt_mem_zeroAtStart _ g s hT _
      (iterPullExt_mem_zeroAtStart hT (fun i => B i.succ) (fun i => σ i.succ) hv)

/-- **Uniform bounds** for `Π_σ` with `|σ i| ≤ R`. -/
theorem exists_norm_iterPullExt_le_of_abs (hT : 0 < T) (R : ℝ) :
    ∀ {n : ℕ} (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      ∃ C, 0 ≤ C ∧ ∀ σ : Fin n → ℝ, (∀ i, |σ i| ≤ R) → ∀ x : ParabolicSpace g s p m T,
        ‖iterPullExt g s p m T B σ x‖ ≤ C * ‖x‖
  | 0, B => ⟨1, zero_le_one, fun _ _ x => by rw [one_mul]; exact le_rfl⟩
  | n + 1, B => by
    obtain ⟨C₁, hC₁0, hC₁⟩ := exists_norm_iterPullExt_le_of_abs hT R (fun i => B i.succ)
    obtain ⟨C₀, hC₀0, hC₀⟩ := exists_norm_hpullExt_le (B 0) g s (p := p) (m := m) hT R
    refine ⟨C₀ * C₁, mul_nonneg hC₀0 hC₁0, fun σ hσ x => ?_⟩
    rw [iterPullExt_succ_apply]
    refine (hC₀ (σ 0) (hσ 0) _).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC₁ _ (fun i => hσ i.succ) x) hC₀0

/-- **Uniform bounds** for `Π_σ` on bounded sets of `σ`. -/
theorem exists_norm_iterPullExt_le (hT : 0 < T) (R : ℝ) {n : ℕ}
    (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∃ C, 0 ≤ C ∧ ∀ σ : Fin n → ℝ, ‖σ‖ ≤ R → ∀ x : ParabolicSpace g s p m T,
      ‖iterPullExt g s p m T B σ x‖ ≤ C * ‖x‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_iterPullExt_le_of_abs g s p m hT R B
  refine ⟨C, hC0, fun σ hσ => hC σ fun i => ?_⟩
  rw [← Real.norm_eq_abs]
  exact (norm_le_pi_norm σ i).trans hσ

/-- **`Π_σ` commutes with `∂ₜ`.** -/
theorem iterPullExt_timeDerivExt (hT : 0 < T) (hm : 1 ≤ m) {n : ℕ}
    (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (σ : Fin n → ℝ)
    (x : ParabolicSpace g s p m T) :
    iterPullExt g s p (m - 1) T B σ (timeDerivExt hT hm x) =
      timeDerivExt hT hm (iterPullExt g s p m T B σ x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterPullExt_succ_apply, iterPullExt_succ_apply, ih (fun i => B i.succ) (fun i => σ i.succ)]
    have h := DFunLike.congr_fun (hpullExt_comp_timeDerivExt (B 0) g s (p := p) (m := m) hT hm (σ 0))
      (iterPullExt g s p m T (fun i => B i.succ) (fun i => σ i.succ) x)
    simp only [ContinuousLinearMap.comp_apply] at h
    exact h

/-- **Continuity in `σ`** of `σ ↦ Π_σ v`, for every `v ∈ 𝒫^m`. -/
theorem continuous_iterPullExt_apply (hT : 0 < T) {n : ℕ}
    (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : ParabolicSpace g s p m T) :
    Continuous fun σ => iterPullExt g s p m T B σ x := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    have h := ih (fun i => B i.succ)
    have hin : Continuous fun σ : Fin (n + 1) → ℝ =>
        (σ 0, iterPullExt g s p m T (fun i => B i.succ) (fun i => σ i.succ) x) :=
      (continuous_apply 0).prodMk (h.comp (continuous_pi fun i => continuous_apply i.succ))
    have h2 := (continuous_hpullExt_uncurry g s p m (B 0) hT).comp hin
    exact h2.congr fun σ => (iterPullExt_succ_apply g s p m B σ x).symm

end HFlow

end ShortTime
