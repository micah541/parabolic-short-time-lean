import Mathlib

/-!
# Positive definite forms are bounded below by a positive multiple of a quadratic form

On a finite-dimensional normed space, a positive definite bilinear form `B` dominates `e · q` for every
continuous quadratic form `q` (compactness of the unit sphere).
-/

noncomputable section

namespace ShortTime

theorem exists_pos_lower_bound {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (q : V → ℝ) (hq : Continuous q)
    (hqh : ∀ (c : ℝ) (ξ : V), q (c • ξ) = c ^ 2 * q ξ) (hpos : ∀ ξ : V, ξ ≠ 0 → 0 < B ξ ξ) :
    ∃ e : ℝ, 0 < e ∧ ∀ ξ : V, e * q ξ ≤ B ξ ξ := by
  let Bc : V →L[ℝ] V →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V →L[ℝ] ℝ)).toLinearMap ∘ₗ B)
  have hBc : ∀ ξ η, Bc ξ η = B ξ η := fun ξ η => rfl
  have hcont : Continuous fun ξ : V => B ξ ξ :=
    Bc.continuous.clm_apply continuous_id
  by_cases hS : (Metric.sphere (0 : V) 1).Nonempty
  · have hcomp : IsCompact (Metric.sphere (0 : V) 1) := isCompact_sphere 0 1
    obtain ⟨ξ₀, hξ₀, hmin⟩ := hcomp.exists_isMinOn hS hcont.continuousOn
    obtain ⟨ξ₁, hξ₁, hmax⟩ := hcomp.exists_isMaxOn hS hq.continuousOn
    have hξ₀ne : ξ₀ ≠ 0 := by
      intro h; rw [h] at hξ₀; simp at hξ₀
    have hm : 0 < B ξ₀ ξ₀ := hpos ξ₀ hξ₀ne
    set C := max (q ξ₁) 1 with hC
    have hCpos : 0 < C := lt_max_of_lt_right one_pos
    refine ⟨B ξ₀ ξ₀ / C, div_pos hm hCpos, fun ξ => ?_⟩
    by_cases hξ : ξ = 0
    · subst hξ
      have h0 : q 0 = 0 := by simpa using hqh 0 0
      simp [h0]
    · have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
      set η := ‖ξ‖⁻¹ • ξ with hη
      have hηS : η ∈ Metric.sphere (0 : V) 1 := by
        simp [hη, norm_smul, hn.ne']
      have h1 : B ξ₀ ξ₀ ≤ B η η := hmin hηS
      have h2 : q η ≤ C := le_trans (hmax hηS) (le_max_left _ _)
      have hξη : ξ = ‖ξ‖ • η := by
        simp [hη, smul_smul, hn.ne']
      have h3 : B ξ ξ = ‖ξ‖ ^ 2 * B η η := by
        conv_lhs => rw [hξη]
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
        ring
      have h4 : q ξ = ‖ξ‖ ^ 2 * q η := by
        conv_lhs => rw [hξη]
        exact hqh _ _
      rw [h3, h4]
      have hn2 : 0 < ‖ξ‖ ^ 2 := by positivity
      calc B ξ₀ ξ₀ / C * (‖ξ‖ ^ 2 * q η) ≤ B ξ₀ ξ₀ / C * (‖ξ‖ ^ 2 * C) := by
            gcongr
        _ = ‖ξ‖ ^ 2 * B ξ₀ ξ₀ := by field_simp
        _ ≤ ‖ξ‖ ^ 2 * B η η := by gcongr
  · refine ⟨1, one_pos, fun ξ => ?_⟩
    have : ξ = 0 := by
      by_contra h
      apply hS
      refine ⟨‖ξ‖⁻¹ • ξ, ?_⟩
      simp [norm_smul, norm_pos_iff.2 h |>.ne']
    subst this
    have h0 : q 0 = 0 := by simpa using hqh 0 0
    simp [h0]

end ShortTime
