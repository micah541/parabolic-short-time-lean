import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# The method of continuity (`lem:continuity`)

Let `X` be a Banach space and `Y` a normed space. Let `T₀, T₁ : X →L Y`, with a uniform
lower bound `‖x‖ ≤ C ‖T_s x‖` along the segment `T_s = (1-s) T₀ + s T₁`. If `T₀` is surjective,
then so is `T₁`.

The perturbation step uses the contraction mapping principle on `X`. It needs neither the open
mapping theorem nor completeness of `Y`.
-/

open Set

namespace ShortTime

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A surjective operator with a lower bound `‖x‖ ≤ C ‖A x‖` stays surjective under a
perturbation `B` with `C ‖B‖ < 1`. -/
theorem surjective_add_of_lowerBound {A B : X →L[ℝ] Y} {C : ℝ} (hC0 : 0 ≤ C)
    (hA : Function.Surjective A) (hbound : ∀ x, ‖x‖ ≤ C * ‖A x‖) (hB : C * ‖B‖ < 1) :
    Function.Surjective (A + B) := by
  intro y
  choose Ainv hAinv using hA
  have hlip : ∀ a b : Y, dist (Ainv a) (Ainv b) ≤ C * dist a b := by
    intro a b
    rw [dist_eq_norm, dist_eq_norm]
    calc ‖Ainv a - Ainv b‖ ≤ C * ‖A (Ainv a - Ainv b)‖ := hbound _
      _ = C * ‖a - b‖ := by rw [map_sub, hAinv, hAinv]
  let Φ : X → X := fun x => Ainv (y - B x)
  have hK : 0 ≤ C * ‖B‖ := mul_nonneg hC0 (norm_nonneg _)
  let K : NNReal := ⟨C * ‖B‖, hK⟩
  have hΦ : ContractingWith K Φ := by
    refine ⟨hB, LipschitzWith.of_dist_le_mul fun x₁ x₂ => ?_⟩
    calc dist (Φ x₁) (Φ x₂) ≤ C * dist (y - B x₁) (y - B x₂) := hlip _ _
      _ = C * ‖B (x₂ - x₁)‖ := by
          rw [dist_eq_norm, map_sub]; congr 1; abel_nf
      _ ≤ C * (‖B‖ * ‖x₂ - x₁‖) := by gcongr; exact B.le_opNorm _
      _ = (K : ℝ) * dist x₁ x₂ := by
          rw [dist_comm, dist_eq_norm]
          show C * (‖B‖ * ‖x₂ - x₁‖) = (C * ‖B‖) * ‖x₂ - x₁‖
          ring
  have : Nonempty X := ⟨0⟩
  refine ⟨ContractingWith.fixedPoint Φ hΦ, ?_⟩
  have hfix := ContractingWith.fixedPoint_isFixedPt (f := Φ) hΦ
  set x := ContractingWith.fixedPoint Φ hΦ
  have hx : A x = y - B x := by
    have := congrArg A hfix
    simpa [Φ, hAinv] using this.symm
  simp [hx]

/-- **Method of continuity** (`lem:continuity`). -/
theorem surjective_of_continuity (T₀ T₁ : X →L[ℝ] Y) (C : ℝ)
    (hC : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x, ‖x‖ ≤ C * ‖((1 - s) • T₀ + s • T₁) x‖)
    (h₀ : Function.Surjective T₀) : Function.Surjective T₁ := by
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hC'bound : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x, ‖x‖ ≤ C' * ‖((1 - s) • T₀ + s • T₁) x‖ :=
    fun s hs x => (hC s hs x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  obtain ⟨N, hN⟩ : ∃ N : ℕ, C' * ‖T₁ - T₀‖ < N ∧ 0 < N :=
    ⟨⌈C' * ‖T₁ - T₀‖⌉₊ + 1, by
      constructor
      · push_cast; linarith [Nat.le_ceil (C' * ‖T₁ - T₀‖)]
      · omega⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN.2
  let T : ℝ → X →L[ℝ] Y := fun s => (1 - s) • T₀ + s • T₁
  have key : ∀ k : ℕ, k ≤ N → Function.Surjective (T (k / N)) := by
    intro k
    induction k with
    | zero => intro _; simpa [T] using h₀
    | succ k ih =>
      intro hk
      have hkN : (k : ℝ) / N ∈ Icc (0 : ℝ) 1 := by
        constructor
        · positivity
        · rw [div_le_one hNpos]; exact_mod_cast (Nat.le_of_succ_le hk)
      have hstep : T ((k + 1 : ℕ) / N) = T (k / N) + (1 / (N : ℝ)) • (T₁ - T₀) := by
        simp only [T]; push_cast
        ext x
        simp only [FunLike.coe_add, FunLike.coe_smul, FunLike.coe_sub, Pi.add_apply, Pi.smul_apply, Pi.sub_apply]
        rw [show ((k : ℝ) + 1) / N = k / N + 1 / N by ring]
        simp only [sub_smul, add_smul, smul_sub]
        abel
      rw [hstep]
      refine surjective_add_of_lowerBound hC'0 (ih (Nat.le_of_succ_le hk))
        (hC'bound _ hkN) ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      calc C' * (1 / N * ‖T₁ - T₀‖) = C' * ‖T₁ - T₀‖ / N := by ring
        _ < 1 := by rw [div_lt_one hNpos]; exact hN.1
  have h1 := key N le_rfl
  rw [div_self hNpos.ne'] at h1
  simpa [T] using h1

end ShortTime
