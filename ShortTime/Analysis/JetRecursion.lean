import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Jets defined by a first-order recursion

The Euclidean part of the comparison between covariant jets and coordinate derivatives.

Let `G i : E → F i` be smooth on an open set `Ω`, related by
`D(G i) = P i (G (i+1)) + Q i (G i)`, with `P i` fixed linear maps and `Q i` smooth fields of linear
maps. (In a chart, `G i` is the reading of `∇^i u`, and `Q i` is the Christoffel term.) Then on a
compact `K ⊆ Ω`, uniformly in `G`:

* `exists_iter_le_rec`: `|D^n G i| ≤ C Σ_{k ≤ i+n} |G k|`;
* `exists_iter_le_rec_inv`: if moreover `G (i+1) = P' i (D(G i) - Q i (G i))`, then
  `|D^n G i| ≤ C Σ_{m ≤ N+i} |D^m G 0|` for `n ≤ N`.

We also record a bound of a multilinear map by its values on a spanning family
(`norm_le_sum_apply_frame`).
-/

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace ShortTime.JetRec

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem natCast_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by
  exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)

/-- Uniform bounds for the derivatives of order `≤ n` of a smooth function on a compact set. -/
theorem exists_bound_iteratedFDerivWithin {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : E → Y} {Ω K : Set E} (hΩ : UniqueDiffOn ℝ Ω) (hf : ContDiffOn ℝ ∞ f Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (n : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ l ≤ n, ∀ y ∈ K, ‖iteratedFDerivWithin ℝ l f Ω y‖ ≤ C := by
    induction n with
    | zero =>
      obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
        ((hf.continuousOn_iteratedFDerivWithin (m := 0) (natCast_le_infty 0) hΩ).mono hKΩ)
      refine ⟨max C 0, le_max_right _ _, fun l hl y hy => ?_⟩
      obtain rfl : l = 0 := Nat.le_zero.mp hl
      exact (hC y hy).trans (le_max_left _ _)
    | succ n ih =>
      obtain ⟨C₀, hC₀, h₀⟩ := ih
      obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
        ((hf.continuousOn_iteratedFDerivWithin (m := n + 1) (natCast_le_infty _) hΩ).mono hKΩ)
      refine ⟨max C₀ C, le_max_of_le_left hC₀, fun l hl y hy => ?_⟩
      rcases Nat.lt_or_ge l (n + 1) with h | h
      · exact (h₀ l (Nat.lt_succ_iff.mp h) y hy).trans (le_max_left _ _)
      · obtain rfl : l = n + 1 := le_antisymm hl h
        exact (hC y hy).trans (le_max_right _ _)

/-- **Leibniz bound** for `y ↦ L (A y) + Q y (B y)`. -/
theorem norm_iter_lin_add_apply_le {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {Ω : Set E} (hΩ : UniqueDiffOn ℝ Ω) {A : E → X} {B : E → Y} {Q : E → Y →L[ℝ] Z}
    (L : X →L[ℝ] Z) (hA : ContDiffOn ℝ ∞ A Ω) (hB : ContDiffOn ℝ ∞ B Ω)
    (hQ : ContDiffOn ℝ ∞ Q Ω) {y : E} (hy : y ∈ Ω) (n : ℕ) :
    ‖iteratedFDerivWithin ℝ n (fun y => L (A y) + Q y (B y)) Ω y‖ ≤
      ‖L‖ * ‖iteratedFDerivWithin ℝ n A Ω y‖ +
        ∑ l ∈ Finset.range (n + 1), (n.choose l : ℝ) * ‖iteratedFDerivWithin ℝ l Q Ω y‖ *
          ‖iteratedFDerivWithin ℝ (n - l) B Ω y‖ := by
  have h1 : ContDiffWithinAt ℝ n (fun y => L (A y)) Ω y :=
    ((L.contDiff.comp_contDiffOn hA).of_le (natCast_le_infty n)) y hy
  have h2 : ContDiffWithinAt ℝ n (fun y => Q y (B y)) Ω y :=
    ((hQ.clm_apply hB).of_le (natCast_le_infty n)) y hy
  have hsum : (fun y => L (A y) + Q y (B y)) = (fun y => L (A y)) + (fun y => Q y (B y)) := rfl
  rw [hsum, iteratedFDerivWithin_add_apply h1 h2 hΩ hy]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · have hL : (fun y => L (A y)) = L ∘ A := rfl
    rw [hL, L.iteratedFDerivWithin_comp_left (hA y hy) hΩ hy (natCast_le_infty n)]
    exact L.norm_compContinuousMultilinearMap_le _
  · exact norm_iteratedFDerivWithin_clm_apply hQ hB hΩ hy (natCast_le_infty n)

theorem sum_range_mono_le {f : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k) {a b : ℕ} (hab : a ≤ b) :
    ∑ k ∈ Finset.range a, f k ≤ ∑ k ∈ Finset.range b, f k :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab) fun k _ _ => hf k

theorem sum_choose_mul_le {n : ℕ} {a : ℕ → ℝ} {M S : ℝ} (_hM : 0 ≤ M) (_hS : 0 ≤ S)
    (ha : ∀ l ∈ Finset.range (n + 1), a l ≤ M * S) (_ha0 : ∀ l, 0 ≤ a l) :
    ∑ l ∈ Finset.range (n + 1), (n.choose l : ℝ) * a l ≤ (2 ^ n * M) * S := by
  calc ∑ l ∈ Finset.range (n + 1), (n.choose l : ℝ) * a l
      ≤ ∑ l ∈ Finset.range (n + 1), (n.choose l : ℝ) * (M * S) :=
        Finset.sum_le_sum fun l hl => mul_le_mul_of_nonneg_left (ha l hl) (by positivity)
    _ = (∑ l ∈ Finset.range (n + 1), (n.choose l : ℝ)) * (M * S) := by rw [Finset.sum_mul]
    _ = (2 ^ n * M) * S := by
        rw [show (∑ l ∈ Finset.range (n + 1), (n.choose l : ℝ)) = 2 ^ n by
          exact_mod_cast Nat.sum_range_choose n]
        ring

section Rec

variable {F : ℕ → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]

/-- **Derivatives of `G i` are bounded by the higher `G k`.** -/
theorem exists_iter_le_rec {Ω K : Set E} (hΩ : UniqueDiffOn ℝ Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (P : ∀ i, F (i + 1) →L[ℝ] (E →L[ℝ] F i))
    (Q : ∀ i, E → F i →L[ℝ] (E →L[ℝ] F i)) (hQ : ∀ i, ContDiffOn ℝ ∞ (Q i) Ω) (n : ℕ) :
    ∀ i, ∃ C, 0 ≤ C ∧ ∀ G : ∀ i, E → F i, (∀ i, ContDiffOn ℝ ∞ (G i) Ω) →
      (∀ i, ∀ y ∈ Ω, fderivWithin ℝ (G i) Ω y = P i (G (i + 1) y) + Q i y (G i y)) →
      ∀ m ≤ n, ∀ y ∈ K, ‖iteratedFDerivWithin ℝ m (G i) Ω y‖ ≤
        C * ∑ k ∈ Finset.range (i + n + 1), ‖G k y‖ := by
  induction n with
  | zero =>
    intro i
    refine ⟨1, zero_le_one, fun G _ _ m hm y _ => ?_⟩
    obtain rfl : m = 0 := Nat.le_zero.mp hm
    rw [norm_iteratedFDerivWithin_zero, one_mul]
    exact Finset.single_le_sum (f := fun k => ‖G k y‖) (fun k _ => norm_nonneg _)
      (Finset.mem_range.mpr (by omega))
  | succ n ih =>
    intro i
    obtain ⟨C₀, hC₀, h₀⟩ := ih i
    obtain ⟨C₁, hC₁, h₁⟩ := ih (i + 1)
    obtain ⟨MQ, hMQ, hQb⟩ := exists_bound_iteratedFDerivWithin hΩ (hQ i) hK hKΩ n
    refine ⟨C₀ + ‖P i‖ * C₁ + 2 ^ n * (MQ * C₀), by positivity, fun G hG hrec m hm y hy => ?_⟩
    set S := ∑ k ∈ Finset.range (i + (n + 1) + 1), ‖G k y‖ with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hmono : ∑ k ∈ Finset.range (i + n + 1), ‖G k y‖ ≤ S :=
      sum_range_mono_le (fun k => norm_nonneg _) (by omega)
    have hP0 : 0 ≤ ‖P i‖ * C₁ := by positivity
    have hQ0 : 0 ≤ 2 ^ n * (MQ * C₀) := by positivity
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · have := h₀ G hG hrec m (Nat.lt_succ_iff.mp hlt) y hy
      calc _ ≤ C₀ * ∑ k ∈ Finset.range (i + n + 1), ‖G k y‖ := this
        _ ≤ C₀ * S := mul_le_mul_of_nonneg_left hmono hC₀
        _ ≤ (C₀ + ‖P i‖ * C₁ + 2 ^ n * (MQ * C₀)) * S := by nlinarith
    · obtain rfl : m = n + 1 := le_antisymm hm hge
      have hyΩ := hKΩ hy
      rw [← norm_iteratedFDerivWithin_fderivWithin hΩ hyΩ,
        iteratedFDerivWithin_congr (fun z hz => hrec i z hz) hyΩ]
      refine (norm_iter_lin_add_apply_le hΩ (P i) (hG (i + 1)) (hG i) (hQ i) hyΩ n).trans ?_
      have hA : ‖iteratedFDerivWithin ℝ n (G (i + 1)) Ω y‖ ≤ C₁ * S := by
        have := h₁ G hG hrec n le_rfl y hy
        rwa [show i + 1 + n + 1 = i + (n + 1) + 1 by omega] at this
      have hB : ∑ l ∈ Finset.range (n + 1), (n.choose l : ℝ) *
          (‖iteratedFDerivWithin ℝ l (Q i) Ω y‖ * ‖iteratedFDerivWithin ℝ (n - l) (G i) Ω y‖) ≤
          (2 ^ n * (MQ * C₀)) * S := by
        have := sum_choose_mul_le (n := n)
          (a := fun l => ‖iteratedFDerivWithin ℝ l (Q i) Ω y‖ *
            ‖iteratedFDerivWithin ℝ (n - l) (G i) Ω y‖) (M := MQ * C₀) (S := S) (by positivity)
          hS0 (fun l hl => by
            have hl' : l ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
            calc ‖iteratedFDerivWithin ℝ l (Q i) Ω y‖ *
                  ‖iteratedFDerivWithin ℝ (n - l) (G i) Ω y‖
                ≤ MQ * (C₀ * S) := mul_le_mul (hQb l hl' y hy)
                  ((h₀ G hG hrec (n - l) (Nat.sub_le _ _) y hy).trans
                    (mul_le_mul_of_nonneg_left hmono hC₀))
                  (norm_nonneg _) hMQ
              _ = MQ * C₀ * S := by ring)
          (fun l => by positivity)
        simpa only [mul_assoc] using this
      have hB' : ∑ l ∈ Finset.range (n + 1), (n.choose l : ℝ) *
          ‖iteratedFDerivWithin ℝ l (Q i) Ω y‖ * ‖iteratedFDerivWithin ℝ (n - l) (G i) Ω y‖ =
          ∑ l ∈ Finset.range (n + 1), (n.choose l : ℝ) *
          (‖iteratedFDerivWithin ℝ l (Q i) Ω y‖ * ‖iteratedFDerivWithin ℝ (n - l) (G i) Ω y‖) :=
        Finset.sum_congr rfl fun l _ => by ring
      rw [hB']
      have hPA : ‖P i‖ * ‖iteratedFDerivWithin ℝ n (G (i + 1)) Ω y‖ ≤ ‖P i‖ * C₁ * S := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hA (by positivity)
      nlinarith

/-- **Derivatives of `G i` are bounded by the derivatives of `G 0`.** -/
theorem exists_iter_le_rec_inv {Ω K : Set E} (hΩ : UniqueDiffOn ℝ Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (P' : ∀ i, (E →L[ℝ] F i) →L[ℝ] F (i + 1))
    (Q : ∀ i, E → F i →L[ℝ] (E →L[ℝ] F i)) (hQ : ∀ i, ContDiffOn ℝ ∞ (Q i) Ω) (i : ℕ) :
    ∀ N, ∃ C, 0 ≤ C ∧ ∀ G : ∀ i, E → F i, (∀ i, ContDiffOn ℝ ∞ (G i) Ω) →
      (∀ i, ∀ y ∈ Ω, G (i + 1) y = P' i (fderivWithin ℝ (G i) Ω y - Q i y (G i y))) →
      ∀ n ≤ N, ∀ y ∈ K, ‖iteratedFDerivWithin ℝ n (G i) Ω y‖ ≤
        C * ∑ m ∈ Finset.range (N + i + 1), ‖iteratedFDerivWithin ℝ m (G 0) Ω y‖ := by
  induction i with
  | zero =>
    intro N
    refine ⟨1, zero_le_one, fun G _ _ n hn y _ => ?_⟩
    rw [one_mul]
    exact Finset.single_le_sum (f := fun m => ‖iteratedFDerivWithin ℝ m (G 0) Ω y‖)
      (fun k _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
  | succ i ih =>
    intro N
    obtain ⟨C₀, hC₀, h₀⟩ := ih (N + 1)
    set Q' : E → F i →L[ℝ] F (i + 1) := fun y => -((P' i).comp (Q i y)) with hQ'
    have hQ'sm : ContDiffOn ℝ ∞ Q' Ω := by
      have h := (((ContinuousLinearMap.compL ℝ (F i) (E →L[ℝ] F i) (F (i + 1))) (P' i)).contDiff.comp_contDiffOn
        (hQ i)).neg
      exact h
    obtain ⟨MQ, hMQ, hQb⟩ := exists_bound_iteratedFDerivWithin hΩ hQ'sm hK hKΩ N
    refine ⟨‖P' i‖ * C₀ + 2 ^ N * (MQ * C₀), by positivity, fun G hG hrec n hn y hy => ?_⟩
    set S := ∑ m ∈ Finset.range (N + (i + 1) + 1), ‖iteratedFDerivWithin ℝ m (G 0) Ω y‖
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hSeq : N + 1 + i + 1 = N + (i + 1) + 1 := by omega
    have hyΩ := hKΩ hy
    have heq : EqOn (G (i + 1)) (fun y => P' i (fderivWithin ℝ (G i) Ω y) + Q' y (G i y)) Ω := by
      intro z hz
      rw [hrec i z hz, map_sub]
      simp [hQ', sub_eq_add_neg]
    have hD : ContDiffOn ℝ ∞ (fderivWithin ℝ (G i) Ω) Ω :=
      ((contDiffOn_infty_iff_fderivWithin hΩ).1 (hG i)).2
    rw [iteratedFDerivWithin_congr heq hyΩ]
    refine (norm_iter_lin_add_apply_le hΩ (P' i) hD (hG i) hQ'sm hyΩ n).trans ?_
    have hA : ‖iteratedFDerivWithin ℝ n (fderivWithin ℝ (G i) Ω) Ω y‖ ≤ C₀ * S := by
      rw [norm_iteratedFDerivWithin_fderivWithin hΩ hyΩ]
      have := h₀ G hG hrec (n + 1) (by omega) y hy
      rwa [hSeq] at this
    have hB : ∑ l ∈ Finset.range (n + 1), (n.choose l : ℝ) *
        (‖iteratedFDerivWithin ℝ l Q' Ω y‖ * ‖iteratedFDerivWithin ℝ (n - l) (G i) Ω y‖) ≤
        (2 ^ n * (MQ * C₀)) * S := by
      refine sum_choose_mul_le (by positivity) hS0 (fun l hl => ?_) (fun l => by positivity)
      have hl' : l ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
      have h2 := h₀ G hG hrec (n - l) (by omega) y hy
      rw [hSeq] at h2
      calc ‖iteratedFDerivWithin ℝ l Q' Ω y‖ * ‖iteratedFDerivWithin ℝ (n - l) (G i) Ω y‖
          ≤ MQ * (C₀ * S) := mul_le_mul (hQb l (hl'.trans hn) y hy) h2 (norm_nonneg _) hMQ
        _ = MQ * C₀ * S := by ring
    have hB' : ∑ l ∈ Finset.range (n + 1), (n.choose l : ℝ) *
        ‖iteratedFDerivWithin ℝ l Q' Ω y‖ * ‖iteratedFDerivWithin ℝ (n - l) (G i) Ω y‖ =
        ∑ l ∈ Finset.range (n + 1), (n.choose l : ℝ) *
        (‖iteratedFDerivWithin ℝ l Q' Ω y‖ * ‖iteratedFDerivWithin ℝ (n - l) (G i) Ω y‖) :=
      Finset.sum_congr rfl fun l _ => by ring
    rw [hB']
    have h2n : (2 : ℝ) ^ n ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hn
    have hPA : ‖P' i‖ * ‖iteratedFDerivWithin ℝ n (fderivWithin ℝ (G i) Ω) Ω y‖ ≤
        ‖P' i‖ * C₀ * S := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hA (by positivity)
    have hB2 : (2 ^ n * (MQ * C₀)) * S ≤ (2 ^ N * (MQ * C₀)) * S :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2n (by positivity)) hS0
    nlinarith

end Rec

/-! ### Multilinear maps on a spanning family -/

/-- A multilinear map is bounded by its values on a spanning family `e` with coordinate functionals
`c`. -/
theorem norm_le_sum_apply_frame {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → X) (c : ι → X →L[ℝ] ℝ) (hec : ∀ v, ∑ k, c k v • e k = v) (n : ℕ)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => X) Y) :
    ‖A‖ ≤ (∑ k, ‖c k‖) ^ n * ∑ κ : Fin n → ι, ‖A (fun m => e (κ m))‖ := by
  set Cc := ∑ k, ‖c k‖ with hCc
  have hCc0 : 0 ≤ Cc := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
  have hm : A m = A (fun i => ∑ k, c k (m i) • e k) := by
    congr 1; funext i; exact (hec (m i)).symm
  rw [hm, ContinuousMultilinearMap.map_sum]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ κ : Fin n → ι, ‖A (fun i => c (κ i) (m i) • e (κ i))‖ ≤
      (∏ i, (Cc * ‖m i‖)) * ‖A (fun i => e (κ i))‖ := by
    intro κ
    rw [ContinuousMultilinearMap.map_smul_univ, norm_smul, norm_prod]
    refine mul_le_mul_of_nonneg_right (Finset.prod_le_prod (fun i _ => norm_nonneg _)
      fun i _ => ?_) (norm_nonneg _)
    calc ‖c (κ i) (m i)‖ ≤ ‖c (κ i)‖ * ‖m i‖ := (c (κ i)).le_opNorm _
      _ ≤ Cc * ‖m i‖ := mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (f := fun k => ‖c k‖) (fun _ _ => norm_nonneg _)
            (Finset.mem_univ _)) (norm_nonneg _)
  calc ∑ κ : Fin n → ι, ‖A (fun i => c (κ i) (m i) • e (κ i))‖
      ≤ ∑ κ : Fin n → ι, (∏ i, (Cc * ‖m i‖)) * ‖A (fun i => e (κ i))‖ :=
        Finset.sum_le_sum fun κ _ => hterm κ
    _ = Cc ^ n * (∑ κ : Fin n → ι, ‖A (fun m => e (κ m))‖) * ∏ i, ‖m i‖ := by
        rw [← Finset.mul_sum, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
        ring

end ShortTime.JetRec
