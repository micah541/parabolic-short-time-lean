import ShortTime.Nonlinear.SmoothRepEuclid
import ShortTime.Analysis.UniformLimit

/-!
# Euclidean tools for the time bootstrap of the continuous representative

Pure analysis, no manifolds (stage 1 of `htime`, see `SmoothRepTime.lean`):

* `SpC.mono_set`: the class `SpC` restricts to smaller spatial sets.
* `hasDerivWithinAt_of_tendstoUniformlyOn_Icc`: derivative of a uniform limit on an interval.
* `hasFDerivAt_limit_rec`: the first-order recursion `D f = A (h) + K f` of chart readings of
  covariant jets passes to uniform limits on a convex open set.
-/

noncomputable section

open Set Filter Topology Metric
open scoped ContDiff

namespace ShortTime

namespace SpatialReg

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ} {S : Set ℝ} {U : Set E}

/-- `SpC` restricts to smaller spatial sets. -/
theorem SpC.mono_set {U' : Set E} (hU : U' ⊆ U) (n : ℕ) : ∀ {V : Type u} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {φ : ℝ → E → V}, SpC k S U n V φ → SpC k S U' n V φ := by
  induction n with
  | zero =>
    intro V _ _ φ h
    exact (show ContDiffOn ℝ k (fun q : ℝ × E => φ q.1 q.2) (S ×ˢ U) from h).mono
      (prod_mono subset_rfl hU)
  | succ n ih =>
    intro V _ _ φ h
    exact ⟨h.1.mono (prod_mono subset_rfl hU), fun t ht y hy => h.2.1 t ht y (hU hy),
      ih h.2.2⟩

end SpatialReg

section Limits

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_smulRight_one_sub (a b : F) :
    ‖(1 : ℝ →L[ℝ] ℝ).smulRight a - (1 : ℝ →L[ℝ] ℝ).smulRight b‖ = ‖a - b‖ := by
  have : (1 : ℝ →L[ℝ] ℝ).smulRight a - (1 : ℝ →L[ℝ] ℝ).smulRight b =
      (1 : ℝ →L[ℝ] ℝ).smulRight (a - b) := by
    ext
    simp
  rw [this, ContinuousLinearMap.norm_smulRight_apply, norm_one, one_mul]

/-- **Derivative of a uniform limit on an interval.** -/
theorem hasDerivWithinAt_of_tendstoUniformlyOn_Icc {a b : ℝ} {f f' : ℕ → ℝ → F} {g g' : ℝ → F}
    (hf : ∀ n, ∀ x ∈ Icc a b, HasDerivWithinAt (f n) (f' n x) (Icc a b) x)
    (hlim : ∀ x ∈ Icc a b, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hunif : TendstoUniformlyOn f' g' atTop (Icc a b)) (hcont : ContinuousOn g' (Icc a b))
    {x : ℝ} (hx : x ∈ Icc a b) : HasDerivWithinAt g (g' x) (Icc a b) x := by
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
  refine hasFDerivWithinAt_of_tendstoUniformlyOn_convex (convex_Icc a b)
    (f' := fun n x => (1 : ℝ →L[ℝ] ℝ).smulRight (f' n x))
    (g' := fun x => (1 : ℝ →L[ℝ] ℝ).smulRight (g' x))
    (fun n y hy => (hasDerivWithinAt_iff_hasFDerivWithinAt.1 (hf n y hy))) hlim ?_ ?_ hx
  · rw [Metric.tendstoUniformlyOn_iff] at hunif ⊢
    intro ε hε
    filter_upwards [hunif ε hε] with n hn y hy
    rw [dist_eq_norm, norm_smulRight_one_sub, ← dist_eq_norm]
    exact hn y hy
  · exact ((ContinuousLinearMap.smulRightL ℝ ℝ F (1 : ℝ →L[ℝ] ℝ)).continuous.comp_continuousOn
      hcont)

end Limits

section Rec

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

theorem mul_lt_half_aux {a d ε : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) (hε : 0 < ε)
    (h : d < ε / (2 * (a + 1))) : a * d < ε / 2 := by
  have h1 : a * d ≤ (a + 1) * d := by nlinarith
  have h2 : (a + 1) * d < (a + 1) * (ε / (2 * (a + 1))) :=
    mul_lt_mul_of_pos_left h (by linarith)
  have h3 : (a + 1) * (ε / (2 * (a + 1))) = ε / 2 := by
    field_simp
  linarith

/-- **The recursion `D f = A h + K f` passes to uniform limits** on a convex open set. -/
theorem hasFDerivAt_limit_rec {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    (A : G →L[ℝ] (E →L[ℝ] F)) (K : E → F →L[ℝ] (E →L[ℝ] F)) {C : ℝ}
    (hKb : ∀ y ∈ U, ‖K y‖ ≤ C) (hKc : ContinuousOn K U)
    {f : ℕ → E → F} {h : ℕ → E → G} {f0 : E → F} {h0 : E → G}
    (hf : ∀ n, ∀ y ∈ U, HasFDerivAt (f n) (A (h n y) + K y (f n y)) y)
    (hfl : TendstoUniformlyOn f f0 atTop U) (hhl : TendstoUniformlyOn h h0 atTop U)
    (hc : ContinuousOn f0 U) (hch : ContinuousOn h0 U) :
    ∀ y ∈ U, HasFDerivAt f0 (A (h0 y) + K y (f0 y)) y := by
  intro y hy
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hunif : TendstoUniformlyOn (fun n z => A (h n z) + K z (f n z))
      (fun z => A (h0 z) + K z (f0 z)) atTop U := by
    rw [Metric.tendstoUniformlyOn_iff] at hhl hfl ⊢
    intro ε hε
    have hδ1 : 0 < ε / (2 * (‖A‖ + 1)) := by positivity
    have hδ2 : 0 < ε / (2 * (max C 0 + 1)) := by positivity
    filter_upwards [hhl _ hδ1, hfl _ hδ2] with n hn1 hn2 z hz
    have e1 : ‖A (h0 z - h n z)‖ ≤ ‖A‖ * ‖h0 z - h n z‖ := A.le_opNorm _
    have e2 : ‖K z (f0 z - f n z)‖ ≤ ‖K z‖ * ‖f0 z - f n z‖ := (K z).le_opNorm _
    have d1 := hn1 z hz
    have d2 := hn2 z hz
    rw [dist_eq_norm] at d1 d2 ⊢
    have i1 := mul_lt_half_aux (norm_nonneg A) (norm_nonneg _) hε d1
    have i2 := mul_lt_half_aux hC0 (norm_nonneg _) hε d2
    have i3 : ‖K z‖ * ‖f0 z - f n z‖ ≤ max C 0 * ‖f0 z - f n z‖ :=
      mul_le_mul_of_nonneg_right ((hKb z hz).trans (le_max_left _ _)) (norm_nonneg _)
    have : A (h0 z) + K z (f0 z) - (A (h n z) + K z (f n z)) =
        A (h0 z - h n z) + K z (f0 z - f n z) := by
      simp only [map_sub]
      abel
    rw [this]
    calc _ ≤ ‖A (h0 z - h n z)‖ + ‖K z (f0 z - f n z)‖ := norm_add_le _ _
      _ < ε := by linarith
  have hcont : ContinuousOn (fun z => A (h0 z) + K z (f0 z)) U :=
    (A.continuous.comp_continuousOn hch).add (hKc.clm_apply hc)
  have key := hasFDerivWithinAt_of_tendstoUniformlyOn_convex hconv
    (f := f) (f' := fun n z => A (h n z) + K z (f n z)) (g := f0)
    (g' := fun z => A (h0 z) + K z (f0 z)) (fun n z hz => (hf n z hz).hasFDerivWithinAt)
    (fun z hz => hfl.tendsto_at hz) hunif hcont hy
  exact key.hasFDerivAt (hU.mem_nhds hy)

/-- As `hasFDerivAt_limit_rec`, with `K` continuous on a compact set containing `U` (so it is
bounded there). -/
theorem hasFDerivAt_limit_rec_compact {U Kc : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    (hUK : U ⊆ Kc) (hKc : IsCompact Kc)
    (A : G →L[ℝ] (E →L[ℝ] F)) (K : E → F →L[ℝ] (E →L[ℝ] F))
    (hKcont : ContinuousOn K Kc)
    {f : ℕ → E → F} {h : ℕ → E → G} {f0 : E → F} {h0 : E → G}
    (hf : ∀ n, ∀ y ∈ U, HasFDerivAt (f n) (A (h n y) + K y (f n y)) y)
    (hfl : TendstoUniformlyOn f f0 atTop U) (hhl : TendstoUniformlyOn h h0 atTop U)
    (hc : ContinuousOn f0 U) (hch : ContinuousOn h0 U) :
    ∀ y ∈ U, HasFDerivAt f0 (A (h0 y) + K y (f0 y)) y := by
  obtain ⟨C, hC⟩ : ∃ C, ∀ y ∈ Kc, ‖K y‖ ≤ C :=
    IsCompact.exists_bound_of_continuousOn hKc (f := K) hKcont
  exact hasFDerivAt_limit_rec hU hconv A K (C := C) (fun y hy => hC y (hUK hy))
    (hKcont.mono hUK) hf hfl hhl hc hch

end Rec

end ShortTime
