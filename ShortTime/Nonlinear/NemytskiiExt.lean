import ShortTime.Analysis.SmoothExtension

/-!
# Smooth extension from a dense subspace, at finite order and at a point

`ShortTime.SmoothExtension.exists_contDiffOn_extension` needs the bounds (M), (T) for *all* orders
`k` on one ball. The composition estimates of `prop:nemytskii` give them on a ball whose radius may
depend on `k`. This file gives:

* `exists_contDiffOn_extension_of_le`: bounds (M) for `k ≤ n + 1` and (T) for `k ≤ n` on a ball give
  a `C^n` extension of `g 0` on that ball.
* `eqOn_of_continuousOn_of_dense`: two continuous extensions agree.
* `exists_contDiffAt_extension`: if for every `n` the bounds up to order `n` hold on some ball, then
  the continuous extension of `g 0` (on the ball of order `0`) is `C^∞` at the centre, with
  derivative `g 1` there.
-/

open Set Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace ShortTime.SmoothExtension

variable {X₀ : Type*} [NormedAddCommGroup X₀] [NormedSpace ℝ X₀]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

variable (ι : X₀ →L[ℝ] X) (hι : ∀ x, ‖ι x‖ = ‖x‖) (hd : DenseRange ι)

include hι hd

/-- **Smooth extension at finite order.** Bounds (M) for `k ≤ n + 1` and the Taylor estimate (T)
for `k ≤ n` on `ball w δ` give a `C^n` extension of `g 0` on `ball (ι w) δ`. -/
theorem exists_contDiffOn_extension_of_le (n : ℕ) (w : X₀) (δ : ℝ)
    (g : (k : ℕ) → X₀ → ContinuousMultilinearMap ℝ (fun _ : Fin k => X₀) Y) (C : ℕ → ℝ)
    (hM : ∀ k ≤ n + 1, ∀ u ∈ ball w δ, ‖g k u‖ ≤ C k)
    (hT : ∀ k ≤ n, ∀ u ∈ ball w δ, ∀ h, u + h ∈ ball w δ →
      ‖g k (u + h) - g k u - (g (k + 1) u).curryLeft h‖ ≤ C k * ‖h‖ ^ 2) :
    ∃ f : X → Y, ContDiffOn ℝ n f (ball (ι w) δ) ∧
      (∀ u ∈ ball w δ, f (ι u) = g 0 u 0) ∧
      (1 ≤ n → ∀ u ∈ ball w δ, ∀ h : X₀, fderiv ℝ f (ι u) (ι h) = g 1 u (fun _ => h)) := by
  obtain ⟨G, hG⟩ : ∃ G : (k : ℕ) → X₀ → ContinuousMultilinearMap ℝ (fun _ : Fin k => X) Y,
      ∀ k u, G k u = extendML ι hι hd k (g k u) := ⟨_, fun _ _ => rfl⟩
  have hGM : ∀ k ≤ n + 1, ∀ u ∈ ball w δ, ‖G k u‖ ≤ C k := by
    intro k hk u hu
    rw [hG, LinearIsometryEquiv.norm_map]
    exact hM k hk u hu
  have hGT : ∀ k ≤ n, ∀ u ∈ ball w δ, ∀ h, u + h ∈ ball w δ →
      ‖G k (u + h) - G k u - (G (k + 1) u).curryLeft (ι h)‖ ≤ C k * ‖h‖ ^ 2 := by
    intro k hk u hu h huh
    rw [hG, hG, hG, ← extendML_curryLeft, ← map_sub, ← map_sub, LinearIsometryEquiv.norm_map]
    exact hT k hk u hu h huh
  have hGL : ∀ k ≤ n, ∀ u ∈ ball w δ, ∀ v ∈ ball w δ,
      ‖G k u - G k v‖ ≤ (C (k + 1) + 2 * δ * C k) * ‖u - v‖ := by
    intro k hk u hu v hv
    have hvh : v + (u - v) ∈ ball w δ := by rwa [add_sub_cancel]
    have h1 := hGT k hk v hv (u - v) hvh
    rw [add_sub_cancel] at h1
    have h2 : ‖(G (k + 1) v).curryLeft (ι (u - v))‖ ≤ C (k + 1) * ‖u - v‖ := by
      refine ((G (k + 1) v).curryLeft.le_opNorm _).trans ?_
      rw [ContinuousMultilinearMap.curryLeft_norm, hι]
      exact mul_le_mul_of_nonneg_right (hGM (k + 1) (by omega) v hv) (norm_nonneg _)
    have h3 : ‖G k u - G k v‖ ≤ ‖G k u - G k v - (G (k + 1) v).curryLeft (ι (u - v))‖ +
        ‖(G (k + 1) v).curryLeft (ι (u - v))‖ := norm_le_norm_sub_add _ _
    have hC : 0 ≤ C k := (norm_nonneg _).trans (hGM k (by omega) v hv)
    have hδ : ‖u - v‖ ≤ 2 * δ := by
      have := dist_triangle_right u v w
      rw [mem_ball] at hu hv
      rw [← dist_eq_norm]
      linarith
    exact lip_arith h3 h1 h2 hC (norm_nonneg _) hδ
  have hex : ∀ k, ∃ F : X → ContinuousMultilinearMap ℝ (fun _ : Fin k => X) Y,
      k ≤ n → ContinuousOn F (ball (ι w) δ) ∧ ∀ u ∈ ball w δ, F (ι u) = G k u := by
    intro k
    by_cases hk : k ≤ n
    · obtain ⟨F, hF1, hF2⟩ := exists_extend_of_lipschitzOn ι hι hd w δ (G k) _ (hGL k hk)
      exact ⟨F, fun _ => ⟨hF1, hF2⟩⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose F hF using hex
  have hFc : ∀ k ≤ n, ContinuousOn (F k) (ball (ι w) δ) := fun k hk => (hF k hk).1
  have hFe : ∀ k ≤ n, ∀ u ∈ ball w δ, F k (ι u) = G k u := fun k hk => (hF k hk).2
  have hFT : ∀ k < n, ∀ x ∈ ball (ι w) δ, ∀ y, x + y ∈ ball (ι w) δ →
      ‖F k (x + y) - F k x - (F (k + 1) x).curryLeft y‖ ≤ C k * ‖y‖ ^ 2 := by
    intro k hk x hx y hxy
    let S : Set (X × X) := Prod.fst ⁻¹' ball (ι w) δ ∩ (fun p => p.1 + p.2) ⁻¹' ball (ι w) δ
    have hS : IsOpen S := (isOpen_ball.preimage continuous_fst).inter
      (isOpen_ball.preimage (continuous_fst.add continuous_snd))
    have hD : Dense (range (Prod.map ι ι)) := hd.prodMap hd
    have c1 : ContinuousOn (fun p : X × X => F k (p.1 + p.2)) S :=
      (hFc k hk.le).comp (continuous_fst.add continuous_snd).continuousOn fun p hp => hp.2
    have c2 : ContinuousOn (fun p : X × X => F k p.1) S :=
      (hFc k hk.le).comp continuous_fst.continuousOn fun p hp => hp.1
    have c3 : ContinuousOn (fun p : X × X => (F (k + 1) p.1).curryLeft) S :=
      (continuous_curryLeft (k := k)).comp_continuousOn
        ((hFc (k + 1) hk).comp continuous_fst.continuousOn fun p hp => hp.1)
    have c4 : ContinuousOn (fun p : X × X => (F (k + 1) p.1).curryLeft p.2) S :=
      c3.clm_apply continuous_snd.continuousOn
    refine le_on_open_of_dense hS hD (f := fun p : X × X =>
        ‖F k (p.1 + p.2) - F k p.1 - (F (k + 1) p.1).curryLeft p.2‖)
      (g := fun p : X × X => C k * ‖p.2‖ ^ 2) ((c1.sub c2).sub c4).norm
      (continuous_const.mul (continuous_snd.norm.pow 2)).continuousOn ?_ (x, y) ⟨hx, hxy⟩
    rintro p hp ⟨⟨u, h⟩, rfl⟩
    have hu : u ∈ ball w δ := (map_mem_ball_iff ι hι).1 hp.1
    have huh : u + h ∈ ball w δ := by
      have := hp.2
      simp only [mem_preimage, Prod.map_fst, Prod.map_snd, ← map_add] at this
      exact (map_mem_ball_iff ι hι).1 this
    show ‖F k (ι u + ι h) - F k (ι u) - (F (k + 1) (ι u)).curryLeft (ι h)‖ ≤ C k * ‖ι h‖ ^ 2
    rw [← map_add, hFe k hk.le u hu, hFe k hk.le (u + h) huh, hFe (k + 1) hk u hu, hι]
    exact hGT k hk.le u hu h huh
  have hFD : ∀ k < n, ∀ x ∈ ball (ι w) δ, HasFDerivAt (F k) ((F (k + 1) x).curryLeft) x := by
    intro k hk x hx
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    have hB : ∀ᶠ y in 𝓝 (0 : X), x + y ∈ ball (ι w) δ :=
      ((continuous_const.add continuous_id).tendsto' (0 : X) x (by simp))
        (isOpen_ball.mem_nhds hx)
    have hO : (fun y => F k (x + y) - F k x - (F (k + 1) x).curryLeft y) =O[𝓝 0]
        (fun y : X => ‖y‖ ^ 2) := by
      refine Asymptotics.IsBigO.of_bound (C k) ?_
      filter_upwards [hB] with y hy
      simp only [norm_pow, norm_norm]
      exact hFT k hk x hx y hy
    exact hO.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id one_lt_two)
  have hTay : HasFTaylorSeriesUpToOn (n : ℕ∞) (fun x => (F 0 x).curry0) (fun x k => F k x)
      (ball (ι w) δ) := by
    refine ⟨fun x _ => rfl, fun m hm x hx => ?_, fun m hm => ?_⟩
    · have hm' : m < n := by exact_mod_cast hm
      exact (hFD m hm' x hx).hasFDerivWithinAt
    · have hm' : m ≤ n := by exact_mod_cast hm
      exact hFc m hm'
  refine ⟨_, hTay.contDiffOn, fun u hu => ?_, fun hn u hu h => ?_⟩
  · show (F 0 (ι u)).curry0 = _
    rw [ContinuousMultilinearMap.curry0_apply, hFe 0 (Nat.zero_le _) u hu, hG]
    rw [← extendML_apply_map ι hι hd 0 (g 0 u) 0]
    congr 1
    exact Subsingleton.elim _ _
  · have hx : ι u ∈ ball (ι w) δ := (map_mem_ball_iff ι hι).2 hu
    have hD : HasFDerivAt (fun x => (F 0 x).curry0)
        (((continuousMultilinearCurryFin0 ℝ X Y).toContinuousLinearEquiv :
          ContinuousMultilinearMap ℝ (fun _ : Fin 0 => X) Y →L[ℝ] Y).comp
          ((F 1 (ι u)).curryLeft)) (ι u) :=
      (continuousMultilinearCurryFin0 ℝ X Y).toContinuousLinearEquiv.hasFDerivAt.comp (ι u)
        (hFD 0 (by omega) (ι u) hx)
    rw [hD.fderiv, ContinuousLinearMap.comp_apply]
    show (F 1 (ι u)).curryLeft (ι h) 0 = _
    rw [ContinuousMultilinearMap.curryLeft_apply, hFe 1 hn u hu, hG,
      ← extendML_apply_map ι hι hd 1 (g 1 u) (fun _ => h)]
    congr 1
    funext i
    obtain ⟨j, hj⟩ := i
    obtain rfl : j = 0 := by omega
    exact Fin.cons_zero _ _

omit [CompleteSpace Y] in
/-- Two maps continuous on a ball of `X` that agree on the image of the ball of `X₀` agree. -/
theorem eqOn_of_continuousOn_of_dense (w : X₀) (δ : ℝ) {f f' : X → Y}
    (hf : ContinuousOn f (ball (ι w) δ)) (hf' : ContinuousOn f' (ball (ι w) δ))
    (h : ∀ u ∈ ball w δ, f (ι u) = f' (ι u)) : EqOn f f' (ball (ι w) δ) := by
  intro x hx
  have key := le_on_open_of_dense isOpen_ball hd (f := fun x => ‖f x - f' x‖) (g := fun _ => 0)
    (hf.sub hf').norm continuousOn_const (by
      rintro _ hx' ⟨u, rfl⟩
      have hu : u ∈ ball w δ := (map_mem_ball_iff ι hι).1 hx'
      show ‖f (ι u) - f' (ι u)‖ ≤ 0
      rw [h u hu, sub_self, norm_zero]) x hx
  exact sub_eq_zero.1 (norm_le_zero_iff.1 key)

/-- **Smooth extension at a point.** If for every `n` the bounds (M) for `k ≤ n + 1` and (T) for
`k ≤ n` hold on some ball around `w`, then `g 0` has a continuous extension `f` on a ball around
`ι w` which is `C^∞` at `ι w`, with derivative `g 1 w` there. -/
theorem exists_contDiffAt_extension (w : X₀)
    (g : (k : ℕ) → X₀ → ContinuousMultilinearMap ℝ (fun _ : Fin k => X₀) Y)
    (hb : ∀ n : ℕ, ∃ δ > 0, ∃ C : ℕ → ℝ,
      (∀ k ≤ n + 1, ∀ u ∈ ball w δ, ‖g k u‖ ≤ C k) ∧
      (∀ k ≤ n, ∀ u ∈ ball w δ, ∀ h, u + h ∈ ball w δ →
        ‖g k (u + h) - g k u - (g (k + 1) u).curryLeft h‖ ≤ C k * ‖h‖ ^ 2)) :
    ∃ δ > 0, ∃ f : X → Y, ContDiffAt ℝ ∞ f (ι w) ∧ ContinuousOn f (ball (ι w) δ) ∧
      (∀ u ∈ ball w δ, f (ι u) = g 0 u 0) ∧
      ∀ h : X₀, fderiv ℝ f (ι w) (ι h) = g 1 w (fun _ => h) := by
  choose δ hδ C hM hT using hb
  choose f hfc hfe hfd using fun n =>
    exists_contDiffOn_extension_of_le ι hι hd n w (δ n) g (C n) (hM n) (hT n)
  have hc : ∀ n, ContinuousOn (f n) (ball (ι w) (δ n)) := fun n => (hfc n).continuousOn
  -- all the extensions agree with `f 0` near `ι w`
  have hev : ∀ n, f 0 =ᶠ[𝓝 (ι w)] f n := by
    intro n
    have h1 := eqOn_of_continuousOn_of_dense ι hι hd w (min (δ 0) (δ n))
      ((hc 0).mono (ball_subset_ball (min_le_left _ _)))
      ((hc n).mono (ball_subset_ball (min_le_right _ _))) (fun u hu => by
        rw [hfe 0 u (ball_subset_ball (min_le_left _ _) hu),
          hfe n u (ball_subset_ball (min_le_right _ _) hu)])
    exact Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds (mem_ball_self (lt_min (hδ 0) (hδ n))))
      h1
  have hw : ∀ n, ι w ∈ ball (ι w) (δ n) := fun n => mem_ball_self (hδ n)
  refine ⟨δ 0, hδ 0, f 0, ?_, hc 0, hfe 0, fun h => ?_⟩
  · refine contDiffAt_infty.2 fun n => ?_
    exact (((hfc n).contDiffAt (isOpen_ball.mem_nhds (hw n)))).congr_of_eventuallyEq (hev n)
  · rw [(hev 1).fderiv_eq]
    exact hfd 1 le_rfl w (mem_ball_self (hδ 1)) h

end ShortTime.SmoothExtension
