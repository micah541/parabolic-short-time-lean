import Mathlib

/-!
# Smooth extension from a dense subspace

Let `ι : X₀ →L[ℝ] X` be norm-preserving with dense range (e.g. the inclusion of a space of smooth
sections into its completion). Suppose that on a ball of `X₀` we are given would-be derivatives
`g k u`, `k`-multilinear maps on `X₀`, which are bounded and satisfy a second-order Taylor estimate

  `‖g k (u + h) - g k u - (g (k+1) u).curryLeft h‖ ≤ C k * ‖h‖ ^ 2`.

Then each `g k` extends to a continuous map `F k` on the corresponding ball of `X`, with values in
multilinear maps on `X`, and `(F k)` is a Taylor series of `F 0` on the ball. In particular the
extension of `g 0` is `C^∞`.

This is used to show that composition (Nemytskii) operators, defined on smooth sections and
extended by continuity to the completions, are `C^∞`.

## Main results

* `ShortTime.SmoothExtension.extendML`: the extension of continuous multilinear maps along `ι`,
  a linear isometric equivalence.
* `ShortTime.SmoothExtension.exists_hasFTaylorSeriesUpToOn_extension`: the extended maps form a
  Taylor series on the ball.
* `ShortTime.SmoothExtension.exists_contDiffOn_extension`: the extension is `C^∞`, with its value
  and derivative on the image of `ι`.
-/

open Set Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace ShortTime.SmoothExtension

variable {X₀ : Type*} [NormedAddCommGroup X₀] [NormedSpace ℝ X₀]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-! ### Generalities -/

/-- An inequality between functions continuous on an open set, which holds on a dense subset,
holds on the whole open set. -/
theorem le_on_open_of_dense {T : Type*} [TopologicalSpace T] {S D : Set T} (hS : IsOpen S)
    (hD : Dense D) {f g : T → ℝ} (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (h : ∀ p ∈ S, p ∈ D → f p ≤ g p) : ∀ p ∈ S, f p ≤ g p := by
  intro p hp
  have hcl : p ∈ closure (S ∩ D) := hD.open_subset_closure_inter hS hp
  exact ContinuousWithinAt.closure_le hcl ((hf p hp).mono inter_subset_left)
    ((hg p hp).mono inter_subset_left) fun q hq => h q hq.1 hq.2

theorem lip_arith {x A B c d e δ : ℝ} (hx : x ≤ A + B) (hA : A ≤ c * e ^ 2) (hB : B ≤ d * e)
    (hc : 0 ≤ c) (he : 0 ≤ e) (hed : e ≤ 2 * δ) : x ≤ (d + 2 * δ * c) * e := by
  have h1 : c * e * e ≤ c * e * (2 * δ) := mul_le_mul_of_nonneg_left hed (mul_nonneg hc he)
  have h2 : c * e ^ 2 = c * e * e := by ring
  have h3 : (d + 2 * δ * c) * e = d * e + c * e * (2 * δ) := by ring
  linarith

section Ball

variable (ι : X₀ →L[ℝ] X)

theorem dist_map_eq (hι : ∀ x, ‖ι x‖ = ‖x‖) (a b : X₀) : dist (ι a) (ι b) = dist a b := by
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, hι]

theorem isUniformInducing_of_norm (hι : ∀ x, ‖ι x‖ = ‖x‖) : IsUniformInducing ι :=
  (Isometry.of_dist_eq fun a b => dist_map_eq ι hι a b).isUniformInducing

theorem map_mem_ball_iff (hι : ∀ x, ‖ι x‖ = ‖x‖) {u w : X₀} {δ : ℝ} :
    ι u ∈ ball (ι w) δ ↔ u ∈ ball w δ := by
  rw [mem_ball, mem_ball, dist_map_eq ι hι]

/-- A map which is Lipschitz on a ball of `X₀` extends continuously to the corresponding ball of
`X`. -/
theorem exists_extend_of_lipschitzOn {Z : Type*} [NormedAddCommGroup Z] [CompleteSpace Z]
    (hι : ∀ x, ‖ι x‖ = ‖x‖) (hd : DenseRange ι) (w : X₀) (δ : ℝ) (G : X₀ → Z) (L : ℝ)
    (hG : ∀ u ∈ ball w δ, ∀ v ∈ ball w δ, ‖G u - G v‖ ≤ L * ‖u - v‖) :
    ∃ F : X → Z, ContinuousOn F (ball (ι w) δ) ∧ ∀ u ∈ ball w δ, F (ι u) = G u := by
  classical
  let e : ball w δ → ball (ι w) δ := fun u => ⟨ι u, (map_mem_ball_iff ι hι).2 u.2⟩
  have he : Isometry e := Isometry.of_dist_eq fun a b => dist_map_eq ι hι a.1 b.1
  have hde : DenseRange e := by
    rw [Metric.denseRange_iff]
    rintro ⟨x, hx⟩ r hr
    have hx' : dist x (ι w) < δ := hx
    obtain ⟨u, hu⟩ := Metric.denseRange_iff.1 hd x (min r (δ - dist x (ι w)))
      (lt_min hr (by linarith))
    have hu' : ι u ∈ ball (ι w) δ := by
      show dist (ι u) (ι w) < δ
      have h1 := dist_triangle (ι u) x (ι w)
      have h2 := min_le_right r (δ - dist x (ι w))
      have h3 := dist_comm x (ι u)
      linarith
    exact ⟨⟨u, (map_mem_ball_iff ι hι).1 hu'⟩, lt_of_lt_of_le hu (min_le_left _ _)⟩
  let G' : ball w δ → Z := fun u => G u
  have hlip : LipschitzWith L.toNNReal G' := LipschitzWith.of_dist_le_mul fun a b => by
    show dist (G a) (G b) ≤ L.toNNReal * dist (a : X₀) b
    rw [dist_eq_norm, dist_eq_norm]
    exact (hG a a.2 b b.2).trans
      (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) (norm_nonneg _))
  have hui : IsUniformInducing e := he.isUniformInducing
  have hψc := (uniformContinuous_uniformly_extend hui hde hlip.uniformContinuous).continuous
  have hψe := uniformly_extend_of_ind hui hde hlip.uniformContinuous
  refine ⟨fun x => if h : x ∈ ball (ι w) δ then (hui.isDenseInducing hde).extend G' ⟨x, h⟩
    else 0, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    refine hψc.congr fun x => ?_
    show _ = (if h : (x : X) ∈ ball (ι w) δ then (hui.isDenseInducing hde).extend G' ⟨x, h⟩
      else 0)
    rw [dif_pos x.2]
  · intro u hu
    have h1 : ι u ∈ ball (ι w) δ := (map_mem_ball_iff ι hι).2 hu
    show (if h : ι u ∈ ball (ι w) δ then (hui.isDenseInducing hde).extend G' ⟨ι u, h⟩
      else 0) = G u
    rw [dif_pos h1]
    exact hψe ⟨u, hu⟩

end Ball

/-! ### Extension of multilinear maps -/

section Multilinear

variable (ι : X₀ →L[ℝ] X) (Y)

/-- Restriction of a continuous multilinear map on `X` to `X₀` along `ι`. -/
def restrictML (k : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => X) Y →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin k => X₀) Y :=
  ContinuousMultilinearMap.compContinuousLinearMapL (fun _ => ι)

variable {Y}

theorem restrictML_apply (k : ℕ) (M : ContinuousMultilinearMap ℝ (fun _ : Fin k => X) Y)
    (v : Fin k → X₀) : restrictML Y ι k M v = M (fun i => ι (v i)) := rfl

variable (hι : ∀ x, ‖ι x‖ = ‖x‖) (hd : DenseRange ι)
include hι

theorem norm_restrictML_le (k : ℕ) (M : ContinuousMultilinearMap ℝ (fun _ : Fin k => X) Y) :
    ‖restrictML Y ι k M‖ ≤ ‖M‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) fun v => ?_
  rw [restrictML_apply]
  refine (M.le_opNorm _).trans_eq ?_
  simp only [hι]

include hd

theorem norm_restrictML (k : ℕ) (M : ContinuousMultilinearMap ℝ (fun _ : Fin k => X) Y) :
    ‖restrictML Y ι k M‖ = ‖M‖ := by
  refine le_antisymm (norm_restrictML_le ι hι k M) ?_
  refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) fun v => ?_
  have hD : DenseRange (fun u : Fin k → X₀ => fun i => ι (u i)) :=
    DenseRange.piMap (fun _ => hd)
  refine hD.induction_on (p := fun v => ‖M v‖ ≤ ‖restrictML Y ι k M‖ * ∏ i, ‖v i‖) v ?_ ?_
  · exact isClosed_le (map_continuous M).norm
      (continuous_const.mul (continuous_finsetProd _ fun i _ => (continuous_apply i).norm))
  · intro u
    have := (restrictML Y ι k M).le_opNorm u
    simpa only [restrictML_apply, hι] using this

theorem restrictML_injective (k : ℕ) : Function.Injective (restrictML Y ι k) := by
  intro M M' h
  have : ‖restrictML Y ι k (M - M')‖ = 0 := by rw [map_sub, h, sub_self, norm_zero]
  rw [norm_restrictML ι hι hd] at this
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

/-- `restrictML` as a linear isometry. -/
def restrictLI (k : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => X) Y →ₗᵢ[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin k => X₀) Y :=
  ⟨(restrictML Y ι k).toLinearMap, fun M => norm_restrictML ι hι hd k M⟩

theorem restrictLI_apply (k : ℕ) (M : ContinuousMultilinearMap ℝ (fun _ : Fin k => X) Y) :
    restrictLI ι hι hd k M = restrictML Y ι k M := rfl

theorem restrictML_surjective [CompleteSpace Y] :
    ∀ k, Function.Surjective (restrictML Y ι k)
  | 0 => fun N => ⟨ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => X) (N 0), by
      ext v
      rw [restrictML_apply, ContinuousMultilinearMap.constOfIsEmpty_apply, Subsingleton.elim v 0]⟩
  | k + 1 => by
    obtain ⟨E, hE⟩ : ∃ E : ContinuousMultilinearMap ℝ (fun _ : Fin k => X₀) Y →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin k => X) Y, ∀ P, restrictML Y ι k (E P) = P := by
      let e := LinearIsometryEquiv.ofSurjective (restrictLI ι hι hd k)
        (restrictML_surjective k)
      refine ⟨e.symm.toContinuousLinearEquiv.toContinuousLinearMap, fun P => ?_⟩
      exact e.apply_symm_apply P
    intro N
    obtain ⟨φ, hφ⟩ : ∃ φ : X₀ →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => X) Y,
        ∀ x, φ x = E (N.curryLeft x) := by
      refine ⟨E.comp (N.curryLeft : X₀ →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => X₀) Y),
        fun x => ?_⟩
      rfl
    have hui := isUniformInducing_of_norm ι hι
    refine ⟨ContinuousLinearMap.uncurryLeft (Ei := fun _ : Fin (k + 1) => X) (φ.extend ι), ?_⟩
    ext v
    have h1 := DFunLike.congr_fun (hE (N.curryLeft (v 0))) (Fin.tail v)
    rw [restrictML_apply, ContinuousMultilinearMap.curryLeft_apply, Fin.cons_self_tail] at h1
    rw [restrictML_apply, ContinuousLinearMap.uncurryLeft_apply]
    refine Eq.trans ?_ h1
    rw [φ.extend_eq hd hui, hφ]
    rfl

variable [CompleteSpace Y]

/-- The extension of continuous multilinear maps along `ι`, a linear isometric equivalence. -/
def extendML (k : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => X₀) Y ≃ₗᵢ[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin k => X) Y :=
  (LinearIsometryEquiv.ofSurjective (restrictLI ι hι hd k)
    (restrictML_surjective ι hι hd k)).symm

theorem restrictML_extendML (k : ℕ) (P : ContinuousMultilinearMap ℝ (fun _ : Fin k => X₀) Y) :
    restrictML Y ι k (extendML ι hι hd k P) = P := by
  have := (LinearIsometryEquiv.ofSurjective (restrictLI ι hι hd k)
    (restrictML_surjective ι hι hd k)).apply_symm_apply P
  exact this

theorem extendML_apply_map (k : ℕ) (P : ContinuousMultilinearMap ℝ (fun _ : Fin k => X₀) Y)
    (v : Fin k → X₀) : extendML ι hι hd k P (fun i => ι (v i)) = P v := by
  exact DFunLike.congr_fun (restrictML_extendML ι hι hd k P) v

theorem extendML_curryLeft (k : ℕ)
    (N : ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => X₀) Y) (h : X₀) :
    extendML ι hι hd k (N.curryLeft h) = (extendML ι hι hd (k + 1) N).curryLeft (ι h) := by
  apply restrictML_injective ι hι hd k
  ext v
  rw [restrictML_apply, restrictML_apply, extendML_apply_map,
    ContinuousMultilinearMap.curryLeft_apply, ContinuousMultilinearMap.curryLeft_apply,
    ← extendML_apply_map ι hι hd (k + 1) N (Fin.cons h v)]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
  · simp only [Fin.cons_succ]

end Multilinear

/-! ### The main theorem -/

section Main

variable [CompleteSpace Y] (ι : X₀ →L[ℝ] X) (hι : ∀ x, ‖ι x‖ = ‖x‖) (hd : DenseRange ι)

omit [CompleteSpace Y] in
theorem continuous_curryLeft (k : ℕ) :
    Continuous (fun M : ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => X) Y =>
      M.curryLeft) :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => X) Y).continuous

include hι hd

/-- **Smooth extension from a dense subspace.** Let `ι : X₀ →L[ℝ] X` preserve norms and have
dense range. Let `g k u` (`k : ℕ`, `u` in the ball `ball w δ` of `X₀`) be `k`-multilinear maps on
`X₀`, bounded by `C k`, satisfying the Taylor estimate
`‖g k (u + h) - g k u - (g (k+1) u).curryLeft h‖ ≤ C k * ‖h‖ ^ 2`. Then the `g k` extend to
continuous maps `F k` on `ball (ι w) δ` with values in multilinear maps on `X`, and these form a
Taylor series of `F 0` on that ball. -/
theorem exists_hasFTaylorSeriesUpToOn_extension (w : X₀) (δ : ℝ)
    (g : (k : ℕ) → X₀ → ContinuousMultilinearMap ℝ (fun _ : Fin k => X₀) Y) (C : ℕ → ℝ)
    (hM : ∀ k, ∀ u ∈ ball w δ, ‖g k u‖ ≤ C k)
    (hT : ∀ k, ∀ u ∈ ball w δ, ∀ h, u + h ∈ ball w δ →
      ‖g k (u + h) - g k u - (g (k + 1) u).curryLeft h‖ ≤ C k * ‖h‖ ^ 2) :
    ∃ F : (k : ℕ) → X → ContinuousMultilinearMap ℝ (fun _ : Fin k => X) Y,
      HasFTaylorSeriesUpToOn ∞ (fun x => (F 0 x).curry0) (fun x k => F k x) (ball (ι w) δ) ∧
      (∀ k, ∀ x ∈ ball (ι w) δ, HasFDerivAt (F k) ((F (k + 1) x).curryLeft) x) ∧
      (∀ k, ∀ x ∈ ball (ι w) δ, ‖F k x‖ ≤ C k) ∧
      ∀ k, ∀ u ∈ ball w δ, ∀ v : Fin k → X₀, F k (ι u) (fun i => ι (v i)) = g k u v := by
  obtain ⟨G, hG⟩ : ∃ G : (k : ℕ) → X₀ → ContinuousMultilinearMap ℝ (fun _ : Fin k => X) Y,
      ∀ k u, G k u = extendML ι hι hd k (g k u) := ⟨_, fun _ _ => rfl⟩
  have hGM : ∀ k, ∀ u ∈ ball w δ, ‖G k u‖ ≤ C k := by
    intro k u hu
    rw [hG, LinearIsometryEquiv.norm_map]
    exact hM k u hu
  have hGT : ∀ k, ∀ u ∈ ball w δ, ∀ h, u + h ∈ ball w δ →
      ‖G k (u + h) - G k u - (G (k + 1) u).curryLeft (ι h)‖ ≤ C k * ‖h‖ ^ 2 := by
    intro k u hu h huh
    rw [hG, hG, hG, ← extendML_curryLeft, ← map_sub, ← map_sub, LinearIsometryEquiv.norm_map]
    exact hT k u hu h huh
  have hGL : ∀ k, ∀ u ∈ ball w δ, ∀ v ∈ ball w δ,
      ‖G k u - G k v‖ ≤ (C (k + 1) + 2 * δ * C k) * ‖u - v‖ := by
    intro k u hu v hv
    have hvh : v + (u - v) ∈ ball w δ := by rwa [add_sub_cancel]
    have h1 := hGT k v hv (u - v) hvh
    rw [add_sub_cancel] at h1
    have h2 : ‖(G (k + 1) v).curryLeft (ι (u - v))‖ ≤ C (k + 1) * ‖u - v‖ := by
      refine ((G (k + 1) v).curryLeft.le_opNorm _).trans ?_
      rw [ContinuousMultilinearMap.curryLeft_norm, hι]
      exact mul_le_mul_of_nonneg_right (hGM (k + 1) v hv) (norm_nonneg _)
    have h3 : ‖G k u - G k v‖ ≤ ‖G k u - G k v - (G (k + 1) v).curryLeft (ι (u - v))‖ +
        ‖(G (k + 1) v).curryLeft (ι (u - v))‖ := norm_le_norm_sub_add _ _
    have hC : 0 ≤ C k := (norm_nonneg _).trans (hGM k v hv)
    have hδ : ‖u - v‖ ≤ 2 * δ := by
      have := dist_triangle_right u v w
      rw [mem_ball] at hu hv
      rw [← dist_eq_norm]
      linarith
    exact lip_arith h3 h1 h2 hC (norm_nonneg _) hδ
  choose F hFc hFe using fun k => exists_extend_of_lipschitzOn ι hι hd w δ (G k) _ (hGL k)
  -- the Taylor estimate on the ball of `X`
  have hFT : ∀ k, ∀ x ∈ ball (ι w) δ, ∀ y, x + y ∈ ball (ι w) δ →
      ‖F k (x + y) - F k x - (F (k + 1) x).curryLeft y‖ ≤ C k * ‖y‖ ^ 2 := by
    intro k x hx y hxy
    let S : Set (X × X) := Prod.fst ⁻¹' ball (ι w) δ ∩ (fun p => p.1 + p.2) ⁻¹' ball (ι w) δ
    have hS : IsOpen S := (isOpen_ball.preimage continuous_fst).inter
      (isOpen_ball.preimage (continuous_fst.add continuous_snd))
    have hD : Dense (range (Prod.map ι ι)) := hd.prodMap hd
    have c1 : ContinuousOn (fun p : X × X => F k (p.1 + p.2)) S :=
      (hFc k).comp (continuous_fst.add continuous_snd).continuousOn fun p hp => hp.2
    have c2 : ContinuousOn (fun p : X × X => F k p.1) S :=
      (hFc k).comp continuous_fst.continuousOn fun p hp => hp.1
    have c3 : ContinuousOn (fun p : X × X => (F (k + 1) p.1).curryLeft) S :=
      (continuous_curryLeft (k := k)).comp_continuousOn
        ((hFc (k + 1)).comp continuous_fst.continuousOn fun p hp => hp.1)
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
    rw [← map_add, hFe k u hu, hFe k (u + h) huh, hFe (k + 1) u hu, hι]
    exact hGT k u hu h huh
  have hFD : ∀ k, ∀ x ∈ ball (ι w) δ, HasFDerivAt (F k) ((F (k + 1) x).curryLeft) x := by
    intro k x hx
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    have hB : ∀ᶠ y in 𝓝 (0 : X), x + y ∈ ball (ι w) δ :=
      ((continuous_const.add continuous_id).tendsto' (0 : X) x (by simp))
        (isOpen_ball.mem_nhds hx)
    have hO : (fun y => F k (x + y) - F k x - (F (k + 1) x).curryLeft y) =O[𝓝 0]
        (fun y : X => ‖y‖ ^ 2) := by
      refine Asymptotics.IsBigO.of_bound (C k) ?_
      filter_upwards [hB] with y hy
      simp only [norm_pow, norm_norm]
      exact hFT k x hx y hy
    exact hO.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id one_lt_two)
  have hFM : ∀ k, ∀ x ∈ ball (ι w) δ, ‖F k x‖ ≤ C k := by
    intro k
    refine le_on_open_of_dense isOpen_ball hd (f := fun x => ‖F k x‖) (g := fun _ => C k)
      (hFc k).norm continuousOn_const ?_
    rintro x hx ⟨u, rfl⟩
    have hu : u ∈ ball w δ := (map_mem_ball_iff ι hι).1 hx
    show ‖F k (ι u)‖ ≤ C k
    rw [hFe k u hu]
    exact hGM k u hu
  refine ⟨F, ⟨fun x _ => rfl, fun m _ x hx => (hFD m x hx).hasFDerivWithinAt,
    fun m _ => hFc m⟩, hFD, hFM, ?_⟩
  intro k u hu v
  rw [hFe k u hu, hG, extendML_apply_map]

/-- **Smoothness of the extension.** Under the hypotheses of
`exists_hasFTaylorSeriesUpToOn_extension`, `g 0` extends to a `C^∞` map `f` on `ball (ι w) δ`,
whose derivative along `ι` is given by `g 1`. -/
theorem exists_contDiffOn_extension (w : X₀) (δ : ℝ)
    (g : (k : ℕ) → X₀ → ContinuousMultilinearMap ℝ (fun _ : Fin k => X₀) Y) (C : ℕ → ℝ)
    (hM : ∀ k, ∀ u ∈ ball w δ, ‖g k u‖ ≤ C k)
    (hT : ∀ k, ∀ u ∈ ball w δ, ∀ h, u + h ∈ ball w δ →
      ‖g k (u + h) - g k u - (g (k + 1) u).curryLeft h‖ ≤ C k * ‖h‖ ^ 2) :
    ∃ f : X → Y, ContDiffOn ℝ ∞ f (ball (ι w) δ) ∧
      (∀ u ∈ ball w δ, f (ι u) = g 0 u 0) ∧
      ∀ u ∈ ball w δ, ∀ h : X₀, fderiv ℝ f (ι u) (ι h) = g 1 u (fun _ => h) := by
  obtain ⟨F, hF, hFD, -, hFg⟩ := exists_hasFTaylorSeriesUpToOn_extension ι hι hd w δ g C hM hT
  refine ⟨_, hF.contDiffOn, fun u hu => ?_, fun u hu h => ?_⟩
  · show (F 0 (ι u)).curry0 = _
    rw [ContinuousMultilinearMap.curry0_apply, ← hFg 0 u hu 0]
    congr 1
    exact Subsingleton.elim _ _
  · have hx : ι u ∈ ball (ι w) δ := (map_mem_ball_iff ι hι).2 hu
    have hD : HasFDerivAt (fun x => (F 0 x).curry0)
        (((continuousMultilinearCurryFin0 ℝ X Y).toContinuousLinearEquiv :
          ContinuousMultilinearMap ℝ (fun _ : Fin 0 => X) Y →L[ℝ] Y).comp
          ((F 1 (ι u)).curryLeft)) (ι u) :=
      (continuousMultilinearCurryFin0 ℝ X Y).toContinuousLinearEquiv.hasFDerivAt.comp (ι u)
        (hFD 0 (ι u) hx)
    rw [hD.fderiv, ContinuousLinearMap.comp_apply]
    show (F 1 (ι u)).curryLeft (ι h) 0 = _
    rw [ContinuousMultilinearMap.curryLeft_apply, ← hFg 1 u hu (fun _ => h)]
    congr 1
    funext i
    obtain ⟨j, hj⟩ := i
    obtain rfl : j = 0 := by omega
    exact Fin.cons_zero _ _

end Main

end ShortTime.SmoothExtension
