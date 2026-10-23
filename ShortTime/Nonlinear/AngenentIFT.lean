import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Angenent's trick, abstract form

Paper: `prop:regularity`, Steps 1–2.

Let `A : X → Y` be continuous linear, `𝒩 : X → Y`, `W ∈ X`, `Z ⊆ X` a complete subspace, and
`G(v) = A(W + v) - 𝒩(W + v)` on `Z`. Let `P σ : X → X`, `Q σ : Y → Y` (`σ ∈ Λ`) be families of
continuous linear maps with `P 0 = id`, `Q 0 = id`, `P σ Z ⊆ Z`, `Q σ ∘ A = A ∘ P σ`, `‖P σ‖`
locally bounded, and `𝒩'(σ, ·)` a family of maps with the naturality `𝒩'(σ, P σ u) = Q σ (𝒩 u)`.
If `𝒩'` is `C^k` (`k ≥ 1`) on a neighbourhood of `(0, W)`, `σ ↦ P σ W` is `C^k` and
`A - D𝒩(W) : Z → Y` is an isomorphism, then for small `v ∈ Z` and small `σ`:

  `σ ↦ Q σ (G v)` is `C^k` at `σ`  ⟹  `σ ↦ P σ v` is `C^k` at `σ`
  (`exists_contDiffAt_of_natural`).

Proof: `H(σ, z) = A(P σ W + z) - 𝒩'(σ, P σ W + z)` satisfies `H(σ, P σ v) = Q σ (G v)`, and
`K(σ, z) = (σ, H(σ, z))` is a local `C^k` diffeomorphism near `(0, 0)` (inverse function theorem).
The derivative of `K` stays invertible near `(0, 0)`, so the local inverse is `C^k` at every point
`K(σ, P σ v)` with `(σ, P σ v)` near `(0, 0)`, and `(σ, P σ v) = K⁻¹(σ, Q σ (G v))`.
-/

noncomputable section

open Set Filter Topology Metric

namespace ShortTime

namespace Angenent

variable {Λ X Y : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [CompleteSpace Λ]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- `(a, b) ↦ (a, L (a, b))` is an equivalence when `b ↦ L (0, b)` is one. -/
def graphEquiv (Z : Submodule ℝ X) (L : Λ × Z →L[ℝ] Y) (Φ : Z ≃L[ℝ] Y)
    (hL : ∀ b : Z, L (0, b) = Φ b) : (Λ × Z) ≃L[ℝ] (Λ × Y) :=
  ContinuousLinearEquiv.equivOfInverse ((ContinuousLinearMap.fst ℝ Λ Z).prod L)
    ((ContinuousLinearMap.fst ℝ Λ Y).prod ((Φ.symm : Y →L[ℝ] Z).comp
      (ContinuousLinearMap.snd ℝ Λ Y -
        L.comp ((ContinuousLinearMap.inl ℝ Λ Z).comp (ContinuousLinearMap.fst ℝ Λ Y)))))
    (fun q => by
      obtain ⟨a, b⟩ := q
      have h : L (a, b) - L (a, 0) = Φ b := by
        rw [← map_sub, Prod.mk_sub_mk, sub_self, sub_zero, hL]
      change (a, Φ.symm (L (a, b) - L (a, 0))) = (a, b)
      rw [h, ContinuousLinearEquiv.symm_apply_apply])
    (fun q => by
      obtain ⟨a, y⟩ := q
      change (a, L (a, Φ.symm (y - L (a, 0)))) = (a, y)
      have h : L (a, Φ.symm (y - L (a, 0))) = L (a, 0) + L (0, Φ.symm (y - L (a, 0))) := by
        rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
      rw [h, hL, ContinuousLinearEquiv.apply_symm_apply, add_sub_cancel])

theorem graphEquiv_coe (Z : Submodule ℝ X) (L : Λ × Z →L[ℝ] Y) (Φ : Z ≃L[ℝ] Y)
    (hL : ∀ b : Z, L (0, b) = Φ b) :
    (graphEquiv Z L Φ hL : (Λ × Z) →L[ℝ] (Λ × Y)) = (ContinuousLinearMap.fst ℝ Λ Z).prod L :=
  rfl

theorem lt_of_mul_lt_aux {C a ε : ℝ} (hC : 0 < C) (ha : a < ε / C) : C * a < ε := by
  rwa [lt_div_iff₀ hC, mul_comm] at ha

/-- **Angenent's trick, abstract form.** See the module docstring. -/
theorem exists_contDiffAt_of_natural (Z : Submodule ℝ X) [CompleteSpace Z]
    (A : X →L[ℝ] Y) (P : Λ → X →L[ℝ] X) (Q : Λ → Y →L[ℝ] Y) (W : X) (𝒩 : X → Y)
    (𝒩' : Λ × X → Y) {k : WithTop ℕ∞} (hk : k ≠ 0) {r : ℝ} (hr : 0 < r)
    (h𝒩' : ContDiffOn ℝ k 𝒩' (ball ((0 : Λ), W) r))
    (hPW : ContDiff ℝ k fun σ => P σ W)
    (hP0 : P 0 = ContinuousLinearMap.id ℝ X) (hQ0 : Q 0 = ContinuousLinearMap.id ℝ Y)
    (hPZ : ∀ σ, ∀ z ∈ Z, P σ z ∈ Z)
    {ρ₀ C : ℝ} (hρ₀ : 0 < ρ₀) (hPb : ∀ σ : Λ, ‖σ‖ < ρ₀ → ∀ x, ‖P σ x‖ ≤ C * ‖x‖)
    (hA : ∀ σ x, Q σ (A x) = A (P σ x))
    {ρ₁ r₁ : ℝ} (hρ₁ : 0 < ρ₁) (hr₁ : 0 < r₁)
    (hnat : ∀ σ : Λ, ‖σ‖ < ρ₁ → ∀ u, dist u W < r₁ → 𝒩' (σ, P σ u) = Q σ (𝒩 u))
    (Φ : Z ≃L[ℝ] Y) (hΦ : ∀ z : Z, Φ z = A z - fderiv ℝ 𝒩 W z) :
    ∃ V ∈ 𝓝 (0 : Z), ∃ ρ > 0, ∀ v ∈ V, ∀ σ ∈ ball (0 : Λ) ρ,
      ContDiffAt ℝ k (fun τ => Q τ (A (W + v) - 𝒩 (W + v))) σ →
        ContDiffAt ℝ k (fun τ => P τ (v : X)) σ := by
  have hk1 : 1 ≤ k := ENat.one_le_iff_ne_zero_withTop.mpr hk
  -- `𝒩 = 𝒩'(0, ·)` near `W`
  have hN0 : ∀ u, dist u W < r₁ → 𝒩' (0, u) = 𝒩 u := fun u hu => by
    have h := hnat 0 (by rw [norm_zero]; exact hρ₁) u hu
    rwa [hP0, hQ0] at h
  have hc0 : ((0 : Λ), W) ∈ ball ((0 : Λ), W) r := mem_ball_self hr
  have h𝒩'at : ContDiffAt ℝ k 𝒩' (0, W) := h𝒩'.contDiffAt (isOpen_ball.mem_nhds hc0)
  have hd𝒩' : DifferentiableAt ℝ 𝒩' (0, W) := h𝒩'at.differentiableAt hk
  have hev : 𝒩 =ᶠ[𝓝 W] 𝒩' ∘ (ContinuousLinearMap.inr ℝ Λ X) := by
    filter_upwards [ball_mem_nhds W hr₁] with u hu using (hN0 u hu).symm
  have hd𝒩 : DifferentiableAt ℝ 𝒩 W := by
    have h1 : HasFDerivAt (𝒩' ∘ (ContinuousLinearMap.inr ℝ Λ X))
        ((fderiv ℝ 𝒩' (0, W)).comp (ContinuousLinearMap.inr ℝ Λ X)) W :=
      hd𝒩'.hasFDerivAt.comp W (ContinuousLinearMap.inr ℝ Λ X).hasFDerivAt
    exact (h1.congr_of_eventuallyEq hev).differentiableAt
  -- the map `K(σ, z) = (σ, H(σ, z))`
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Λ × Z → Λ × X, ψ = fun q => (q.1, P q.1 W + (q.2 : X)) := ⟨_, rfl⟩
  have hψc : ContDiff ℝ k ψ := by
    rw [hψ]
    exact contDiff_fst.prodMk ((hPW.comp contDiff_fst).add (Z.subtypeL.contDiff.comp contDiff_snd))
  obtain ⟨H, hH⟩ : ∃ H : Λ × Z → Y, H = fun q => A (ψ q).2 - 𝒩' (ψ q) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : Λ × Z → Λ × Y, K = fun q => (q.1, H q) := ⟨_, rfl⟩
  obtain ⟨U₀, hU₀⟩ : ∃ U₀ : Set (Λ × Z), U₀ = ψ ⁻¹' ball ((0 : Λ), W) r := ⟨_, rfl⟩
  have hU₀o : IsOpen U₀ := by rw [hU₀]; exact isOpen_ball.preimage hψc.continuous
  have hψ0 : ψ 0 = ((0 : Λ), W) := by
    rw [hψ]
    simp [hP0]
  have h00 : (0 : Λ × Z) ∈ U₀ := by
    rw [hU₀, mem_preimage, hψ0]
    exact hc0
  have hHc : ContDiffOn ℝ k H U₀ := by
    rw [hH]
    have h1 : ContDiffOn ℝ k (𝒩' ∘ ψ) U₀ := h𝒩'.comp hψc.contDiffOn (fun q hq => by
      rw [hU₀] at hq; exact hq)
    exact (A.contDiff.comp (contDiff_snd.comp hψc)).contDiffOn.sub h1
  have hKc : ContDiffOn ℝ k K U₀ := by
    rw [hK]
    exact contDiffOn_fst.prodMk hHc
  have hHd : DifferentiableAt ℝ H 0 := (hHc.contDiffAt (hU₀o.mem_nhds h00)).differentiableAt hk
  -- `D_z H(0, 0) = A - D𝒩(W) = Φ`
  have hL : ∀ b : Z, fderiv ℝ H 0 (0, b) = Φ b := by
    have e1 : HasFDerivAt (H ∘ (ContinuousLinearMap.inr ℝ Λ Z))
        ((fderiv ℝ H 0).comp (ContinuousLinearMap.inr ℝ Λ Z)) 0 := by
      have h := hHd.hasFDerivAt
      rw [← map_zero (ContinuousLinearMap.inr ℝ Λ Z)] at h
      exact h.comp (0 : Z) (ContinuousLinearMap.inr ℝ Λ Z).hasFDerivAt
    have haff : HasFDerivAt (fun v : Z => W + (v : X)) Z.subtypeL (0 : Z) :=
      Z.subtypeL.hasFDerivAt.const_add W
    have h0 : W + ((0 : Z) : X) = W := by rw [Submodule.coe_zero, add_zero]
    have hd : HasFDerivAt 𝒩 (fderiv ℝ 𝒩 W) (W + ((0 : Z) : X)) := by
      rw [h0]; exact hd𝒩.hasFDerivAt
    have e2 := (A.hasFDerivAt.comp (0 : Z) haff).sub (hd.comp (0 : Z) haff)
    have e3 : H ∘ (ContinuousLinearMap.inr ℝ Λ Z) =ᶠ[𝓝 0]
        fun z : Z => (⇑A ∘ fun v : Z => W + (v : X)) z - (𝒩 ∘ fun v : Z => W + (v : X)) z := by
      filter_upwards [ball_mem_nhds (0 : Z) hr₁] with z hz
      have hz' : dist (W + (z : X)) W < r₁ := by
        rw [dist_eq_norm, add_sub_cancel_left]
        rw [mem_ball, dist_zero_right] at hz
        exact hz
      simp only [Function.comp_apply, ContinuousLinearMap.inr_apply, hH, hψ, hP0,
        ContinuousLinearMap.id_apply]
      rw [hN0 _ hz']
    have e4 := e1.unique (e2.congr_of_eventuallyEq e3)
    intro b
    have e5 := congrArg (fun T : Z →L[ℝ] Y => T b) e4
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      ContinuousLinearMap.sub_apply] at e5
    rw [e5, hΦ]
    rfl
  -- the inverse function theorem at `(0, 0)`
  set e := graphEquiv Z (fderiv ℝ H 0) Φ hL with he
  have hKd : HasFDerivAt K (e : (Λ × Z) →L[ℝ] (Λ × Y)) 0 := by
    rw [he, graphEquiv_coe, hK]
    exact hasFDerivAt_fst.prodMk hHd.hasFDerivAt
  have hKat : ContDiffAt ℝ k K 0 := hKc.contDiffAt (hU₀o.mem_nhds h00)
  have hs : HasStrictFDerivAt K (e : (Λ × Z) →L[ℝ] (Λ × Y)) 0 := hKat.hasStrictFDerivAt' hKd hk
  set h := hs.toOpenPartialHomeomorph K with hdef
  have hcoe : (h : Λ × Z → Λ × Y) = K := hs.toOpenPartialHomeomorph_coe
  -- the good set: `K` is `C^k` with invertible derivative
  have hfc : ContinuousOn (fderiv ℝ K) U₀ := hKc.continuousOn_fderiv_of_isOpen hU₀o hk1
  have hGo : IsOpen ((U₀ ∩ fderiv ℝ K ⁻¹'
      range ((↑) : ((Λ × Z) ≃L[ℝ] (Λ × Y)) → (Λ × Z) →L[ℝ] (Λ × Y))) ∩ h.source) :=
    (hfc.isOpen_inter_preimage hU₀o ContinuousLinearEquiv.isOpen).inter h.open_source
  have hG0 : (0 : Λ × Z) ∈ (U₀ ∩ fderiv ℝ K ⁻¹'
      range ((↑) : ((Λ × Z) ≃L[ℝ] (Λ × Y)) → (Λ × Z) →L[ℝ] (Λ × Y))) ∩ h.source :=
    ⟨⟨h00, e, hKd.fderiv.symm⟩, hs.mem_toOpenPartialHomeomorph_source⟩
  obtain ⟨ε, hε, hεG⟩ := Metric.isOpen_iff.mp hGo 0 hG0
  have hsymm : ∀ q ∈ ball (0 : Λ × Z) ε, ContDiffAt ℝ k h.symm (K q) := by
    intro q hq
    obtain ⟨⟨hqU, ⟨eq, heq⟩⟩, hqs⟩ := hεG hq
    have hKq : ContDiffAt ℝ k K q := hKc.contDiffAt (hU₀o.mem_nhds hqU)
    have hdq : HasFDerivAt K (eq : (Λ × Z) →L[ℝ] (Λ × Y)) q := by
      rw [heq]; exact (hKq.differentiableAt hk).hasFDerivAt
    have hinv : h.symm (K q) = q := by
      rw [← hcoe]; exact h.left_inv hqs
    refine h.contDiffAt_symm (f₀' := eq) ?_ ?_ ?_
    · rw [← hcoe]; exact h.map_source hqs
    · rw [hinv, hcoe]; exact hdq
    · rw [hinv, hcoe]; exact hKq
  -- the neighbourhoods
  set C' := max C 0 + 1 with hC'def
  have hC' : 0 < C' := by positivity
  have hCC' : C ≤ C' := (le_max_left C 0).trans (le_add_of_nonneg_right zero_le_one)
  refine ⟨ball (0 : Z) (min (ε / C') r₁), ball_mem_nhds _ (lt_min (div_pos hε hC') hr₁),
    min ε (min ρ₀ ρ₁), lt_min hε (lt_min hρ₀ hρ₁), fun v hv σ₀ hσ₀ hy => ?_⟩
  rw [mem_ball, dist_zero_right] at hv
  have hvε : ‖v‖ < ε / C' := hv.trans_le (min_le_left _ _)
  have hvr : ‖v‖ < r₁ := hv.trans_le (min_le_right _ _)
  set y := A (W + v) - 𝒩 (W + v) with hydef
  have key : ∀ σ ∈ ball (0 : Λ) (min ε (min ρ₀ ρ₁)),
      ((σ, (⟨P σ v, hPZ σ v v.2⟩ : Z)) : Λ × Z) ∈ ball (0 : Λ × Z) ε ∧
      K (σ, ⟨P σ v, hPZ σ v v.2⟩) = (σ, Q σ y) := by
    intro σ hσ
    rw [mem_ball, dist_zero_right] at hσ
    have hσε : ‖σ‖ < ε := hσ.trans_le (min_le_left _ _)
    have hσ0 : ‖σ‖ < ρ₀ := hσ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hσ1 : ‖σ‖ < ρ₁ := hσ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    constructor
    · rw [mem_ball, dist_zero_right, Prod.norm_def]
      refine max_lt hσε ?_
      have h1 : ‖P σ v‖ ≤ C' * ‖v‖ :=
        (hPb σ hσ0 v).trans (mul_le_mul_of_nonneg_right hCC' (norm_nonneg _))
      exact h1.trans_lt (lt_of_mul_lt_aux hC' hvε)
    · have hu : dist (W + (v : X)) W < r₁ := by
        rw [dist_eq_norm, add_sub_cancel_left]; exact hvr
      have e1 := hnat σ hσ1 _ hu
      rw [hK, hH, hψ]
      simp only
      rw [← map_add, e1, ← hA, ← map_sub]
  obtain ⟨hq0, hK0⟩ := key σ₀ hσ₀
  have hsm := hsymm _ hq0
  rw [hK0] at hsm
  have hcomp : ContDiffAt ℝ k (fun τ => Z.subtypeL ((h.symm (τ, Q τ y)).2)) σ₀ :=
    Z.subtypeL.contDiff.contDiffAt.comp σ₀
      (contDiffAt_snd.comp σ₀ (hsm.comp σ₀ (contDiffAt_id.prodMk hy)))
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ball.mem_nhds hσ₀] with τ hτ
  obtain ⟨hqτ, hKτ⟩ := key τ hτ
  have hinv : h.symm (τ, Q τ y) = (τ, ⟨P τ v, hPZ τ v v.2⟩) := by
    rw [← hKτ, ← hcoe]
    exact h.left_inv (hεG hqτ).2
  rw [hinv]
  rfl

end Angenent

end ShortTime
