import ShortTime.Nonlinear.AngenentNaturalCore
import ShortTime.Nonlinear.UniformTubeParam

/-!
# Angenent's trick for the abstract solution (`prop:regularity`, Step: smoothness in `σ`)

In the setting of `EquationData.parabolicSpace_solution_smooth`, for any family of vector fields `B`
(flow data) there are a neighbourhood `V` of `0` in `𝒫^m_0` and `ρ > 0` such that every `v ∈ V` with
`G(v) = ∂ₜ(w + v) - 𝒩(w + v)` equal to a smooth family `f` has `σ ↦ Π^B_σ v` of class `C^∞` on
`ball 0 ρ` (`exists_iterPull_contDiffOn`). This is exactly the `hflow` input of
`SmoothRep.exists_smooth_rep`, apart from the choice of the frame `B`.

The neighbourhood `V` depends on `B`: it comes from the implicit function theorem for the parametric
operator of `iterFM B`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter Topology Metric
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open scoped Manifold ContDiff

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

variable {g : SmoothRiemannianMetric I M}

namespace EquationData

variable {s p : ℕ}

open ParabolicSpace HFlow

/-- **`σ ↦ Π_σ v` is `C^∞` on a ball** (Angenent's trick, concrete form). Hypotheses as in
`parabolicSpace_solution_smooth`; `B` is any finite family of smooth vector fields. -/
theorem exists_iterPull_contDiffOn (D : EquationData I M 0 s p) (hp : 1 ≤ p)
    {m : ℕ} (hm : Module.finrank ℝ E / (2 * p) + 4 ≤ m) (hm1 : 1 ≤ m)
    {T₁ : ℝ} (hT₁ : 0 < T₁) (hT₁D : T₁ ≤ D.T₀) {lam : ℝ}
    {w : ℝ → SmoothCcTensor g 0 s} (hw : JointlySmoothOn g 0 s (Icc 0 T₁) w)
    (hleg : ∀ t ∈ Icc (0 : ℝ) T₁, ∀ x : M, covJet g 0 s (2 * p) (w t) x ∈ D.dom t x ∧
      LegendreAt g 0 s p x (D.principal t x (covJet g 0 s (2 * p) (w t) x)) lam)
    {δ : ℝ} (hδ : 0 < δ)
    {𝒩 : ParabolicSpace g s p m T₁ → ParabolicSpace g s p (m - 1) T₁}
    (h𝒩 : ContDiffAt ℝ ∞ 𝒩 (ofSmooth w hw))
    (hagree : ∀ u (hu : JointlySmoothOn g 0 s (Icc 0 T₁) u),
      dist (ofSmooth (p := p) (m := m) u hu) (ofSmooth w hw) < δ →
      (∀ t ∈ Icc (0 : ℝ) T₁, ∀ x : M, covJet g 0 s (2 * p) (u t) x ∈ D.dom t x) ∧
      ∃ hF, 𝒩 (ofSmooth u hu) = ofSmooth (D.nonlinFamily u) hF)
    (hL : ∃ L : LinearOp g s p T₁, L.IsParabolic lam ∧
      (∀ k t, t ∈ Icc (0 : ℝ) T₁ → ∀ x,
        opFieldHom ((L.coeff k t).toSection x) =
          D.partialDeriv k t x (covJet g 0 s (2 * p) (w t) x)) ∧
      ∀ h (hh : JointlySmoothOn g 0 s (Icc 0 T₁) h), ∃ hL,
        fderiv ℝ 𝒩 (ofSmooth w hw) (ofSmooth h hh) =
          ofSmooth (fun t => L.apply t (h t)) hL)
    {n : ℕ} (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∃ V ∈ 𝓝 (0 : zeroAtStart g s p m T₁), ∃ ρ > 0, ∀ v ∈ V,
      ∀ (f : ℝ → SmoothCcTensor g 0 s) (hf : JointlySmoothOn g 0 s (Icc 0 T₁) f),
        existenceMap hT₁ hm1 𝒩 (ofSmooth w hw) v = ofSmooth f hf →
        ContDiffOn ℝ ∞ (fun σ => iterPullExt g s p m T₁ B σ (v : ParabolicSpace g s p m T₁))
          (ball (0 : Fin n → ℝ) ρ) := by
  obtain ⟨L, hLpar, hLc, hLd⟩ := hL
  obtain ⟨Φ, hΦ⟩ := L.isomorphism hp hT₁ hLpar m hm1
  have hdec : timeDerivExt hT₁ hm1 - fderiv ℝ 𝒩 (ofSmooth w hw) = L.heatExt hT₁ hm1 :=
    timeDerivExt_sub_eq_heatExt hT₁ hm1 L _ hLd
  have hΦW : ∀ z : zeroAtStart g s p m T₁,
      Φ z = timeDerivExt hT₁ hm1 z - fderiv ℝ 𝒩 (ofSmooth w hw) z := fun z => by
    rw [← sub_apply, hdec]
    exact L.isomorphism_eq_heatExt hT₁ hm1 Φ hΦ z
  have hwdom : ∀ t ∈ Icc (0 : ℝ) T₁, ∀ x : M,
      covJet g 0 s (2 * p) (w t) x ∈ (iterFM B g D).dom 0 t x := fun t ht x => by
    rw [iterFM_dom_zero]
    exact (hleg t ht x).1
  obtain ⟨δ', hδ', 𝒩', hball, hpar, -⟩ := FibreMap.exists_nonlinOp_param_ball (iterFM B g D) hp
    hT₁ (by rw [iterFM_T₀]; exact hT₁D) hm hw hwdom
  obtain ⟨V, hV, ρ, hρ, hreg⟩ := Angenent.regularity_core g D hp hT₁ hT₁D hm1 B hw hδ 𝒩 h𝒩
    hagree hδ' 𝒩' hball hpar Φ hΦW
  refine ⟨V, hV, ρ, hρ, fun v hv f hf hG => ?_⟩
  intro σ hσ
  refine ((hreg v hv σ hσ ?_).contDiffWithinAt)
  have hfun : (fun τ => iterPullExt g s p (m - 1) T₁ B τ
      (timeDerivExt (p := p) hT₁ hm1 (ofSmooth w hw + (v : ParabolicSpace g s p m T₁)) -
        𝒩 (ofSmooth w hw + (v : ParabolicSpace g s p m T₁)))) =
      fun τ => iterPullExt g s p (m - 1) T₁ B τ (ofSmooth f hf) := by
    funext τ
    rw [← hG]
    rfl
  rw [hfun]
  exact (contDiff_iterPullExt_ofSmooth g s hp hT₁ B hf (m - 1)).contDiffAt

end EquationData

end ShortTime
