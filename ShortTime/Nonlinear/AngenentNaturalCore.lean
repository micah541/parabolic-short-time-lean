import ShortTime.Nonlinear.AngenentNatural
import ShortTime.Nonlinear.Existence

/-!
# Angenent's trick, concrete form (`prop:regularity`, Steps 1–2)

`Angenent.regularity_core` instantiates `Angenent.exists_contDiffAt_of_natural` on the parabolic
spaces: `X = 𝒫^m`, `Y = 𝒫^{m-1}`, `A = ∂ₜ`, `P σ = Π_σ` (`iterPullExt`), `Z = 𝒫^m_0`. The remaining
inputs are the parametric operator `𝒩'` (`C^∞` on a ball, agreeing with the composition operator of
`iterFM B` on smooth families) and the invertibility of `∂ₜ - D𝒩(W)` on `𝒫^m_0`.
-/

noncomputable section

open Bundle Manifold Set Filter Topology Metric
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open scoped Manifold ContDiff

set_option linter.unusedSectionVars false

namespace ShortTime

namespace Angenent

open HFlow ParabolicSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]
variable (g : SmoothRiemannianMetric I M) {s p : ℕ} {T : ℝ}

theorem regularity_core (D : EquationData I M 0 s p) (hp : 1 ≤ p) (hT : 0 < T) (hTD : T ≤ D.T₀)
    {m : ℕ} (hm1 : 1 ≤ m) {n : ℕ} (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {w : ℝ → SmoothCcTensor g 0 s} (hw : JointlySmoothOn g 0 s (Icc 0 T) w)
    {δ : ℝ} (hδ : 0 < δ) (𝒩 : ParabolicSpace g s p m T → ParabolicSpace g s p (m - 1) T)
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
    (Φ : zeroAtStart g s p m T ≃L[ℝ] ParabolicSpace g s p (m - 1) T)
    (hΦ : ∀ z : zeroAtStart g s p m T,
      Φ z = timeDerivExt (p := p) hT hm1 (z : ParabolicSpace g s p m T) -
        fderiv ℝ 𝒩 (ofSmooth w hw) (z : ParabolicSpace g s p m T)) :
    ∃ V ∈ 𝓝 (0 : zeroAtStart g s p m T), ∃ ρ > 0, ∀ v ∈ V, ∀ σ ∈ ball (0 : Fin n → ℝ) ρ,
      ContDiffAt ℝ ∞ (fun τ => iterPullExt g s p (m - 1) T B τ
        (timeDerivExt (p := p) hT hm1 (ofSmooth w hw + (v : ParabolicSpace g s p m T)) -
          𝒩 (ofSmooth w hw + (v : ParabolicSpace g s p m T)))) σ →
      ContDiffAt ℝ ∞ (fun τ => iterPullExt g s p m T B τ (v : ParabolicSpace g s p m T)) σ := by
  obtain ⟨ρ₁, hρ₁, r₁, hr₁, hnat⟩ := natural_concrete g D hT hTD B hw 𝒩 h𝒩 hagree hδ' 𝒩' hball
    hpar hδ
  haveI : CompleteSpace (zeroAtStart g s p m T) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  obtain ⟨C, hC0, hC⟩ := exists_norm_iterPullExt_le g s p m (T := T) hT 1 B
  exact exists_contDiffAt_of_natural (zeroAtStart g s p m T)
    (timeDerivExt (p := p) hT hm1) (fun σ => iterPullExt g s p m T B σ)
    (fun σ => iterPullExt g s p (m - 1) T B σ) (ofSmooth w hw) 𝒩 𝒩' (k := ∞) (by simp) hδ' hball
    (contDiff_iterPullExt_ofSmooth g s hp hT B hw m)
    (iterPullExt_zero g s p m hT B) (iterPullExt_zero g s p (m - 1) hT B)
    (fun σ z hz => iterPullExt_mem_zeroAtStart g s p m hT B σ hz) one_pos
    (fun σ hσ x => hC σ hσ.le x)
    (fun σ x => (iterPullExt_timeDerivExt g s p m hT hm1 B σ x))
    hρ₁ hr₁ hnat Φ hΦ

end Angenent

end ShortTime
