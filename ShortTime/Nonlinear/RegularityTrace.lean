import ShortTime.Nonlinear.RegularityAngenent
import ShortTime.Nonlinear.RegularityTraceAbstract

/-!
# Angenent's trick with an initial trace, concrete form (`thm:C`, Step 2)

`exists_iterPull_contDiffOn` produces a neighbourhood `V` of `0` in `𝒫^m_0`: perturbations of the
base point `w` that vanish at `t = 0`.  For smooth dependence on the initial datum we need the
neighbourhood to be a neighbourhood of `ofSmooth w` in `𝒫^m` itself.  Here the elements `U` of the
neighbourhood need not vanish at `t = 0`, but `U - ofSmooth b ∈ 𝒫^m_0` for a smooth `b`, i.e. the
trace of `U` is smooth.  Then `σ ↦ Π_σ U` is `C^∞` on a ball (`exists_iterPull_contDiffOn_trace`),
by `Angenent.exists_contDiffAt_of_natural_trace` (the implicit function theorem for
`U ↦ (∂ₜU - 𝒩U, [U])`).
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

/-- **`σ ↦ Π_σ U` is `C^∞` on a ball, for `U` near `w` with smooth trace** (Angenent's trick with an
initial trace). Hypotheses as in `exists_iterPull_contDiffOn`; the neighbourhood is taken in `𝒫^m`. -/
theorem exists_iterPull_contDiffOn_trace (D : EquationData I M 0 s p) (hp : 1 ≤ p)
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
    ∃ V ∈ 𝓝 (ofSmooth (p := p) (m := m) w hw : ParabolicSpace g s p m T₁), ∃ ρ > 0, ∀ U ∈ V,
      ∀ (f : ℝ → SmoothCcTensor g 0 s) (hf : JointlySmoothOn g 0 s (Icc 0 T₁) f),
        timeDerivExt hT₁ hm1 U - 𝒩 U = ofSmooth f hf →
        ∀ (b : ℝ → SmoothCcTensor g 0 s) (hb : JointlySmoothOn g 0 s (Icc 0 T₁) b),
          U - ofSmooth b hb ∈ zeroAtStart g s p m T₁ →
          ContDiffOn ℝ ∞ (fun σ => iterPullExt g s p m T₁ B σ U) (ball (0 : Fin n → ℝ) ρ) := by
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
  obtain ⟨ρ₁, hρ₁, r₁, hr₁, hnat⟩ := HFlow.natural_concrete g D hT₁ hT₁D B hw 𝒩 h𝒩 hagree
    hδ' 𝒩' hball hpar hδ
  haveI : IsClosed ((zeroAtStart g s p m T₁ : Submodule ℝ (ParabolicSpace g s p m T₁)) :
      Set (ParabolicSpace g s p m T₁)) := Submodule.isClosed_topologicalClosure _
  obtain ⟨C, hC0, hC⟩ := exists_norm_iterPullExt_le g s p m (T := T₁) hT₁ 1 B
  have hd𝒩 : DifferentiableAt ℝ 𝒩 (ofSmooth w hw) := h𝒩.differentiableAt (by simp)
  obtain ⟨V0, hV0, ρ, hρ, hreg⟩ := Angenent.exists_contDiffAt_of_natural_trace
    (zeroAtStart g s p m T₁) (timeDerivExt (p := p) hT₁ hm1) (fun σ => iterPullExt g s p m T₁ B σ)
    (fun σ => iterPullExt g s p (m - 1) T₁ B σ) (ofSmooth w hw) 𝒩 𝒩' (k := ∞) (by simp) hδ' hball
    (contDiff_iterPullExt_ofSmooth g s hp hT₁ B hw m)
    (iterPullExt_zero g s p m hT₁ B) (iterPullExt_zero g s p (m - 1) hT₁ B)
    (fun σ z hz => iterPullExt_mem_zeroAtStart g s p m hT₁ B σ hz) one_pos
    (fun σ hσ x => hC σ hσ.le x)
    (fun σ x => (iterPullExt_timeDerivExt g s p m hT₁ hm1 B σ x))
    hρ₁ hr₁ hnat hd𝒩 Φ hΦW
  refine ⟨(fun U => U - ofSmooth (p := p) (m := m) w hw) ⁻¹' V0, ?_, ρ, hρ,
    fun U hU f hf hG b hb hUb σ hσ => ?_⟩
  · refine (continuous_sub_right _).continuousAt.preimage_mem_nhds ?_
    rwa [sub_self]
  · have hUW : ofSmooth (p := p) (m := m) w hw + (U - ofSmooth w hw) = U := add_sub_cancel _ _
    refine ContDiffAt.contDiffWithinAt ?_
    have h1 := hreg (U - ofSmooth w hw) hU σ hσ ?_ ?_
    · have hfun : (fun τ => iterPullExt g s p m T₁ B τ U) =
          fun τ => iterPullExt g s p m T₁ B τ (ofSmooth w hw) +
            iterPullExt g s p m T₁ B τ (U - ofSmooth w hw) := by
        funext τ
        rw [← map_add, hUW]
      rw [hfun]
      exact ((contDiff_iterPullExt_ofSmooth g s hp hT₁ B hw m).contDiffAt).add h1
    · simp only [hUW, hG]
      exact (contDiff_iterPullExt_ofSmooth g s hp hT₁ B hf (m - 1)).contDiffAt
    · simp only [hUW]
      have hfun : (fun τ => (zeroAtStart g s p m T₁).mkQ (iterPullExt g s p m T₁ B τ U)) =
          fun τ => (zeroAtStart g s p m T₁).mkQL (iterPullExt g s p m T₁ B τ (ofSmooth b hb)) := by
        funext τ
        exact (Submodule.Quotient.eq (zeroAtStart g s p m T₁)).2 (by
          rw [← map_sub]
          exact iterPullExt_mem_zeroAtStart g s p m hT₁ B τ hUb)
      rw [hfun]
      exact ((zeroAtStart g s p m T₁).mkQL.contDiff.comp
        (contDiff_iterPullExt_ofSmooth g s hp hT₁ B hb m)).contDiffAt

end EquationData

end ShortTime
