import ShortTime.Nonlinear.Existence
import ShortTime.Nonlinear.RegularityFinal
import ShortTime.Nonlinear.SmoothRepTime

/-!
# Regularity of the abstract solution (`prop:regularity`, covariant bundles)

`EquationData.exists_parabolicSpace_solution` produces `v ∈ 𝒫^m_0` with
`G(v) = ∂ₜ(w + v) - 𝒩(w + v) = f_ε` (`ParabolicSpace.existenceMap`), where `f_ε` is smooth. Angenent's
trick (`prop:regularity`) shows that such a `v` is smooth, provided it is small.

The statement below is made for any data `w, 𝒩, L` with the properties that
`exists_parabolicSpace_solution` provides (they are its hypotheses here), since these data come out
of an existential. These properties determine `𝒩` near `w`: it is continuous near `w`
(`ContDiffAt`) and agrees on the dense smooth families within `δ` with the composition operator
`u ↦ F[u]`. So the statement is about the operator `G` of the paper.

Why the statement is true (the proof of `prop:regularity`):
* For small `v` (in the neighbourhood `V`), the jets of `w + v` lie within the `δ`-tube where `𝒩`
  is the composition operator, `G(v)` lies in the image neighbourhood of the inverse function
  theorem around `v = 0`, where `DG(0) = ∂ₜ - L_w` is an isomorphism (`L_w` is parabolic).
* Angenent's trick: with horizontal flows `Π_s`, `H(s, v) = ∂ₜ(Π_s w + v) - F_s[Π_s w + v]`, the
  implicit function theorem gives `Π_s v = Ψ(s, Π_s f)`, which is `C^∞` in `s` because `f` is
  smooth. Hence all spatial derivatives of `v` lie in `𝒫^m`.
* Time regularity follows from `∂ₜu = F[u] + f` on `[0, T₁]` by bootstrapping in `H^k`.

The conclusion is stated on all of `[0, T₁]` (not only on `[0, ε]` as in the paper): the argument
above uses only that `f = G(v)` is smooth on `[0, T₁]`, and `f_ε` is.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter Topology MeasureTheory Metric
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Spectral
open scoped Manifold ContDiff BigOperators

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

open ParabolicSpace

/-- **Regularity** (`prop:regularity`, covariant bundles). In the setting of
`exists_parabolicSpace_solution` (a smooth `w` on `[0, T₁]` with parabolic jets, the nonlinear
operator `𝒩 : 𝒫^m → 𝒫^{m-1}` around `w`, and its parabolic linearization `L_w`), every small
`v ∈ 𝒫^m_0` with `G(v) = ∂ₜ(w + v) - 𝒩(w + v)` (`existenceMap`) equal to a smooth family is itself
a smooth family on `[0, T₁]`. -/
theorem parabolicSpace_solution_smooth (D : EquationData I M 0 s p) (hp : 1 ≤ p)
    {m : ℕ} (hm : Module.finrank ℝ E / (2 * p) + 4 ≤ m) (hm1 : 1 ≤ m)
    {T₁ : ℝ} (hT₁ : 0 < T₁) (hT₁D : T₁ ≤ D.T₀) {lam : ℝ} (hlam : 0 < lam)
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
          ofSmooth (fun t => L.apply t (h t)) hL) :
    ∃ V ∈ 𝓝 (0 : zeroAtStart g s p m T₁), ∀ v ∈ V,
      ∀ (f : ℝ → SmoothCcTensor g 0 s) (hf : JointlySmoothOn g 0 s (Icc 0 T₁) f),
        existenceMap hT₁ hm1 𝒩 (ofSmooth w hw) v = ofSmooth f hf →
        ∃ (vt : ℝ → SmoothCcTensor g 0 s) (hvt : JointlySmoothOn g 0 s (Icc 0 T₁) vt),
          (v : ParabolicSpace g s p m T₁) = ofSmooth vt hvt := by
  exact regularity_of_time D hp hm hm1 hT₁ hT₁D hw hleg hδ h𝒩 hagree hL
    (by
      obtain ⟨Vt, hVt, H⟩ := smoothRep_time D hp hm hm1 hT₁ hT₁D hlam hw hleg hδ h𝒩 hagree hL
      exact ⟨Vt, hVt, fun α r hr B hb hB => by
        obtain ⟨εt, ⟨h0, h1⟩, h⟩ := H α r hr B hb hB
        exact ⟨εt, h0, h1, h⟩⟩)

end EquationData

end ShortTime
