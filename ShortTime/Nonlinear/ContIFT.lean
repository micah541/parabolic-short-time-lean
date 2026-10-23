import ShortTime.Nonlinear.Regularity
import ShortTime.Analysis.IFTParam

/-!
# The parametric inverse function theorem around a solution (`cor:C`, covariant bundles)

Let `u` be a smooth solution of `∂ₜu = F[u]` on `[0, T]` whose jets are parabolic with a uniform
Legendre constant. At level `m ≥ ⌊n/2p⌋ + 4` the nonlinear operator `𝒩` of `cor:N` around `u` and its
parabolic linearization give `∂ₜ - D𝒩(u) : 𝒫^m_0 ≃ 𝒫^{m-1}`. The parametric inverse function theorem
(`exists_solution_param`, with `A = ∂ₜ`, `W = u`) then solves, for every small `ζ ∈ 𝒫^m`,

  `∂ₜ(u + ζ + v) = 𝒩(u + ζ + v)`   with `v ∈ 𝒫^m_0` small.

For a smooth datum `a` near `u₀`, `ζ = (a - u₀)` (constant in time) has initial value `a - u₀`, so
`u + ζ + v` has initial value `a`.
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

namespace EquationData

variable {s p : ℕ} {g : SmoothRiemannianMetric I M}

open ParabolicSpace

/-- A solution satisfies `∂ₜu = F[u]` as an identity of smooth families on `[0, T]`. -/
theorem timeDeriv_eq_nonlinFamily (D : EquationData I M 0 s p) {u₀ : SmoothCcTensor g 0 s}
    {T : ℝ} {u : ℝ → SmoothCcTensor g 0 s} (hu : D.IsSolution g u₀ T u) :
    ∀ t ∈ Icc (0 : ℝ) T, timeDeriv T u t = D.nonlinFamily u t := by
  intro t ht
  have hFspec := (D.nonlinFamily_spec hu.le_T₀ hu.smooth hu.jets_mem).1
  refine smoothCcTensor_eq_of_toSection fun x => ?_
  have h1 := hasDerivWithinAt_timeDeriv hu.pos hu.smooth ht x
  have h2 := hu.eqn t ht x
  have huniq : UniqueDiffWithinAt ℝ (Icc (0 : ℝ) T) t := (uniqueDiffOn_Icc hu.pos) t ht
  have h3 := huniq.eq_deriv _ h1 h2
  rw [hFspec t ht x]
  exact TensorRSSpace.toModel_injective (I := I) (r := 0) (s := s) (x := x) h3

/-- **The parametric inverse function theorem at level `m`.** Let `u` be a smooth family on `[0, T]`
with `∂ₜu = F[u]`, whose jets lie in the domain with Legendre constant `lam`. Then there are the data
`δ, 𝒩, L_u` of `cor:N` around `u`, and for every `ε > 0` a `ρ > 0` such that for every `ζ ∈ 𝒫^m`
with `‖ζ‖ < ρ` the equation `∂ₜ(u + ζ + v) = 𝒩(u + ζ + v)` has a solution `v ∈ 𝒫^m_0` with
`‖v‖ < ε`. -/
theorem exists_ift_cov (D : EquationData I M 0 s p) (hp : 1 ≤ p)
    {m : ℕ} (hm : Module.finrank ℝ E / (2 * p) + 4 ≤ m) {T : ℝ} (hT : 0 < T) (hTD : T ≤ D.T₀)
    {lam : ℝ} (hlam : 0 < lam) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u)
    (hleg : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (u t) x ∈ D.dom t x ∧
      LegendreAt g 0 s p x (D.principal t x (covJet g 0 s (2 * p) (u t) x)) lam)
    (hsol : ∀ t ∈ Icc (0 : ℝ) T, timeDeriv T u t = D.nonlinFamily u t) :
    ∃ hm1 : 1 ≤ m, ∃ δ > 0,
      ∃ 𝒩 : ParabolicSpace g s p m T → ParabolicSpace g s p (m - 1) T,
        ContDiffAt ℝ ∞ 𝒩 (ofSmooth u hu) ∧
        (∀ w (hw : JointlySmoothOn g 0 s (Icc 0 T) w),
          dist (ofSmooth (p := p) (m := m) w hw) (ofSmooth u hu) < δ →
          (∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (w t) x ∈ D.dom t x) ∧
          ∃ hF, 𝒩 (ofSmooth w hw) = ofSmooth (D.nonlinFamily w) hF) ∧
        (∃ L : LinearOp g s p T, L.IsParabolic lam ∧
          (∀ k t, t ∈ Icc (0 : ℝ) T → ∀ x,
            opFieldHom ((L.coeff k t).toSection x) =
              D.partialDeriv k t x (covJet g 0 s (2 * p) (u t) x)) ∧
          ∀ h (hh : JointlySmoothOn g 0 s (Icc 0 T) h), ∃ hL,
            fderiv ℝ 𝒩 (ofSmooth u hu) (ofSmooth h hh) =
              ofSmooth (fun t => L.apply t (h t)) hL) ∧
        ∀ ε > 0, ∃ ρ > 0, ∀ ζ : ParabolicSpace g s p m T, ‖ζ‖ < ρ →
          ∃ v : zeroAtStart g s p m T, ‖v‖ < ε ∧
            timeDerivExt hT hm1 (ofSmooth u hu + ζ + (v : ParabolicSpace g s p m T)) =
              𝒩 (ofSmooth u hu + ζ + (v : ParabolicSpace g s p m T)) := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hm1 : 1 ≤ m := le_trans (by norm_num) (le_trans (Nat.le_add_left 4 _) hm)
  have hdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, covJet g 0 s (2 * p) (u t) x ∈ D.dom t x :=
    fun t ht x => (hleg t ht x).1
  obtain ⟨δ, hδ, 𝒩, h𝒩, hagree, L, hLc, hLd⟩ := D.exists_nonlinOp hp hT hTD hm hu hdom
  have hLpar : L.IsParabolic lam := by
    refine ⟨hlam, fun t ht x => ?_⟩
    have h := (hleg t ht x).2
    unfold LinearOp.principal
    rw [hLc ⟨2 * p, Nat.lt_succ_self _⟩ t ht x]
    exact h
  obtain ⟨Φ, hΦ⟩ := L.isomorphism hp hT hLpar m hm1
  have hFw := (D.nonlinFamily_spec hTD hu hdom).2
  have hNW : 𝒩 (ofSmooth u hu) = ofSmooth (D.nonlinFamily u) hFw := by
    obtain ⟨-, hF, hEq⟩ := hagree u hu (by rw [dist_self]; exact hδ)
    exact hEq
  have hdec : timeDerivExt hT hm1 - fderiv ℝ 𝒩 (ofSmooth u hu) = L.heatExt hT hm1 :=
    timeDerivExt_sub_eq_heatExt hT hm1 L _ hLd
  have hΦW : ∀ z : zeroAtStart g s p m T,
      Φ z = timeDerivExt hT hm1 z - fderiv ℝ 𝒩 (ofSmooth u hu) z := fun z => by
    rw [← sub_apply, hdec]
    exact L.isomorphism_eq_heatExt hT hm1 Φ hΦ z
  have : IsClosed ((zeroAtStart g s p m T : Submodule ℝ (ParabolicSpace g s p m T)) :
      Set (ParabolicSpace g s p m T)) := Submodule.isClosed_topologicalClosure _
  have : CompleteSpace (zeroAtStart g s p m T) := IsClosed.completeSpace_coe
  have hW : timeDerivExt hT hm1 (ofSmooth (p := p) u hu) = 𝒩 (ofSmooth u hu) := by
    rw [timeDerivExt_ofSmooth, hNW]
    exact ofSmooth_congr hT _ _ hsol
  exact ⟨hm1, δ, hδ, 𝒩, h𝒩, hagree, ⟨L, hLpar, hLc, hLd⟩,
    exists_solution_param (zeroAtStart g s p m T) (timeDerivExt hT hm1) 𝒩 (ofSmooth u hu)
      (h𝒩.of_le (by norm_num)) hW Φ hΦW⟩

end EquationData

end ShortTime
