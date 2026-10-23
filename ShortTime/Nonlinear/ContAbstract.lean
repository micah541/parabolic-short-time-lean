import ShortTime.Nonlinear.ContIFT
import ShortTime.Nonlinear.ExistenceAssembly

/-!
# From an abstract solution to a pointwise solution (`cor:C`)

`EquationData.solution_of_abstract`: let `w` be a smooth family on `[0, T]` with
`ofSmooth w - ofSmooth b ∈ 𝒫^m_0` and `∂ₜ(ofSmooth w) = 𝒩(ofSmooth w)` in `𝒫^{m-1}`, where `𝒩` agrees
with the composition operator on smooth families near `ofSmooth u`. Then `w(0) = b(0)`, the jets of `w`
lie in the domain, and `∂ₜw = F[w]` pointwise on `[0, T]`.
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

theorem solution_of_abstract (D : EquationData I M 0 s p) (hp : 1 ≤ p)
    {m : ℕ} (hm : Module.finrank ℝ E / (2 * p) + 4 ≤ m) {T : ℝ} (hT : 0 < T) (hTD : T ≤ D.T₀)
    (hm1 : 1 ≤ m) {u : ℝ → SmoothCcTensor g 0 s} (hu : JointlySmoothOn g 0 s (Icc 0 T) u)
    {𝒩 : ParabolicSpace g s p m T → ParabolicSpace g s p (m - 1) T} {δ : ℝ}
    (hagree : ∀ w (hw : JointlySmoothOn g 0 s (Icc 0 T) w),
      dist (ofSmooth (p := p) (m := m) w hw) (ofSmooth u hu) < δ →
      (∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (w t) x ∈ D.dom t x) ∧
      ∃ hF, 𝒩 (ofSmooth w hw) = ofSmooth (D.nonlinFamily w) hF)
    {w : ℝ → SmoothCcTensor g 0 s} (hw : JointlySmoothOn g 0 s (Icc 0 T) w)
    (hdist : dist (ofSmooth (p := p) (m := m) w hw) (ofSmooth u hu) < δ)
    {b : ℝ → SmoothCcTensor g 0 s} (hb : JointlySmoothOn g 0 s (Icc 0 T) b)
    (hzero : ofSmooth (p := p) (m := m) w hw - ofSmooth b hb ∈ zeroAtStart g s p m T)
    (heq : timeDerivExt hT hm1 (ofSmooth w hw) = 𝒩 (ofSmooth w hw)) :
    w 0 = b 0 ∧ (∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (w t) x ∈ D.dom t x) ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        HasDerivWithinAt (fun τ => TensorRSSpace.toModel ((w τ).toSection x))
          (TensorRSSpace.toModel (D.F t x (covJet g 0 s (2 * p) (w t) x))) (Icc 0 T) t := by
  obtain ⟨hdom, hF, h𝒩w⟩ := hagree w hw hdist
  have hk := evalJet_dim_arith (n := Module.finrank ℝ E) hp hm
  have hm2 : 2 ≤ m := le_trans (by norm_num) (le_trans (Nat.le_add_left 4 _) hm)
  have hm0 : 0 < m := by omega
  refine ⟨?_, hdom, ?_⟩
  · -- the initial value
    have hd : JointlySmoothOn g 0 s (Icc 0 T) (fun t => w t - b t) := jointlySmoothOn_sub hw hb
    have hmem : ofSmooth (p := p) (m := m) (fun t => w t - b t) hd ∈ zeroAtStart g s p m T := by
      rw [ofSmooth_sub hw hb]
      exact hzero
    have h0 : w 0 - b 0 = 0 := by
      refine smoothCcTensor_eq_of_toFun fun x => ?_
      have h1 := evalJet_eq_zero_of_mem_zeroAtStart hT hm0 hk x hmem
      rw [evalJet_ofSmooth hT hm0 (by rwa [Nat.sub_zero]) ⟨le_rfl, hT.le⟩ x hd] at h1
      rw [Cutoff.toFun_zero]
      exact h1
    exact sub_eq_zero.mp h0
  · -- the equation
    have hFspec := (D.nonlinFamily_spec hTD hw hdom).1
    have hTD' := jointlySmoothOn_timeDeriv hT hw
    have h1 : ofSmooth (p := p) (m := m - 1)
        (fun t => timeDeriv T w t - D.nonlinFamily w t) (jointlySmoothOn_sub hTD' hF) = 0 := by
      rw [ofSmooth_sub hTD' hF, ← timeDerivExt_ofSmooth hT hm1 hw, ← h𝒩w, sub_eq_zero]
      exact heq
    intro t ht x
    have hd : timeDeriv T w t - D.nonlinFamily w t = 0 :=
      eq_zero_of_ofSmooth_eq_zero hT (by omega) _ h1 ht
    have hd' : timeDeriv T w t = D.nonlinFamily w t := sub_eq_zero.mp hd
    have h := hasDerivWithinAt_timeDeriv hT hw ht x
    rw [hd', hFspec t ht x] at h
    exact h

end EquationData

end ShortTime
