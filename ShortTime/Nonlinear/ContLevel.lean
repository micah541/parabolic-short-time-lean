import ShortTime.Nonlinear.ContJetClose
import ShortTime.Nonlinear.StabGlobal3
import ShortTime.Nonlinear.TraceRegularityStatement

/-!
# The solution at one Sobolev level (`cor:C`)

`EquationData.level_solution`: let `u` be a solution on `[0, T]` whose jets are uniformly parabolic and
whose neighbourhood of jets is uniformly parabolic (`hstab`). At level `m ≥ ⌊n/2p⌋ + 4` and for every
`ε > 0` there is `ρ > 0` such that for every smooth `a` with `‖a - u₀‖_{𝒫^m} < ρ` (as a time-independent
family) there is a smooth parabolic solution `w` with datum `a` on `[0, T]`, `ε`-close to `u` in `𝒫^m`.

Proof: parametric inverse function theorem (`exists_ift_cov`) for `U = u + ζ + v`, `ζ = a - u₀`,
then regularity in trace form (`TraceRegularity`) to see that `U` is smooth, then
`solution_of_abstract` for the pointwise equation, and `hstab` for parabolicity.
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

namespace EquationData

variable {s p : ℕ} {g : SmoothRiemannianMetric I M}

open ParabolicSpace

theorem ofSmooth_zero_family {T : ℝ} (hT : 0 < T) {m : ℕ}
    (u : ℝ → SmoothCcTensor g 0 s) (hu : JointlySmoothOn g 0 s (Icc 0 T) u)
    (h0 : JointlySmoothOn g 0 s (Icc 0 T) (fun _ => (0 : SmoothCcTensor g 0 s))) :
    ofSmooth (p := p) (m := m) (fun _ => (0 : SmoothCcTensor g 0 s)) h0 = 0 := by
  have h := ofSmooth_sub (p := p) (m := m) hu hu
  rw [sub_self] at h
  rw [← h]
  exact ofSmooth_congr hT _ _ fun t _ => (sub_self (u t)).symm

theorem covJet_sub_apply (k : Fin (2 * p + 1)) (w u : SmoothCcTensor g 0 s) (y : M) :
    covJet g 0 s (2 * p) w y k - covJet g 0 s (2 * p) u y k =
      (iteratedCovGrad g 0 s k (w - u)).toSection y := by
  simp only [covJet, iteratedCovGrad_sub, SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub,
    Pi.sub_apply]

set_option maxHeartbeats 1600000 in
theorem level_solution (D : EquationData I M 0 s p) (hp : 1 ≤ p) (hreg : D.TraceRegularity g)
    {u₀ : SmoothCcTensor g 0 s} {T : ℝ} {u : ℝ → SmoothCcTensor g 0 s}
    (hsol : D.IsSolution g u₀ T u) {lam η : ℝ} (hlam : 0 < lam) (hη : 0 < η)
    (hleg : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (u t) x ∈ D.dom t x ∧
      LegendreAt g 0 s p x (D.principal t x (covJet g 0 s (2 * p) (u t) x)) lam)
    (hstab : ∀ t ∈ Icc (0 : ℝ) T, ∀ y : M, ∀ ζ : CovJetFiber I 0 s (2 * p) y,
      (∀ k : Fin (2 * p + 1), riemannianFiberNormSq (I := I) (M := M) g 0 (s + k) y
        (ζ k - covJet g 0 s (2 * p) (u t) y k) ≤ η) →
      ζ ∈ D.dom t y ∧ LegendreAt g 0 s p y (D.principal t y ζ) lam)
    {m : ℕ} (hm : Module.finrank ℝ E / (2 * p) + 4 ≤ m) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ∀ a : SmoothCcTensor g 0 s,
      ‖ofSmooth (p := p) (m := m) (T := T) (fun _ => a - u₀)
        (jointlySmoothOn_const (g := g) (Icc 0 T) (a - u₀))‖ < ρ →
      ∃ (w : ℝ → SmoothCcTensor g 0 s) (hw : JointlySmoothOn g 0 s (Icc 0 T) w),
        D.IsParabolicSolution g a T w ∧
        dist (ofSmooth (p := p) (m := m) w hw) (ofSmooth u hsol.smooth) < ε := by
  have hT := hsol.pos
  have hTD := hsol.le_T₀
  have hu := hsol.smooth
  have hsolF := D.timeDeriv_eq_nonlinFamily hsol
  obtain ⟨hm1, δ, hδ, 𝒩, h𝒩, hagree, hL, hift⟩ :=
    D.exists_ift_cov hp hm hT hTD hlam hu hleg hsolF
  obtain ⟨V, hV, hVp⟩ := hreg hp hm hm1 hT hTD hlam hu hleg hδ h𝒩 hagree hL
  obtain ⟨rV, hrV, hball⟩ := Metric.mem_nhds_iff.mp hV
  have hm0 : 0 < m := by omega
  -- the pointwise control of the jets
  have hCex : ∀ k : Fin (2 * p + 1), ∃ C, 0 ≤ C ∧
      ∀ (w u : ℝ → SmoothCcTensor g 0 s) (hw : JointlySmoothOn g 0 s (Icc 0 T) w)
        (hu : JointlySmoothOn g 0 s (Icc 0 T) u), ∀ t ∈ Icc (0 : ℝ) T, ∀ y : M,
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + k) y
            ((iteratedCovGrad g 0 s k (w t - u t)).toSection y) ≤
            C * dist (ofSmooth (p := p) (m := m) w hw) (ofSmooth u hu) ^ 2 :=
    fun k => exists_jetSq_close hT hp hm0 (emb_arith hp hm (Nat.lt_succ_iff.mp k.2))
  choose C hC0 hC using hCex
  set Cm := ∑ k, C k with hCm
  have hCm0 : 0 ≤ Cm := Finset.sum_nonneg fun k _ => hC0 k
  set r₂ := Real.sqrt (η / (Cm + 1)) with hr₂
  have hr₂pos : 0 < r₂ := Real.sqrt_pos.2 (by positivity)
  set r := min (min ε δ) (min rV r₂) with hr
  have hrpos : 0 < r := lt_min (lt_min hε hδ) (lt_min hrV hr₂pos)
  have hrε : r ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have hrδ : r ≤ δ := (min_le_left _ _).trans (min_le_right _ _)
  have hrV' : r ≤ rV := (min_le_right _ _).trans (min_le_left _ _)
  have hrr₂ : r ≤ r₂ := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨ρ₁, hρ₁, hρ₁p⟩ := hift (r / 2) (half_pos hrpos)
  refine ⟨min ρ₁ (r / 2), lt_min hρ₁ (half_pos hrpos), fun a ha => ?_⟩
  set hc : JointlySmoothOn g 0 s (Icc 0 T) (fun _ => a - u₀) :=
    jointlySmoothOn_const (g := g) (Icc 0 T) (a - u₀) with hchc
  set ζ : ParabolicSpace g s p m T := ofSmooth (fun _ => a - u₀) hc with hζ
  set W : ParabolicSpace g s p m T := ofSmooth u hu with hW
  obtain ⟨v, hvn, hveq⟩ := hρ₁p ζ (lt_of_lt_of_le ha (min_le_left _ _))
  have hvn' : ‖(v : ParabolicSpace g s p m T)‖ < r / 2 := by
    exact hvn
  have hζn : ‖ζ‖ < r / 2 := lt_of_lt_of_le ha (min_le_right _ _)
  set U : ParabolicSpace g s p m T := W + ζ + (v : ParabolicSpace g s p m T) with hU
  have hdistU : dist U W < r := by
    rw [dist_eq_norm, hU, add_assoc, add_sub_cancel_left]
    calc ‖ζ + (v : ParabolicSpace g s p m T)‖ ≤ ‖ζ‖ + ‖(v : ParabolicSpace g s p m T)‖ :=
          norm_add_le _ _
      _ < r / 2 + r / 2 := add_lt_add hζn hvn'
      _ = r := by ring
  have hUV : U ∈ V := hball (by rw [mem_ball]; exact lt_of_lt_of_le hdistU hrV')
  -- the smooth comparison family `b = u + (a - u₀)`
  have hb : JointlySmoothOn g 0 s (Icc 0 T) (fun t => u t + (a - u₀)) := jointlySmoothOn_add hu hc
  have hbζ : ofSmooth (p := p) (m := m) (fun t => u t + (a - u₀)) hb = W + ζ := ofSmooth_add hu hc
  have hzero : U - ofSmooth (p := p) (m := m) (fun t => u t + (a - u₀)) hb ∈
      zeroAtStart g s p m T := by
    rw [hbζ, hU, add_sub_cancel_left]
    exact v.2
  have hf0 : JointlySmoothOn g 0 s (Icc 0 T) (fun _ => (0 : SmoothCcTensor g 0 s)) :=
    jointlySmoothOn_const (g := g) (Icc 0 T) 0
  have heq0 : timeDerivExt hT hm1 U - 𝒩 U = ofSmooth (p := p) (m := m - 1) (fun _ => (0 : SmoothCcTensor g 0 s)) hf0 := by
    rw [ofSmooth_zero_family hT u hu hf0]
    exact sub_eq_zero.mpr hveq
  obtain ⟨vt, hvt, hUvt⟩ := hVp U hUV _ hf0 _ hb hzero heq0
  have hdist : dist (ofSmooth (p := p) (m := m) vt hvt) W < r := by rw [← hUvt]; exact hdistU
  obtain ⟨h0, hdom, heqn⟩ := D.solution_of_abstract hp hm hT hTD hm1 hu hagree hvt
    (hdist.trans_le hrδ) hb (by rw [← hUvt]; exact hzero) (by rw [← hUvt]; exact hveq)
  have hinit : vt 0 = a := by
    rw [h0]
    change u 0 + (a - u₀) = a
    rw [hsol.initial]
    abel
  -- parabolicity, from the stability of the jets
  have hd2 : dist (ofSmooth (p := p) (m := m) vt hvt) W ^ 2 < η / (Cm + 1) := by
    have h1 : dist (ofSmooth (p := p) (m := m) vt hvt) W < r₂ := hdist.trans_le hrr₂
    have h2 := (Real.lt_sqrt dist_nonneg).1 h1
    exact h2
  have hjets : ∀ t ∈ Icc (0 : ℝ) T, ∀ y : M, ∀ k : Fin (2 * p + 1),
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + k) y
        (covJet g 0 s (2 * p) (vt t) y k - covJet g 0 s (2 * p) (u t) y k) ≤ η := by
    intro t ht y k
    rw [covJet_sub_apply]
    refine (hC k vt u hvt hu t ht y).trans ?_
    have hCk : C k ≤ Cm := Finset.single_le_sum (f := C) (fun k _ => hC0 k) (Finset.mem_univ k)
    have hd0 : 0 ≤ dist (ofSmooth (p := p) (m := m) vt hvt) (ofSmooth u hu) ^ 2 := sq_nonneg _
    calc C k * dist (ofSmooth (p := p) (m := m) vt hvt) (ofSmooth u hu) ^ 2
        ≤ (Cm + 1) * dist (ofSmooth (p := p) (m := m) vt hvt) W ^ 2 :=
          mul_le_mul (by linarith) le_rfl hd0 (by positivity)
      _ ≤ η := by
          have := mul_lt_mul_of_pos_left hd2 (show 0 < Cm + 1 by positivity)
          rw [mul_div_cancel₀ _ (by positivity)] at this
          exact this.le
  have hpar : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, D.IsParabolicAt g t x (covJet g 0 s (2 * p) (vt t) x) :=
    fun t ht x => by
      obtain ⟨hd, hl⟩ := hstab t ht x _ (hjets t ht x)
      exact ⟨hd, lam, hl⟩
  refine ⟨vt, hvt, ⟨⟨hT, hTD, hvt, hinit, hdom, heqn⟩, hpar⟩, hdist.trans_le hrε⟩

end EquationData

end ShortTime
