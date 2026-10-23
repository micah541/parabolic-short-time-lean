import ShortTime.Nonlinear.SmoothRepTimeDom
import ShortTime.Nonlinear.SmoothRepTimePi

/-!
# The time part of the regularity of the representative: the core argument

`htime_core`: for a fixed `v` with `U = ofSmooth w + v` satisfying the equation
`∂ₜ U - 𝒩 U = ofSmooth f`, and a frame patch at `α`, the continuous representative `v̂` satisfies, in
the chart at `α`, `∂ₜ v̂ = G` with `G` a smooth Euclidean function of `(t, y, jets of v̂)`. Hence
`G` is in `SpC k` whenever the representative is.
-/

noncomputable section

open Bundle Manifold Set Filter Topology Metric
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff BigOperators

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 3200000

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

variable {g : SmoothRiemannianMetric I M} {s p m : ℕ} {T : ℝ}

open ParabolicSpace HFlow

namespace SmoothRep

open EquationData

theorem jetChart_add (α : M) (j i : ℕ) (a b : ParabolicSpace g s p m T) (t : ℝ) (y : E) :
    jetChart g s p m T α j i (a + b) t y =
      jetChart g s p m T α j i a t y + jetChart g s p m T α j i b t y := by
  have h := jetChart_sub (g := g) (s := s) (p := p) (m := m) (T := T) α j i (a + b) b t y
  rw [add_sub_cancel_right] at h
  rw [← h]
  abel

theorem htime_core (D : EquationData I M 0 s p) (hT : 0 < T) (hTD : T ≤ D.T₀)
    (hm1 : 1 ≤ m) (hm2 : 2 ≤ m)
    (hk : Module.finrank ℝ E / 2 + 1 + 2 * p ≤ 2 * p * (m - 2))
    {w : ℝ → SmoothCcTensor g 0 s} (hw : JointlySmoothOn g 0 s (Icc 0 T) w)
    {f : ℝ → SmoothCcTensor g 0 s} (hf : JointlySmoothOn g 0 s (Icc 0 T) f) {δ : ℝ}
    {𝒩 : ParabolicSpace g s p m T → ParabolicSpace g s p (m - 1) T}
    (hagree : ∀ u (hu : JointlySmoothOn g 0 s (Icc 0 T) u),
      dist (ofSmooth (p := p) (m := m) u hu) (ofSmooth w hw) < δ →
      (∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (u t) x ∈ D.dom t x) ∧
      ∃ hF, 𝒩 (ofSmooth u hu) = ofSmooth (D.nonlinFamily u) hF)
    {v : ParabolicSpace g s p m T}
    (hUδ : dist (ofSmooth w hw + v) (ofSmooth w hw) < δ)
    (hcontU : ContinuousAt 𝒩 (ofSmooth w hw + v))
    (hdomU : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      jetTuple g s p m T (ofSmooth w hw + v) t x ∈ D.toFibreMap.dom 0 t x)
    (heq : timeDerivExt hT hm1 (ofSmooth w hw + v) - 𝒩 (ofSmooth w hw + v) = ofSmooth f hf)
    {α : M} {r : ℝ}
    {B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (hball : Metric.closedBall (extChartAt I α α) r ⊆ (extChartAt I α).target)
    (hB : ∀ y ∈ Metric.closedBall (extChartAt I α α) r, ∀ k,
      trivToE I α ((extChartAt I α).symm y) (B k ((extChartAt I α).symm y)) =
        Module.finBasis ℝ E k) :
    ∃ G : ℝ → E → TensorRSModel 0 s ℝ E,
      (∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ Metric.ball (extChartAt I α α) r,
        HasDerivWithinAt (fun τ => repChart g s p m T α v τ y) (G t y) (Icc 0 T) t) ∧
      ∀ ε ≤ r, ∀ k, (∀ n, SpatialReg.SpC k (Icc 0 T) (Metric.ball (extChartAt I α α) ε) n
          (TensorRSModel 0 s ℝ E) (repChart g s p m T α v)) →
        ∀ n, SpatialReg.SpC k (Icc 0 T) (Metric.ball (extChartAt I α α) ε) n
          (TensorRSModel 0 s ℝ E) G := by
  have hm0 : 0 < m := by omega
  have hkc : ∀ c : ℕ, c ≤ 2 * p → Module.finrank ℝ E / 2 + 1 + c ≤ 2 * p * (m - 0 - 1) :=
    fun c hc => le_trans (by omega) (le_trans hk (Nat.mul_le_mul_left _ (by omega)))
  have hk0m : Module.finrank ℝ E / 2 + 1 ≤ 2 * p * (m - 2) := le_trans (by omega) hk
  have hk1 : Module.finrank ℝ E / 2 + 1 + 0 ≤ 2 * p * (m - (0 + 1) - 1) := by
    have : m - (0 + 1) - 1 = m - 2 := by omega
    rw [this]; omega
  obtain ⟨Wd, hWdo, hsmooth, hdomW, hinW⟩ := D.toFibreMap.exists_euclDom (0 : ℝ) α hTD
  have hballr : Metric.ball (extChartAt I α α) r ⊆ (extChartAt I α).target :=
    Metric.ball_subset_closedBall.trans hball
  have hW : ∀ c : Fin (2 * p + 1), JointlySmoothOn g 0 (jetRanks s p c) (Icc 0 T)
      (jetFamily (p := p) w c) := fun c => jointlySmoothOn_iteratedCovGrad hw c
  -- the readings of the reference jets
  have hvalW : ∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ (extChartAt I α).target, ∀ c : Fin (2 * p + 1),
      FibreMap.valFam α (jetFamily (p := p) w) (t, y) c =
        jetChart g s p m T α 0 (c : ℕ) (ofSmooth w hw) t y := by
    intro t ht y hy c
    rw [jetChart_ofSmooth (g := g) (s := s) (p := p) (m := m) hT hm0 (hkc (c : ℕ) (Nat.lt_succ_iff.1 c.isLt)) α
      ht hy hw]
    rfl
  have hxiU : ∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ (extChartAt I α).target,
      ((fun c : Fin (2 * p + 1) => jetChart g s p m T α 0 (c : ℕ) v t y) +
        FibreMap.valFam α (jetFamily (p := p) w) (t, y)) =
      fun c : Fin (2 * p + 1) => jetChart g s p m T α 0 (c : ℕ) (ofSmooth w hw + v) t y := by
    intro t ht y hy
    funext c
    simp only [Pi.add_apply]
    rw [hvalW t ht y hy c, jetChart_add]
    exact add_comm _ _
  set Bsm : ℝ → E → TensorRSModel 0 s ℝ E := fun t y =>
    chartRd g α (f t) y - chartRd g α (timeDeriv T w t) y with hBsm
  set Gfun : ℝ → E → TensorRSModel 0 s ℝ E := fun t y =>
    D.toFibreMap.euclRep 0 α ((t, y), (fun c : Fin (2 * p + 1) => jetChart g s p m T α 0 (c : ℕ) v t y) +
      FibreMap.valFam α (jetFamily (p := p) w) (t, y)) + Bsm t y with hGfun
  have hkey : ∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ Metric.ball (extChartAt I α α) r,
      jetChart g s p m T α 1 0 v t y = Gfun t y := by
    intro t ht y hy
    have hyt := hballr hy
    have e1 := jetChart_add (g := g) (s := s) (p := p) (m := m) (T := T) α 1 0
      (ofSmooth w hw) v t y
    have e2 := jetChart_timeDerivExt (g := g) (s := s) (p := p) (m := m) hT hm1 hm2 hk0m α ht y
      (ofSmooth w hw + v)
    have e3 : timeDerivExt hT hm1 (ofSmooth w hw + v) =
        ofSmooth f hf + 𝒩 (ofSmooth w hw + v) := by
      rw [← heq]; abel
    have e4 := jetChart_add (g := g) (s := s) (p := p) (m := m - 1) (T := T) α 0 0
      (ofSmooth f hf) (𝒩 (ofSmooth w hw + v)) t y
    have e5 := jetChart_nonlin D hT hTD hm2 hk hw hagree hUδ hcontU α ht hyt (hdomU t ht _)
    have e6 := jetChart_ofSmooth (g := g) (s := s) (p := p) (m := m - 1) hT (j := 0) (i := 0)
      (by omega) (by
        have : m - 1 - 0 - 1 = m - 2 := by omega
        rw [this]; omega) α ht hyt hf
    have e7 := jetChart_ofSmooth (g := g) (s := s) (p := p) (m := m) hT (j := 1) (i := 0)
      (by omega) (by
        have : m - 1 - 1 = m - 2 := by omega
        rw [this]; omega) α ht hyt hw
    have e5' : jetChart g s p (m - 1) T α 0 0 (𝒩 (ofSmooth w hw + v)) t y =
        D.toFibreMap.euclRep 0 α ((t, y),
          (fun c : Fin (2 * p + 1) => jetChart g s p m T α 0 (c : ℕ) v t y) +
            FibreMap.valFam α (jetFamily (p := p) w) (t, y)) := by
      rw [e5, hxiU t ht y hyt]
    have e6' : jetChart g s p (m - 1) T α 0 0 (ofSmooth f hf) t y = chartRd g α (f t) y := e6
    have e7' : jetChart g s p m T α 1 0 (ofSmooth w hw) t y = chartRd g α (timeDeriv T w t) y :=
      e7
    have hA : jetChart g s p m T α 1 0 (ofSmooth w hw + v) t y =
        chartRd g α (f t) y + D.toFibreMap.euclRep 0 α ((t, y),
          (fun c : Fin (2 * p + 1) => jetChart g s p m T α 0 (c : ℕ) v t y) +
            FibreMap.valFam α (jetFamily (p := p) w) (t, y)) := by
      rw [← e2, e3, e4, e5', e6']
    have hx : jetChart g s p m T α 1 0 v t y =
        jetChart g s p m T α 1 0 (ofSmooth w hw + v) t y -
          jetChart g s p m T α 1 0 (ofSmooth w hw) t y := by
      rw [e1]; abel
    show _ = D.toFibreMap.euclRep 0 α ((t, y),
          (fun c : Fin (2 * p + 1) => jetChart g s p m T α 0 (c : ℕ) v t y) +
            FibreMap.valFam α (jetFamily (p := p) w) (t, y)) +
        (chartRd g α (f t) y - chartRd g α (timeDeriv T w t) y)
    rw [hx, hA, e7']
    abel
  refine ⟨Gfun, ?_, ?_⟩
  · intro t ht y hy
    have hyt := hballr hy
    have hd := hasDerivWithinAt_jetChart_time (g := g) (s := s) (p := p) (m := m) hT (j := 0)
      (i := 0) (by omega) hk1 α hyt v ht
    have hd' : HasDerivWithinAt (fun τ => jetChart g s p m T α 0 0 v τ y) (Gfun t y)
        (Icc 0 T) t := by
      rw [← hkey t ht y hy]
      exact hd
    exact hd'.congr (fun τ _ => repChart_eq_jetChart α v τ hyt)
      (repChart_eq_jetChart α v t hyt)
  · intro ε hεr k h0 n
    have hεt : Metric.ball (extChartAt I α α) ε ⊆ (extChartAt I α).target :=
      (Metric.ball_subset_ball hεr).trans hballr
    have hUo : IsOpen (Metric.ball (extChartAt I α α) ε) := Metric.isOpen_ball
    have hS : UniqueDiffOn ℝ (Icc (0 : ℝ) T) := uniqueDiffOn_Icc hT
    have hξv : SpatialReg.SpC k (Icc 0 T) (Metric.ball (extChartAt I α α) ε) n
        (∀ c : Fin (2 * p + 1), TensorRSModel 0 (jetRanks s p c) ℝ E)
        (fun t y c => jetChart g s p m T α 0 (c : ℕ) v t y) :=
      SpatialReg.SpC.pi (k := k) hS hUo (ι := Fin (2 * p + 1)) n
        (V := fun c : Fin (2 * p + 1) => TensorRSModel 0 (jetRanks s p c) ℝ E)
        (φ := fun (c : Fin (2 * p + 1)) t y => jetChart g s p m T α 0 (c : ℕ) v t y)
        (fun (c : Fin (2 * p + 1)) =>
          spC_jetChart hT hm0 hball hB hεr v h0 (c : ℕ) (hkc (c : ℕ) (Nat.lt_succ_iff.1 c.isLt)) n)
    have hξW : SpatialReg.SpC k (Icc 0 T) (Metric.ball (extChartAt I α α) ε) n
        (∀ c : Fin (2 * p + 1), TensorRSModel 0 (jetRanks s p c) ℝ E)
        (fun t y => FibreMap.valFam α (jetFamily (p := p) w) (t, y)) :=
      SpatialReg.SpC.of_contDiffOn hS hUo n hξv
        ((FibreMap.contDiffOn_valFam α hW).mono (prod_mono subset_rfl hεt))
    have hξU := SpatialReg.SpC.add hS hUo hξv hξW
    set Wo : Set (ℝ × E × (∀ c : Fin (2 * p + 1), TensorRSModel 0 (jetRanks s p c) ℝ E)) :=
      {q | q.2.1 ∈ (extChartAt I α).target ∧ ((q.1, q.2.1), q.2.2) ∈ Wd} with hWo
    have hrearr : Continuous (fun q : ℝ × E × (∀ c : Fin (2 * p + 1),
        TensorRSModel 0 (jetRanks s p c) ℝ E) => ((q.1, q.2.1), q.2.2)) :=
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
        (continuous_snd.comp continuous_snd)
    have hWoo : IsOpen Wo :=
      ((isOpen_extChartAt_target (I := I) α).preimage
        (continuous_fst.comp continuous_snd)).inter (hWdo.preimage hrearr)
    have hΨ : ContDiffOn ℝ ∞ (fun q : ℝ × E × (∀ c : Fin (2 * p + 1),
        TensorRSModel 0 (jetRanks s p c) ℝ E) => D.toFibreMap.euclRep 0 α ((q.1, q.2.1), q.2.2))
        ((Icc 0 T ×ˢ (univ : Set (E × (∀ c : Fin (2 * p + 1),
          TensorRSModel 0 (jetRanks s p c) ℝ E)))) ∩ Wo) := by
      have hre : ContDiffOn ℝ ∞ (fun q : ℝ × E × (∀ c : Fin (2 * p + 1),
          TensorRSModel 0 (jetRanks s p c) ℝ E) => ((q.1, q.2.1), q.2.2))
          ((Icc 0 T ×ˢ (univ : Set (E × (∀ c : Fin (2 * p + 1),
            TensorRSModel 0 (jetRanks s p c) ℝ E)))) ∩ Wo) :=
        ((contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)).prodMk
          (contDiff_snd.comp contDiff_snd)).contDiffOn
      have h := hsmooth.comp hre
        (fun q hq => ⟨⟨⟨hq.1.1, hq.2.1⟩, trivial⟩, hq.2.2⟩)
      simp only [Function.comp_def] at h
      exact h
    have hO : ∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ Metric.ball (extChartAt I α α) ε,
        (t, y, (fun c : Fin (2 * p + 1) => jetChart g s p m T α 0 (c : ℕ) v t y) +
          FibreMap.valFam α (jetFamily (p := p) w) (t, y)) ∈ Wo := by
      intro t ht y hy
      have hyt := hεt hy
      refine ⟨hyt, hinW t ht y hyt _ ?_⟩
      show prodOfModel (jetRanks s p) α ((extChartAt I α).symm y) _ ∈ _
      rw [hxiU t ht y hyt, prodOfModel_jetChart _ α t hyt]
      exact hdomU t ht _
    have hA := SpatialReg.SpC.comp_rel hS hUo n hWoo hΨ hO hξU
    have hBs : SpatialReg.SpC k (Icc 0 T) (Metric.ball (extChartAt I α α) ε) n
        (TensorRSModel 0 s ℝ E) Bsm :=
      SpatialReg.SpC.of_contDiffOn hS hUo n (h0 n)
        (((contDiffOn_chartFam α hf).sub
          (contDiffOn_chartFam α (jointlySmoothOn_timeDeriv hT hw))).mono
          (prod_mono subset_rfl hεt))
    exact SpatialReg.SpC.add hS hUo hA hBs

end SmoothRep

end ShortTime
