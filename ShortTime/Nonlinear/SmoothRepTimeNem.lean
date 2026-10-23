import ShortTime.Nonlinear.SmoothRepTimeEq
import ShortTime.Nonlinear.SmoothRepTube
import ShortTime.Nonlinear.EqFibre

/-!
# The nonlinearity evaluated on the continuous representative

`jetChart_nonlin`: if `𝒩 : 𝒫^m → 𝒫^{m-1}` agrees with the composition operator on smooth families
near `ofSmooth w` and is continuous at `U`, and the jets of the representative of `U` lie in the
domain at `(t, φ⁻¹ y)`, then the chart reading of `evalJet 0 0 (𝒩 U)` is `euclRep` of the chart
readings of the jets of `U`.
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
set_option maxHeartbeats 1600000

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

variable (g s p m T) in
/-- The jets `(evalJet 0 c t x U)_{c ≤ 2p}` of the continuous representative, as a point of the
jet bundle over `x`. -/
def jetTuple (U : ParabolicSpace g s p m T) (t : ℝ) (x : M) :
    ProdFiber I (jetRanks s p) x :=
  fun c => TensorRSSpace.ofModel (evalJet g s p m T 0 (c : ℕ) t x U)

theorem prodOfModel_jetChart (U : ParabolicSpace g s p m T) (α : M) (t : ℝ) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    prodOfModel (jetRanks s p) α ((extChartAt I α).symm y)
        (fun c : Fin (2 * p + 1) => jetChart g s p m T α 0 (c : ℕ) U t y) =
      jetTuple g s p m T U t ((extChartAt I α).symm y) := by
  have hs : (extChartAt I α).symm y ∈ (chartAt H α).source := by
    rw [← extChartAt_source (I := I)]; exact (extChartAt I α).map_target hy
  funext c
  unfold prodOfModel jetTuple
  have key : jetChart g s p m T α 0 (c : ℕ) U t y =
      (trivAt I M 0 (s + (c : ℕ)) α).continuousLinearMapAt ℝ ((extChartAt I α).symm y)
        (TensorRSSpace.ofModel (evalJet g s p m T 0 (c : ℕ) t ((extChartAt I α).symm y) U)) := by
    unfold jetChart
    rw [triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M) 0 (s + (c : ℕ)) α hs,
      TensorRSSpace.toModel_ofModel]
  show (trivAt I M 0 (s + (c : ℕ)) α).symmL ℝ ((extChartAt I α).symm y)
      (jetChart g s p m T α 0 (c : ℕ) U t y) = _
  rw [key]
  exact Trivialization.symmL_continuousLinearMapAt (trivAt I M 0 (s + (c : ℕ)) α)
    (mem_trivAt_baseSet_of_chart (I := I) (M := M) (a := s + (c : ℕ)) hs) _

theorem jetChart_ofSmooth (hT : 0 < T) {j i : ℕ} (hj : j < m)
    (hk : Module.finrank ℝ E / 2 + 1 + i ≤ 2 * p * (m - j - 1)) (α : M) {t : ℝ}
    (ht : t ∈ Icc 0 T) {y : E} (hy : y ∈ (extChartAt I α).target)
    {u : ℝ → SmoothCcTensor g 0 s} (hu : JointlySmoothOn g 0 s (Icc 0 T) u) :
    jetChart g s p m T α j i (ofSmooth u hu) t y =
      chartRd g α (iteratedCovGrad g 0 s i (timeDerivIter T u j t)) y := by
  unfold jetChart
  rw [evalJet_ofSmooth hT hj hk ht _ hu, chartRd_eq_twist α _ hy]

theorem continuous_jetChart (α : M) (j i : ℕ) (t : ℝ) (y : E) :
    Continuous fun v : ParabolicSpace g s p m T => jetChart g s p m T α j i v t y :=
  (continuous_chartRSTwistInv (I := I) (M := M) α ((extChartAt I α).symm y) 0 (s + i)).comp
    (evalJet g s p m T j i t ((extChartAt I α).symm y)).continuous

theorem jetChart_nonlin (D : EquationData I M 0 s p) (hT : 0 < T) (hTD : T ≤ D.T₀)
    (hm2 : 2 ≤ m)
    (hk : Module.finrank ℝ E / 2 + 1 + 2 * p ≤ 2 * p * (m - 2))
    {w : ℝ → SmoothCcTensor g 0 s} (hw : JointlySmoothOn g 0 s (Icc 0 T) w) {δ : ℝ}
    {𝒩 : ParabolicSpace g s p m T → ParabolicSpace g s p (m - 1) T}
    (hagree : ∀ u (hu : JointlySmoothOn g 0 s (Icc 0 T) u),
      dist (ofSmooth (p := p) (m := m) u hu) (ofSmooth w hw) < δ →
      (∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (u t) x ∈ D.dom t x) ∧
      ∃ hF, 𝒩 (ofSmooth u hu) = ofSmooth (D.nonlinFamily u) hF)
    {U : ParabolicSpace g s p m T} (hU : dist U (ofSmooth w hw) < δ) (hcont : ContinuousAt 𝒩 U)
    (α : M) {t : ℝ} (ht : t ∈ Icc 0 T) {y : E} (hy : y ∈ (extChartAt I α).target)
    (hdomU : jetTuple g s p m T U t ((extChartAt I α).symm y) ∈
      D.toFibreMap.dom 0 t ((extChartAt I α).symm y)) :
    jetChart g s p (m - 1) T α 0 0 (𝒩 U) t y =
      D.toFibreMap.euclRep 0 α ((t, y),
        fun c : Fin (2 * p + 1) => jetChart g s p m T α 0 (c : ℕ) U t y) := by
  have hkc : ∀ i, i ≤ 2 * p → Module.finrank ℝ E / 2 + 1 + i ≤ 2 * p * (m - 0 - 1) :=
    fun i hi => le_trans (by omega) (le_trans hk (Nat.mul_le_mul_left _ (by omega)))
  have hk0 : Module.finrank ℝ E / 2 + 1 + 0 ≤ 2 * p * (m - 1 - 0 - 1) := by
    have : m - 1 - 0 - 1 = m - 2 := by omega
    rw [this]; omega
  obtain ⟨u, hu⟩ := exists_seq_tendsto U
  obtain ⟨Wd, hWdo, hsmooth, hdomW, hinW⟩ := D.toFibreMap.exists_euclDom (0 : ℝ) α hTD
  set ξ : ℕ → ProdModel E (jetRanks s p) := fun n c =>
    jetChart g s p m T α 0 (c : ℕ) (u n : ParabolicSpace g s p m T) t y with hξ
  set ξU : ProdModel E (jetRanks s p) := fun c =>
    jetChart g s p m T α 0 (c : ℕ) U t y with hξU
  have hξt : Tendsto ξ atTop (𝓝 ξU) :=
    tendsto_pi_nhds.2 fun c => ((continuous_jetChart (g := g) (s := s) (p := p) (m := m) (T := T)
      α 0 (c : ℕ) t y).tendsto U).comp hu
  have hev : ∀ᶠ n in atTop, dist (u n : ParabolicSpace g s p m T) (ofSmooth w hw) < δ :=
    (Metric.tendsto_nhds.1 hu _ (sub_pos.2 hU)).mono fun n hn => by
      have := dist_triangle (u n : ParabolicSpace g s p m T) U (ofSmooth w hw)
      linarith [hn]
  set Sdom := ((Icc 0 T ×ˢ (extChartAt I α).target) ×ˢ
    (univ : Set (ProdModel E (jetRanks s p)))) ∩ Wd with hSdom
  have hmemU : ((t, y), ξU) ∈ Sdom := by
    refine ⟨⟨⟨ht, hy⟩, trivial⟩, hinW t ht y hy ξU ?_⟩
    rw [hξU, prodOfModel_jetChart U α t hy]
    exact hdomU
  have hseq : ∀ᶠ n in atTop,
      jetChart g s p (m - 1) T α 0 0 (𝒩 (u n : ParabolicSpace g s p m T)) t y =
        D.toFibreMap.euclRep 0 α ((t, y), ξ n) ∧ ((t, y), ξ n) ∈ Sdom := by
    filter_upwards [hev] with n hn
    have e : (u n : ParabolicSpace g s p m T) = ofSmooth (u n).family (u n).2 := rfl
    obtain ⟨hdom, hF, hN⟩ := hagree (u n).family (u n).2 (by rw [← e]; exact hn)
    have hV : ∀ c, JointlySmoothOn g 0 (jetRanks s p c) (Icc 0 T)
        (jetFamily (p := p) (u n).family c) :=
      fun c => jointlySmoothOn_iteratedCovGrad (u n).2 c
    have hdomV : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
        FibreMap.valAt (fun c => jetFamily (p := p) (u n).family c τ) x ∈
          D.toFibreMap.dom 0 τ x := fun τ hτ x => hdom τ hτ x
    have hq : (t, y) ∈ Icc 0 T ×ˢ (extChartAt I α).target := ⟨ht, hy⟩
    have hvf : FibreMap.valFam α (jetFamily (p := p) (u n).family) (t, y) = ξ n := by
      funext c
      rw [hξ]
      simp only
      rw [jetChart_coe (g := g) (s := s) (p := p) (m := m) hT (by omega) (hkc c (by omega)) α ht hy]
      rfl
    refine ⟨?_, ?_⟩
    · have e1 : jetChart g s p (m - 1) T α 0 0 (𝒩 (u n : ParabolicSpace g s p m T)) t y =
          jetChart g s p (m - 1) T α 0 0
            (ofSmooth (D.nonlinFamily (u n).family) hF) t y := by
        rw [e, hN]
      rw [e1]
      have e2 := jetChart_ofSmooth (g := g) (s := s) (p := p) (m := m - 1) hT (j := 0) (i := 0)
        (by omega) hk0 α ht hy hF
      rw [e2]
      have e4 := FibreMap.chartFam_apply_eq D.toFibreMap (0 : ℝ) hTD hV hdomV (α := α) hq
      rw [← hvf]
      exact e4
    · refine ⟨⟨⟨ht, hy⟩, trivial⟩, hinW t ht y hy (ξ n) ?_⟩
      have hpv := FibreMap.prodOfModel_valFam (α := α) (jetFamily (p := p) (u n).family)
        (q := (t, y)) hy
      have h5 := hdomV t ht ((extChartAt I α).symm y)
      rw [← hvf]
      rwa [← hpv] at h5
  have hlhs : Tendsto
      (fun n => jetChart g s p (m - 1) T α 0 0 (𝒩 (u n : ParabolicSpace g s p m T)) t y)
      atTop (𝓝 (jetChart g s p (m - 1) T α 0 0 (𝒩 U) t y)) :=
    ((continuous_jetChart (g := g) (s := s) (p := p) (m := m - 1) (T := T) α 0 0 t y).tendsto
      _).comp (hcont.tendsto.comp hu)
  have hrhs : Tendsto (fun n => D.toFibreMap.euclRep 0 α ((t, y), ξ n)) atTop
      (𝓝 (D.toFibreMap.euclRep 0 α ((t, y), ξU))) := by
    have hc := (hsmooth.continuousOn _ hmemU)
    have ht' : Tendsto (fun n => ((t, y), ξ n)) atTop (𝓝[Sdom] ((t, y), ξU)) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.prodMk_nhds hξt, hseq.mono fun n hn => hn.2⟩
    exact hc.tendsto.comp ht'
  exact tendsto_nhds_unique_of_eventuallyEq hlhs hrhs (hseq.mono fun n hn => hn.1)

end SmoothRep

end ShortTime
