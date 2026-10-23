import ShortTime.Nonlinear.SmoothRepTimeNem

/-!
# Small elements of `𝒫^m` have their jets in the domain

`exists_small_dom`: there is `ρ > 0` such that for every `U ∈ 𝒫^m` with `‖U - ofSmooth w‖ < ρ`, the
jets of the continuous representative of `U` lie in the domain at every `(t, x)`. The proof covers
`M` by finitely many chart balls and uses the chart-coordinate tube `FibreMap.exists_euclTube` in
each.
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

theorem exists_pos_le_finset {ι : Type*} (A : Finset ι) (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ ρ > 0, ∀ i ∈ A, ρ ≤ f i := by
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a A ha ih =>
    obtain ⟨ρ, hρ, h⟩ := ih
    refine ⟨min ρ (f a), lt_min hρ (hf a), fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (h i hi)

/-- **Chart-local smallness**: around `α`, small elements have their jets in the domain. -/
theorem exists_small_dom_chart (D : EquationData I M 0 s p) (hT : 0 < T) (hTD : T ≤ D.T₀)
    (hm : 0 < m) (hk : Module.finrank ℝ E / 2 + 1 + 2 * p ≤ 2 * p * (m - 2))
    {w : ℝ → SmoothCcTensor g 0 s} (hw : JointlySmoothOn g 0 s (Icc 0 T) w)
    (hwdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (w t) x ∈ D.dom t x) (α : M) :
    ∃ r > 0, ∃ ρ > 0, ∀ U : ParabolicSpace g s p m T, ‖U - ofSmooth w hw‖ < ρ →
      ∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ Metric.ball (extChartAt I α α) r,
        jetTuple g s p m T U t ((extChartAt I α).symm y) ∈
          D.toFibreMap.dom 0 t ((extChartAt I α).symm y) := by
  have hkc : ∀ c : ℕ, c ≤ 2 * p → Module.finrank ℝ E / 2 + 1 + c ≤ 2 * p * (m - 0 - 1) :=
    fun c hc => le_trans (by omega) (le_trans hk (Nat.mul_le_mul_left _ (by omega)))
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.1
    ((isOpen_extChartAt_target (I := I) α).mem_nhds (mem_extChartAt_target (I := I) α))
  have hW : ∀ c : Fin (2 * p + 1), JointlySmoothOn g 0 (jetRanks s p c) (Icc 0 T)
      (jetFamily (p := p) w c) := fun c => jointlySmoothOn_iteratedCovGrad hw c
  have hWdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      FibreMap.valAt (fun c => jetFamily (p := p) w c t) x ∈ D.toFibreMap.dom 0 t x :=
    fun t ht x => hwdom t ht x
  obtain ⟨Wd, hWdo, hsmooth, hdomW, ε, hε, hεW⟩ :=
    D.toFibreMap.exists_euclTube (0 : ℝ) hTD hW hWdom α hsub
  have hcl : IsCompact (Metric.closedBall (extChartAt I α α) r) := isCompact_closedBall _ _
  choose C hC0 hC using fun c : Fin (2 * p + 1) =>
    exists_norm_jetChart_le (g := g) (s := s) (p := p) (m := m) hT hm
      (hkc (c : ℕ) (by omega)) α hcl hsub
  set K : ℝ := ∑ c, C c with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun c _ => hC0 c
  have hCK : ∀ c, C c ≤ K := fun c =>
    Finset.single_le_sum (f := C) (fun c _ => hC0 c) (Finset.mem_univ c)
  refine ⟨r, hr, ε / (K + 1), by positivity, fun U hU t ht y hy => ?_⟩
  have hyt : y ∈ (extChartAt I α).target := hsub (Metric.ball_subset_closedBall hy)
  have hyc : y ∈ Metric.closedBall (extChartAt I α α) r := Metric.ball_subset_closedBall hy
  have hnorm : ∀ c : Fin (2 * p + 1),
      ‖jetChart g s p m T α 0 (c : ℕ) U t y -
        FibreMap.valFam α (jetFamily (p := p) w) (t, y) c‖ ≤ ε := by
    intro c
    have e : FibreMap.valFam α (jetFamily (p := p) w) (t, y) c =
        jetChart g s p m T α 0 (c : ℕ) (ofSmooth w hw) t y := by
      rw [jetChart_ofSmooth (g := g) (s := s) (p := p) (m := m) hT hm (hkc (c : ℕ) (by omega)) α
        ht hyt hw]
      rfl
    rw [e]
    refine (hC c t ht y hyc _ _).trans ?_
    calc C c * ‖U - ofSmooth w hw‖ ≤ K * (ε / (K + 1)) :=
          mul_le_mul (hCK c) hU.le (norm_nonneg _) hK0
      _ ≤ ε := by
          rw [mul_div_assoc']
          rw [div_le_iff₀ (by positivity)]
          nlinarith
  have hmem : ((t, y), fun c : Fin (2 * p + 1) => jetChart g s p m T α 0 (c : ℕ) U t y) ∈ Wd :=
    hεW t ht y hyc _ ((pi_norm_le_iff_of_nonneg hε.le).2 hnorm)
  have hd := hdomW ((t, y), fun c : Fin (2 * p + 1) => jetChart g s p m T α 0 (c : ℕ) U t y)
    ⟨⟨⟨ht, hyt⟩, trivial⟩, hmem⟩
  simp only at hd
  rwa [prodOfModel_jetChart U α t hyt] at hd

/-- **Smallness gives the domain, globally.** -/
theorem exists_small_dom (D : EquationData I M 0 s p) (hT : 0 < T) (hTD : T ≤ D.T₀)
    (hm : 0 < m) (hk : Module.finrank ℝ E / 2 + 1 + 2 * p ≤ 2 * p * (m - 2))
    {w : ℝ → SmoothCcTensor g 0 s} (hw : JointlySmoothOn g 0 s (Icc 0 T) w)
    (hwdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (w t) x ∈ D.dom t x) :
    ∃ ρ > 0, ∀ U : ParabolicSpace g s p m T, ‖U - ofSmooth w hw‖ < ρ →
      ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        jetTuple g s p m T U t x ∈ D.toFibreMap.dom 0 t x := by
  choose r hr ρ hρ hdom using exists_small_dom_chart D hT hTD hm hk hw hwdom
  set O : M → Set M := fun α =>
    (extChartAt I α).source ∩ extChartAt I α ⁻¹' Metric.ball (extChartAt I α α) (r α) with hO
  have hOo : ∀ α, IsOpen (O α) := fun α => isOpen_extChartAt_preimage' α Metric.isOpen_ball
  have hαO : ∀ α, α ∈ O α := fun α =>
    ⟨mem_extChartAt_source α, Metric.mem_ball_self (hr α)⟩
  obtain ⟨A, hA⟩ := isCompact_univ.elim_finite_subcover O hOo (fun x _ => mem_iUnion.2 ⟨x, hαO x⟩)
  obtain ⟨ρ₀, hρ₀, hρ₀A⟩ := exists_pos_le_finset A ρ hρ
  refine ⟨ρ₀, hρ₀, fun U hU t ht x => ?_⟩
  have hx := hA (mem_univ x)
  simp only [mem_iUnion] at hx
  obtain ⟨α, hαA, hxα⟩ := hx
  have h := hdom α U (lt_of_lt_of_le hU (hρ₀A α hαA)) t ht (extChartAt I α x) hxα.2
  rwa [(extChartAt I α).left_inv hxα.1] at h

end SmoothRep

end ShortTime
