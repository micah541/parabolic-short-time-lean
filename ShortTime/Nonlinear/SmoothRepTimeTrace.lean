import ShortTime.Nonlinear.SmoothRepTime

/-!
# The time bootstrap for a solution that does not start at zero

`EquationData.smoothRep_time_trace`: the version of `smoothRep_time` for `U ∈ 𝒫^m` in a
neighbourhood of the smooth base point `ofSmooth w` (no zero-start condition), with the equation
`∂ₜ U - 𝒩 U = ofSmooth f`. The representative of `U` is the sum of the representative of
`v = U - ofSmooth w`, to which `htime_core` applies, and the (smooth) reading of `w`; so
`G_U = G_v + (reading of ∂ₜ w)`.
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
set_option linter.unusedVariables false
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

variable {g : SmoothRiemannianMetric I M} {s p : ℕ}

open ParabolicSpace HFlow SmoothRep

namespace EquationData

theorem smoothRep_time_trace (D : EquationData I M 0 s p) (hp : 1 ≤ p)
    {m : ℕ} (hm : Module.finrank ℝ E / (2 * p) + 4 ≤ m) (hm1 : 1 ≤ m)
    {T₁ : ℝ} (hT₁ : 0 < T₁) (hT₁D : T₁ ≤ D.T₀)
    {w : ℝ → SmoothCcTensor g 0 s} (hw : JointlySmoothOn g 0 s (Icc 0 T₁) w)
    (hwdom : ∀ t ∈ Icc (0 : ℝ) T₁, ∀ x : M, covJet g 0 s (2 * p) (w t) x ∈ D.dom t x)
    {δ : ℝ} (hδ : 0 < δ)
    {𝒩 : ParabolicSpace g s p m T₁ → ParabolicSpace g s p (m - 1) T₁}
    (h𝒩 : ContDiffAt ℝ ∞ 𝒩 (ofSmooth w hw))
    (hagree : ∀ u (hu : JointlySmoothOn g 0 s (Icc 0 T₁) u),
      dist (ofSmooth (p := p) (m := m) u hu) (ofSmooth w hw) < δ →
      (∀ t ∈ Icc (0 : ℝ) T₁, ∀ x : M, covJet g 0 s (2 * p) (u t) x ∈ D.dom t x) ∧
      ∃ hF, 𝒩 (ofSmooth u hu) = ofSmooth (D.nonlinFamily u) hF) :
    ∃ V ∈ 𝓝 (ofSmooth w hw : ParabolicSpace g s p m T₁),
      ∀ (α : M) (r : ℝ) (_ : 0 < r)
        (B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
        (_ : Metric.closedBall (extChartAt I α α) r ⊆ (extChartAt I α).target)
        (_ : ∀ y ∈ Metric.closedBall (extChartAt I α α) r, ∀ k,
          trivToE I α ((extChartAt I α).symm y) (B k ((extChartAt I α).symm y)) =
            Module.finBasis ℝ E k),
      ∃ εt ∈ Ioc 0 r, ∀ U ∈ V, ∀ (f : ℝ → SmoothCcTensor g 0 s)
        (hf : JointlySmoothOn g 0 s (Icc 0 T₁) f),
        timeDerivExt hT₁ hm1 U - 𝒩 U = ofSmooth f hf →
        ∃ G : ℝ → E → TensorRSModel 0 s ℝ E,
          (∀ t ∈ Icc (0 : ℝ) T₁, ∀ y ∈ Metric.ball (extChartAt I α α) εt,
            HasDerivWithinAt
              (fun τ => repChart g s p m T₁ α U τ y)
              (G t y) (Icc 0 T₁) t) ∧
          ∀ ε ≤ εt, ∀ k, (∀ n, SpatialReg.SpC k (Icc 0 T₁)
              (Metric.ball (extChartAt I α α) ε) n (TensorRSModel 0 s ℝ E)
              (repChart g s p m T₁ α U)) →
            ∀ n, SpatialReg.SpC k (Icc 0 T₁) (Metric.ball (extChartAt I α α) ε) n
              (TensorRSModel 0 s ℝ E) G := by
  have hk := hk_of_hm (E := E) hp hm
  have hm2 : 2 ≤ m := by
    have := Nat.zero_le (Module.finrank ℝ E / (2 * p))
    omega
  have hm0 : 0 < m := by omega
  obtain ⟨ρ, hρ, hsmall⟩ := exists_small_dom D hT₁ hT₁D (by omega) hk hw hwdom
  set c : ℝ := min δ ρ with hc
  have hc0 : 0 < c := lt_min hδ hρ
  have hev : ∀ᶠ y in 𝓝 (ofSmooth w hw), ContinuousAt 𝒩 y :=
    ((h𝒩.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)).eventually (by simp)).mono
      fun y hy => hy.continuousAt
  refine ⟨_, inter_mem (Metric.ball_mem_nhds (ofSmooth w hw) hc0) hev,
    fun α r hr B hball hB => ⟨r, ⟨hr, le_rfl⟩, ?_⟩⟩
  rintro U ⟨hU1, hU2⟩ f hf heq
  have hU1' : dist U (ofSmooth w hw) < c := hU1
  set v : ParabolicSpace g s p m T₁ := U - ofSmooth w hw with hv
  have hWv : ofSmooth w hw + v = U := add_sub_cancel _ _
  have hdist : dist (ofSmooth w hw + v) (ofSmooth w hw) < δ := by
    rw [hWv]; exact lt_of_lt_of_le hU1' (min_le_left _ _)
  have hdom : ∀ t ∈ Icc (0 : ℝ) T₁, ∀ x : M,
      jetTuple g s p m T₁ (ofSmooth w hw + v) t x ∈ D.toFibreMap.dom 0 t x := by
    refine hsmall _ ?_
    rw [hWv, ← dist_eq_norm]
    exact lt_of_lt_of_le hU1' (min_le_right _ _)
  have hcont : ContinuousAt 𝒩 (ofSmooth w hw + v) := by rw [hWv]; exact hU2
  have heq' : timeDerivExt hT₁ hm1 (ofSmooth w hw + v) - 𝒩 (ofSmooth w hw + v) =
      ofSmooth f hf := by rw [hWv]; exact heq
  obtain ⟨G, hG1, hG2⟩ := htime_core D hT₁ hT₁D hm1 hm2 hk hw hf hagree hdist hcont hdom heq'
    hball hB
  have hballr : Metric.ball (extChartAt I α α) r ⊆ (extChartAt I α).target :=
    Metric.ball_subset_closedBall.trans hball
  have hkc : ∀ c : ℕ, c ≤ 2 * p → Module.finrank ℝ E / 2 + 1 + c ≤ 2 * p * (m - 0 - 1) :=
    fun c hc => le_trans (by omega) (le_trans hk (Nat.mul_le_mul_left _ (by omega)))
  have hk0m : Module.finrank ℝ E / 2 + 1 ≤ 2 * p * (m - 2) := le_trans (by omega) hk
  have hk1 : Module.finrank ℝ E / 2 + 1 + 0 ≤ 2 * p * (m - (0 + 1) - 1) := by
    have : m - (0 + 1) - 1 = m - 2 := by omega
    rw [this]; omega
  -- readings of the base point
  have e0 : ∀ t ∈ Icc (0 : ℝ) T₁, ∀ y ∈ Metric.ball (extChartAt I α α) r,
      jetChart g s p m T₁ α 0 0 (ofSmooth w hw) t y = chartRd g α (w t) y := by
    intro t ht y hy
    exact jetChart_ofSmooth (g := g) (s := s) (p := p) (m := m) hT₁ (j := 0) (i := 0) hm0
      (hkc 0 (Nat.zero_le _)) α ht (hballr hy) hw
  have e1 : ∀ t ∈ Icc (0 : ℝ) T₁, ∀ y ∈ Metric.ball (extChartAt I α α) r,
      jetChart g s p m T₁ α 1 0 (ofSmooth w hw) t y = chartRd g α (timeDeriv T₁ w t) y := by
    intro t ht y hy
    exact jetChart_ofSmooth (g := g) (s := s) (p := p) (m := m) hT₁ (j := 1) (i := 0)
      (by omega) (by
        have : m - 1 - 1 = m - 2 := by omega
        rw [this]; omega) α ht (hballr hy) hw
  refine ⟨fun t y => G t y + chartRd g α (timeDeriv T₁ w t) y, ?_, ?_⟩
  · intro t ht y hy
    have hyt := hballr hy
    have hd1 := hG1 t ht y hy
    have hd2 := hasDerivWithinAt_jetChart_time (g := g) (s := s) (p := p) (m := m) hT₁ (j := 0)
      (i := 0) (by omega) hk1 α hyt (ofSmooth w hw) ht
    rw [e1 t ht y hy] at hd2
    have hd1' : HasDerivWithinAt (fun τ => jetChart g s p m T₁ α 0 0 v τ y) (G t y)
        (Icc 0 T₁) t :=
      hd1.congr (fun τ _ => (repChart_eq_jetChart α v τ hyt).symm)
        (repChart_eq_jetChart α v t hyt).symm
    have hd := hd1'.add hd2
    refine hd.congr (fun τ hτ => ?_) ?_
    · rw [repChart_eq_jetChart α U τ hyt]
      have hadd := jetChart_add (g := g) (s := s) (p := p) (m := m) (T := T₁) α 0 0
        (ofSmooth w hw) v τ y
      rw [hWv] at hadd
      exact hadd.trans (add_comm _ _)
    · rw [repChart_eq_jetChart α U t hyt]
      have hadd := jetChart_add (g := g) (s := s) (p := p) (m := m) (T := T₁) α 0 0
        (ofSmooth w hw) v t y
      rw [hWv] at hadd
      exact hadd.trans (add_comm _ _)
  · intro ε hεr k h0 n
    have hεt : Metric.ball (extChartAt I α α) ε ⊆ (extChartAt I α).target :=
      (Metric.ball_subset_ball hεr).trans hballr
    have hUo : IsOpen (Metric.ball (extChartAt I α α) ε) := Metric.isOpen_ball
    have hS : UniqueDiffOn ℝ (Icc (0 : ℝ) T₁) := uniqueDiffOn_Icc hT₁
    have hRW : ∀ n', SpatialReg.SpC k (Icc 0 T₁) (Metric.ball (extChartAt I α α) ε) n'
        (TensorRSModel 0 s ℝ E) (fun t y => -chartRd g α (w t) y) := fun n' =>
      SpatialReg.SpC.of_contDiffOn hS hUo n' (h0 n')
        (ψ := fun t y => -chartRd g α (w t) y)
        (((contDiffOn_chartFam α hw).neg).mono (prod_mono subset_rfl hεt))
    have hRv : SpatialReg.SpC k (Icc 0 T₁) (Metric.ball (extChartAt I α α) ε) n
        (TensorRSModel 0 s ℝ E) (repChart g s p m T₁ α v) := by
      refine SpatialReg.SpC.congr hUo n (fun t ht y hy => ?_) (SpatialReg.SpC.add hS hUo (h0 n) (hRW n))
      rw [repChart_eq_jetChart α U t (hεt hy), repChart_eq_jetChart α v t (hεt hy), ← hWv,
        jetChart_add, e0 t ht y (Metric.ball_subset_ball hεr hy)]
      abel
    have hGv := hG2 ε hεr k (fun n' => by
      refine SpatialReg.SpC.congr hUo n' (fun t ht y hy => ?_)
        (SpatialReg.SpC.add hS hUo (h0 n') (hRW n'))
      rw [repChart_eq_jetChart α U t (hεt hy), repChart_eq_jetChart α v t (hεt hy), ← hWv,
        jetChart_add, e0 t ht y (Metric.ball_subset_ball hεr hy)]
      abel) n
    exact SpatialReg.SpC.add hS hUo hGv
      (SpatialReg.SpC.of_contDiffOn hS hUo n (h0 n)
        ((contDiffOn_chartFam α (jointlySmoothOn_timeDeriv hT₁ hw)).mono
          (prod_mono subset_rfl hεt)))

end EquationData

end ShortTime
