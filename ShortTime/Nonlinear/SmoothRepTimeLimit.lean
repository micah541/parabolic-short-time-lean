import ShortTime.Nonlinear.SmoothRepAssembly
import ShortTime.Nonlinear.FibreMapChart
import ShortTime.Nonlinear.SmoothRepTimeAnalysis

/-!
# Jets of the continuous representative: spatial recursion and time derivative

Stage 1 of the derivation of `htime` (see `SmoothRepTime.lean` for the plan and the corrected
interface). For `v ∈ 𝒫^m` write `jetChart j i v t y` for the reading, in the chart and
trivialization at `α`, of `∂ₜ^j ∇^i v̂ (t, φ⁻¹ y)` (the continuous representative, `evalJet`).

* `jetChart_coe`: on a smooth family it is the chart reading `chartRd` of `∇^i ∂ₜ^j u`.
* `tendstoUniformlyOn_jetChart_space/time`: along smooth approximants it converges uniformly.
* **`hasFDerivAt_jetChart`**: on a patch, `D (jetChart j i) = slotIns (jetChart j (i+1)) +
  kerL (jetChart j i)` (the recursion of `fderiv_chartRd_eq` for the limit).
* **`hasDerivWithinAt_jetChart_time`**: `∂ₜ (jetChart j i) = jetChart (j+1) i` within `[0,T]`.

## Corrected interface `htime'` (to replace `htime` in `exists_smooth_rep`)

`htime` as stated in `SmoothRepAssembly` is not provable: it quantifies over every `ε` with
`ball ⊆ target`, but the chart recursion only holds on the closed ball of radius `r` where the frame
`B` has constant chart coordinates, and it contains no equation. The corrected hypothesis is, for
every `α`, with `(r, B, hball, hB)` the data of `hflow α`:

  `∃ ε ∈ (0, r], ∃ G, (∀ t ∈ Icc 0 T, ∀ y ∈ ball (φ α) ε, HasDerivWithinAt (repChart · y) (G t y) (Icc 0 T) t) ∧`
  `  ∀ k, (∀ n, SpC k (Icc 0 T) (ball (φ α) ε) n _ (repChart …)) → ∀ n, SpC k … n _ G`

(i.e. `htime` with the extra `∃ ε ≤ r` and `ε` chosen by the proof, not universally). The consumer
`exists_smooth_rep_of_spatial` then restricts the `SpC` hypothesis `hspat` to the smaller ball
(`SpatialReg.SpC.mono_set`). `htime'` is derived (stages 2, 3) from:
`G t y = jetChart 1 0 v t y` (`hasDerivWithinAt_jetChart_time` gives the first clause), the equation
`existenceMap … v = ofSmooth f hf`, `hagree`, `h𝒩` (continuity of `𝒩` near `w`; `v` in a
neighbourhood `V` of `0` inside the continuity set, the `δ`-ball and the sup-norm tube), which gives
`jetChart 1 0 v = Ψ(t, y, jetChart 0 0 v, …, jetChart 0 (2p) v) + (f - ∂ₜ w)` with `Ψ` the Euclidean
reading of `F`; the jets `jetChart 0 i v` obey `hasFDerivAt_jetChart`, so `SpC` of
`jetChart 0 0 = repChart` propagates to all of them and `SpC.comp` gives the second clause.
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

variable (g s p m T) in
/-- The chart reading of the jet `∂ₜ^j ∇^i v̂ (t, φ⁻¹ y)` of the continuous representative. -/
def jetChart (α : M) (j i : ℕ) (v : ParabolicSpace g s p m T) (t : ℝ) (y : E) :
    TensorRSModel 0 (s + i) ℝ E :=
  chartRSTwistInv (I := I) (M := M) α ((extChartAt I α).symm y) 0 (s + i)
    (evalJet g s p m T j i t ((extChartAt I α).symm y) v)

theorem jetChart_sub (α : M) (j i : ℕ) (v w : ParabolicSpace g s p m T) (t : ℝ) (y : E) :
    jetChart g s p m T α j i v t y - jetChart g s p m T α j i w t y =
      jetChart g s p m T α j i (v - w) t y := by
  unfold jetChart
  rw [← chartRSTwistInv_sub_model, map_sub]

/-- On a smooth family, `jetChart` is the chart reading of `∇^i ∂ₜ^j u`. -/
theorem jetChart_coe (hT : 0 < T) {j i : ℕ} (hj : j < m)
    (hk : Module.finrank ℝ E / 2 + 1 + i ≤ 2 * p * (m - j - 1)) (α : M) {t : ℝ}
    (ht : t ∈ Icc 0 T) {y : E} (hy : y ∈ (extChartAt I α).target)
    (u : ParabolicPre g s p m T) :
    jetChart g s p m T α j i (u : ParabolicSpace g s p m T) t y =
      chartRd g α (iteratedCovGrad g 0 s i (timeDerivIter T u.family j t)) y := by
  unfold jetChart
  rw [evalJet_coe hT hj hk ht _ u, evalPre_apply, chartRd_eq_twist α _ hy]

/-- `jetChart` along an approximating sequence is within `C ‖u - v‖` of the limit. -/
theorem exists_norm_jetChart_le (hT : 0 < T) {j i : ℕ} (hj : j < m)
    (hk : Module.finrank ℝ E / 2 + 1 + i ≤ 2 * p * (m - j - 1)) (α : M) {Ky : Set E}
    (hK : IsCompact Ky) (hKt : Ky ⊆ (extChartAt I α).target) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ Ky, ∀ v w : ParabolicSpace g s p m T,
      ‖jetChart g s p m T α j i v t y - jetChart g s p m T α j i w t y‖ ≤ C * ‖v - w‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_twist_evalJet_le (g := g) (s := s) (p := p) (m := m) hT hj hk
    α hK hKt
  refine ⟨C, hC0, fun t ht y hy v w => ?_⟩
  rw [jetChart_sub]
  exact hC t ht y hy _

/-- A uniform bound `C a_n` gives uniform convergence. -/
theorem tendstoUniformlyOn_of_bound {X Y : Type*} [NormedAddCommGroup Y] {S : Set X}
    {F : ℕ → X → Y} {f : X → Y} {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0)) (C : ℝ)
    (hb : ∀ n, ∀ x ∈ S, ‖F n x - f x‖ ≤ C * a n) : TendstoUniformlyOn F f atTop S := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have h : Tendsto (fun n => C * a n) atTop (𝓝 0) := by simpa using ha.const_mul C
  filter_upwards [(tendsto_order.1 h).2 ε hε] with n hn x hx
  rw [dist_comm, dist_eq_norm]
  exact (hb n x hx).trans_lt hn

/-- An approximating sequence of smooth families. -/
theorem exists_seq_tendsto (v : ParabolicSpace g s p m T) :
    ∃ u : ℕ → ParabolicPre g s p m T,
      Tendsto (fun n => (u n : ParabolicSpace g s p m T)) atTop (𝓝 v) := by
  have hd := UniformSpace.Completion.denseRange_coe (α := ParabolicPre g s p m T)
  obtain ⟨x, hx, hlim⟩ := mem_closure_iff_seq_limit.1 (hd.closure_range ▸ mem_univ v)
  choose u hu using hx
  refine ⟨u, ?_⟩
  have : (fun n => (u n : ParabolicSpace g s p m T)) = x := funext hu
  rw [this]
  exact hlim

theorem tendsto_norm_sub_of_tendsto {u : ℕ → ParabolicSpace g s p m T} {v : ParabolicSpace g s p m T}
    (hu : Tendsto u atTop (𝓝 v)) : Tendsto (fun n => ‖u n - v‖) atTop (𝓝 0) := by
  simpa [tendsto_iff_norm_sub_tendsto_zero] using hu

/-- Uniform convergence in space, at a fixed time. -/
theorem tendstoUniformlyOn_jetChart_space (hT : 0 < T) {j i : ℕ} (hj : j < m)
    (hk : Module.finrank ℝ E / 2 + 1 + i ≤ 2 * p * (m - j - 1)) (α : M) {Ky : Set E}
    (hK : IsCompact Ky) (hKt : Ky ⊆ (extChartAt I α).target) {t : ℝ} (ht : t ∈ Icc 0 T)
    {v : ParabolicSpace g s p m T} {u : ℕ → ParabolicPre g s p m T}
    (hu : Tendsto (fun n => (u n : ParabolicSpace g s p m T)) atTop (𝓝 v)) :
    TendstoUniformlyOn (fun n y => jetChart g s p m T α j i (u n : ParabolicSpace g s p m T) t y)
      (jetChart g s p m T α j i v t) atTop Ky := by
  obtain ⟨C, -, hC⟩ := exists_norm_jetChart_le (g := g) (s := s) (p := p) (m := m) hT hj hk α hK hKt
  exact tendstoUniformlyOn_of_bound (tendsto_norm_sub_of_tendsto hu) C
    fun n y hy => hC t ht y hy _ _

/-- Uniform convergence in time, at a fixed point. -/
theorem tendstoUniformlyOn_jetChart_time (hT : 0 < T) {j i : ℕ} (hj : j < m)
    (hk : Module.finrank ℝ E / 2 + 1 + i ≤ 2 * p * (m - j - 1)) (α : M) {y : E}
    (hy : y ∈ (extChartAt I α).target)
    {v : ParabolicSpace g s p m T} {u : ℕ → ParabolicPre g s p m T}
    (hu : Tendsto (fun n => (u n : ParabolicSpace g s p m T)) atTop (𝓝 v)) :
    TendstoUniformlyOn (fun n t => jetChart g s p m T α j i (u n : ParabolicSpace g s p m T) t y)
      (fun t => jetChart g s p m T α j i v t y) atTop (Icc 0 T) := by
  obtain ⟨C, -, hC⟩ := exists_norm_jetChart_le (g := g) (s := s) (p := p) (m := m) hT hj hk α
    (isCompact_singleton (x := y)) (singleton_subset_iff.2 hy)
  exact tendstoUniformlyOn_of_bound (tendsto_norm_sub_of_tendsto hu) C
    fun n t ht => hC t ht y rfl _ _

/-- `jetChart` is jointly continuous on `[0,T] × K`. -/
theorem continuousOn_jetChart (hT : 0 < T) {j i : ℕ} (hj : j < m)
    (hk : Module.finrank ℝ E / 2 + 1 + i ≤ 2 * p * (m - j - 1)) (α : M) {Ky : Set E}
    (hK : IsCompact Ky) (hKt : Ky ⊆ (extChartAt I α).target) (v : ParabolicSpace g s p m T) :
    ContinuousOn (fun q : ℝ × E => jetChart g s p m T α j i v q.1 q.2) (Icc 0 T ×ˢ Ky) :=
  continuousOn_evalJet_chart hT hj hk α hK hKt v

/-- **The spatial recursion for the continuous representative.** On a patch where the frame `B`
has constant chart coordinates, for `y` in the open ball,
`D (jetChart j i) = slotIns (jetChart j (i+1)) + kerL (jetChart j i)`. -/
theorem hasFDerivAt_jetChart (hT : 0 < T) {j i : ℕ} (hj : j < m)
    (hk : Module.finrank ℝ E / 2 + 1 + (i + 1) ≤ 2 * p * (m - j - 1)) {α : M} {r : ℝ}
    {B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (hball : Metric.closedBall (extChartAt I α α) r ⊆ (extChartAt I α).target)
    (hB : ∀ y ∈ Metric.closedBall (extChartAt I α α) r, ∀ k,
      trivToE I α ((extChartAt I α).symm y) (B k ((extChartAt I α).symm y)) =
        Module.finBasis ℝ E k)
    (v : ParabolicSpace g s p m T) {t : ℝ} (ht : t ∈ Icc 0 T) {y : E}
    (hy : y ∈ Metric.ball (extChartAt I α α) r) :
    HasFDerivAt (jetChart g s p m T α j i v t)
      (slotIns E (s + i) (jetChart g s p m T α j (i + 1) v t y) +
        kerL g α (s + i) B y (jetChart g s p m T α j i v t y)) y := by
  have hk0 : Module.finrank ℝ E / 2 + 1 + i ≤ 2 * p * (m - j - 1) :=
    le_trans (by omega) hk
  obtain ⟨u, hu⟩ := exists_seq_tendsto v
  have hKc : IsCompact (Metric.closedBall (extChartAt I α α) r) := isCompact_closedBall _ _
  have hKcont : ContinuousOn (kerL g α (s + i) B) (Metric.closedBall (extChartAt I α α) r) :=
    (contDiffOn_kerL α (s + i) B).continuousOn.mono hball
  have hsub : Metric.ball (extChartAt I α α) r ⊆ Metric.closedBall (extChartAt I α α) r :=
    Metric.ball_subset_closedBall
  have hf : ∀ n, ∀ z ∈ Metric.ball (extChartAt I α α) r,
      HasFDerivAt (fun w => jetChart g s p m T α j i (u n : ParabolicSpace g s p m T) t w)
        (slotIns E (s + i) (jetChart g s p m T α j (i + 1) (u n : ParabolicSpace g s p m T) t z) +
          kerL g α (s + i) B z
            (jetChart g s p m T α j i (u n : ParabolicSpace g s p m T) t z)) z := by
    intro n z hz
    have hzt : z ∈ (extChartAt I α).target := hball (hsub hz)
    set S := iteratedCovGrad g 0 s i (timeDerivIter T (u n).family j t) with hS
    have hdiff : DifferentiableAt ℝ (chartRd g α S) z :=
      ((contDiffOn_chartRd α S).differentiableOn (by simp)).differentiableAt
        ((isOpen_extChartAt_target (I := I) α).mem_nhds hzt)
    have h1 := hdiff.hasFDerivAt
    rw [fderiv_chartRd_eq hball hB S (hsub hz)] at h1
    have e1 := jetChart_coe (g := g) (s := s) (p := p) (m := m) hT hj hk α ht hzt (u n)
    have e0 := jetChart_coe (g := g) (s := s) (p := p) (m := m) hT hj hk0 α ht hzt (u n)
    rw [e1, e0]
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_extChartAt_target (I := I) α).mem_nhds hzt] with w hw
    exact jetChart_coe (g := g) (s := s) (p := p) (m := m) hT hj hk0 α ht hw (u n)
  have hk' : Module.finrank ℝ E / 2 + 1 + (i + 1) ≤ 2 * p * (m - j - 1) := hk
  refine hasFDerivAt_limit_rec_compact (U := Metric.ball (extChartAt I α α) r) Metric.isOpen_ball
    (convex_ball _ _) hsub hKc (slotIns E (s + i)) (kerL g α (s + i) B) hKcont hf
    ((tendstoUniformlyOn_jetChart_space hT hj hk0 α hKc hball ht hu).mono hsub)
    ((tendstoUniformlyOn_jetChart_space hT hj hk' α hKc hball ht hu).mono hsub)
    ?_ ?_ y hy
  · have hf0 : ContinuousOn (fun z : E => (t, z)) (Metric.ball (extChartAt I α α) r) :=
      continuousOn_const.prodMk continuousOn_id
    have h := (continuousOn_jetChart hT hj hk0 α hKc hball v).comp hf0
      (fun z hz => ⟨ht, hsub hz⟩)
    simp only [Function.comp_def] at h
    exact h
  · have hf0 : ContinuousOn (fun z : E => (t, z)) (Metric.ball (extChartAt I α α) r) :=
      continuousOn_const.prodMk continuousOn_id
    have h := (continuousOn_jetChart hT hj hk' α hKc hball v).comp hf0
      (fun z hz => ⟨ht, hsub hz⟩)
    simp only [Function.comp_def] at h
    exact h

/-- **The time derivative of the continuous representative**: `∂ₜ (jetChart j i) = jetChart (j+1) i`
within `[0,T]`. -/
theorem hasDerivWithinAt_jetChart_time (hT : 0 < T) {j i : ℕ} (hj : j + 1 < m)
    (hk : Module.finrank ℝ E / 2 + 1 + i ≤ 2 * p * (m - (j + 1) - 1)) (α : M) {y : E}
    (hy : y ∈ (extChartAt I α).target) (v : ParabolicSpace g s p m T) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun τ => jetChart g s p m T α j i v τ y)
      (jetChart g s p m T α (j + 1) i v t y) (Icc 0 T) t := by
  have hj0 : j < m := by omega
  have hk0 : Module.finrank ℝ E / 2 + 1 + i ≤ 2 * p * (m - j - 1) :=
    le_trans hk (Nat.mul_le_mul_left _ (by omega))
  obtain ⟨u, hu⟩ := exists_seq_tendsto v
  have hf : ∀ n, ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun σ => jetChart g s p m T α j i (u n : ParabolicSpace g s p m T) σ y)
        (jetChart g s p m T α (j + 1) i (u n : ParabolicSpace g s p m T) τ y) (Icc 0 T) τ := by
    intro n τ hτ
    set A : ℝ → SmoothCcTensor g 0 (s + i) := fun σ => iteratedCovGrad g 0 s i ((u n).family σ)
      with hA
    have hAs : JointlySmoothOn g 0 (s + i) (Icc 0 T) A := jointlySmoothOn_iteratedCovGrad (u n).2 i
    have hD := hasDerivWithinAt_chartRd_time hT α
      (jointlySmoothOn_timeDerivIter hT hAs j) hτ hy
    have e : ∀ σ ∈ Icc (0 : ℝ) T, timeDerivIter T A j σ =
        iteratedCovGrad g 0 s i (timeDerivIter T (u n).family j σ) :=
      fun σ hσ => timeDerivIter_iteratedCovGrad hT (u n).2 i j hσ
    have e' : timeDeriv T (timeDerivIter T A j) τ =
        iteratedCovGrad g 0 s i (timeDerivIter T (u n).family (j + 1) τ) :=
      timeDerivIter_iteratedCovGrad hT (u n).2 i (j + 1) hτ
    have e2 := jetChart_coe (g := g) (s := s) (p := p) (m := m) hT hj hk α hτ hy (u n)
    rw [e2, ← e']
    refine hD.congr (fun σ hσ => ?_) ?_
    · rw [jetChart_coe (g := g) (s := s) (p := p) (m := m) hT hj0 hk0 α hσ hy (u n), e σ hσ]
    · rw [jetChart_coe (g := g) (s := s) (p := p) (m := m) hT hj0 hk0 α hτ hy (u n), e τ hτ]
  refine hasDerivWithinAt_of_tendstoUniformlyOn_Icc hf ?_
    (tendstoUniformlyOn_jetChart_time hT hj hk α hy hu) ?_ ht
  · intro τ hτ
    exact (tendstoUniformlyOn_jetChart_time hT hj0 hk0 α hy hu).tendsto_at hτ
  · have hKc : IsCompact ({y} : Set E) := isCompact_singleton
    have := continuousOn_jetChart hT hj hk α hKc (singleton_subset_iff.2 hy) v
    have hf0 : ContinuousOn (fun τ : ℝ => (τ, y)) (Icc 0 T) :=
      continuousOn_id.prodMk continuousOn_const
    have h := this.comp hf0 (fun τ hτ => ⟨hτ, rfl⟩)
    simp only [Function.comp_def] at h
    exact h

end SmoothRep

end ShortTime
