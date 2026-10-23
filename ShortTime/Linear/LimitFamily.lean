import ShortTime.Linear.LimitSmooth

/-!
# The limit family of a good sequence

For a good sequence `wₘ` (`Good`), the fibre values `wₘ(t)(x)` converge for every `t ∈ [0,T]`,
`x ∈ M` (`tendsto_limModel`). The limit is jointly smooth on `M × [0,T]` (`rawJoint_limSec`): in the
chart and trivialization at any point, its reading is the limit of the chart readings, which is
`C^∞` (`contDiffOn_limChart`). `limFam T w` packages it as a jointly smooth family of smooth tensor
fields.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff BigOperators

set_option linter.unusedSectionVars false

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

variable {g : SmoothRiemannianMetric I M} {T : ℝ}

theorem continuous_chartRSTwistInv (α b : M) (r s : ℕ) :
    Continuous (chartRSTwistInv (I := I) (M := M) α b r s) := by
  unfold chartRSTwistInv
  exact continuous_const.clm_comp (continuous_id.clm_comp continuous_const)

theorem continuous_chartRSTwist (α b : M) (r s : ℕ) :
    Continuous (chartRSTwist (I := I) (M := M) α b r s) := by
  unfold chartRSTwist
  exact continuous_const.clm_comp (continuous_id.clm_comp continuous_const)

/-- The pointwise limit of the model values `wₘ(t)(x)`. -/
def limModel {a : ℕ} (w : ℕ → ℝ → SmoothCcTensor g 0 a) (t : ℝ) (x : M) : TensorRSModel 0 a ℝ E :=
  limUnder atTop (fun m => TensorRSSpace.toModel ((w m t).toSection x))

theorem toModel_eq_twist_chartRd (α : M) {a : ℕ} (S : SmoothCcTensor g 0 a) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    TensorRSSpace.toModel (S.toSection x) =
      chartRSTwist (I := I) (M := M) α x 0 a (chartRd g α S (extChartAt I α x)) := by
  have hxs : x ∈ (extChartAt I α).source := by rw [extChartAt_source]; exact hx
  rw [chartRd_eq_twist α S ((extChartAt I α).map_source hxs), (extChartAt I α).left_inv hxs,
    chartRSTwist_chartRSTwistInv (I := I) (M := M) α (by
      rw [TangentBundle.trivializationAt_baseSet]; exact hx)]

theorem tendsto_limModel {a : ℕ} {w : ℕ → ℝ → SmoothCcTensor g 0 a} (hw : Good T w) {t : ℝ}
    (ht : t ∈ Icc 0 T) (x : M) :
    Tendsto (fun m => TensorRSSpace.toModel ((w m t).toSection x)) atTop
      (𝓝 (limModel w t x)) := by
  obtain ⟨r, hr, B, hball, -⟩ := exists_chart_patch (I := I) x
  have hx : x ∈ (chartAt H x).source := mem_chart_source H x
  have h1 := (tendstoUniformlyOn_limChart (g := g) hball hw.ucauchy).tendsto_at
    (show (t, extChartAt I x x) ∈ Icc 0 T ×ˢ Metric.closedBall (extChartAt I x x) r from
      ⟨ht, Metric.mem_closedBall_self hr.le⟩)
  have h2 := ((continuous_chartRSTwist (I := I) (M := M) x x 0 a).tendsto _).comp h1
  simp only [Function.comp_def, ← toModel_eq_twist_chartRd x _ hx] at h2
  exact tendsto_nhds_limUnder ⟨_, h2⟩

/-- In the chart at `α`, the limit values are read by the limit of the chart readings. -/
theorem twist_limModel {a : ℕ} {w : ℕ → ℝ → SmoothCcTensor g 0 a} (hw : Good T w) {α : M} {r : ℝ}
    (hball : Metric.closedBall (extChartAt I α α) r ⊆ (extChartAt I α).target) {t : ℝ}
    (ht : t ∈ Icc 0 T) {y : E} (hy : y ∈ Metric.closedBall (extChartAt I α α) r) :
    chartRSTwistInv (I := I) (M := M) α ((extChartAt I α).symm y) 0 a
        (limModel w t ((extChartAt I α).symm y)) = limChart g α w (t, y) := by
  have h1 := ((continuous_chartRSTwistInv (I := I) (M := M) α ((extChartAt I α).symm y) 0 a).tendsto _).comp
    (tendsto_limModel hw ht ((extChartAt I α).symm y))
  have h2 := (tendstoUniformlyOn_limChart (g := g) hball hw.ucauchy).tendsto_at
    (show (t, y) ∈ Icc 0 T ×ˢ Metric.closedBall (extChartAt I α α) r from ⟨ht, hy⟩)
  simp only [Function.comp_def, ← chartRd_eq_twist α _ (hball hy)] at h1
  exact tendsto_nhds_unique h1 h2

/-- Joint smoothness of a family of (not necessarily smooth) sections. -/
def RawJoint (r s : ℕ) (S : Set ℝ) (v : ℝ → (x : M) → TensorRSSpace r s I x) : Prop :=
  ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
    (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E) (E := fun x : M => TensorRSSpace r s I x)
      q.1 (v q.2 q.1)) ((Set.univ : Set M) ×ˢ S)

/-- The limit values, as fibre elements. -/
def limSec {a : ℕ} (w : ℕ → ℝ → SmoothCcTensor g 0 a) (t : ℝ) (x : M) : TensorRSSpace 0 a I x :=
  TensorRSSpace.ofModel (limModel w t x)

/-- **The limit of a good sequence is jointly smooth.** -/
theorem rawJoint_limSec (hT : 0 < T) {a : ℕ} {w : ℕ → ℝ → SmoothCcTensor g 0 a} (hw : Good T w) :
    RawJoint 0 a (Icc 0 T) (fun t x => limSec w t x) := by
  intro p₀ hp₀
  have ht₀ : p₀.2 ∈ Icc 0 T := hp₀.2
  obtain ⟨r, hr, B, hball, hB⟩ := exists_chart_patch (I := I) p₀.1
  set α := p₀.1 with hα
  set φ := extChartAt I α with hφ
  set U := (chartAt H α).source ∩ φ ⁻¹' Metric.ball (φ α) r with hU
  have hUo : IsOpen U := by
    have := (continuousOn_extChartAt (I := I) α).isOpen_inter_preimage (isOpen_extChartAt_source α)
      (Metric.isOpen_ball (x := φ α) (ε := r))
    rwa [extChartAt_source] at this
  have hαU : α ∈ U := ⟨mem_chart_source H α, Metric.mem_ball_self hr⟩
  have hL : ContDiffOn ℝ ∞ (limChart g α w) (Icc 0 T ×ˢ Metric.ball (φ α) r) :=
    contDiffOn_infty.2 fun n => contDiffOn_limChart hT hball hB n hw
  -- the chart reading of the limit, as a function on `M × ℝ`
  have hF : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, TensorRSModel 0 a ℝ E) ∞
      (fun p : M × ℝ => limChart g α w (p.2, φ p.1)) (U ×ˢ Icc 0 T) p₀ := by
    have hmove : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × E) ∞
        (fun q : M × ℝ => (q.2, φ q.1)) (U ×ˢ Icc 0 T) p₀ := by
      have hmoveOn : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
          (fun q : M × ℝ => (q.2, φ q.1)) (U ×ˢ Icc 0 T) := by
        refine ContMDiffOn.prodMk contMDiffOn_snd ?_
        exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst
          (fun q hq => hq.1.1)
      have hm := hmoveOn p₀ ⟨hαU, ht₀⟩
      rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
      exact hm
    have hEuM : ContMDiffWithinAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ, TensorRSModel 0 a ℝ E) ∞ (limChart g α w)
        (Icc 0 T ×ˢ Metric.ball (φ α) r) (p₀.2, φ p₀.1) := by
      rw [contMDiffWithinAt_iff_contDiffWithinAt]
      exact hL _ ⟨ht₀, Metric.mem_ball_self hr⟩
    have hc := hEuM.comp p₀ hmove (fun q hq =>
      (⟨hq.2, hq.1.2⟩ : (q.2, φ q.1) ∈ Icc 0 T ×ˢ Metric.ball (φ α) r))
    exact hc
  have hbase : ∀ p : M × ℝ, p.1 ∈ (chartAt H α).source →
      p.1 ∈ (trivializationAt (TensorRSModel 0 a ℝ E) (fun y : M => TensorRSSpace 0 a I y) α).baseSet := by
    intro p hp
    change p.1 ∈ ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) α).baseSet) ∩
        ((trivializationAt (Tensor0SBundle.Tensor0SModel a ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace a I y) α).baseSet)
    refine ⟨?_, ?_⟩ <;>
      · change p.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet
        rw [TangentBundle.trivializationAt_baseSet]
        exact hp
  have hval : ∀ p : M × ℝ, p ∈ U ×ˢ Icc 0 T →
      ((trivializationAt (TensorRSModel 0 a ℝ E) (fun y : M => TensorRSSpace 0 a I y) α)
        ⟨p.1, limSec w p.2 p.1⟩).2 = limChart g α w (p.2, φ p.1) := by
    intro p hp
    have hsrc : p.1 ∈ φ.source := by rw [hφ, extChartAt_source]; exact hp.1.1
    have e1 : ((trivializationAt (TensorRSModel 0 a ℝ E) (fun y : M => TensorRSSpace 0 a I y) α)
        ⟨p.1, limSec w p.2 p.1⟩).2 =
        (trivializationAt (TensorRSModel 0 a ℝ E) (fun y : M => TensorRSSpace 0 a I y)
          α).continuousLinearMapAt ℝ p.1 (limSec w p.2 p.1) := by
      rw [Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ (hbase p hp.1.1)]
    rw [e1, triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel 0 a α hp.1.1, limSec,
      TensorRSSpace.toModel_ofModel]
    have h := twist_limModel hw hball hp.2 (Metric.ball_subset_closedBall hp.1.2)
    rwa [φ.left_inv hsrc] at h
  have hsource : (⟨p₀.1, limSec w p₀.2 p₀.1⟩ : TotalSpace (TensorRSModel 0 a ℝ E)
      (fun y : M => TensorRSSpace 0 a I y)) ∈
      (trivializationAt (TensorRSModel 0 a ℝ E) (fun y : M => TensorRSSpace 0 a I y) α).source := by
    rw [Bundle.Trivialization.mem_source]
    exact hbase p₀ (mem_chart_source H α)
  have hfib : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, TensorRSModel 0 a ℝ E) ∞
      (fun p : M × ℝ => ((trivializationAt (TensorRSModel 0 a ℝ E)
        (fun y : M => TensorRSSpace 0 a I y) α) ⟨p.1, limSec w p.2 p.1⟩).2) (U ×ˢ Icc 0 T) p₀ :=
    hF.congr_of_eventuallyEq (Filter.eventually_of_mem self_mem_nhdsWithin hval)
      (hval p₀ ⟨hαU, ht₀⟩)
  have h := (Bundle.Trivialization.contMDiffWithinAt_iff (IM := I.prod 𝓘(ℝ, ℝ)) (n := ∞)
    (f := fun p : M × ℝ => (⟨p.1, limSec w p.2 p.1⟩ :
      TotalSpace (TensorRSModel 0 a ℝ E) (fun y : M => TensorRSSpace 0 a I y)))
    (s := U ×ˢ Icc 0 T) (x₀ := p₀)
    (e := trivializationAt (TensorRSModel 0 a ℝ E) (fun y : M => TensorRSSpace 0 a I y) α)
    hsource).mpr ⟨contMDiffWithinAt_fst, hfib⟩
  have hnhd : U ×ˢ (Set.univ : Set ℝ) ∈ 𝓝 p₀ :=
    (hUo.prod isOpen_univ).mem_nhds ⟨hαU, Set.mem_univ _⟩
  have hset : U ×ˢ Icc 0 T = ((Set.univ : Set M) ×ˢ Icc 0 T) ∩ U ×ˢ (Set.univ : Set ℝ) := by
    ext p; simp only [Set.mem_prod, Set.mem_inter_iff, Set.mem_univ, true_and, and_true]; tauto
  rw [hset] at h
  exact (contMDiffWithinAt_inter hnhd).mp h

/-- Smoothness of a time slice of a jointly smooth family. -/
theorem RawJoint.slice {r s : ℕ} {S : Set ℝ} {v : ℝ → (x : M) → TensorRSSpace r s I x}
    (hv : RawJoint r s S v) {t : ℝ} (ht : t ∈ S) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun x => TotalSpace.mk' (TensorRSModel r s ℝ E) (E := fun x : M => TensorRSSpace r s I x) x
        (v t x)) := by
  have hsl : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞ (fun y : M => (y, t)) :=
    contMDiff_id.prodMk contMDiff_const
  exact hv.comp_contMDiff hsl fun _ => ⟨Set.mem_univ _, ht⟩

variable (T) in
open Classical in
/-- **The limit family** of a good sequence (zero outside `[0,T]`). -/
def limFam {a : ℕ} (w : ℕ → ℝ → SmoothCcTensor g 0 a) (t : ℝ) : SmoothCcTensor g 0 a :=
  if h : 0 < T ∧ Good T w ∧ t ∈ Icc 0 T then
    { toSection := ⟨fun x => limSec w t x, (rawJoint_limSec h.1 h.2.1).slice h.2.2⟩
      hasCompactSupport := HasCompactSupport.of_compactSpace _ }
  else 0

theorem limFam_toSection (hT : 0 < T) {a : ℕ} {w : ℕ → ℝ → SmoothCcTensor g 0 a} (hw : Good T w)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : M) : (limFam T w t).toSection x = limSec w t x := by
  unfold limFam
  rw [dif_pos ⟨hT, hw, ht⟩]
  rfl

theorem jointlySmoothOn_limFam (hT : 0 < T) {a : ℕ} {w : ℕ → ℝ → SmoothCcTensor g 0 a}
    (hw : Good T w) : JointlySmoothOn g 0 a (Icc 0 T) (limFam T w) :=
  (rawJoint_limSec hT hw).congr fun q hq => by rw [limFam_toSection hT hw hq.2]

/-- The members of a good sequence converge pointwise to the limit family. -/
theorem tendsto_limFam (hT : 0 < T) {a : ℕ} {w : ℕ → ℝ → SmoothCcTensor g 0 a} (hw : Good T w)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : M) :
    Tendsto (fun m => TensorRSSpace.toModel ((w m t).toSection x)) atTop
      (𝓝 (TensorRSSpace.toModel ((limFam T w t).toSection x))) := by
  rw [limFam_toSection hT hw ht, limSec, TensorRSSpace.toModel_ofModel]
  exact tendsto_limModel hw ht x

/-! ### Covariant derivatives of good sequences -/

theorem UCauchy.heq {a a' : ℕ} (h : a = a') {w : ℕ → ℝ → SmoothCcTensor g 0 a}
    {w' : ℕ → ℝ → SmoothCcTensor g 0 a'} (hww : ∀ m, ∀ t ∈ Icc (0 : ℝ) T, HEq (w m t) (w' m t))
    (hw : UCauchy T w) : UCauchy T w' := by
  subst h
  exact hw.congr fun m t ht => (eq_of_heq (hww m t ht)).symm

/-- `∇^k` preserves good sequences. -/
theorem Good.iterCovGrad (hT : 0 < T) {a : ℕ} (k : ℕ) {w : ℕ → ℝ → SmoothCcTensor g 0 a}
    (hw : Good T w) : Good T (fun m t => iteratedCovGrad g 0 a k (w m t)) := by
  refine ⟨fun m => jointlySmoothOn_iteratedCovGrad (hw.1 m) k, fun i j => ?_⟩
  refine UCauchy.heq (by omega : a + (k + i) = a + k + i) (fun m t ht => ?_) (hw.2 (k + i) j)
  rw [timeDerivIter_iteratedCovGrad hT (hw.1 m) k j ht]
  exact (iteratedCovGrad_comp_heq 0 a k _ i).symm

/-! ### The limit commutes with `∂ₜ` and `∇` -/

theorem chartRd_limFam (hT : 0 < T) {a : ℕ} {w : ℕ → ℝ → SmoothCcTensor g 0 a} (hw : Good T w)
    {α : M} {r : ℝ} (hball : Metric.closedBall (extChartAt I α α) r ⊆ (extChartAt I α).target)
    {t : ℝ} (ht : t ∈ Icc 0 T) {y : E} (hy : y ∈ Metric.closedBall (extChartAt I α α) r) :
    chartRd g α (limFam T w t) y = limChart g α w (t, y) := by
  rw [chartRd_eq_twist α _ (hball hy), limFam_toSection hT hw ht, limSec, TensorRSSpace.toModel_ofModel]
  exact twist_limModel hw hball ht hy

theorem toModel_eq_of_chartRd_center {a : ℕ} {S S' : SmoothCcTensor g 0 a} (x : M)
    (h : chartRd g x S (extChartAt I x x) = chartRd g x S' (extChartAt I x x)) :
    TensorRSSpace.toModel (S.toSection x) = TensorRSSpace.toModel (S'.toSection x) := by
  rw [toModel_eq_twist_chartRd x S (mem_chart_source H x),
    toModel_eq_twist_chartRd x S' (mem_chart_source H x), h]

/-- Slices of the derivative of the limit chart reading. -/
theorem limChart_slices (hT : 0 < T) {α : M} {r : ℝ}
    {B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (hball : Metric.closedBall (extChartAt I α α) r ⊆ (extChartAt I α).target)
    (hB : ∀ y ∈ Metric.closedBall (extChartAt I α α) r, ∀ k,
      trivToE I α ((extChartAt I α).symm y) (B k ((extChartAt I α).symm y)) = Module.finBasis ℝ E k)
    {a : ℕ} {w : ℕ → ℝ → SmoothCcTensor g 0 a} (hw : Good T w) {t : ℝ} (ht : t ∈ Icc 0 T)
    {y : E} (hy : y ∈ Metric.ball (extChartAt I α α) r) :
    HasDerivWithinAt (fun τ => limChart g α w (τ, y))
        (limChart g α (fun m => timeDeriv T (w m)) (t, y)) (Icc 0 T) t ∧
      ∀ k, fderiv ℝ (fun y' => limChart g α w (t, y')) y (Module.finBasis ℝ E k) =
        limChart g α (fun m t => operatorFieldApply (I := I) (M := M) g (a + 1) a
          (insField g (B k)) (covGrad (I := I) (M := M) g 0 a (w m t))) (t, y) +
          kerSum g α a (B k) y (limChart g α w (t, y)) := by
  have hD := hasFDerivWithinAt_limChart hT hball hB hw (q := (t, y)) ⟨ht, hy⟩
  refine ⟨?_, fun k => ?_⟩
  · have hin : HasDerivAt (fun τ : ℝ => (τ, y)) ((1 : ℝ), (0 : E)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
    have h := hD.comp_hasDerivWithinAt t hin.hasDerivWithinAt
      (fun τ hτ => (⟨hτ, hy⟩ : (τ, y) ∈ Icc 0 T ×ˢ Metric.ball (extChartAt I α α) r))
    simp only [combL_apply, one_smul, map_zero, zero_smul, Finset.sum_const_zero, add_zero] at h
    exact h
  · have hin : HasFDerivAt (fun y' : E => (t, y')) (ContinuousLinearMap.inr ℝ ℝ E) y :=
      (hasFDerivAt_const t y).prodMk (hasFDerivAt_id y)
    have h := hD.comp y hin.hasFDerivWithinAt
      (fun y' hy' => (⟨ht, hy'⟩ : (t, y') ∈ Icc 0 T ×ˢ Metric.ball (extChartAt I α α) r))
    have h2 := (h.hasFDerivAt (Metric.isOpen_ball.mem_nhds hy)).fderiv
    rw [show (fun y' => limChart g α w (t, y')) = limChart g α w ∘ Prod.mk t from rfl, h2]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, combL_apply, zero_smul,
      zero_add]
    rw [Finset.sum_eq_single k]
    · simp [coordL]
    · intro j _ hj
      simp [coordL, Module.Basis.repr_self, Finsupp.single_apply, Ne.symm hj]
    · simp

/-- **`∂ₜ` commutes with the limit.** -/
theorem timeDeriv_limFam (hT : 0 < T) {a : ℕ} {w : ℕ → ℝ → SmoothCcTensor g 0 a} (hw : Good T w)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    timeDeriv T (limFam T w) t = limFam T (fun m => timeDeriv T (w m)) t := by
  refine smoothCcTensor_eq_of_toFun fun x => ?_
  refine toModel_eq_of_chartRd_center x ?_
  obtain ⟨r, hr, B, hball, hB⟩ := exists_chart_patch (I := I) x
  have hc : extChartAt I x x ∈ Metric.closedBall (extChartAt I x x) r := Metric.mem_closedBall_self hr.le
  have h1 := hasDerivWithinAt_chartRd_time hT x (jointlySmoothOn_limFam hT hw) ht (hball hc)
  have h2 := (limChart_slices hT hball hB hw ht (Metric.mem_ball_self hr)).1.congr_of_mem
    (fun τ hτ => chartRd_limFam hT hw hball hτ hc) ht
  rw [(uniqueDiffOn_Icc hT t ht).eq_deriv _ h1 h2,
    chartRd_limFam hT (hw.timeDeriv hT) hball ht hc]

/-- An operator field at `x`, read in the model fibres. -/
def psiAt {b c : ℕ} (Φ : SmoothCcTensor g b c) (x : M) :
    Tensor0SModel b ℝ E →L[ℝ] Tensor0SModel c ℝ E :=
  (tensor0SSpaceContinuousLinearEquiv (I := I) c x).toContinuousLinearMap.comp
    ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x).comp
      (tensor0SSpaceContinuousLinearEquiv (I := I) b x).symm.toContinuousLinearMap)

theorem toModel_opField_apply {b c : ℕ} (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g 0 b)
    (x : M) :
    TensorRSSpace.toModel ((operatorFieldApply (I := I) (M := M) g b c Φ W).toSection x) =
      (psiAt Φ x).comp (TensorRSSpace.toModel (W.toSection x)) := by
  refine ContinuousLinearMap.ext fun β => ?_
  rw [toModel_tensorRS_apply, ContinuousLinearMap.comp_apply, toModel_tensorRS_apply, psiAt,
    operatorFieldApplication_toSection]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]
  rfl

/-- A fixed operator field commutes with the pointwise limit. -/
theorem tendsto_opField_limFam (hT : 0 < T) {b c : ℕ} (Φ : SmoothCcTensor g b c)
    {w : ℕ → ℝ → SmoothCcTensor g 0 b} (hw : Good T w) {t : ℝ} (ht : t ∈ Icc 0 T) (x : M) :
    Tendsto (fun m => TensorRSSpace.toModel
        ((operatorFieldApply (I := I) (M := M) g b c Φ (w m t)).toSection x)) atTop
      (𝓝 (TensorRSSpace.toModel
        ((operatorFieldApply (I := I) (M := M) g b c Φ (limFam T w t)).toSection x))) := by
  simp only [toModel_opField_apply]
  exact ((continuous_const.clm_comp continuous_id).tendsto _).comp (tendsto_limFam hT hw ht x)

/-- Vectors are combinations of the frame vectors `B k x`. -/
theorem eq_sum_frame {x : M} {B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (hB : ∀ k, trivToE I x x (B k x) = Module.finBasis ℝ E k) (v : TangentSpace I x) :
    v = ∑ k, coordL k (trivToE I x x v) • B k x := by
  have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := mem_baseSet_trivializationAt _ _ x
  have hsym : ∀ k, (trivializationAt E (TangentSpace I) x).symmL ℝ x (Module.finBasis ℝ E k) = B k x :=
    fun k => by
      rw [← hB k]
      exact (trivializationAt E (TangentSpace I) x).symmL_continuousLinearMapAt (R := ℝ) hx _
  conv_lhs => rw [← (trivializationAt E (TangentSpace I) x).symmL_continuousLinearMapAt (R := ℝ) hx v,
    ← sum_coordL_smul ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x v)]
  rw [map_sum]
  simp only [map_smul, hsym]

/-- Two tensors with the same contractions against a frame are equal. -/
theorem model_eq_of_curryLeft_frame {a : ℕ} {x : M}
    {B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (hB : ∀ k, trivToE I x x (B k x) = Module.finBasis ℝ E k)
    {ζ ζ' : Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel (a + 1) ℝ E}
    (h : ∀ k β, (ζ β).curryLeft (tangentSpaceModelContinuousLinearEquiv (I := I) x (B k x)) =
      (ζ' β).curryLeft (tangentSpaceModelContinuousLinearEquiv (I := I) x (B k x))) : ζ = ζ' := by
  refine ContinuousLinearMap.ext fun β => ContinuousMultilinearMap.ext fun m => ?_
  rw [← Fin.cons_self_tail m, ← ContinuousMultilinearMap.curryLeft_apply,
    ← ContinuousMultilinearMap.curryLeft_apply]
  set e := tangentSpaceModelContinuousLinearEquiv (I := I) x
  have hm : m 0 = ∑ k, coordL k (trivToE I x x (e.symm (m 0))) • e (B k x) := by
    have := congrArg e (eq_sum_frame (I := I) hB (e.symm (m 0)))
    rw [map_sum] at this
    simp only [map_smul, ContinuousLinearEquiv.apply_symm_apply] at this
    exact this
  rw [hm]
  simp only [map_sum, map_smul, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, h]

theorem psiAt_insField {a : ℕ} (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M)
    (D : Tensor0SModel (a + 1) ℝ E) :
    psiAt (insField g B) x D = D.curryLeft (tangentSpaceModelContinuousLinearEquiv (I := I) x (B x)) :=
  rfl

theorem Good.covGrad (hT : 0 < T) {a : ℕ} {w : ℕ → ℝ → SmoothCcTensor g 0 a} (hw : Good T w) :
    Good T (fun m t => covGrad (I := I) (M := M) g 0 a (w m t)) :=
  hw.iterCovGrad hT 1

/-- **`∇` commutes with the limit.** -/
theorem covGrad_limFam (hT : 0 < T) {a : ℕ} {w : ℕ → ℝ → SmoothCcTensor g 0 a} (hw : Good T w)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    covGrad (I := I) (M := M) g 0 a (limFam T w t) =
      limFam T (fun m t => covGrad (I := I) (M := M) g 0 a (w m t)) t := by
  refine smoothCcTensor_eq_of_toFun fun x => ?_
  obtain ⟨r, hr, B, hball, hB⟩ := exists_chart_patch (I := I) x
  have hc : extChartAt I x x ∈ Metric.closedBall (extChartAt I x x) r :=
    Metric.mem_closedBall_self hr.le
  have hxx : (extChartAt I x).symm (extChartAt I x x) = x := extChartAt_to_inv x
  have hB0 : ∀ k, trivToE I x x (B k x) = Module.finBasis ℝ E k := fun k => by
    have := hB _ hc k
    rwa [hxx] at this
  have key : ∀ k, TensorRSSpace.toModel ((operatorFieldApply (I := I) (M := M) g (a + 1) a
      (insField g (B k)) (covGrad (I := I) (M := M) g 0 a (limFam T w t))).toSection x) =
      TensorRSSpace.toModel ((operatorFieldApply (I := I) (M := M) g (a + 1) a (insField g (B k))
      (limFam T (fun m t => covGrad (I := I) (M := M) g 0 a (w m t)) t)).toSection x) := by
    intro k
    have hQ := tendsto_nhds_unique
      (tendsto_opField_limFam hT (insField g (B k)) (hw.covGrad hT) ht x)
      (tendsto_limFam hT (hw.opField_covGrad hT (insField g (B k))) ht x)
    rw [hQ]
    refine toModel_eq_of_chartRd_center x ?_
    rw [chartRd_limFam hT (hw.opField_covGrad hT (insField g (B k))) hball ht hc]
    have hF := fderiv_chartRd x (limFam T w t) (B k) (hball hc)
    rw [hB _ hc k] at hF
    have hev : chartRd g x (limFam T w t) =ᶠ[𝓝 (extChartAt I x x)]
        fun y' => limChart g x w (t, y') :=
      Filter.eventually_of_mem (Metric.ball_mem_nhds _ hr) fun y hy =>
        chartRd_limFam hT hw hball ht (Metric.ball_subset_closedBall hy)
    rw [hev.fderiv_eq, (limChart_slices hT hball hB hw ht (Metric.mem_ball_self hr)).2 k,
      chartRd_limFam hT hw hball ht hc, kerSum, ContinuousLinearMap.sum_apply] at hF
    exact (add_right_cancel hF).symm
  have hmain : TensorRSSpace.toModel ((covGrad (I := I) (M := M) g 0 a (limFam T w t)).toSection x) =
      TensorRSSpace.toModel
        ((limFam T (fun m t => covGrad (I := I) (M := M) g 0 a (w m t)) t).toSection x) := by
    refine model_eq_of_curryLeft_frame hB0 fun k β => ?_
    have := congrArg (fun ζ => ζ β) (key k)
    simp only [toModel_opField_apply, ContinuousLinearMap.comp_apply, psiAt_insField] at this
    exact this
  exact hmain

theorem Good.timeDerivIter (hT : 0 < T) {a : ℕ} {w : ℕ → ℝ → SmoothCcTensor g 0 a} (hw : Good T w) :
    ∀ j, Good T (fun m => ShortTime.timeDerivIter T (w m) j)
  | 0 => hw
  | j + 1 => by
    have e : (fun m => ShortTime.timeDerivIter T (w m) (j + 1)) =
        fun m => ShortTime.timeDerivIter T (ShortTime.timeDeriv T (w m)) j :=
      funext fun m => timeDerivIter_succ' (w m) j
    rw [e]
    exact Good.timeDerivIter hT (hw.timeDeriv hT) j

/-- **`∂ₜ^j` commutes with the limit.** -/
theorem timeDerivIter_limFam (hT : 0 < T) {a : ℕ} :
    ∀ j {w : ℕ → ℝ → SmoothCcTensor g 0 a}, Good T w → ∀ {t : ℝ}, t ∈ Icc 0 T →
      timeDerivIter T (limFam T w) j t = limFam T (fun m => timeDerivIter T (w m) j) t
  | 0, _, _, _, _ => rfl
  | j + 1, w, hw, t, ht => by
    rw [timeDerivIter_succ', timeDerivIter_congr hT
        (jointlySmoothOn_timeDeriv hT (jointlySmoothOn_limFam hT hw))
        (jointlySmoothOn_limFam hT (hw.timeDeriv hT)) (fun τ hτ => timeDeriv_limFam hT hw hτ) j ht,
      timeDerivIter_limFam hT j (hw.timeDeriv hT) ht]
    simp only [timeDerivIter_succ']

/-- **`∇^i` commutes with the limit.** -/
theorem iteratedCovGrad_limFam (hT : 0 < T) {a : ℕ} {w : ℕ → ℝ → SmoothCcTensor g 0 a}
    (hw : Good T w) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∀ i, iteratedCovGrad g 0 a i (limFam T w t) =
      limFam T (fun m t => iteratedCovGrad g 0 a i (w m t)) t
  | 0 => rfl
  | i + 1 => by
    change covGrad (I := I) (M := M) g 0 (a + i) (iteratedCovGrad g 0 a i (limFam T w t)) = _
    rw [iteratedCovGrad_limFam hT hw ht i, covGrad_limFam hT (hw.iterCovGrad hT i) ht]
    rfl

/-- **`∇^i ∂ₜ^j` commutes with the limit.** -/
theorem jet_limFam (hT : 0 < T) {a : ℕ} {w : ℕ → ℝ → SmoothCcTensor g 0 a} (hw : Good T w)
    {t : ℝ} (ht : t ∈ Icc 0 T) (i j : ℕ) :
    iteratedCovGrad g 0 a i (timeDerivIter T (limFam T w) j t) =
      limFam T (fun m t => iteratedCovGrad g 0 a i (timeDerivIter T (w m) j t)) t := by
  rw [timeDerivIter_limFam hT j hw ht, iteratedCovGrad_limFam hT (hw.timeDerivIter hT j) ht i]

/-- The jets of the members converge pointwise to those of the limit. -/
theorem tendsto_jet_limFam (hT : 0 < T) {a : ℕ} {w : ℕ → ℝ → SmoothCcTensor g 0 a} (hw : Good T w)
    {t : ℝ} (ht : t ∈ Icc 0 T) (i j : ℕ) (x : M) :
    Tendsto (fun m => TensorRSSpace.toModel
        ((iteratedCovGrad g 0 a i (timeDerivIter T (w m) j t)).toSection x)) atTop
      (𝓝 (TensorRSSpace.toModel
        ((iteratedCovGrad g 0 a i (timeDerivIter T (limFam T w) j t)).toSection x))) := by
  rw [jet_limFam hT hw ht]
  exact tendsto_limFam hT ((hw.timeDerivIter hT j).iterCovGrad hT i) ht x

end ShortTime
