import ShortTime.Nonlinear.FlowsNaturalEuclid
import ShortTime.Nonlinear.FlowsGroup
import ShortTime.Nonlinear.FibreMapChart
import ShortTime.Nonlinear.LocalRep
import ShortTime.Setting.LinearData

/-!
# Jets of the horizontal pullback in a chart

Paper: Lemma `lem:flows` (d), the formula `j^N(Π_σ u) = Θ_σ (Π_σ j^N u)`, read in a chart.

Fix `α ∈ M` and a chart patch at `α` (`exists_chart_patch`). For `(σ, y)` in the open set
`flowDom α` (both `y` and the chart coordinates of `φ_σ(x)`, `x = chart⁻¹ y`, lie in the patch),
the chart readings at `α` of the covariant jet of `Π_σ u` at `x` are a smooth linear function
`jetMap α N (σ, y)` of the chart readings of the jet of `u` at `φ_σ(x)` (`trivJet_hpull`):

  `trivJet α x (j^N (Π_σ u) x) = jetMap α N (σ, y) (trivJet α (φ_σ x) (j^N u (φ_σ x)))`.

The map `jetMap α N` is smooth on `flowDom α` and is the identity at `σ = 0`. It does not depend on
`u`. The proof feeds the chart recursion `fderiv_chartRd_eq` into the Euclidean lemma
`FlowNat.jetCoef_rep`, with `ψ(σ, y) = chart(φ_σ(chart⁻¹ y))` and `Q(σ, y)` the chart reading of
`P_σ(x)⁻¹` (`flowQ`).
-/

noncomputable section

open Bundle Manifold Set Filter
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

namespace ShortTime

namespace HFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

/-! ### Generalities -/

theorem trivAt_baseSet (a : ℕ) (α : M) : (trivAt I M 0 a α).baseSet = (chartAt H α).source := by
  change ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
      (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) α).baseSet) ∩
      ((trivializationAt (Tensor0SBundle.Tensor0SModel a ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace a I y) α).baseSet) = (chartAt H α).source
  change (trivializationAt E (TangentSpace I) α).baseSet ∩
      (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source
  rw [Set.inter_self]
  rfl

theorem mem_trivAt_baseSet {a : ℕ} {α x : M} (hx : x ∈ (extChartAt I α).source) :
    x ∈ (trivAt I M 0 a α).baseSet := by
  rw [trivAt_baseSet]
  rwa [extChartAt_source] at hx

theorem mem_jetBase_of_source {s N : ℕ} {α x : M} (hx : x ∈ (extChartAt I α).source) :
    x ∈ jetBase (I := I) 0 s N α :=
  ⟨mem_trivAt_baseSet hx, mem_iInter.2 fun _ => mem_trivAt_baseSet hx⟩

theorem chartRd_eq_trivAt {g : SmoothRiemannianMetric I M} (α : M) {a : ℕ}
    (S : SmoothCcTensor g 0 a) (y : E) :
    chartRd g α S y = (trivAt I M 0 a α).continuousLinearMapAt ℝ ((extChartAt I α).symm y)
      (S.toSection ((extChartAt I α).symm y)) := rfl

variable (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
variable (g : SmoothRiemannianMetric I M) (s : ℕ)

theorem mk_pt_symm (σ : ℝ) (x : M) (w : TensorRSSpace 0 s I (flow X σ x)) :
    (⟨x, (pt X g s σ x).symm w⟩ :
      TotalSpace (TensorRSModel 0 s ℝ E) (fun z : M => TensorRSSpace 0 s I z)) =
      ⟨flow X 0 x, (ptRaw X g s σ x).symm w⟩ := by
  unfold pt
  rw [ContinuousLinearEquiv.symm_trans_apply]
  exact mk_fibCast_symm _ _

theorem pt_zero_symm (x : M) (w : TensorRSSpace 0 s I (flow X 0 x)) :
    (pt X g s 0 x).symm w = (fibCast (flow_zero X x).symm).symm w := by
  unfold pt
  rw [ContinuousLinearEquiv.symm_trans_apply]
  congr 1
  rw [ContinuousLinearEquiv.symm_apply_eq, ptRaw_zero]

theorem clmAt_fibCast_symm_symmL {a : ℕ} {α : M} {x y : M} (h : x = y)
    (hx : x ∈ (trivAt I M 0 a α).baseSet) (v : TensorRSModel 0 a ℝ E) :
    (trivAt I M 0 a α).continuousLinearMapAt ℝ x
      ((fibCast h).symm ((trivAt I M 0 a α).symmL ℝ y v)) = v := by
  subst h
  exact (trivAt I M 0 a α).continuousLinearMapAt_symmL hx v

/-! ### The chart patch and the flow domain -/

/-- The radius of the chart patch at `α`. -/
def patchR (α : M) : ℝ := (exists_chart_patch (I := I) α).choose

/-- Vector fields with constant chart coordinates on the patch at `α`. -/
def patchB (α : M) : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  (exists_chart_patch (I := I) α).choose_spec.2.choose

theorem patchR_pos (α : M) : 0 < patchR (I := I) α := (exists_chart_patch (I := I) α).choose_spec.1

theorem patch_subset (α : M) :
    Metric.closedBall (extChartAt I α α) (patchR (I := I) α) ⊆ (extChartAt I α).target :=
  (exists_chart_patch (I := I) α).choose_spec.2.choose_spec.1

theorem patchB_spec (α : M) :
    ∀ y ∈ Metric.closedBall (extChartAt I α α) (patchR (I := I) α), ∀ k,
      trivToE I α ((extChartAt I α).symm y) (patchB (I := I) α k ((extChartAt I α).symm y)) =
        Module.finBasis ℝ E k :=
  (exists_chart_patch (I := I) α).choose_spec.2.choose_spec.2

/-- The open patch `Ω_α`. -/
def patchΩ (α : M) : Set E := Metric.ball (extChartAt I α α) (patchR (I := I) α)

theorem patchΩ_subset_closedBall (α : M) :
    patchΩ (I := I) α ⊆ Metric.closedBall (extChartAt I α α) (patchR (I := I) α) :=
  Metric.ball_subset_closedBall

theorem patchΩ_subset_target (α : M) : patchΩ (I := I) α ⊆ (extChartAt I α).target :=
  (patchΩ_subset_closedBall α).trans (patch_subset α)

theorem isOpen_patchΩ (α : M) : IsOpen (patchΩ (I := I) α) := Metric.isOpen_ball

theorem mem_patchΩ_self (α : M) : extChartAt I α α ∈ patchΩ (I := I) α :=
  Metric.mem_ball_self (patchR_pos α)

/-- The point `φ_σ(chart⁻¹ y)`. -/
def flowPt (α : M) (q : ℝ × E) : M := flow X q.1 ((extChartAt I α).symm q.2)

/-- The flow domain: `y` and `chart(φ_σ(chart⁻¹ y))` lie in the patch. -/
def flowDom (α : M) : Set (ℝ × E) :=
  {q | q.2 ∈ patchΩ (I := I) α ∧ flowPt X α q ∈ (extChartAt I α).source ∧
    extChartAt I α (flowPt X α q) ∈ patchΩ (I := I) α}

/-- The flow in chart coordinates, `ψ(σ, y) = chart(φ_σ(chart⁻¹ y))`. -/
def flowψ (α : M) (q : ℝ × E) : E := extChartAt I α (flowPt X α q)

theorem contMDiffOn_flowPt (α : M) :
    ContMDiffOn 𝓘(ℝ, ℝ × E) I ∞ (flowPt X α) {q | q.2 ∈ (extChartAt I α).target} := by
  have h1 : ContMDiff 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × E => q.1) := contDiff_fst.contMDiff
  have h2 : ContMDiff 𝓘(ℝ, ℝ × E) 𝓘(ℝ, E) ∞ (fun q : ℝ × E => q.2) := contDiff_snd.contMDiff
  have h3 : ContMDiffOn 𝓘(ℝ, ℝ × E) I ∞ (fun q : ℝ × E => (extChartAt I α).symm q.2)
      {q | q.2 ∈ (extChartAt I α).target} :=
    (contMDiffOn_extChartAt_symm α).comp h2.contMDiffOn fun q hq => hq
  exact (contMDiff_flow X).comp_contMDiffOn (h1.contMDiffOn.prodMk h3)

theorem isOpen_flowDom (α : M) : IsOpen (flowDom X α (I := I)) := by
  have hT : IsOpen ((extChartAt I α).source ∩ extChartAt I α ⁻¹' patchΩ (I := I) α) :=
    (continuousOn_extChartAt α).isOpen_inter_preimage (isOpen_extChartAt_source α)
      (isOpen_patchΩ α)
  have hcont : ContinuousOn (flowPt X α) {q : ℝ × E | q.2 ∈ patchΩ (I := I) α} :=
    ((contMDiffOn_flowPt X α).continuousOn).mono fun q hq => patchΩ_subset_target α hq
  have hO : IsOpen {q : ℝ × E | q.2 ∈ patchΩ (I := I) α} :=
    (isOpen_patchΩ α).preimage continuous_snd
  have h := hcont.isOpen_inter_preimage hO hT
  convert h using 1
  ext q
  simp only [flowDom, mem_setOf_eq, mem_inter_iff, mem_preimage]

theorem contDiffOn_flowψ (α : M) : ContDiffOn ℝ ∞ (flowψ X α) (flowDom X α (I := I)) := by
  rw [← contMDiffOn_iff_contDiffOn]
  refine (contMDiffOn_extChartAt (x := α)).comp
    ((contMDiffOn_flowPt X α).mono fun q hq => patchΩ_subset_target α hq.1) fun q hq => ?_
  have h := hq.2.1
  rwa [extChartAt_source] at h

theorem flowψ_mem (α : M) {q : ℝ × E} (hq : q ∈ flowDom X α (I := I)) :
    flowψ X α q ∈ patchΩ (I := I) α := hq.2.2

theorem flowψ_zero (α : M) {q : ℝ × E} (hq : q ∈ flowDom X α (I := I)) (h0 : q.1 = 0) :
    flowψ X α q = q.2 := by
  simp only [flowψ, flowPt, h0, flow_zero]
  exact (extChartAt I α).right_inv (patchΩ_subset_target α hq.1)

theorem symm_flowψ (α : M) {q : ℝ × E} (hq : q ∈ flowDom X α (I := I)) :
    (extChartAt I α).symm (flowψ X α q) = flowPt X α q :=
  (extChartAt I α).left_inv hq.2.1

/-! ### Parallel transport in the chart -/

/-- The chart reading at `α` of `P_σ(x)⁻¹ : T⁰_s|_{φ_σ x} → T⁰_s|_x`, `x = chart⁻¹ y`. -/
def flowQ (α : M) (q : ℝ × E) : TensorRSModel 0 s ℝ E →L[ℝ] TensorRSModel 0 s ℝ E :=
  ((trivAt I M 0 s α).continuousLinearMapAt ℝ ((extChartAt I α).symm q.2)).comp
    ((pt X g s q.1 ((extChartAt I α).symm q.2)).symm.toContinuousLinearMap.comp
      ((trivAt I M 0 s α).symmL ℝ (flow X q.1 ((extChartAt I α).symm q.2))))

theorem flowQ_apply (α : M) (q : ℝ × E) (v : TensorRSModel 0 s ℝ E) :
    flowQ X g s α q v = (trivAt I M 0 s α).continuousLinearMapAt ℝ ((extChartAt I α).symm q.2)
      ((pt X g s q.1 ((extChartAt I α).symm q.2)).symm
        ((trivAt I M 0 s α).symmL ℝ (flowPt X α q) v)) := rfl

theorem contDiffOn_flowQ (α : M) : ContDiffOn ℝ ∞ (flowQ X g s α) (flowDom X α (I := I)) := by
  rw [contDiffOn_clm_apply]
  intro v
  rw [← contMDiffOn_iff_contDiffOn]
  intro q₀ hq₀
  refine ContMDiffAt.contMDiffWithinAt ?_
  set e := trivAt I M 0 s α with he
  have hb : ContMDiffAt 𝓘(ℝ, ℝ × E) I ∞ (fun q : ℝ × E => (extChartAt I α).symm q.2) q₀ := by
    have h2 : ContMDiff 𝓘(ℝ, ℝ × E) 𝓘(ℝ, E) ∞ (fun q : ℝ × E => q.2) := contDiff_snd.contMDiff
    exact ((contMDiffOn_extChartAt_symm α).contMDiffAt
      ((isOpen_extChartAt_target α).mem_nhds (patchΩ_subset_target α hq₀.1))).comp q₀ (h2 q₀)
  have hm : ContMDiffAt 𝓘(ℝ, ℝ × E) ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun q : ℝ × E => ((q.1, (extChartAt I α).symm q.2), v)) q₀ :=
    ((contDiff_fst.contMDiff q₀).prodMk hb).prodMk contMDiffAt_const
  have hopen : IsOpen {q' : (ℝ × M) × TensorRSModel 0 s ℝ E |
      q'.1.1 ∈ (univ : Set ℝ) ∧ flow X q'.1.1 q'.1.2 ∈ e.baseSet} := by
    simp only [mem_univ, true_and]
    exact ((contMDiff_flow X).continuous.comp continuous_fst).isOpen_preimage _ e.open_baseSet
  have hflow : flowPt X α q₀ ∈ e.baseSet := mem_trivAt_baseSet hq₀.2.1
  have hinv := (ptRaw_inverse X g s e).contMDiffAt
    (hopen.mem_nhds (x := ((q₀.1, (extChartAt I α).symm q₀.2), v)) ⟨mem_univ _, hflow⟩)
  have hcomp := hinv.comp q₀ hm
  have hv : ContMDiffAt 𝓘(ℝ, ℝ × E) (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun q : ℝ × E => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun x : M => TensorRSSpace 0 s I x) ((extChartAt I α).symm q.2)
        ((pt X g s q.1 ((extChartAt I α).symm q.2)).symm (e.symmL ℝ (flowPt X α q) v))) q₀ := by
    refine hcomp.congr_of_eventuallyEq (Eventually.of_forall fun q => ?_)
    exact mk_pt_symm X g s q.1 _ _
  have hx₀ : (extChartAt I α).symm q₀.2 ∈ e.baseSet :=
    mem_trivAt_baseSet ((extChartAt I α).map_target (patchΩ_subset_target α hq₀.1))
  exact contMDiffAt_continuousLinearMapAt_apply (I := I) (M := M) α
    (fun q : ℝ × E => (extChartAt I α).symm q.2) _ hv hx₀

theorem flowQ_zero (α : M) {q : ℝ × E} (hq : q ∈ flowDom X α (I := I)) (h0 : q.1 = 0) :
    flowQ X g s α q = ContinuousLinearMap.id ℝ _ := by
  obtain ⟨σ, y⟩ := q
  simp only at h0
  subst h0
  refine ContinuousLinearMap.ext fun v => ?_
  rw [flowQ_apply, ContinuousLinearMap.id_apply]
  change (trivAt I M 0 s α).continuousLinearMapAt ℝ ((extChartAt I α).symm y)
      ((pt X g s 0 ((extChartAt I α).symm y)).symm
        ((trivAt I M 0 s α).symmL ℝ (flow X 0 ((extChartAt I α).symm y)) v)) = v
  rw [pt_zero_symm]
  exact clmAt_fibCast_symm_symmL _
    (mem_trivAt_baseSet ((extChartAt I α).map_target (patchΩ_subset_target α hq.1))) v

/-! ### The jet map -/

/-- **The jet map at `α`**: `trivJet α x (j^N (Π_σ u) x) = jetMap α N (σ, y) (trivJet α (φ_σ x) (j^N u))`,
`x = chart⁻¹ y`. -/
def jetMap (α : M) (N : ℕ) (q : ℝ × E) : JetModel E 0 s N →L[ℝ] JetModel E 0 s N :=
  FlowNat.jetCoef (F := fun j => TensorRSModel 0 (s + j) ℝ E)
    (fun j => slotIns E (s + j)) (fun j => kerL g α (s + j) (patchB (I := I) α)) (flowψ X α)
    (fun j => slotUnins E (s + j)) (flowQ X g s α) N q

theorem slotUnins_slotIns' (j : ℕ) (w : TensorRSModel 0 (s + j + 1) ℝ E) :
    slotUnins E (s + j) (slotIns E (s + j) w) = w :=
  slotUnins_slotIns w

theorem contDiffOn_kerL_patch (α : M) (j : ℕ) :
    ContDiffOn ℝ ∞ (kerL g α (s + j) (patchB (I := I) α)) (patchΩ (I := I) α) :=
  (contDiffOn_kerL α (s + j) (patchB α)).mono (patchΩ_subset_target α)

theorem contDiffOn_jetMap (α : M) (N : ℕ) :
    ContDiffOn ℝ ∞ (jetMap X g s α N) (flowDom X α (I := I)) :=
  FlowNat.contDiffOn_jetCoef (F := fun j => TensorRSModel 0 (s + j) ℝ E)
    (fun j => slotUnins E (s + j)) (contDiffOn_kerL_patch g s α) (isOpen_flowDom X α)
    (fun _ hq => hq.1) (contDiffOn_flowψ X α) (fun _ hq => flowψ_mem X α hq)
    (contDiffOn_flowQ X g s α) N

theorem jetMap_zero (α : M) (N : ℕ) {q : ℝ × E} (hq : q ∈ flowDom X α (I := I)) (h0 : q.1 = 0) :
    jetMap X g s α N q = ContinuousLinearMap.id ℝ _ :=
  FlowNat.jetCoef_zero (F := fun j => TensorRSModel 0 (s + j) ℝ E)
    (fun j => slotUnins E (s + j)) (slotUnins_slotIns' s) (contDiffOn_kerL_patch g s α)
    (isOpen_flowDom X α) (fun _ hq => hq.1) (contDiffOn_flowψ X α)
    (fun _ hq => flowψ_mem X α hq) (fun _ hq h0 => flowψ_zero X α hq h0)
    (contDiffOn_flowQ X g s α) (fun _ hq h0 => flowQ_zero X g s α hq h0) N hq h0

/-- The chart recursion on the open patch, as a derivative. -/
theorem hasFDerivAt_chartRd_patch (α : M) {a : ℕ} (S : SmoothCcTensor g 0 a) {z : E}
    (hz : z ∈ patchΩ (I := I) α) :
    HasFDerivAt (chartRd g α S)
      (slotIns E a (chartRd g α (covGrad (I := I) (M := M) g 0 a S) z) +
        kerL g α a (patchB (I := I) α) z (chartRd g α S z)) z := by
  have hd : DifferentiableAt ℝ (chartRd g α S) z :=
    ((contDiffOn_chartRd α S).differentiableOn (by simp)).differentiableAt
      ((isOpen_extChartAt_target α).mem_nhds (patchΩ_subset_target α hz))
  have h := hd.hasFDerivAt
  rwa [fderiv_chartRd_eq (patch_subset α) (patchB_spec α) S (patchΩ_subset_closedBall α hz)] at h

theorem hasFDerivAt_chartRd_iter (α : M) (u : SmoothCcTensor g 0 s) (j : ℕ) {z : E}
    (hz : z ∈ patchΩ (I := I) α) :
    HasFDerivAt (chartRd g α (iteratedCovGrad g 0 s j u))
      (slotIns E (s + j) (chartRd g α (iteratedCovGrad g 0 s (j + 1) u) z) +
        kerL g α (s + j) (patchB (I := I) α) z (chartRd g α (iteratedCovGrad g 0 s j u) z)) z :=
  hasFDerivAt_chartRd_patch g α (iteratedCovGrad g 0 s j u) hz

/-- **Jets of the horizontal pullback in the chart at `α`.** -/
theorem trivJet_hpull (α : M) (N : ℕ) (u : SmoothCcTensor g 0 s) {q : ℝ × E}
    (hq : q ∈ flowDom X α (I := I)) :
    EquationData.trivJet α ((extChartAt I α).symm q.2)
        (covJet g 0 s N (hpull X g s q.1 u) ((extChartAt I α).symm q.2)) =
      jetMap X g s α N q (EquationData.trivJet α (flowPt X α q)
        (covJet g 0 s N u (flowPt X α q))) := by
  have h := FlowNat.jetCoef_rep (F := fun j => TensorRSModel 0 (s + j) ℝ E)
    (ins := fun j => slotIns E (s + j)) (K := fun j => kerL g α (s + j) (patchB (I := I) α))
    (ψ := flowψ X α) (fun j => slotUnins E (s + j)) (slotUnins_slotIns' s)
    (contDiffOn_kerL_patch g s α)
    (fun j z => chartRd g α (iteratedCovGrad g 0 s j u) z)
    (fun j z hz => hasFDerivAt_chartRd_iter g s α u j hz)
    (isOpen_flowDom X α) (fun _ hq => hq.1) (contDiffOn_flowψ X α)
    (fun q hq => flowψ_mem X α hq) (contDiffOn_flowQ X g s α)
    (fun k q => chartRd g α (iteratedCovGrad g 0 s k (hpull X g s q.1 u)) q.2)
    (fun q hq => by
      change chartRd g α (hpull X g s q.1 u) q.2 = flowQ X g s α q (chartRd g α u (flowψ X α q))
      rw [chartRd_eq_trivAt, chartRd_eq_trivAt, symm_flowψ X α hq, flowQ_apply,
        (trivAt I M 0 s α).symmL_continuousLinearMapAt (mem_trivAt_baseSet hq.2.1)]
      rfl)
    (fun k q hq => hasFDerivAt_chartRd_iter g s α (hpull X g s q.1 u) k hq.1) N hq
  refine h.trans ?_
  congr 1
  funext j
  change chartRd g α (iteratedCovGrad g 0 s j u) (flowψ X α q) = _
  rw [chartRd_eq_trivAt, symm_flowψ X α hq]
  rfl

end HFlow

end ShortTime
