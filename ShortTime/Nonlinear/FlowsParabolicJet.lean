import ShortTime.Nonlinear.FlowsNaturalJet
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.InnerJointCont
import DifferentialGeometry.Analysis.Spectral.Tensor.TrivProj.ChartTwistIdentity
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.InnerBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.InnerBounds.InnerLowerBound

/-!
# Uniform pointwise jet bounds for the horizontal pullback

Paper: Lemma `lem:flows` (b), the pointwise part of "use the chain rule".

* `exists_jet_bound_hpull_unif`: there are `δ > 0` and `C` with
  `|∇^N (Π_σ u)|²(x) ≤ C Σ_{k ≤ N} |∇^k u|²(φ_σ x)` for `|σ| ≤ δ`, all `x` and all smooth `u`.
* `exists_jetNormSq_hpull_le`: for every `R`, `jetNormSq N (Π_σ u) x ≤ C jetNormSq N u (φ_σ x)` for
  `|σ| ≤ R`, by iterating with the group law.

Proof: in the chart at `α`, `trivJet_hpull_at` writes the jet of `Π_σ u` at `y` as `jetMap` applied
to the jet of `u` at `φ_σ y`. The jet map is bounded on a compact neighbourhood of `(0, chart α)`,
and on compact subsets of the chart domain the Riemannian fibre norms and the norms of the chart
readings bound each other (`exists_clmAt_sq_le`, `exists_fiberNormSq_le_clmAt`). Finitely many
charts cover `M`.
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

/-! ### Quadratic forms on compact sets -/

/-- A family of quadratic forms, jointly continuous over a compact set, is uniformly bounded. -/
theorem exists_quad_le {Xs V : Type*} [TopologicalSpace Xs] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] {K : Set Xs} (hK : IsCompact K) {Q : Xs → V → ℝ}
    (hQ : ContinuousOn (fun p : Xs × V => Q p.1 p.2) (K ×ˢ univ))
    (hhom : ∀ x ∈ K, ∀ (c : ℝ) (v : V), Q x (c • v) = c ^ 2 * Q x v) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ v, Q x v ≤ C * ‖v‖ ^ 2 := by
  have hS : IsCompact (K ×ˢ Metric.sphere (0 : V) 1) := hK.prod (isCompact_sphere 0 1)
  obtain ⟨B, hB⟩ := hS.bddAbove_image (hQ.mono (prod_mono le_rfl (subset_univ _)))
  refine ⟨max B 0, le_max_right _ _, fun x hx v => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · have h0 := hhom x hx 0 0
    rw [zero_smul] at h0
    have : Q x 0 = 0 := by rw [h0]; ring
    rw [this, norm_zero]
    simp
  · have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hw : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : V) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have h1 : Q x (‖v‖⁻¹ • v) ≤ B := hB ⟨(x, ‖v‖⁻¹ • v), ⟨hx, hw⟩, rfl⟩
    have h2 : v = ‖v‖ • (‖v‖⁻¹ • v) := by rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    calc Q x v = Q x (‖v‖ • (‖v‖⁻¹ • v)) := by rw [← h2]
      _ = ‖v‖ ^ 2 * Q x (‖v‖⁻¹ • v) := hhom x hx _ _
      _ ≤ ‖v‖ ^ 2 * max B 0 := mul_le_mul_of_nonneg_left (h1.trans (le_max_left _ _)) (sq_nonneg _)
      _ = max B 0 * ‖v‖ ^ 2 := mul_comm _ _

/-- The square of the sup norm of a finite product is at most the sum of the squares. -/
theorem norm_sq_le_sum_norm_sq {ι : Type*} [Fintype ι] {F : ι → Type*}
    [∀ i, SeminormedAddCommGroup (F i)] (w : ∀ i, F i) :
    ‖w‖ ^ 2 ≤ ∑ i, ‖w i‖ ^ 2 := by
  have hS : 0 ≤ ∑ i, ‖w i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h : ‖w‖ ≤ Real.sqrt (∑ i, ‖w i‖ ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
    refine Real.le_sqrt_of_sq_le ?_
    exact Finset.single_le_sum (f := fun i => ‖w i‖ ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ i)
  calc ‖w‖ ^ 2 ≤ Real.sqrt (∑ i, ‖w i‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = ∑ i, ‖w i‖ ^ 2 := Real.sq_sqrt hS

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

/-! ### Fibre norms against chart readings -/

section Norms

variable (g : SmoothRiemannianMetric I M)

/-- On a compact subset of the chart domain at `α`, the chart readings are bounded by the fibre
norm. -/
theorem exists_clmAt_sq_le (α : M) (a : ℕ) {K : Set M} (hK : IsCompact K)
    (hKs : K ⊆ (chartAt H α).source) :
    ∃ C, 0 ≤ C ∧ ∀ b ∈ K, ∀ v : TensorRSSpace 0 a I b,
      ‖(trivAt I M 0 a α).continuousLinearMapAt ℝ b v‖ ^ 2 ≤
        C * riemannianFiberNormSq (I := I) (M := M) g 0 a b v := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_twist_le (g := g) α a hK hKs
  refine ⟨C, hC0, fun b hb v => ?_⟩
  rw [triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel 0 a α (hKs hb)]
  exact hC b hb v

/-- On a compact subset of the chart domain at `α`, the fibre norm is bounded by the chart
readings. -/
theorem exists_fiberNormSq_le_clmAt (α : M) (a : ℕ) {K : Set M} (hK : IsCompact K)
    (hKs : K ⊆ (chartAt H α).source) :
    ∃ C, 0 ≤ C ∧ ∀ b ∈ K, ∀ v : TensorRSSpace 0 a I b,
      riemannianFiberNormSq (I := I) (M := M) g 0 a b v ≤
        C * ‖(trivAt I M 0 a α).continuousLinearMapAt ℝ b v‖ ^ 2 := by
  have hKb : K ⊆ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hKs
  obtain ⟨C, hC0, hC⟩ := exists_quad_le hK
    (Q := fun b S => chartTensorInnerPointwiseRsModel (I := I) (M := M) g 0 a α b S S)
    ((chartTensorInnerPointwise_rs_model_quadratic_continuousOn (I := I) (M := M) g 0 a α).mono
      (prod_mono hKb le_rfl))
    (fun b _ c S => by
      rw [chartTensorInnerPointwise_rs_model_smul_left, chartTensorInnerPointwise_rs_model_smul_right]
      ring)
  refine ⟨C, hC0, fun b hb v => ?_⟩
  have hb' := hKb hb
  rw [triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel 0 a α (hKs hb)]
  refine le_trans (le_of_eq ?_) (hC b hb _)
  rw [chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise (I := I) (M := M) g 0 a α hb',
    chartRSTwist_chartRSTwistInv (I := I) (M := M) α hb' 0 a,
    riemannianFiberNormSq_eq_tensorInnerPointwise]

end Norms

/-! ### The local bound -/

section Local

variable (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
variable (g : SmoothRiemannianMetric I M) (s : ℕ)

/-- A compact subset of the chart domain at `α` containing the patch. -/
def patchK (α : M) : Set M :=
  (extChartAt I α).symm '' Metric.closedBall (extChartAt I α α) (patchR (I := I) α)

theorem isCompact_patchK (α : M) : IsCompact (patchK (I := I) α) := by
  have : ProperSpace E := FiniteDimensional.proper_real E
  exact (isCompact_closedBall _ _).image_of_continuousOn
    ((continuousOn_extChartAt_symm α).mono (patch_subset α))

theorem patchK_subset (α : M) : patchK (I := I) α ⊆ (chartAt H α).source := by
  rintro _ ⟨y, hy, rfl⟩
  rw [← extChartAt_source (I := I)]
  exact (extChartAt I α).map_target (patch_subset α hy)

theorem mem_patchK {α x : M} (hx : x ∈ (extChartAt I α).source)
    (hy : extChartAt I α x ∈ patchΩ (I := I) α) : x ∈ patchK (I := I) α :=
  ⟨extChartAt I α x, patchΩ_subset_closedBall α hy, (extChartAt I α).left_inv hx⟩

/-- The jet map is bounded near `(0, chart α)`. -/
theorem exists_jetMap_bound (α : M) (N : ℕ) :
    ∃ r > 0, ∃ J, 0 ≤ J ∧ ∀ σ : ℝ, ∀ y : E, |σ| ≤ r → dist y (extChartAt I α α) ≤ r →
      (σ, y) ∈ flowDom X α (I := I) ∧ ‖jetMap X g s α N (σ, y)‖ ≤ J := by
  have : ProperSpace E := FiniteDimensional.proper_real E
  have h0 : ((0 : ℝ), extChartAt I α α) ∈ flowDom X α (I := I) := by
    have hα : (extChartAt I α).symm (extChartAt I α α) = α :=
      (extChartAt I α).left_inv (mem_extChartAt_source α)
    refine ⟨mem_patchΩ_self α, ?_, ?_⟩
    · simp only [flowPt, flow_zero, hα]
      exact mem_extChartAt_source α
    · simp only [flowPt, flow_zero, hα]
      exact mem_patchΩ_self α
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_flowDom X α) _ h0
  have hsub : Metric.closedBall (((0 : ℝ), extChartAt I α α)) (ε / 2) ⊆ flowDom X α (I := I) :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  obtain ⟨J, hJ⟩ := (isCompact_closedBall (((0 : ℝ), extChartAt I α α)) (ε / 2)).exists_bound_of_continuousOn
    ((contDiffOn_jetMap X g s α N).continuousOn.mono hsub)
  refine ⟨ε / 2, by linarith, max J 0, le_max_right _ _, fun σ y hσ hy => ?_⟩
  have hmem : (σ, y) ∈ Metric.closedBall (((0 : ℝ), extChartAt I α α)) (ε / 2) := by
    rw [Metric.mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq, sub_zero]
    exact ⟨hσ, hy⟩
  exact ⟨hsub hmem, (hJ _ hmem).trans (le_max_left _ _)⟩

/-- **The local pointwise jet bound** near `α`. -/
theorem local_jet_bound (α : M) (N : ℕ) :
    ∃ r > 0, ∃ C, 0 ≤ C ∧ ∀ y ∈ (extChartAt I α).source,
      extChartAt I α y ∈ Metric.ball (extChartAt I α α) r → ∀ σ : ℝ, |σ| ≤ r →
      ∀ u : SmoothCcTensor g 0 s,
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + N) y
            ((iteratedCovGrad g 0 s N (hpull X g s σ u)).toSection y) ≤
          C * ∑ k : Fin (N + 1), riemannianFiberNormSq (I := I) (M := M) g 0 (s + k)
            (flow X σ y) ((iteratedCovGrad g 0 s k u).toSection (flow X σ y)) := by
  obtain ⟨r, hr, J, hJ0, hJ⟩ := exists_jetMap_bound X g s α N
  have hK := isCompact_patchK (I := I) α
  have hKs := patchK_subset (I := I) α
  choose A1 hA10 hA1 using fun k : Fin (N + 1) => exists_clmAt_sq_le g α (s + k) hK hKs
  obtain ⟨A2, hA20, hA2⟩ := exists_fiberNormSq_le_clmAt g α (s + N) hK hKs
  set A1s := ∑ k : Fin (N + 1), A1 k with hA1s
  have hA1s0 : 0 ≤ A1s := Finset.sum_nonneg fun k _ => hA10 k
  refine ⟨r, hr, A2 * J ^ 2 * A1s, mul_nonneg (mul_nonneg hA20 (sq_nonneg _)) hA1s0,
    fun y hy hyr σ hσ u => ?_⟩
  obtain ⟨hq, hJq⟩ := hJ σ (extChartAt I α y) hσ (Metric.mem_ball.mp hyr).le
  have hT := trivJet_hpull_at X g s α N u hy rfl hq
  have hyK : y ∈ patchK (I := I) α := mem_patchK hy hq.1
  have hφK : flow X σ y ∈ patchK (I := I) α := by
    have h1 := hq.2.1
    have h2 := hq.2.2
    simp only [flowPt, (extChartAt I α).left_inv hy] at h1 h2
    exact mem_patchK h1 h2
  set w := EquationData.trivJet α y (covJet g 0 s N (hpull X g s σ u) y) with hw
  set w' := EquationData.trivJet α (flow X σ y) (covJet g 0 s N u (flow X σ y)) with hw'
  -- the top component of `w`
  have hwN : (trivAt I M 0 (s + N) α).continuousLinearMapAt ℝ y
      ((iteratedCovGrad g 0 s N (hpull X g s σ u)).toSection y) = w (Fin.last N) := rfl
  have h1 := hA2 y hyK ((iteratedCovGrad g 0 s N (hpull X g s σ u)).toSection y)
  rw [hwN] at h1
  have h2 : ‖w (Fin.last N)‖ ≤ J * ‖w'‖ := by
    refine (norm_le_pi_norm w _).trans ?_
    rw [hT]
    exact ((jetMap X g s α N _).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hJq (norm_nonneg _))
  have h3 := norm_sq_le_sum_norm_sq w'
  have h4 : ∀ k : Fin (N + 1), ‖w' k‖ ^ 2 ≤ A1s *
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + k) (flow X σ y)
        ((iteratedCovGrad g 0 s k u).toSection (flow X σ y)) := by
    intro k
    refine (hA1 k _ hφK ((iteratedCovGrad g 0 s k u).toSection (flow X σ y))).trans
      (mul_le_mul_of_nonneg_right ?_
      (riemannianFiberNormSq_nonneg g 0 (s + k) _ _))
    exact Finset.single_le_sum (f := A1) (fun k _ => hA10 k) (Finset.mem_univ k)
  have h5 : ∑ k : Fin (N + 1), ‖w' k‖ ^ 2 ≤ A1s * ∑ k : Fin (N + 1),
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + k) (flow X σ y)
        ((iteratedCovGrad g 0 s k u).toSection (flow X σ y)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => h4 k
  have h6 : ‖w (Fin.last N)‖ ^ 2 ≤ J ^ 2 * ‖w'‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h2 2
  calc _ ≤ A2 * ‖w (Fin.last N)‖ ^ 2 := h1
    _ ≤ A2 * (J ^ 2 * (A1s * ∑ k : Fin (N + 1),
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + k) (flow X σ y)
            ((iteratedCovGrad g 0 s k u).toSection (flow X σ y)))) := by
        refine mul_le_mul_of_nonneg_left (h6.trans ?_) hA20
        exact mul_le_mul_of_nonneg_left (h3.trans h5) (sq_nonneg _)
    _ = _ := by ring

end Local

/-! ### The global bound -/

section Global

variable (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
variable (g : SmoothRiemannianMetric I M) (s : ℕ)

/-- **Uniform pointwise jet bound for the horizontal pullback**: for `|σ| ≤ δ`,
`|∇^N (Π_σ u)|²(x) ≤ C Σ_{k ≤ N} |∇^k u|²(φ_σ x)`. -/
theorem exists_jet_bound_hpull_unif (N : ℕ) :
    ∃ δ > 0, ∃ C, 0 ≤ C ∧ ∀ σ : ℝ, |σ| ≤ δ → ∀ (u : SmoothCcTensor g 0 s) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + N) x
          ((iteratedCovGrad g 0 s N (hpull X g s σ u)).toSection x) ≤
        C * ∑ k : Fin (N + 1), riemannianFiberNormSq (I := I) (M := M) g 0 (s + k)
          (flow X σ x) ((iteratedCovGrad g 0 s k u).toSection (flow X σ x)) := by
  classical
  choose r hr C hC0 hC using fun α : M => local_jet_bound X g s α N
  set W : M → Set M := fun α =>
    (extChartAt I α).source ∩ extChartAt I α ⁻¹' Metric.ball (extChartAt I α α) (r α) with hW
  have hWo : ∀ α, IsOpen (W α) := fun α =>
    (continuousOn_extChartAt α).isOpen_inter_preimage (isOpen_extChartAt_source α)
      Metric.isOpen_ball
  have hWα : ∀ α, α ∈ W α := fun α =>
    ⟨mem_extChartAt_source α, Metric.mem_ball_self (hr α)⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hWo
    (fun x _ => mem_iUnion.2 ⟨x, hWα x⟩)
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_le_finset t r (fun a _ => hr a)
  refine ⟨δ, hδ, ∑ α ∈ t, C α, Finset.sum_nonneg fun α _ => hC0 α, fun σ hσ u x => ?_⟩
  obtain ⟨α, hαt, hxα⟩ := mem_iUnion₂.mp (ht (mem_univ x))
  have hS : 0 ≤ ∑ k : Fin (N + 1), riemannianFiberNormSq (I := I) (M := M) g 0 (s + k)
      (flow X σ x) ((iteratedCovGrad g 0 s k u).toSection (flow X σ x)) :=
    Finset.sum_nonneg fun k _ => riemannianFiberNormSq_nonneg g 0 (s + k) _ _
  refine (hC α x hxα.1 hxα.2 σ (hσ.trans (hδle α hαt)) u).trans
    (mul_le_mul_of_nonneg_right ?_ hS)
  exact Finset.single_le_sum (f := C) (fun α _ => hC0 α) hαt

/-- `Σ_{k ≤ N} |∇^k u|²(x)`, the squared covariant `N`-jet. -/
def jetNormSq (N : ℕ) (u : SmoothCcTensor g 0 s) (x : M) : ℝ :=
  ∑ k : Fin (N + 1), riemannianFiberNormSq (I := I) (M := M) g 0 (s + k) x
    ((iteratedCovGrad g 0 s k u).toSection x)

theorem jetNormSq_nonneg (N : ℕ) (u : SmoothCcTensor g 0 s) (x : M) :
    0 ≤ jetNormSq g s N u x :=
  Finset.sum_nonneg fun k _ => riemannianFiberNormSq_nonneg g 0 (s + k) _ _

/-- The jet bound for the full `N`-jet, for small `|σ|`. -/
theorem exists_jetNormSq_hpull_le_small (N : ℕ) :
    ∃ δ > 0, ∃ C, 1 ≤ C ∧ ∀ σ : ℝ, |σ| ≤ δ → ∀ (u : SmoothCcTensor g 0 s) (x : M),
      jetNormSq g s N (hpull X g s σ u) x ≤ C * jetNormSq g s N u (flow X σ x) := by
  choose δ hδ C hC0 hC using fun k : Fin (N + 1) => exists_jet_bound_hpull_unif X g s k
  obtain ⟨δ₀, hδ₀, hδ₀le⟩ : ∃ δ₀ > 0, ∀ k : Fin (N + 1), δ₀ ≤ δ k := by
    refine ⟨Finset.univ.inf' Finset.univ_nonempty δ, ?_, fun k => Finset.inf'_le _ (Finset.mem_univ k)⟩
    rw [gt_iff_lt, Finset.lt_inf'_iff]
    exact fun k _ => hδ k
  set Cs := ∑ k : Fin (N + 1), C k with hCs
  have hCs0 : 0 ≤ Cs := Finset.sum_nonneg fun k _ => hC0 k
  refine ⟨δ₀, hδ₀, (N + 1) * Cs + 1, by
    have : 0 ≤ ((N : ℝ) + 1) * Cs := by positivity
    linarith, fun σ hσ u x => ?_⟩
  have hJ := jetNormSq_nonneg g s N u (flow X σ x)
  -- each component of the jet of `Π_σ u` is bounded by the jet of `u` at `φ_σ x`
  have hk : ∀ k : Fin (N + 1), riemannianFiberNormSq (I := I) (M := M) g 0 (s + k) x
      ((iteratedCovGrad g 0 s k (hpull X g s σ u)).toSection x) ≤ Cs * jetNormSq g s N u (flow X σ x) := by
    intro k
    refine (hC k σ (hσ.trans (hδ₀le k)) u x).trans ?_
    refine mul_le_mul (Finset.single_le_sum (f := C) (fun k _ => hC0 k) (Finset.mem_univ k)) ?_
      (Finset.sum_nonneg fun k _ => riemannianFiberNormSq_nonneg g 0 (s + k) _ _) hCs0
    -- the sum over `j ≤ k` is part of the sum over `j ≤ N`
    unfold jetNormSq
    have hle : ∑ j : Fin ((k : ℕ) + 1), riemannianFiberNormSq (I := I) (M := M) g 0 (s + j)
        (flow X σ x) ((iteratedCovGrad g 0 s j u).toSection (flow X σ x)) =
        ∑ j ∈ Finset.range ((k : ℕ) + 1), riemannianFiberNormSq (I := I) (M := M) g 0 (s + j)
          (flow X σ x) ((iteratedCovGrad g 0 s j u).toSection (flow X σ x)) :=
      Fin.sum_univ_eq_sum_range (fun j => riemannianFiberNormSq (I := I) (M := M) g 0 (s + j)
          (flow X σ x) ((iteratedCovGrad g 0 s j u).toSection (flow X σ x))) _
    have hle' : ∑ j : Fin (N + 1), riemannianFiberNormSq (I := I) (M := M) g 0 (s + j)
        (flow X σ x) ((iteratedCovGrad g 0 s j u).toSection (flow X σ x)) =
        ∑ j ∈ Finset.range (N + 1), riemannianFiberNormSq (I := I) (M := M) g 0 (s + j)
          (flow X σ x) ((iteratedCovGrad g 0 s j u).toSection (flow X σ x)) :=
      Fin.sum_univ_eq_sum_range (fun j => riemannianFiberNormSq (I := I) (M := M) g 0 (s + j)
          (flow X σ x) ((iteratedCovGrad g 0 s j u).toSection (flow X σ x))) _
    rw [hle, hle']
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_of_lt k.isLt))
      fun j _ _ => riemannianFiberNormSq_nonneg g 0 (s + j) _ _
  calc jetNormSq g s N (hpull X g s σ u) x = ∑ k : Fin (N + 1),
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + k) x
          ((iteratedCovGrad g 0 s k (hpull X g s σ u)).toSection x) := rfl
    _ ≤ ∑ _k : Fin (N + 1), Cs * jetNormSq g s N u (flow X σ x) := Finset.sum_le_sum fun k _ => hk k
    _ = (N + 1) * Cs * jetNormSq g s N u (flow X σ x) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ ((N + 1) * Cs + 1) * jetNormSq g s N u (flow X σ x) :=
        mul_le_mul_of_nonneg_right (by linarith) hJ

/-- **The jet bound on bounded parameter ranges**, by the group law. -/
theorem exists_jetNormSq_hpull_le (N : ℕ) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ σ : ℝ, |σ| ≤ R → ∀ (u : SmoothCcTensor g 0 s) (x : M),
      jetNormSq g s N (hpull X g s σ u) x ≤ C * jetNormSq g s N u (flow X σ x) := by
  obtain ⟨δ, hδ, C, hC1, hC⟩ := exists_jetNormSq_hpull_le_small X g s N
  have hstep : ∀ n : ℕ, ∀ σ : ℝ, |σ| ≤ n * δ → ∀ (u : SmoothCcTensor g 0 s) (x : M),
      jetNormSq g s N (hpull X g s σ u) x ≤ C ^ n * jetNormSq g s N u (flow X σ x) := by
    intro n
    induction n with
    | zero =>
      intro σ hσ u x
      have hσ0 : σ = 0 := by
        have : |σ| ≤ 0 := by simpa using hσ
        exact abs_nonpos_iff.mp this
      subst hσ0
      rw [hpull_zero, flow_zero, pow_zero, one_mul]
    | succ n ih =>
      intro σ hσ u x
      have hn : (0 : ℝ) < n + 1 := by positivity
      have hn' : (n : ℝ) + 1 ≠ 0 := hn.ne'
      set σ₁ := σ / (n + 1) with hσ₁
      set σ₂ := σ - σ₁ with hσ₂
      have h1 : |σ₁| ≤ δ := by
        rw [hσ₁, abs_div, abs_of_pos hn, div_le_iff₀ hn]
        push_cast at hσ
        linarith
      have h2 : |σ₂| ≤ n * δ := by
        have e : σ₂ = σ * (n / (n + 1)) := by
          have hc : σ / (↑n + 1) * (↑n + 1) = σ := div_mul_cancel₀ σ hn'
          rw [hσ₂, hσ₁]
          linear_combination -hc
        rw [e, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n / (n + 1))]
        push_cast at hσ
        calc |σ| * (n / (n + 1)) ≤ ((n + 1) * δ) * (n / (n + 1)) :=
              mul_le_mul_of_nonneg_right hσ (by positivity)
          _ = n * δ := by
              have hc : ((n : ℝ) + 1) * ((n : ℝ) + 1)⁻¹ = 1 := mul_inv_cancel₀ hn'
              rw [div_eq_mul_inv]
              linear_combination (n : ℝ) * δ * hc
      have hsum : σ₁ + σ₂ = σ := by rw [hσ₂]; ring
      have hgrp : hpull X g s σ u = hpull X g s σ₁ (hpull X g s σ₂ u) := by
        rw [hpull_hpull, hsum]
      have hfl : flow X σ₂ (flow X σ₁ x) = flow X σ x := by
        rw [← flow_add, hsum]
      rw [hgrp]
      refine (hC σ₁ h1 _ x).trans ?_
      have h3 := ih σ₂ h2 u (flow X σ₁ x)
      rw [hfl] at h3
      calc C * jetNormSq g s N (hpull X g s σ₂ u) (flow X σ₁ x)
          ≤ C * (C ^ n * jetNormSq g s N u (flow X σ x)) :=
            mul_le_mul_of_nonneg_left h3 (by linarith)
        _ = C ^ (n + 1) * jetNormSq g s N u (flow X σ x) := by ring
  obtain ⟨n, hn⟩ := exists_nat_ge (R / δ)
  refine ⟨C ^ n, pow_nonneg (by linarith) n, fun σ hσ u x => hstep n σ ?_ u x⟩
  calc |σ| ≤ R := hσ
    _ ≤ n * δ := by rwa [div_le_iff₀ hδ] at hn

end Global

end HFlow

end ShortTime
