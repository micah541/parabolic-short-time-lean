import ShortTime.Nonlinear.FlowsParabolicJet
import DifferentialGeometry.Analysis.Integration.Measure.Pullback
import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensity
import DifferentialGeometry.Geometry.Metric.Pullback.Basic
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.LowerAllUpperIndices
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Change of variables along the flow

Paper: Lemma `lem:flows` (b), "a change of variables".

* `exists_flow_deriv_bound`: `|dφ_σ v|² ≤ C |v|²` for `|σ| ≤ δ`, uniformly on `M`
  (`ContMDiffAt.mfderiv` in the tangent charts, and the comparison of `g` with the chart norms on
  compact subsets of chart domains, `exists_tangent_inner_le`, `exists_tangent_clmAt_sq_le`).
* `exists_integral_comp_flow_le`: `∫_M F(φ_σ x) dx ≤ C ∫_M F` for continuous `F ≥ 0` and
  `|σ| ≤ δ`. The push-forward of the volume by `φ_σ` is the volume of the pulled-back metric
  (`riemannianVolumeMeasure_pullback`), whose density is bounded by the derivative bound
  (`riemannianVolumeDensity_le_of_inner_le`).
-/

noncomputable section

open Bundle Manifold Set Filter MeasureTheory
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral DifferentialGeometry.Analysis.Elliptic
open scoped Manifold ContDiff Topology ENNReal

set_option linter.unusedSectionVars false

namespace ShortTime

namespace HFlow

/-- A family of positive definite quadratic forms, jointly continuous over a compact set, is
uniformly positive. -/
theorem exists_quad_ge {Xs V : Type*} [TopologicalSpace Xs] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] {K : Set Xs} (hK : IsCompact K) {Q : Xs → V → ℝ}
    (hQ : ContinuousOn (fun p : Xs × V => Q p.1 p.2) (K ×ˢ univ))
    (hhom : ∀ x ∈ K, ∀ (c : ℝ) (v : V), Q x (c • v) = c ^ 2 * Q x v)
    (hpos : ∀ x ∈ K, ∀ v : V, v ≠ 0 → 0 < Q x v) :
    ∃ c, 0 < c ∧ ∀ x ∈ K, ∀ v, c * ‖v‖ ^ 2 ≤ Q x v := by
  have hS : IsCompact (K ×ˢ Metric.sphere (0 : V) 1) := hK.prod (isCompact_sphere 0 1)
  have hQ0 : ∀ x ∈ K, Q x 0 = 0 := fun x hx => by
    have h0 := hhom x hx 0 0
    rw [zero_smul] at h0
    rw [h0]; ring
  have hunit : ∀ v : V, v ≠ 0 → ‖v‖⁻¹ • v ∈ Metric.sphere (0 : V) 1 := fun v hv => by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_pos_iff.mpr hv).ne']
  have hdecomp : ∀ x ∈ K, ∀ v : V, v ≠ 0 → Q x v = ‖v‖ ^ 2 * Q x (‖v‖⁻¹ • v) := fun x hx v hv => by
    rw [← hhom x hx, smul_smul, mul_inv_cancel₀ (norm_pos_iff.mpr hv).ne', one_smul]
  by_cases hne : (K ×ˢ Metric.sphere (0 : V) 1).Nonempty
  · obtain ⟨p₀, hp₀, hmin⟩ := hS.exists_isMinOn hne (hQ.mono (prod_mono le_rfl (subset_univ _)))
    have hp₀0 : p₀.2 ≠ 0 := by
      intro h
      have h1 := mem_sphere_zero_iff_norm.mp hp₀.2
      rw [h, norm_zero] at h1
      exact zero_ne_one h1
    have hc := hpos p₀.1 hp₀.1 p₀.2 hp₀0
    refine ⟨Q p₀.1 p₀.2, hc, fun x hx v => ?_⟩
    rcases eq_or_ne v 0 with rfl | hv
    · rw [hQ0 x hx, norm_zero]; simp
    · rw [hdecomp x hx v hv, mul_comm]
      exact mul_le_mul_of_nonneg_left (hmin (show (x, ‖v‖⁻¹ • v) ∈ K ×ˢ Metric.sphere (0 : V) 1
        from ⟨hx, hunit v hv⟩)) (sq_nonneg _)
  · refine ⟨1, one_pos, fun x hx v => ?_⟩
    rcases eq_or_ne v 0 with rfl | hv
    · rw [hQ0 x hx, norm_zero]; simp
    · exact absurd ⟨(x, ‖v‖⁻¹ • v), hx, hunit v hv⟩ hne

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

/-! ### The metric in tangent charts -/

section Tangent

variable (g : SmoothRiemannianMetric I M)

theorem chartGramBilin_self_eq (α b : M) (w : E) :
    chartGramBilin (I := I) (M := M) g α b w w =
      g.inner b ((trivializationAt E (TangentSpace I) α).symmL ℝ b w)
        ((trivializationAt E (TangentSpace I) α).symmL ℝ b w) := by
  rw [chartGramBilin_eq_innerJinv, modelInnerAt_apply, Tensor.Tensor0SRiemannian.chartJinv_apply,
    ContinuousLinearEquiv.symm_apply_apply]

theorem continuousOn_chartGramBilin (α : M) :
    ContinuousOn (fun p : M × E => chartGramBilin (I := I) (M := M) g α p.1 p.2 p.2)
      ((trivializationAt E (TangentSpace I) α).baseSet ×ˢ univ) := by
  have hcoord : ∀ j, Continuous fun w : E =>
      (Tensor.Coordinates.chartModelBasis E).equivFun w j := fun j =>
    (continuous_apply j).comp
      (LinearEquiv.toContinuousLinearEquiv (Tensor.Coordinates.chartModelBasis E).equivFun).continuous
  have hfun : (fun p : M × E => chartGramBilin (I := I) (M := M) g α p.1 p.2 p.2) = fun p =>
      ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        Tensor.Coordinates.chartGramMatrix g α p.1 j k *
          (Tensor.Coordinates.chartModelBasis E).equivFun p.2 j *
          (Tensor.Coordinates.chartModelBasis E).equivFun p.2 k :=
    funext fun p => chartGramBilin_apply g α p.1 p.2 p.2
  rw [hfun]
  refine continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun k _ => ?_
  refine ((((Tensor.Coordinates.chartGramMatrix_entry_contMDiffOn g α j k).continuousOn.comp
    continuousOn_fst fun p hp => hp.1)).mul ((hcoord j).comp continuous_snd).continuousOn).mul
    ((hcoord k).comp continuous_snd).continuousOn

/-- Upper comparison of `g` with the chart norm, on compact subsets of the chart domain. -/
theorem exists_tangent_inner_le (α : M) {K : Set M} (hK : IsCompact K)
    (hKs : K ⊆ (chartAt H α).source) :
    ∃ C, 0 ≤ C ∧ ∀ b ∈ K, ∀ w : E,
      g.inner b ((trivializationAt E (TangentSpace I) α).symmL ℝ b w)
        ((trivializationAt E (TangentSpace I) α).symmL ℝ b w) ≤ C * ‖w‖ ^ 2 := by
  have hKb : K ⊆ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hKs
  obtain ⟨C, hC0, hC⟩ := exists_quad_le hK
    (Q := fun b w => chartGramBilin (I := I) (M := M) g α b w w)
    ((continuousOn_chartGramBilin g α).mono (prod_mono hKb le_rfl))
    (fun b _ c w => by simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]; ring)
  exact ⟨C, hC0, fun b hb w => by rw [← chartGramBilin_self_eq]; exact hC b hb w⟩

/-- Lower comparison of `g` with the chart norm, on compact subsets of the chart domain. -/
theorem exists_tangent_clmAt_sq_le (α : M) {K : Set M} (hK : IsCompact K)
    (hKs : K ⊆ (chartAt H α).source) :
    ∃ C, 0 ≤ C ∧ ∀ b ∈ K, ∀ v : TangentSpace I b,
      ‖(trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b v‖ ^ 2 ≤
        C * g.inner b v v := by
  have hKb : K ⊆ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hKs
  obtain ⟨c, hc, hC⟩ := exists_quad_ge hK
    (Q := fun b w => chartGramBilin (I := I) (M := M) g α b w w)
    ((continuousOn_chartGramBilin g α).mono (prod_mono hKb le_rfl))
    (fun b _ c w => by simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]; ring)
    (fun b hb w hw => by
      rw [chartGramBilin_eq_innerJinv]
      refine modelInnerAt_pos_of_ne_zero g b ?_
      rw [Tensor.Tensor0SRiemannian.chartJinv_apply]
      intro h0
      apply hw
      have h1 := (trivializationAt E (TangentSpace I) α).continuousLinearMapAt_symmL (R := ℝ)
        (hKb hb) w
      rw [← h1, (ContinuousLinearEquiv.map_eq_zero_iff _).mp h0, map_zero])
  refine ⟨c⁻¹, inv_nonneg.mpr hc.le, fun b hb v => ?_⟩
  have h1 := hC b hb ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b v)
  rw [chartGramBilin_self_eq, Trivialization.symmL_continuousLinearMapAt _ (hKb hb)] at h1
  rw [inv_mul_eq_div, le_div_iff₀ hc, mul_comm]
  exact h1

end Tangent

/-! ### The derivative of the flow -/

section FlowDeriv

variable (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
variable (g : SmoothRiemannianMetric I M)

theorem local_flow_deriv_bound (x₀ : M) :
    ∃ W : Set M, IsOpen W ∧ x₀ ∈ W ∧ ∃ r > 0, ∃ C, 0 ≤ C ∧ ∀ x ∈ W, ∀ σ : ℝ, |σ| ≤ r →
      ∀ v : TangentSpace I x,
        g.inner (flow X σ x) (mfderiv I I (flow X σ) x v) (mfderiv I I (flow X σ) x v) ≤
          C * g.inner x v v := by
  set y₀ := flow X 0 x₀ with hy₀
  set p₀ : ℝ × M := (0, x₀) with hp₀
  have hf : ContMDiffAt ((𝓘(ℝ, ℝ).prod I).prod I) I ∞
      (Function.uncurry fun (p : ℝ × M) (y : M) => flow X p.1 y) (p₀, x₀) :=
    ((contMDiff_flow X).comp ((contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd)).contMDiffAt
  have hΦ := ContMDiffAt.mfderiv (m := 0) (fun (p : ℝ × M) (y : M) => flow X p.1 y) Prod.snd hf
    contMDiffAt_snd (by simp)
  set Φ := inTangentCoordinates I I Prod.snd (fun p : ℝ × M => flow X p.1 p.2)
    (fun p : ℝ × M => mfderiv I I (flow X p.1) p.2) p₀ with hΦdef
  have hcont : ContinuousAt Φ p₀ := hΦ.continuousAt
  set J := ‖Φ p₀‖ + 1 with hJ
  set O₀ := (extChartAt I x₀).source ∩ extChartAt I x₀ ⁻¹' patchΩ (I := I) x₀ with hO₀
  set O₁ := (extChartAt I y₀).source ∩ extChartAt I y₀ ⁻¹' patchΩ (I := I) y₀ with hO₁
  have hO₀o : IsOpen O₀ := (continuousOn_extChartAt x₀).isOpen_inter_preimage
    (isOpen_extChartAt_source x₀) (isOpen_patchΩ x₀)
  have hO₁o : IsOpen O₁ := (continuousOn_extChartAt y₀).isOpen_inter_preimage
    (isOpen_extChartAt_source y₀) (isOpen_patchΩ y₀)
  have e1 : ∀ᶠ p in 𝓝 p₀, p.2 ∈ O₀ := continuous_snd.continuousAt.preimage_mem_nhds
    (hO₀o.mem_nhds (show p₀.2 ∈ O₀ from ⟨mem_extChartAt_source x₀, mem_patchΩ_self x₀⟩))
  have e2 : ∀ᶠ p in 𝓝 p₀, flow X p.1 p.2 ∈ O₁ :=
    ((contMDiff_flow X).continuous.continuousAt (x := p₀)).preimage_mem_nhds
      (hO₁o.mem_nhds (show flow X p₀.1 p₀.2 ∈ O₁ from
        ⟨mem_extChartAt_source y₀, mem_patchΩ_self y₀⟩))
  have e3 : ∀ᶠ p in 𝓝 p₀, ‖Φ p‖ ≤ J :=
    (hcont.norm.eventually (gt_mem_nhds (lt_add_one ‖Φ p₀‖))).mono fun p hp => hp.le
  have hev : ∀ᶠ p in 𝓝 p₀, p.2 ∈ O₀ ∧ flow X p.1 p.2 ∈ O₁ ∧ ‖Φ p‖ ≤ J := e1.and (e2.and e3)
  obtain ⟨u, hu, v', hv', huv⟩ := mem_nhds_prod_iff.mp hev
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hu
  obtain ⟨C1, hC10, hC1⟩ := exists_tangent_inner_le g y₀ (isCompact_patchK (I := I) y₀)
    (patchK_subset (I := I) y₀)
  obtain ⟨C2, hC20, hC2⟩ := exists_tangent_clmAt_sq_le g x₀ (isCompact_patchK (I := I) x₀)
    (patchK_subset (I := I) x₀)
  refine ⟨interior v', isOpen_interior, mem_interior_iff_mem_nhds.mpr hv', ε / 2, by linarith,
    C1 * J ^ 2 * C2, by positivity, fun x hx σ hσ w => ?_⟩
  have hp : (σ, x) ∈ u ×ˢ v' := ⟨hball (by rw [Metric.mem_ball, Real.dist_eq, sub_zero]; linarith),
    interior_subset hx⟩
  obtain ⟨hxO, hφO, hΦJ⟩ := huv hp
  have hxK : x ∈ patchK (I := I) x₀ := mem_patchK hxO.1 hxO.2
  have hφK : flow X σ x ∈ patchK (I := I) y₀ := mem_patchK hφO.1 hφO.2
  have hxb : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet, ← extChartAt_source (I := I)]; exact hxO.1
  have hφb : flow X σ x ∈ (trivializationAt E (TangentSpace I) y₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet, ← extChartAt_source (I := I)]; exact hφO.1
  set a := (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x w with ha
  have hΦa : Φ (σ, x) a = (trivializationAt E (TangentSpace I) y₀).continuousLinearMapAt ℝ
      (flow X σ x) (mfderiv I I (flow X σ) x
        ((trivializationAt E (TangentSpace I) x₀).symmL ℝ x a)) := rfl
  rw [ha, Trivialization.symmL_continuousLinearMapAt _ hxb] at hΦa
  have hd : mfderiv I I (flow X σ) x w =
      (trivializationAt E (TangentSpace I) y₀).symmL ℝ (flow X σ x) (Φ (σ, x) a) := by
    rw [hΦa, Trivialization.symmL_continuousLinearMapAt _ hφb]
  rw [hd]
  have h1 := hC1 _ hφK (Φ (σ, x) a)
  have h2 : ‖Φ (σ, x) a‖ ^ 2 ≤ J ^ 2 * ‖a‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (((Φ (σ, x)).le_opNorm a).trans
      (mul_le_mul_of_nonneg_right hΦJ (norm_nonneg _))) 2
  have h3 := hC2 x hxK w
  calc _ ≤ C1 * ‖Φ (σ, x) a‖ ^ 2 := h1
    _ ≤ C1 * (J ^ 2 * (C2 * g.inner x w w)) :=
        mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 (sq_nonneg _))) hC10
    _ = C1 * J ^ 2 * C2 * g.inner x w w := by ring

/-- **Uniform bound for the derivative of the flow**, for `|σ| ≤ δ`. -/
theorem exists_flow_deriv_bound :
    ∃ δ > 0, ∃ C, 0 ≤ C ∧ ∀ σ : ℝ, |σ| ≤ δ → ∀ (x : M) (v : TangentSpace I x),
      g.inner (flow X σ x) (mfderiv I I (flow X σ) x v) (mfderiv I I (flow X σ) x v) ≤
        C * g.inner x v v := by
  classical
  choose W hWo hWx r hr C hC0 hC using fun x₀ : M => local_flow_deriv_bound X g x₀
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hWo (fun x _ => mem_iUnion.2 ⟨x, hWx x⟩)
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_le_finset t r (fun a _ => hr a)
  refine ⟨δ, hδ, ∑ α ∈ t, C α, Finset.sum_nonneg fun α _ => hC0 α, fun σ hσ x v => ?_⟩
  obtain ⟨α, hαt, hxα⟩ := mem_iUnion₂.mp (ht (mem_univ x))
  have hnn : 0 ≤ g.inner x v v := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact (g.pos x v hv).le
  refine (hC α x hxα σ (hσ.trans (hδle α hαt)) v).trans (mul_le_mul_of_nonneg_right ?_ hnn)
  exact Finset.single_le_sum (f := C) (fun α _ => hC0 α) hαt

end FlowDeriv

/-! ### The change of variables -/

section Volume

variable (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
variable (g : SmoothRiemannianMetric I M)

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem contMDiff_flow_at (σ : ℝ) : ContMDiff I I ∞ (flow X σ) :=
  (contMDiff_flow X).comp (contMDiff_const.prodMk contMDiff_id)

/-- The flow `φ_σ` as an equivalence. -/
def flowEquiv (σ : ℝ) : M ≃ M where
  toFun := flow X (-σ)
  invFun := flow X σ
  left_inv x := by
    have h := flow_neg_flow X (-σ) x
    rwa [neg_neg] at h
  right_inv x := flow_neg_flow X σ x

/-- The flow `φ_{-σ}` as a diffeomorphism, with inverse `φ_σ`. -/
def flowDiffeo (σ : ℝ) : M ≃ₘ⟮I, I⟯ M where
  toEquiv := flowEquiv X σ
  contMDiff_toFun := contMDiff_flow_at X (-σ)
  contMDiff_invFun := contMDiff_flow_at X σ

theorem coe_flowDiffeo (σ : ℝ) : ⇑(flowDiffeo X σ) = flow X (-σ) := rfl

theorem coe_flowDiffeo_symm (σ : ℝ) : ⇑(flowDiffeo X σ).symm = flow X σ := rfl

theorem continuous_fiberNormSq {a : ℕ} (S : SmoothCcTensor g 0 a) :
    Continuous fun x => riemannianFiberNormSq (I := I) (M := M) g 0 a x (S.toSection x) := by
  have hj : JointlySmoothOn g 0 a univ (fun _ : ℝ => S) :=
    _root_.ShortTime.jointlySmoothOn_const g univ S
  have h := Vendor.joint_riemannianFiberNormSq_cont g 0 a (fun _ : ℝ => S) (subset_refl univ) hj
  have h2 : Continuous fun x : M => ((0 : ℝ), x) := continuous_const.prodMk continuous_id
  have h3 := h.comp_continuous h2 fun x => ⟨mem_univ _, mem_univ _⟩
  exact h3.congr fun x => rfl

/-- **Change of variables along the flow**: `∫_M F(φ_σ x) dx ≤ C ∫_M F` for `|σ| ≤ δ`. -/
theorem exists_integral_comp_flow_le :
    ∃ δ > 0, ∃ C, 0 ≤ C ∧ ∀ σ : ℝ, |σ| ≤ δ → ∀ F : M → ℝ, Continuous F → (∀ x, 0 ≤ F x) →
      ∫ x, F (flow X σ x) ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
        C * ∫ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  obtain ⟨δ, hδ, Q, hQ0, hQ⟩ := exists_flow_deriv_bound X g
  have := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  set B := Real.sqrt ((Q + 1) ^ Module.finrank ℝ E) with hB
  refine ⟨δ, hδ, B, Real.sqrt_nonneg _, fun σ hσ F hF hF0 => ?_⟩
  set Φ := flowDiffeo X σ with hΦ
  have hsymm : (Φ.symm : M → M) = flow X σ := coe_flowDiffeo_symm X σ
  have hmap : Measure.map (flow X σ) (riemannianVolumeMeasure (I := I) (M := M) g) =
      riemannianVolumeMeasure (I := I) (M := M) (Diffeomorph.pullbackMetric g Φ) := by
    rw [riemannianVolumeMeasure_pullback (I := I) g Φ, hsymm]
  have hmeas : Measurable (flow X σ) := (contMDiff_flow_at X σ).continuous.measurable
  have hdens : ∀ x, riemannianVolumeDensity g (Diffeomorph.pullbackMetric g Φ) x ≤ B := by
    intro x
    refine riemannianVolumeDensity_le_of_inner_le g _ (by linarith) x fun v => ?_
    rw [Diffeomorph.pullbackMetric_inner, hΦ, coe_flowDiffeo]
    have h1 := hQ (-σ) (by rwa [abs_neg]) x v
    have hnn : 0 ≤ g.inner x v v := by
      rcases eq_or_ne v 0 with rfl | hv
      · simp
      · exact (g.pos x v hv).le
    exact h1.trans (by nlinarith)
  have hρm : Measurable fun x =>
      ENNReal.ofReal (riemannianVolumeDensity g (Diffeomorph.pullbackMetric g Φ) x) :=
    ENNReal.measurable_ofReal.comp (riemannianVolumeDensity_contMDiff (I := I) g
        (Diffeomorph.pullbackMetric g Φ)).continuous.measurable
  rw [← integral_map hmeas.aemeasurable hF.aestronglyMeasurable, hmap,
    riemannianVolumeMeasure_eq_withDensity g (Diffeomorph.pullbackMetric g Φ),
    integral_withDensity_eq_integral_toReal_smul₀ hρm.aemeasurable
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [← integral_const_mul]
  have hint : Integrable F (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hdc := (riemannianVolumeDensity_contMDiff (I := I) g (Diffeomorph.pullbackMetric g Φ)).continuous
  have hfun : (fun x => (ENNReal.ofReal
      (riemannianVolumeDensity g (Diffeomorph.pullbackMetric g Φ) x)).toReal • F x) =
      fun x => riemannianVolumeDensity g (Diffeomorph.pullbackMetric g Φ) x * F x := funext fun x => by
    rw [smul_eq_mul, ENNReal.toReal_ofReal (riemannianVolumeDensity_pos g _ x).le]
  rw [hfun]
  refine integral_mono ((hdc.mul hF).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)) (hint.const_mul B) fun x => ?_
  exact mul_le_mul_of_nonneg_right (hdens x) (hF0 x)

end Volume

end HFlow

end ShortTime
