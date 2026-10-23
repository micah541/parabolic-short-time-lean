import ShortTime.Nonlinear.FlowsNaturalChart

/-!
# The jet transport of the horizontal flow

Paper: Lemma `lem:flows` (d): `j^N(Π_σ u) = Θ_σ (Π_σ j^N u)` with `Θ_σ` a smooth family of linear maps
of jets, `Θ_0 = id`.

We state it in the form used by the naturality of the equation. For `|σ| < δ` there are linear maps
`Υ_σ(x) : J^N_x → J^N_{φ_σ x}` with

  `Υ_σ(x) (j^N u (x)) = j^N (Π_{-σ} u) (φ_σ x)`        (`exists_jetTransport`)

for every smooth `u`, `Υ_0(x) = id` (up to the identification of the fibres over `φ_0 x = x`), and
`(σ, x, ζ) ↦ Υ_σ(x) ζ` is smooth in the trivializations. With `σ` replaced by `-σ` and `x` by
`φ_σ x` this is the paper's `Θ_σ ∘ P_σ⁻¹`.

`Υ` is glued from the chart formulas `trivJet_hpull` by a smooth partition of unity on `M`,
subordinate to a finite cover by sets `W_α` on which the chart formula at `α` holds for `|σ| < δ_α`.
Only the values of `Υ_σ(x)` on jets of sections are determined (covariant jets are not arbitrary:
the antisymmetric part of `∇²u` is a curvature term), so the gluing is by convex combination.
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

/-! ### Jets in trivializations, as linear maps -/

section Lin

variable {s N : ℕ}

/-- `trivJet x₀ y` as a linear map. -/
def trivJetL (x₀ y : M) : CovJetFiber I 0 s N y →ₗ[ℝ] JetModel E 0 s N :=
  LinearMap.pi fun k => ((trivAt I M 0 (s + k) x₀).continuousLinearMapAt ℝ y).toLinearMap ∘ₗ
    LinearMap.proj k

theorem trivJetL_apply (x₀ y : M) (ζ : CovJetFiber I 0 s N y) :
    trivJetL x₀ y ζ = EquationData.trivJet x₀ y ζ := rfl

/-- `jetOfModel x₀ y` as a linear map. -/
def jetOfModelL (x₀ y : M) : JetModel E 0 s N →ₗ[ℝ] CovJetFiber I 0 s N y :=
  LinearMap.pi fun k => ((trivAt I M 0 (s + k) x₀).symmL ℝ y).toLinearMap ∘ₗ LinearMap.proj k

theorem jetOfModelL_apply (x₀ y : M) (w : JetModel E 0 s N) :
    jetOfModelL x₀ y w = jetOfModel (I := I) 0 s N x₀ y w := rfl

/-- The identification of the jet fibres over two equal points. -/
def jetCast {x y : M} (h : x = y) (ζ : CovJetFiber I 0 s N x) : CovJetFiber I 0 s N y :=
  h ▸ ζ

theorem jetOfModel_trivJet_cast {x₀ x y : M} (h : x = y) (hx : x ∈ jetBase (I := I) 0 s N x₀)
    (ζ : CovJetFiber I 0 s N x) :
    jetOfModel (I := I) 0 s N x₀ y (EquationData.trivJet x₀ x ζ) = jetCast h ζ := by
  subst h
  exact EquationData.jetOfModel_trivJet hx ζ

/-- Reading a jet given in one trivialization in another one is smooth. -/
theorem contMDiffAt_trivJet_jetOfModel
    {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] {HN : Type*} [TopologicalSpace HN]
    {J : ModelWithCorners ℝ EN HN} {Nn : Type*} [TopologicalSpace Nn] [ChartedSpace HN Nn]
    (x₁ x₂ : M) (b : Nn → M) (w : Nn → JetModel E 0 s N) {n₀ : Nn}
    (hb : ContMDiffAt J I ∞ b n₀) (hw : ContMDiffAt J 𝓘(ℝ, JetModel E 0 s N) ∞ w n₀)
    (h₁ : b n₀ ∈ jetBase (I := I) 0 s N x₁) (h₂ : b n₀ ∈ jetBase (I := I) 0 s N x₂) :
    ContMDiffAt J 𝓘(ℝ, JetModel E 0 s N) ∞
      (fun n => EquationData.trivJet x₂ (b n) (jetOfModel (I := I) 0 s N x₁ (b n) (w n))) n₀ := by
  rw [contMDiffAt_pi_space]
  intro k
  have hwk : ContMDiffAt J 𝓘(ℝ, TensorRSModel 0 (s + k) ℝ E) ∞ (fun n => w n k) n₀ := by
    let pr : JetModel E 0 s N →L[ℝ] TensorRSModel 0 (s + k) ℝ E :=
      ContinuousLinearMap.proj (R := ℝ) (φ := fun k : Fin (N + 1) => TensorRSModel 0 (s + (k : ℕ)) ℝ E) k
    exact pr.contDiff.contMDiff.contMDiffAt.comp n₀ hw
  have hv := contMDiffAt_symmL_apply (I := I) (M := M) x₁ b (fun n => w n k) hb hwk
    (mem_iInter.mp h₁.2 k)
  exact contMDiffAt_continuousLinearMapAt_apply (I := I) (M := M) x₂ b _ hv (mem_iInter.mp h₂.2 k)

end Lin

variable (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
variable (g : SmoothRiemannianMetric I M) (s : ℕ)

theorem flow_neg_flow (σ : ℝ) (x : M) : flow X (-σ) (flow X σ x) = x := by
  rw [← flow_add, add_neg_cancel, flow_zero]

/-! ### The chart formula at a point -/

/-- `trivJet_hpull`, at a point `y` of the chart with `φ_τ(y) = x`. -/
theorem trivJet_hpull_at (α : M) (N : ℕ) (u : SmoothCcTensor g 0 s) {τ : ℝ} {x y : M}
    (hy : y ∈ (extChartAt I α).source) (hxy : flow X τ y = x)
    (hq : (τ, extChartAt I α y) ∈ flowDom X α (I := I)) :
    EquationData.trivJet α y (covJet g 0 s N (hpull X g s τ u) y) =
      jetMap X g s α N (τ, extChartAt I α y) (EquationData.trivJet α x (covJet g 0 s N u x)) := by
  have h := trivJet_hpull X g s α N u hq
  simp only [flowPt] at h
  rw [(extChartAt I α).left_inv hy, hxy] at h
  exact h

/-- A neighbourhood of `α` on which the chart formula at `α` applies for small `|σ|`. -/
theorem exists_flow_nbhd (α : M) :
    ∃ δ > 0, ∃ W : Set M, IsOpen W ∧ α ∈ W ∧ ∀ x ∈ W, ∀ σ : ℝ, |σ| < δ →
      (-σ, extChartAt I α (flow X σ x)) ∈ flowDom X α (I := I) ∧
        flow X σ x ∈ (extChartAt I α).source ∧ x ∈ (extChartAt I α).source := by
  set O := (extChartAt I α).source ∩ extChartAt I α ⁻¹' patchΩ (I := I) α with hO
  have hOo : IsOpen O :=
    (continuousOn_extChartAt α).isOpen_inter_preimage (isOpen_extChartAt_source α)
      (isOpen_patchΩ α)
  have hαO : α ∈ O := ⟨mem_extChartAt_source α, mem_patchΩ_self α⟩
  have hpre : IsOpen ((fun q : ℝ × M => flow X q.1 q.2) ⁻¹' O) :=
    hOo.preimage (contMDiff_flow X).continuous
  have h0 : ((0 : ℝ), α) ∈ (fun q : ℝ × M => flow X q.1 q.2) ⁻¹' O := by
    simp only [mem_preimage, flow_zero]
    exact hαO
  obtain ⟨u, v, hu, hv, h0u, hαv, huv⟩ := isOpen_prod_iff.mp hpre 0 α h0
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hu 0 h0u
  refine ⟨δ, hδ, v ∩ O, hv.inter hOo, ⟨hαv, hαO⟩, fun x hx σ hσ => ?_⟩
  have hσu : σ ∈ u := hball (by simpa [Real.dist_eq] using hσ)
  have hfl : flow X σ x ∈ O := huv (mk_mem_prod hσu hx.1)
  refine ⟨⟨hfl.2, ?_, ?_⟩, hfl.1, hx.2.1⟩
  · simp only [flowPt]
    rw [(extChartAt I α).left_inv hfl.1, flow_neg_flow]
    exact hx.2.1
  · simp only [flowPt]
    rw [(extChartAt I α).left_inv hfl.1, flow_neg_flow]
    exact hx.2.2

theorem exists_pos_le_finset (t : Finset M) (f : M → ℝ) (hf : ∀ a ∈ t, 0 < f a) :
    ∃ δ > 0, ∀ a ∈ t, δ ≤ f a := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a t ha ih =>
    obtain ⟨δ, hδ, h⟩ := ih fun b hb => hf b (Finset.mem_insert_of_mem hb)
    refine ⟨min δ (f a), lt_min hδ (hf a (Finset.mem_insert_self a t)), fun b hb => ?_⟩
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (h b hb)

/-! ### The local pieces -/

/-- The jet transport given by the chart formula at `α`. -/
def termL (N : ℕ) (α : M) (σ : ℝ) (x : M) :
    CovJetFiber I 0 s N x →ₗ[ℝ] CovJetFiber I 0 s N (flow X σ x) :=
  (jetOfModelL α (flow X σ x)) ∘ₗ
    (jetMap X g s α N (-σ, extChartAt I α (flow X σ x))).toLinearMap ∘ₗ trivJetL α x

theorem termL_apply (N : ℕ) (α : M) (σ : ℝ) (x : M) (ζ : CovJetFiber I 0 s N x) :
    termL X g s N α σ x ζ = jetOfModel (I := I) 0 s N α (flow X σ x)
      (jetMap X g s α N (-σ, extChartAt I α (flow X σ x)) (EquationData.trivJet α x ζ)) := rfl

/-- On the good set, the local piece transports jets of sections. -/
theorem termL_covJet (N : ℕ) (α : M) {σ : ℝ} {x : M}
    (hq : (-σ, extChartAt I α (flow X σ x)) ∈ flowDom X α (I := I))
    (hfl : flow X σ x ∈ (extChartAt I α).source) (u : SmoothCcTensor g 0 s) :
    termL X g s N α σ x (covJet g 0 s N u x) =
      covJet g 0 s N (hpull X g s (-σ) u) (flow X σ x) := by
  rw [termL_apply, ← trivJet_hpull_at X g s α N u hfl (flow_neg_flow X σ x) hq]
  exact EquationData.jetOfModel_trivJet (mem_jetBase_of_source hfl) _

/-- At `σ = 0`, the local piece is the identity. -/
theorem termL_zero (N : ℕ) (α : M) {x : M}
    (hq : (-(0 : ℝ), extChartAt I α (flow X 0 x)) ∈ flowDom X α (I := I))
    (hx : x ∈ (extChartAt I α).source) (ζ : CovJetFiber I 0 s N x) :
    termL X g s N α 0 x ζ = jetCast (flow_zero X x).symm ζ := by
  rw [termL_apply, jetMap_zero X g s α N hq (by simp), ContinuousLinearMap.id_apply]
  exact jetOfModel_trivJet_cast _ (mem_jetBase_of_source hx) ζ

/-- Smoothness of the local piece, read in the trivializations at `x₀` and `y₀`. -/
theorem contMDiffAt_termL (N : ℕ) (α x₀ y₀ : M) {p₀ : ℝ × M × JetModel E 0 s N}
    (hq : (-p₀.1, extChartAt I α (flow X p₀.1 p₀.2.1)) ∈ flowDom X α (I := I))
    (hfl : flow X p₀.1 p₀.2.1 ∈ (extChartAt I α).source)
    (hx : p₀.2.1 ∈ (extChartAt I α).source)
    (hx₀ : p₀.2.1 ∈ jetBase (I := I) 0 s N x₀)
    (hy₀ : flow X p₀.1 p₀.2.1 ∈ jetBase (I := I) 0 s N y₀) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 s N))) 𝓘(ℝ, JetModel E 0 s N) ∞
      (fun p : ℝ × M × JetModel E 0 s N => EquationData.trivJet y₀ (flow X p.1 p.2.1)
        (termL X g s N α p.1 p.2.1 (jetOfModel (I := I) 0 s N x₀ p.2.1 p.2.2))) p₀ := by
  have hπx : ContMDiff (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 s N))) I ∞
      (fun p : ℝ × M × JetModel E 0 s N => p.2.1) := contMDiff_fst.comp contMDiff_snd
  have hπw : ContMDiff (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 s N))) 𝓘(ℝ, JetModel E 0 s N) ∞
      (fun p : ℝ × M × JetModel E 0 s N => p.2.2) := contMDiff_snd.comp contMDiff_snd
  have hπσ : ContMDiff (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 s N))) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M × JetModel E 0 s N => p.1) := contMDiff_fst
  have hfl' : ContMDiff (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 s N))) I ∞
      (fun p : ℝ × M × JetModel E 0 s N => flow X p.1 p.2.1) :=
    (contMDiff_flow X).comp (hπσ.prodMk hπx)
  -- the jet at `x` in the trivialization at `α`
  have h1 : ContMDiffAt (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 s N))) 𝓘(ℝ, JetModel E 0 s N) ∞
      (fun p : ℝ × M × JetModel E 0 s N =>
        EquationData.trivJet α p.2.1 (jetOfModel (I := I) 0 s N x₀ p.2.1 p.2.2)) p₀ :=
    contMDiffAt_trivJet_jetOfModel x₀ α (fun p : ℝ × M × JetModel E 0 s N => p.2.1)
      (fun p : ℝ × M × JetModel E 0 s N => p.2.2) (hπx p₀) (hπw p₀) hx₀
      (mem_jetBase_of_source hx)
  -- the chart point `(-σ, chart(φ_σ x))`
  have hq' : ContMDiffAt (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 s N))) 𝓘(ℝ, ℝ × E) ∞
      (fun p : ℝ × M × JetModel E 0 s N => (-p.1, extChartAt I α (flow X p.1 p.2.1))) p₀ := by
    have hneg : ContMDiffAt (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 s N))) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M × JetModel E 0 s N => -p.1) p₀ :=
      (contDiff_neg (𝕜 := ℝ) (F := ℝ) (n := ∞)).contMDiff.contMDiffAt.comp p₀ (hπσ p₀)
    have hch : ContMDiffAt (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 s N))) 𝓘(ℝ, E) ∞
        (fun p : ℝ × M × JetModel E 0 s N => extChartAt I α (flow X p.1 p.2.1)) p₀ := by
      have hc := (contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)).contMDiffAt
        ((chartAt H α).open_source.mem_nhds (by rw [← extChartAt_source (I := I)]; exact hfl))
      exact hc.comp p₀ hfl'.contMDiffAt
    have h := hneg.prodMk_space hch
    exact h
  obtain ⟨Jm, hJm⟩ : ∃ Jm : ℝ × E → JetModel E 0 s N →L[ℝ] JetModel E 0 s N,
      Jm = jetMap X g s α N := ⟨_, rfl⟩
  have hJ : ContMDiffAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ, JetModel E 0 s N →L[ℝ] JetModel E 0 s N) ∞
      Jm (-p₀.1, extChartAt I α (flow X p₀.1 p₀.2.1)) := by
    rw [hJm]
    exact ((contDiffOn_jetMap X g s α N).contDiffAt ((isOpen_flowDom X α).mem_nhds hq)).contMDiffAt
  have h2 : ContMDiffAt (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 s N))) 𝓘(ℝ, JetModel E 0 s N) ∞
      (fun p : ℝ × M × JetModel E 0 s N => Jm (-p.1, extChartAt I α (flow X p.1 p.2.1))
        (EquationData.trivJet α p.2.1 (jetOfModel (I := I) 0 s N x₀ p.2.1 p.2.2))) p₀ :=
    (hJ.comp p₀ hq').clm_apply h1
  have h3 := contMDiffAt_trivJet_jetOfModel α y₀ (fun p : ℝ × M × JetModel E 0 s N =>
    flow X p.1 p.2.1) _ hfl'.contMDiffAt h2 (mem_jetBase_of_source hfl) hy₀
  have hfun : (fun p : ℝ × M × JetModel E 0 s N => EquationData.trivJet y₀ (flow X p.1 p.2.1)
        (termL X g s N α p.1 p.2.1 (jetOfModel (I := I) 0 s N x₀ p.2.1 p.2.2))) =
      (fun p : ℝ × M × JetModel E 0 s N => EquationData.trivJet y₀ (flow X p.1 p.2.1)
        (jetOfModel (I := I) 0 s N α (flow X p.1 p.2.1)
          (Jm (-p.1, extChartAt I α (flow X p.1 p.2.1))
            (EquationData.trivJet α p.2.1 (jetOfModel (I := I) 0 s N x₀ p.2.1 p.2.2))))) := by
    funext p
    rw [termL_apply, hJm]
  rw [hfun]
  exact h3

/-! ### Gluing -/

/-- **The jet transport of the horizontal flow** (`lem:flows` (d)). For `|σ| < δ`,
`Υ_σ(x) (j^N u (x)) = j^N (Π_{-σ} u)(φ_σ x)`; `Υ_0 = id`; and `Υ` is smooth in the
trivializations. -/
theorem exists_jetTransport (N : ℕ) :
    ∃ δ > 0, ∃ Υ : ∀ σ : ℝ, ∀ x : M, CovJetFiber I 0 s N x →ₗ[ℝ] CovJetFiber I 0 s N (flow X σ x),
      (∀ σ : ℝ, |σ| < δ → ∀ (x : M) (u : SmoothCcTensor g 0 s),
        Υ σ x (covJet g 0 s N u x) = covJet g 0 s N (hpull X g s (-σ) u) (flow X σ x)) ∧
      (∀ (x : M) (ζ : CovJetFiber I 0 s N x), Υ 0 x ζ = jetCast (flow_zero X x).symm ζ) ∧
      (∀ x₀ y₀ : M,
        ContMDiffOn (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 s N))) 𝓘(ℝ, JetModel E 0 s N) ∞
          (fun p : ℝ × M × JetModel E 0 s N => EquationData.trivJet y₀ (flow X p.1 p.2.1)
            (Υ p.1 p.2.1 (jetOfModel (I := I) 0 s N x₀ p.2.1 p.2.2)))
          {p | |p.1| < δ ∧ p.2.1 ∈ jetBase (I := I) 0 s N x₀ ∧
            flow X p.1 p.2.1 ∈ jetBase (I := I) 0 s N y₀}) := by
  classical
  choose δf hδf W hWo hWα hW using exists_flow_nbhd X (I := I)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hWo
    (fun x _ => mem_iUnion.2 ⟨x, hWα x⟩)
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_le_finset t δf (fun a _ => hδf a)
  have hcov : (univ : Set M) ⊆ ⋃ i : t, W i := by
    intro x _
    obtain ⟨i, hi, hx⟩ := mem_iUnion₂.mp (ht (mem_univ x))
    exact mem_iUnion.2 ⟨⟨i, hi⟩, hx⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := I) isClosed_univ
    (fun i : t => W i) (fun i => hWo i) hcov
  have hsum : ∀ x : M, ∑ i : t, ρ i x = 1 := by
    intro x
    rw [← finsum_eq_sum_of_fintype]
    exact ρ.sum_eq_one (mem_univ x)
  have hgood : ∀ (i : t) (x : M), ρ i x ≠ 0 → ∀ σ : ℝ, |σ| < δ →
      (-σ, extChartAt I (i : M) (flow X σ x)) ∈ flowDom X (i : M) (I := I) ∧
        flow X σ x ∈ (extChartAt I (i : M)).source ∧ x ∈ (extChartAt I (i : M)).source := by
    intro i x hx σ hσ
    exact hW i x (hρ i (subset_tsupport _ (Function.mem_support.mpr hx))) σ
      (hσ.trans_le (hδle i i.2))
  refine ⟨δ, hδ, fun σ x => ∑ i : t, ρ i x • termL X g s N (i : M) σ x, ?_, ?_, ?_⟩
  · -- the transport of jets
    intro σ hσ x u
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    have hterm : ∀ i : t, ρ i x • termL X g s N (i : M) σ x (covJet g 0 s N u x) =
        ρ i x • covJet g 0 s N (hpull X g s (-σ) u) (flow X σ x) := by
      intro i
      by_cases hx : ρ i x = 0
      · rw [hx, zero_smul, zero_smul]
      · obtain ⟨hq, hfl, -⟩ := hgood i x hx σ hσ
        rw [termL_covJet X g s N (i : M) hq hfl u]
    rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_smul, hsum, one_smul]
  · -- `Υ_0 = id`
    intro x ζ
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    have hterm : ∀ i : t, ρ i x • termL X g s N (i : M) 0 x ζ =
        ρ i x • jetCast (flow_zero X x).symm ζ := by
      intro i
      by_cases hx : ρ i x = 0
      · rw [hx, zero_smul, zero_smul]
      · obtain ⟨hq, -, hxs⟩ := hgood i x hx 0 (by simpa using hδ)
        rw [termL_zero X g s N (i : M) hq hxs ζ]
    rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_smul, hsum, one_smul]
  · -- smoothness
    intro x₀ y₀
    have hopen : IsOpen {p : ℝ × M × JetModel E 0 s N | |p.1| < δ ∧
        p.2.1 ∈ jetBase (I := I) 0 s N x₀ ∧ flow X p.1 p.2.1 ∈ jetBase (I := I) 0 s N y₀} := by
      have hb : ∀ z : M, IsOpen (jetBase (I := I) 0 s N z) := fun z =>
        (trivAt I M 0 s z).open_baseSet.inter
          (isOpen_iInter_of_finite fun k => (trivAt I M 0 (s + k) z).open_baseSet)
      have hc : Continuous fun p : ℝ × M × JetModel E 0 s N => flow X p.1 p.2.1 :=
        (contMDiff_flow X).continuous.comp (continuous_fst.prodMk continuous_snd.fst)
      exact (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
        (((hb x₀).preimage continuous_snd.fst).inter ((hb y₀).preimage hc))
    intro p₀ hp₀
    refine ContMDiffAt.contMDiffWithinAt ?_
    have hlin : ∀ p : ℝ × M × JetModel E 0 s N,
        EquationData.trivJet y₀ (flow X p.1 p.2.1)
          ((∑ i : t, ρ i p.2.1 • termL X g s N (i : M) p.1 p.2.1)
            (jetOfModel (I := I) 0 s N x₀ p.2.1 p.2.2)) =
        ∑ i : t, ρ i p.2.1 • EquationData.trivJet y₀ (flow X p.1 p.2.1)
          (termL X g s N (i : M) p.1 p.2.1 (jetOfModel (I := I) 0 s N x₀ p.2.1 p.2.2)) := by
      intro p
      simp only [LinearMap.sum_apply, LinearMap.smul_apply,
        ← trivJetL_apply, map_sum, map_smul]
    simp only [hlin]
    refine contMDiffAt_finsetSum fun i _ => ?_
    have hρs : ContMDiffAt (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 s N))) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M × JetModel E 0 s N => ρ i p.2.1) p₀ :=
      ((ρ i).contMDiff.comp (contMDiff_fst.comp contMDiff_snd)).contMDiffAt
    by_cases hsupp : p₀.2.1 ∈ tsupport (ρ i)
    · -- near `p₀`, the chart formula at `i` applies
      have hWi : p₀.2.1 ∈ W i := hρ i hsupp
      obtain ⟨hq, hfl, hxs⟩ := hW i p₀.2.1 hWi p₀.1 (hp₀.1.trans_le (hδle i i.2))
      exact hρs.smul (contMDiffAt_termL X g s N (i : M) x₀ y₀ hq hfl hxs hp₀.2.1 hp₀.2.2)
    · -- away from the support, the term vanishes
      have hev : (fun p : ℝ × M × JetModel E 0 s N => ρ i p.2.1 •
            EquationData.trivJet y₀ (flow X p.1 p.2.1)
              (termL X g s N (i : M) p.1 p.2.1 (jetOfModel (I := I) 0 s N x₀ p.2.1 p.2.2))) =ᶠ[𝓝 p₀]
          fun _ => 0 := by
        have hopen' : IsOpen ((tsupport (ρ i))ᶜ) := (isClosed_tsupport _).isOpen_compl
        filter_upwards [(hopen'.preimage continuous_snd.fst).mem_nhds hsupp] with p hp
        rw [image_eq_zero_of_notMem_tsupport hp, zero_smul]
      exact contMDiffAt_const.congr_of_eventuallyEq hev

end HFlow

end ShortTime
