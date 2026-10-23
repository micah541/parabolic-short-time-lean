import ShortTime.Nonlinear.FlowsNaturalJet
import ShortTime.Nonlinear.EqFibre

/-!
# Naturality of the equation under the horizontal flow

Paper: Lemma `lem:flows` (d).

For equation data `D` on `T⁰_s M` and the horizontal pullback `Π_σ` along the flow of `X`, the
transported nonlinearity

  `F_σ(t, x, ζ) = P_σ(x)⁻¹ F(t, φ_σ x, Υ_σ(x) ζ)`,     `|σ| < δ`,

is a smooth fibre map with parameter `σ` (`natFibreMap`), with `F_0 = F` (`natFibreMap_F_zero`,
`natFibreMap_dom_zero`), and

  `Π_σ (F[u](t)) = F_σ[Π_σ u](t)`                       (`hpull_nonlinFamily`)

for every smooth family `u` with jets in the domain. Here `Υ_σ(x)` is the jet transport of
`exists_jetTransport`: `Υ_σ(x) (j^{2p} v (x)) = j^{2p} (Π_{-σ} v) (φ_σ x)`. Since `Π_{-σ} Π_σ = id`,
`Υ_σ(x)` takes the jet of `Π_σ u` at `x` to the jet of `u` at `φ_σ x`, which is all the identity
needs; the paper's `Θ_σ⁻¹` is never formed.
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

/-! ### Readings in trivializations, within a set -/

/-- Reading a section in a fixed trivialization, within a set. -/
theorem contMDiffWithinAt_clmAt_apply {a : ℕ}
    {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] {HN : Type*} [TopologicalSpace HN]
    {J : ModelWithCorners ℝ EN HN} {Nn : Type*} [TopologicalSpace Nn] [ChartedSpace HN Nn]
    (x₀ : M) (b : Nn → M) (v : ∀ n, TensorRSSpace 0 a I (b n)) {S : Set Nn} {n₀ : Nn}
    (hv : ContMDiffWithinAt J (I.prod 𝓘(ℝ, TensorRSModel 0 a ℝ E)) ∞
      (fun n => TotalSpace.mk' (TensorRSModel 0 a ℝ E)
        (E := fun x : M => TensorRSSpace 0 a I x) (b n) (v n)) S n₀)
    (hn : b n₀ ∈ (trivAt I M 0 a x₀).baseSet) :
    ContMDiffWithinAt J 𝓘(ℝ, TensorRSModel 0 a ℝ E) ∞
      (fun n => (trivAt I M 0 a x₀).continuousLinearMapAt ℝ (b n) (v n)) S n₀ := by
  have h := ((trivAt I M 0 a x₀).contMDiffWithinAt_iff
    (by simpa [Trivialization.mem_source] using hn)).mp hv
  have hbc : ContinuousWithinAt b S n₀ := (contMDiffWithinAt_totalSpace.mp hv).1.continuousWithinAt
  refine h.2.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hbc.preimage_mem_nhdsWithin ((trivAt I M 0 a x₀).open_baseSet.mem_nhds hn)]
      with n hn'
    rw [Trivialization.continuousLinearMapAt_apply, Trivialization.coe_linearMapAt_of_mem _ hn']
  · rw [Trivialization.continuousLinearMapAt_apply, Trivialization.coe_linearMapAt_of_mem _ hn]

variable (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
variable (g : SmoothRiemannianMetric I M)

/-- Reading `P_σ(x)⁻¹ w`, with `w` given in the trivialization at `y₀`, in the trivialization at
`x₀`. -/
theorem contMDiffWithinAt_pt_read {s : ℕ}
    {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] {HN : Type*} [TopologicalSpace HN]
    {J : ModelWithCorners ℝ EN HN} {Nn : Type*} [TopologicalSpace Nn] [ChartedSpace HN Nn]
    [IsManifold J ∞ Nn]
    (x₀ y₀ : M) (σf : Nn → ℝ) (xf : Nn → M) (v : Nn → TensorRSModel 0 s ℝ E)
    {S : Set Nn} {n₀ : Nn}
    (hσ : ContMDiffAt J 𝓘(ℝ, ℝ) ∞ σf n₀) (hx : ContMDiffAt J I ∞ xf n₀)
    (hv : ContMDiffWithinAt J 𝓘(ℝ, TensorRSModel 0 s ℝ E) ∞ v S n₀)
    (hxb : xf n₀ ∈ (trivAt I M 0 s x₀).baseSet)
    (hyb : flow X (σf n₀) (xf n₀) ∈ (trivAt I M 0 s y₀).baseSet) :
    ContMDiffWithinAt J 𝓘(ℝ, TensorRSModel 0 s ℝ E) ∞
      (fun n => (trivAt I M 0 s x₀).continuousLinearMapAt ℝ (xf n)
        ((pt X g s (σf n) (xf n)).symm
          ((trivAt I M 0 s y₀).symmL ℝ (flow X (σf n) (xf n)) (v n)))) S n₀ := by
  set e := trivAt I M 0 s y₀ with he
  have hopen : IsOpen {q' : (ℝ × M) × TensorRSModel 0 s ℝ E |
      q'.1.1 ∈ (univ : Set ℝ) ∧ flow X q'.1.1 q'.1.2 ∈ e.baseSet} := by
    simp only [mem_univ, true_and]
    exact ((contMDiff_flow X).continuous.comp continuous_fst).isOpen_preimage _ e.open_baseSet
  have hinv := (ptRaw_inverse X g s e).contMDiffAt
    (hopen.mem_nhds (x := ((σf n₀, xf n₀), v n₀)) ⟨mem_univ _, hyb⟩)
  have hm : ContMDiffWithinAt J ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun n => ((σf n, xf n), v n)) S n₀ :=
    (hσ.contMDiffWithinAt.prodMk hx.contMDiffWithinAt).prodMk hv
  have hcomp := hinv.comp_contMDiffWithinAt n₀ hm
  have htot : ContMDiffWithinAt J (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun n => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun x : M => TensorRSSpace 0 s I x) (xf n)
        ((pt X g s (σf n) (xf n)).symm (e.symmL ℝ (flow X (σf n) (xf n)) (v n)))) S n₀ := by
    refine hcomp.congr (fun n _ => ?_) ?_
    · exact mk_pt_symm X g s (σf n) (xf n) _
    · exact mk_pt_symm X g s (σf n₀) (xf n₀) _
  exact contMDiffWithinAt_clmAt_apply x₀ xf _ htot hxb

/-! ### The jet transport, fixed -/

section Transport

variable (s : ℕ)

/-- The radius of validity of the jet transport. -/
def natδ (N : ℕ) : ℝ := (exists_jetTransport X g s (I := I) N).choose

theorem natδ_pos (N : ℕ) : 0 < natδ X g s N (I := I) :=
  (exists_jetTransport X g s (I := I) N).choose_spec.1

/-- The jet transport `Υ_σ(x) : J^N_x → J^N_{φ_σ x}` (`exists_jetTransport`). -/
def natΥ (N : ℕ) (σ : ℝ) (x : M) : CovJetFiber I 0 s N x →ₗ[ℝ] CovJetFiber I 0 s N (flow X σ x) :=
  (exists_jetTransport X g s (I := I) N).choose_spec.2.choose σ x

theorem natΥ_covJet (N : ℕ) {σ : ℝ} (hσ : |σ| < natδ X g s N (I := I)) (x : M)
    (u : SmoothCcTensor g 0 s) :
    natΥ X g s N σ x (covJet g 0 s N u x) = covJet g 0 s N (hpull X g s (-σ) u) (flow X σ x) :=
  (exists_jetTransport X g s (I := I) N).choose_spec.2.choose_spec.1 σ hσ x u

theorem natΥ_zero (N : ℕ) (x : M) (ζ : CovJetFiber I 0 s N x) :
    natΥ X g s N 0 x ζ = jetCast (flow_zero X x).symm ζ :=
  (exists_jetTransport X g s (I := I) N).choose_spec.2.choose_spec.2.1 x ζ

theorem contMDiffOn_natΥ (N : ℕ) (x₀ y₀ : M) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 s N))) 𝓘(ℝ, JetModel E 0 s N) ∞
      (fun p : ℝ × M × JetModel E 0 s N => EquationData.trivJet y₀ (flow X p.1 p.2.1)
        (natΥ X g s N p.1 p.2.1 (jetOfModel (I := I) 0 s N x₀ p.2.1 p.2.2)))
      {p | |p.1| < natδ X g s N (I := I) ∧ p.2.1 ∈ jetBase (I := I) 0 s N x₀ ∧
        flow X p.1 p.2.1 ∈ jetBase (I := I) 0 s N y₀} :=
  (exists_jetTransport X g s (I := I) N).choose_spec.2.choose_spec.2.2 x₀ y₀

theorem isOpen_natΥ_dom (N : ℕ) (x₀ y₀ : M) :
    IsOpen {p : ℝ × M × JetModel E 0 s N | |p.1| < natδ X g s N (I := I) ∧
      p.2.1 ∈ jetBase (I := I) 0 s N x₀ ∧ flow X p.1 p.2.1 ∈ jetBase (I := I) 0 s N y₀} := by
  have hb : ∀ z : M, IsOpen (jetBase (I := I) 0 s N z) := fun z =>
    (trivAt I M 0 s z).open_baseSet.inter
      (isOpen_iInter_of_finite fun k => (trivAt I M 0 (s + k) z).open_baseSet)
  have hc : Continuous fun p : ℝ × M × JetModel E 0 s N => flow X p.1 p.2.1 :=
    (contMDiff_flow X).continuous.comp (continuous_fst.prodMk continuous_snd.fst)
  exact (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
    (((hb x₀).preimage continuous_snd.fst).inter ((hb y₀).preimage hc))

end Transport

/-! ### The transported nonlinearity -/

section Natural

variable {s p : ℕ} (D : EquationData I M 0 s p)

/-- `F_σ(t, x, ζ) = P_σ(x)⁻¹ F(t, φ_σ x, Υ_σ(x) ζ)`. -/
def natF (σ t : ℝ) (x : M) (ζ : CovJetFiber I 0 s (2 * p) x) : TensorRSSpace 0 s I x :=
  (pt X g s σ x).symm (D.F t (flow X σ x) (natΥ X g s (2 * p) σ x ζ))

/-- The domain of `F_σ`: `|σ| < δ` and `Υ_σ(x) ζ ∈ 𝒟`. -/
def natDom (σ t : ℝ) (x : M) : Set (CovJetFiber I 0 s (2 * p) x) :=
  {ζ | |σ| < natδ X g s (2 * p) (I := I) ∧ natΥ X g s (2 * p) σ x ζ ∈ D.dom t (flow X σ x)}

/-- The jet transport read in the trivializations at `x₀` and `y₀`, as a function of
`(σ, t, x, z)`. -/
def natW (x₀ y₀ : M) (q : ℝ × ℝ × M × JetModel E 0 s (2 * p)) : JetModel E 0 s (2 * p) :=
  EquationData.trivJet y₀ (flow X q.1 q.2.2.1)
    (natΥ X g s (2 * p) q.1 q.2.2.1 (jetOfModel (I := I) 0 s (2 * p) x₀ q.2.2.1 q.2.2.2))

theorem contMDiffAt_natW (x₀ y₀ : M) {q₀ : ℝ × ℝ × M × JetModel E 0 s (2 * p)}
    (hσ : |q₀.1| < natδ X g s (2 * p) (I := I)) (hx : q₀.2.2.1 ∈ jetBase (I := I) 0 s (2 * p) x₀)
    (hy : flow X q₀.1 q₀.2.2.1 ∈ jetBase (I := I) 0 s (2 * p) y₀) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 s (2 * p)))))
      𝓘(ℝ, JetModel E 0 s (2 * p)) ∞ (natW X g (s := s) (p := p) x₀ y₀) q₀ := by
  have hpr : ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 s (2 * p)))))
      (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 s (2 * p)))) ∞
      (fun q : ℝ × ℝ × M × JetModel E 0 s (2 * p) => (q.1, q.2.2.1, q.2.2.2)) :=
    contMDiff_fst.prodMk (contMDiff_snd.comp contMDiff_snd)
  have h := (contMDiffOn_natΥ X g s (2 * p) x₀ y₀).contMDiffAt
    ((isOpen_natΥ_dom X g s (2 * p) x₀ y₀).mem_nhds (x := (q₀.1, q₀.2.2.1, q₀.2.2.2))
      ⟨hσ, hx, hy⟩)
  exact h.comp q₀ hpr.contMDiffAt

theorem continuousOn_natW (x₀ y₀ : M) :
    ContinuousOn (natW X g (s := s) (p := p) x₀ y₀)
      {q | |q.1| < natδ X g s (2 * p) (I := I) ∧ q.2.2.1 ∈ jetBase (I := I) 0 s (2 * p) x₀ ∧
        flow X q.1 q.2.2.1 ∈ jetBase (I := I) 0 s (2 * p) y₀} := fun q hq =>
  (contMDiffAt_natW X g x₀ y₀ hq.1 hq.2.1 hq.2.2).continuousAt.continuousWithinAt

theorem jetOfModel_natW {x₀ y₀ : M} {q : ℝ × ℝ × M × JetModel E 0 s (2 * p)}
    (hy : flow X q.1 q.2.2.1 ∈ jetBase (I := I) 0 s (2 * p) y₀) :
    jetOfModel (I := I) 0 s (2 * p) y₀ (flow X q.1 q.2.2.1) (natW X g x₀ y₀ q) =
      natΥ X g s (2 * p) q.1 q.2.2.1 (jetOfModel (I := I) 0 s (2 * p) x₀ q.2.2.1 q.2.2.2) :=
  EquationData.jetOfModel_trivJet hy _

theorem mem_jetBase_self (N : ℕ) (y : M) : y ∈ jetBase (I := I) 0 s N y :=
  ⟨mem_baseSet_trivializationAt _ _ y, mem_iInter.2 fun _ => mem_baseSet_trivializationAt _ _ y⟩

theorem isOpen_jetBase (N : ℕ) (z : M) : IsOpen (jetBase (I := I) 0 s N z) :=
  (trivAt I M 0 s z).open_baseSet.inter
    (isOpen_iInter_of_finite fun k => (trivAt I M 0 (s + k) z).open_baseSet)

/-- The domain of `F_σ` is relatively open. -/
theorem natDom_relOpen (x₀ : M) :
    ∃ U : Set (ℝ × ℝ × M × ProdModel E (EquationData.jetRanks s p)), IsOpen U ∧
      {q ∈ prodSlab (I := I) ℝ (EquationData.jetRanks s p) s D.T₀ x₀ |
          prodOfModel (EquationData.jetRanks s p) x₀ q.2.2.1 q.2.2.2 ∈
            natDom X g D q.1 q.2.1 q.2.2.1} =
        U ∩ prodSlab (I := I) ℝ (EquationData.jetRanks s p) s D.T₀ x₀ := by
  set A := {q ∈ prodSlab (I := I) ℝ (EquationData.jetRanks s p) s D.T₀ x₀ |
    prodOfModel (EquationData.jetRanks s p) x₀ q.2.2.1 q.2.2.2 ∈
      natDom X g D q.1 q.2.1 q.2.2.1} with hA
  have hloc : ∀ q₀ ∈ A, ∃ V : Set (ℝ × ℝ × M × ProdModel E (EquationData.jetRanks s p)),
      IsOpen V ∧ q₀ ∈ V ∧ V ∩ prodSlab (I := I) ℝ (EquationData.jetRanks s p) s D.T₀ x₀ ⊆ A := by
    intro q₀ hq₀
    obtain ⟨⟨ht₀, hx₀⟩, hσ₀, hd₀⟩ := hq₀
    set y₀ := flow X q₀.1 q₀.2.2.1 with hy₀
    obtain ⟨UD, hUDo, hUD⟩ := D.dom_relOpen y₀
    set O := {q : ℝ × ℝ × M × JetModel E 0 s (2 * p) | |q.1| < natδ X g s (2 * p) (I := I) ∧
      q.2.2.1 ∈ jetBase (I := I) 0 s (2 * p) x₀ ∧
        flow X q.1 q.2.2.1 ∈ jetBase (I := I) 0 s (2 * p) y₀} with hO
    have hOo : IsOpen O := by
      have hc : Continuous fun q : ℝ × ℝ × M × JetModel E 0 s (2 * p) => flow X q.1 q.2.2.1 :=
        (contMDiff_flow X).continuous.comp (continuous_fst.prodMk continuous_snd.snd.fst)
      exact (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
        (((isOpen_jetBase (2 * p) x₀).preimage continuous_snd.snd.fst).inter
          ((isOpen_jetBase (2 * p) y₀).preimage hc))
    let Ψ : ℝ × ℝ × M × JetModel E 0 s (2 * p) → ℝ × M × JetModel E 0 s (2 * p) :=
      fun q => (q.2.1, flow X q.1 q.2.2.1, natW X g x₀ y₀ q)
    have hΨ : ContinuousOn Ψ O := by
      have hc : Continuous fun q : ℝ × ℝ × M × JetModel E 0 s (2 * p) => flow X q.1 q.2.2.1 :=
        (contMDiff_flow X).continuous.comp (continuous_fst.prodMk continuous_snd.snd.fst)
      exact continuous_snd.fst.continuousOn.prodMk (hc.continuousOn.prodMk
        (continuousOn_natW X g x₀ y₀))
    refine ⟨O ∩ Ψ ⁻¹' UD, hΨ.isOpen_inter_preimage hOo hUDo, ⟨⟨hσ₀, hx₀, ?_⟩, ?_⟩, ?_⟩
    · exact mem_jetBase_self (2 * p) y₀
    · have hloc : Ψ q₀ ∈ localDom 0 s (2 * p) D.T₀ D.dom y₀ := by
        refine ⟨⟨ht₀, mem_jetBase_self (2 * p) y₀⟩, ?_⟩
        change jetOfModel (I := I) 0 s (2 * p) y₀ (flow X q₀.1 q₀.2.2.1) (natW X g x₀ y₀ q₀) ∈ _
        rw [jetOfModel_natW X g (mem_jetBase_self (2 * p) y₀)]
        exact hd₀
      rw [hUD] at hloc
      exact hloc.1
    · rintro q ⟨⟨hqO, hqU⟩, hqs⟩
      refine ⟨hqs, hqO.1, ?_⟩
      have hloc : Ψ q ∈ localDom 0 s (2 * p) D.T₀ D.dom y₀ := by
        rw [hUD]
        exact ⟨hqU, hqs.1, hqO.2.2⟩
      have h2 := hloc.2
      change jetOfModel (I := I) 0 s (2 * p) y₀ (flow X q.1 q.2.2.1) (natW X g x₀ y₀ q) ∈ _ at h2
      rw [jetOfModel_natW X g hqO.2.2] at h2
      exact h2
  choose! V hVo hqV hVA using hloc
  refine ⟨⋃ q ∈ A, V q, isOpen_biUnion fun q hq => hVo q hq, ?_⟩
  ext q
  constructor
  · intro hq
    exact ⟨mem_biUnion hq (hqV q hq), hq.1⟩
  · rintro ⟨hU, hs⟩
    obtain ⟨q', hq', hqV'⟩ := mem_iUnion₂.mp hU
    exact hVA q' hq' ⟨hqV', hs⟩

/-- `F_σ` is smooth on its domain, read in the trivializations at `x₀`. -/
theorem natF_smooth (x₀ : M) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 s (2 * p)))))
      𝓘(ℝ, TensorRSModel 0 s ℝ E) ∞
      (fun q : ℝ × ℝ × M × JetModel E 0 s (2 * p) =>
        (trivAt I M 0 s x₀).continuousLinearMapAt ℝ q.2.2.1
          (natF X g D q.1 q.2.1 q.2.2.1 (jetOfModel (I := I) 0 s (2 * p) x₀ q.2.2.1 q.2.2.2)))
      {q | (q.2.1 ∈ Icc 0 D.T₀ ∧ q.2.2.1 ∈ jetBase (I := I) 0 s (2 * p) x₀) ∧
        jetOfModel (I := I) 0 s (2 * p) x₀ q.2.2.1 q.2.2.2 ∈ natDom X g D q.1 q.2.1 q.2.2.1} := by
  intro q₀ hq₀
  obtain ⟨⟨ht₀, hx₀⟩, hσ₀, hd₀⟩ := hq₀
  set y₀ := flow X q₀.1 q₀.2.2.1 with hy₀
  set Sset := {q : ℝ × ℝ × M × JetModel E 0 s (2 * p) |
    (q.2.1 ∈ Icc 0 D.T₀ ∧ q.2.2.1 ∈ jetBase (I := I) 0 s (2 * p) x₀) ∧
      jetOfModel (I := I) 0 s (2 * p) x₀ q.2.2.1 q.2.2.2 ∈ natDom X g D q.1 q.2.1 q.2.2.1}
    with hSset
  have hc : Continuous fun q : ℝ × ℝ × M × JetModel E 0 s (2 * p) => flow X q.1 q.2.2.1 :=
    (contMDiff_flow X).continuous.comp (continuous_fst.prodMk continuous_snd.snd.fst)
  set O := (fun q : ℝ × ℝ × M × JetModel E 0 s (2 * p) => flow X q.1 q.2.2.1) ⁻¹'
    jetBase (I := I) 0 s (2 * p) y₀ with hO
  have hOo : IsOpen O := (isOpen_jetBase (2 * p) y₀).preimage hc
  have hq₀O : q₀ ∈ O := mem_jetBase_self (2 * p) y₀
  -- smooth pieces
  have hσf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 s (2 * p)))))
      𝓘(ℝ, ℝ) ∞ (fun q : ℝ × ℝ × M × JetModel E 0 s (2 * p) => q.1) := contMDiff_fst
  have htf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 s (2 * p)))))
      𝓘(ℝ, ℝ) ∞ (fun q : ℝ × ℝ × M × JetModel E 0 s (2 * p) => q.2.1) :=
    contMDiff_fst.comp contMDiff_snd
  have hxf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 s (2 * p)))))
      I ∞ (fun q : ℝ × ℝ × M × JetModel E 0 s (2 * p) => q.2.2.1) :=
    contMDiff_fst.comp (contMDiff_snd.comp contMDiff_snd)
  have hff : ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 s (2 * p)))))
      I ∞ (fun q : ℝ × ℝ × M × JetModel E 0 s (2 * p) => flow X q.1 q.2.2.1) :=
    (contMDiff_flow X).comp (hσf.prodMk hxf)
  have hw := contMDiffAt_natW X g x₀ y₀ hσ₀ hx₀ (mem_jetBase_self (2 * p) y₀)
  -- the nonlinearity read at `y₀`
  have hΨ : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 s (2 * p)))))
      (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 s (2 * p)))) ∞
      (fun q : ℝ × ℝ × M × JetModel E 0 s (2 * p) =>
        (q.2.1, flow X q.1 q.2.2.1, natW X g x₀ y₀ q)) q₀ :=
    (htf q₀).prodMk ((hff q₀).prodMk hw)
  have hmaps : MapsTo (fun q : ℝ × ℝ × M × JetModel E 0 s (2 * p) =>
        (q.2.1, flow X q.1 q.2.2.1, natW X g x₀ y₀ q)) (Sset ∩ O)
      (localDom 0 s (2 * p) D.T₀ D.dom y₀) := by
    rintro q ⟨⟨⟨ht, -⟩, -, hd⟩, hqO⟩
    refine ⟨⟨ht, hqO⟩, ?_⟩
    change jetOfModel (I := I) 0 s (2 * p) y₀ (flow X q.1 q.2.2.1) (natW X g x₀ y₀ q) ∈ _
    rw [jetOfModel_natW X g hqO]
    exact hd
  have hq₀D : (q₀.2.1, flow X q₀.1 q₀.2.2.1, natW X g x₀ y₀ q₀) ∈
      localDom 0 s (2 * p) D.T₀ D.dom y₀ :=
    hmaps ⟨⟨⟨ht₀, hx₀⟩, hσ₀, hd₀⟩, hq₀O⟩
  have hv : ContMDiffWithinAt
      (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 s (2 * p)))))
      𝓘(ℝ, TensorRSModel 0 s ℝ E) ∞
      (fun q : ℝ × ℝ × M × JetModel E 0 s (2 * p) =>
        localRep 0 s (2 * p) D.F y₀ (q.2.1, flow X q.1 q.2.2.1, natW X g x₀ y₀ q)) Sset q₀ := by
    have h := (D.smooth y₀ _ hq₀D).comp q₀ hΨ.contMDiffWithinAt hmaps
    exact h.mono_of_mem_nhdsWithin (inter_mem_nhdsWithin _ (hOo.mem_nhds hq₀O))
  -- parallel transport back
  have hread := contMDiffWithinAt_pt_read X g x₀ y₀
    (fun q : ℝ × ℝ × M × JetModel E 0 s (2 * p) => q.1)
    (fun q : ℝ × ℝ × M × JetModel E 0 s (2 * p) => q.2.2.1) _ (hσf q₀) (hxf q₀) hv hx₀.1
    (mem_jetBase_self (2 * p) y₀).1
  refine hread.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [inter_mem_nhdsWithin Sset (hOo.mem_nhds hq₀O)] with q hq
    simp only [natF, localRep]
    rw [jetOfModel_natW X g hq.2, (trivAt I M 0 s y₀).symmL_continuousLinearMapAt hq.2.1]
  · simp only [natF, localRep]
    rw [jetOfModel_natW X g hq₀O, (trivAt I M 0 s y₀).symmL_continuousLinearMapAt hq₀O.1]

/-- **The transported nonlinearity** `F_σ(t, x, ζ) = P_σ(x)⁻¹ F(t, φ_σ x, Υ_σ(x) ζ)` as a smooth fibre
map with parameter `σ` (paper: `lem:flows` (d)). -/
def natFibreMap : FibreMap I M ℝ (EquationData.jetRanks s p) s where
  T₀ := D.T₀
  dom := natDom X g D
  F := natF X g D
  dom_relOpen := natDom_relOpen X g D
  smooth := natF_smooth X g D

theorem natFibreMap_F (σ t : ℝ) (x : M) (ζ : CovJetFiber I 0 s (2 * p) x) :
    (natFibreMap X g D).F σ t x ζ =
      (pt X g s σ x).symm (D.F t (flow X σ x) (natΥ X g s (2 * p) σ x ζ)) := rfl

theorem natFibreMap_T₀ : (natFibreMap X g D).T₀ = D.T₀ := rfl

theorem fibCast_symm_F_jetCast {x y : M} (h : x = y) (t : ℝ) (ζ : CovJetFiber I 0 s (2 * p) x) :
    (fibCast h).symm (D.F t y (jetCast h ζ)) = D.F t x ζ := by
  subst h
  rfl

/-- **`F_0 = F`**. -/
theorem natFibreMap_F_zero (t : ℝ) (x : M) (ζ : CovJetFiber I 0 s (2 * p) x) :
    (natFibreMap X g D).F 0 t x ζ = D.toFibreMap.F 0 t x ζ := by
  rw [natFibreMap_F, natΥ_zero, pt_zero_symm, EquationData.toFibreMap_F]
  exact fibCast_symm_F_jetCast D (flow_zero X x).symm t ζ

theorem jetCast_mem_dom {x y : M} (h : x = y) (t : ℝ) (ζ : CovJetFiber I 0 s (2 * p) x) :
    jetCast h ζ ∈ D.dom t y ↔ ζ ∈ D.dom t x := by
  subst h
  rfl

/-- **`𝒟_0 = 𝒟`**. -/
theorem natFibreMap_dom_zero (t : ℝ) (x : M) :
    (natFibreMap X g D).dom 0 t x = D.toFibreMap.dom 0 t x := by
  ext ζ
  change (|(0 : ℝ)| < natδ X g s (2 * p) (I := I) ∧ natΥ X g s (2 * p) 0 x ζ ∈
    D.dom t (flow X 0 x)) ↔ ζ ∈ D.dom t x
  rw [natΥ_zero, jetCast_mem_dom D (flow_zero X x).symm t ζ, abs_zero]
  exact and_iff_right (natδ_pos X g s (2 * p))

/-- The jets of the transported section are taken to the jets of the original one. -/
theorem natΥ_covJet_hpull {σ : ℝ} (hσ : |σ| < natδ X g s (2 * p) (I := I)) (x : M)
    (u : SmoothCcTensor g 0 s) :
    natΥ X g s (2 * p) σ x (covJet g 0 s (2 * p) (hpull X g s σ u) x) =
      covJet g 0 s (2 * p) u (flow X σ x) := by
  rw [natΥ_covJet X g s (2 * p) hσ, hpull_hpull, neg_add_cancel, hpull_zero]

/-- The jets of `Π_σ u` lie in the domain of `F_σ` when those of `u` lie in `𝒟`. -/
theorem covJet_hpull_mem_natDom {σ : ℝ} (hσ : |σ| < natδ X g s (2 * p) (I := I)) {t : ℝ}
    {u : SmoothCcTensor g 0 s} (hu : ∀ x, covJet g 0 s (2 * p) u x ∈ D.dom t x) (x : M) :
    covJet g 0 s (2 * p) (hpull X g s σ u) x ∈ (natFibreMap X g D).dom σ t x := by
  refine ⟨hσ, ?_⟩
  rw [natΥ_covJet_hpull X g hσ]
  exact hu _

/-- **Naturality** (`lem:flows` (d)): `Π_σ (F[u](t)) = F_σ[Π_σ u](t)` for a smooth family `u` with
jets in `𝒟`. -/
theorem hpull_nonlinFamily {T : ℝ} (hT : T ≤ D.T₀) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u)
    (hdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (u t) x ∈ D.dom t x)
    {σ : ℝ} (hσ : |σ| < natδ X g s (2 * p) (I := I)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    hpull X g s σ (D.nonlinFamily u t) =
      (natFibreMap X g D).apply σ (EquationData.jetFamily (p := p) (fun τ => hpull X g s σ (u τ)))
        t := by
  have hV : ∀ k : Fin (2 * p + 1), JointlySmoothOn g 0 (EquationData.jetRanks s p k) (Icc 0 T)
      (EquationData.jetFamily (p := p) u k) := fun k =>
    Vendor.covGrad_iter_joint (I := I) (M := M) g 0 s k u (Icc 0 T) hu
  obtain ⟨hex, -⟩ := D.toFibreMap.jointlySmoothOn_fibreApply 0 hT hV
    (fun t ht x => by rw [EquationData.valAt_jetFamily]; exact hdom t ht x)
  have h0 := FibreMap.apply_toSection D.toFibreMap 0 (EquationData.jetFamily u) t (hex t ht)
  have hpt : ∀ x : M, (hpull X g s σ (D.nonlinFamily u t)).toSection x =
      (natFibreMap X g D).F σ t x
        (FibreMap.valAt (fun c => EquationData.jetFamily (p := p)
          (fun τ => hpull X g s σ (u τ)) c t) x) := by
    intro x
    rw [EquationData.valAt_jetFamily, natFibreMap_F, natΥ_covJet_hpull X g hσ, hpull_toSection]
    change (pt X g s σ x).symm ((D.nonlinFamily u t).toSection (flow X σ x)) = _
    rw [EquationData.nonlinFamily, h0, EquationData.valAt_jetFamily, EquationData.toFibreMap_F]
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [FibreMap.apply_toSection _ σ _ t ⟨_, hpt⟩ x]
  exact hpt x

end Natural

end HFlow

end ShortTime
