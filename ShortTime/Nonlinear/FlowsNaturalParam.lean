import ShortTime.Nonlinear.FlowsNatural

/-!
# Naturality of the horizontal pullback for parametrized fibre maps

Paper: Lemma `lem:flows` (d), with an extra parameter.

For a smooth fibre map `Φ` on covariant `2p`-jets with parameter `λ ∈ Λ` and the horizontal pullback
`Π_σ` along the flow of `X`, the transported map

  `Φ_X(λ, σ)(t, x, ζ) = P_σ(x)⁻¹ Φ(λ, t, φ_σ x, Υ_σ(x) ζ)`,     `|σ| < δ`,

is a smooth fibre map with parameter `(λ, σ)` (`natParam`), with `Φ_X(λ, 0) = Φ(λ)`
(`natParam_F_zero`, `natParam_dom_zero`) and

  `Π_σ (Φ[λ, j u](t)) = Φ_X[(λ, σ), j (Π_σ u)](t)`          (`hpull_fibreApply`).

This generalizes `natFibreMap` (the case `Φ = D.toFibreMap`, whose parameter is a dummy). It allows
iterating the construction over several vector fields (`ShortTime.Nonlinear.FlowsNaturalParamIter`).

We also define the reparametrization `FibreMap.reparam` of a fibre map along a continuous linear map
of parameter spaces.
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-! ### Reparametrization of a fibre map -/

namespace FibreMap

variable {ι : Type*} [Fintype ι] {b : ι → ℕ} {b' : ℕ}
variable {Λ Λ' : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ]
  [NormedAddCommGroup Λ'] [NormedSpace ℝ Λ']

/-- The fibre map `Φ(L λ')` with parameter `λ' ∈ Λ'`, for a continuous linear map `L : Λ' → Λ`. -/
def reparam (Φ : FibreMap I M Λ b b') (L : Λ' →L[ℝ] Λ) : FibreMap I M Λ' b b' where
  T₀ := Φ.T₀
  dom l := Φ.dom (L l)
  F l := Φ.F (L l)
  dom_relOpen x₀ := by
    obtain ⟨U, hU, hdom⟩ := Φ.dom_relOpen x₀
    refine ⟨(fun q : Λ' × ℝ × M × ProdModel E b => ((L q.1, q.2) : Λ × ℝ × M × ProdModel E b))
      ⁻¹' U, hU.preimage ((L.continuous.comp continuous_fst).prodMk continuous_snd), ?_⟩
    ext q
    exact Iff.of_eq (congrArg (fun S => ((L q.1, q.2) : Λ × ℝ × M × ProdModel E b) ∈ S) hdom)
  smooth x₀ := by
    have hψ : ContMDiff (𝓘(ℝ, Λ').prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, ProdModel E b))))
        (𝓘(ℝ, Λ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, ProdModel E b)))) ∞
        (fun q : Λ' × ℝ × M × ProdModel E b => ((L q.1, q.2) : Λ × ℝ × M × ProdModel E b)) :=
      (L.contDiff.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
    exact (Φ.smooth x₀).comp hψ.contMDiffOn (fun q hq => hq)

@[simp] theorem reparam_T₀ (Φ : FibreMap I M Λ b b') (L : Λ' →L[ℝ] Λ) : (Φ.reparam L).T₀ = Φ.T₀ :=
  rfl

@[simp] theorem reparam_F (Φ : FibreMap I M Λ b b') (L : Λ' →L[ℝ] Λ) (l : Λ') :
    (Φ.reparam L).F l = Φ.F (L l) := rfl

@[simp] theorem reparam_dom (Φ : FibreMap I M Λ b b') (L : Λ' →L[ℝ] Λ) (l : Λ') :
    (Φ.reparam L).dom l = Φ.dom (L l) := rfl

theorem reparam_apply {g : SmoothRiemannianMetric I M} (Φ : FibreMap I M Λ b b') (L : Λ' →L[ℝ] Λ)
    (l : Λ') (V : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)) (t : ℝ) :
    (Φ.reparam L).apply l V t = Φ.apply (L l) V t := rfl

end FibreMap

namespace HFlow

variable [CompleteSpace E]
variable (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
variable (g : SmoothRiemannianMetric I M)

section Param

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ]
variable {s p : ℕ} (Φ : FibreMap I M Λ (EquationData.jetRanks s p) s)

/-- `Φ_X(λ, σ)(t, x, ζ) = P_σ(x)⁻¹ Φ(λ, t, φ_σ x, Υ_σ(x) ζ)`. -/
def natParamF (l : Λ × ℝ) (t : ℝ) (x : M) (ζ : ProdFiber I (EquationData.jetRanks s p) x) :
    TensorRSSpace 0 s I x :=
  (pt X g s l.2 x).symm (Φ.F l.1 t (flow X l.2 x) (natΥ X g s (2 * p) l.2 x ζ))

/-- The domain of `Φ_X(λ, σ)`: `|σ| < δ` and `Υ_σ(x) ζ ∈ dom Φ(λ)`. -/
def natParamDom (l : Λ × ℝ) (t : ℝ) (x : M) : Set (ProdFiber I (EquationData.jetRanks s p) x) :=
  {ζ | |l.2| < natδ X g s (2 * p) (I := I) ∧
    natΥ X g s (2 * p) l.2 x ζ ∈ Φ.dom l.1 t (flow X l.2 x)}

/-- The jet transport read in the trivializations at `x₀` and `y₀`, as a function of
`((λ, σ), t, x, z)`. -/
def natWP (x₀ y₀ : M) (q : (Λ × ℝ) × ℝ × M × ProdModel E (EquationData.jetRanks s p)) :
    ProdModel E (EquationData.jetRanks s p) :=
  natW X g (s := s) (p := p) x₀ y₀ (q.1.2, q.2)

theorem prodOfModel_natWP {x₀ y₀ : M}
    {q : (Λ × ℝ) × ℝ × M × ProdModel E (EquationData.jetRanks s p)}
    (hy : flow X q.1.2 q.2.2.1 ∈ jetBase (I := I) 0 s (2 * p) y₀) :
    prodOfModel (EquationData.jetRanks s p) y₀ (flow X q.1.2 q.2.2.1) (natWP X g x₀ y₀ q) =
      natΥ X g s (2 * p) q.1.2 q.2.2.1
        (prodOfModel (EquationData.jetRanks s p) x₀ q.2.2.1 q.2.2.2) :=
  jetOfModel_natW X g (q := (q.1.2, q.2)) hy

theorem contMDiffAt_natWP (x₀ y₀ : M)
    {q₀ : (Λ × ℝ) × ℝ × M × ProdModel E (EquationData.jetRanks s p)}
    (hσ : |q₀.1.2| < natδ X g s (2 * p) (I := I))
    (hx : q₀.2.2.1 ∈ jetBase (I := I) 0 s (2 * p) x₀)
    (hy : flow X q₀.1.2 q₀.2.2.1 ∈ jetBase (I := I) 0 s (2 * p) y₀) :
    ContMDiffAt (𝓘(ℝ, Λ × ℝ).prod (𝓘(ℝ, ℝ).prod
        (I.prod 𝓘(ℝ, ProdModel E (EquationData.jetRanks s p)))))
      𝓘(ℝ, ProdModel E (EquationData.jetRanks s p)) ∞ (natWP X g x₀ y₀) q₀ := by
  have hpr : ContMDiff (𝓘(ℝ, Λ × ℝ).prod (𝓘(ℝ, ℝ).prod
        (I.prod 𝓘(ℝ, ProdModel E (EquationData.jetRanks s p)))))
      (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, ProdModel E (EquationData.jetRanks s p))))) ∞
      (fun q : (Λ × ℝ) × ℝ × M × ProdModel E (EquationData.jetRanks s p) => (q.1.2, q.2)) :=
    (contDiff_snd.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
  have h := contMDiffAt_natW X g x₀ y₀ (q₀ := (q₀.1.2, q₀.2)) hσ hx hy
  exact h.comp q₀ hpr.contMDiffAt

/-- The domain of `Φ_X` is relatively open. -/
theorem natParam_dom_relOpen (x₀ : M) :
    ∃ U : Set ((Λ × ℝ) × ℝ × M × ProdModel E (EquationData.jetRanks s p)), IsOpen U ∧
      {q ∈ prodSlab (I := I) (Λ × ℝ) (EquationData.jetRanks s p) s Φ.T₀ x₀ |
          prodOfModel (EquationData.jetRanks s p) x₀ q.2.2.1 q.2.2.2 ∈
            natParamDom X g Φ q.1 q.2.1 q.2.2.1} =
        U ∩ prodSlab (I := I) (Λ × ℝ) (EquationData.jetRanks s p) s Φ.T₀ x₀ := by
  set A := {q ∈ prodSlab (I := I) (Λ × ℝ) (EquationData.jetRanks s p) s Φ.T₀ x₀ |
    prodOfModel (EquationData.jetRanks s p) x₀ q.2.2.1 q.2.2.2 ∈
      natParamDom X g Φ q.1 q.2.1 q.2.2.1} with hA
  have hloc : ∀ q₀ ∈ A,
      ∃ V : Set ((Λ × ℝ) × ℝ × M × ProdModel E (EquationData.jetRanks s p)), IsOpen V ∧ q₀ ∈ V ∧
        V ∩ prodSlab (I := I) (Λ × ℝ) (EquationData.jetRanks s p) s Φ.T₀ x₀ ⊆ A := by
    intro q₀ hq₀
    obtain ⟨⟨ht₀, hx₀⟩, hσ₀, hd₀⟩ := hq₀
    set y₀ := flow X q₀.1.2 q₀.2.2.1 with hy₀
    obtain ⟨UD, hUDo, hUD⟩ := Φ.dom_relOpen y₀
    have hc : Continuous fun q : (Λ × ℝ) × ℝ × M × ProdModel E (EquationData.jetRanks s p) =>
        flow X q.1.2 q.2.2.1 :=
      (contMDiff_flow X).continuous.comp (continuous_fst.snd.prodMk continuous_snd.snd.fst)
    set O := {q : (Λ × ℝ) × ℝ × M × ProdModel E (EquationData.jetRanks s p) |
      |q.1.2| < natδ X g s (2 * p) (I := I) ∧ q.2.2.1 ∈ jetBase (I := I) 0 s (2 * p) x₀ ∧
        flow X q.1.2 q.2.2.1 ∈ jetBase (I := I) 0 s (2 * p) y₀} with hO
    have hOo : IsOpen O :=
      (isOpen_lt (continuous_abs.comp continuous_fst.snd) continuous_const).inter
        (((isOpen_jetBase (2 * p) x₀).preimage continuous_snd.snd.fst).inter
          ((isOpen_jetBase (2 * p) y₀).preimage hc))
    let Ψ : (Λ × ℝ) × ℝ × M × ProdModel E (EquationData.jetRanks s p) →
        Λ × ℝ × M × ProdModel E (EquationData.jetRanks s p) :=
      fun q => (q.1.1, q.2.1, flow X q.1.2 q.2.2.1, natWP X g x₀ y₀ q)
    have hΨ : ContinuousOn Ψ O :=
      continuous_fst.fst.continuousOn.prodMk (continuous_snd.fst.continuousOn.prodMk
        (hc.continuousOn.prodMk (fun q hq =>
          (contMDiffAt_natWP X g x₀ y₀ hq.1 hq.2.1 hq.2.2).continuousAt.continuousWithinAt)))
    refine ⟨O ∩ Ψ ⁻¹' UD, hΨ.isOpen_inter_preimage hOo hUDo,
      ⟨⟨hσ₀, hx₀, mem_jetBase_self (2 * p) y₀⟩, ?_⟩, ?_⟩
    · have hmem : Ψ q₀ ∈ {q ∈ prodSlab (I := I) Λ (EquationData.jetRanks s p) s Φ.T₀ y₀ |
          prodOfModel (EquationData.jetRanks s p) y₀ q.2.2.1 q.2.2.2 ∈
            Φ.dom q.1 q.2.1 q.2.2.1} := by
        refine ⟨⟨ht₀, mem_jetBase_self (2 * p) y₀⟩, ?_⟩
        change prodOfModel (EquationData.jetRanks s p) y₀ (flow X q₀.1.2 q₀.2.2.1)
          (natWP X g x₀ y₀ q₀) ∈ Φ.dom q₀.1.1 q₀.2.1 (flow X q₀.1.2 q₀.2.2.1)
        rw [prodOfModel_natWP X g (mem_jetBase_self (2 * p) y₀)]
        exact hd₀
      rw [hUD] at hmem
      exact hmem.1
    · rintro q ⟨⟨hqO, hqU⟩, hqs⟩
      refine ⟨hqs, hqO.1, ?_⟩
      have hmem : Ψ q ∈ {q ∈ prodSlab (I := I) Λ (EquationData.jetRanks s p) s Φ.T₀ y₀ |
          prodOfModel (EquationData.jetRanks s p) y₀ q.2.2.1 q.2.2.2 ∈
            Φ.dom q.1 q.2.1 q.2.2.1} := by
        rw [hUD]
        exact ⟨hqU, hqs.1, hqO.2.2⟩
      have h2 := hmem.2
      change prodOfModel (EquationData.jetRanks s p) y₀ (flow X q.1.2 q.2.2.1)
        (natWP X g x₀ y₀ q) ∈ Φ.dom q.1.1 q.2.1 (flow X q.1.2 q.2.2.1) at h2
      rw [prodOfModel_natWP X g hqO.2.2] at h2
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

/-- `Φ_X` is smooth on its domain, read in the trivializations at `x₀`. -/
theorem natParam_smooth (x₀ : M) :
    ContMDiffOn (𝓘(ℝ, Λ × ℝ).prod (𝓘(ℝ, ℝ).prod
        (I.prod 𝓘(ℝ, ProdModel E (EquationData.jetRanks s p)))))
      𝓘(ℝ, TensorRSModel 0 s ℝ E) ∞
      (fun q : (Λ × ℝ) × ℝ × M × ProdModel E (EquationData.jetRanks s p) =>
        (trivAt I M 0 s x₀).continuousLinearMapAt ℝ q.2.2.1
          (natParamF X g Φ q.1 q.2.1 q.2.2.1
            (prodOfModel (EquationData.jetRanks s p) x₀ q.2.2.1 q.2.2.2)))
      {q ∈ prodSlab (I := I) (Λ × ℝ) (EquationData.jetRanks s p) s Φ.T₀ x₀ |
          prodOfModel (EquationData.jetRanks s p) x₀ q.2.2.1 q.2.2.2 ∈
            natParamDom X g Φ q.1 q.2.1 q.2.2.1} := by
  intro q₀ hq₀
  obtain ⟨⟨ht₀, hx₀⟩, hσ₀, hd₀⟩ := hq₀
  set y₀ := flow X q₀.1.2 q₀.2.2.1 with hy₀
  set Sset := {q ∈ prodSlab (I := I) (Λ × ℝ) (EquationData.jetRanks s p) s Φ.T₀ x₀ |
    prodOfModel (EquationData.jetRanks s p) x₀ q.2.2.1 q.2.2.2 ∈
      natParamDom X g Φ q.1 q.2.1 q.2.2.1} with hSset
  have hc : Continuous fun q : (Λ × ℝ) × ℝ × M × ProdModel E (EquationData.jetRanks s p) =>
      flow X q.1.2 q.2.2.1 :=
    (contMDiff_flow X).continuous.comp (continuous_fst.snd.prodMk continuous_snd.snd.fst)
  set O := (fun q : (Λ × ℝ) × ℝ × M × ProdModel E (EquationData.jetRanks s p) =>
    flow X q.1.2 q.2.2.1) ⁻¹' jetBase (I := I) 0 s (2 * p) y₀ with hO
  have hOo : IsOpen O := (isOpen_jetBase (2 * p) y₀).preimage hc
  have hq₀O : q₀ ∈ O := mem_jetBase_self (2 * p) y₀
  -- smooth pieces
  have hlf : ContMDiff (𝓘(ℝ, Λ × ℝ).prod (𝓘(ℝ, ℝ).prod
        (I.prod 𝓘(ℝ, ProdModel E (EquationData.jetRanks s p))))) 𝓘(ℝ, Λ) ∞
      (fun q : (Λ × ℝ) × ℝ × M × ProdModel E (EquationData.jetRanks s p) => q.1.1) :=
    contDiff_fst.contMDiff.comp contMDiff_fst
  have hσf : ContMDiff (𝓘(ℝ, Λ × ℝ).prod (𝓘(ℝ, ℝ).prod
        (I.prod 𝓘(ℝ, ProdModel E (EquationData.jetRanks s p))))) 𝓘(ℝ, ℝ) ∞
      (fun q : (Λ × ℝ) × ℝ × M × ProdModel E (EquationData.jetRanks s p) => q.1.2) :=
    contDiff_snd.contMDiff.comp contMDiff_fst
  have htf : ContMDiff (𝓘(ℝ, Λ × ℝ).prod (𝓘(ℝ, ℝ).prod
        (I.prod 𝓘(ℝ, ProdModel E (EquationData.jetRanks s p))))) 𝓘(ℝ, ℝ) ∞
      (fun q : (Λ × ℝ) × ℝ × M × ProdModel E (EquationData.jetRanks s p) => q.2.1) :=
    contMDiff_fst.comp contMDiff_snd
  have hxf : ContMDiff (𝓘(ℝ, Λ × ℝ).prod (𝓘(ℝ, ℝ).prod
        (I.prod 𝓘(ℝ, ProdModel E (EquationData.jetRanks s p))))) I ∞
      (fun q : (Λ × ℝ) × ℝ × M × ProdModel E (EquationData.jetRanks s p) => q.2.2.1) :=
    contMDiff_fst.comp (contMDiff_snd.comp contMDiff_snd)
  have hff : ContMDiff (𝓘(ℝ, Λ × ℝ).prod (𝓘(ℝ, ℝ).prod
        (I.prod 𝓘(ℝ, ProdModel E (EquationData.jetRanks s p))))) I ∞
      (fun q : (Λ × ℝ) × ℝ × M × ProdModel E (EquationData.jetRanks s p) =>
        flow X q.1.2 q.2.2.1) :=
    (contMDiff_flow X).comp (hσf.prodMk hxf)
  have hw := contMDiffAt_natWP X g x₀ y₀ hσ₀ hx₀ (mem_jetBase_self (2 * p) y₀)
  -- the map `Φ` read at `y₀`
  have hΨ : ContMDiffAt (𝓘(ℝ, Λ × ℝ).prod (𝓘(ℝ, ℝ).prod
        (I.prod 𝓘(ℝ, ProdModel E (EquationData.jetRanks s p)))))
      (𝓘(ℝ, Λ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, ProdModel E (EquationData.jetRanks s p))))) ∞
      (fun q : (Λ × ℝ) × ℝ × M × ProdModel E (EquationData.jetRanks s p) =>
        (q.1.1, q.2.1, flow X q.1.2 q.2.2.1, natWP X g x₀ y₀ q)) q₀ :=
    (hlf q₀).prodMk ((htf q₀).prodMk ((hff q₀).prodMk hw))
  have hmaps : MapsTo (fun q : (Λ × ℝ) × ℝ × M × ProdModel E (EquationData.jetRanks s p) =>
        (q.1.1, q.2.1, flow X q.1.2 q.2.2.1, natWP X g x₀ y₀ q)) (Sset ∩ O)
      {q ∈ prodSlab (I := I) Λ (EquationData.jetRanks s p) s Φ.T₀ y₀ |
          prodOfModel (EquationData.jetRanks s p) y₀ q.2.2.1 q.2.2.2 ∈
            Φ.dom q.1 q.2.1 q.2.2.1} := by
    rintro q ⟨⟨⟨ht, -⟩, -, hd⟩, hqO⟩
    refine ⟨⟨ht, hqO⟩, ?_⟩
    change prodOfModel (EquationData.jetRanks s p) y₀ (flow X q.1.2 q.2.2.1)
      (natWP X g x₀ y₀ q) ∈ Φ.dom q.1.1 q.2.1 (flow X q.1.2 q.2.2.1)
    rw [prodOfModel_natWP X g hqO]
    exact hd
  have hq₀D := hmaps ⟨⟨⟨ht₀, hx₀⟩, hσ₀, hd₀⟩, hq₀O⟩
  have hv : ContMDiffWithinAt (𝓘(ℝ, Λ × ℝ).prod (𝓘(ℝ, ℝ).prod
        (I.prod 𝓘(ℝ, ProdModel E (EquationData.jetRanks s p)))))
      𝓘(ℝ, TensorRSModel 0 s ℝ E) ∞
      (fun q : (Λ × ℝ) × ℝ × M × ProdModel E (EquationData.jetRanks s p) =>
        (trivAt I M 0 s y₀).continuousLinearMapAt ℝ (flow X q.1.2 q.2.2.1)
          (Φ.F q.1.1 q.2.1 (flow X q.1.2 q.2.2.1)
            (prodOfModel (EquationData.jetRanks s p) y₀ (flow X q.1.2 q.2.2.1)
              (natWP X g x₀ y₀ q)))) Sset q₀ := by
    have h := (Φ.smooth y₀ _ hq₀D).comp q₀ hΨ.contMDiffWithinAt hmaps
    exact h.mono_of_mem_nhdsWithin (inter_mem_nhdsWithin _ (hOo.mem_nhds hq₀O))
  -- parallel transport back
  have hread := contMDiffWithinAt_pt_read X g x₀ y₀
    (fun q : (Λ × ℝ) × ℝ × M × ProdModel E (EquationData.jetRanks s p) => q.1.2)
    (fun q : (Λ × ℝ) × ℝ × M × ProdModel E (EquationData.jetRanks s p) => q.2.2.1) _
    (hσf q₀) (hxf q₀) hv hx₀.1 (mem_jetBase_self (2 * p) y₀).1
  refine hread.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [inter_mem_nhdsWithin Sset (hOo.mem_nhds hq₀O)] with q hq
    simp only [natParamF]
    rw [prodOfModel_natWP X g hq.2, (trivAt I M 0 s y₀).symmL_continuousLinearMapAt hq.2.1]
  · simp only [natParamF]
    rw [prodOfModel_natWP X g hq₀O, (trivAt I M 0 s y₀).symmL_continuousLinearMapAt hq₀O.1]

/-- **The transported fibre map** `Φ_X(λ, σ)(t, x, ζ) = P_σ(x)⁻¹ Φ(λ, t, φ_σ x, Υ_σ(x) ζ)`, a smooth
fibre map with parameter `(λ, σ)` (paper: `lem:flows` (d)). -/
def natParam : FibreMap I M (Λ × ℝ) (EquationData.jetRanks s p) s where
  T₀ := Φ.T₀
  dom := natParamDom X g Φ
  F := natParamF X g Φ
  dom_relOpen := natParam_dom_relOpen X g Φ
  smooth := natParam_smooth X g Φ

theorem natParam_F (l : Λ × ℝ) (t : ℝ) (x : M) (ζ : ProdFiber I (EquationData.jetRanks s p) x) :
    (natParam X g Φ).F l t x ζ =
      (pt X g s l.2 x).symm (Φ.F l.1 t (flow X l.2 x) (natΥ X g s (2 * p) l.2 x ζ)) := rfl

theorem natParam_dom (l : Λ × ℝ) (t : ℝ) (x : M) :
    (natParam X g Φ).dom l t x = natParamDom X g Φ l t x := rfl

@[simp] theorem natParam_T₀ : (natParam X g Φ).T₀ = Φ.T₀ := rfl

theorem fibCast_symm_FM_jetCast (l : Λ) {x y : M} (h : x = y) (t : ℝ)
    (ζ : CovJetFiber I 0 s (2 * p) x) :
    (fibCast h).symm (Φ.F l t y (jetCast h ζ)) = Φ.F l t x ζ := by
  subst h
  rfl

theorem jetCast_mem_FMdom (l : Λ) {x y : M} (h : x = y) (t : ℝ)
    (ζ : CovJetFiber I 0 s (2 * p) x) :
    jetCast h ζ ∈ Φ.dom l t y ↔ ζ ∈ Φ.dom l t x := by
  subst h
  rfl

/-- **`Φ_X(λ, 0) = Φ(λ)`**. -/
theorem natParam_F_zero (l : Λ) (t : ℝ) (x : M) (ζ : ProdFiber I (EquationData.jetRanks s p) x) :
    (natParam X g Φ).F (l, 0) t x ζ = Φ.F l t x ζ := by
  rw [natParam_F]
  change (pt X g s 0 x).symm (Φ.F l t (flow X 0 x) (natΥ X g s (2 * p) 0 x ζ)) = _
  rw [natΥ_zero, pt_zero_symm]
  exact fibCast_symm_FM_jetCast Φ l (flow_zero X x).symm t ζ

/-- **`dom Φ_X(λ, 0) = dom Φ(λ)`**. -/
theorem natParam_dom_zero (l : Λ) (t : ℝ) (x : M) :
    (natParam X g Φ).dom (l, 0) t x = Φ.dom l t x := by
  ext ζ
  change (|(0 : ℝ)| < natδ X g s (2 * p) (I := I) ∧ natΥ X g s (2 * p) 0 x ζ ∈
    Φ.dom l t (flow X 0 x)) ↔ ζ ∈ Φ.dom l t x
  rw [natΥ_zero, jetCast_mem_FMdom Φ l (flow_zero X x).symm t ζ, abs_zero]
  exact and_iff_right (natδ_pos X g s (2 * p))

/-- The jets of `Π_σ u` lie in the domain of `Φ_X(λ, σ)` when those of `u` lie in that of
`Φ(λ)`. -/
theorem covJet_hpull_mem_natParam_dom {l : Λ} {σ : ℝ} (hσ : |σ| < natδ X g s (2 * p) (I := I))
    {t : ℝ} {u : SmoothCcTensor g 0 s} (hu : ∀ x, covJet g 0 s (2 * p) u x ∈ Φ.dom l t x)
    (x : M) :
    covJet g 0 s (2 * p) (hpull X g s σ u) x ∈ (natParam X g Φ).dom (l, σ) t x := by
  refine ⟨hσ, ?_⟩
  change natΥ X g s (2 * p) σ x (covJet g 0 s (2 * p) (hpull X g s σ u) x) ∈
    Φ.dom l t (flow X σ x)
  rw [natΥ_covJet_hpull X g hσ]
  exact hu _

/-- **Naturality** (`lem:flows` (d), with a parameter):
`Π_σ (Φ[λ, j u](t)) = Φ_X[(λ, σ), j(Π_σ u)](t)` for a jointly smooth family `u` with jets in the domain of `Φ(λ)`. -/
theorem hpull_fibreApply {l : Λ} {T : ℝ} (hT : T ≤ Φ.T₀) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u)
    (hdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (u t) x ∈ Φ.dom l t x)
    {σ : ℝ} (hσ : |σ| < natδ X g s (2 * p) (I := I)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    hpull X g s σ (Φ.apply l (EquationData.jetFamily (p := p) u) t) =
      (natParam X g Φ).apply (l, σ)
        (EquationData.jetFamily (p := p) (fun τ => hpull X g s σ (u τ))) t := by
  have hV : ∀ k : Fin (2 * p + 1), JointlySmoothOn g 0 (EquationData.jetRanks s p k) (Icc 0 T)
      (EquationData.jetFamily (p := p) u k) := fun k =>
    Vendor.covGrad_iter_joint (I := I) (M := M) g 0 s k u (Icc 0 T) hu
  obtain ⟨hex, -⟩ := Φ.jointlySmoothOn_fibreApply l hT hV
    (fun t ht x => by rw [EquationData.valAt_jetFamily]; exact hdom t ht x)
  have h0 := FibreMap.apply_toSection Φ l (EquationData.jetFamily u) t (hex t ht)
  have hpt : ∀ x : M,
      (hpull X g s σ (Φ.apply l (EquationData.jetFamily (p := p) u) t)).toSection x =
      (natParam X g Φ).F (l, σ) t x
        (FibreMap.valAt (fun c => EquationData.jetFamily (p := p)
          (fun τ => hpull X g s σ (u τ)) c t) x) := by
    intro x
    rw [EquationData.valAt_jetFamily, natParam_F]
    change _ = (pt X g s σ x).symm (Φ.F l t (flow X σ x)
      (natΥ X g s (2 * p) σ x (covJet g 0 s (2 * p) (hpull X g s σ (u t)) x)))
    rw [natΥ_covJet_hpull X g hσ, hpull_toSection]
    change (pt X g s σ x).symm
      ((Φ.apply l (EquationData.jetFamily (p := p) u) t).toSection (flow X σ x)) = _
    rw [h0, EquationData.valAt_jetFamily]
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [FibreMap.apply_toSection _ (l, σ) _ t ⟨_, hpt⟩ x]
  exact hpt x

/-- The transported family stays jointly smooth (for the record: `Φ_X[(λ, σ), j(Π_σ u)]`). -/
theorem jointlySmoothOn_natParam_apply {l : Λ} {T : ℝ} (hT : T ≤ Φ.T₀)
    {u : ℝ → SmoothCcTensor g 0 s} (hu : JointlySmoothOn g 0 s (Icc 0 T) u)
    (hdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (u t) x ∈ Φ.dom l t x)
    {σ : ℝ} (hσ : |σ| < natδ X g s (2 * p) (I := I)) :
    JointlySmoothOn g 0 s (Icc 0 T) ((natParam X g Φ).apply (l, σ)
        (EquationData.jetFamily (p := p) (fun τ => hpull X g s σ (u τ)))) := by
  have hu' := jointlySmoothOn_hpull X g s σ hu
  have hV : ∀ k : Fin (2 * p + 1), JointlySmoothOn g 0 (EquationData.jetRanks s p k) (Icc 0 T)
      (EquationData.jetFamily (p := p) (fun τ => hpull X g s σ (u τ)) k) := fun k =>
    Vendor.covGrad_iter_joint (I := I) (M := M) g 0 s k (fun τ => hpull X g s σ (u τ)) (Icc 0 T)
      hu'
  exact ((natParam X g Φ).jointlySmoothOn_fibreApply (l, σ) hT hV
    (fun t ht x => by
      rw [EquationData.valAt_jetFamily]
      exact covJet_hpull_mem_natParam_dom X g Φ hσ (hdom t ht) x)).2

end Param

end HFlow

end ShortTime
