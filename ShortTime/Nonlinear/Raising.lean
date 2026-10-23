import ShortTime.Nonlinear.Lowering

/-!
# Raising indices: Theorem A reduces to covariant bundles

Paper: Lemma `lem:lowering`, the converse direction.

The inverse `♯ = ♭⁻¹` of lowering is a smooth bundle map (`contMDiff_flatSymm`): read in the
trivializations at `x₀` it is `(flatCoord g r s x₀ y)⁻¹`, smooth by
`contMDiffAt_flatCoord_inverse`. Hence raising indices maps smooth tensor fields to smooth tensor
fields (`sharpCc`), inverse to `flatCc`, and jointly smooth families to jointly smooth families.

A family `u` is a parabolic solution of `D` as soon as `♭u` is one of the lowered equation `D^♭`
(`isParabolicSolution_of_flatData`). So every parabolic solution of `D^♭` with initial datum `♭u₀`
is `♭` of a parabolic solution of `D` with initial datum `u₀`, and Theorem A follows from its
covariant case (`exists_solution_of_covariant`).
-/

noncomputable section

open Bundle Manifold Set Filter
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

variable (g : SmoothRiemannianMetric I M)

/-! ### `♯ = ♭⁻¹` as a smooth bundle map -/

section Sharp

variable [CompleteSpace E]

/-- **Raising indices is smooth**: `♭⁻¹` is a smooth section of `Hom(T⁰_{r+s}, T^r_s)`. -/
theorem contMDiff_flatSymm (r s : ℕ) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (r + s) ℝ E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 (r + s) ℝ E →L[ℝ] TensorRSModel r s ℝ E)
        (E := fun x : M => TensorRSSpace 0 (r + s) I x →L[ℝ] TensorRSSpace r s I x) y
        ((flat g r s y).symm : TensorRSSpace 0 (r + s) I y →L[ℝ] TensorRSSpace r s I y)) := by
  intro x₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  have hx₀ : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) x₀
  refine (contMDiffAt_flatCoord_inverse g r s (x₀ := x₀) (mem_trivAt_baseSet hx₀)
    (mem_trivAt_baseSet hx₀)).congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hx₀] with y hy
  refine ContinuousLinearMap.ext fun z => ?_
  change (trivAt I M r s x₀).continuousLinearMapAt ℝ y
      ((flat g r s y).symm ((trivAt I M 0 (r + s) x₀).symmL ℝ y z)) = _
  rw [trivAt_flat_symm g hy, Trivialization.continuousLinearMapAt_symmL _ (mem_trivAt_baseSet hy)]

/-- `♭⁻¹` with a dummy time parameter, as needed for jointly smooth families. -/
theorem contMDiffOn_flatSymm_param (r s : ℕ) (S : Set ℝ) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 0 (r + s) ℝ E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 0 (r + s) ℝ E →L[ℝ] TensorRSModel r s ℝ E)
        (E := fun x : M => TensorRSSpace 0 (r + s) I x →L[ℝ] TensorRSSpace r s I x) p.1
        ((flat g r s p.1).symm : TensorRSSpace 0 (r + s) I p.1 →L[ℝ] TensorRSSpace r s I p.1))
      ((Set.univ : Set M) ×ˢ S) := fun p _ =>
  ((contMDiff_flatSymm g r s p.1).comp p
    (contMDiffAt_fst (I := I) (J := 𝓘(ℝ, ℝ)) (n := ∞))).contMDiffWithinAt

/-- **Raising all indices** of a tensor field, `♯ : T⁰_{r+s} → T^r_s`. -/
def sharpCc (r s : ℕ) (W : SmoothCcTensor g 0 (r + s)) : SmoothCcTensor g r s where
  toSection :=
    { toFun := fun x => (flat g r s x).symm (W.toSection x)
      contMDiff_toFun := (contMDiff_flatSymm g r s).clm_bundle_apply W.toSection.contMDiff }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

theorem sharpCc_toSection {r s : ℕ} (W : SmoothCcTensor g 0 (r + s)) (x : M) :
    (sharpCc g r s W).toSection x = (flat g r s x).symm (W.toSection x) := rfl

theorem flatCc_sharpCc {r s : ℕ} (W : SmoothCcTensor g 0 (r + s)) :
    flatCc g r s (sharpCc g r s W) = W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [flatCc_toSection, sharpCc_toSection, ContinuousLinearEquiv.apply_symm_apply]

theorem sharpCc_flatCc {r s : ℕ} (T : SmoothCcTensor g r s) : sharpCc g r s (flatCc g r s T) = T :=
  flatCc_injective g (flatCc_sharpCc g _)

/-- Raising preserves jointly smooth families: if `♭u` is jointly smooth, so is `u`. -/
theorem jointlySmoothOn_of_flatCc {r s : ℕ} {S : Set ℝ} {u : ℝ → SmoothCcTensor g r s}
    (hu : JointlySmoothOn g 0 (r + s) S (fun t => flatCc g r s (u t))) :
    JointlySmoothOn g r s S u := by
  have h := ContMDiffOn.clm_bundle_apply (b := Prod.fst) (contMDiffOn_flatSymm_param g r s S) hu
  refine h.congr fun p _ => ?_
  simp only
  rw [flatCc_toSection, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]

end Sharp

/-! ### Parabolic solutions of the lowered equation -/

namespace EquationData

variable [CompleteSpace E] {r s p : ℕ} (D : EquationData I M r s p)

/-- The Legendre condition for `D^♭` at `♭_J ζ` gives the Legendre condition for `D` at `ζ`. -/
theorem legendreAt_of_flatData {t : ℝ} {x : M} {ζ : CovJetFiber I r s (2 * p) x} {lam : ℝ}
    (h : LegendreAt g 0 (r + s) p x ((D.flatData g).principal t x (jetFlat g r s (2 * p) x ζ)) lam) :
    LegendreAt g r s p x (D.principal t x ζ) lam := by
  refine ⟨h.1, fun ξ => ?_⟩
  have hn : fiberInner g 0 ((r + s) + p) x (jetFlatP g (r := r) (s := s) (p := p) x ξ)
      (jetFlatP g (r := r) (s := s) (p := p) x ξ) = fiberInner g r (s + p) x ξ ξ := by
    simp only [jetFlatP, ContinuousLinearEquiv.trans_apply, fiberInner_slotPerm, fiberInner_flat]
  have h2 := h.2 (jetFlatP g (r := r) (s := s) (p := p) x ξ)
  rw [hn, legendreForm_flatData] at h2
  exact h2

/-- Parabolicity of `D^♭` at `♭_J ζ` gives parabolicity of `D` at `ζ`. -/
theorem isParabolicAt_of_flatData {t : ℝ} {x : M} {ζ : CovJetFiber I r s (2 * p) x}
    (h : (D.flatData g).IsParabolicAt g t x (jetFlat g r s (2 * p) x ζ)) :
    D.IsParabolicAt g t x ζ := by
  obtain ⟨hdom, lam, hlam⟩ := h
  exact ⟨(D.mem_flatData_dom g t x ζ).mp hdom, lam, D.legendreAt_of_flatData g hlam⟩

theorem isParabolicAt_flatData_iff {t : ℝ} {x : M} {ζ : CovJetFiber I r s (2 * p) x} :
    (D.flatData g).IsParabolicAt g t x (jetFlat g r s (2 * p) x ζ) ↔ D.IsParabolicAt g t x ζ :=
  ⟨D.isParabolicAt_of_flatData g, D.isParabolicAt_flatData g⟩

/-- **Raising carries parabolic solutions of `D^♭` to parabolic solutions of `D`**
(`lem:lowering`, converse): if `♭u` is a parabolic solution of the lowered equation with initial
datum `♭u₀`, then `u` is a parabolic solution of `D` with initial datum `u₀`. -/
theorem isParabolicSolution_of_flatData {u₀ : SmoothCcTensor g r s} {T : ℝ}
    {u : ℝ → SmoothCcTensor g r s}
    (hv : (D.flatData g).IsParabolicSolution g (flatCc g r s u₀) T (fun t => flatCc g r s (u t))) :
    D.IsParabolicSolution g u₀ T u := by
  obtain ⟨hsol, hpar⟩ := hv
  refine ⟨⟨hsol.pos, hsol.le_T₀, jointlySmoothOn_of_flatCc g hsol.smooth,
    flatCc_injective g hsol.initial, ?_, ?_⟩, ?_⟩
  · intro t ht x
    have h := hsol.jets_mem t ht x
    simp only [covJet_flatCc_eq] at h
    exact (D.mem_flatData_dom g t x _).mp h
  · intro t ht x
    have h1 := hsol.eqn t ht x
    have h2 := ((flatModel g r s x).symm : TensorRSModel 0 (r + s) ℝ E →L[ℝ]
      TensorRSModel r s ℝ E).hasFDerivAt.comp_hasDerivWithinAt t h1
    have hf : ((flatModel g r s x).symm : TensorRSModel 0 (r + s) ℝ E →L[ℝ] TensorRSModel r s ℝ E) ∘
        (fun τ => TensorRSSpace.toModel ((flatCc g r s (u τ)).toSection x)) =
          fun τ => TensorRSSpace.toModel ((u τ).toSection x) := by
      funext τ
      rw [Function.comp_apply, flatCc_toSection, toModel_flat]
      exact (flatModel g r s x).symm_apply_apply _
    have hd : ((flatModel g r s x).symm : TensorRSModel 0 (r + s) ℝ E →L[ℝ] TensorRSModel r s ℝ E)
        (TensorRSSpace.toModel
          ((D.flatData g).F t x (covJet g 0 (r + s) (2 * p) (flatCc g r s (u t)) x))) =
        TensorRSSpace.toModel (D.F t x (covJet g r s (2 * p) (u t) x)) := by
      rw [covJet_flatCc_eq, flatData_F, toModel_flat]
      exact (flatModel g r s x).symm_apply_apply _
    rw [hf, hd] at h2
    exact h2
  · intro t ht x
    have h := hpar t ht x
    simp only [covJet_flatCc_eq] at h
    exact D.isParabolicAt_of_flatData g h

/-- Lowering is a bijection between the parabolic solutions of `D` and those of `D^♭`. -/
theorem isParabolicSolution_flatData_iff {u₀ : SmoothCcTensor g r s} {T : ℝ}
    {u : ℝ → SmoothCcTensor g r s} :
    (D.flatData g).IsParabolicSolution g (flatCc g r s u₀) T (fun t => flatCc g r s (u t)) ↔
      D.IsParabolicSolution g u₀ T u :=
  ⟨D.isParabolicSolution_of_flatData g, D.isParabolicSolution_flatData g⟩

end EquationData

/-- **Theorem A reduces to covariant bundles.** If parabolic solutions exist for every equation on
a covariant bundle `T⁰_{s'} M` that is parabolic at its initial datum, they exist on every
`T^r_s M`. -/
theorem exists_solution_of_covariant {p : ℕ} (g : SmoothRiemannianMetric I M)
    (hcov : ∀ (s' : ℕ) (D' : EquationData I M 0 s' p) (u₀ : SmoothCcTensor g 0 s'),
      (∀ x : M, D'.IsParabolicAt g 0 x (covJet g 0 s' (2 * p) u₀ x)) →
      ∃ T > 0, ∃ u : ℝ → SmoothCcTensor g 0 s', D'.IsParabolicSolution g u₀ T u)
    {r s : ℕ} (D : EquationData I M r s p) (u₀ : SmoothCcTensor g r s)
    (h₀ : ∀ x : M, D.IsParabolicAt g 0 x (covJet g r s (2 * p) u₀ x)) :
    ∃ T > 0, ∃ u : ℝ → SmoothCcTensor g r s, D.IsParabolicSolution g u₀ T u := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨T, hT, v, hv⟩ := hcov (r + s) (D.flatData g) (flatCc g r s u₀) fun x => by
    rw [covJet_flatCc_eq]
    exact D.isParabolicAt_flatData g (h₀ x)
  refine ⟨T, hT, fun t => sharpCc g r s (v t), D.isParabolicSolution_of_flatData g ?_⟩
  simp only [flatCc_sharpCc]
  exact hv

end ShortTime
