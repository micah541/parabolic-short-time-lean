import ShortTime.Nonlinear.FlatAlgebra
import ShortTime.Nonlinear.ModelCoords

/-!
# Lowering preserves the Legendre condition

Paper: Lemma `lem:lowering`, last part.

The partial derivatives of the lowered equation are `D_k F^♭(♭_J ζ) = ♭ ∘ D_k F(ζ) ∘ Λ_k⁻¹`
(`flatData_partialDeriv`), computed in model coordinates. With the compatibilities of
`FlatAlgebra.lean`, the principal coefficient satisfies
`P^♭(θ ⊗ Λ_p η) = ♭ P(θ ⊗ η)` (`flatData_principal_prepend`), so the Legendre forms agree:
`B_{P^♭}(Λ_p ξ, Λ_p ξ) = B_P(ξ, ξ)` (`legendreForm_flatData`). Since `Λ_p` is an isometry onto
`T⁰_{(r+s)+p}`, the Legendre condition holds with the same constant (`legendreAt_flatData`).
-/

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Connection
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

variable (g : SmoothRiemannianMetric I M)

/-! ### The jet map in the model -/

/-- The jet map `♭_J` in the model spaces. -/
def jetFlatModel (r s N : ℕ) (x : M) : JetModel E r s N ≃L[ℝ] JetModel E 0 (r + s) N :=
  ContinuousLinearEquiv.piCongrRight fun k =>
    (flatModel g r (s + k) x).trans (permModel E (jetPerm r s k))

theorem jetIso_jetFlat {r s N : ℕ} {x : M} (ζ : CovJetFiber I r s N x) :
    jetIso I 0 (r + s) N x (jetFlat g r s N x ζ) = jetFlatModel g r s N x (jetIso I r s N x ζ) := by
  funext k
  rw [jetIso_apply, jetFlat_apply, toModel_slotPerm, toModel_flat]
  rfl

theorem jetFlat_symm_jetIso_symm {r s N : ℕ} {x : M} (z : JetModel E 0 (r + s) N) :
    (jetFlat g r s N x).symm ((jetIso I 0 (r + s) N x).symm z) =
      (jetIso I r s N x).symm ((jetFlatModel g r s N x).symm z) := by
  apply (jetFlat g r s N x).injective
  apply (jetIso I 0 (r + s) N x).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply, jetIso_jetFlat,
    LinearIsometryEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]

theorem jetFlatModel_symm_single {r s N : ℕ} {x : M} (k : Fin (N + 1))
    (m : TensorRSModel 0 ((r + s) + k) ℝ E) :
    (jetFlatModel g r s N x).symm (Pi.single k m) =
      Pi.single k ((flatModel g r (s + k) x).symm ((permModel E (jetPerm r s k)).symm m)) := by
  funext j
  by_cases h : j = k
  · subst h
    simp [jetFlatModel]
  · rw [Pi.single_eq_of_ne h]
    simp [jetFlatModel, Pi.single_eq_of_ne h]

theorem toModel_flat_symm {r s : ℕ} {x : M} (W : TensorRSSpace 0 (r + s) I x) :
    TensorRSSpace.toModel ((flat g r s x).symm W) = (flatModel g r s x).symm (TensorRSSpace.toModel W) := by
  apply (flatModel g r s x).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, ← toModel_flat, ContinuousLinearEquiv.apply_symm_apply]

theorem toModel_slotPerm_symm {a b : ℕ} (e : Fin a ≃ Fin b) {x : M} (W : TensorRSSpace 0 b I x) :
    TensorRSSpace.toModel ((slotPerm I e x).symm W) = (permModel E e).symm (TensorRSSpace.toModel W) := by
  apply (permModel E e).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, ← toModel_slotPerm, ContinuousLinearEquiv.apply_symm_apply]

/-! ### Partial derivatives of the lowered equation -/

namespace EquationData

variable {r s p : ℕ} (D : EquationData I M r s p)

theorem Fmod_flatData (t : ℝ) (x : M) :
    (D.flatData g).Fmod t x =
      (flatModel g r s x) ∘ (D.Fmod t x ∘ (jetFlatModel g r s (2 * p) x).symm) := by
  funext z
  change TensorRSSpace.toModel (flat g r s x (D.F t x ((jetFlat g r s (2 * p) x).symm
    ((jetIso I 0 (r + s) (2 * p) x).symm z)))) = _
  rw [toModel_flat, jetFlat_symm_jetIso_symm]
  rfl

/-- **Partial derivatives of the lowered equation**: `D_k F^♭(♭_J ζ) = ♭ ∘ D_k F(ζ) ∘ Λ_k⁻¹`. -/
theorem flatData_partialDeriv (k : Fin (2 * p + 1)) (t : ℝ) (x : M)
    (ζ : CovJetFiber I r s (2 * p) x) (w : TensorRSSpace 0 ((r + s) + k) I x) :
    (D.flatData g).partialDeriv k t x (jetFlat g r s (2 * p) x ζ) w =
      flat g r s x (D.partialDeriv k t x ζ
        ((flat g r (s + k) x).symm ((slotPerm I (jetPerm r s k) x).symm w))) := by
  apply (fibIso I 0 (r + s) x).injective
  rw [fibIso_partialDeriv, fibIso_apply (flat g r s x _), toModel_flat, ← fibIso_apply,
    fibIso_partialDeriv, Fmod_flatData, ContinuousLinearEquiv.comp_fderiv,
    ContinuousLinearEquiv.comp_right_fderiv, jetIso_jetFlat]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply, jetFlatModel_symm_single]
  congr 3

/-! ### The principal coefficient and the Legendre condition -/

/-- **The principal coefficient of the lowered equation**: `P^♭(θ ⊗ Λ_p η) = ♭ P(θ ⊗ η)`. -/
theorem flatData_principal_prepend (t : ℝ) (x : M) (ζ : CovJetFiber I r s (2 * p) x)
    (θ : Fin p → (TangentSpace I x →L[ℝ] ℝ)) (η : TensorRSSpace r (s + p) I x) :
    (D.flatData g).principal t x (jetFlat g r s (2 * p) x ζ)
        (prependCovectors p θ (slotPerm I (jetPerm r s p) x (flat g r (s + p) x η))) =
      flat g r s x (D.principal t x ζ (prependCovectors p θ η)) := by
  simp only [principal, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [flatData_partialDeriv]
  congr 2
  rw [ContinuousLinearEquiv.symm_apply_eq, ContinuousLinearEquiv.symm_apply_eq]
  exact castIdx_prepend_jetFlat g θ η _ _

/-- The isometry `Λ_p = σ_p ♭ : T^r_{s+p} ≃ T⁰_{(r+s)+p}`. -/
def jetFlatP (x : M) : TensorRSSpace r (s + p) I x ≃L[ℝ] TensorRSSpace 0 ((r + s) + p) I x :=
  (flat g r (s + p) x).trans (slotPerm I (jetPerm r s p) x)

/-- **Lowering preserves the Legendre form**: `B_{P^♭}(Λ_p ξ, Λ_p ξ) = B_P(ξ, ξ)`. -/
theorem legendreForm_flatData (t : ℝ) (x : M) (ζ : CovJetFiber I r s (2 * p) x)
    (ξ : TensorRSSpace r (s + p) I x) :
    legendreForm g 0 (r + s) p x ((D.flatData g).principal t x (jetFlat g r s (2 * p) x ζ))
        (jetFlatP g (r := r) (s := s) (p := p) x ξ) (jetFlatP g (r := r) (s := s) (p := p) x ξ) =
      legendreForm g r s p x (D.principal t x ζ) ξ ξ := by
  simp only [legendreForm, jetFlatP, ContinuousLinearEquiv.trans_apply, evalFirst_jetFlat,
    D.flatData_principal_prepend g, fiberInner_flat]

/-- **Lowering preserves the Legendre condition**, with the same constant. -/
theorem legendreAt_flatData {t : ℝ} {x : M} {ζ : CovJetFiber I r s (2 * p) x} {lam : ℝ}
    (h : LegendreAt g r s p x (D.principal t x ζ) lam) :
    LegendreAt g 0 (r + s) p x ((D.flatData g).principal t x (jetFlat g r s (2 * p) x ζ)) lam := by
  refine ⟨h.1, fun ξ' => ?_⟩
  obtain ⟨ξ, rfl⟩ : ∃ ξ, jetFlatP g (r := r) (s := s) (p := p) x ξ = ξ' :=
    ⟨(jetFlatP g x).symm ξ', ContinuousLinearEquiv.apply_symm_apply _ _⟩
  have hn : fiberInner g 0 ((r + s) + p) x (jetFlatP g (r := r) (s := s) (p := p) x ξ)
      (jetFlatP g (r := r) (s := s) (p := p) x ξ) = fiberInner g r (s + p) x ξ ξ := by
    simp only [jetFlatP, ContinuousLinearEquiv.trans_apply, fiberInner_slotPerm, fiberInner_flat]
  rw [hn, legendreForm_flatData]
  exact h.2 ξ

/-- **Lowering preserves parabolicity.** -/
theorem isParabolicAt_flatData {t : ℝ} {x : M} {ζ : CovJetFiber I r s (2 * p) x}
    (h : D.IsParabolicAt g t x ζ) :
    (D.flatData g).IsParabolicAt g t x (jetFlat g r s (2 * p) x ζ) := by
  obtain ⟨hdom, lam, hlam⟩ := h
  exact ⟨(D.mem_flatData_dom g t x ζ).mpr hdom, lam, D.legendreAt_flatData g hlam⟩

end EquationData

end ShortTime
