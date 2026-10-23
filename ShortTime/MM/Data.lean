import ShortTime.MM.PairingBasis
import ShortTime.Setting.Equation

/-!
# Mantegazza–Martinazzi data and the MM equation

Paper: `cor:MM`. The scalar equation `∂ₜ u = (-1)^{p+1} Σ E_1^{i₁j₁}⋯E_p^{i_pj_p} ∇^{2p}_{i₁j₁⋯i_pj_p} u + b`
with symmetric positive definite forms `E_ℓ` and lower-order data `E_ℓ, b` depending on
`(t, x, u, ∇u, …, ∇^{2p-1}u)`.

* `MMData` collects the data. Smoothness is stated in the coordinates of the trivialisations at `x₀`
  (as in `EquationData.smooth`): the matrix entries `E_ℓ(e^i, e^j)` in the coordinate coframe, and `b`.
* `MMData.F` is the right side. It uses the metric-free contraction `frameSum` in the fixed frame
  `stdFrame` of `T_xM = E`; by `frameSum_eq_frameSum` it does not depend on the frame, nor on any metric.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral DifferentialGeometry.Analysis.Sobolev
open scoped Manifold ContDiff BigOperators

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- The coordinate frame at `y` of the trivialisation at `x₀`. -/
def coordFrame (x₀ y : M) (i : Fin (Module.finrank ℝ E)) : TangentSpace I y :=
  (trivializationAt E (TangentSpace I) x₀).symmL ℝ y (Module.finBasis ℝ E i)

/-- The dual coordinate coframe at `y` of the trivialisation at `x₀`. -/
def coordCoframe (x₀ y : M) (i : Fin (Module.finrank ℝ E)) : TangentSpace I y →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i) ∘L
    (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y

theorem coordCoframe_coordFrame (x₀ y : M)
    (hy : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) (i j : Fin (Module.finrank ℝ E)) :
    coordCoframe (I := I) x₀ y i (coordFrame (I := I) x₀ y j) = if i = j then 1 else 0 := by
  simp only [coordCoframe, coordFrame, ContinuousLinearMap.comp_apply]
  rw [Trivialization.continuousLinearMapAt_symmL _ hy]
  simp [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, eq_comm]

/-- A fixed frame of `T_xM`. -/
def stdFrame (x : M) (i : Fin (Module.finrank ℝ (TangentSpace I x))) : TangentSpace I x :=
  Module.finBasis ℝ (TangentSpace I x) i

/-- The dual coframe of `stdFrame`. -/
def stdCoframe (x : M) (i : Fin (Module.finrank ℝ (TangentSpace I x))) : TangentSpace I x →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((Module.finBasis ℝ (TangentSpace I x)).coord i)

theorem stdCoframe_stdFrame (x : M) (i j : Fin (Module.finrank ℝ (TangentSpace I x))) :
    stdCoframe (I := I) x i (stdFrame (I := I) x j) = if i = j then 1 else 0 := by
  simp only [stdCoframe, stdFrame, LinearMap.coe_toContinuousLinearMap']
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  exact if_congr eq_comm rfl rfl

/-- **Frame independence of the MM contraction**, between two dual pairs. -/
theorem frameSum_eq_frameSum (p : ℕ) (x : M)
    (Ef : Fin p → (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (b₁ b₂ : Fin (Module.finrank ℝ (TangentSpace I x)) → TangentSpace I x)
    (b₁' b₂' : Fin (Module.finrank ℝ (TangentSpace I x)) → (TangentSpace I x →L[ℝ] ℝ))
    (h₁ : ∀ i j, b₁' i (b₁ j) = if i = j then 1 else 0)
    (h₂ : ∀ i j, b₂' i (b₂ j) = if i = j then 1 else 0)
    (ζ : TensorRSSpace 0 (0 + 2 * p) I x) :
    frameSum p x Ef b₁ b₁' ζ = frameSum p x Ef b₂ b₂' ζ := by
  have : NeZero (Module.finrank ℝ (TangentSpace I x)) :=
    inferInstanceAs (NeZero (Module.finrank ℝ E))
  apply lam_injective x
  rw [lam_frameSum, lam_frameSum]
  congr 1
  let ev : (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
    ContinuousLinearMap.coeLM ℝ
  have hW : ∀ w w' : (TangentSpace I x →L[ℝ] ℝ), (∀ v, ev w v = ev w' v) → w = w' :=
    fun w w' h => ContinuousLinearMap.ext h
  have hb₁ := MMAlg.isDual_of_dual rfl ev hW b₁ b₁' h₁
  have hb₂ := MMAlg.isDual_of_dual rfl ev hW b₂ b₂' h₂
  exact MMAlg.contr_indep hb₂ hb₁ _ _

variable (I M) in
/-- **Mantegazza–Martinazzi data** (`cor:MM`): the scalar equation
`∂ₜu = (-1)^{p+1} Σ E_1^{i₁j₁}⋯E_p^{i_pj_p} ∇^{2p}_{i₁j₁⋯i_pj_p} u + b`.

`Ef l t x ζ` is the symmetric form `E_ℓ` on covectors; `Ef` and `b` depend on the jet only through
`ζ_0, …, ζ_{2p-1}` (not on the top component). Positive definiteness is required pointwise on the
domain; local uniform positivity (the hypothesis of the paper) follows by continuity of `E_ℓ`. -/
structure MMData (p : ℕ) where
  /-- The final time. -/
  T₀ : ℝ
  T₀_pos : 0 < T₀
  /-- The domain `𝒟 ⊆ [0,T₀] × J^{2p}`. -/
  dom : ℝ → (x : M) → Set (CovJetFiber I 0 0 (2 * p) x)
  /-- The symmetric forms `E_ℓ` on covectors. -/
  Ef : Fin p → ℝ → (x : M) → CovJetFiber I 0 0 (2 * p) x →
    ((TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
  /-- The lower-order term. -/
  b : ℝ → (x : M) → CovJetFiber I 0 0 (2 * p) x → TensorRSSpace 0 0 I x
  dom_relOpen : ∀ x₀ : M, ∃ U : Set (ℝ × M × JetModel E 0 0 (2 * p)),
    IsOpen U ∧ localDom 0 0 (2 * p) T₀ dom x₀ = U ∩ localSlab (I := I) 0 0 (2 * p) T₀ x₀
  Ef_lower : ∀ l t x (ζ ζ' : CovJetFiber I 0 0 (2 * p) x),
    (∀ k, k ≠ Fin.last (2 * p) → ζ k = ζ' k) → Ef l t x ζ = Ef l t x ζ'
  b_lower : ∀ t x (ζ ζ' : CovJetFiber I 0 0 (2 * p) x),
    (∀ k, k ≠ Fin.last (2 * p) → ζ k = ζ' k) → b t x ζ = b t x ζ'
  Ef_symm : ∀ l t x ζ ξ η, Ef l t x ζ ξ η = Ef l t x ζ η ξ
  Ef_pos : ∀ l t x ζ, t ∈ Icc (0 : ℝ) T₀ → ζ ∈ dom t x → ∀ ξ : TangentSpace I x →L[ℝ] ℝ,
    ξ ≠ 0 → 0 < Ef l t x ζ ξ ξ
  /-- The matrix entries `E_ℓ(e^i, e^j)` in the coordinate coframe at `x₀` are smooth. -/
  Ef_smooth : ∀ (x₀ : M) (l : Fin p) (i j : Fin (Module.finrank ℝ E)),
    ContMDiffOn (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 0 (2 * p)))) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M × JetModel E 0 0 (2 * p) =>
        Ef l q.1 q.2.1 (jetOfModel 0 0 (2 * p) x₀ q.2.1 q.2.2)
          (coordCoframe (I := I) x₀ q.2.1 i) (coordCoframe (I := I) x₀ q.2.1 j))
      (localDom 0 0 (2 * p) T₀ dom x₀)
  b_smooth : ∀ x₀ : M,
    ContMDiffOn (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, JetModel E 0 0 (2 * p)))) 𝓘(ℝ, TensorRSModel 0 0 ℝ E) ∞
      (localRep 0 0 (2 * p) b x₀) (localDom 0 0 (2 * p) T₀ dom x₀)

namespace MMData

variable {p : ℕ} (d : MMData I M p)

/-- The right side of the MM equation: the contraction of `E_1 ⊗ ⋯ ⊗ E_p` with the top jet
component, plus `b`. -/
def F (t : ℝ) (x : M) (ζ : CovJetFiber I 0 0 (2 * p) x) : TensorRSSpace 0 0 I x :=
  frameSum p x (fun l => d.Ef l t x ζ) (stdFrame x) (stdCoframe x) (ζ (Fin.last (2 * p))) +
    d.b t x ζ

end MMData

end ShortTime
