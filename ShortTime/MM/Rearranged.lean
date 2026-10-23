import ShortTime.MM.RearrangedSmooth
import ShortTime.MM.PartialLast
import ShortTime.MM.PosDef

/-!
# The MM equation and its Legendre-rearranged form as `EquationData`

Paper: `cor:MM`, `rem:rewrite`.

* `MMData.toEquationData`: the MM equation `∂ₜu = F[u]` as equation data.
* `MMData.rearranged g`: the equation data with the same domain and the right side `F'` of
  `rem:rewrite`. Solutions coincide (`rearranged_isSolution_iff`), and `F'` is parabolic at every point
  of the domain (`rearranged_isParabolicAt`): the principal coefficient is the split pairing
  `productCLM`, which satisfies the Legendre condition by `legendre_product`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Elliptic DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff BigOperators

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

variable {p : ℕ} (d : MMData I M p)

/-- **The MM equation** `∂ₜ u = F[u]` as equation data. -/
def MMData.toEquationData : EquationData I M 0 0 p where
  T₀ := d.T₀
  T₀_pos := d.T₀_pos
  dom := d.dom
  F := d.F
  dom_relOpen := d.dom_relOpen
  smooth := fun x₀ => smooth_F d x₀

variable (g : SmoothRiemannianMetric I M)

/-- **The Legendre-rearranged equation** (`rem:rewrite`): same domain, right side `F'`. -/
def MMData.rearranged : EquationData I M 0 0 p where
  T₀ := d.T₀
  T₀_pos := d.T₀_pos
  dom := d.dom
  F := d.Frearr g
  dom_relOpen := d.dom_relOpen
  smooth := fun x₀ => smooth_Frearr g d x₀

/-- The rearranged equation has the same solutions as the MM equation. -/
theorem MMData.rearranged_isSolution_iff {u₀ : SmoothCcTensor g 0 0} {T : ℝ}
    {u : ℝ → SmoothCcTensor g 0 0} :
    (d.rearranged g).IsSolution g u₀ T u ↔ d.toEquationData.IsSolution g u₀ T u := by
  have key : ∀ t x, (d.rearranged g).F t x (covJet g 0 0 (2 * p) (u t) x) =
      d.toEquationData.F t x (covJet g 0 0 (2 * p) (u t) x) :=
    fun t x => d.Frearr_covJet g (u t) t x
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨h1, h2, h3, h4, h5, fun t ht x => ?_⟩
    have := h6 t ht x
    rwa [key] at this
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨h1, h2, h3, h4, h5, fun t ht x => ?_⟩
    have := h6 t ht x
    rwa [← key] at this

/-- The rearranged right side is affine in the top jet component. -/
theorem MMData.Frearr_add_single (hp : 1 ≤ p) (t : ℝ) (x : M) (ζ : CovJetFiber I 0 0 (2 * p) x)
    (w : TensorRSSpace 0 (0 + 2 * p) I x) :
    d.Frearr g t x (ζ + (Pi.single (Fin.last (2 * p)) w : CovJetFiber I 0 0 (2 * p) x)) =
      d.Frearr g t x ζ +
      productCLM g 0 0 p x (fun l => d.Ef l t x ζ)
        (EquationData.castIdx (show 0 + 2 * p = 0 + p + p by omega) x w) := by
  have hne : ∀ k : Fin (2 * p + 1), k ≠ Fin.last (2 * p) →
      (ζ + (Pi.single (Fin.last (2 * p)) w : CovJetFiber I 0 0 (2 * p) x)) k = ζ k :=
    fun k hk => by
      show ζ k + (Pi.single (Fin.last (2 * p)) w : CovJetFiber I 0 0 (2 * p) x) k = ζ k
      rw [Pi.single_eq_of_ne hk, add_zero]
  have hEf : ∀ l, d.Ef l t x (ζ + (Pi.single (Fin.last (2 * p)) w : CovJetFiber I 0 0 (2 * p) x)) =
      d.Ef l t x ζ := fun l => d.Ef_lower l t x _ _ hne
  have hb : d.b t x (ζ + (Pi.single (Fin.last (2 * p)) w : CovJetFiber I 0 0 (2 * p) x)) =
      d.b t x ζ := d.b_lower t x _ _ hne
  have htr : truncJet x (ζ + (Pi.single (Fin.last (2 * p)) w : CovJetFiber I 0 0 (2 * p) x)) =
      truncJet x ζ := by
    funext k
    refine hne _ ?_
    intro h
    have h' := congrArg Fin.val h
    have hk := k.isLt
    rw [Fin.val_last] at h'
    simp only at h'
    omega
  have htop : jtop p (ζ + (Pi.single (Fin.last (2 * p)) w : CovJetFiber I 0 0 (2 * p) x)) =
      jtop p ζ + w := by
    show ζ (Fin.last (2 * p)) + (Pi.single (Fin.last (2 * p)) w : CovJetFiber I 0 0 (2 * p) x)
      (Fin.last (2 * p)) = _
    rw [Pi.single_eq_same]
    rfl
  simp only [MMData.Frearr, hEf, hb, htr, htop]
  have e : jtop p ζ + w + ricciQ g p x (truncJet x ζ) =
      (jtop p ζ + ricciQ g p x (truncJet x ζ)) + w := by abel
  rw [e, map_add, map_add, add_right_comm]

/-- The principal coefficient of the rearranged equation is the split pairing `productCLM`. -/
theorem MMData.rearranged_principal (hp : 1 ≤ p) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) d.T₀) {x : M}
    {ζ : CovJetFiber I 0 0 (2 * p) x} (hζ : ζ ∈ d.dom t x) :
    (d.rearranged g).principal t x ζ = productCLM g 0 0 p x (fun l => d.Ef l t x ζ) := by
  let L : TensorRSSpace 0 (0 + ((Fin.last (2 * p) : Fin (2 * p + 1)) : ℕ)) I x →ₗ[ℝ]
      TensorRSSpace 0 0 I x :=
    (productCLM g 0 0 p x (fun l => d.Ef l t x ζ)).toLinearMap ∘ₗ
      (EquationData.castIdx (show 0 + 2 * p = 0 + p + p by omega) x).toLinearEquiv.toLinearMap
  refine ContinuousLinearMap.ext fun w => ?_
  simp only [EquationData.principal, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [EquationData.partialDeriv_last_eq (d.rearranged g) ht hζ L (fun w => ?_)]
  · show productCLM g 0 0 p x (fun l => d.Ef l t x ζ)
      (EquationData.castIdx (show 0 + 2 * p = 0 + p + p by omega) x
        (EquationData.castIdx (r := 0) (a := 0 + p + p) (b := 0 + 2 * p) (by omega) x w)) =
      productCLM g 0 0 p x (fun l => d.Ef l t x ζ) w
    rw [castIdx_castIdx]
    rfl
  · exact d.Frearr_add_single g hp t x ζ w

/-- **Parabolicity of the rearranged equation** (`lem:legendre-examples` (a), `rem:rewrite`): at every
point of the domain, the principal coefficient satisfies the Legendre condition. -/
theorem MMData.rearranged_isParabolicAt (hp : 1 ≤ p) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) d.T₀) {x : M}
    {ζ : CovJetFiber I 0 0 (2 * p) x} (hζ : ζ ∈ d.dom t x) :
    (d.rearranged g).IsParabolicAt g t x ζ := by
  have hq : Continuous (fun ξ : TangentSpace I x →L[ℝ] ℝ =>
      ∑ a, (ξ (tangentFrame g x a)) ^ 2) :=
    continuous_finsetSum _ fun a _ =>
      ((ContinuousLinearMap.apply ℝ ℝ (tangentFrame g x a)).continuous).pow 2
  have hqh : ∀ (c : ℝ) (ξ : TangentSpace I x →L[ℝ] ℝ),
      ∑ a, ((c • ξ) (tangentFrame g x a)) ^ 2 = c ^ 2 * ∑ a, (ξ (tangentFrame g x a)) ^ 2 := by
    intro c ξ
    simp only [smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  have hex : ∀ l, ∃ e : ℝ, 0 < e ∧ ∀ ξ : TangentSpace I x →L[ℝ] ℝ,
      e * ∑ a, (ξ (tangentFrame g x a)) ^ 2 ≤ d.Ef l t x ζ ξ ξ := fun l =>
    exists_pos_lower_bound (d.Ef l t x ζ) _ hq hqh (fun ξ hξ => d.Ef_pos l t x ζ ht hζ ξ hξ)
  choose e he hle using hex
  refine ⟨hζ, ∏ l, e l, ?_⟩
  rw [d.rearranged_principal g hp ht hζ]
  exact legendre_product g (fun l => d.Ef l t x ζ) e he
    (fun l ξ η => d.Ef_symm l t x ζ ξ η) hle

end ShortTime
