import ShortTime.Linear.Garding
import ShortTime.Nonlinear.Linearize
import DifferentialGeometry.Bundle.Frame
import DifferentialGeometry.Analysis.Integration.L2.Tensor.InnerSectionSmoothness

/-!
# The segment between two nearby jets stays parabolic (`lem:legendre-basic` (iii))

If two parabolic solutions agree at a time `t₀`, then for a short time the jets on the segment
between them stay in the domain and satisfy the Legendre condition with a uniform constant
(`EquationData.exists_parabolic_segment`).

The Legendre constant is uniform because the Legendre form depends continuously on the base point.
We read it in the trivializations at a point `x₀`:

* the Legendre form is trilinear (`legendreForm_expand`);
* near `x₀` we choose smooth global sections that have constant coordinates (`exists_opField_frame`,
  `exists_tensor_frame`); in them the Legendre form is a section-wise inner product, hence
  continuous (`continuous_legendreForm_sections`);
* so in coordinates the Legendre form is a polynomial with continuous coefficients
  (`legendreForm_fibMap_expand`).

Compactness of `[0, 1]` times the unit sphere, and then of `M`, gives the uniform constant.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Elliptic DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff Topology BigOperators

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

variable (g : SmoothRiemannianMetric I M)

/-! ### The Legendre form is trilinear -/

section Linear

variable {r : ℕ} {x : M}

theorem evalFirst_add {s : ℕ} : ∀ (p : ℕ) (v : Fin p → TangentSpace I x)
    (ξ η : TensorRSSpace r (s + p) I x), evalFirst p v (ξ + η) = evalFirst p v ξ + evalFirst p v η
  | 0, _, _, _ => rfl
  | p + 1, v, ξ, η => by
    simp only [evalFirst, map_add, FunLike.coe_add, Pi.add_apply]
    exact evalFirst_add p _ _ _

theorem evalFirst_smul {s : ℕ} : ∀ (p : ℕ) (v : Fin p → TangentSpace I x) (c : ℝ)
    (ξ : TensorRSSpace r (s + p) I x), evalFirst p v (c • ξ) = c • evalFirst p v ξ
  | 0, _, _, _ => rfl
  | p + 1, v, c, ξ => by
    simp only [evalFirst, map_smul, FunLike.coe_smul, Pi.smul_apply]
    exact evalFirst_smul p _ _ _

theorem prependCovectors_add {t : ℕ} : ∀ (p : ℕ) (θ : Fin p → (TangentSpace I x →L[ℝ] ℝ))
    (η η' : TensorRSSpace r t I x),
    prependCovectors p θ (η + η') = prependCovectors p θ η + prependCovectors p θ η'
  | 0, _, _, _ => rfl
  | p + 1, θ, η, η' => by
    simp only [prependCovectors]
    rw [prependCovectors_add p, ← map_add]
    congr 1
    refine ContinuousLinearMap.ext fun w => ?_
    simp only [ContinuousLinearMap.smulRight_apply, FunLike.coe_add, Pi.add_apply, smul_add]

theorem prependCovectors_smul {t : ℕ} : ∀ (p : ℕ) (θ : Fin p → (TangentSpace I x →L[ℝ] ℝ))
    (c : ℝ) (η : TensorRSSpace r t I x),
    prependCovectors p θ (c • η) = c • prependCovectors p θ η
  | 0, _, _, _ => rfl
  | p + 1, θ, c, η => by
    simp only [prependCovectors]
    rw [prependCovectors_smul p, ← map_smul]
    congr 1
    refine ContinuousLinearMap.ext fun w => ?_
    simp only [ContinuousLinearMap.smulRight_apply, FunLike.coe_smul, Pi.smul_apply]
    exact smul_comm _ _ _

theorem fiberInner_smul_left {s : ℕ} (c : ℝ) (v w : TensorRSSpace r s I x) :
    fiberInner g r s x (c • v) w = c * fiberInner g r s x v w := by
  rw [fiberInner_symm, fiberInner_smul_right, fiberInner_symm]

variable {s p : ℕ}

theorem legendreForm_add_left (P : TensorRSSpace r (s + p + p) I x →L[ℝ] TensorRSSpace r s I x)
    (ξ ξ' η : TensorRSSpace r (s + p) I x) :
    legendreForm g r s p x P (ξ + ξ') η =
      legendreForm g r s p x P ξ η + legendreForm g r s p x P ξ' η := by
  simp only [legendreForm_eq, evalFirst_add, fiberInner_add_left, Finset.sum_add_distrib]

theorem legendreForm_smul_left (P : TensorRSSpace r (s + p + p) I x →L[ℝ] TensorRSSpace r s I x)
    (c : ℝ) (ξ η : TensorRSSpace r (s + p) I x) :
    legendreForm g r s p x P (c • ξ) η = c * legendreForm g r s p x P ξ η := by
  simp only [legendreForm_eq, evalFirst_smul, fiberInner_smul_left, Finset.mul_sum]

theorem legendreForm_add_right (P : TensorRSSpace r (s + p + p) I x →L[ℝ] TensorRSSpace r s I x)
    (ξ η η' : TensorRSSpace r (s + p) I x) :
    legendreForm g r s p x P ξ (η + η') =
      legendreForm g r s p x P ξ η + legendreForm g r s p x P ξ η' := by
  simp only [legendreForm_eq, prependCovectors_add, map_add, fiberInner_add_right,
    Finset.sum_add_distrib]

theorem legendreForm_smul_right (P : TensorRSSpace r (s + p + p) I x →L[ℝ] TensorRSSpace r s I x)
    (c : ℝ) (ξ η : TensorRSSpace r (s + p) I x) :
    legendreForm g r s p x P ξ (c • η) = c * legendreForm g r s p x P ξ η := by
  simp only [legendreForm_eq, prependCovectors_smul, map_smul, fiberInner_smul_right,
    Finset.mul_sum]

/-- The Legendre form as a bilinear map. -/
def legendreBilin (P : TensorRSSpace r (s + p + p) I x →L[ℝ] TensorRSSpace r s I x) :
    TensorRSSpace r (s + p) I x →ₗ[ℝ] TensorRSSpace r (s + p) I x →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (legendreForm g r s p x P) (legendreForm_add_left g P)
    (fun c ξ η => legendreForm_smul_left g P c ξ η) (legendreForm_add_right g P)
    (fun c ξ η => legendreForm_smul_right g P c ξ η)

/-- The Legendre form as a linear map in the coefficient. -/
def legendreLin (ξ η : TensorRSSpace r (s + p) I x) :
    (TensorRSSpace r (s + p + p) I x →L[ℝ] TensorRSSpace r s I x) →ₗ[ℝ] ℝ where
  toFun P := legendreForm g r s p x P ξ η
  map_add' P Q := legendreForm_add g r s p x P Q ξ η
  map_smul' c P := legendreForm_smul g r s p x c P ξ η

/-- The fibre inner product as a bilinear map. -/
def fiberBilin : TensorRSSpace r s I x →ₗ[ℝ] TensorRSSpace r s I x →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fiberInner g r s x) (fiberInner_add_left g x)
    (fun c v w => fiberInner_smul_left g c v w) (fiberInner_add_right g r s x)
    (fun c v w => fiberInner_smul_right g r s x v w c)

theorem legendreForm_expand {ι κ : Type*} [Fintype ι] [Fintype κ] (c : ι → ℝ)
    (P : ι → (TensorRSSpace r (s + p + p) I x →L[ℝ] TensorRSSpace r s I x)) (a : κ → ℝ)
    (ξ : κ → TensorRSSpace r (s + p) I x) :
    legendreForm g r s p x (∑ i, c i • P i) (∑ j, a j • ξ j) (∑ j, a j • ξ j) =
      ∑ i, c i * ∑ j, a j * ∑ l, a l * legendreForm g r s p x (P i) (ξ j) (ξ l) := by
  change legendreLin g (∑ j, a j • ξ j) (∑ j, a j • ξ j) (∑ i, c i • P i) = _
  simp only [map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  change legendreBilin g (P i) (∑ j, a j • ξ j) (∑ j, a j • ξ j) = _
  simp only [map_sum, map_smul, LinearMap.sum_apply, smul_eq_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  change a l * (a j * legendreForm g r s p x (P i) (ξ j) (ξ l)) = _
  ring

theorem fiberInner_expand {κ : Type*} [Fintype κ] (a : κ → ℝ) (ξ : κ → TensorRSSpace r s I x) :
    fiberInner g r s x (∑ j, a j • ξ j) (∑ j, a j • ξ j) =
      ∑ j, a j * ∑ l, a l * fiberInner g r s x (ξ j) (ξ l) := by
  change fiberBilin g (∑ j, a j • ξ j) (∑ j, a j • ξ j) = _
  simp only [map_sum, map_smul, LinearMap.sum_apply, smul_eq_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  change a l * (a j * fiberInner g r s x (ξ j) (ξ l)) = _
  ring

theorem legendreForm_smul_smul (P : TensorRSSpace r (s + p + p) I x →L[ℝ] TensorRSSpace r s I x)
    (c : ℝ) (ξ : TensorRSSpace r (s + p) I x) :
    legendreForm g r s p x P (c • ξ) (c • ξ) = c ^ 2 * legendreForm g r s p x P ξ ξ := by
  rw [legendreForm_smul_left, legendreForm_smul_right]
  ring

theorem fiberInner_smul_smul (c : ℝ) (ξ : TensorRSSpace r s I x) :
    fiberInner g r s x (c • ξ) (c • ξ) = c ^ 2 * fiberInner g r s x ξ ξ := by
  rw [fiberInner_smul_left, fiberInner_smul_right]
  ring

theorem LegendreAt.mono {P : TensorRSSpace r (s + p + p) I x →L[ℝ] TensorRSSpace r s I x}
    {lam lam' : ℝ} (h : LegendreAt g r s p x P lam) (hlam' : 0 < lam') (hle : lam' ≤ lam) :
    LegendreAt g r s p x P lam' := by
  refine ⟨hlam', fun ξ => le_trans ?_ (h.2 ξ)⟩
  have h0 : 0 ≤ fiberInner g r (s + p) x ξ ξ := by
    by_cases hξ : ξ = 0
    · subst hξ
      simp [fiberInner]
    · exact ((Tensor.TensorRSRiemannianBundle.tensorRSRiemannianMetric (I := I) (M := M) g r
        (s + p)).pos x ξ hξ).le
  exact mul_le_mul_of_nonneg_right hle h0

end Linear

/-! ### Continuity through smooth sections -/

section Sections

variable [CompleteSpace E] {s p : ℕ}

theorem continuous_legendreForm_sections (P : SmoothCcTensor g (s + 2 * p) s)
    (Ψ Φ : SmoothCcTensor g 0 (s + p)) :
    Continuous fun x => legendreForm g 0 s p x
      ((opFieldHom (P.toSection x)).comp
        (EquationData.castIdx (r := 0) (by omega : s + p + p = s + 2 * p) x).toContinuousLinearMap)
      (Ψ.toSection x) (Φ.toSection x) := by
  have key : (fun x => legendreForm g 0 s p x
      ((opFieldHom (P.toSection x)).comp
        (EquationData.castIdx (r := 0) (by omega : s + p + p = s + 2 * p) x).toContinuousLinearMap)
      (Ψ.toSection x) (Φ.toSection x)) =
      fun x => tensorInnerPointwise (I := I) (M := M) g 0 (s + p) x
        ((domDomCongrSection (I := I) g (extPerm s p Fin.revPerm) Ψ).toFun x)
        ((operatorFieldApply (I := I) (M := M) g (s + p) (s + p)
          (flipIter g s p p p (by omega) P) Φ).toFun x) := by
    funext x
    rw [legendreForm_eq_fiberInner_flipIter g s p x P _ _ _ _
      (fun w => evalFirst_rev_domDomCongrSection g Ψ x w)]
    rfl
  rw [key]
  exact (Tensor.tensorInnerPointwise_contMDiff g 0 (s + p) _ _).continuous

theorem continuous_fiberInner_sections {a : ℕ} (Ψ Φ : SmoothCcTensor g 0 a) :
    Continuous fun x => fiberInner g 0 a x (Ψ.toSection x) (Φ.toSection x) :=
  (Tensor.tensorInnerPointwise_contMDiff g 0 a Ψ Φ).continuous

end Sections

/-! ### Local frames with constant coordinates -/

section Frames

variable (I) in
/-- The fibre map over `y` whose coordinates in the trivializations at `x₀` are `Q`. -/
def fibMap (a b : ℕ) (x₀ y : M) :
    (TensorRSModel 0 a ℝ E →L[ℝ] TensorRSModel 0 b ℝ E) →ₗ[ℝ]
      (TensorRSSpace 0 a I y →L[ℝ] TensorRSSpace 0 b I y) where
  toFun Q := ((trivAt I M 0 b x₀).symmL ℝ y).comp
    (Q.comp ((trivAt I M 0 a x₀).continuousLinearMapAt ℝ y))
  map_add' Q Q' := ContinuousLinearMap.ext fun w => by
    simp only [ContinuousLinearMap.comp_apply, FunLike.coe_add, Pi.add_apply, map_add]
  map_smul' c Q := ContinuousLinearMap.ext fun w => by
    simp only [ContinuousLinearMap.comp_apply, FunLike.coe_smul, Pi.smul_apply, map_smul,
      RingHom.id_apply]

theorem coordP_fibMap {a b : ℕ} {x₀ y : M} (ha : y ∈ (trivAt I M 0 a x₀).baseSet)
    (hb : y ∈ (trivAt I M 0 b x₀).baseSet)
    (Q : TensorRSModel 0 a ℝ E →L[ℝ] TensorRSModel 0 b ℝ E) :
    coordP x₀ y (fibMap I a b x₀ y Q) = Q :=
  ContinuousLinearMap.ext fun z => by
    simp only [coordP, fibMap, LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.comp_apply,
      Trivialization.continuousLinearMapAt_symmL _ ha, Trivialization.continuousLinearMapAt_symmL _ hb]

theorem fibMap_coordP {a b : ℕ} {x₀ y : M} (ha : y ∈ (trivAt I M 0 a x₀).baseSet)
    (hb : y ∈ (trivAt I M 0 b x₀).baseSet)
    (P : TensorRSSpace 0 a I y →L[ℝ] TensorRSSpace 0 b I y) :
    fibMap I a b x₀ y (coordP x₀ y P) = P :=
  ContinuousLinearMap.ext fun w => by
    simp only [coordP, fibMap, LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.comp_apply,
      Trivialization.symmL_continuousLinearMapAt _ ha, Trivialization.symmL_continuousLinearMapAt _ hb]

/-- Smooth operator fields that, near `x₀`, have the constant coordinates `Q i`. -/
theorem exists_opField_frame (a b : ℕ) (x₀ : M) {ι : Type*}
    (Q : ι → (TensorRSModel 0 a ℝ E →L[ℝ] TensorRSModel 0 b ℝ E)) :
    ∃ P : ι → SmoothCcTensor g a b, ∀ᶠ y in 𝓝 x₀, ∀ i,
      opFieldHom ((P i).toSection y) = fibMap I a b x₀ y (Q i) := by
  set W := (trivializationAt E (TangentSpace I) x₀).baseSet ∩ ((trivAt I M 0 a x₀).baseSet ∩
    ((trivAt I M 0 b x₀).baseSet ∩ (trivAt I M a b x₀).baseSet)) with hW
  have hWo : IsOpen W := (trivializationAt E (TangentSpace I) x₀).open_baseSet.inter
    ((trivAt I M 0 a x₀).open_baseSet.inter
      ((trivAt I M 0 b x₀).open_baseSet.inter (trivAt I M a b x₀).open_baseSet))
  have hx₀ : x₀ ∈ W := ⟨mem_baseSet_trivializationAt _ _ x₀, mem_baseSet_trivializationAt _ _ x₀,
    mem_baseSet_trivializationAt _ _ x₀, mem_baseSet_trivializationAt _ _ x₀⟩
  have hs : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel a b ℝ E)) ∞
      (fun y => TotalSpace.mk' (TensorRSModel a b ℝ E) (E := fun y : M => TensorRSSpace a b I y) y
        (opFieldOf (fibMap I a b x₀ y (Q i)))) W := by
    intro i
    rw [(trivAt I M a b x₀).contMDiffOn_iff
      fun y hy => (trivAt I M a b x₀).mem_source.mpr hy.2.2.2]
    refine ⟨contMDiffOn_id, (contMDiffOn_const (c := opFieldCoord a b (Q i))).congr
      fun y hy => ?_⟩
    rw [trivAt_opFieldOf hy.1, coordP_fibMap hy.2.1 hy.2.2.1]
  obtain ⟨P, hP⟩ := exists_contMDiffSection_eqOn_nhd (I := I)
    (s := fun i y => opFieldOf (fibMap I a b x₀ y (Q i))) hs hWo hx₀
  refine ⟨fun i => ⟨P i, HasCompactSupport.of_compactSpace _⟩, ?_⟩
  filter_upwards [hP] with y hy i
  change opFieldHom (P i y) = _
  rw [hy i, opFieldHom_opFieldOf]

/-- Smooth tensor fields that, near `x₀`, have the constant coordinates `c j`. -/
theorem exists_tensor_frame (a : ℕ) (x₀ : M) {ι : Type*} (c : ι → TensorRSModel 0 a ℝ E) :
    ∃ Ψ : ι → SmoothCcTensor g 0 a, ∀ᶠ y in 𝓝 x₀, ∀ j,
      (Ψ j).toSection y = (trivAt I M 0 a x₀).symmL ℝ y (c j) := by
  have hs : ∀ j, ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel 0 a ℝ E)) ∞
      (fun y => TotalSpace.mk' (TensorRSModel 0 a ℝ E) (E := fun y : M => TensorRSSpace 0 a I y) y
        ((trivAt I M 0 a x₀).symmL ℝ y (c j))) (trivAt I M 0 a x₀).baseSet := by
    intro j
    rw [(trivAt I M 0 a x₀).contMDiffOn_iff fun y hy => (trivAt I M 0 a x₀).mem_source.mpr hy]
    refine ⟨contMDiffOn_id, (contMDiffOn_const (c := c j)).congr fun y hy => ?_⟩
    rw [Trivialization.symmL_apply _ hy, (trivAt I M 0 a x₀).apply_mk_symm hy]
  obtain ⟨Ψ, hΨ⟩ := exists_contMDiffSection_eqOn_nhd (I := I)
    (s := fun j y => (trivAt I M 0 a x₀).symmL ℝ y (c j)) hs (trivAt I M 0 a x₀).open_baseSet
    (mem_baseSet_trivializationAt _ _ x₀)
  exact ⟨fun j => ⟨Ψ j, HasCompactSupport.of_compactSpace _⟩, hΨ⟩

end Frames

/-! ### The Legendre form in coordinates -/

section Coordinates

variable [CompleteSpace E] {s p : ℕ}

theorem mem_jetBase_self (r s N : ℕ) (x₀ : M) : x₀ ∈ jetBase (I := I) r s N x₀ :=
  ⟨mem_baseSet_trivializationAt _ _ x₀, mem_iInter.mpr fun _ => mem_baseSet_trivializationAt _ _ x₀⟩

theorem isOpen_jetBase (r s N : ℕ) (x₀ : M) : IsOpen (jetBase (I := I) r s N x₀) :=
  (trivAt I M r s x₀).open_baseSet.inter
    (isOpen_iInter_of_finite fun k => (trivAt I M r (s + k) x₀).open_baseSet)

theorem continuous_basis_repr {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ F) (i : ι) :
    Continuous fun z => b.repr z i := by
  have h := (continuous_apply i).comp b.equivFunL.continuous
  simpa only [Function.comp_def, Module.Basis.equivFunL_apply, Module.Basis.equivFun_apply] using h

/-- Through frames, the Legendre form in coordinates is a polynomial in the coordinates. -/
theorem legendreForm_fibMap_expand {x₀ y : M} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (bQ : Module.Basis ι ℝ (TensorRSModel 0 (s + 2 * p) ℝ E →L[ℝ] TensorRSModel 0 s ℝ E))
    (bz : Module.Basis κ ℝ (TensorRSModel 0 (s + p) ℝ E))
    (P : ι → SmoothCcTensor g (s + 2 * p) s) (Ψ : κ → SmoothCcTensor g 0 (s + p))
    (hP : ∀ i, opFieldHom ((P i).toSection y) = fibMap I (s + 2 * p) s x₀ y (bQ i))
    (hΨ : ∀ j, (Ψ j).toSection y = (trivAt I M 0 (s + p) x₀).symmL ℝ y (bz j))
    (Q : TensorRSModel 0 (s + 2 * p) ℝ E →L[ℝ] TensorRSModel 0 s ℝ E)
    (z : TensorRSModel 0 (s + p) ℝ E) :
    legendreForm g 0 s p y ((fibMap I (s + 2 * p) s x₀ y Q).comp
        (EquationData.castIdx (r := 0) (by omega : s + p + p = s + 2 * p) y).toContinuousLinearMap)
      ((trivAt I M 0 (s + p) x₀).symmL ℝ y z) ((trivAt I M 0 (s + p) x₀).symmL ℝ y z) =
    ∑ i, bQ.repr Q i * ∑ j, bz.repr z j * ∑ l, bz.repr z l *
      legendreForm g 0 s p y ((opFieldHom ((P i).toSection y)).comp
        (EquationData.castIdx (r := 0) (by omega : s + p + p = s + 2 * p) y).toContinuousLinearMap)
        ((Ψ j).toSection y) ((Ψ l).toSection y) := by
  have hQ : fibMap I (s + 2 * p) s x₀ y Q = ∑ i, bQ.repr Q i • opFieldHom ((P i).toSection y) := by
    conv_lhs => rw [← bQ.sum_repr Q]
    simp only [map_sum, map_smul, hP]
  have hz : (trivAt I M 0 (s + p) x₀).symmL ℝ y z = ∑ j, bz.repr z j • (Ψ j).toSection y := by
    conv_lhs => rw [← bz.sum_repr z]
    simp only [map_sum, map_smul, hΨ]
  have hcomp : ∀ (c : ι → ℝ)
      (F : ι → (TensorRSSpace 0 (s + 2 * p) I y →L[ℝ] TensorRSSpace 0 s I y))
      (C : TensorRSSpace 0 (s + p + p) I y →L[ℝ] TensorRSSpace 0 (s + 2 * p) I y),
      (∑ i, c i • F i).comp C = ∑ i, c i • (F i).comp C := fun c F C =>
    ContinuousLinearMap.ext fun w => by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply, FunLike.coe_smul,
        Pi.smul_apply]
  rw [hQ, hz, hcomp, legendreForm_expand]

theorem fiberInner_symmL_expand {a : ℕ} {x₀ y : M} {κ : Type*} [Fintype κ]
    (bz : Module.Basis κ ℝ (TensorRSModel 0 a ℝ E)) (Ψ : κ → SmoothCcTensor g 0 a)
    (hΨ : ∀ j, (Ψ j).toSection y = (trivAt I M 0 a x₀).symmL ℝ y (bz j))
    (z : TensorRSModel 0 a ℝ E) :
    fiberInner g 0 a y ((trivAt I M 0 a x₀).symmL ℝ y z) ((trivAt I M 0 a x₀).symmL ℝ y z) =
      ∑ j, bz.repr z j * ∑ l, bz.repr z l *
        fiberInner g 0 a y ((Ψ j).toSection y) ((Ψ l).toSection y) := by
  have hz : (trivAt I M 0 a x₀).symmL ℝ y z = ∑ j, bz.repr z j • (Ψ j).toSection y := by
    conv_lhs => rw [← bz.sum_repr z]
    simp only [map_sum, map_smul, hΨ]
  rw [hz, fiberInner_expand]

/-- **The Legendre form is continuous in coordinates.** Near `x₀`, the Legendre form and the fibre
inner product, read in the trivializations at `x₀`, agree with jointly continuous functions. -/
theorem exists_legendre_coord (x₀ : M) :
    ∃ (Λ : M → (TensorRSModel 0 (s + 2 * p) ℝ E →L[ℝ] TensorRSModel 0 s ℝ E) →
        TensorRSModel 0 (s + p) ℝ E → ℝ) (B : M → TensorRSModel 0 (s + p) ℝ E → ℝ),
      Continuous (fun w : M × (TensorRSModel 0 (s + 2 * p) ℝ E →L[ℝ] TensorRSModel 0 s ℝ E) ×
        TensorRSModel 0 (s + p) ℝ E => Λ w.1 w.2.1 w.2.2) ∧
      Continuous (fun w : M × TensorRSModel 0 (s + p) ℝ E => B w.1 w.2) ∧
      ∀ᶠ y in 𝓝 x₀, ∀ Q z,
        legendreForm g 0 s p y ((fibMap I (s + 2 * p) s x₀ y Q).comp
          (EquationData.castIdx (r := 0) (by omega : s + p + p = s + 2 * p) y).toContinuousLinearMap)
          ((trivAt I M 0 (s + p) x₀).symmL ℝ y z) ((trivAt I M 0 (s + p) x₀).symmL ℝ y z) =
            Λ y Q z ∧
        fiberInner g 0 (s + p) y ((trivAt I M 0 (s + p) x₀).symmL ℝ y z)
          ((trivAt I M 0 (s + p) x₀).symmL ℝ y z) = B y z := by
  haveI : Module.Free ℝ (TensorRSModel 0 (s + p) ℝ E) := Module.Free.of_divisionRing _ _
  haveI : Module.Free ℝ (TensorRSModel 0 (s + 2 * p) ℝ E →L[ℝ] TensorRSModel 0 s ℝ E) :=
    Module.Free.of_divisionRing _ _
  let bz := Module.finBasis ℝ (TensorRSModel 0 (s + p) ℝ E)
  let bQ := Module.finBasis ℝ (TensorRSModel 0 (s + 2 * p) ℝ E →L[ℝ] TensorRSModel 0 s ℝ E)
  obtain ⟨Pf, hPf⟩ := exists_opField_frame g (s + 2 * p) s x₀ bQ
  obtain ⟨Ψf, hΨf⟩ := exists_tensor_frame g (s + p) x₀ bz
  refine ⟨fun y Q z => ∑ i, bQ.repr Q i * ∑ j, bz.repr z j * ∑ l, bz.repr z l *
      legendreForm g 0 s p y ((opFieldHom ((Pf i).toSection y)).comp
        (EquationData.castIdx (r := 0) (by omega : s + p + p = s + 2 * p) y).toContinuousLinearMap)
        ((Ψf j).toSection y) ((Ψf l).toSection y),
    fun y z => ∑ j, bz.repr z j * ∑ l, bz.repr z l *
      fiberInner g 0 (s + p) y ((Ψf j).toSection y) ((Ψf l).toSection y), ?_, ?_, ?_⟩
  · refine continuous_finsetSum _ fun i _ => ?_
    refine (continuous_basis_repr bQ i).fst'.snd'.mul ?_
    refine continuous_finsetSum _ fun j _ => ?_
    refine (continuous_basis_repr bz j).snd'.snd'.mul ?_
    refine continuous_finsetSum _ fun l _ => ?_
    exact (continuous_basis_repr bz l).snd'.snd'.mul
      (continuous_legendreForm_sections g (Pf i) (Ψf j) (Ψf l)).fst'
  · refine continuous_finsetSum _ fun j _ => ?_
    refine (continuous_basis_repr bz j).snd'.mul ?_
    refine continuous_finsetSum _ fun l _ => ?_
    exact (continuous_basis_repr bz l).snd'.mul
      (continuous_fiberInner_sections g (Ψf j) (Ψf l)).fst'
  · filter_upwards [hPf, hΨf] with y hPy hΨy
    intro Q z
    exact ⟨legendreForm_fibMap_expand g bQ bz Pf Ψf hPy hΨy Q z,
      fiberInner_symmL_expand g bz Ψf hΨy z⟩

end Coordinates

/-! ### The tube lemma -/

theorem mul_le_mul_of_lt_aux {a b c d n : ℝ} (hn : 0 < n) (h : a * b < c * d) :
    a * (n * b) ≤ c * (n * d) := by
  nlinarith

namespace EquationData

variable [CompleteSpace E] {s p : ℕ} (D : EquationData I M 0 s p)

/-- The principal coefficient through its coordinates at `x₀`. -/
theorem principal_eq_fibMap {x₀ y : M} (hy : y ∈ jetBase (I := I) 0 s (2 * p) x₀) (t : ℝ)
    (ζ : CovJetFiber I 0 s (2 * p) y) :
    D.principal t y ζ =
      (fibMap I (s + 2 * p) s x₀ y (coordP x₀ y (D.partialDeriv (Fin.last (2 * p)) t y ζ))).comp
        (EquationData.castIdx (r := 0) (by omega : s + p + p = s + 2 * p) y).toContinuousLinearMap := by
  have h := fibMap_coordP (I := I) (a := s + ((Fin.last (2 * p) : Fin (2 * p + 1)) : ℕ)) (b := s)
    (x₀ := x₀) (mem_iInter.mp hy.2 (Fin.last (2 * p))) hy.1
    (D.partialDeriv (Fin.last (2 * p)) t y ζ)
  calc D.principal t y ζ
      = (D.partialDeriv (Fin.last (2 * p)) t y ζ).comp
          (EquationData.castIdx (r := 0) (by simp only [Fin.val_last]; omega) y).toContinuousLinearMap :=
        rfl
    _ = (fibMap I (s + ((Fin.last (2 * p) : Fin (2 * p + 1)) : ℕ)) s x₀ y
          (coordP x₀ y (D.partialDeriv (Fin.last (2 * p)) t y ζ))).comp
          (EquationData.castIdx (r := 0) (by simp only [Fin.val_last]; omega) y).toContinuousLinearMap := by
        rw [h]
    _ = _ := rfl

/-- **The tube lemma at a point.** Near `x₀` and for a short time after `t₀`, the jets on the
segment between two parabolic solutions that agree at `t₀` lie in the domain and satisfy the Legendre
condition with a uniform constant. -/
theorem tube_local {u₀ u₀' : SmoothCcTensor g 0 s} {T : ℝ} {u v : ℝ → SmoothCcTensor g 0 s}
    (hu : D.IsParabolicSolution g u₀ T u) (hv : D.IsParabolicSolution g u₀' T v)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico 0 T) (h : u t₀ = v t₀) (x₀ : M) :
    ∃ lam > 0, ∃ N ∈ 𝓝 x₀, ∃ ε > 0, ∀ y ∈ N, ∀ τ ∈ Icc (0 : ℝ) ε, τ ≤ T - t₀ →
      ∀ σ ∈ Icc (0 : ℝ) 1,
        covJet g 0 s (2 * p) (v (t₀ + τ) + σ • (u (t₀ + τ) - v (t₀ + τ))) y ∈ D.dom (t₀ + τ) y ∧
        LegendreAt g 0 s p y (D.principal (t₀ + τ) y
          (covJet g 0 s (2 * p) (v (t₀ + τ) + σ • (u (t₀ + τ) - v (t₀ + τ))) y)) lam := by
  have hηT : t₀ + (T - t₀) ≤ T := by linarith
  have hTT₀ : T ≤ D.T₀ := hu.1.le_T₀
  set R0 : Set ((M × ℝ) × ℝ) :=
    (jetBase (I := I) 0 s (2 * p) x₀ ×ˢ Icc 0 (T - t₀)) ×ˢ Icc (0 : ℝ) 1 with hR0
  have hγ := D.contMDiffOn_trivJet_segment hu.1.smooth hv.1.smooth hu.1.le_T₀ ht₀.1 hηT x₀
  have hJ₀ : ∀ (y : M) (σ : ℝ), covJet g 0 s (2 * p)
      (v (t₀ + 0) + σ • (u (t₀ + 0) - v (t₀ + 0))) y = covJet g 0 s (2 * p) (u t₀) y := by
    intro y σ
    simp [h]
  have hm₀R0 : ∀ σ ∈ Icc (0 : ℝ) 1, ((x₀, (0 : ℝ)), σ) ∈ R0 := fun σ hσ =>
    mk_mem_prod (mk_mem_prod (mem_jetBase_self 0 s (2 * p) x₀) ⟨le_rfl, by linarith [ht₀.2]⟩) hσ
  /- Step 1: the segment stays in the domain. -/
  obtain ⟨U, hUo, hU⟩ := D.dom_relOpen x₀
  let Fd : (M × ℝ) × ℝ → ℝ × M × JetModel E 0 s (2 * p) := fun z =>
    (t₀ + z.1.2, z.1.1, trivJet x₀ z.1.1 (covJet g 0 s (2 * p)
      (v (t₀ + z.1.2) + z.2 • (u (t₀ + z.1.2) - v (t₀ + z.1.2))) z.1.1))
  have hFd : ∀ z ∈ R0, Fd z ∈ U → covJet g 0 s (2 * p)
      (v (t₀ + z.1.2) + z.2 • (u (t₀ + z.1.2) - v (t₀ + z.1.2))) z.1.1 ∈
        D.dom (t₀ + z.1.2) z.1.1 := by
    intro z hz hzU
    have hmem : ((t₀ + z.1.2, z.1.1, trivJet x₀ z.1.1 (covJet g 0 s (2 * p)
        (v (t₀ + z.1.2) + z.2 • (u (t₀ + z.1.2) - v (t₀ + z.1.2))) z.1.1)) :
          ℝ × M × JetModel E 0 s (2 * p)) ∈ localDom 0 s (2 * p) D.T₀ D.dom x₀ := by
      rw [hU]
      exact ⟨hzU, ⟨by linarith [hz.1.2.1, ht₀.1], by linarith [hz.1.2.2]⟩, hz.1.1⟩
    have h2 : jetOfModel 0 s (2 * p) x₀ z.1.1 (trivJet x₀ z.1.1 (covJet g 0 s (2 * p)
        (v (t₀ + z.1.2) + z.2 • (u (t₀ + z.1.2) - v (t₀ + z.1.2))) z.1.1)) ∈
          D.dom (t₀ + z.1.2) z.1.1 := hmem.2
    rwa [jetOfModel_trivJet hz.1.1] at h2
  have hstep1 : ∀ σ ∈ Icc (0 : ℝ) 1, ∀ᶠ z : (M × ℝ) × ℝ in 𝓝 ((x₀, (0 : ℝ)), σ),
      (z.1, z.2) ∈ R0 → Fd (z.1, z.2) ∈ U := by
    intro σ hσ
    have hc : ContinuousWithinAt Fd R0 ((x₀, 0), σ) :=
      (continuousWithinAt_const.add (continuous_snd.comp continuous_fst).continuousWithinAt).prodMk
        ((continuous_fst.comp continuous_fst).continuousWithinAt.prodMk
          (hγ _ (hm₀R0 σ hσ)).continuousWithinAt)
    have hin : Fd ((x₀, 0), σ) ∈ U := by
      have hmem : ((t₀ + 0, x₀, trivJet x₀ x₀ (covJet g 0 s (2 * p)
          (v (t₀ + 0) + σ • (u (t₀ + 0) - v (t₀ + 0))) x₀)) : ℝ × M × JetModel E 0 s (2 * p)) ∈
            localDom 0 s (2 * p) D.T₀ D.dom x₀ := by
        refine ⟨⟨⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩, mem_jetBase_self 0 s (2 * p) x₀⟩, ?_⟩
        change jetOfModel 0 s (2 * p) x₀ x₀ (trivJet x₀ x₀ (covJet g 0 s (2 * p)
          (v (t₀ + 0) + σ • (u (t₀ + 0) - v (t₀ + 0))) x₀)) ∈ D.dom (t₀ + 0) x₀
        rw [jetOfModel_trivJet (mem_jetBase_self 0 s (2 * p) x₀), hJ₀, add_zero]
        exact hu.1.jets_mem t₀ ⟨ht₀.1, ht₀.2.le⟩ x₀
      rw [hU] at hmem
      exact hmem.1
    filter_upwards [eventually_nhdsWithin_iff.mp
      (hc.preimage_mem_nhdsWithin (hUo.mem_nhds hin))] with z hz hzR
    exact hz hzR
  have hdomEv := isCompact_Icc.eventually_forall_of_forall_eventually
    (P := fun q σ => (q, σ) ∈ R0 → Fd (q, σ) ∈ U) hstep1
  obtain ⟨O, hOsub, hOo, hO0⟩ := eventually_nhds_iff.mp hdomEv
  set R1 : Set ((M × ℝ) × ℝ) := R0 ∩ (O ×ˢ univ) with hR1
  have hdomR1 : ∀ m ∈ R1, covJet g 0 s (2 * p)
      (v (t₀ + m.1.2) + m.2 • (u (t₀ + m.1.2) - v (t₀ + m.1.2))) m.1.1 ∈
        D.dom (t₀ + m.1.2) m.1.1 :=
    fun m hm => hFd m hm.1 (hOsub m.1 hm.2.1 m.2 hm.1.2 hm.1)
  have hm₀R1 : ∀ σ ∈ Icc (0 : ℝ) 1, ((x₀, (0 : ℝ)), σ) ∈ R1 := fun σ hσ =>
    ⟨hm₀R0 σ hσ, mk_mem_prod hO0 (mem_univ _)⟩
  /- Step 2: the Legendre condition, in coordinates at `x₀`. -/
  obtain ⟨Λ, Bf, hΛ, hBf, hev⟩ := exists_legendre_coord (s := s) (p := p) g x₀
  obtain ⟨A, hA⟩ : ∃ A : (M × ℝ) × ℝ →
      (TensorRSModel 0 (s + 2 * p) ℝ E →L[ℝ] TensorRSModel 0 s ℝ E),
      ∀ m, A m = avgIntegrand D u v t₀ x₀ (Fin.last (2 * p)) m.1 m.2 :=
    ⟨fun m => avgIntegrand D u v t₀ x₀ (Fin.last (2 * p)) m.1 m.2, fun _ => rfl⟩
  have hAc : ContinuousOn A R1 :=
    (D.contMDiffOn_avgIntegrand_of_subset hu.1.smooth hv.1.smooth hu.1.le_T₀ ht₀.1 hηT x₀ inter_subset_left hdomR1
      (Fin.last (2 * p))).continuousOn.congr fun m _ => hA m
  obtain ⟨-, lam₁, hL₁⟩ := hu.2 t₀ ⟨ht₀.1, ht₀.2.le⟩ x₀
  have hlam₁ : 0 < lam₁ := hL₁.1
  have hstep2 : ∀ w ∈ Icc (0 : ℝ) 1 ×ˢ Metric.sphere (0 : TensorRSModel 0 (s + p) ℝ E) 1,
      ∀ᶠ z : (M × ℝ) × (ℝ × TensorRSModel 0 (s + p) ℝ E) in 𝓝 ((x₀, (0 : ℝ)), w),
        (z.1, z.2.1) ∈ R1 →
          lam₁ / 2 * Bf z.1.1 z.2.2 < (-1) ^ (p + 1) * Λ z.1.1 (A (z.1, z.2.1)) z.2.2 := by
    rintro ⟨σ, z⟩ ⟨hσ, hz⟩
    have hz1 : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
    have hm₀ := hm₀R1 σ hσ
    -- the gap function is continuous
    have hA' : ContinuousWithinAt (A ∘ fun z : (M × ℝ) × (ℝ × TensorRSModel 0 (s + p) ℝ E) =>
        (z.1, z.2.1)) {z | (z.1, z.2.1) ∈ R1} ((x₀, 0), (σ, z)) :=
      ContinuousWithinAt.comp (g := A)
        (f := fun z : (M × ℝ) × (ℝ × TensorRSModel 0 (s + p) ℝ E) => (z.1, z.2.1))
        (x := ((x₀, 0), (σ, z))) (hAc _ hm₀)
        (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).continuousWithinAt
        fun z hz => hz
    have h11 : Continuous fun z : (M × ℝ) × (ℝ × TensorRSModel 0 (s + p) ℝ E) => z.1.1 :=
      continuous_fst.fst
    have h22 : Continuous fun z : (M × ℝ) × (ℝ × TensorRSModel 0 (s + p) ℝ E) => z.2.2 :=
      continuous_snd.snd
    have hΛc : ContinuousWithinAt
        (fun z : (M × ℝ) × (ℝ × TensorRSModel 0 (s + p) ℝ E) => Λ z.1.1 (A (z.1, z.2.1)) z.2.2)
        {z | (z.1, z.2.1) ∈ R1} ((x₀, 0), (σ, z)) :=
      hΛ.continuousAt.comp_continuousWithinAt
        (h11.continuousWithinAt.prodMk (hA'.prodMk h22.continuousWithinAt))
    have hBc : ContinuousWithinAt
        (fun z : (M × ℝ) × (ℝ × TensorRSModel 0 (s + p) ℝ E) => Bf z.1.1 z.2.2)
        {z | (z.1, z.2.1) ∈ R1} ((x₀, 0), (σ, z)) :=
      hBf.continuousAt.comp_continuousWithinAt
        (h11.continuousWithinAt.prodMk h22.continuousWithinAt)
    have hGc : ContinuousWithinAt
        (fun z : (M × ℝ) × (ℝ × TensorRSModel 0 (s + p) ℝ E) =>
          (-1) ^ (p + 1) * Λ z.1.1 (A (z.1, z.2.1)) z.2.2 - lam₁ / 2 * Bf z.1.1 z.2.2)
        {z | (z.1, z.2.1) ∈ R1} ((x₀, 0), (σ, z)) :=
      (continuousWithinAt_const.mul hΛc).sub (continuousWithinAt_const.mul hBc)
    -- the gap is positive at `(x₀, t₀)`, by the Legendre condition for `u`
    have hpos : 0 < (-1) ^ (p + 1) * Λ x₀ (A ((x₀, 0), σ)) z - lam₁ / 2 * Bf x₀ z := by
      obtain ⟨hΛx, hBx⟩ := hev.self_of_nhds (A ((x₀, 0), σ)) z
      have hJdom := hdomR1 _ hm₀
      have hcoord : A ((x₀, 0), σ) = coordP x₀ x₀ (D.partialDeriv (Fin.last (2 * p)) (t₀ + 0) x₀
          (covJet g 0 s (2 * p) (v (t₀ + 0) + σ • (u (t₀ + 0) - v (t₀ + 0))) x₀)) := by
        rw [hA, D.coordP_partialDeriv_segment (mem_jetBase_self 0 s (2 * p) x₀)
          ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩ hJdom]
      have hL : LegendreAt g 0 s p x₀ (D.principal (t₀ + 0) x₀
          (covJet g 0 s (2 * p) (v (t₀ + 0) + σ • (u (t₀ + 0) - v (t₀ + 0))) x₀)) lam₁ := by
        rw [hJ₀ x₀ σ, add_zero]
        exact hL₁
      have key := hL.2 ((trivAt I M 0 (s + p) x₀).symmL ℝ x₀ z)
      rw [D.principal_eq_fibMap (mem_jetBase_self 0 s (2 * p) x₀), ← hcoord, hΛx, hBx] at key
      have hBpos : 0 < Bf x₀ z := by
        rw [← hBx]
        refine (Tensor.TensorRSRiemannianBundle.tensorRSRiemannianMetric (I := I) (M := M) g 0
          (s + p)).pos x₀ _ fun h0 => ?_
        have h1 := congrArg ((trivAt I M 0 (s + p) x₀).continuousLinearMapAt ℝ x₀) h0
        rw [Trivialization.continuousLinearMapAt_symmL _ (mem_baseSet_trivializationAt _ _ x₀),
          map_zero] at h1
        rw [h1, norm_zero] at hz1
        exact zero_ne_one hz1
      nlinarith [mul_pos hlam₁ hBpos]
    filter_upwards [eventually_nhdsWithin_iff.mp
      (hGc.preimage_mem_nhdsWithin (Ioi_mem_nhds hpos))] with w hw hwR
    have := hw hwR
    simp only [mem_Ioi] at this
    linarith
  have hLegEv := (isCompact_Icc.prod
    (isCompact_sphere (0 : TensorRSModel 0 (s + p) ℝ E) 1)).eventually_forall_of_forall_eventually
    (P := fun q w => (q, w.1) ∈ R1 →
      lam₁ / 2 * Bf q.1 w.2 < (-1) ^ (p + 1) * Λ q.1 (A (q, w.1)) w.2) hstep2
  /- Step 3: a product neighbourhood of `(x₀, 0)`. -/
  have hall : ∀ᶠ q : M × ℝ in 𝓝 (x₀, 0), q ∈ O ∧
      (∀ w ∈ Icc (0 : ℝ) 1 ×ˢ Metric.sphere (0 : TensorRSModel 0 (s + p) ℝ E) 1,
        (q, w.1) ∈ R1 → lam₁ / 2 * Bf q.1 w.2 < (-1) ^ (p + 1) * Λ q.1 (A (q, w.1)) w.2) ∧
      (∀ Q z, legendreForm g 0 s p q.1 ((fibMap I (s + 2 * p) s x₀ q.1 Q).comp
          (EquationData.castIdx (r := 0) (by omega : s + p + p = s + 2 * p)
            q.1).toContinuousLinearMap)
          ((trivAt I M 0 (s + p) x₀).symmL ℝ q.1 z) ((trivAt I M 0 (s + p) x₀).symmL ℝ q.1 z) =
            Λ q.1 Q z ∧
        fiberInner g 0 (s + p) q.1 ((trivAt I M 0 (s + p) x₀).symmL ℝ q.1 z)
          ((trivAt I M 0 (s + p) x₀).symmL ℝ q.1 z) = Bf q.1 z) ∧
      q.1 ∈ jetBase (I := I) 0 s (2 * p) x₀ :=
    Filter.Eventually.and (hOo.mem_nhds hO0) (hLegEv.and
      (((continuous_fst.tendsto (x₀, (0 : ℝ))).eventually hev).and
        ((continuous_fst.tendsto (x₀, (0 : ℝ))).eventually
          ((isOpen_jetBase 0 s (2 * p) x₀).mem_nhds (mem_jetBase_self 0 s (2 * p) x₀)))))
  obtain ⟨N, hN, V, hV, hNV⟩ := mem_nhds_prod_iff.mp hall
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨lam₁ / 2, half_pos hlam₁, N, hN, ε / 2, half_pos hε, fun y hy τ hτ hτT σ hσ => ?_⟩
  have hτV : τ ∈ V := hεV (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hτ.1]
    linarith [hτ.2])
  obtain ⟨hqO, hqLeg, hqev, hqJ⟩ := hNV (mk_mem_prod hy hτV)
  have hmR1 : ((y, τ), σ) ∈ R1 := ⟨mk_mem_prod (mk_mem_prod hqJ ⟨hτ.1, hτT⟩) hσ,
    mk_mem_prod hqO (mem_univ _)⟩
  have hdomJ := hdomR1 _ hmR1
  refine ⟨hdomJ, half_pos hlam₁, fun ξ => ?_⟩
  have hcoord : A ((y, τ), σ) = coordP x₀ y (D.partialDeriv (Fin.last (2 * p)) (t₀ + τ) y
      (covJet g 0 s (2 * p) (v (t₀ + τ) + σ • (u (t₀ + τ) - v (t₀ + τ))) y)) := by
    rw [hA, D.coordP_partialDeriv_segment hqJ
      ⟨by linarith [ht₀.1, hτ.1], by linarith [hτT]⟩ hdomJ]
  rw [D.principal_eq_fibMap hqJ, ← hcoord]
  have hyb : y ∈ (trivAt I M 0 (s + p) x₀).baseSet :=
    mem_iInter.mp hqJ.2 ⟨p, by omega⟩
  have hξ : ξ = (trivAt I M 0 (s + p) x₀).symmL ℝ y
      ((trivAt I M 0 (s + p) x₀).continuousLinearMapAt ℝ y ξ) :=
    (Trivialization.symmL_continuousLinearMapAt _ hyb ξ).symm
  by_cases hz0 : (trivAt I M 0 (s + p) x₀).continuousLinearMapAt ℝ y ξ = 0
  · rw [hz0, map_zero] at hξ
    subst hξ
    rw [show (0 : TensorRSSpace 0 (s + p) I y) = (0 : ℝ) • (0 : TensorRSSpace 0 (s + p) I y) from
      (zero_smul ℝ _).symm, legendreForm_smul_smul, fiberInner_smul_smul]
    simp
  · set z := (trivAt I M 0 (s + p) x₀).continuousLinearMapAt ℝ y ξ with hz
    have hzh : ‖z‖⁻¹ • z ∈ Metric.sphere (0 : TensorRSModel 0 (s + p) ℝ E) 1 := by
      rw [mem_sphere_zero_iff_norm]
      exact norm_smul_inv_norm hz0
    have hlt : lam₁ / 2 * fiberInner g 0 (s + p) y
          ((trivAt I M 0 (s + p) x₀).symmL ℝ y (‖z‖⁻¹ • z))
          ((trivAt I M 0 (s + p) x₀).symmL ℝ y (‖z‖⁻¹ • z)) <
        (-1) ^ (p + 1) * legendreForm g 0 s p y ((fibMap I (s + 2 * p) s x₀ y (A ((y, τ), σ))).comp
          (EquationData.castIdx (r := 0) (by omega : s + p + p = s + 2 * p) y).toContinuousLinearMap)
          ((trivAt I M 0 (s + p) x₀).symmL ℝ y (‖z‖⁻¹ • z))
          ((trivAt I M 0 (s + p) x₀).symmL ℝ y (‖z‖⁻¹ • z)) := by
      have h1 := hqLeg (σ, ‖z‖⁻¹ • z) ⟨hσ, hzh⟩ hmR1
      obtain ⟨hΛy, hBy⟩ := hqev (A ((y, τ), σ)) (‖z‖⁻¹ • z)
      dsimp only at h1 hΛy hBy
      rw [hΛy, hBy]
      exact h1
    have hξ' : ξ = ‖z‖ • (trivAt I M 0 (s + p) x₀).symmL ℝ y (‖z‖⁻¹ • z) := by
      rw [← map_smul, smul_inv_smul₀ (norm_ne_zero_iff.mpr hz0)]
      exact hξ
    rw [hξ', legendreForm_smul_smul, fiberInner_smul_smul]
    have hn : 0 < ‖z‖ ^ 2 := by positivity
    exact mul_le_mul_of_lt_aux hn hlt

/-- **The segment between the jets stays parabolic** (tube lemma, `lem:legendre-basic` (iii)). If
two parabolic solutions agree at `t₀ < T`, then for a short time the jets on the segment between them
lie in the domain and satisfy the Legendre condition with a uniform constant. -/
theorem exists_parabolic_segment {u₀ u₀' : SmoothCcTensor g 0 s} {T : ℝ}
    {u v : ℝ → SmoothCcTensor g 0 s}
    (hu : D.IsParabolicSolution g u₀ T u) (hv : D.IsParabolicSolution g u₀' T v)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico 0 T) (h : u t₀ = v t₀) :
    ∃ η > 0, t₀ + η ≤ T ∧ ∃ lam > 0, ∀ t ∈ Icc t₀ (t₀ + η), ∀ x : M, ∀ σ ∈ Icc (0 : ℝ) 1,
      covJet g 0 s (2 * p) (v t + σ • (u t - v t)) x ∈ D.dom t x ∧
        LegendreAt g 0 s p x
          (D.principal t x (covJet g 0 s (2 * p) (v t + σ • (u t - v t)) x)) lam := by
  classical
  choose lamf hlamf Nf hNf εf hεf hgood using fun x₀ => D.tube_local g hu hv ht₀ h x₀
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover Nf fun x _ => hNf x
  set η := (insert (T - t₀) (t.image εf)).min' (Finset.insert_nonempty _ _) with hη
  set lam := (insert 1 (t.image lamf)).min' (Finset.insert_nonempty _ _) with hlam
  have hηpos : 0 < η := by
    rw [hη, Finset.lt_min'_iff]
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · linarith [ht₀.2]
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp ha
      exact hεf x
  have hlampos : 0 < lam := by
    rw [hlam, Finset.lt_min'_iff]
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact one_pos
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp ha
      exact hlamf x
  have hηT : η ≤ T - t₀ := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  refine ⟨η, hηpos, by linarith, lam, hlampos, fun t' ht' x σ hσ => ?_⟩
  obtain ⟨x₀, hx₀t, hx⟩ : ∃ x₀ ∈ t, x ∈ Nf x₀ := by
    simpa using ht (mem_univ x)
  have hηle : η ≤ εf x₀ :=
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hx₀t))
  have hlamle : lam ≤ lamf x₀ :=
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hx₀t))
  have hgood' := hgood x₀ x hx (t' - t₀) ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
    (by linarith [ht'.2]) σ hσ
  rw [add_sub_cancel] at hgood'
  exact ⟨hgood'.1, LegendreAt.mono g hgood'.2 hlampos hlamle⟩

end EquationData

end ShortTime
