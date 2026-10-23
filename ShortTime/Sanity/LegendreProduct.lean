import ShortTime.Sanity.PolyTrace
import ShortTime.Sanity.ProductCore

/-!
# The product structure satisfies the Legendre condition

Paper: Lemma `lem:legendre-examples` (a).

Let `E₁, …, E_p` be symmetric bilinear forms on `T*_xM` with `E_ℓ(ξ,ξ) ≥ e_ℓ |ξ|²_g`, `e_ℓ > 0`. The
coefficient `productCLM` is
`P(X) = (-1)^{p+1} Σ_{K,K'} ∏_ℓ E_ℓ(e^{K_ℓ}, e^{K'_ℓ}) X(e_K, e_{K'}, ·)`
(split ordering: the first `p` slots are paired with the last `p` slots), where `(e_a)` is the
`g`-orthonormal frame `tangentFrame` and `e^a = g(e_a, ·)`. `legendre_product` shows it satisfies
`LegendreAt` with constant `∏ e_ℓ`. For `E_ℓ = g^{-1}` one recovers `polyTrace`.

The coefficients are `c(K,K') = ∏_ℓ E_ℓ(e^{K_ℓ}, e^{K'_ℓ})`, multilinear in `(E_ℓ)`, times the
fixed maps `X ↦ X(e_K, e_{K'}, ·)`: this is the shape used to express `P` as a bundle map.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Elliptic
open scoped Manifold ContDiff BigOperators

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

variable (g : SmoothRiemannianMetric I M)

/-- The `g`-orthonormal coframe `e^a = g(e_a, ·)`. -/
def coframe (x : M) (a : Fin (Module.finrank ℝ (TangentSpace I x))) :
    TangentSpace I x →L[ℝ] ℝ :=
  g.inner x (tangentFrame g x a)

/-- The product coefficient (split ordering) built from bilinear forms `E_ℓ` on covectors. -/
def productCLM (r s p : ℕ) (x : M)
    (Ef : Fin p → (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] ℝ) :
    TensorRSSpace r (s + p + p) I x →L[ℝ] TensorRSSpace r s I x :=
  (-1 : ℝ) ^ (p + 1) • ∑ K : Fin p → Fin (Module.finrank ℝ (TangentSpace I x)),
    ∑ K' : Fin p → Fin (Module.finrank ℝ (TangentSpace I x)),
      (∏ l, Ef l (coframe g x (K l)) (coframe g x (K' l))) •
        (evalFirstCLM (s := s) p (fun i => tangentFrame g x (K' i))).comp
          (evalFirstCLM (s := s + p) p (fun i => tangentFrame g x (K i)))

/-- `productCLM` undoes prepending frame covectors:
`P(e^I ⊗ η) = (-1)^{p+1} Σ_{K'} ∏_ℓ E_ℓ(e^{I_ℓ}, e^{K'_ℓ}) η(e_{K'}, ·)`. -/
theorem productCLM_prepend {r s p : ℕ} {x : M}
    (Ef : Fin p → (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (K' : Fin p → Fin (Module.finrank ℝ (TangentSpace I x))) (η : TensorRSSpace r (s + p) I x) :
    productCLM g r s p x Ef (prependCovectors p (fun i => g.inner x (tangentFrame g x (K' i))) η) =
      (-1 : ℝ) ^ (p + 1) • ∑ K : Fin p → Fin (Module.finrank ℝ (TangentSpace I x)),
        (∏ l, Ef l (coframe g x (K' l)) (coframe g x (K l))) •
          evalFirst p (fun i => tangentFrame g x (K i)) η := by
  classical
  have h : ∀ K : Fin p → Fin (Module.finrank ℝ (TangentSpace I x)),
      (∏ i, g.inner x (tangentFrame g x (K' i)) (tangentFrame g x (K i))) =
        if K' = K then 1 else 0 := by
    intro K
    simp only [tangentFrame_inner]
    rw [Finset.prod_boole]
    simp [funext_iff]
  simp only [productCLM, smul_apply, sum_apply,
    ContinuousLinearMap.comp_apply, evalFirstCLM_apply, evalFirst_prependCovectors, h, ite_smul,
    one_smul, zero_smul]
  congr 1
  rw [Finset.sum_eq_single K']
  · refine Finset.sum_congr rfl fun K _ => ?_
    rw [if_pos rfl]
  · intro K _ hK
    refine Finset.sum_eq_zero fun K'' _ => ?_
    rw [if_neg (Ne.symm hK), ← evalFirstCLM_apply, map_zero, smul_zero]
  · intro hK
    exact absurd (Finset.mem_univ K') hK

/-- `fiberInner` on `T^0_s` as a bilinear form. -/
def prodFiberBilin (s : ℕ) (x : M) :
    TensorRSSpace 0 s I x →ₗ[ℝ] TensorRSSpace 0 s I x →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fiberInner g 0 s x)
    (fun v v' w => fiberInner_add_left g x v v' w)
    (fun c v w => by
      rw [fiberInner_symm g x (c • v) w, fiberInner_smul_right g 0 s x w v c,
        fiberInner_symm g x w v, smul_eq_mul])
    (fun v w w' => fiberInner_add_right g 0 s x v w w')
    (fun c v w => fiberInner_smul_right g 0 s x v w c)

theorem fiberBilin_apply (s : ℕ) (x : M) (v w : TensorRSSpace 0 s I x) :
    prodFiberBilin g s x v w = fiberInner g 0 s x v w := rfl

theorem fiberInner_self_nonneg (s : ℕ) (x : M) (v : TensorRSSpace 0 s I x) :
    0 ≤ fiberInner g 0 s x v v := by
  have h : fiberInner g 0 s x v v = riemannianFiberNormSq (I := I) (M := M) g 0 s x v :=
    (riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 s x v).symm
  rw [h]
  exact riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x v

/-- Matrix of `E_ℓ` in the orthonormal coframe. -/
def coMatrix {p : ℕ} {x : M}
    (Ef : Fin p → (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] ℝ) :
    Fin p → Matrix (Fin (Module.finrank ℝ (TangentSpace I x)))
      (Fin (Module.finrank ℝ (TangentSpace I x))) ℝ :=
  fun l => Matrix.of fun a a' => Ef l (coframe g x a) (coframe g x a')

theorem coframe_apply (x : M) (a b : Fin (Module.finrank ℝ (TangentSpace I x))) :
    coframe g x a (tangentFrame g x b) = if a = b then 1 else 0 :=
  tangentFrame_inner g x a b

/-- The Legendre form of the product coefficient is `(-1)^{p+1}` times the `pf` form of the
coframe matrices, evaluated on `ξ_I = ξ(e_I, ·)`. -/
theorem legendreForm_productCLM {s p : ℕ} {x : M}
    (Ef : Fin p → (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (ξ : TensorRSSpace 0 (s + p) I x) :
    legendreForm g 0 s p x (productCLM g 0 s p x Ef) ξ ξ =
      (-1 : ℝ) ^ (p + 1) * pf (coMatrix g Ef) (prodFiberBilin g s x)
        (fun I => evalFirst p (fun i => tangentFrame g x (I i)) ξ)
        (fun I => evalFirst p (fun i => tangentFrame g x (I i)) ξ) := by
  classical
  rw [legendreForm_eq]
  simp only [productCLM_prepend, fiberInner_smul_right, ← fiberBilin_apply, map_sum, map_smul,
    smul_eq_mul, pf, coMatrix, Matrix.of_apply, Finset.mul_sum, coframe]

/-- **Product structure** (`lem:legendre-examples` (a)). Let `E_ℓ` be symmetric bilinear forms on
covectors with `E_ℓ(ξ,ξ) ≥ e_ℓ |ξ|²_g`, `e_ℓ > 0`. Then the product coefficient `productCLM`
satisfies the Legendre condition with constant `∏ e_ℓ`. -/
theorem legendre_product {s p : ℕ} {x : M}
    (Ef : Fin p → (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (e : Fin p → ℝ) (he : ∀ l, 0 < e l)
    (hsymm : ∀ l ξ η, Ef l ξ η = Ef l η ξ)
    (hpos : ∀ l ξ, e l * ∑ a, (ξ (tangentFrame g x a)) ^ 2 ≤ Ef l ξ ξ) :
    LegendreAt g 0 s p x (productCLM g 0 s p x Ef) (∏ l, e l) := by
  classical
  refine ⟨Finset.prod_pos fun l _ => he l, fun ξ => ?_⟩
  have hH : ∀ l, (coMatrix g Ef l).IsHermitian := fun l => by
    ext i j
    simp [Matrix.conjTranspose_apply, coMatrix, hsymm l (coframe g x i)]
  have hE : ∀ l (c : Fin (Module.finrank ℝ (TangentSpace I x)) → ℝ),
      e l * ∑ a, c a * c a ≤ ∑ a, ∑ a', c a * coMatrix g Ef l a a' * c a' := by
    intro l c
    have hξ : ∀ b, (∑ a, c a • coframe g x a) (tangentFrame g x b) = c b := by
      intro b
      simp [coframe_apply]
    have h := hpos l (∑ a, c a • coframe g x a)
    have hexp : Ef l (∑ a, c a • coframe g x a) (∑ a, c a • coframe g x a) =
        ∑ a, ∑ a', c a * coMatrix g Ef l a a' * c a' := by
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        coMatrix, Matrix.of_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => by
        rw [hsymm l (coframe g x a')]; ring
    rw [hexp] at h
    simpa only [hξ, sq] using h
  have key := pf_ge p (coMatrix g Ef) e (prodFiberBilin g s x) he hH hE
    (fun v w => fiberInner_symm g x v w) (fun v => fiberInner_self_nonneg g s x v)
    (fun I => evalFirst p (fun i => tangentFrame g x (I i)) ξ)
  rw [legendreForm_productCLM, ← mul_assoc, ← mul_pow, fiberInner_eq_sum_evalFirst g s x p ξ ξ]
  norm_num
  simpa [fiberBilin_apply] using key

end ShortTime
