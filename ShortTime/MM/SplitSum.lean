import ShortTime.MM.Data

/-!
# The split-ordered contraction in an arbitrary dual basis

`productCLM` (the split pairing: slots `(ℓ, p+ℓ)` paired) is a metric-free contraction too:
`productCLM_castIdx_eq_splitFrameSum` and `splitFrameSum_eq_splitFrameSum`. They mirror the interleaved
case of `PairingBasis`, with the slot equivalence `(ℓ,c) ↦ ℓ + c p` in place of `(ℓ,c) ↦ 2ℓ + c`.
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

/-- The slots `(ℓ, c)` as the positions `ℓ + c p` of `Fin (2p)`. -/
def splitEquiv (p : ℕ) : MMAlg.Slot p ≃ Fin (2 * p) where
  toFun q := ⟨q.1.val + q.2.val * p, by
    have := q.1.isLt; have := q.2.isLt
    have : q.2.val * p ≤ p := by
      calc q.2.val * p ≤ 1 * p := Nat.mul_le_mul_right _ (by omega)
        _ = p := one_mul p
    omega⟩
  invFun m := (⟨m.val % p, Nat.mod_lt _ (by have := m.isLt; omega)⟩,
    ⟨m.val / p, by
      have hp : 0 < p := by have := m.isLt; omega
      rw [Nat.div_lt_iff_lt_mul hp]; have := m.isLt; omega⟩)
  left_inv q := by
    obtain ⟨⟨l, hl⟩, ⟨c, hc⟩⟩ := q
    ext
    · simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]
    · simp only [Nat.add_mul_div_right _ _ (show 0 < p by omega), Nat.div_eq_of_lt hl,
        zero_add]
  right_inv m := by
    ext
    simp only
    have := Nat.mod_add_div m.val p
    rw [Nat.mul_comm p] at this
    exact this

/-- Model-level multilinear form of a `2p`-tensor, slots indexed through `e`. -/
def phiOfE (p : ℕ) (e : MMAlg.Slot p ≃ Fin (2 * p)) (x : M) (ζ : TensorRSSpace 0 (0 + 2 * p) I x) :
    MultilinearMap ℝ (fun _ : MMAlg.Slot p => TangentSpace I x) ℝ :=
  ((Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2 * p) I x from ζ)
        (unitZeroSec (I := I) (M := M) x))).toMultilinearMap.compLinearMap
    (fun _ => (tangentSpaceModelContinuousLinearEquiv (I := I) x).toLinearEquiv.toLinearMap)).domDomCongr
    ((finCongr (Nat.zero_add (2 * p))).trans e.symm)

theorem lam_evalFirst_phiOfE (p : ℕ) (e : MMAlg.Slot p ≃ Fin (2 * p)) (x : M)
    (v : Fin (2 * p) → TangentSpace I x) (ζ : TensorRSSpace 0 (0 + 2 * p) I x) :
    lam x (evalFirst (r := 0) (s := 0) (2 * p) v ζ) = phiOfE p e x ζ (fun q => v (e q)) := by
  rw [lam_evalFirst]
  simp only [phiOfE, MultilinearMap.domDomCongr_apply, MultilinearMap.compLinearMap_apply]
  refine congrArg (fun f => Tensor0SSpace.toModel
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2 * p) I x from ζ)
      (unitZeroSec (I := I) (M := M) x)) f) (funext fun k => ?_)
  have hk := k.isLt
  simp only [appendIdx, dif_pos (show (k : ℕ) < 2 * p by omega), Equiv.trans_apply,
    Equiv.apply_symm_apply, LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv]
  rfl

/-- The split frame sum in an arbitrary pair of families `(b_i)`, `(b'_i)`. -/
def splitFrameSum (p : ℕ) (x : M)
    (Ef : Fin p → (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (b : Fin (Module.finrank ℝ (TangentSpace I x)) → TangentSpace I x)
    (b' : Fin (Module.finrank ℝ (TangentSpace I x)) → (TangentSpace I x →L[ℝ] ℝ))
    (ζ : TensorRSSpace 0 (0 + 2 * p) I x) : TensorRSSpace 0 0 I x :=
  (-1 : ℝ) ^ (p + 1) • ∑ K : Fin p → Fin (Module.finrank ℝ (TangentSpace I x)),
    ∑ K' : Fin p → Fin (Module.finrank ℝ (TangentSpace I x)),
      (∏ l, Ef l (b' (K l)) (b' (K' l))) •
        evalFirst (r := 0) (s := 0) (2 * p) (splitVec (fun i => b (K i)) (fun i => b (K' i))) ζ

theorem lam_splitFrameSum (p : ℕ) (x : M)
    (Ef : Fin p → (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (b : Fin (Module.finrank ℝ (TangentSpace I x)) → TangentSpace I x)
    (b' : Fin (Module.finrank ℝ (TangentSpace I x)) → (TangentSpace I x →L[ℝ] ℝ))
    (ζ : TensorRSSpace 0 (0 + 2 * p) I x) :
    lam x (splitFrameSum p x Ef b b' ζ) =
      (-1 : ℝ) ^ (p + 1) * MMAlg.contr (phiOfE p (splitEquiv p) x ζ) Ef b b' := by
  classical
  simp only [splitFrameSum, map_smul, map_sum, smul_eq_mul]
  congr 1
  rw [MMAlg.contr, ← Finset.sum_product']
  refine Fintype.sum_equiv (pairsEquiv p _) _ _ (fun KK => ?_)
  obtain ⟨K, K'⟩ := KK
  rw [lam_evalFirst_phiOfE p (splitEquiv p)]
  have h1 : (∏ l, Ef l (b' (K l)) (b' (K' l))) =
      ∏ l, Ef l (b' (pairsEquiv p _ (K, K') (l, 0))) (b' (pairsEquiv p _ (K, K') (l, 1))) := by
    simp [pairsEquiv]
  have h2 : (fun q => splitVec (fun i => b (K i)) (fun i => b (K' i)) (splitEquiv p q)) =
      fun q => b (pairsEquiv p _ (K, K') q) := by
    funext ⟨l, c⟩
    have hl := l.isLt
    fin_cases c
    · simp [splitVec, splitEquiv, pairsEquiv]
    · simp [splitVec, splitEquiv, pairsEquiv]
  rw [h2, h1]

/-- **Frame independence of the split contraction**, between two dual pairs. -/
theorem splitFrameSum_eq_splitFrameSum (p : ℕ) (x : M)
    (Ef : Fin p → (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (b₁ b₂ : Fin (Module.finrank ℝ (TangentSpace I x)) → TangentSpace I x)
    (b₁' b₂' : Fin (Module.finrank ℝ (TangentSpace I x)) → (TangentSpace I x →L[ℝ] ℝ))
    (h₁ : ∀ i j, b₁' i (b₁ j) = if i = j then 1 else 0)
    (h₂ : ∀ i j, b₂' i (b₂ j) = if i = j then 1 else 0)
    (ζ : TensorRSSpace 0 (0 + 2 * p) I x) :
    splitFrameSum p x Ef b₁ b₁' ζ = splitFrameSum p x Ef b₂ b₂' ζ := by
  have : NeZero (Module.finrank ℝ (TangentSpace I x)) :=
    inferInstanceAs (NeZero (Module.finrank ℝ E))
  apply lam_injective x
  rw [lam_splitFrameSum, lam_splitFrameSum]
  congr 1
  let ev : (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
    ContinuousLinearMap.coeLM ℝ
  have hW : ∀ w w' : (TangentSpace I x →L[ℝ] ℝ), (∀ v, ev w v = ev w' v) → w = w' :=
    fun w w' h => ContinuousLinearMap.ext h
  have hb₁ := MMAlg.isDual_of_dual rfl ev hW b₁ b₁' h₁
  have hb₂ := MMAlg.isDual_of_dual rfl ev hW b₂ b₂' h₂
  exact MMAlg.contr_indep hb₂ hb₁ _ _

variable (g : SmoothRiemannianMetric I M)

/-- The split pairing `productCLM` of a `2p`-tensor is the split frame sum in the orthonormal frame. -/
theorem productCLM_castIdx_eq_splitFrameSum (p : ℕ) (x : M)
    (Ef : Fin p → (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (ζ : TensorRSSpace 0 (0 + 2 * p) I x) :
    productCLM g 0 0 p x Ef (EquationData.castIdx (show 0 + 2 * p = 0 + p + p by omega) x ζ) =
      splitFrameSum p x Ef (tangentFrame g x) (coframe g x) ζ := by
  simp only [productCLM, splitFrameSum, smul_apply, sum_apply, ContinuousLinearMap.comp_apply,
    evalFirstCLM_apply]
  congr 1
  refine Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun K' _ => ?_
  congr 1
  exact evalFirst_split x p _ _ ζ

end ShortTime
