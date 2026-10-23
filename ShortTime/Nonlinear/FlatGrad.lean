import ShortTime.Nonlinear.Flat
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Permutation.Naturality
import DifferentialGeometry.Tensor.RSTensor.Coordinates.Field

/-!
# Lowering indices commutes with covariant derivatives

Paper: Lemma `lem:lowering`, the identity `∇^k(♭u) = σ_k ♭(∇^k u)`.

`flatCc` lowers all indices of a tensor field, `T^r_s → T⁰_{r+s}`. Since `♭` is parallel
(`loweringIntertwinerRS_holds`), one covariant derivative gives `∇(♭u) = σ ♭(∇u)`, where the
cycle `σ` moves the new derivative slot in front of the `r` lowered slots
(`unitModel_covGrad_flatCc`). Covariant derivatives commute with slot relabellings
(`unitModel_covGrad_domDomCongr`), so by induction `∇^k(♭u) = σ_k ♭(∇^k u)` for the relabelling
`σ_k = jetPerm r s k : Fin (r + (s + k)) ≃ Fin ((r + s) + k)` (`covJet_flatCc`). The proofs
follow the library's `lowerCc_grad_rel` and `exists_iteratedCovGrad_unit_toModel_domDomCongr`.
-/

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open scoped Manifold ContDiff

set_option linter.unusedSectionVars false

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-! ### Slot relabellings -/

/-- Extend `e : Fin a ≃ Fin b` to `Fin (a + 1) ≃ Fin (b + 1)` fixing the first slot. -/
def succCongr {a b : ℕ} (e : Fin a ≃ Fin b) : Fin (a + 1) ≃ Fin (b + 1) :=
  (finSuccEquiv a).trans ((Equiv.optionCongr e).trans (finSuccEquiv b).symm)

@[simp] theorem succCongr_zero {a b : ℕ} (e : Fin a ≃ Fin b) : succCongr e 0 = 0 := by
  simp [succCongr]

@[simp] theorem succCongr_succ {a b : ℕ} (e : Fin a ≃ Fin b) (i : Fin a) :
    succCongr e i.succ = (e i).succ := by
  simp [succCongr]

/-- The cycle moving the slot `r` (the derivative slot of `♭(∇u)`) to the front. -/
def lowerGradPerm (r s : ℕ) : Equiv.Perm (Fin ((r + s) + 1)) :=
  Fin.cycleRange ⟨r, by omega⟩

/-- The relabelling `σ_k` with `∇^k(♭u) = σ_k ♭(∇^k u)`. -/
def jetPerm (r s : ℕ) : ∀ k : ℕ, Fin (r + (s + k)) ≃ Fin ((r + s) + k)
  | 0 => Equiv.refl _
  | k + 1 => (lowerGradPerm r (s + k)).trans (succCongr (jetPerm r s k))

theorem domDomCongr_trans {a b c : ℕ} (e₁ : Fin a ≃ Fin b) (e₂ : Fin b ≃ Fin c)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin a => E) ℝ) :
    A.domDomCongr (e₁.trans e₂) = (A.domDomCongr e₁).domDomCongr e₂ :=
  ContinuousMultilinearMap.ext fun _ => rfl

/-! ### Lowering tensor fields -/

variable (g : SmoothRiemannianMetric I M)

/-- **Lowering all indices** of a tensor field, `♭ : T^r_s → T⁰_{r+s}`. -/
def flatCc (r s : ℕ) (T : SmoothCcTensor g r s) : SmoothCcTensor g 0 (r + s) where
  toSection := Tensor0SField.toTensorRSField ∞
    (⟨liftedTensorSection (I := I) (M := M) g r s T.toSection,
      liftedTensorSection_contMDiff (I := I) (M := M) g r s T.toSection⟩ :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ (r + s))
  hasCompactSupport := HasCompactSupport.of_compactSpace _

theorem flatCc_apply {r s : ℕ} (T : SmoothCcTensor g r s) (x : M) :
    (flatCc g r s T).toSection x =
      Tensor0SSpace.toRS0 (liftedTensorSection (I := I) (M := M) g r s T.toSection x) :=
  Tensor0SField.toRS0_eq ∞ _ x

theorem flatCc_unit {r s : ℕ} (T : SmoothCcTensor g r s) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (r + s) I x from (flatCc g r s T).toSection x)
        (unitZeroSec (I := I) (M := M) x) =
      liftedTensorSection (I := I) (M := M) g r s T.toSection x := by
  rw [flatCc_apply, Tensor0SSpace.toRS0_apply, Tensor0SSpace.evalScalar_apply, unitZeroSec_apply]
  change ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) 1 Fin.elim0 • _ = _
  rw [ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]

theorem unitModel_flatCc {r s : ℕ} (T : SmoothCcTensor g r s) (x : M) :
    unitModel (I := I) (M := M) g (r + s) (flatCc g r s T) x =
      lowerAllUpperIndices (I := I) (M := M) g r s x (TensorRSSpace.toModel (T.toSection x)) := by
  rw [unitModel, show unitTensor (I := I) (M := M) x = unitZeroSec (I := I) (M := M) x from rfl,
    flatCc_unit, toModel_liftedTensorSection]

/-- `unitModel` is the `n`-form of the model value. -/
theorem unitEquiv_toModel {n : ℕ} (W : SmoothCcTensor g 0 n) (x : M) :
    unitEquiv E n (TensorRSSpace.toModel (W.toSection x)) = unitModel (I := I) (M := M) g n W x := by
  rw [unitEquiv_apply, unitModel, toModel_tensorRS_apply, unitTensor, Tensor0SSpace.toModel_ofModel]
  rfl

theorem rsToModel_injective {r s : ℕ} {x : M} :
    Function.Injective (TensorRSSpace.toModel (I := I) (r := r) (s := s) (x := x)) :=
  (tensorRSSpaceContinuousLinearEquiv (I := I) r s x).injective

/-- On a covariant fibre, a tensor is determined by its `n`-form. -/
theorem eq_of_unitEquiv_toModel_eq {n : ℕ} {x : M} {v w : TensorRSSpace 0 n I x}
    (h : unitEquiv E n (TensorRSSpace.toModel v) = unitEquiv E n (TensorRSSpace.toModel w)) :
    v = w :=
  rsToModel_injective ((unitEquiv E n).injective h)

/-- `flatCc` is the fibrewise lowering `flat`. -/
theorem flatCc_toSection {r s : ℕ} (T : SmoothCcTensor g r s) (x : M) :
    (flatCc g r s T).toSection x = flat g r s x (T.toSection x) := by
  refine eq_of_unitEquiv_toModel_eq ?_
  rw [unitEquiv_toModel, unitModel_flatCc, toModel_flat, unitEquiv_flatModel]

/-! ### One covariant derivative -/

/-- The model value of `∇_v W` evaluated at the unit scalar (the library's private
`covDerivUnitModel`). -/
def covDerivUM {s : ℕ} (W : SmoothCcTensor g 0 s) (x : M) (v : TangentSpace I x) :
    Tensor0SModel s ℝ E :=
  Tensor0SSpace.toModel
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      tensorCovDerivAt (I := I) (M := M) g 0 s W x (tangentSpaceModelContinuousLinearEquiv (I := I) x v))
      (unitTensor (I := I) (M := M) x))

theorem unitModel_covGrad_apply {s : ℕ} (W : SmoothCcTensor g 0 s) (x : M)
    (v : Fin (s + 1) → E) :
    unitModel (I := I) (M := M) g (s + 1) (covGrad (I := I) (M := M) g 0 s W) x v =
      covDerivUM g W x (v 0) (Matrix.vecTail v) := by
  unfold unitModel covDerivUM
  exact covGrad_toSection_apply_eval (I := I) (M := M) g 0 s W x (unitTensor (I := I) (M := M) x) v

theorem covDerivUM_domDomCongr {a : ℕ} (e : Equiv.Perm (Fin a)) (A B : SmoothCcTensor g 0 a)
    (h : ∀ y : M, unitModel (I := I) (M := M) g a B y =
      (unitModel (I := I) (M := M) g a A y).domDomCongr e) (x : M) (v : TangentSpace I x) :
    covDerivUM g B x v = (covDerivUM g A x v).domDomCongr e :=
  tensorCovDerivAt_unit_toModel_domDomCongr_of_section (I := I) (M := M) g a e A B h x v

/-- Covariant derivatives commute with slot relabellings: if `B = e·A` then `∇B = e'·∇A`, where
`e' = succCongr e` fixes the new first slot. -/
theorem unitModel_covGrad_domDomCongr {a b : ℕ} (e : Fin a ≃ Fin b)
    (A : SmoothCcTensor g 0 a) (B : SmoothCcTensor g 0 b)
    (h : ∀ y : M, unitModel (I := I) (M := M) g b B y =
      (unitModel (I := I) (M := M) g a A y).domDomCongr e) (x : M) :
    unitModel (I := I) (M := M) g (b + 1) (covGrad (I := I) (M := M) g 0 b B) x =
      (unitModel (I := I) (M := M) g (a + 1) (covGrad (I := I) (M := M) g 0 a A) x).domDomCongr
        (succCongr e) := by
  obtain rfl : a = b := by simpa using Fintype.card_congr e
  refine ContinuousMultilinearMap.ext fun v => ?_
  rw [unitModel_covGrad_apply, ContinuousMultilinearMap.domDomCongr_apply, unitModel_covGrad_apply,
    covDerivUM_domDomCongr g e A B h x (v 0),
    ContinuousMultilinearMap.domDomCongr_apply]
  have hzero : v (succCongr e 0) = v 0 := by rw [succCongr_zero]
  have htail : (Matrix.vecTail fun k : Fin (a + 1) => v (succCongr e k)) =
      fun j : Fin a => Matrix.vecTail v (e j) := by
    funext j
    change v (succCongr e j.succ) = v (e j).succ
    rw [succCongr_succ]
  rw [hzero, htail]

/-- **One covariant derivative**: `∇(♭T) = σ·♭(∇T)`, with `σ = lowerGradPerm r s`. -/
theorem unitModel_covGrad_flatCc {r s : ℕ} (T : SmoothCcTensor g r s) (y : M) :
    unitModel (I := I) (M := M) g ((r + s) + 1) (covGrad (I := I) (M := M) g 0 (r + s) (flatCc g r s T))
        y =
      (unitModel (I := I) (M := M) g ((r + s) + 1)
        (flatCc g r (s + 1) (covGrad (I := I) (M := M) g r s T)) y).domDomCongr (lowerGradPerm r s) := by
  classical
  refine ContinuousMultilinearMap.ext fun v => ?_
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  unfold unitModel
  rw [show unitTensor (I := I) (M := M) y = unitZeroSec (I := I) (M := M) y from rfl,
    covGrad_toSection_apply_eval (I := I) (M := M) g 0 (r + s) (flatCc g r s T) y, tensorCovDerivAt_def,
    tensorRSCovariantDerivative_zeroS_unit_eval (I := I) (M := M) g (r + s) (flatCc g r s T).toSection y]
  have hsec : (fun z : M =>
      (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace (r + s) I z from (flatCc g r s T).toSection z)
        (unitZeroSec (I := I) (M := M) z)) =
      fun z : M => liftedTensorSection (I := I) (M := M) g r s T.toSection z :=
    funext fun z => flatCc_unit g T z
  rw [hsec]
  change Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g r s T.toSection y (v 0))
      (Matrix.vecTail v) = _
  rw [loweredCovDerivAt_eq_lower_tensorCovDerivAt_rs (I := I) (M := M) g r s T.toSection y (v 0),
    flatCc_unit, toModel_liftedTensorSection, lowerAllUpperIndices_apply, lowerAllUpperIndices_apply]
  have hcg (Dm : Tensor0SModel r ℝ E) (u : Fin (s + 1) → E) :
      TensorRSSpace.toModel ((covGrad (I := I) (M := M) g r s T).toSection y) Dm u =
        TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g r s T y (u 0)) Dm
          (Matrix.vecTail u) := by
    change Tensor0SSpace.toModel
        ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace (s + 1) I y from
          (covGrad (I := I) (M := M) g r s T).toSection y) (Tensor0SSpace.ofModel Dm)) u =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from
          tensorCovDerivAt (I := I) (M := M) g r s T y (u 0)) (Tensor0SSpace.ofModel Dm))
        (Matrix.vecTail u)
    exact covGrad_toSection_apply_eval (I := I) (M := M) g r s T y (Tensor0SSpace.ofModel Dm) u
  rw [hcg]
  have hupper : (fun a : Fin r => v (lowerGradPerm r s (Fin.castAdd (s + 1) a))) =
      fun a : Fin r => Matrix.vecTail v (Fin.castAdd s a) := by
    funext a
    have hidx : lowerGradPerm r s (Fin.castAdd (s + 1) a) = (Fin.castAdd s a).succ := by
      apply Fin.ext
      simp only [lowerGradPerm, Fin.val_succ, Fin.val_castAdd]
      rw [Fin.coe_cycleRange_of_lt (by rw [Fin.lt_def]; simp)]
      simp only [Fin.val_castAdd]
    exact congrArg v hidx
  have hdir : lowerGradPerm r s (Fin.natAdd r (0 : Fin (s + 1))) = 0 := by
    rw [lowerGradPerm,
      show Fin.natAdd r (0 : Fin (s + 1)) = (⟨r, by omega⟩ : Fin ((r + s) + 1)) from by ext; simp,
      Fin.cycleRange_self]
  have hlower : (fun a : Fin s => v (lowerGradPerm r s (Fin.natAdd r a.succ))) =
      fun a : Fin s => Matrix.vecTail v (Fin.natAdd r a) := by
    funext a
    have hidx : lowerGradPerm r s (Fin.natAdd r a.succ) = (Fin.natAdd r a).succ := by
      rw [lowerGradPerm, Fin.cycleRange_of_gt
        (by simp only [Fin.lt_def, Fin.val_natAdd, Fin.val_succ]; omega)]
      ext
      simp only [Fin.val_natAdd, Fin.val_succ]
      omega
    exact congrArg v hidx
  rw [hupper, hdir]
  congr 1
  exact hlower.symm

/-! ### Iterated covariant derivatives -/

/-- `∇^k(♭T) = σ_k·♭(∇^k T)`, on `n`-forms. -/
theorem unitModel_iteratedCovGrad_flatCc {r s : ℕ} (T : SmoothCcTensor g r s) (k : ℕ) (y : M) :
    unitModel (I := I) (M := M) g ((r + s) + k) (iteratedCovGrad g 0 (r + s) k (flatCc g r s T)) y =
      (unitModel (I := I) (M := M) g (r + (s + k))
        (flatCc g r (s + k) (iteratedCovGrad g r s k T)) y).domDomCongr (jetPerm r s k) := by
  induction k generalizing y with
  | zero => exact (ContinuousMultilinearMap.ext fun _ => rfl)
  | succ k ih =>
    change unitModel (I := I) (M := M) g ((r + s) + k + 1)
        (covGrad (I := I) (M := M) g 0 ((r + s) + k) (iteratedCovGrad g 0 (r + s) k (flatCc g r s T)))
        y = _
    rw [unitModel_covGrad_domDomCongr g (jetPerm r s k) _ _ ih y,
      unitModel_covGrad_flatCc g (iteratedCovGrad g r s k T) y, ← domDomCongr_trans]
    rfl

/-- **Lowering commutes with covariant jets**: the `k`-th component of the jet of `♭T` is
`σ_k ♭` of the `k`-th component of the jet of `T`. -/
theorem covJet_flatCc {r s : ℕ} (N : ℕ) (T : SmoothCcTensor g r s) (x : M) (k : Fin (N + 1)) :
    covJet g 0 (r + s) N (flatCc g r s T) x k =
      slotPerm I (jetPerm r s k) x (flat g r (s + k) x (covJet g r s N T x k)) := by
  refine eq_of_unitEquiv_toModel_eq ?_
  rw [covJet, covJet, unitEquiv_toModel, unitModel_iteratedCovGrad_flatCc, toModel_slotPerm,
    unitEquiv_permModel, toModel_flat, unitEquiv_flatModel, unitModel_flatCc]

end ShortTime
