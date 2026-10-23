import ShortTime.Linear.RicciEstimate

/-!
# Jet operators: exact Ricci identities, algebra (towards `rem:rewrite`)

A `JetOp s c n` is a map `u ↦ D u` from `T⁰_s`-sections to `T⁰_c`-sections of the form
`D u = ∑_{k ≤ n} Q_k (∇^k u)` with smooth bundle maps `Q_k`. These are closed under sums, negation,
permuting the output slots (`JetOp.perm`) and applying `∇` (`JetOp.covGrad`, order `+1`).
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff BigOperators

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]
variable {g : SmoothRiemannianMetric I M}

/-! ### Pointwise facts about `T⁰_s`-sections -/

theorem zeroTensor_eq_smul_unitTensor' (x : M) (D : Tensor0SSpace 0 I x) :
    D = (Tensor0SNabla.tensor0Iso I M x D) • unitTensor (I := I) (M := M) x := by
  classical
  have hunit : Tensor0SNabla.tensor0Iso I M x (unitTensor (I := I) (M := M) x) = (1 : ℝ) := by
    have h := Tensor0SNabla.scalarFn_unitZero (I := I) (M := M)
    have hx := congrFun h x
    change Tensor0SNabla.tensor0Iso I M x (unitTensor (I := I) (M := M) x) = 1 at hx
    exact hx
  apply (Tensor0SNabla.tensor0Iso I M x).injective
  rw [map_smul, hunit, smul_eq_mul, mul_one]

theorem clm_ext_unit' {s : ℕ} {x : M}
    {φ ψ : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x}
    (h : φ (unitTensor (I := I) (M := M) x) = ψ (unitTensor (I := I) (M := M) x)) :
    φ = ψ := by
  classical
  ext D
  rw [zeroTensor_eq_smul_unitTensor' (I := I) (M := M) x D, map_smul, map_smul, h]

/-- A `T⁰_s`-section is determined at `x` by its `unitModel` at `x`. -/
theorem toSection_eq_of_unitModel_eq {s : ℕ} {S S' : SmoothCcTensor g 0 s} (x : M)
    (h : unitModel (I := I) (M := M) g s S x = unitModel (I := I) (M := M) g s S' x) :
    S.toSection x = S'.toSection x := by
  have hval : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
      (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S'.toSection x)
        (unitTensor (I := I) (M := M) x) := by
    apply Tensor0SSpace.toModel_injective
    simpa [unitModel] using h
  exact clm_ext_unit' hval

theorem domDomCongrSection_toSection_congr {s : ℕ} (σ : Equiv.Perm (Fin s))
    {S S' : SmoothCcTensor g 0 s} (x : M) (h : S.toSection x = S'.toSection x) :
    (domDomCongrSection (I := I) g σ S).toSection x =
      (domDomCongrSection (I := I) g σ S').toSection x := by
  apply toSection_eq_of_unitModel_eq
  rw [domDomCongrSection_unitModel, domDomCongrSection_unitModel]
  congr 1
  simp only [unitModel, h]

theorem domDomCongrSection_add' {a : ℕ} (σ : Equiv.Perm (Fin a)) (A B : SmoothCcTensor g 0 a) :
    domDomCongrSection (I := I) g σ (A + B) =
      domDomCongrSection (I := I) g σ A + domDomCongrSection (I := I) g σ B := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g (fun x => ?_)
  rw [unitModel_add, domDomCongrSection_unitModel, domDomCongrSection_unitModel,
    domDomCongrSection_unitModel, unitModel_add]
  ext v
  simp only [ContinuousMultilinearMap.domDomCongr_apply, add_apply]

theorem domDomCongrSection_smul' {a : ℕ} (σ : Equiv.Perm (Fin a)) (k : ℝ)
    (A : SmoothCcTensor g 0 a) :
    domDomCongrSection (I := I) g σ (k • A) = k • domDomCongrSection (I := I) g σ A := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g (fun x => ?_)
  rw [unitModel_smul, domDomCongrSection_unitModel, domDomCongrSection_unitModel,
    unitModel_smul]
  ext v
  simp only [ContinuousMultilinearMap.domDomCongr_apply, smul_apply]

theorem domDomCongrSection_neg' {a : ℕ} (σ : Equiv.Perm (Fin a)) (A : SmoothCcTensor g 0 a) :
    domDomCongrSection (I := I) g σ (-A) = -domDomCongrSection (I := I) g σ A := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g (fun x => ?_)
  rw [unitModel_neg, domDomCongrSection_unitModel, domDomCongrSection_unitModel, unitModel_neg]
  ext v
  simp only [ContinuousMultilinearMap.domDomCongr_apply, neg_apply]

theorem domDomCongrSection_zero' {a : ℕ} (σ : Equiv.Perm (Fin a)) :
    domDomCongrSection (I := I) g σ (0 : SmoothCcTensor g 0 a) = 0 := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g (fun x => ?_)
  rw [unitModel_zero, domDomCongrSection_unitModel, unitModel_zero]
  ext v
  simp only [ContinuousMultilinearMap.domDomCongr_apply, zero_apply]

/-! ### Hom fields: linearity in the argument -/

theorem homApply_add_right {a c : ℕ} (Q : HomTensorRSField (E := E) (M := M) 0 a c I)
    (W₁ W₂ : SmoothCcTensor g 0 a) :
    homTensorRSFieldApply (I := I) (M := M) g 0 a c Q (W₁ + W₂) =
      homTensorRSFieldApply (I := I) (M := M) g 0 a c Q W₁ +
        homTensorRSFieldApply (I := I) (M := M) g 0 a c Q W₂ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_add (S := _), ContMDiffSection.coe_add, Pi.add_apply,
    homTensorRSFieldApply_toSection, homTensorRSFieldApply_toSection, homTensorRSFieldApply_toSection,
    SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply, map_add]

theorem homApply_smul_right {a c : ℕ} (Q : HomTensorRSField (E := E) (M := M) 0 a c I)
    (k : ℝ) (W : SmoothCcTensor g 0 a) :
    homTensorRSFieldApply (I := I) (M := M) g 0 a c Q (k • W) =
      k • homTensorRSFieldApply (I := I) (M := M) g 0 a c Q W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
    homTensorRSFieldApply_toSection, homTensorRSFieldApply_toSection,
    SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply, map_smul]

theorem homApply_neg_left {a c : ℕ} (Q : HomTensorRSField (E := E) (M := M) 0 a c I)
    (W : SmoothCcTensor g 0 a) :
    homTensorRSFieldApply (I := I) (M := M) g 0 a c (-Q) W =
      -homTensorRSFieldApply (I := I) (M := M) g 0 a c Q W := by
  have h := homTensorRSFieldApply_sub_left (I := I) (M := M) g 0 a c 0 Q W
  rw [zero_sub, homTensorRSFieldApply_zero_left, zero_sub] at h
  exact h

/-- Composing a smooth bundle map with a permutation of the output slots is again a smooth
bundle map. -/
theorem exists_hom_domDomCongr {a c : ℕ} (Q : HomTensorRSField (E := E) (M := M) 0 a c I)
    (ρ : Equiv.Perm (Fin c)) :
    ∃ Q' : HomTensorRSField (E := E) (M := M) 0 a c I, ∀ W : SmoothCcTensor g 0 a,
      homTensorRSFieldApply (I := I) (M := M) g 0 a c Q' W =
        domDomCongrSection (I := I) g ρ (homTensorRSFieldApply (I := I) (M := M) g 0 a c Q W) := by
  obtain ⟨Θ, hΘ⟩ := exists_value_local_homTensorRSFieldApply (I := I) (M := M) g 0 a c
    (fun W => domDomCongrSection (I := I) g ρ (homTensorRSFieldApply (I := I) (M := M) g 0 a c Q W))
    (fun W₁ W₂ x => by
      rw [homApply_add_right, domDomCongrSection_add']
      rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply])
    (fun k W x => by
      rw [homApply_smul_right, domDomCongrSection_smul']
      rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply])
    (fun W₁ W₂ x h => by
      apply domDomCongrSection_toSection_congr
      rw [homTensorRSFieldApply_toSection, homTensorRSFieldApply_toSection, h])
  exact ⟨Θ, fun W => (hΘ W).symm⟩

/-! ### The class of jet operators -/

variable (g) in
/-- `JetOp g s n c D`: `D : T⁰_s → T⁰_c` is `u ↦ ∑ Q_j ∇^j u` with smooth bundle maps `Q_j`,
`j ≤ n` (a finite sum, generated by `zero`, `term`, `add`). -/
inductive JetOp (s : ℕ) : (n c : ℕ) → (SmoothCcTensor g 0 s → SmoothCcTensor g 0 c) → Prop
  | zero {n c : ℕ} : JetOp s n c (fun _ => 0)
  | term {n c : ℕ} (j : ℕ) (hj : j ≤ n) (Q : HomTensorRSField (E := E) (M := M) 0 (s + j) c I) :
      JetOp s n c (fun u =>
        homTensorRSFieldApply (I := I) (M := M) g 0 (s + j) c Q (iteratedCovGrad g 0 s j u))
  | add {n c : ℕ} {D₁ D₂ : SmoothCcTensor g 0 s → SmoothCcTensor g 0 c} :
      JetOp s n c D₁ → JetOp s n c D₂ → JetOp s n c (fun u => D₁ u + D₂ u)

namespace JetOp

variable {s n c : ℕ} {D D' : SmoothCcTensor g 0 s → SmoothCcTensor g 0 c}

theorem congr (h : JetOp g s n c D) (hD : ∀ u, D u = D' u) : JetOp g s n c D' := by
  have : D = D' := funext hD
  exact this ▸ h

theorem mono (h : JetOp g s n c D) {n' : ℕ} (hn : n ≤ n') : JetOp g s n' c D := by
  induction h with
  | zero => exact zero
  | term j hj Q => exact term j (hj.trans hn) Q
  | add _ _ ih1 ih2 => exact add ih1 ih2

theorem neg (h : JetOp g s n c D) : JetOp g s n c (fun u => -D u) := by
  induction h with
  | zero => exact zero.congr fun u => (neg_zero).symm
  | term j hj Q =>
    exact (term j hj (-Q)).congr fun u => homApply_neg_left _ _
  | add _ _ ih1 ih2 => exact (add ih1 ih2).congr fun u => (neg_add _ _).symm

theorem sub {D₂ : SmoothCcTensor g 0 s → SmoothCcTensor g 0 c} (h : JetOp g s n c D)
    (h₂ : JetOp g s n c D₂) : JetOp g s n c (fun u => D u - D₂ u) :=
  (add h h₂.neg).congr fun u => (sub_eq_add_neg _ _).symm

theorem perm (h : JetOp g s n c D) (ρ : Equiv.Perm (Fin c)) :
    JetOp g s n c (fun u => domDomCongrSection (I := I) g ρ (D u)) := by
  induction h with
  | zero => exact zero.congr fun u => (domDomCongrSection_zero' ρ).symm
  | term j hj Q =>
    obtain ⟨Q', hQ'⟩ := exists_hom_domDomCongr (g := g) Q ρ
    exact (term j hj Q').congr fun u => hQ' _
  | add _ _ ih1 ih2 => exact (add ih1 ih2).congr fun u => (domDomCongrSection_add' _ _ _).symm

/-- `∇` of a jet operator is a jet operator of order one higher. -/
theorem nabla (h : JetOp g s n c D) :
    JetOp g s (n + 1) (c + 1) (fun u => covGrad g 0 c (D u)) := by
  induction h with
  | zero => exact zero.congr fun u => (covGrad_zero g 0 _).symm
  | term j hj Q =>
    refine (add (term j (by omega) (homTensorRSCovGradSec (I := I) (M := M) g 0 (s + j) _ Q))
      (term (j + 1) (by omega) (slotInsertHomTensorRSField (I := I) (M := M) 0 (s + j) _ Q))).congr
      fun u => ?_
    rw [covGrad_homTensorRSFieldApply_eq, iteratedCovGrad_succ]
    rfl
  | add _ _ ih1 ih2 =>
    exact (add ih1 ih2).congr fun u => (covGrad_add g 0 _ _ _).symm

theorem iterNabla (h : JetOp g s n c D) :
    ∀ k : ℕ, JetOp g s (n + k) (c + k) (fun u => iteratedCovGrad g 0 c k (D u))
  | 0 => h.congr fun _ => (iteratedCovGrad_zero g 0 c _).symm
  | k + 1 => ((h.iterNabla k).nabla).congr fun u => (iteratedCovGrad_succ g 0 c k _).symm

end JetOp

end ShortTime
