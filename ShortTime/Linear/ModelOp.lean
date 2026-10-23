import ShortTime.Linear.LinearTheorem
import ShortTime.Sanity.PolyTrace
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.Commutation.CovariantDivergence
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.Commutation.OperatorFieldApplication

/-!
# The polyharmonic model operator (`prop:model`, `lem:legendre-examples` (b))

The rough Laplacian of the library is `Δ_raw W = tr₁₂ ∇²W` (`rawTensorConnLapSmooth`, negative
semidefinite). Its `k`-th power is
`Δ_raw^k u = Φ_k(∇^{2k}u) + (order ≤ 2k - 1)` (`isDiffOp_lapIter_sub`), where
`Φ_k = DT_s ∘ DT_{s+2} ∘ ⋯ ∘ DT_{s+2k-2}` (`lapTop`) contracts the derivative slots in adjacent
pairs `(1,2), (3,4), …`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Spectral.DeTurck
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

/-- `Φ_k = DT_s ∘ DT_{s+2} ∘ ⋯ ∘ DT_{s+2k-2}`, the principal coefficient of `Δ_raw^k` before the
derivative slots are reordered. -/
def lapTop (s : ℕ) : ∀ k : ℕ, SmoothCcTensor g (s + 2 * k) s
  | 0 => permField g (Equiv.refl (Fin s))
  | k + 1 => ccOperatorFieldComp (I := I) (M := M) g (s + 2 * k + 2) (s + 2 * k) s (lapTop s k)
      (cometricDoubleTraceField (I := I) g (s + 2 * k))

variable {g}

theorem operatorFieldApply_lapTop_zero {s : ℕ} (W : SmoothCcTensor g 0 s) :
    operatorFieldApply (I := I) (M := M) g (s + 2 * 0) s (lapTop g s 0) W = W := by
  change operatorFieldApply (I := I) (M := M) g s s (permField g (1 : Equiv.Perm (Fin s))) W = W
  rw [operatorFieldApply_permField, domDomCongrSection_one]

theorem operatorFieldApply_lapTop_succ {s : ℕ} (k : ℕ) (W : SmoothCcTensor g 0 (s + 2 * (k + 1))) :
    operatorFieldApply (I := I) (M := M) g (s + 2 * (k + 1)) s (lapTop g s (k + 1)) W =
      operatorFieldApply (I := I) (M := M) g (s + 2 * k) s (lapTop g s k)
        (operatorFieldApply (I := I) (M := M) g (s + 2 * k + 2) (s + 2 * k)
          (cometricDoubleTraceField (I := I) g (s + 2 * k)) W) := by
  rw [operatorFieldApply_assoc]
  rfl

/-- One step: `∇²(Φ(∇^n u))` is `(slotExtend² Φ)(∇^{n+2}u)` plus an operator of order `n + 1`. -/
theorem isDiffOp_covGrad_two_field (S : Set ℝ) {s b : ℕ} (n : ℕ) (Φ : SmoothCcTensor g (s + n) b) :
    IsDiffOp (g := g) S (n + 1) (fun (_ : ℝ) (u : SmoothCcTensor g 0 s) =>
      iteratedCovGrad g 0 b 2 (operatorFieldApply (I := I) (M := M) g (s + n) b Φ
          (iteratedCovGrad g 0 s n u)) -
        operatorFieldApply (I := I) (M := M) g (s + n + 2) (b + 2)
          (slotExtend (I := I) (M := M) g (s + n + 1) (b + 1)
            (slotExtend (I := I) (M := M) g (s + n) b Φ))
          (iteratedCovGrad g 0 s (n + 2) u)) := by
  have h1 : IsDiffOp (g := g) S (n + 1) (fun (_ : ℝ) (u : SmoothCcTensor g 0 s) =>
      covGrad (I := I) (M := M) g 0 (b + 1) (operatorFieldApply (I := I) (M := M) g (s + n) (b + 1)
        (covGrad (I := I) (M := M) g (s + n) b Φ) (iteratedCovGrad g 0 s n u))) :=
    (IsDiffOp.field_grad (S := S) n (jointlySmoothOn_const g S (covGrad (I := I) (M := M) g (s + n) b Φ))).grad
  have h2 : IsDiffOp (g := g) S (n + 1) (fun (_ : ℝ) (u : SmoothCcTensor g 0 s) =>
      operatorFieldApply (I := I) (M := M) g (s + n + 1) (b + 2)
        (covGrad (I := I) (M := M) g (s + n + 1) (b + 1) (slotExtend (I := I) (M := M) g (s + n) b Φ))
        (iteratedCovGrad g 0 s (n + 1) u)) :=
    IsDiffOp.field_grad (S := S) (n + 1)
      (jointlySmoothOn_const g S (covGrad (I := I) (M := M) g (s + n + 1) (b + 1)
        (slotExtend (I := I) (M := M) g (s + n) b Φ)))
  refine (h1.add h2).congr' fun t u => ?_
  change _ = covGrad (I := I) (M := M) g 0 (b + 1) (covGrad (I := I) (M := M) g 0 b
      (operatorFieldApply (I := I) (M := M) g (s + n) b Φ (iteratedCovGrad g 0 s n u))) - _
  conv_rhs => rw [covGrad_operatorFieldApply_eq g (s + n) b Φ, covGrad_add,
    covGrad_operatorFieldApply_eq g (s + n + 1) (b + 1) (slotExtend (I := I) (M := M) g (s + n) b Φ)]
  rw [show covGrad (I := I) (M := M) g 0 (s + n + 1)
      (covGrad (I := I) (M := M) g 0 (s + n) (iteratedCovGrad g 0 s n u)) =
    iteratedCovGrad g 0 s (n + 2) u from rfl,
    show covGrad (I := I) (M := M) g 0 (s + n) (iteratedCovGrad g 0 s n u) =
    iteratedCovGrad g 0 s (n + 1) u from rfl]
  abel

/-- **`Δ_raw^k = Φ_k ∘ ∇^{2k} + (lower order)`**: the difference is an operator of order `2k - 1`. -/
theorem isDiffOp_lapIter_sub (S : Set ℝ) (s : ℕ) : ∀ k : ℕ,
    IsDiffOp (g := g) S (2 * k - 1) (fun (_ : ℝ) (u : SmoothCcTensor g 0 s) =>
      rawTensorConnLapIter (I := I) g 0 s k u -
        operatorFieldApply (I := I) (M := M) g (s + 2 * k) s (lapTop g s k)
          (iteratedCovGrad g 0 s (2 * k) u))
  | 0 => (IsDiffOp.zero (g := g) (S := S) (a := s) (b := s) 0).congr' fun t u => by
      rw [rawTensorConnLapIter_zero, operatorFieldApply_lapTop_zero]
      exact (sub_self u).symm
  | 1 => (IsDiffOp.zero (g := g) (S := S) (a := s) (b := s) 1).congr' fun t u => by
      rw [operatorFieldApply_lapTop_succ, operatorFieldApply_lapTop_zero, rawTensorConnLapIter_succ,
        rawTensorConnLapIter_zero, rawTensorConnLapSmooth_eq_operatorFieldApplication_cometricDoubleTrace_of_rank]
      exact (sub_self _).symm
  | k + 2 => by
    have ih := isDiffOp_lapIter_sub S s (k + 1)
    have hA := (isDiffOp_covGrad_two_field (g := g) S (2 * (k + 1)) (lapTop g s (k + 1))).comp_field
      (jointlySmoothOn_const g S (cometricDoubleTraceField (I := I) g s))
    have hB := (ih.iterGrad 2).comp_field
      (jointlySmoothOn_const g S (cometricDoubleTraceField (I := I) g s))
    refine ((hA.add hB).mono (by omega)).congr' fun t u => ?_
    rw [rawTensorConnLapIter_succ _ _ _ (k + 1),
      rawTensorConnLapSmooth_eq_operatorFieldApplication_cometricDoubleTrace_of_rank,
      operatorFieldApply_lapTop_succ (k + 1)]
    simp only [operatorFieldApplication_sub_right, iteratedCovGrad_sub]
    rw [cometricDoubleTrace_operatorFieldApplication_slotExtend_two_comm,
      show iteratedCovGrad g 0 s (2 * (k + 2)) u = iteratedCovGrad g 0 s (2 * (k + 1) + 2) u from rfl]
    abel

/-! ### The double trace in the orthonormal frame -/

theorem multilinear_cons_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (Z : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => E) ℝ) (α : ι → ℝ) (v : ι → E)
    (rest : Fin n → E) :
    Z (Fin.cons (∑ i, α i • v i) rest) = ∑ i, α i * Z (Fin.cons (v i) rest) := by
  rw [← ContinuousMultilinearMap.curryLeft_apply, map_sum]
  simp [ContinuousMultilinearMap.curryLeft_apply]

variable (g) in
theorem tangentFrame_linInd (x : M) : LinearIndependent ℝ (tangentFrame g x) := by
  rw [linearIndependent_iff']
  intro fs c hsum k hk
  have h0 : g.inner x (tangentFrame g x k) (∑ j ∈ fs, c j • tangentFrame g x j) = 0 := by
    rw [hsum]; simp
  rw [map_sum] at h0
  simp only [map_smul, smul_eq_mul, tangentFrame_inner, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, if_pos hk] at h0
  exact h0

variable (g) in
/-- `tangentFrame g x` as a basis of `T_xM`. -/
def frameBasis (x : M) : Module.Basis (Fin (Module.finrank ℝ (TangentSpace I x))) ℝ (TangentSpace I x) :=
  haveI : Nonempty (Fin (Module.finrank ℝ (TangentSpace I x))) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  basisOfLinearIndependentOfCardEqFinrank (tangentFrame_linInd g x) (by simp)

variable (g) in
theorem frameBasis_apply (x : M) (i) : frameBasis g x i = tangentFrame g x i := by
  simp [frameBasis]

variable (g) in
/-- Expansion in the orthonormal frame: `v = Σ_i g(v, e_i) e_i`. -/
theorem eq_sum_inner_tangentFrame (x : M) (v : TangentSpace I x) :
    v = ∑ i, g.inner x v (tangentFrame g x i) • tangentFrame g x i := by
  classical
  conv_lhs => rw [← (frameBasis g x).sum_repr v]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [frameBasis_apply]
  congr 1
  conv_rhs => rw [← (frameBasis g x).sum_repr v]
  simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, frameBasis_apply, tangentFrame_inner,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

variable (g) in
/-- **The double trace in the orthonormal frame**: `(tr₁₂ D)(m) = Σ_i D(e_i, e_i, m)`. -/
theorem toModel_doubleTrace (b : ℕ) (x : M) (D : Tensor0SSpace (b + 2) I x) (m : Fin b → E) :
    Tensor0SSpace.toModel ((show Tensor0SSpace (b + 2) I x →L[ℝ] Tensor0SSpace b I x from
        (cometricDoubleTraceField (I := I) g b).toSection x) D) m =
      ∑ i, Tensor0SSpace.toModel D
        (Fin.cons (toE (tangentFrame g x i)) (Fin.cons (toE (tangentFrame g x i)) m)) := by
  classical
  rw [show (show Tensor0SSpace (b + 2) I x →L[ℝ] Tensor0SSpace b I x from
      (cometricDoubleTraceField (I := I) g b).toSection x) D = cometricDoubleTraceFib g b x D from rfl,
    cometricDoubleTraceFib_toModel, modelDoubleTrace_apply]
  set Z := Tensor0SSpace.toModel D
  set f : Fin (Module.finrank ℝ (TangentSpace I x)) → E := fun i => toE (tangentFrame g x i) with hf
  set eb := Module.finBasis ℝ E
  -- the raised dual basis in the frame
  have hc : ∀ k, cometricLmodel (I := I) g x
      (Tensor0SBundle.modelCovectorOfCLM (𝕜 := ℝ) (E := E) (eb.cDualBasis k)) =
        ∑ i, eb.repr (f i) k • f i := by
    intro k
    refine (eq_sum_inner_tangentFrame g x _).trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [cometricLmodel_covectorOfCLM_inner]
    simp [Module.Basis.cDualBasis, hf, toE]
    rfl
  simp_rw [hc, multilinear_cons_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 := multilinear_cons_sum (Z.curryLeft (f i)) (fun k => eb.repr (f i) k) (fun k => eb k) m
  simp only [ContinuousMultilinearMap.curryLeft_apply, eb.sum_repr] at h2
  rw [h2]

/-! ### `Φ_k` in the orthonormal frame -/

/-- `(f_{K₀}, f_{K₀}, f_{K₁}, f_{K₁}, …, f_{K_{k-1}}, f_{K_{k-1}}, w)`. -/
def pairVec {N s : ℕ} (f : Fin N → E) (k : ℕ) (K : Fin k → Fin N) (w : Fin s → E) :
    Fin (s + 2 * k) → E :=
  fun j => if h : (j : ℕ) < 2 * k then f (K ⟨j / 2, by omega⟩) else w ⟨j - 2 * k, by omega⟩

theorem pairVec_zero {N s : ℕ} (f : Fin N → E) (K : Fin 0 → Fin N) (w : Fin s → E) :
    pairVec f 0 K w = w := by
  funext j
  simp [pairVec]

theorem pairVec_succ {N s : ℕ} (f : Fin N → E) (k : ℕ) (i : Fin N) (K : Fin k → Fin N)
    (w : Fin s → E) :
    pairVec f (k + 1) (Fin.cons i K) w =
      (Fin.cons (f i) (Fin.cons (f i) (pairVec f k K w)) : Fin (s + 2 * k + 1 + 1) → E) := by
  funext j
  rcases j with ⟨j, hj⟩
  rcases j with _ | _ | j
  · simp [pairVec]
  · simp only [pairVec]
    rw [dif_pos (by omega)]
    rfl
  · rw [show (⟨j + 1 + 1, hj⟩ : Fin (s + 2 * k + 1 + 1)) = (Fin.succ (Fin.succ ⟨j, by omega⟩)) from rfl,
      Fin.cons_succ, Fin.cons_succ]
    simp only [pairVec, Fin.val_succ]
    by_cases h : j < 2 * k
    · rw [dif_pos (by omega), dif_pos h]
      have : (⟨(j + 1 + 1) / 2, by omega⟩ : Fin (k + 1)) = Fin.succ ⟨j / 2, by omega⟩ :=
        Fin.ext (by simp; omega)
      rw [this, Fin.cons_succ]
    · rw [dif_neg (by omega), dif_neg h]
      congr 1
      exact Fin.ext (by simp; omega)

variable (g) in
/-- **`Φ_k` in the orthonormal frame**: `Φ_k(D)(w) = Σ_K D(e_{K₀}, e_{K₀}, …, e_{K_{k-1}}, e_{K_{k-1}}, w)`. -/
theorem toModel_lapTop (s : ℕ) (x : M) : ∀ (k : ℕ) (D : Tensor0SSpace (s + 2 * k) I x) (w : Fin s → E),
    Tensor0SSpace.toModel ((show Tensor0SSpace (s + 2 * k) I x →L[ℝ] Tensor0SSpace s I x from
        (lapTop g s k).toSection x) D) w =
      ∑ K : Fin k → Fin (Module.finrank ℝ (TangentSpace I x)),
        Tensor0SSpace.toModel D (pairVec (fun i => toE (tangentFrame g x i)) k K w)
  | 0, D, w => by
    rw [Fintype.sum_unique, pairVec_zero]
    change Tensor0SSpace.toModel (permFib I (Equiv.refl (Fin s)) x D) w = _
    rw [toModel_permFib, ContinuousMultilinearMap.domDomCongr_apply]
    rfl
  | k + 1, D, w => by
    change Tensor0SSpace.toModel ((show Tensor0SSpace (s + 2 * k) I x →L[ℝ] Tensor0SSpace s I x from
        (lapTop g s k).toSection x)
        ((show Tensor0SSpace (s + 2 * k + 2) I x →L[ℝ] Tensor0SSpace (s + 2 * k) I x from
          (cometricDoubleTraceField (I := I) g (s + 2 * k)).toSection x) D)) w = _
    rw [toModel_lapTop s x k]
    simp_rw [toModel_doubleTrace]
    rw [← (Fin.consEquiv fun _ : Fin (k + 1) => Fin (Module.finrank ℝ (TangentSpace I x))).sum_comp,
      Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun K _ => ?_
    exact congrArg _ (pairVec_succ (fun i => toE (tangentFrame g x i)) k i K w).symm

/-! ### Reordering the derivative slots -/

/-- `j ↦ 2j` for `j < p`, `p + j ↦ 2j + 1`: interleaves the two halves of `Fin (2p)`. -/
def riffleFun (p : ℕ) (j : Fin (2 * p)) : Fin (2 * p) :=
  ⟨if (j : ℕ) < p then 2 * (j : ℕ) else 2 * ((j : ℕ) - p) + 1, by split_ifs <;> omega⟩

theorem riffleFun_injective (p : ℕ) : Function.Injective (riffleFun p) := by
  intro a b h
  have h' := congrArg Fin.val h
  simp only [riffleFun] at h'
  apply Fin.ext
  split_ifs at h' <;> omega

/-- The riffle permutation of the derivative slots. -/
def riffle (p : ℕ) : Equiv.Perm (Fin (2 * p)) :=
  Equiv.ofBijective (riffleFun p) (Finite.injective_iff_bijective.mp (riffleFun_injective p))

theorem riffle_val (p : ℕ) (j : Fin (2 * p)) :
    (riffle p j : ℕ) = if (j : ℕ) < p then 2 * (j : ℕ) else 2 * ((j : ℕ) - p) + 1 := rfl

variable (g) in
/-- The polyharmonic principal coefficient before the sign: `Φ_p ∘ (riffle)`, which pairs derivative
slot `j` with slot `p + j`. -/
def modelTop (s p : ℕ) : SmoothCcTensor g (s + 2 * p) s :=
  ccOperatorFieldComp (I := I) (M := M) g (s + 2 * p) (s + 2 * p) s (lapTop g s p)
    (permField g (extPerm s (2 * p) (riffle p)))

theorem extPerm_riffle_val (s p : ℕ) (j : Fin (s + 2 * p)) :
    (extPerm s (2 * p) (riffle p) j : ℕ) =
      if (j : ℕ) < p then 2 * (j : ℕ) else if (j : ℕ) < 2 * p then 2 * ((j : ℕ) - p) + 1
        else (j : ℕ) := by
  by_cases h : (j : ℕ) < 2 * p
  · rw [extPerm_apply_lt s (2 * p) _ j h, riffle_val]
    dsimp only
    split_ifs <;> omega
  · rw [extPerm_apply_ge s (2 * p) _ j (by omega)]
    split_ifs <;> omega

variable (g) in
/-- `modelTop` undoes prepending frame covectors: `P(e^K ⊗ η) = η(e_K, ·)` (compare
`polyTrace_prepend`). -/
theorem modelTop_prepend (s p : ℕ) (x : M) (hc : s + p + p = s + 2 * p)
    (K : Fin p → Fin (Module.finrank ℝ (TangentSpace I x))) (η : TensorRSSpace 0 (s + p) I x) :
    opFieldHom ((modelTop g s p).toSection x) (EquationData.castIdx (r := 0) hc x
        (prependCovectors p (fun j => g.inner x (tangentFrame g x (K j))) η)) =
      evalFirst p (fun j => tangentFrame g x (K j)) η := by
  classical
  refine rsToModel_injective (ContinuousLinearMap.ext fun β =>
    ContinuousMultilinearMap.ext fun w => ?_)
  rw [toModel_opFieldHom, modelTop, operatorFieldComposition_toSection, ContinuousLinearMap.comp_apply]
  rw [toModel_lapTop g s x p, toModel_evalFirst]
  set f : Fin (Module.finrank ℝ (TangentSpace I x)) → E := fun i => toE (tangentFrame g x i) with hf
  have hterm : ∀ J : Fin p → Fin (Module.finrank ℝ (TangentSpace I x)),
      Tensor0SSpace.toModel ((show Tensor0SSpace (s + 2 * p) I x →L[ℝ] Tensor0SSpace (s + 2 * p) I x from
          (permField g (extPerm s (2 * p) (riffle p))).toSection x)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2 * p) I x from
            EquationData.castIdx (r := 0) hc x
              (prependCovectors p (fun j => g.inner x (tangentFrame g x (K j))) η))
            (Tensor0SSpace.ofModel β))) (pairVec f p J w) =
        (if J = K then (1 : ℝ) else 0) *
          TensorRSSpace.toModel η β (appendFirst p (fun i => toE (tangentFrame g x (K i))) w) := by
    intro J
    change Tensor0SSpace.toModel (permFib I (extPerm s (2 * p) (riffle p)) x _) _ = _
    rw [toModel_permFib, ContinuousMultilinearMap.domDomCongr_apply, ← toModel_tensorRS_apply,
      toModel_castIdx, toModel_prependCovectors]
    have hprod : ∀ i : Fin p, g.inner x (tangentFrame g x (K i)) (ofE I x (pairVec f p J w
        (extPerm s (2 * p) (riffle p) (Fin.cast hc ⟨i, by omega⟩)))) = if K i = J i then 1 else 0 := by
      intro i
      have hv := extPerm_riffle_val s p (Fin.cast hc ⟨i, by omega⟩)
      simp only [Fin.val_cast] at hv
      rw [if_pos i.2] at hv
      have h2 : pairVec f p J w (extPerm s (2 * p) (riffle p) (Fin.cast hc ⟨i, by omega⟩)) = f (J i) := by
        unfold pairVec
        rw [dif_pos (by omega)]
        congr 2
        exact Fin.ext (by simp only [hv]; omega)
      rw [h2]
      exact tangentFrame_inner g x (K i) (J i)
    simp only [hprod, Finset.prod_boole]
    by_cases hJK : J = K
    · subst hJK
      rw [if_pos fun _ _ => rfl, if_pos rfl]
      congr 2
      funext j
      rw [appendFirst_apply]
      have hv := extPerm_riffle_val s p (Fin.cast hc ⟨(j : ℕ) + p, by omega⟩)
      simp only [Fin.val_cast] at hv
      unfold pairVec
      by_cases hj : (j : ℕ) < p
      · rw [if_neg (by omega), if_pos (by omega)] at hv
        rw [dif_pos (by omega), dif_pos hj]
        congr 2
        exact Fin.ext (by simp only [hv]; omega)
      · rw [if_neg (by omega), if_neg (by omega)] at hv
        rw [dif_neg (by omega), dif_neg hj]
        congr 1
        exact Fin.ext (by simp only [hv]; omega)
    · rw [if_neg fun h => hJK (funext fun i => (h i (Finset.mem_univ i)).symm), if_neg hJK, zero_mul,
        zero_mul]
  simp_rw [hterm]
  rw [Finset.sum_eq_single K]
  · rw [if_pos rfl, one_mul]
  · intro J _ hJ
    rw [if_neg hJ, zero_mul]
  · intro hK
    exact absurd (Finset.mem_univ K) hK

theorem opFieldHom_smul {a b : ℕ} {x : M} (c : ℝ) (Φ : TensorRSSpace a b I x)
    (ξ : TensorRSSpace 0 a I x) : opFieldHom (c • Φ) ξ = c • opFieldHom Φ ξ := rfl

variable (g) in
/-- **The polyharmonic principal coefficient satisfies the Legendre condition** with constant `1`
(`lem:legendre-examples` (b)). -/
theorem legendreAt_modelTop (s p : ℕ) (x : M) (hc : s + p + p = s + 2 * p) :
    LegendreAt g 0 s p x ((opFieldHom ((((-1 : ℝ) ^ (p + 1)) • modelTop g s p).toSection x)).comp
      (EquationData.castIdx (r := 0) hc x).toContinuousLinearMap) 1 := by
  refine ⟨one_pos, fun ξ => ?_⟩
  rw [legendreForm_eq]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply, opFieldHom_smul,
    modelTop_prepend, fiberInner_smul_right]
  rw [← Finset.mul_sum, ← fiberInner_eq_sum_evalFirst g s x p ξ ξ, ← mul_assoc, ← mul_pow]
  norm_num

/-- **`Δ_raw^p = (Φ_p ∘ riffle)(∇^{2p}) + (order ≤ 2p - 1)`**: the slots are reordered by the Ricci
identities (`permute_iteratedCovGrad`). -/
theorem isDiffOp_lapIter_sub_modelTop (S : Set ℝ) (s : ℕ) {p : ℕ} (hp : 1 ≤ p) :
    IsDiffOp (g := g) S (2 * p - 1) (fun (_ : ℝ) (u : SmoothCcTensor g 0 s) =>
      rawTensorConnLapIter (I := I) g 0 s p u -
        operatorFieldApply (I := I) (M := M) g (s + 2 * p) s (modelTop g s p)
          (iteratedCovGrad g 0 s (2 * p) u)) := by
  have h1 := isDiffOp_lapIter_sub (g := g) S s p
  have h2 := ((permute_iteratedCovGrad (g := g) S s (2 * p) (riffle p)).comp_field
    (jointlySmoothOn_const g S (lapTop g s p))).neg.mono (show 2 * p - 2 ≤ 2 * p - 1 by omega)
  refine (h1.add h2).congr' fun t u => ?_
  rw [modelTop, ← operatorFieldApply_assoc, operatorFieldApply_permField,
    operatorFieldApplication_sub_right]
  abel

/-- **The polyharmonic model operator** (`prop:model`, first part): `L₀ = (-1)^{p+1} Δ_raw^p = -(Δ)^p`
(with `Δ = -Δ_raw ≥ 0`) is a linear operator of order `2p` in the class, with Legendre constant
`1`. -/
theorem exists_polyharmonic (s : ℕ) {p : ℕ} (hp : 1 ≤ p) (T : ℝ) :
    ∃ L₀ : LinearOp g s p T, (∀ t u, L₀.apply t u =
        ((-1 : ℝ) ^ (p + 1)) • rawTensorConnLapIter (I := I) g 0 s p u) ∧ L₀.IsParabolic 1 := by
  obtain ⟨F, hF, hDF⟩ := isDiffOp_lapIter_sub_modelTop (g := g) (Icc 0 T) s hp
  set c : ℝ := (-1 : ℝ) ^ (p + 1) with hc
  refine ⟨⟨Fin.lastCases (motive := fun k => ℝ → SmoothCcTensor g (s + k) s)
    (fun _ => c • modelTop g s p) (fun i t => c • F i t), fun k => ?_⟩, fun t u => ?_, one_pos,
    fun t _ x => ?_⟩
  · induction k using Fin.lastCases with
    | last => rw [Fin.lastCases_last]; exact jointlySmoothOn_const g _ _
    | cast i => rw [Fin.lastCases_castSucc]; exact jointlySmoothOn_smul c (hF i)
  · unfold LinearOp.apply
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_last, Fin.lastCases_castSucc, Fin.val_castSucc, Fin.val_last,
      operatorFieldApplication_smul_left]
    have h := hDF t u
    rw [show 2 * p - 1 + 1 = 2 * p by omega, Finset.sum_range] at h
    rw [← Finset.smul_sum, ← smul_add, ← h, sub_add_cancel]
  · change LegendreAt g 0 s p x ((opFieldHom ((Fin.lastCases
        (motive := fun k => ℝ → SmoothCcTensor g (s + k) s)
        (fun _ => c • modelTop g s p) (fun i t => c • F i t) (Fin.last (2 * p)) t).toSection x)).comp
        (EquationData.castIdx (r := 0) (by simp only [Fin.val_last]; omega) x).toContinuousLinearMap) 1
    rw [Fin.lastCases_last]
    exact legendreAt_modelTop g s p x _

end ShortTime
