import ShortTime.Linear.RicciSwap
import ShortTime.Linear.Balance
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.Linearization
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert

/-!
# Commuting covariant derivatives costs lower order (`lem:ricci`)

For a permutation `σ` of the first `n` slots of `∇^n u` (the derivative slots),

  `‖σ(∇^n u) - ∇^n u‖ ≤ C · N_{n-2}(u)`,   `N_k(u) = ∑_{i ≤ k} ‖∇^i u‖`.

Slot permutations of covariant tensor fields are the library's `domDomCongrSection`. The
estimate is proved for one adjacent transposition from the Ricci identity (`exists_swap_defect`)
and the jet bounds for curvature terms, and extended to all permutations because
`σ ↦ σ(T) - T` is subadditive along products of isometries.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set MeasureTheory
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

/-- `‖T‖`, the `L²` norm of a covariant tensor field. -/
abbrev ccNorm {a : ℕ} (T : SmoothCcTensor g 0 a) : ℝ :=
  tensorL2Norm (I := I) (M := M) g 0 a T.toFun

theorem ccNorm_sq {a : ℕ} (T : SmoothCcTensor g 0 a) :
    ccNorm T ^ 2 = ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 a x (T.toSection x)
      ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [← tensorL2Inner_self_eq_sq_norm, tensorL2Inner_self_eq_integral]

/-- A pointwise bound by finitely many jets integrates to an `L²` bound. -/
theorem ccNorm_sq_le_of_pointwise {a : ℕ} (A : SmoothCcTensor g 0 a) (n : ℕ) (b : ℕ → ℕ)
    (B : ∀ i, SmoothCcTensor g 0 (b i)) {c : ℝ} (_hc : 0 ≤ c)
    (h : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 a x (A.toSection x) ≤
      c * ∑ i ∈ Finset.range n, riemannianFiberNormSq (I := I) (M := M) g 0 (b i) x
        ((B i).toSection x)) :
    ccNorm A ^ 2 ≤ c * ∑ i ∈ Finset.range n, ccNorm (B i) ^ 2 := by
  rw [ccNorm_sq]
  simp_rw [ccNorm_sq]
  rw [← integral_finsetSum _ fun i _ => integrable_riemannianFiberNormSq_cc g 0 (b i) (B i),
    ← integral_const_mul]
  exact integral_mono (integrable_riemannianFiberNormSq_cc g 0 a A)
    ((integrable_finsetSum _ fun i _ => integrable_riemannianFiberNormSq_cc g 0 (b i) (B i)).const_mul c)
    h

/-! ### One transposition -/

/-- The Ricci identity for one transposition, as an identity of tensor fields. -/
theorem exists_swap_field (t k : ℕ) :
    ∃ R : HomTensorRSField (E := E) (M := M) 0 t (t + 2) I, ∀ W : SmoothCcTensor g 0 t,
      domDomCongrSection (I := I) g
          (Equiv.swap (⟨k, by omega⟩ : Fin (t + 2 + k)) ⟨k + 1, by omega⟩)
          (iteratedCovGrad g 0 (t + 2) k (iteratedCovGrad g 0 t 2 W)) =
        iteratedCovGrad g 0 (t + 2) k (iteratedCovGrad g 0 t 2 W) -
          iteratedCovGrad g 0 (t + 2) k (homTensorRSFieldApply (I := I) (M := M) g 0 t (t + 2) R W) := by
  obtain ⟨R, hR⟩ := exists_swap_defect (I := I) (M := M) g t
  refine ⟨R, fun W => ?_⟩
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g (fun x => ?_)
  rw [domDomCongrSection_unitModel, unitModel_sub, ← liftPerm_swap t k]
  have h := hR W k x (unitTensor (I := I) (M := M) x)
  simp only [unitModel]
  rw [← h]
  abel

/-- `L²` bound for one transposition of `∇^k ∇² ∇^m u`. -/
theorem exists_swap_bound (s m k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SmoothCcTensor g 0 s,
      ccNorm (domDomCongrSection (I := I) g
          (Equiv.swap (⟨k, by omega⟩ : Fin (s + m + 2 + k)) ⟨k + 1, by omega⟩)
          (iteratedCovGrad g 0 (s + m + 2) k (iteratedCovGrad g 0 (s + m) 2 (iteratedCovGrad g 0 s m u))) -
        iteratedCovGrad g 0 (s + m + 2) k
          (iteratedCovGrad g 0 (s + m) 2 (iteratedCovGrad g 0 s m u))) ≤
        C * jetSum g s (m + k) u := by
  obtain ⟨R, hR⟩ := exists_swap_field (g := g) (s + m) k
  obtain ⟨cc, hcc0, hcc⟩ :=
    exists_homTensorRSFieldApply_on_jet_iteratedCovGrad_window_bound (I := I) (M := M) g 0 s m
      (s + m + 2) R
  refine ⟨Real.sqrt (cc k), Real.sqrt_nonneg _, fun u => ?_⟩
  rw [hR (iteratedCovGrad g 0 s m u), sub_sub_cancel_left]
  set X := iteratedCovGrad g 0 (s + m + 2) k
    (homTensorRSFieldApply (I := I) (M := M) g 0 (s + m) (s + m + 2) R (iteratedCovGrad g 0 s m u))
  have hneg : ccNorm (-X) = ccNorm X := by
    unfold ccNorm tensorL2Norm
    rw [SmoothCcTensor.toFun_neg]
    congr 1
    rw [show -X.toFun = (-1 : ℝ) • X.toFun from (neg_one_smul ℝ _).symm,
      tensorL2Inner_smul_left, tensorL2Inner_smul_right]
    ring
  rw [hneg]
  have hsq := ccNorm_sq_le_of_pointwise X (1 + k) (fun i => s + (i + m))
    (fun i => iteratedCovGrad g 0 s (i + m) u) (hcc0 k) (fun x => hcc u k x)
  -- `∑_{i ≤ k} ‖∇^{i+m} u‖² ≤ N_{m+k}(u)²`
  have hsum : ∑ i ∈ Finset.range (1 + k), ccNorm (iteratedCovGrad g 0 s (i + m) u) ^ 2 ≤
      jetSum g s (m + k) u ^ 2 := by
    have h1 : ∑ i ∈ Finset.range (1 + k), ccNorm (iteratedCovGrad g 0 s (i + m) u) ^ 2 ≤
        (∑ i ∈ Finset.range (1 + k), ccNorm (iteratedCovGrad g 0 s (i + m) u)) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => tensorL2Norm_nonneg (I := I) (M := M) g 0 _ _)
    have h2 : ∑ i ∈ Finset.range (1 + k), ccNorm (iteratedCovGrad g 0 s (i + m) u) ≤
        jetSum g s (m + k) u := by
      unfold jetSum
      rw [show Finset.range (m + k + 1) = Finset.range m ∪ Finset.Ico m (m + k + 1) from by
        ext j; simp [Finset.mem_Ico]; omega]
      rw [Finset.sum_union (Finset.disjoint_left.mpr fun j hj hj' => by
          simp only [Finset.mem_range, Finset.mem_Ico] at hj hj'; omega),
        Finset.sum_Ico_eq_sum_range]
      have hrw : ∑ i ∈ Finset.range (m + k + 1 - m), jetNorm g s (m + i) u =
          ∑ i ∈ Finset.range (1 + k), ccNorm (iteratedCovGrad g 0 s (i + m) u) := by
        rw [show m + k + 1 - m = 1 + k by omega]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Nat.add_comm m i]
      rw [hrw]
      have h0 : 0 ≤ ∑ i ∈ Finset.range m, jetNorm g s i u :=
        Finset.sum_nonneg fun i _ => jetNorm_nonneg g s i u
      linarith
    have hnn : 0 ≤ ∑ i ∈ Finset.range (1 + k), ccNorm (iteratedCovGrad g 0 s (i + m) u) :=
      Finset.sum_nonneg fun i _ => tensorL2Norm_nonneg (I := I) (M := M) g 0 _ _
    exact h1.trans (pow_le_pow_left₀ hnn h2 2)
  have hX : ccNorm X ^ 2 ≤ (Real.sqrt (cc k) * jetSum g s (m + k) u) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (hcc0 k)]
    exact hsq.trans (mul_le_mul_of_nonneg_left hsum (hcc0 k))
  exact (pow_le_pow_iff_left₀ (tensorL2Norm_nonneg (I := I) (M := M) g 0 _ _)
    (mul_nonneg (Real.sqrt_nonneg _) (jetSum_nonneg s _ u)) two_ne_zero).mp hX

/-! ### All permutations of the derivative slots -/

theorem ccNorm_swap_transport {N N' : ℕ} (h : N = N') (T : SmoothCcTensor g 0 N)
    (T' : SmoothCcTensor g 0 N') (hT : HEq T T') (k : ℕ) (hk : k + 1 < N) :
    ccNorm (domDomCongrSection (I := I) g (Equiv.swap (⟨k, by omega⟩ : Fin N) ⟨k + 1, hk⟩) T - T) =
      ccNorm (domDomCongrSection (I := I) g
        (Equiv.swap (⟨k, by omega⟩ : Fin N') ⟨k + 1, by omega⟩) T' - T') := by
  subst h
  cases eq_of_heq hT
  rfl

/-- **One transposition of the derivative slots of `∇^p u`.** -/
theorem exists_adjSwap_bound (s p k : ℕ) (hk : k + 2 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SmoothCcTensor g 0 s,
      ccNorm (domDomCongrSection (I := I) g
          (Equiv.swap (⟨k, by omega⟩ : Fin (s + p)) ⟨k + 1, by omega⟩)
          (iteratedCovGrad g 0 s p u) - iteratedCovGrad g 0 s p u) ≤
        C * jetSum g s (p - 2) u := by
  obtain ⟨C, hC0, hC⟩ := exists_swap_bound (g := g) s (p - 2 - k) k
  refine ⟨C, hC0, fun u => ?_⟩
  have hheq : HEq (iteratedCovGrad g 0 (s + (p - 2 - k) + 2) k
      (iteratedCovGrad g 0 (s + (p - 2 - k)) 2 (iteratedCovGrad g 0 s (p - 2 - k) u)))
      (iteratedCovGrad g 0 s p u) := by
    have h1 := iteratedCovGrad_comp_heq (g := g) 0 s (p - 2 - k + 2) u k
    have hp : p - 2 - k + 2 + k = p := by omega
    rw [hp] at h1
    exact h1
  rw [← ccNorm_swap_transport (by omega) _ _ hheq k (by omega)]
  have h := hC u
  rwa [show p - 2 - k + k = p - 2 by omega] at h

theorem domDomCongrSection_one {a : ℕ} (T : SmoothCcTensor g 0 a) :
    domDomCongrSection (I := I) g 1 T = T := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g (fun x => ?_)
  rw [domDomCongrSection_unitModel]
  ext v
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rfl

theorem domDomCongrSection_mul {a : ℕ} (σ τ : Equiv.Perm (Fin a)) (T : SmoothCcTensor g 0 a) :
    domDomCongrSection (I := I) g (σ * τ) T =
      domDomCongrSection (I := I) g σ (domDomCongrSection (I := I) g τ T) := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g (fun x => ?_)
  rw [domDomCongrSection_unitModel, domDomCongrSection_unitModel, domDomCongrSection_unitModel]
  ext v
  simp only [ContinuousMultilinearMap.domDomCongr_apply]
  rfl

theorem domDomCongrSection_sub {a : ℕ} (σ : Equiv.Perm (Fin a)) (A B : SmoothCcTensor g 0 a) :
    domDomCongrSection (I := I) g σ (A - B) =
      domDomCongrSection (I := I) g σ A - domDomCongrSection (I := I) g σ B := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g (fun x => ?_)
  rw [unitModel_sub, domDomCongrSection_unitModel, domDomCongrSection_unitModel,
    domDomCongrSection_unitModel, unitModel_sub]
  ext v
  simp only [ContinuousMultilinearMap.domDomCongr_apply, sub_apply]

theorem ccNorm_domDomCongrSection {a : ℕ} (σ : Equiv.Perm (Fin a)) (T : SmoothCcTensor g 0 a) :
    ccNorm (domDomCongrSection (I := I) g σ T) = ccNorm T := by
  have h : ccNorm (domDomCongrSection (I := I) g σ T) ^ 2 = ccNorm T ^ 2 := by
    rw [ccNorm_sq, ccNorm_sq]
    congr 1
    funext x
    exact riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g σ T 0 x
  exact (pow_left_inj₀ (tensorL2Norm_nonneg (I := I) (M := M) g 0 _ _)
    (tensorL2Norm_nonneg (I := I) (M := M) g 0 _ _) two_ne_zero).mp h

theorem ccNorm_eq_norm {a : ℕ} (T : SmoothCcTensor g 0 a) : ccNorm T = ‖T‖ := rfl

/-- Permutations of the first `p` slots of a `(0, s+p)`-tensor. -/
def extPerm (s p : ℕ) : Equiv.Perm (Fin p) →* Equiv.Perm (Fin (s + p)) :=
  ((Equiv.permCongrHom (finSumFinEquiv.trans (finCongr (Nat.add_comm p s)))).toMonoidHom).comp
    ((Equiv.Perm.sumCongrHom (Fin p) (Fin s)).comp (MonoidHom.inl _ _))

theorem extPerm_swap (s n : ℕ) (i : Fin n) :
    extPerm s (n + 1) (Equiv.swap i.castSucc i.succ) =
      Equiv.swap (⟨i, by omega⟩ : Fin (s + (n + 1))) ⟨i + 1, by omega⟩ := by
  simp only [extPerm, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply,
    Equiv.Perm.sumCongrHom_apply, MulEquiv.coe_toMonoidHom]
  rw [show (Equiv.swap i.castSucc i.succ).sumCongr (1 : Equiv.Perm (Fin s)) =
      Equiv.swap (Sum.inl i.castSucc) (Sum.inl i.succ) from Equiv.Perm.sumCongr_swap_refl _ _]
  change (finSumFinEquiv.trans (finCongr (Nat.add_comm (n + 1) s))).permCongr
    (Equiv.swap (Sum.inl i.castSucc) (Sum.inl i.succ)) = _
  rw [Equiv.permCongr_def, Equiv.symm_trans_swap_trans]
  congr 1 <;> ext <;> simp [finSumFinEquiv_apply_left]

/-- **Commuting covariant derivatives** (`lem:ricci`, in `L²` form): permuting the derivative
slots of `∇^p u` changes it by at most `C · N_{p-2}(u)`. -/
theorem exists_perm_bound (s p : ℕ) (σ : Equiv.Perm (Fin p)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SmoothCcTensor g 0 s,
      ccNorm (domDomCongrSection (I := I) g (extPerm s p σ) (iteratedCovGrad g 0 s p u) -
        iteratedCovGrad g 0 s p u) ≤ C * jetSum g s (p - 2) u := by
  -- the property, stated for any permutation of the slots of `∇^p u`
  let Pr : Equiv.Perm (Fin (s + p)) → Prop := fun τ => ∃ C : ℝ, 0 ≤ C ∧
    ∀ u : SmoothCcTensor g 0 s,
      ccNorm (domDomCongrSection (I := I) g τ (iteratedCovGrad g 0 s p u) -
        iteratedCovGrad g 0 s p u) ≤ C * jetSum g s (p - 2) u
  have hone : Pr 1 := ⟨0, le_rfl, fun u => by
    rw [domDomCongrSection_one, sub_self, zero_mul]
    exact le_of_eq (by rw [ccNorm_eq_norm, norm_zero])⟩
  have hmul : ∀ τ₁ τ₂, Pr τ₁ → Pr τ₂ → Pr (τ₁ * τ₂) := by
    rintro τ₁ τ₂ ⟨C₁, hC₁0, hC₁⟩ ⟨C₂, hC₂0, hC₂⟩
    refine ⟨C₁ + C₂, by positivity, fun u => ?_⟩
    set T := iteratedCovGrad g 0 s p u
    rw [domDomCongrSection_mul]
    have htri : ccNorm (domDomCongrSection (I := I) g τ₁ (domDomCongrSection (I := I) g τ₂ T) - T) ≤
        ccNorm (domDomCongrSection (I := I) g τ₂ T - T) +
          ccNorm (domDomCongrSection (I := I) g τ₁ T - T) := by
      simp only [ccNorm_eq_norm]
      calc ‖domDomCongrSection (I := I) g τ₁ (domDomCongrSection (I := I) g τ₂ T) - T‖
          = ‖domDomCongrSection (I := I) g τ₁ (domDomCongrSection (I := I) g τ₂ T - T) +
              (domDomCongrSection (I := I) g τ₁ T - T)‖ := by
            rw [domDomCongrSection_sub]; abel_nf
        _ ≤ _ := norm_add_le _ _
        _ = _ := by rw [← ccNorm_eq_norm, ccNorm_domDomCongrSection, ccNorm_eq_norm]
    calc _ ≤ _ := htri
      _ ≤ C₂ * jetSum g s (p - 2) u + C₁ * jetSum g s (p - 2) u := add_le_add (hC₂ u) (hC₁ u)
      _ = (C₁ + C₂) * jetSum g s (p - 2) u := by ring
  -- reduce to generators
  rcases p with _ | n
  · have hσ : σ = 1 := Subsingleton.elim _ _
    rw [hσ, map_one]
    exact hone
  · have hmem : σ ∈ Submonoid.closure (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      exact Submonoid.mem_top σ
    induction hmem using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [extPerm_swap]
      exact exists_adjSwap_bound s (n + 1) i (by omega)
    | one => rw [map_one]; exact hone
    | mul x y _ _ hx hy => rw [map_mul]; exact hmul _ _ hx hy

end ShortTime
