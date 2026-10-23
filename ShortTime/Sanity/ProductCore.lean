import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Algebraic core of the product Legendre condition (`lem:legendre-examples` (a))

For symmetric `n × n` matrices `E₁, …, E_p` with `E_ℓ ≥ e_ℓ · 1` and a positive semidefinite symmetric
bilinear form `b`: `Σ_{I,K} ∏ E_ℓ(I_ℓ, K_ℓ) · b(v_I, v_K) ≥ (∏ e_ℓ) Σ_I b(v_I, v_I)` (`pf_ge`).
Induction on `p`, writing `E₁ - e₁ = Σ_m a_m a_mᵀ`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open scoped BigOperators

namespace ShortTime

section Core

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- `Σ_{I,K} ∏_ℓ E_ℓ(I_ℓ,K_ℓ) · b(v_I, w_K)`. -/
def pf {p : ℕ} (E : Fin p → Matrix (Fin n) (Fin n) ℝ) (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (v w : (Fin p → Fin n) → V) : ℝ :=
  ∑ I, ∑ K, (∏ l, E l (I l) (K l)) * b (v I) (w K)

theorem pf_split {p : ℕ} (E : Fin (p + 1) → Matrix (Fin n) (Fin n) ℝ) (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (v w : (Fin (p + 1) → Fin n) → V) :
    pf E b v w = ∑ i, ∑ k, E 0 i k *
      pf (fun l => E l.succ) b (fun J => v (Fin.cons i J)) (fun L => w (Fin.cons k L)) := by
  unfold pf
  rw [← (Fin.consEquiv fun _ => Fin n).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [← (Fin.consEquiv fun _ => Fin n).sum_comp (fun K => _), Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun L _ => ?_
  have hc : ∀ (i : Fin n) (J : Fin p → Fin n),
      (Fin.consEquiv fun _ => Fin n) (i, J) = Fin.cons i J := fun _ _ => rfl
  simp only [hc, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

theorem pf_sum_left {p m : ℕ} (E : Fin p → Matrix (Fin n) (Fin n) ℝ) (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (c : Fin m → ℝ) (f : Fin m → (Fin p → Fin n) → V) (w : (Fin p → Fin n) → V) :
    pf E b (fun J => ∑ i, c i • f i J) w = ∑ i, c i * pf E b (f i) w := by
  have key : ∀ I K, (∏ l, E l (I l) (K l)) * b (∑ i, c i • f i I) (w K) =
      ∑ i, c i * ((∏ l, E l (I l) (K l)) * b (f i I) (w K)) := by
    intro I K
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold pf
  calc ∑ I, ∑ K, (∏ l, E l (I l) (K l)) * b (∑ i, c i • f i I) (w K)
      = ∑ I, ∑ K, ∑ i, c i * ((∏ l, E l (I l) (K l)) * b (f i I) (w K)) := by simp_rw [key]
    _ = ∑ I, ∑ i, ∑ K, c i * ((∏ l, E l (I l) (K l)) * b (f i I) (w K)) :=
        Finset.sum_congr rfl fun I _ => Finset.sum_comm
    _ = ∑ i, ∑ I, ∑ K, c i * ((∏ l, E l (I l) (K l)) * b (f i I) (w K)) := Finset.sum_comm
    _ = _ := by simp_rw [Finset.mul_sum]

theorem pf_sum_right {p m : ℕ} (E : Fin p → Matrix (Fin n) (Fin n) ℝ) (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (c : Fin m → ℝ) (v : (Fin p → Fin n) → V) (f : Fin m → (Fin p → Fin n) → V) :
    pf E b v (fun J => ∑ i, c i • f i J) = ∑ i, c i * pf E b v (f i) := by
  have key : ∀ I K, (∏ l, E l (I l) (K l)) * b (v I) (∑ i, c i • f i K) =
      ∑ i, c i * ((∏ l, E l (I l) (K l)) * b (v I) (f i K)) := by
    intro I K
    simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold pf
  calc ∑ I, ∑ K, (∏ l, E l (I l) (K l)) * b (v I) (∑ i, c i • f i K)
      = ∑ I, ∑ K, ∑ i, c i * ((∏ l, E l (I l) (K l)) * b (v I) (f i K)) := by simp_rw [key]
    _ = ∑ I, ∑ i, ∑ K, c i * ((∏ l, E l (I l) (K l)) * b (v I) (f i K)) :=
        Finset.sum_congr rfl fun I _ => Finset.sum_comm
    _ = ∑ i, ∑ I, ∑ K, c i * ((∏ l, E l (I l) (K l)) * b (v I) (f i K)) := Finset.sum_comm
    _ = _ := by simp_rw [Finset.mul_sum]

/-- The core inequality. -/
theorem pf_ge : ∀ (p : ℕ) (E : Fin p → Matrix (Fin n) (Fin n) ℝ) (e : Fin p → ℝ)
    (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ),
    (∀ l, 0 < e l) → (∀ l, (E l).IsHermitian) →
    (∀ l (c : Fin n → ℝ), e l * ∑ a, c a * c a ≤ ∑ a, ∑ a', c a * E l a a' * c a') →
    (∀ v w, b v w = b w v) → (∀ v, 0 ≤ b v v) →
    ∀ v : (Fin p → Fin n) → V,
      (∏ l, e l) * ∑ I, b (v I) (v I) ≤ pf E b v v := by
  intro p
  induction p with
  | zero =>
    intro E e b _ _ _ _ _ v
    simp [pf]
  | succ p ih =>
    intro E e b he hH hE hsy hnn v
    set E' : Fin p → Matrix (Fin n) (Fin n) ℝ := fun l => E l.succ with hE'
    set e' : Fin p → ℝ := fun l => e l.succ with he'
    have IH := ih E' e' b (fun l => he l.succ) (fun l => hH l.succ) (fun l c => hE l.succ c) hsy hnn
    -- the positive semidefinite part
    set S : Matrix (Fin n) (Fin n) ℝ := E 0 - e 0 • (1 : Matrix (Fin n) (Fin n) ℝ) with hS
    have hSpsd : S.PosSemidef := by
      refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
      · rw [Matrix.IsHermitian, hS, Matrix.conjTranspose_sub, (hH 0).eq,
          Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
        simp
      · intro c
        have := hE 0 c
        have e1 : star c ⬝ᵥ (S.mulVec c) =
            ∑ a, ∑ a', c a * E 0 a a' * c a' - e 0 * ∑ a, c a * c a := by
          simp only [hS, dotProduct, Matrix.mulVec, Matrix.sub_apply, Matrix.smul_apply,
            Matrix.one_apply, star_trivial, smul_eq_mul, mul_ite, mul_one, mul_zero,
            sub_mul, Finset.sum_sub_distrib, mul_sub, Finset.mul_sum, ite_mul, zero_mul,
            Finset.sum_ite_eq, Finset.mem_univ, if_true]
          congr 1
          · exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => by ring
          · exact Finset.sum_congr rfl fun a _ => by ring
        rw [e1]; linarith
    obtain ⟨mm, a, hSa⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hSpsd
    have hSent : ∀ i k, E 0 i k = (if i = k then e 0 else 0) + ∑ m, a m i * a m k := by
      intro i k
      have h := congrFun (congrFun hSa i) k
      simp only [hS, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.sum_apply,
        Matrix.vecMulVec_apply, star_trivial, smul_eq_mul] at h
      by_cases hik : i = k
      · subst hik; simp only [if_true, mul_one] at h ⊢; linarith
      · simp only [hik, if_false, mul_zero] at h ⊢; linarith
    set vi : Fin n → (Fin p → Fin n) → V := fun i J => v (Fin.cons i J) with hvi
    set u : Fin mm → (Fin p → Fin n) → V := fun m J => ∑ i, a m i • vi i J with hu
    have hT : ∀ i, (∏ l, e' l) * ∑ J, b (vi i J) (vi i J) ≤ pf E' b (vi i) (vi i) :=
      fun i => IH (vi i)
    have hprod : 0 ≤ ∏ l, e' l := Finset.prod_nonneg fun l _ => (he l.succ).le
    have hU : ∀ m, 0 ≤ pf E' b (u m) (u m) := fun m =>
      le_trans (mul_nonneg hprod (Finset.sum_nonneg fun J _ => hnn _)) (IH (u m))
    have hexp : pf E b v v = e 0 * ∑ i, pf E' b (vi i) (vi i) + ∑ m, pf E' b (u m) (u m) := by
      rw [pf_split]
      have h1 : ∀ m, pf E' b (u m) (u m) =
          ∑ i, ∑ k, (a m i * a m k) * pf E' b (vi i) (vi k) := by
        intro m
        simp only [hu]
        rw [pf_sum_left]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [pf_sum_right, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      simp_rw [h1, hSent, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true, Finset.mul_sum, Finset.sum_mul]
      congr 1
      exact (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans Finset.sum_comm
    have hsplit : ∑ I, b (v I) (v I) = ∑ i, ∑ J, b (vi i J) (vi i J) := by
      rw [← (Fin.consEquiv fun _ => Fin n).sum_comp, Fintype.sum_prod_type]
      rfl
    rw [hexp, Fin.prod_univ_succ, hsplit]
    have h5 : (e 0 * ∏ l, e' l) * ∑ i, ∑ J, b (vi i J) (vi i J) =
        e 0 * ∑ i, (∏ l, e' l) * ∑ J, b (vi i J) (vi i J) := by
      rw [mul_assoc, Finset.mul_sum]
    have h2 : e 0 * ∑ i, (∏ l, e' l) * ∑ J, b (vi i J) (vi i J) ≤
        e 0 * ∑ i, pf E' b (vi i) (vi i) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hT i) (he 0).le
    have h3 : 0 ≤ ∑ m, pf E' b (u m) (u m) := Finset.sum_nonneg fun m _ => hU m
    rw [h5]
    linarith

end Core

end ShortTime
