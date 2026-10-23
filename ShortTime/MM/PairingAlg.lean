import Mathlib

/-!
# Basis independence of a full contraction (pure multilinear algebra)

`contr Φ Ef b b' = Σ_r (∏_ℓ E_ℓ(b'_{r(ℓ,0)}, b'_{r(ℓ,1)})) Φ(b_r)` does not depend on the dual pair
`(b, b')`: this is the contraction of `E_1 ⊗ ⋯ ⊗ E_p` with the multilinear form `Φ`, slots `(ℓ,0), (ℓ,1)`
being paired.
-/

noncomputable section

namespace ShortTime
namespace MMAlg

open Finset

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W] {n p : ℕ}

/-- The slots `(ℓ, c)`, `ℓ < p`, `c < 2`. -/
abbrev Slot (p : ℕ) := Fin p × Fin 2

/-- `r : Slot p → Fin n` as a list of `p` pairs. -/
def pairEquiv : (Slot p → Fin n) ≃ (Fin p → Fin n × Fin n) where
  toFun t l := (t (l, 0), t (l, 1))
  invFun τ q := if q.2 = 0 then (τ q.1).1 else (τ q.1).2
  left_inv t := by
    funext ⟨l, c⟩
    fin_cases c <;> simp
  right_inv τ := by
    funext l
    simp

/-- A dual pair of families for the pairing `ev : W × V → ℝ`. -/
structure IsDual (ev : W →ₗ[ℝ] V →ₗ[ℝ] ℝ) (b : Fin n → V) (b' : Fin n → W) : Prop where
  vec : ∀ v, v = ∑ i, ev (b' i) v • b i
  cov : ∀ w, w = ∑ i, ev w (b i) • b' i
  dual : ∀ i j, ev (b' i) (b j) = if i = j then 1 else 0

/-- The full contraction. -/
def contr (Φ : MultilinearMap ℝ (fun _ : Slot p => V) ℝ) (Ef : Fin p → W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (b : Fin n → V) (b' : Fin n → W) : ℝ :=
  ∑ r : Slot p → Fin n, (∏ l, Ef l (b' (r (l, 0))) (b' (r (l, 1)))) * Φ (fun q => b (r q))

theorem sum_cross {ev : W →ₗ[ℝ] V →ₗ[ℝ] ℝ} {b c : Fin n → V} {b' c' : Fin n → W}
    (hb : IsDual ev b b') (hc : IsDual ev c c') (s t : Fin n) :
    ∑ a, ev (b' s) (c a) * ev (c' a) (b t) = if s = t then 1 else 0 := by
  have h2 := congrArg (ev (b' s)) (hc.vec (b t))
  rw [hb.dual, map_sum] at h2
  simp only [map_smul, smul_eq_mul] at h2
  rw [h2]
  exact Finset.sum_congr rfl fun a _ => by rw [mul_comm]

theorem phi_expand (Φ : MultilinearMap ℝ (fun _ : Slot p => V) ℝ) (x : Slot p → V)
    (b : Fin n → V) (κ : Slot p → Fin n → ℝ) (hx : ∀ q, x q = ∑ i, κ q i • b i) :
    Φ x = ∑ s : Slot p → Fin n, (∏ q, κ q (s q)) * Φ (fun q => b (s q)) := by
  have : x = fun q => ∑ i, κ q i • b i := funext hx
  rw [this, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]

theorem bilin_expand (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (b' : Fin n → W) (X Y : W) (α β : Fin n → ℝ)
    (hX : X = ∑ i, α i • b' i) (hY : Y = ∑ i, β i • b' i) :
    B X Y = ∑ u : Fin n × Fin n, α u.1 * β u.2 * B (b' u.1) (b' u.2) := by
  rw [hX, hY, Fintype.sum_prod_type]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem cross_prod {ev : W →ₗ[ℝ] V →ₗ[ℝ] ℝ} {b c : Fin n → V} {b' c' : Fin n → W}
    (hb : IsDual ev b b') (hc : IsDual ev c c') (s t : Slot p → Fin n) :
    ∑ r : Slot p → Fin n, (∏ q, ev (c' (r q)) (b (t q))) * (∏ q, ev (b' (s q)) (c (r q))) =
      if s = t then 1 else 0 := by
  classical
  simp_rw [← Finset.prod_mul_distrib]
  have h := Finset.prod_univ_sum (fun _ : Slot p => (Finset.univ : Finset (Fin n)))
    (fun q a => ev (c' a) (b (t q)) * ev (b' (s q)) (c a))
  rw [Fintype.piFinset_univ] at h
  rw [← h]
  have h2 : ∀ q, ∑ a, ev (c' a) (b (t q)) * ev (b' (s q)) (c a) =
      if s q = t q then 1 else 0 := fun q => by
    rw [← sum_cross hb hc (s q) (t q)]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  simp_rw [h2]
  rw [Finset.prod_boole]
  simp [funext_iff]

/-- **Basis independence.** The full contraction does not depend on the dual pair. -/
theorem contr_indep {ev : W →ₗ[ℝ] V →ₗ[ℝ] ℝ} {b c : Fin n → V} {b' c' : Fin n → W}
    (hb : IsDual ev b b') (hc : IsDual ev c c')
    (Φ : MultilinearMap ℝ (fun _ : Slot p => V) ℝ) (Ef : Fin p → W →ₗ[ℝ] W →ₗ[ℝ] ℝ) :
    contr Φ Ef c c' = contr Φ Ef b b' := by
  classical
  set G : (Slot p → Fin n) → ℝ := fun t => ∏ l, Ef l (b' (t (l, 0))) (b' (t (l, 1))) with hG
  set Pb : (Slot p → Fin n) → ℝ := fun s => Φ (fun q => b (s q)) with hPb
  have hP : ∀ r : Slot p → Fin n, (∏ l, Ef l (c' (r (l, 0))) (c' (r (l, 1)))) =
      ∑ t : Slot p → Fin n, (∏ q, ev (c' (r q)) (b (t q))) * G t := by
    intro r
    have h1 : ∀ l, Ef l (c' (r (l, 0))) (c' (r (l, 1))) =
        ∑ u : Fin n × Fin n, (ev (c' (r (l, 0))) (b u.1) * ev (c' (r (l, 1))) (b u.2)) *
          Ef l (b' u.1) (b' u.2) := fun l =>
      bilin_expand (Ef l) b' _ _ (fun i => ev (c' (r (l, 0))) (b i))
        (fun i => ev (c' (r (l, 1))) (b i)) (hb.cov _) (hb.cov _)
    simp only [h1]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Fintype.sum_equiv (pairEquiv (n := n) (p := p)).symm _ _ (fun τ => ?_)
    simp only [G, Fintype.prod_prod_type, Fin.prod_univ_two, pairEquiv, Equiv.coe_fn_symm_mk,
      Fin.isValue, if_true, show ((1 : Fin 2) = 0) = False by decide, if_false]
    rw [← Finset.prod_mul_distrib]
  have hPhi : ∀ r : Slot p → Fin n, Φ (fun q => c (r q)) =
      ∑ s, (∏ q, ev (b' (s q)) (c (r q))) * Pb s := fun r =>
    phi_expand Φ _ b (fun q i => ev (b' i) (c (r q))) (fun q => hb.vec _)
  unfold contr
  calc ∑ r : Slot p → Fin n, (∏ l, Ef l (c' (r (l, 0))) (c' (r (l, 1)))) * Φ (fun q => c (r q))
      = ∑ r : Slot p → Fin n, ∑ t : Slot p → Fin n, ∑ s : Slot p → Fin n,
          ((∏ q, ev (c' (r q)) (b (t q))) * (∏ q, ev (b' (s q)) (c (r q)))) * (G t * Pb s) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [hP r, hPhi r, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => ?_
        ring
    _ = ∑ t : Slot p → Fin n, ∑ s : Slot p → Fin n,
          (∑ r : Slot p → Fin n,
            (∏ q, ev (c' (r q)) (b (t q))) * (∏ q, ev (b' (s q)) (c (r q)))) * (G t * Pb s) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ s : Slot p → Fin n, G s * Pb s := by
        simp_rw [cross_prod hb hc]
        simp only [ite_mul, one_mul, zero_mul]
        rw [Finset.sum_comm]
        simp [Finset.sum_ite_eq]

/-- A dual family of `Module.finrank` vectors and functionals is a dual pair. -/
theorem isDual_of_dual [FiniteDimensional ℝ V] [NeZero n] (hn : n = Module.finrank ℝ V)
    (ev : W →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hW : ∀ w w' : W, (∀ v, ev w v = ev w' v) → w = w')
    (b : Fin n → V) (b' : Fin n → W) (hd : ∀ i j, ev (b' i) (b j) = if i = j then 1 else 0) :
    IsDual ev b b' := by
  classical
  have hli : LinearIndependent ℝ b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h := congrArg (ev (b' i)) hg
    simp only [map_sum, map_smul, hd, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, map_zero] at h
    exact h
  subst hn
  have : Nonempty (Fin (Module.finrank ℝ V)) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
  let B : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hB : ∀ i, B i = b i := fun i => by simp [B]
  have hvec : ∀ v, v = ∑ i, ev (b' i) v • b i := by
    intro v
    have h := B.sum_repr v
    have hc : ∀ j, ev (b' j) v = B.repr v j := by
      intro j
      conv_lhs => rw [← h]
      simp only [map_sum, map_smul, hB, hd, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp only [hc]
    conv_lhs => rw [← h]
    simp only [hB]
  refine ⟨hvec, fun w => hW _ _ fun v => ?_, hd⟩
  conv_lhs => rw [hvec v]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end MMAlg
end ShortTime
