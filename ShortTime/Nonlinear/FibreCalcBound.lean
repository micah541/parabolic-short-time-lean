import ShortTime.Nonlinear.FibreCalc
import ShortTime.Nonlinear.ParabolicBound
import ShortTime.Nonlinear.FibreMapTame

/-!
# The multilinear composition bound (bound (M) of `prop:nemytskii`)

A fibre map `G(ζ; η₁, …, η_k)` on a tuple `ζ` followed by `k` blocks `η_l` is *multilinear in the
blocks* (`IsBlockMultilinear`) if it is homogeneous of degree one in each block and its domain only
depends on `ζ`. The iterated fibre derivatives are of this kind (`isBlockMultilinear_fibreDeriv`).

**The bound** (`exists_block_bound`). Near a smooth reference `w` (pointwise tube of radius `δ`),
for families `u` of bounded `𝒫^N` norm and all smooth blocks `h_l`,
`‖G[u; h₁, …, h_k]‖²_{𝒫^N} ≤ C ∏_l ‖h_l‖²_{𝒫^N}`, where `‖h_l‖² = Σ_c ‖h_{l,c}‖²`.

*Proof.* Scale each block, `h_l = s_l h'_l` with `‖h'_l‖² ≤ ρ`. By the embedding
(`exists_jetSq_le_parabolicInner`) the low jets of `(u, h')` are bounded and `h'` is pointwise small,
so the pointwise tame bound (`FibreMap.exists_tame_pointwise`) and its integral
(`parabolicInner_le_of_jetSq_le`) bound `‖G[u; h']‖²` by a constant. Multilinearity gives
`G[u; h] = (∏ s_l) G[u; h']`. Finally let `s_l² ρ ↓ ‖h_l‖²`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter Topology MeasureTheory
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Elliptic
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

/-! ### Small facts on families -/

theorem smoothCcTensor_eq_of_toSection {a : ℕ} {S S' : SmoothCcTensor g 0 a}
    (h : ∀ x : M, S.toSection x = S'.toSection x) : S = S' := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  exact h

theorem toSection_smul_apply {a : ℕ} (c : ℝ) (S : SmoothCcTensor g 0 a) (x : M) :
    (c • S).toSection x = c • S.toSection x := by
  rw [SmoothCcTensor.toSection_smul]
  rfl

theorem jetSq_zero_zero {a : ℕ} {T : ℝ} (V : ℝ → SmoothCcTensor g 0 a) (t : ℝ) (x : M) :
    jetSq g T V 0 0 t x = riemannianFiberNormSq (I := I) (M := M) g 0 a x ((V t).toSection x) := rfl

/-- `‖c φ‖²_{𝒫^N} = c² ‖φ‖²_{𝒫^N}`. -/
theorem parabolicInner_smul_self {a : ℕ} {T : ℝ} {φ : ℝ → SmoothCcTensor g 0 a}
    (hφ : JointlySmoothOn g 0 a (Icc 0 T) φ) (c : ℝ) (p N : ℕ) :
    parabolicInner g a p N T (fun t => c • φ t) (fun t => c • φ t) =
      c ^ 2 * parabolicInner g a p N T φ φ := by
  unfold parabolicInner
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mixedInner_smul_left hφ, mixedInner_comm, mixedInner_smul_left hφ, mixedInner_comm]
  ring

/-! ### Tuples with blocks of families -/

section Blocks

variable {κ ι₀ : Type*} [Fintype κ] [Fintype ι₀] {a : κ → ℕ} {b₀ : ι₀ → ℕ} {k : ℕ}

/-- A tuple of families `u` followed by `k` blocks of families `h_l`. -/
def joinFam (u : ∀ c : κ, ℝ → SmoothCcTensor g 0 (a c))
    (h : Fin k → ∀ c : ι₀, ℝ → SmoothCcTensor g 0 (b₀ c)) :
    ∀ q : κ ⊕ (Fin k × ι₀), ℝ → SmoothCcTensor g 0 (blkRanks a b₀ k q)
  | .inl c => u c
  | .inr q => h q.1 q.2

/-- The zero blocks. -/
def zeroBlk : Fin k → ∀ c : ι₀, ℝ → SmoothCcTensor g 0 (b₀ c) := fun _ _ _ => 0

theorem jointlySmoothOn_joinFam {S : Set ℝ} {u : ∀ c : κ, ℝ → SmoothCcTensor g 0 (a c)}
    {h : Fin k → ∀ c : ι₀, ℝ → SmoothCcTensor g 0 (b₀ c)}
    (hu : ∀ c, JointlySmoothOn g 0 (a c) S (u c)) (hh : ∀ l c, JointlySmoothOn g 0 (b₀ c) S (h l c)) :
    ∀ q, JointlySmoothOn g 0 (blkRanks a b₀ k q) S (joinFam u h q)
  | .inl c => hu c
  | .inr q => hh q.1 q.2

theorem jointlySmoothOn_zeroBlk {S : Set ℝ} :
    ∀ l c, JointlySmoothOn g 0 (b₀ c) S (zeroBlk (g := g) (k := k) l c) :=
  fun _ c => jointlySmoothOn_const g S (0 : SmoothCcTensor g 0 (b₀ c))

theorem fbase_valAt_joinFam (u : ∀ c : κ, ℝ → SmoothCcTensor g 0 (a c))
    (h h' : Fin k → ∀ c : ι₀, ℝ → SmoothCcTensor g 0 (b₀ c)) (t : ℝ) (x : M) :
    fbase (FibreMap.valAt (fun q => joinFam u h q t) x) =
      fbase (FibreMap.valAt (fun q => joinFam u h' q t) x) := rfl

theorem valAt_joinFam_smul (u : ∀ c : κ, ℝ → SmoothCcTensor g 0 (a c))
    (h : Fin k → ∀ c : ι₀, ℝ → SmoothCcTensor g 0 (b₀ c)) (s : Fin k → ℝ) (t : ℝ) (x : M) :
    FibreMap.valAt (fun q => joinFam u (fun l c τ => s l • h l c τ) q t) x =
      scaleBlk s (FibreMap.valAt (fun q => joinFam u h q t) x) := by
  funext q
  rcases q with c | ⟨l, c⟩
  · rfl
  · exact toSection_smul_apply (s l) (h l c t) x

theorem scaleBlk_scaleBlk {x : M} (s s' : Fin k → ℝ) (V : ProdFiber I (blkRanks a b₀ k) x) :
    scaleBlk s (scaleBlk s' V) = scaleBlk (fun l => s l * s' l) V := by
  funext q
  rcases q with c | ⟨l, c⟩
  · rfl
  · exact smul_smul (s l) (s' l) _

theorem scaleBlk_one {x : M} (V : ProdFiber I (blkRanks a b₀ k) x) :
    scaleBlk (fun _ => (1 : ℝ)) V = V := by
  funext q
  rcases q with c | ⟨l, c⟩
  · rfl
  · exact one_smul ℝ _

end Blocks

/-! ### Multilinearity in the blocks -/

namespace FibreMap

variable {κ ι₀ : Type*} [Fintype κ] [Fintype ι₀] {a : κ → ℕ} {b₀ : ι₀ → ℕ} {k : ℕ}
variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] {b' : ℕ}

/-- A fibre map on `ζ` followed by `k` blocks is **multilinear in the blocks**: homogeneous of
degree one in each block (everywhere), with a domain depending only on `ζ`. -/
structure IsBlockMultilinear (G : FibreMap I M Λ (blkRanks a b₀ k) b') : Prop where
  dom_iff : ∀ (lam : Λ) (t : ℝ) (x : M) (V V' : ProdFiber I (blkRanks a b₀ k) x),
    fbase V = fbase V' → (V ∈ G.dom lam t x ↔ V' ∈ G.dom lam t x)
  smul : ∀ (lam : Λ) (t : ℝ) (x : M) (s : Fin k → ℝ) (V : ProdFiber I (blkRanks a b₀ k) x),
    G.F lam t x (scaleBlk s V) = (∏ l, s l) • G.F lam t x V

/-- The iterated fibre derivatives are multilinear in the blocks. -/
theorem isBlockMultilinear_fibreDeriv {ι : Type*} [Fintype ι] {b : ι → ℕ}
    (Φ : FibreMap I M Λ b b') (k : ℕ) : IsBlockMultilinear (Φ.fibreDeriv k) where
  dom_iff lam t x V V' hV := by
    show fbase V ∈ Φ.dom lam t x ↔ fbase V' ∈ Φ.dom lam t x
    rw [hV]
  smul := Φ.fibreDeriv_smul k

/-- **Scaling the blocks of the families scales `G[u; h]`.** -/
theorem apply_joinFam_smul {G : FibreMap I M Λ (blkRanks a b₀ k) b'} (hG : IsBlockMultilinear G)
    (lam : Λ) (u : ∀ c : κ, ℝ → SmoothCcTensor g 0 (a c))
    (h : Fin k → ∀ c : ι₀, ℝ → SmoothCcTensor g 0 (b₀ c)) {s : Fin k → ℝ} (hs : ∀ l, s l ≠ 0) :
    G.apply lam (joinFam u fun l c τ => s l • h l c τ) =
      fun t => (∏ l, s l) • G.apply lam (joinFam u h) t := by
  funext t
  by_cases hex : ∃ S : SmoothCcTensor g 0 b', ∀ x : M,
      S.toSection x = G.F lam t x (valAt (fun q => joinFam u h q t) x)
  · have hex' : ∃ S : SmoothCcTensor g 0 b', ∀ x : M,
        S.toSection x = G.F lam t x (valAt (fun q => joinFam u (fun l c τ => s l • h l c τ) q t) x) := by
      obtain ⟨S, hS⟩ := hex
      refine ⟨(∏ l, s l) • S, fun x => ?_⟩
      rw [toSection_smul_apply, hS, valAt_joinFam_smul, hG.smul]
    refine smoothCcTensor_eq_of_toSection fun x => ?_
    rw [apply_toSection G lam _ t hex' x, toSection_smul_apply, apply_toSection G lam _ t hex x,
      valAt_joinFam_smul, hG.smul]
  · have hex' : ¬ ∃ S : SmoothCcTensor g 0 b', ∀ x : M,
        S.toSection x = G.F lam t x (valAt (fun q => joinFam u (fun l c τ => s l • h l c τ) q t) x) := by
      rintro ⟨S, hS⟩
      refine hex ⟨(∏ l, (s l)⁻¹) • S, fun x => ?_⟩
      rw [toSection_smul_apply, hS, valAt_joinFam_smul, ← hG.smul, scaleBlk_scaleBlk]
      congr 1
      have e : (fun l => (s l)⁻¹ * s l) = fun _ => (1 : ℝ) := funext fun l => inv_mul_cancel₀ (hs l)
      rw [e, scaleBlk_one]
    simp only [apply, dif_neg hex, dif_neg hex', smul_zero]

/-! ### The bound -/

theorem mul_le_mul_aux {c K X Y : ℝ} (hc : 0 ≤ c) (hcK : c ≤ K) (hX : 0 ≤ X) (hXY : X ≤ Y) :
    c * X ≤ K * Y :=
  mul_le_mul hcK hXY hX (hc.trans hcK)

theorem rho_aux {δ K : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K) :
    0 < min 1 (δ / (K + 1)) ∧ min 1 (δ / (K + 1)) ≤ 1 ∧ K * min 1 (δ / (K + 1)) ≤ δ := by
  have hK1 : 0 < K + 1 := by linarith
  refine ⟨lt_min one_pos (div_pos hδ hK1), min_le_left _ _, ?_⟩
  calc K * min 1 (δ / (K + 1)) ≤ (K + 1) * (δ / (K + 1)) :=
        mul_le_mul (by linarith) (min_le_right _ _) (le_min zero_le_one (div_pos hδ hK1).le) hK1.le
    _ = δ := mul_div_cancel₀ δ hK1.ne'

theorem inv_sq_mul_le_aux {s n ρ : ℝ} (hs : 0 < s) (hn : n ≤ s ^ 2 * ρ) : s⁻¹ ^ 2 * n ≤ ρ := by
  have h2 : 0 < s ^ 2 := by positivity
  rw [inv_pow, inv_mul_le_iff₀ h2]
  exact hn

theorem prod_sqrt_sq_aux {k : ℕ} (n : Fin k → ℝ) {ε ρ : ℝ} (hn : ∀ l, 0 ≤ n l) (hε : 0 < ε)
    (hρ : 0 < ρ) :
    (∏ l, Real.sqrt ((n l + ε) / ρ)) ^ 2 = (∏ l, (n l + ε)) / ρ ^ k := by
  rw [← Finset.prod_pow]
  have e : ∀ l, Real.sqrt ((n l + ε) / ρ) ^ 2 = (n l + ε) / ρ := fun l =>
    Real.sq_sqrt (div_nonneg (by linarith [hn l]) hρ.le)
  simp only [e]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The core of the scaling argument: if `‖h_l‖² ≤ s_l² ρ` then `‖G[u; h]‖² ≤ (∏ s_l)² · const`. -/
theorem block_bound_scaled {G : FibreMap I M Λ (blkRanks a b₀ k) b'} (hG : IsBlockMultilinear G)
    (lam : Λ) {T : ℝ} (hT : 0 < T) (hTT : T ≤ G.T₀) {p N : ℕ} (hp : 1 ≤ p)
    {W : ∀ q, ℝ → SmoothCcTensor g 0 (blkRanks a b₀ k q)}
    {w : ∀ c : κ, ℝ → SmoothCcTensor g 0 (a c)} (hWw : W = joinFam w zeroBlk)
    {δ R C₁ K ρ B : ℝ} (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ V : ∀ q, ℝ → SmoothCcTensor g 0 (blkRanks a b₀ k q),
      (∀ q, JointlySmoothOn g 0 (blkRanks a b₀ k q) (Icc 0 T) (V q)) →
      (∀ q, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 0 (blkRanks a b₀ k q) x
          ((V q t - W q t).toSection x) ≤ δ) →
      (∀ q j i, 2 * (2 * p * j + i) ≤ 2 * p * N → ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        jetSq g T (V q) j i t x ≤ R) →
      ∀ j i, 2 * p * j + i ≤ 2 * p * N → ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        jetSq g T (G.apply lam V) j i t x ≤
          C₁ * (1 + ∑ q, ∑ j' ∈ Finset.range (j + 1), ∑ i' ∈ Finset.range (i + 1),
            jetSq g T (V q) j' i' t x))
    {Ce : κ ⊕ (Fin k × ι₀) → ℝ} (hCe0 : ∀ q, 0 ≤ Ce q) (hCeK : ∀ q, Ce q ≤ K)
    (hCe : ∀ q, ∀ V : ℝ → SmoothCcTensor g 0 (blkRanks a b₀ k q),
      JointlySmoothOn g 0 (blkRanks a b₀ k q) (Icc 0 T) V →
      ∀ j i, 2 * (2 * p * j + i) ≤ 2 * p * N → ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        jetSq g T V j i t x ≤ Ce q * parabolicInner g (blkRanks a b₀ k q) p N T V V)
    (hρ0 : 0 < ρ) (hKρ : K * ρ ≤ δ) (hR : K * (B + ρ) ≤ R)
    {u : ∀ c : κ, ℝ → SmoothCcTensor g 0 (a c)} (hu : ∀ c, JointlySmoothOn g 0 (a c) (Icc 0 T) (u c))
    (hutube : ∀ c, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (a c) x ((u c t - w c t).toSection x) ≤ δ)
    (huB : ∑ c, parabolicInner g (a c) p N T (u c) (u c) ≤ B)
    (hudom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      valAt (fun q => joinFam u (zeroBlk (g := g) (b₀ := b₀) (k := k)) q t) x ∈ G.dom lam t x)
    {h : Fin k → ∀ c : ι₀, ℝ → SmoothCcTensor g 0 (b₀ c)}
    (hh : ∀ l c, JointlySmoothOn g 0 (b₀ c) (Icc 0 T) (h l c))
    {s : Fin k → ℝ} (hs : ∀ l, 0 < s l)
    (hn : ∀ l, ∑ c, parabolicInner g (b₀ c) p N T (h l c) (h l c) ≤ s l ^ 2 * ρ) :
    parabolicInner g b' p N T (G.apply lam (joinFam u h)) (G.apply lam (joinFam u h)) ≤
      (∏ l, s l) ^ 2 * (C₁ * parabolicCount p N *
        (T * (riemannianVolumeMeasure (I := I) (M := M) g).real univ + 1) * (1 + (B + k * ρ))) := by
  have hB0 : 0 ≤ B := (Finset.sum_nonneg fun c _ => parabolicInner_self_nonneg p N (u c)).trans huB
  set h' : Fin k → ∀ c : ι₀, ℝ → SmoothCcTensor g 0 (b₀ c) := fun l c τ => (s l)⁻¹ • h l c τ
    with hh'_def
  have hh' : ∀ l c, JointlySmoothOn g 0 (b₀ c) (Icc 0 T) (h' l c) := fun l c =>
    jointlySmoothOn_smul _ (hh l c)
  have hn'sum : ∀ l, ∑ c, parabolicInner g (b₀ c) p N T (h' l c) (h' l c) ≤ ρ := by
    intro l
    have e : ∑ c, parabolicInner g (b₀ c) p N T (h' l c) (h' l c) =
        (s l)⁻¹ ^ 2 * ∑ c, parabolicInner g (b₀ c) p N T (h l c) (h l c) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => parabolicInner_smul_self (hh l c) _ p N
    rw [e]
    exact inv_sq_mul_le_aux (hs l) (hn l)
  have hn' : ∀ l c, parabolicInner g (b₀ c) p N T (h' l c) (h' l c) ≤ ρ := fun l c =>
    (Finset.single_le_sum (f := fun c => parabolicInner g (b₀ c) p N T (h' l c) (h' l c))
      (fun c _ => parabolicInner_self_nonneg p N _) (Finset.mem_univ c)).trans (hn'sum l)
  set V := joinFam u h' with hV_def
  have hV : ∀ q, JointlySmoothOn g 0 (blkRanks a b₀ k q) (Icc 0 T) (V q) :=
    jointlySmoothOn_joinFam hu hh'
  have hVdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, valAt (fun q => V q t) x ∈ G.dom lam t x :=
    fun t ht x => (hG.dom_iff lam t x _ _ (fbase_valAt_joinFam u zeroBlk h' t x)).mp (hudom t ht x)
  have htube : ∀ q, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (blkRanks a b₀ k q) x
        ((V q t - W q t).toSection x) ≤ δ := by
    subst hWw
    rintro (c | ⟨l, c⟩) t ht x
    · exact hutube c t ht x
    · change riemannianFiberNormSq (I := I) (M := M) g 0 (b₀ c) x ((h' l c t - 0).toSection x) ≤ δ
      rw [sub_zero, ← jetSq_zero_zero (T := T)]
      refine (hCe (.inr (l, c)) (h' l c) (hh' l c) 0 0 (by simp) t ht x).trans ?_
      exact (mul_le_mul_aux (hCe0 _) (hCeK _) (parabolicInner_self_nonneg p N _) (hn' l c)).trans hKρ
  have hlow : ∀ q j i, 2 * (2 * p * j + i) ≤ 2 * p * N → ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      jetSq g T (V q) j i t x ≤ R := by
    rintro (c | ⟨l, c⟩) j i hw t ht x
    · refine (hCe (.inl c) (u c) (hu c) j i hw t ht x).trans ?_
      have hc : parabolicInner g (a c) p N T (u c) (u c) ≤ B :=
        (Finset.single_le_sum (f := fun c => parabolicInner g (a c) p N T (u c) (u c))
          (fun c _ => parabolicInner_self_nonneg p N _) (Finset.mem_univ c)).trans huB
      refine (mul_le_mul_aux (hCe0 _) (hCeK _) (parabolicInner_self_nonneg p N _) hc).trans ?_
      refine le_trans ?_ hR
      exact mul_le_mul_of_nonneg_left (by linarith) ((hCe0 (.inl c)).trans (hCeK _))
    · refine (hCe (.inr (l, c)) (h' l c) (hh' l c) j i hw t ht x).trans ?_
      refine (mul_le_mul_aux (hCe0 _) (hCeK _) (parabolicInner_self_nonneg p N _) (hn' l c)).trans ?_
      refine le_trans ?_ hR
      exact mul_le_mul_of_nonneg_left (by linarith) ((hCe0 (.inr (l, c))).trans (hCeK _))
  have hpt := hC₁ V hV htube hlow
  have hφ := (G.jointlySmoothOn_fibreApply lam hTT hV hVdom).2
  have hint := parabolicInner_le_of_jetSq_le hT hφ hV hC₁0 (p := p) (N := N)
    (fun j i hj hi t ht x => (hpt j i ((weight_le_iff hp).mpr ⟨hj, hi⟩) t ht x).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl (Finset.sum_le_sum fun q _ =>
        sum_jetSq_le_parabolicJetSq hj hi (V q) t x)) hC₁0))
  have hsumV : ∑ q, parabolicInner g (blkRanks a b₀ k q) p N T (V q) (V q) ≤ B + k * ρ := by
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
    refine add_le_add huB ?_
    calc ∑ l, ∑ c, parabolicInner g (b₀ c) p N T (h' l c) (h' l c) ≤ ∑ _l : Fin k, ρ :=
          Finset.sum_le_sum fun l _ => hn'sum l
      _ = k * ρ := by simp
  have hcnt : 0 ≤ C₁ * parabolicCount p N *
      (T * (riemannianVolumeMeasure (I := I) (M := M) g).real univ + 1) :=
    mul_nonneg (mul_nonneg hC₁0 (Nat.cast_nonneg _))
      (add_nonneg (mul_nonneg hT.le measureReal_nonneg) zero_le_one)
  have hGV : parabolicInner g b' p N T (G.apply lam V) (G.apply lam V) ≤
      C₁ * parabolicCount p N * (T * (riemannianVolumeMeasure (I := I) (M := M) g).real univ + 1) *
        (1 + (B + k * ρ)) :=
    hint.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hsumV) hcnt)
  -- scaling back
  have hss : (fun l c τ => s l • h' l c τ) = h := by
    funext l c τ
    simp only [hh'_def, smul_smul, mul_inv_cancel₀ (hs l).ne', one_smul]
  have hscale := apply_joinFam_smul hG lam u h' (s := s) fun l => (hs l).ne'
  rw [hss] at hscale
  rw [hscale, parabolicInner_smul_self hφ]
  exact mul_le_mul_of_nonneg_left hGV (sq_nonneg _)

theorem final_arith_aux {P D C₂ B B' k ρ : ℝ} (hP : 0 ≤ P) (hD : 0 < D) (hC : 0 ≤ C₂) (hB : B ≤ B') :
    P / D * (C₂ * (1 + (B + k * ρ))) ≤ C₂ * (1 + (B' + k * ρ)) / D * P := by
  have h : C₂ * (1 + (B + k * ρ)) ≤ C₂ * (1 + (B' + k * ρ)) :=
    mul_le_mul_of_nonneg_left (by linarith) hC
  calc P / D * (C₂ * (1 + (B + k * ρ))) = C₂ * (1 + (B + k * ρ)) / D * P := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h hD.le) hP

/-- `X ≤ C ∏ (n_l + ε)` for all `ε > 0` gives `X ≤ C ∏ n_l`. -/
theorem le_of_forall_prod_add {k : ℕ} {X C : ℝ} (n : Fin k → ℝ)
    (h : ∀ ε > 0, X ≤ C * ∏ l, (n l + ε)) : X ≤ C * ∏ l, n l := by
  have hcont : Continuous fun ε : ℝ => C * ∏ l, (n l + ε) :=
    continuous_const.mul (continuous_finset_prod _ fun l _ => continuous_const.add continuous_id)
  have ht := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simp only [add_zero] at ht
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => h ε hε)

/-- **The multilinear composition bound** (bound (M) of `prop:nemytskii`). Let `G(ζ; η₁, …, η_k)` be
multilinear in the blocks, `N ≥ ⌊n/2p⌋ + 3`, and `w` a smooth reference tuple in the domain. There
is `δ > 0` such that for every `B` there is `C` with
`‖G[u; h₁, …, h_k]‖²_{𝒫^N} ≤ C ∏_l Σ_c ‖h_{l,c}‖²_{𝒫^N}` for all smooth `u` with
`|u - w|² ≤ δ` pointwise, `Σ_c ‖u_c‖²_{𝒫^N} ≤ B` and values in the domain, and all smooth blocks
`h_l`. -/
theorem exists_block_bound {G : FibreMap I M Λ (blkRanks a b₀ k) b'} (hG : IsBlockMultilinear G)
    (lam : Λ) {T : ℝ} (hT : 0 < T) (hTT : T ≤ G.T₀) {p N : ℕ} (hp : 1 ≤ p)
    (hN : Module.finrank ℝ E / (2 * p) + 3 ≤ N)
    {w : ∀ c : κ, ℝ → SmoothCcTensor g 0 (a c)} (hw : ∀ c, JointlySmoothOn g 0 (a c) (Icc 0 T) (w c))
    (hwdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      valAt (fun q => joinFam w (zeroBlk (g := g) (b₀ := b₀) (k := k)) q t) x ∈ G.dom lam t x) :
    ∃ δ > 0, ∀ B : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : ∀ c : κ, ℝ → SmoothCcTensor g 0 (a c), (∀ c, JointlySmoothOn g 0 (a c) (Icc 0 T) (u c)) →
        (∀ c, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 0 (a c) x ((u c t - w c t).toSection x) ≤ δ) →
        ∑ c, parabolicInner g (a c) p N T (u c) (u c) ≤ B →
        (∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
          valAt (fun q => joinFam u (zeroBlk (g := g) (b₀ := b₀) (k := k)) q t) x ∈ G.dom lam t x) →
        ∀ h : Fin k → ∀ c : ι₀, ℝ → SmoothCcTensor g 0 (b₀ c),
          (∀ l c, JointlySmoothOn g 0 (b₀ c) (Icc 0 T) (h l c)) →
          parabolicInner g b' p N T (G.apply lam (joinFam u h)) (G.apply lam (joinFam u h)) ≤
            C * ∏ l, ∑ c, parabolicInner g (b₀ c) p N T (h l c) (h l c) := by
  classical
  obtain ⟨δ, hδ, -, hR⟩ := G.exists_tame_pointwise lam hT hTT (W := joinFam w zeroBlk)
    (jointlySmoothOn_joinFam hw jointlySmoothOn_zeroBlk) hwdom (p := p) (by omega) (2 * p * N)
  have hemb := fun q => exists_jetSq_le_parabolicInner (g := g) hT hp hN (blkRanks a b₀ k q)
  choose Ce hCe0 hCe using hemb
  obtain ⟨K, hK0, hCeK⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ q, Ce q ≤ K :=
    ⟨∑ q, Ce q, Finset.sum_nonneg fun q _ => hCe0 q,
      fun q => Finset.single_le_sum (fun q _ => hCe0 q) (Finset.mem_univ q)⟩
  obtain ⟨ρ, hρ0, hKρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ K * ρ ≤ δ :=
    ⟨_, (rho_aux hδ hK0).1, (rho_aux hδ hK0).2.2⟩
  refine ⟨δ, hδ, fun B => ?_⟩
  obtain ⟨C₁, hC₁0, hC₁⟩ := hR (K * (B + ρ))
  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℝ, C₂ = C₁ * parabolicCount p N *
      (T * (riemannianVolumeMeasure (I := I) (M := M) g).real univ + 1) := ⟨_, rfl⟩
  have hC₂0 : 0 ≤ C₂ := by
    rw [hC₂]
    exact mul_nonneg (mul_nonneg hC₁0 (Nat.cast_nonneg _))
      (add_nonneg (mul_nonneg hT.le measureReal_nonneg) zero_le_one)
  refine ⟨C₂ * (1 + (|B| + k * ρ)) / ρ ^ k,
    div_nonneg (mul_nonneg hC₂0 (add_nonneg zero_le_one (add_nonneg (abs_nonneg B)
      (mul_nonneg (Nat.cast_nonneg k) hρ0.le)))) (pow_nonneg hρ0.le k), ?_⟩
  intro u hu hutube huB hudom h hh
  have hn0 : ∀ l, 0 ≤ ∑ c, parabolicInner g (b₀ c) p N T (h l c) (h l c) := fun l =>
    Finset.sum_nonneg fun c _ => parabolicInner_self_nonneg p N _
  refine le_of_forall_prod_add (fun l => ∑ c, parabolicInner g (b₀ c) p N T (h l c) (h l c))
    fun ε hε => ?_
  have hs : ∀ l, 0 < Real.sqrt ((∑ c, parabolicInner g (b₀ c) p N T (h l c) (h l c) + ε) / ρ) :=
    fun l => Real.sqrt_pos.mpr (div_pos (by linarith [hn0 l]) hρ0)
  have hsn : ∀ l, ∑ c, parabolicInner g (b₀ c) p N T (h l c) (h l c) ≤
      Real.sqrt ((∑ c, parabolicInner g (b₀ c) p N T (h l c) (h l c) + ε) / ρ) ^ 2 * ρ := by
    intro l
    rw [Real.sq_sqrt (div_nonneg (by linarith [hn0 l]) hρ0.le), div_mul_cancel₀ _ hρ0.ne']
    linarith
  have key := block_bound_scaled hG lam hT hTT hp rfl hC₁0 hC₁ hCe0 hCeK hCe hρ0 hKρ le_rfl hu
    hutube huB hudom hh hs hsn
  rw [prod_sqrt_sq_aux (fun l => ∑ c, parabolicInner g (b₀ c) p N T (h l c) (h l c)) hn0 hε hρ0,
    ← hC₂] at key
  exact key.trans (final_arith_aux (Finset.prod_nonneg fun l _ => by linarith [hn0 l])
    (pow_pos hρ0 k) hC₂0 (le_abs_self B))

/-! ### Bound (M) for the iterated fibre derivatives -/

section Deriv

variable {ι : Type*} [Fintype ι] {b : ι → ℕ}

/-- **`g_k(u)(h₁, …, h_k) = D^k_ζ F(t, u)[h₁, …, h_k]`** at the level of families. -/
def derivFam (Φ : FibreMap I M Λ b b') (k : ℕ) (lam : Λ) (u : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c))
    (h : Fin k → ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)) : ℝ → SmoothCcTensor g 0 b' :=
  (Φ.fibreDeriv k).apply lam (joinFam u h)

/-- `g_k(u)(h)` is jointly smooth when `u` and `h` are and `u` has values in the domain; its values
are `D^k_ζ F(t, u)[h]`. -/
theorem jointlySmoothOn_derivFam (Φ : FibreMap I M Λ b b') (k : ℕ) (lam : Λ) {T : ℝ}
    (hTT : T ≤ Φ.T₀) {u : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)}
    (hu : ∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (u c))
    (hudom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, valAt (fun c => u c t) x ∈ Φ.dom lam t x)
    {h : Fin k → ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)}
    (hh : ∀ l c, JointlySmoothOn g 0 (b c) (Icc 0 T) (h l c)) :
    (∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, (Φ.derivFam k lam u h t).toSection x =
      Φ.derivF k lam t x (valAt (fun q => joinFam u h q t) x)) ∧
    JointlySmoothOn g 0 b' (Icc 0 T) (Φ.derivFam k lam u h) := by
  have hj := (Φ.fibreDeriv k).jointlySmoothOn_fibreApply lam hTT (jointlySmoothOn_joinFam hu hh)
    (fun t ht x => hudom t ht x)
  exact ⟨fun t ht x => apply_toSection _ lam _ t (hj.1 t ht) x, hj.2⟩

/-- **Bound (M)** for `g_k(u)(h₁, …, h_k) = D^k_ζ F(t, u)[h₁, …, h_k]`: near a smooth reference `w`
with values in the domain,
`‖g_k(u)(h)‖²_{𝒫^N} ≤ C ∏_l ‖h_l‖²_{𝒫^N}` for smooth `u` in a pointwise tube around `w`, with
bounded `𝒫^N` norm and values in the domain. -/
theorem exists_derivFam_bound (Φ : FibreMap I M Λ b b') (k : ℕ) (lam : Λ) {T : ℝ} (hT : 0 < T)
    (hTT : T ≤ Φ.T₀) {p N : ℕ} (hp : 1 ≤ p) (hN : Module.finrank ℝ E / (2 * p) + 3 ≤ N)
    {w : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)} (hw : ∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (w c))
    (hwdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, valAt (fun c => w c t) x ∈ Φ.dom lam t x) :
    ∃ δ > 0, ∀ B : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c), (∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (u c)) →
        (∀ c, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 0 (b c) x ((u c t - w c t).toSection x) ≤ δ) →
        ∑ c, parabolicInner g (b c) p N T (u c) (u c) ≤ B →
        (∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, valAt (fun c => u c t) x ∈ Φ.dom lam t x) →
        ∀ h : Fin k → ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c),
          (∀ l c, JointlySmoothOn g 0 (b c) (Icc 0 T) (h l c)) →
          parabolicInner g b' p N T (Φ.derivFam k lam u h) (Φ.derivFam k lam u h) ≤
            C * ∏ l, ∑ c, parabolicInner g (b c) p N T (h l c) (h l c) := by
  obtain ⟨δ, hδ, hB⟩ := exists_block_bound (isBlockMultilinear_fibreDeriv Φ k) lam hT hTT hp hN hw
    (fun t ht x => hwdom t ht x)
  refine ⟨δ, hδ, fun B => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hB B
  exact ⟨C, hC0, fun u hu hut huB hud h hh => hC u hu hut huB (fun t ht x => hud t ht x) h hh⟩

end Deriv

end FibreMap

end ShortTime
