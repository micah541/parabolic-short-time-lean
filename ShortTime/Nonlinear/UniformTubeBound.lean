import ShortTime.Nonlinear.UniformTubeDeriv
import ShortTime.Nonlinear.UniformTubeTaylor
import ShortTime.Nonlinear.FibreCalcBound
import ShortTime.Nonlinear.FibreCalcRemainder

/-!
# Uniform tube radius for the multilinear bounds (stage 4)

`exists_block_bound_gen`: bound (M) for a block-multilinear fibre map, given a tube radius `δ` with
`TameGood`. `exists_derivFam_bound_unif`, `exists_taylor_bound_unif`: **one** `δ` for all `k`.
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

namespace FibreMap

section BlockGen

variable {κ ι₀ : Type*} [Fintype κ] [Fintype ι₀] {a : κ → ℕ} {b₀ : ι₀ → ℕ} {k : ℕ}
variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] {b' : ℕ}

theorem exists_block_bound_gen {G : FibreMap I M Λ (blkRanks a b₀ k) b'} (hG : IsBlockMultilinear G)
    (lam : Λ) {T : ℝ} (hT : 0 < T) (hTT : T ≤ G.T₀) {p N : ℕ} (hp : 1 ≤ p)
    (hN : Module.finrank ℝ E / (2 * p) + 3 ≤ N)
    {w : ∀ c : κ, ℝ → SmoothCcTensor g 0 (a c)} (hw : ∀ c, JointlySmoothOn g 0 (a c) (Icc 0 T) (w c))
    (hwdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      valAt (fun q => joinFam w (zeroBlk (g := g) (b₀ := b₀) (k := k)) q t) x ∈ G.dom lam t x)
    {δ : ℝ} (hδ : 0 < δ)
    (hgood : TameGood G lam T (joinFam w (zeroBlk (g := g) (b₀ := b₀) (k := k))) p (2 * p * N) δ) :
    ∀ B : ℝ, ∃ C : ℝ, 0 ≤ C ∧
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
  have hR := hgood.2
  have hemb := fun q => exists_jetSq_le_parabolicInner (g := g) hT hp hN (blkRanks a b₀ k q)
  choose Ce hCe0 hCe using hemb
  obtain ⟨K, hK0, hCeK⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ q, Ce q ≤ K :=
    ⟨∑ q, Ce q, Finset.sum_nonneg fun q _ => hCe0 q,
      fun q => Finset.single_le_sum (fun q _ => hCe0 q) (Finset.mem_univ q)⟩
  obtain ⟨ρ, hρ0, hKρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ K * ρ ≤ δ :=
    ⟨_, (rho_aux hδ hK0).1, (rho_aux hδ hK0).2.2⟩
  intro B
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

end BlockGen

section TaylorDeriv

variable {ι : Type*} [Fintype ι] {b : ι → ℕ}
variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] {b' : ℕ}

/-- **Bound (M) for all `k` with one tube radius.** -/
theorem exists_derivFam_bound_unif (Φ : FibreMap I M Λ b b') (lam : Λ) {T : ℝ} (hT : 0 < T)
    (hTT : T ≤ Φ.T₀) {p N : ℕ} (hp : 1 ≤ p) (hN : Module.finrank ℝ E / (2 * p) + 3 ≤ N)
    {w : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)} (hw : ∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (w c))
    (hwdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, valAt (fun c => w c t) x ∈ Φ.dom lam t x) :
    ∃ δ > 0, ∀ k : ℕ, ∀ B : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c), (∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (u c)) →
        (∀ c, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 0 (b c) x ((u c t - w c t).toSection x) ≤ δ) →
        ∑ c, parabolicInner g (b c) p N T (u c) (u c) ≤ B →
        (∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, valAt (fun c => u c t) x ∈ Φ.dom lam t x) →
        ∀ h : Fin k → ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c),
          (∀ l c, JointlySmoothOn g 0 (b c) (Icc 0 T) (h l c)) →
          parabolicInner g b' p N T (Φ.derivFam k lam u h) (Φ.derivFam k lam u h) ≤
            C * ∏ l, ∑ c, parabolicInner g (b c) p N T (h l c) (h l c) := by
  obtain ⟨δ, hδ, hg⟩ := exists_uniform_good_deriv Φ lam hT hTT hw hwdom (p := p) (by omega)
    (2 * p * N)
  refine ⟨δ, hδ, fun k B => ?_⟩
  obtain ⟨C, hC0, hC⟩ := exists_block_bound_gen (isBlockMultilinear_fibreDeriv Φ k) lam hT hTT hp
    hN hw hwdom hδ (hg k) B
  exact ⟨C, hC0, fun u hu hut huB hud h hh => hC u hu hut huB (fun t ht x => hud t ht x) h hh⟩

theorem exists_taylor_bound_aux (Φ : FibreMap I M Λ b b') (k : ℕ) (lam : Λ) {T : ℝ} (hT : 0 < T)
    (hTT : T ≤ Φ.T₀) {p N : ℕ} (hp : 1 ≤ p) (hN : Module.finrank ℝ E / (2 * p) + 3 ≤ N)
    [CompleteSpace E]
    {w : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)} (hw : ∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (w c))
    (hwdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, valAt (fun c => w c t) x ∈ Φ.dom lam t x)
    {δ : ℝ} (hδ : 0 < δ)
    (hg : TameGood (Φ.taylorMap k) lam T
      (joinFam (pairFam w (fun _ _ => 0)) (zeroBlk (g := g) (b₀ := b) (k := k + 2))) p (2 * p * N) δ) :
    ∀ B : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u h : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c),
        (∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (u c)) →
        (∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (h c)) →
        (∀ c, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 0 (b c) x ((u c t - w c t).toSection x) ≤ δ) →
        (∀ c, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 0 (b c) x ((h c t).toSection x) ≤ δ) →
        ∑ c, parabolicInner g (b c) p N T (u c) (u c) +
          ∑ c, parabolicInner g (b c) p N T (h c) (h c) ≤ B →
        (∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ τ ∈ Icc (0 : ℝ) 1,
          valAt (fun c => u c t) x + τ • valAt (fun c => h c t) x ∈ Φ.dom lam t x) →
        ∀ hs : Fin k → ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c),
          (∀ l c, JointlySmoothOn g 0 (b c) (Icc 0 T) (hs l c)) →
          parabolicInner g b' p N T
              (fun t => Φ.derivFam k lam (fun c τ => u c τ + h c τ) hs t -
                Φ.derivFam k lam u hs t - Φ.derivFam (k + 1) lam u (Fin.cons h hs) t)
              (fun t => Φ.derivFam k lam (fun c τ => u c τ + h c τ) hs t -
                Φ.derivFam k lam u hs t - Φ.derivFam (k + 1) lam u (Fin.cons h hs) t) ≤
            C * (∑ c, parabolicInner g (b c) p N T (h c) (h c)) ^ 2 *
              ∏ l, ∑ c, parabolicInner g (b c) p N T (hs l c) (hs l c) := by
  have hz : ∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (fun _ : ℝ => (0 : SmoothCcTensor g 0 (b c))) :=
    fun c => jointlySmoothOn_const g _ (0 : SmoothCcTensor g 0 (b c))
  have hB := exists_block_bound_gen (isBlockMultilinear_taylorMap Φ k) lam hT hTT hp hN
    (w := pairFam w fun _ _ => 0) (jointlySmoothOn_pairFam hw hz) (fun t ht x τ _ => by
      have e : psnd (fbase (valAt (fun q => joinFam (pairFam w fun _ _ => 0)
          (zeroBlk (g := g) (b₀ := b) (k := k + 2)) q t) x)) = 0 := by
        funext c
        exact toSection_zero_apply x
      show pfst (fbase _) + τ • psnd (fbase _) ∈ Φ.dom lam t x
      rw [e, smul_zero, add_zero]
      exact hwdom t ht x) hδ hg
  intro B
  obtain ⟨C, hC0, hC⟩ := hB B
  refine ⟨C, hC0, ?_⟩
  intro u h hu hh hut hht huB hseg hs hhs
  have hconsS : ∀ l c, JointlySmoothOn g 0 (b c) (Icc 0 T)
      ((Fin.cons h hs : Fin (k + 1) → ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)) l c) := by
    intro l c
    refine Fin.cases ?_ (fun i => ?_) l
    · exact hh c
    · exact hhs i c
  have hconsS2 : ∀ l c, JointlySmoothOn g 0 (b c) (Icc 0 T)
      ((Fin.cons h (Fin.cons h hs) : Fin (k + 2) → ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)) l c) := by
    intro l c
    refine Fin.cases ?_ (fun i => ?_) l
    · exact hh c
    · exact hconsS i c
  have hQ := hC (pairFam u h) (jointlySmoothOn_pairFam hu hh)
    (by
      rintro (c | c) t ht x
      · exact hut c t ht x
      · change riemannianFiberNormSq (I := I) (M := M) g 0 (b c) x ((h c t - 0).toSection x) ≤ δ
        rw [sub_zero]
        exact hht c t ht x)
    (by rw [Fintype.sum_sum_type]; exact huB)
    (fun t ht x τ hτ => hseg t ht x τ hτ)
    (Fin.cons h (Fin.cons h hs)) hconsS2
  -- the remainder agrees with `Q_k` on `[0,T]`
  have hdom0 : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, valAt (fun c => u c t) x ∈ Φ.dom lam t x :=
    fun t ht x => by simpa using hseg t ht x 0 ⟨le_rfl, zero_le_one⟩
  have hvadd : ∀ t x, valAt (fun c => u c t + h c t) x =
      valAt (fun c => u c t) x + valAt (fun c => h c t) x := fun t x => by
    funext c
    exact toSection_add_apply _ _ x
  have hdom1 : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      valAt (fun c => u c t + h c t) x ∈ Φ.dom lam t x :=
    fun t ht x => by simpa [hvadd] using hseg t ht x 1 ⟨zero_le_one, le_rfl⟩
  have huh : ∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (fun τ => u c τ + h c τ) := fun c =>
    jointlySmoothOn_add (hu c) (hh c)
  have hR : JointlySmoothOn g 0 b' (Icc 0 T)
      (fun t => Φ.derivFam k lam (fun c τ => u c τ + h c τ) hs t -
        Φ.derivFam k lam u hs t - Φ.derivFam (k + 1) lam u (Fin.cons h hs) t) :=
    jointlySmoothOn_sub (jointlySmoothOn_sub
      (Φ.jointlySmoothOn_derivFam k lam hTT huh hdom1 hhs).2
      (Φ.jointlySmoothOn_derivFam k lam hTT hu hdom0 hhs).2)
      (Φ.jointlySmoothOn_derivFam (k + 1) lam hTT hu hdom0 hconsS).2
  rw [parabolicInner_congr_self hT hR (Φ.jointlySmoothOn_taylorFam k lam hTT hu hh hseg hconsS2).2
    (fun t ht => Φ.derivFam_taylor k lam hTT hu hh hseg hhs t ht) p N]
  refine hQ.trans (le_of_eq ?_)
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

/-- **Bound (T) for all `k` with one tube radius.** -/
theorem exists_taylor_bound_unif (Φ : FibreMap I M Λ b b') (lam : Λ) {T : ℝ} (hT : 0 < T)
    (hTT : T ≤ Φ.T₀) {p N : ℕ} (hp : 1 ≤ p) (hN : Module.finrank ℝ E / (2 * p) + 3 ≤ N)
    {w : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)} (hw : ∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (w c))
    (hwdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, valAt (fun c => w c t) x ∈ Φ.dom lam t x) :
    ∃ δ > 0, ∀ k : ℕ, ∀ B : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u h : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c),
        (∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (u c)) →
        (∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (h c)) →
        (∀ c, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 0 (b c) x ((u c t - w c t).toSection x) ≤ δ) →
        (∀ c, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 0 (b c) x ((h c t).toSection x) ≤ δ) →
        ∑ c, parabolicInner g (b c) p N T (u c) (u c) +
          ∑ c, parabolicInner g (b c) p N T (h c) (h c) ≤ B →
        (∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ τ ∈ Icc (0 : ℝ) 1,
          valAt (fun c => u c t) x + τ • valAt (fun c => h c t) x ∈ Φ.dom lam t x) →
        ∀ hs : Fin k → ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c),
          (∀ l c, JointlySmoothOn g 0 (b c) (Icc 0 T) (hs l c)) →
          parabolicInner g b' p N T
              (fun t => Φ.derivFam k lam (fun c τ => u c τ + h c τ) hs t -
                Φ.derivFam k lam u hs t - Φ.derivFam (k + 1) lam u (Fin.cons h hs) t)
              (fun t => Φ.derivFam k lam (fun c τ => u c τ + h c τ) hs t -
                Φ.derivFam k lam u hs t - Φ.derivFam (k + 1) lam u (Fin.cons h hs) t) ≤
            C * (∑ c, parabolicInner g (b c) p N T (h c) (h c)) ^ 2 *
              ∏ l, ∑ c, parabolicInner g (b c) p N T (hs l c) (hs l c) := by
  have hz : ∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (fun _ : ℝ => (0 : SmoothCcTensor g 0 (b c))) :=
    fun c => jointlySmoothOn_const g _ (0 : SmoothCcTensor g 0 (b c))
  obtain ⟨δ, hδ, hg⟩ := exists_uniform_good_taylor Φ lam hT hTT hw hwdom (p := p) (by omega)
    (2 * p * N)
  exact ⟨δ, hδ, fun k => exists_taylor_bound_aux Φ k lam hT hTT hp hN hw hwdom hδ (hg k)⟩

end TaylorDeriv

end FibreMap

end ShortTime
