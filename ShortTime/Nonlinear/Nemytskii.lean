import ShortTime.Nonlinear.NemytskiiDef
import ShortTime.Nonlinear.NemytskiiExt
import ShortTime.Nonlinear.NemytskiiTube
import ShortTime.Nonlinear.LinOp
import ShortTime.Nonlinear.Formal

/-!
# The nonlinear operator on the parabolic spaces (`cor:N`)

Let `w` be a jointly smooth family on `[0,T]` with `2p`-jets in the domain, and
`m ≥ ⌊n/2p⌋ + 4`. Then `u ↦ F[u]` extends from the smooth families near `w` to a map
`𝒩 : 𝒫^m → 𝒫^{m-1}` which is `C^∞` at `w`, agrees with `F[u]` on smooth families near `w` (whose
jets then lie in the domain), and whose derivative at `w` is the linearization `L_w`
(`EquationData.exists_nonlinOp`).

*Proof.* The would-be derivatives `g_k(v)(h) = D^k_ζ F(t, j v)[j h₁, …, j h_k]`
(`EquationData.gCML`) satisfy the bounds (M) (`exists_gfun_bound`, from
`FibreMap.exists_derivFam_bound`) and (T) (`exists_gfun_taylor`, from
`FibreMap.exists_taylor_bound`) on balls around `w` in the subspace of smooth families, through the
pointwise embedding (`exists_fiberNormSq_jet_le`) and the jet bound `sum_jetFamily_le`. The jets stay
in the domain by the tube lemma (`exists_dom_tube`). The radius of these balls may depend on the
order `k`, so the smooth extension is applied at each finite order
(`SmoothExtension.exists_contDiffAt_extension`), which gives smoothness at `w`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter Topology MeasureTheory Metric
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Spectral
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

open ParabolicSpace

/-! ### Arithmetic -/

theorem exists_pos_le_fin (f : ℕ → ℝ) (hf : ∀ k, 0 < f k) (n : ℕ) :
    ∃ δ > 0, ∀ k ≤ n, δ ≤ f k := by
  induction n with
  | zero => exact ⟨f 0, hf 0, fun k hk => by rw [Nat.le_zero.1 hk]⟩
  | succ n ih =>
    obtain ⟨δ, hδ, h⟩ := ih
    refine ⟨min δ (f (n + 1)), lt_min hδ (hf _), fun k hk => ?_⟩
    rcases Nat.lt_or_ge k (n + 1) with h1 | h1
    · exact (min_le_left _ _).trans (h k (by omega))
    · rw [show k = n + 1 by omega]
      exact min_le_right _ _

theorem exists_radius {Ce δ : ℝ} (hCe : 0 ≤ Ce) (hδ : 0 < δ) : ∃ r > 0, Ce * (2 * r) ^ 2 ≤ δ := by
  have hc : 0 < Ce + 1 := by linarith
  refine ⟨Real.sqrt (δ / (4 * (Ce + 1))), Real.sqrt_pos.2 (by positivity), ?_⟩
  have h1 : (2 * Real.sqrt (δ / (4 * (Ce + 1)))) ^ 2 = δ / (Ce + 1) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
    ring
  rw [h1, mul_div_assoc', div_le_iff₀ hc]
  nlinarith

theorem sq_le_two_mul_sq {a r : ℝ} (ha : 0 ≤ a) (h : a < r) : a ^ 2 ≤ (2 * r) ^ 2 :=
  pow_le_pow_left₀ ha (by linarith) 2

theorem prod_bound_aux {k : ℕ} (a n : Fin k → ℝ) {K : ℝ} (ha : ∀ l, 0 ≤ a l)
    (h : ∀ l, a l ≤ K * n l ^ 2) : ∏ l, a l ≤ K ^ k * (∏ l, n l) ^ 2 := by
  calc ∏ l, a l ≤ ∏ l, (K * n l ^ 2) :=
        Finset.prod_le_prod (fun l _ => ha l) (fun l _ => h l)
    _ = K ^ k * (∏ l, n l) ^ 2 := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          Finset.prod_pow]

theorem taylor_arith {x C₀ S P K a Q : ℝ} (k : ℕ) (hC₀ : 0 ≤ C₀) (hS0 : 0 ≤ S) (hP0 : 0 ≤ P)
    (hx : x ≤ C₀ * S ^ 2 * P) (hS : S ≤ K * a) (hP : P ≤ K ^ k * Q ^ 2) :
    x ≤ C₀ * K ^ (k + 2) * (a * Q) ^ 2 := by
  have h1 : S ^ 2 ≤ (K * a) ^ 2 := pow_le_pow_left₀ hS0 hS 2
  calc x ≤ C₀ * S ^ 2 * P := hx
    _ ≤ C₀ * (K * a) ^ 2 * (K ^ k * Q ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 hC₀) hP hP0 (mul_nonneg hC₀ (sq_nonneg _))
    _ = C₀ * K ^ (k + 2) * (a * Q) ^ 2 := by ring

theorem jointlySmoothOn_congr_Icc {a : ℕ} {T : ℝ} {A B : ℝ → SmoothCcTensor g 0 a}
    (hA : JointlySmoothOn g 0 a (Icc 0 T) A) (h : ∀ t ∈ Icc (0 : ℝ) T, B t = A t) :
    JointlySmoothOn g 0 a (Icc 0 T) B :=
  hA.congr fun q hq => by rw [h q.2 hq.2]

namespace EquationData

variable {s p : ℕ} (D : EquationData I M 0 s p) {T : ℝ} {N : ℕ}

/-! ### Pointwise bounds through the norm -/

theorem repJet_sub_eq (v : smoothSub g s p (N + 1) T) (w : ℝ → SmoothCcTensor g 0 s)
    (c : Fin (2 * p + 1)) (t : ℝ) :
    repJet v c t - jetFamily (p := p) w c t = iteratedCovGrad g 0 s c (rep v t - w t) := by
  rw [iteratedCovGrad_sub]
  rfl

/-- **The embedding, for elements of `smoothSub`.** -/
theorem exists_fiberNormSq_repJet_le (hT : 0 < T) (hp : 1 ≤ p)
    (hN : Module.finrank ℝ E / (2 * p) + 3 ≤ N) :
    ∃ Ce : ℝ, 0 ≤ Ce ∧
      (∀ (w : ℝ → SmoothCcTensor g 0 s) (hw : JointlySmoothOn g 0 s (Icc 0 T) w)
        (v : smoothSub g s p (N + 1) T) (c : Fin (2 * p + 1)), ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 0 (jetRanks s p c) x
          ((repJet v c t - jetFamily (p := p) w c t).toSection x) ≤
          Ce * ‖(v : ParabolicSpace g s p (N + 1) T) - ofSmooth w hw‖ ^ 2) ∧
      (∀ (v : smoothSub g s p (N + 1) T) (c : Fin (2 * p + 1)), ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 0 (jetRanks s p c) x
          ((repJet v c t).toSection x) ≤ Ce * ‖v‖ ^ 2) := by
  obtain ⟨Ce, hCe0, hCe⟩ := exists_fiberNormSq_jet_le (g := g) (s := s) hT hp hN
  refine ⟨Ce, hCe0, fun w hw v c t ht x => ?_, fun v c t ht x => ?_⟩
  · rw [repJet_sub_eq, norm_sub_sq_eq v hw]
    exact hCe _ (jointlySmoothOn_sub (rep_smooth v) hw) c t ht x
  · rw [norm_sq_eq_rep]
    exact hCe _ (rep_smooth v) c t ht x

theorem sum_repJet_le (hT : 0 < T) (v : smoothSub g s p (N + 1) T) :
    ∑ c : Fin (2 * p + 1), parabolicInner g (jetRanks s p c) p N T (repJet v c) (repJet v c) ≤
      (2 * p + 1 : ℕ) * ‖v‖ ^ 2 := by
  rw [norm_sq_eq_rep]
  exact sum_jetFamily_le hT (rep_smooth v) N

/-- Pointwise closeness of the jets to those of `w` gives jets in the domain. -/
theorem repInDom_of_tube {w : ℝ → SmoothCcTensor g 0 s} {δ : ℝ}
    (hδ : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ ζ : CovJetFiber I 0 s (2 * p) x,
      (∀ k : Fin (2 * p + 1), riemannianFiberNormSq (I := I) (M := M) g 0 (s + k) x
        (ζ k - covJet g 0 s (2 * p) (w t) x k) ≤ δ) → ζ ∈ D.dom t x)
    {v : smoothSub g s p (N + 1) T}
    (h : ∀ c : Fin (2 * p + 1), ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (jetRanks s p c) x
        ((repJet v c t - jetFamily (p := p) w c t).toSection x) ≤ δ) : D.RepInDom v := by
  intro t ht x
  refine hδ t ht x _ fun k => ?_
  have e : covJet g 0 s (2 * p) (rep v t) x k - covJet g 0 s (2 * p) (w t) x k =
      (repJet v k t - jetFamily (p := p) w k t).toSection x := (toSection_sub_apply _ _ x).symm
  rw [e]
  exact h k t ht x

/-! ### Bound (M) for `g_k` -/

theorem norm_gfun_sq (hTD : T ≤ D.T₀) (k : ℕ) {v : smoothSub g s p (N + 1) T}
    (hv : D.RepInDom v) (h : Fin k → smoothSub g s p (N + 1) T) :
    ‖D.gfun k v h‖ ^ 2 = parabolicInner g s p N T (D.gfam k v h) (D.gfam k v h) := by
  rw [D.gfun_eq hTD k hv, norm_ofSmooth_sq]

/-- **Bound (M)** for `g_k` near `w`. -/
theorem exists_gfun_bound (hT : 0 < T) (hTD : T ≤ D.T₀) (hp : 1 ≤ p)
    (hN : Module.finrank ℝ E / (2 * p) + 3 ≤ N) {w : ℝ → SmoothCcTensor g 0 s}
    (hw : JointlySmoothOn g 0 s (Icc 0 T) w)
    (hwdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (w t) x ∈ D.dom t x) (k : ℕ) :
    ∃ δ > 0, ∀ B : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ v : smoothSub g s p (N + 1) T,
      (∀ c : Fin (2 * p + 1), ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 0 (jetRanks s p c) x
          ((repJet v c t - jetFamily (p := p) w c t).toSection x) ≤ δ) →
      ‖v‖ ^ 2 ≤ B → D.RepInDom v →
      ∀ h : Fin k → smoothSub g s p (N + 1) T, ‖D.gfun k v h‖ ≤ C * ∏ l, ‖h l‖ := by
  obtain ⟨δ, hδ, hB⟩ := D.toFibreMap.exists_derivFam_bound k 0 hT hTD hp hN
    (w := jetFamily (p := p) w) (fun c => jointlySmoothOn_iteratedCovGrad hw c)
    (fun t ht x => hwdom t ht x)
  refine ⟨δ, hδ, fun B => ?_⟩
  obtain ⟨C₀, hC₀, hC⟩ := hB ((2 * p + 1 : ℕ) * B)
  refine ⟨Real.sqrt (C₀ * ((2 * p + 1 : ℕ) : ℝ) ^ k), Real.sqrt_nonneg _,
    fun v htube hvB hv h => ?_⟩
  have hK : (0 : ℝ) ≤ ((2 * p + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsum : ∑ c : Fin (2 * p + 1), parabolicInner g (jetRanks s p c) p N T (repJet v c)
      (repJet v c) ≤ (2 * p + 1 : ℕ) * B :=
    (sum_repJet_le hT v).trans (mul_le_mul_of_nonneg_left hvB hK)
  have h1 := hC (repJet v) (fun c => repJet_smooth v c) htube hsum (fun t ht x => hv t ht x)
    (fun l => repJet (h l)) (fun l c => repJet_smooth (h l) c)
  have h2 : ∏ l, ∑ c : Fin (2 * p + 1), parabolicInner g (jetRanks s p c) p N T
      (repJet (h l) c) (repJet (h l) c) ≤ ((2 * p + 1 : ℕ) : ℝ) ^ k * (∏ l, ‖h l‖) ^ 2 :=
    prod_bound_aux _ _ (fun l => Finset.sum_nonneg fun c _ => parabolicInner_self_nonneg _ _ _)
      fun l => sum_repJet_le hT (h l)
  refine le_sqrt_mul_of_sq (norm_nonneg _)
    (Finset.prod_nonneg fun l _ => norm_nonneg _) (mul_nonneg hC₀ (pow_nonneg hK k)) ?_
  rw [D.norm_gfun_sq hTD k hv]
  calc parabolicInner g s p N T (D.gfam k v h) (D.gfam k v h)
      ≤ C₀ * ∏ l, ∑ c : Fin (2 * p + 1), parabolicInner g (jetRanks s p c) p N T
          (repJet (h l) c) (repJet (h l) c) := h1
    _ ≤ C₀ * (((2 * p + 1 : ℕ) : ℝ) ^ k * (∏ l, ‖h l‖) ^ 2) :=
        mul_le_mul_of_nonneg_left h2 hC₀
    _ = C₀ * ((2 * p + 1 : ℕ) : ℝ) ^ k * (∏ l, ‖h l‖) ^ 2 := by ring

/-! ### Bound (T) for `g_k` -/

theorem gfam_add_eqOn (hT : 0 < T) (k : ℕ) (v h : smoothSub g s p (N + 1) T)
    (hs : Fin k → smoothSub g s p (N + 1) T) :
    ∀ t ∈ Icc (0 : ℝ) T, D.gfam k (v + h) hs t =
      D.toFibreMap.derivFam k 0 (fun c τ => repJet v c τ + repJet h c τ)
        (fun l => repJet (hs l)) t := by
  intro t ht
  refine FibreMap.apply_congr_time _ _ fun q => ?_
  rcases q with c | q
  · change iteratedCovGrad g 0 s c (rep (v + h) t) =
      iteratedCovGrad g 0 s c (rep v t) + iteratedCovGrad g 0 s c (rep h t)
    rw [rep_add hT (by omega) v h ht, iteratedCovGrad_add]
  · rfl

theorem gfam_cons (k : ℕ) (v h : smoothSub g s p (N + 1) T)
    (hs : Fin k → smoothSub g s p (N + 1) T) :
    D.gfam (k + 1) v (Fin.cons h hs) =
      D.toFibreMap.derivFam (k + 1) 0 (repJet v) (Fin.cons (repJet h) fun l => repJet (hs l)) := by
  rw [gfam, fun_fin_cons]

/-- **Bound (T)** for `g_k` near `w`. -/
theorem exists_gfun_taylor (hT : 0 < T) (hTD : T ≤ D.T₀) (hp : 1 ≤ p)
    (hN : Module.finrank ℝ E / (2 * p) + 3 ≤ N) {w : ℝ → SmoothCcTensor g 0 s}
    (hw : JointlySmoothOn g 0 s (Icc 0 T) w)
    (hwdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (w t) x ∈ D.dom t x) (k : ℕ) :
    ∃ δ > 0, ∀ B : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ v h : smoothSub g s p (N + 1) T,
      (∀ c : Fin (2 * p + 1), ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 0 (jetRanks s p c) x
          ((repJet v c t - jetFamily (p := p) w c t).toSection x) ≤ δ) →
      (∀ c : Fin (2 * p + 1), ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 0 (jetRanks s p c) x
          ((repJet h c t).toSection x) ≤ δ) →
      ‖v‖ ^ 2 + ‖h‖ ^ 2 ≤ B → (∀ τ ∈ Icc (0 : ℝ) 1, D.RepInDom (v + τ • h)) →
      ∀ hs : Fin k → smoothSub g s p (N + 1) T,
        ‖D.gfun k (v + h) hs - D.gfun k v hs - D.gfun (k + 1) v (Fin.cons h hs)‖ ≤
          C * (‖h‖ ^ 2 * ∏ l, ‖hs l‖) := by
  obtain ⟨δ, hδ, hB⟩ := D.toFibreMap.exists_taylor_bound k 0 hT hTD hp hN
    (w := jetFamily (p := p) w) (fun c => jointlySmoothOn_iteratedCovGrad hw c)
    (fun t ht x => hwdom t ht x)
  refine ⟨δ, hδ, fun B => ?_⟩
  obtain ⟨C₀, hC₀, hC⟩ := hB ((2 * p + 1 : ℕ) * B)
  refine ⟨Real.sqrt (C₀ * ((2 * p + 1 : ℕ) : ℝ) ^ (k + 2)), Real.sqrt_nonneg _,
    fun v h htube hhδ hvhB hseg hs => ?_⟩
  have hK : (0 : ℝ) ≤ ((2 * p + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hm : 1 ≤ N + 1 := by omega
  have hv : D.RepInDom v := by
    have := hseg 0 ⟨le_rfl, zero_le_one⟩
    rwa [zero_smul, add_zero] at this
  have hvh : D.RepInDom (v + h) := by
    have := hseg 1 ⟨zero_le_one, le_rfl⟩
    rwa [one_smul] at this
  have hsegF : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ τ ∈ Icc (0 : ℝ) 1,
      FibreMap.valAt (fun c => repJet v c t) x + τ • FibreMap.valAt (fun c => repJet h c t) x ∈
        D.toFibreMap.dom 0 t x := by
    intro t ht x τ hτ
    have h1 := hseg τ hτ t ht x
    have e : rep (v + τ • h) t = rep v t + τ • rep h t := by
      rw [rep_add hT hm v (τ • h) ht]
      dsimp only
      rw [rep_smul hT hm τ h ht]
    rw [e, covJet_add', covJet_smul'] at h1
    exact h1
  have hsum : ∑ c : Fin (2 * p + 1), parabolicInner g (jetRanks s p c) p N T (repJet v c)
        (repJet v c) + ∑ c : Fin (2 * p + 1), parabolicInner g (jetRanks s p c) p N T
        (repJet h c) (repJet h c) ≤ (2 * p + 1 : ℕ) * B := by
    have := add_le_add (sum_repJet_le hT v) (sum_repJet_le hT h)
    refine this.trans ?_
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left hvhB hK
  have h1 := hC (repJet v) (repJet h) (fun c => repJet_smooth v c) (fun c => repJet_smooth h c)
    htube (fun c t ht x => by simpa using hhδ c t ht x) hsum hsegF (fun l => repJet (hs l))
    (fun l c => repJet_smooth (hs l) c)
  -- the three families
  set A := D.toFibreMap.derivFam k 0 (fun c τ => repJet v c τ + repJet h c τ)
    (fun l => repJet (hs l)) with hA_def
  set Bf := D.toFibreMap.derivFam k 0 (repJet v) (fun l => repJet (hs l)) with hB_def
  set Cf := D.toFibreMap.derivFam (k + 1) 0 (repJet v)
    (Fin.cons (repJet h) fun l => repJet (hs l)) with hC_def
  have hAs : JointlySmoothOn g 0 s (Icc 0 T) A :=
    jointlySmoothOn_congr_Icc (D.gfam_spec hTD k hvh hs).2 fun t ht =>
      (D.gfam_add_eqOn hT k v h hs t ht).symm
  have hBs : JointlySmoothOn g 0 s (Icc 0 T) Bf := (D.gfam_spec hTD k hv hs).2
  have hCs : JointlySmoothOn g 0 s (Icc 0 T) Cf := by
    have := (D.gfam_spec hTD (k + 1) hv (Fin.cons h hs)).2
    rwa [gfam_cons] at this
  have hR := jointlySmoothOn_sub (jointlySmoothOn_sub hAs hBs) hCs
  have heq : D.gfun k (v + h) hs - D.gfun k v hs - D.gfun (k + 1) v (Fin.cons h hs) =
      ofSmooth (p := p) (m := N) (fun t => A t - Bf t - Cf t) hR := by
    rw [ofSmooth_sub (jointlySmoothOn_sub hAs hBs) hCs, ofSmooth_sub hAs hBs,
      D.gfun_eq hTD k hvh, D.gfun_eq hTD k hv, D.gfun_eq hTD (k + 1) hv]
    congr 1
    · congr 1
      exact ofSmooth_congr hT _ _ (D.gfam_add_eqOn hT k v h hs)
  rw [heq]
  have hP := prod_bound_aux _ (fun l => ‖hs l‖)
    (fun l => Finset.sum_nonneg fun c _ => parabolicInner_self_nonneg (g := g) (T := T) p N
      (repJet (hs l) c)) fun l => sum_repJet_le hT (hs l)
  refine le_sqrt_mul_of_sq (norm_nonneg _)
    (mul_nonneg (sq_nonneg _) (Finset.prod_nonneg fun l _ => norm_nonneg _))
    (mul_nonneg hC₀ (pow_nonneg hK _)) ?_
  rw [norm_ofSmooth_sq]
  exact taylor_arith k hC₀ (Finset.sum_nonneg fun c _ => parabolicInner_self_nonneg _ _ _)
    (Finset.prod_nonneg fun l _ => Finset.sum_nonneg fun c _ => parabolicInner_self_nonneg _ _ _)
    h1 (sum_repJet_le hT h) hP

/-! ### The main theorem -/

/-- `cor:N` at the level `𝒫^{N+1} → 𝒫^N`. -/
theorem exists_nonlinOp_aux (hp : 1 ≤ p) (hT : 0 < T) (hTD : T ≤ D.T₀)
    (hN : Module.finrank ℝ E / (2 * p) + 3 ≤ N) {w : ℝ → SmoothCcTensor g 0 s}
    (hw : JointlySmoothOn g 0 s (Icc 0 T) w)
    (hwdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (w t) x ∈ D.dom t x) :
    ∃ δ > 0, ∃ 𝒩 : ParabolicSpace g s p (N + 1) T → ParabolicSpace g s p N T,
      ContDiffAt ℝ ∞ 𝒩 (ofSmooth w hw) ∧
      (∀ u (hu : JointlySmoothOn g 0 s (Icc 0 T) u),
        dist (ofSmooth (p := p) (m := N + 1) u hu) (ofSmooth w hw) < δ →
        (∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (u t) x ∈ D.dom t x) ∧
        ∃ hF, 𝒩 (ofSmooth u hu) = ofSmooth (D.nonlinFamily u) hF) ∧
      ∃ L : LinearOp g s p T, (∀ k t, t ∈ Icc (0 : ℝ) T → ∀ x,
          opFieldHom ((L.coeff k t).toSection x) =
            D.partialDeriv k t x (covJet g 0 s (2 * p) (w t) x)) ∧
        ∀ h (hh : JointlySmoothOn g 0 s (Icc 0 T) h), ∃ hL,
          fderiv ℝ 𝒩 (ofSmooth w hw) (ofSmooth h hh) =
            ofSmooth (fun t => L.apply t (h t)) hL := by
  have hm : 1 ≤ N + 1 := by omega
  obtain ⟨Ce, hCe0, hCe, hCe'⟩ := exists_fiberNormSq_repJet_le (g := g) (s := s) hT hp hN
  obtain ⟨δ₁, hδ₁, hδ₁dom⟩ := D.exists_dom_tube hTD hw hwdom
  choose δM hδM CM hCM0 hCM using fun k => D.exists_gfun_bound hT hTD hp hN hw hwdom k
  choose δT hδT CT hCT0 hCT using fun k => D.exists_gfun_taylor hT hTD hp hN hw hwdom k
  set w₀ : smoothSub g s p (N + 1) T := smoothElt w hw with hw₀
  have hw₀coe : ((w₀ : smoothSub g s p (N + 1) T) : ParabolicSpace g s p (N + 1) T) =
      ofSmooth w hw := rfl
  have htube : ∀ v : smoothSub g s p (N + 1) T, ∀ r : ℝ, dist v w₀ < r →
      ∀ c : Fin (2 * p + 1), ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 0 (jetRanks s p c) x
          ((repJet v c t - jetFamily (p := p) w c t).toSection x) ≤ Ce * (2 * r) ^ 2 := by
    intro v r hv c t ht x
    refine (hCe w hw v c t ht x).trans
      (mul_le_mul_of_nonneg_left (sq_le_two_mul_sq (norm_nonneg _) ?_) hCe0)
    rw [← dist_eq_norm, ← hw₀coe]
    exact hv
  have hdomv : ∀ v : smoothSub g s p (N + 1) T, ∀ r : ℝ, dist v w₀ < r →
      Ce * (2 * r) ^ 2 ≤ δ₁ → D.RepInDom v := fun v r hv hr =>
    D.repInDom_of_tube hδ₁dom fun c t ht x => (htube v r hv c t ht x).trans hr
  have hb : ∀ n : ℕ, ∃ δ > 0, ∃ C : ℕ → ℝ,
      (∀ k ≤ n + 1, ∀ u ∈ ball w₀ δ, ‖D.gCML hT hTD k u‖ ≤ C k) ∧
      (∀ k ≤ n, ∀ u ∈ ball w₀ δ, ∀ h, u + h ∈ ball w₀ δ →
        ‖D.gCML hT hTD k (u + h) - D.gCML hT hTD k u - (D.gCML hT hTD (k + 1) u).curryLeft h‖ ≤
          C k * ‖h‖ ^ 2) := by
    intro n
    obtain ⟨δs, hδs, hδsle⟩ := exists_pos_le_fin (fun k => min δ₁ (min (δM k) (δT k)))
      (fun k => lt_min hδ₁ (lt_min (hδM k) (hδT k))) (n + 1)
    obtain ⟨r, hr, hrδ⟩ := exists_radius hCe0 hδs
    obtain ⟨B, hB⟩ : ∃ B : ℝ, B = (‖w₀‖ + r) ^ 2 + (2 * r) ^ 2 := ⟨_, rfl⟩
    have hle1 : Ce * (2 * r) ^ 2 ≤ δ₁ :=
      hrδ.trans ((hδsle 0 (Nat.zero_le _)).trans (min_le_left _ _))
    have hleM : ∀ k ≤ n + 1, Ce * (2 * r) ^ 2 ≤ δM k := fun k hk =>
      hrδ.trans ((hδsle k hk).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hleT : ∀ k ≤ n + 1, Ce * (2 * r) ^ 2 ≤ δT k := fun k hk =>
      hrδ.trans ((hδsle k hk).trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hdomb : ∀ u ∈ ball w₀ r, D.RepInDom u := fun u hu => hdomv u r hu hle1
    have hnorm : ∀ u ∈ ball w₀ r, ‖u‖ ≤ ‖w₀‖ + r := fun u hu => by
      have h1 := norm_sub_norm_le u w₀
      have h2 : ‖u - w₀‖ < r := by rw [← dist_eq_norm]; exact hu
      linarith
    have hnormB : ∀ u ∈ ball w₀ r, ‖u‖ ^ 2 ≤ B := fun u hu => by
      rw [hB]
      exact (pow_le_pow_left₀ (norm_nonneg _) (hnorm u hu) 2).trans
        (le_add_of_nonneg_right (sq_nonneg _))
    have hbound : ∀ k ≤ n + 1, ∀ u ∈ ball w₀ r, ∀ h : Fin k → smoothSub g s p (N + 1) T,
        ‖D.gfun k u h‖ ≤ CM k B * ∏ l, ‖h l‖ := fun k hk u hu h =>
      hCM k B u (fun c t ht x => (htube u r hu c t ht x).trans (hleM k hk)) (hnormB u hu)
        (hdomb u hu) h
    have happly : ∀ k ≤ n + 1, ∀ u ∈ ball w₀ r, ∀ h : Fin k → smoothSub g s p (N + 1) T,
        D.gCML hT hTD k u h = D.gfun k u h :=
      fun k hk u hu h => D.gCML_apply hT hTD k (hdomb u hu) ⟨_, hbound k hk u hu⟩ h
    refine ⟨r, hr, fun k => max (CM k B) (CT k B), fun k hk u hu => ?_,
      fun k hk u hu h huh => ?_⟩
    · refine (ContinuousMultilinearMap.opNorm_le_bound (hCM0 k B) fun h => ?_).trans
        (le_max_left _ _)
      rw [happly k hk u hu]
      exact hbound k hk u hu h
    · have hh : ‖h‖ < 2 * r := by
        have h1 : ‖h‖ = dist (u + h) u := by rw [dist_eq_norm, add_sub_cancel_left]
        have h2 := dist_triangle_right (u + h) u w₀
        rw [mem_ball] at hu huh
        linarith
      have hseg : ∀ τ ∈ Icc (0 : ℝ) 1, D.RepInDom (u + τ • h) := by
        intro τ hτ
        have hmem : u + τ • h ∈ ball w₀ r := by
          have := (convex_ball w₀ r).add_smul_sub_mem hu huh hτ
          rwa [add_sub_cancel_left] at this
        exact hdomb _ hmem
      have hBh : ‖u‖ ^ 2 + ‖h‖ ^ 2 ≤ B := by
        rw [hB]
        exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) (hnorm u hu) 2)
          (pow_le_pow_left₀ (norm_nonneg _) hh.le 2)
      have hhpt : ∀ c : Fin (2 * p + 1), ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 0 (jetRanks s p c) x
            ((repJet h c t).toSection x) ≤ δT k := fun c t ht x =>
        (hCe' h c t ht x).trans ((mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) hh.le 2) hCe0).trans (hleT k (by omega)))
      refine (ContinuousMultilinearMap.opNorm_le_bound
        (mul_nonneg (hCT0 k B) (sq_nonneg _)) fun hs => ?_).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))
      rw [sub_apply, sub_apply,
        ContinuousMultilinearMap.curryLeft_apply, happly k (by omega) (u + h) huh,
        happly k (by omega) u hu, happly (k + 1) (by omega) u hu, mul_assoc]
      exact hCT k B u h (fun c t ht x => (htube u r hu c t ht x).trans (hleT k (by omega)))
        hhpt hBh hseg hs
  obtain ⟨δ₀, hδ₀, 𝒩, h𝒩, -, h𝒩e, h𝒩d⟩ := SmoothExtension.exists_contDiffAt_extension
    (smoothSub g s p (N + 1) T).subtypeL (fun v => norm_subtypeL v) denseRange_smoothSub w₀
    (fun k => D.gCML hT hTD k) hb
  obtain ⟨rD, hrD, hrDδ⟩ := exists_radius hCe0 hδ₁
  refine ⟨min δ₀ rD, lt_min hδ₀ hrD, 𝒩, h𝒩, fun u hu hdist => ?_, ?_⟩
  · set u₀ : smoothSub g s p (N + 1) T := smoothElt u hu with hu₀def
    have hu₀ : dist u₀ w₀ < min δ₀ rD := hdist
    have hdom₀ : D.RepInDom u₀ := hdomv u₀ rD (lt_of_lt_of_le hu₀ (min_le_right _ _)) hrDδ
    have hrep : ∀ t ∈ Icc (0 : ℝ) T, rep u₀ t = u t := fun t ht => rep_smoothElt hT hm u hu ht
    have hdomu : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (u t) x ∈ D.dom t x :=
      fun t ht x => by
        rw [← hrep t ht]
        exact hdom₀ t ht x
    obtain ⟨hF1, hF2⟩ := D.nonlinFamily_spec hTD hu hdomu
    refine ⟨hdomu, hF2, ?_⟩
    have e1 : 𝒩 (ofSmooth u hu) = D.gCML hT hTD 0 u₀ 0 :=
      h𝒩e u₀ (lt_of_lt_of_le hu₀ (min_le_left _ _))
    have hb0 : ∃ C, ∀ h : Fin 0 → smoothSub g s p (N + 1) T,
        ‖D.gfun 0 u₀ h‖ ≤ C * ∏ l, ‖h l‖ :=
      ⟨‖D.gfun 0 u₀ 0‖, fun h => by rw [Subsingleton.elim h 0]; simp⟩
    rw [e1, D.gCML_apply hT hTD 0 hdom₀ hb0, D.gfun_eq hTD 0 hdom₀]
    refine ofSmooth_congr hT _ _ fun t ht => smoothCcTensor_eq_of_toSection fun x => ?_
    rw [(D.gfam_spec hTD 0 hdom₀ 0).1 t ht x, FibreMap.derivF_zero_eq, fbase_joinPt,
      toFibreMap_F, hF1 t ht x, hrep t ht]
  · obtain ⟨L, hL⟩ := D.exists_linOp hT hTD hw hwdom
    refine ⟨L, fun k t ht x => hL k t ht x, fun h hh => ⟨L.jointlySmoothOn_apply hh, ?_⟩⟩
    set h₀ : smoothSub g s p (N + 1) T := smoothElt h hh with hh₀def
    have hrepw : ∀ t ∈ Icc (0 : ℝ) T, rep w₀ t = w t := fun t ht => rep_smoothElt hT hm w hw ht
    have hreph : ∀ t ∈ Icc (0 : ℝ) T, rep h₀ t = h t := fun t ht => rep_smoothElt hT hm h hh ht
    have hdomw : D.RepInDom w₀ := hdomv w₀ rD (by rw [dist_self]; exact hrD) hrDδ
    have e1 : fderiv ℝ 𝒩 (ofSmooth w hw) (ofSmooth h hh) =
        D.gCML hT hTD 1 w₀ (fun _ => h₀) := h𝒩d h₀
    have hw0t : ∀ c : Fin (2 * p + 1), ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 0 (jetRanks s p c) x
          ((repJet w₀ c t - jetFamily (p := p) w c t).toSection x) ≤ δM 1 := by
      intro c t ht x
      have h1 := hCe w hw w₀ c t ht x
      rw [hw₀coe, sub_self, norm_zero] at h1
      have h2 : Ce * (0 : ℝ) ^ 2 = 0 := by ring
      rw [h2] at h1
      exact h1.trans (hδM 1).le
    have hb1 : ∃ C, ∀ hs : Fin 1 → smoothSub g s p (N + 1) T,
        ‖D.gfun 1 w₀ hs‖ ≤ C * ∏ l, ‖hs l‖ :=
      ⟨CM 1 (‖w₀‖ ^ 2), hCM 1 _ w₀ hw0t le_rfl hdomw⟩
    rw [e1, D.gCML_apply hT hTD 1 hdomw hb1, D.gfun_eq hTD 1 hdomw]
    refine ofSmooth_congr hT _ _ fun t ht => smoothCcTensor_eq_of_toSection fun x => ?_
    rw [(D.gfam_spec hTD 1 hdomw _).1 t ht x]
    rw [hrepw t ht, hreph t ht, D.derivF_one_jet, LinearOp.apply, toSection_finset_sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [operatorFieldApply_toSection_eq, hL k t ht x]
    rfl

/-- **The nonlinear operator on the parabolic spaces** (`cor:N`). Let `w` be a jointly smooth
family on `[0,T]` with `2p`-jets in the domain, and `m ≥ ⌊n/2p⌋ + 4`. There are `δ > 0` and
`𝒩 : 𝒫^m → 𝒫^{m-1}` such that

* `𝒩` is `C^∞` at `w`;
* every smooth family `u` within `δ` of `w` in `𝒫^m` has jets in the domain, and `𝒩 u = F[u]`;
* the derivative of `𝒩` at `w` is the linearization `L_w`, whose coefficients are
  `D_k F(t, j^{2p} w)`: `D𝒩(w) h = L_w h` for smooth `h`.

`D𝒩(w)` is determined on all of `𝒫^m` by its values on the dense smooth families. -/
theorem exists_nonlinOp (hp : 1 ≤ p) (hT : 0 < T) (hTD : T ≤ D.T₀) {m : ℕ}
    (hm : Module.finrank ℝ E / (2 * p) + 4 ≤ m) {w : ℝ → SmoothCcTensor g 0 s}
    (hw : JointlySmoothOn g 0 s (Icc 0 T) w)
    (hwdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (w t) x ∈ D.dom t x) :
    ∃ δ > 0, ∃ 𝒩 : ParabolicSpace g s p m T → ParabolicSpace g s p (m - 1) T,
      ContDiffAt ℝ ∞ 𝒩 (ofSmooth w hw) ∧
      (∀ u (hu : JointlySmoothOn g 0 s (Icc 0 T) u),
        dist (ofSmooth (p := p) (m := m) u hu) (ofSmooth w hw) < δ →
        (∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (u t) x ∈ D.dom t x) ∧
        ∃ hF, 𝒩 (ofSmooth u hu) = ofSmooth (D.nonlinFamily u) hF) ∧
      ∃ L : LinearOp g s p T, (∀ k t, t ∈ Icc (0 : ℝ) T → ∀ x,
          opFieldHom ((L.coeff k t).toSection x) =
            D.partialDeriv k t x (covJet g 0 s (2 * p) (w t) x)) ∧
        ∀ h (hh : JointlySmoothOn g 0 s (Icc 0 T) h), ∃ hL,
          fderiv ℝ 𝒩 (ofSmooth w hw) (ofSmooth h hh) =
            ofSmooth (fun t => L.apply t (h t)) hL := by
  have h4 : 4 ≤ m := le_trans (Nat.le_add_left 4 _) hm
  obtain ⟨N, rfl⟩ : ∃ N, m = N + 1 := ⟨m - 1, by omega⟩
  have hN : Module.finrank ℝ E / (2 * p) + 3 ≤ N := by omega
  exact D.exists_nonlinOp_aux hp hT hTD hN hw hwdom

end EquationData

end ShortTime
