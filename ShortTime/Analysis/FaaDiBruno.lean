import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Data.Finset.Sort

/-!
# A tame weighted Faà di Bruno bound

The Euclidean core of the composition estimate `prop:nemytskii`.

* `blockDeriv f s z v B`: `D^{|B|} f(z)` applied to the directions `v i`, `i ∈ B`, in increasing
  order.
* `iteratedFDerivWithin_comp_apply_eq_sum`: the Faà di Bruno formula, evaluated on directions.
* `prod_le_pow_mul_of_atMostOneLarge`: a product of nonnegative factors, all but at most one of
  which are `≤ R`, is `≤ R ^ card * max`.
* `exists_tame_bound_comp`: the tame bound for `g ∘ f`, `g` fixed and `f` varying.
* `exists_tame_bound_graph`: the tame bound for `z ↦ Φ (z, u z)`, `Φ` fixed and `u` varying.

Weights `wt : Fin n → ℕ` are attached to the directions. A block `B` is *small* if
`2 * wt(B) ≤ wt(univ)`. In a partition of `Fin n`, at most one block is not small, so a bound `R`
on the small blocks makes the estimate linear in the derivatives of `u`.
-/

noncomputable section

open Set Function

namespace ShortTime.FaaDiBruno

variable {X Y G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-! ### Products with at most one large factor -/

/-- A product of nonnegative factors, each `≤ T`, of which any two distinct ones include one
`≤ R`, is at most `R ^ card * T` (for `R, T ≥ 1`). -/
theorem prod_le_pow_mul_of_atMostOneLarge {ι : Type*} [Fintype ι] [DecidableEq ι] {a : ι → ℝ}
    {R T : ℝ} (ha : ∀ i, 0 ≤ a i) (hR : 1 ≤ R) (hT : 1 ≤ T) (haT : ∀ i, a i ≤ T)
    (hpair : ∀ i j, i ≠ j → a i ≤ R ∨ a j ≤ R) :
    ∏ i, a i ≤ R ^ Fintype.card ι * T := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  by_cases h : ∃ i₀, R < a i₀
  · obtain ⟨i₀, hi₀⟩ := h
    have hrest : ∀ i ∈ Finset.univ.erase i₀, a i ≤ R := by
      intro i hi
      rcases hpair i i₀ (Finset.ne_of_mem_erase hi) with h | h
      · exact h
      · exact absurd h (not_le.2 hi₀)
    rw [← Finset.mul_prod_erase Finset.univ a (Finset.mem_univ i₀)]
    have h1 : ∏ i ∈ Finset.univ.erase i₀, a i ≤ ∏ _i ∈ Finset.univ.erase i₀, R :=
      Finset.prod_le_prod (fun i _ => ha i) hrest
    rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at h1
    calc a i₀ * ∏ i ∈ Finset.univ.erase i₀, a i
        ≤ T * R ^ (Fintype.card ι - 1) :=
          mul_le_mul (haT i₀) h1 (Finset.prod_nonneg fun i _ => ha i) hT0
      _ ≤ T * R ^ Fintype.card ι :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR (Nat.sub_le _ _)) hT0
      _ = R ^ Fintype.card ι * T := mul_comm _ _
  · simp only [not_exists, not_lt] at h
    calc ∏ i, a i ≤ ∏ _i : ι, R := Finset.prod_le_prod (fun i _ => ha i) (fun i _ => h i)
      _ = R ^ Fintype.card ι := by rw [Finset.prod_const, Finset.card_univ]
      _ ≤ R ^ Fintype.card ι * T := le_mul_of_one_le_right (pow_nonneg hR0 _) hT

/-! ### Blocks of directions -/

/-- `D^{|B|} f(z)` (within `s`) applied to the directions `v i`, `i ∈ B`, in increasing order
of `i`. -/
def blockDeriv {n : ℕ} (f : X → Y) (s : Set X) (z : X) (v : Fin n → X) (B : Finset (Fin n)) : Y :=
  iteratedFDerivWithin ℝ B.card f s z (fun j => v (B.orderEmbOfFin rfl j))

/-- Feeding the directions along a strictly increasing map `e` is `blockDeriv` of the image
of `e`. -/
theorem iteratedFDerivWithin_comp_strictMono_eq_blockDeriv {n k : ℕ} (f : X → Y) (s : Set X)
    (z : X) (v : Fin n → X) (e : Fin k → Fin n) (he : StrictMono e) :
    iteratedFDerivWithin ℝ k f s z (v ∘ e) = blockDeriv f s z v (Finset.univ.image e) := by
  have key : ∀ (B : Finset (Fin n)) (k : ℕ) (e : Fin k → Fin n), B.card = k → StrictMono e →
      (∀ j, e j ∈ B) → iteratedFDerivWithin ℝ k f s z (v ∘ e) = blockDeriv f s z v B := by
    rintro B k e rfl he hmem
    have := Finset.orderEmbOfFin_unique rfl hmem he
    subst this
    rfl
  exact key _ k e
    (by rw [Finset.card_image_of_injective _ he.injective, Finset.card_univ, Fintype.card_fin])
    he (fun j => Finset.mem_image_of_mem e (Finset.mem_univ j))

/-- Of two distinct blocks of an ordered partition, one is small for any weights. -/
theorem small_or_small {n : ℕ} (c : OrderedFinpartition n) (wt : Fin n → ℕ) {i j : Fin c.length}
    (hij : i ≠ j) :
    2 * ∑ x ∈ Finset.univ.image (c.emb i), wt x ≤ ∑ x, wt x ∨
      2 * ∑ x ∈ Finset.univ.image (c.emb j), wt x ≤ ∑ x, wt x := by
  have hdisj : Disjoint (Finset.univ.image (c.emb i)) (Finset.univ.image (c.emb j)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨b, -, hb⟩ := Finset.mem_image.1 hx'
    exact c.emb_ne_emb_of_ne hij hb.symm
  have h := Finset.sum_le_sum_of_subset (f := wt)
    (Finset.subset_univ (Finset.univ.image (c.emb i) ∪ Finset.univ.image (c.emb j)))
  rw [Finset.sum_union hdisj] at h
  omega

/-! ### The Faà di Bruno formula -/

/-- The Faà di Bruno formula, evaluated on directions `v`. -/
theorem iteratedFDerivWithin_comp_apply_eq_sum {g : Y → G} {f : X → Y} {s : Set X} {t : Set Y}
    {n : ℕ} (hg : ContDiffOn ℝ n g t) (hf : ContDiffOn ℝ n f s) (ht : UniqueDiffOn ℝ t)
    (hs : UniqueDiffOn ℝ s) (hst : MapsTo f s t) {z : X} (hz : z ∈ s) (v : Fin n → X) :
    iteratedFDerivWithin ℝ n (g ∘ f) s z v =
      ∑ c : OrderedFinpartition n, iteratedFDerivWithin ℝ c.length g t (f z)
        (fun i => iteratedFDerivWithin ℝ (c.partSize i) f s z (v ∘ c.emb i)) := by
  have H := (hg.ftaylorSeriesWithin ht).comp (hf.ftaylorSeriesWithin hs) hst
  rw [← H.eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl hs hz]
  simp only [FormalMultilinearSeries.taylorComp, sum_apply,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply]
  rfl

/-! ### The tame bound -/

/-- The product of the block factors is bounded by `(1 + R)^n (1 + ∑_B ‖blockDeriv f B‖)` when
the small blocks are bounded by `R`. -/
theorem prod_norm_blocks_le {n : ℕ} (c : OrderedFinpartition n) (f : X → Y) (s : Set X) (z : X)
    (v : Fin n → X) (wt : Fin n → ℕ) {R : ℝ} (hR : 0 ≤ R)
    (hsmall : ∀ B : Finset (Fin n), B.Nonempty → 2 * ∑ i ∈ B, wt i ≤ ∑ i, wt i →
      ‖blockDeriv f s z v B‖ ≤ R) :
    ∏ i, ‖iteratedFDerivWithin ℝ (c.partSize i) f s z (v ∘ c.emb i)‖ ≤
      (1 + R) ^ n * (1 + ∑ B ∈ Finset.univ.filter (fun B : Finset (Fin n) => B.Nonempty),
        ‖blockDeriv f s z v B‖) := by
  set S := ∑ B ∈ Finset.univ.filter (fun B : Finset (Fin n) => B.Nonempty),
    ‖blockDeriv f s z v B‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hB : ∀ i, iteratedFDerivWithin ℝ (c.partSize i) f s z (v ∘ c.emb i) =
      blockDeriv f s z v (Finset.univ.image (c.emb i)) := fun i =>
    iteratedFDerivWithin_comp_strictMono_eq_blockDeriv f s z v (c.emb i) (c.emb_strictMono i)
  have hne : ∀ i, (Finset.univ.image (c.emb i)).Nonempty := fun i =>
    ⟨c.emb i ⟨0, c.partSize_pos i⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have hle : ∀ i, ‖iteratedFDerivWithin ℝ (c.partSize i) f s z (v ∘ c.emb i)‖ ≤ 1 + S := by
    intro i
    rw [hB i]
    have : ‖blockDeriv f s z v (Finset.univ.image (c.emb i))‖ ≤ S :=
      Finset.single_le_sum (f := fun B => ‖blockDeriv f s z v B‖) (fun B _ => norm_nonneg _)
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, hne i⟩)
    linarith
  have hpair : ∀ i j, i ≠ j →
      ‖iteratedFDerivWithin ℝ (c.partSize i) f s z (v ∘ c.emb i)‖ ≤ 1 + R ∨
        ‖iteratedFDerivWithin ℝ (c.partSize j) f s z (v ∘ c.emb j)‖ ≤ 1 + R := by
    intro i j hij
    rcases small_or_small c wt hij with h | h
    · left
      rw [hB i]
      linarith [hsmall _ (hne i) h]
    · right
      rw [hB j]
      linarith [hsmall _ (hne j) h]
  calc ∏ i, ‖iteratedFDerivWithin ℝ (c.partSize i) f s z (v ∘ c.emb i)‖
      ≤ (1 + R) ^ Fintype.card (Fin c.length) * (1 + S) :=
        prod_le_pow_mul_of_atMostOneLarge (fun i => norm_nonneg _) (by linarith) (by linarith)
          hle hpair
    _ ≤ (1 + R) ^ n * (1 + S) := by
        rw [Fintype.card_fin]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) c.length_le)
          (by linarith)

/-- **Tame Faà di Bruno bound** for `g ∘ f`, with `g` fixed and `f` varying. For every `R ≥ 0`
there is `C` such that, whenever `f z ∈ K` and the small blocks of directions satisfy
`‖D^{|B|} f(z) v_B‖ ≤ R`, the iterated derivative `D^n (g ∘ f)(z) v` is bounded by
`C (1 + ∑_{B ≠ ∅} ‖D^{|B|} f(z) v_B‖)`. -/
theorem exists_tame_bound_comp {g : Y → G} {t K : Set Y} {n : ℕ} (hg : ContDiffOn ℝ n g t)
    (ht : UniqueDiffOn ℝ t) (hK : IsCompact K) (hKt : K ⊆ t) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C, 0 ≤ C ∧ ∀ (f : X → Y) (s : Set X), UniqueDiffOn ℝ s → ContDiffOn ℝ n f s →
      MapsTo f s t → ∀ z ∈ s, f z ∈ K → ∀ (v : Fin n → X) (wt : Fin n → ℕ),
      (∀ B : Finset (Fin n), B.Nonempty → 2 * ∑ i ∈ B, wt i ≤ ∑ i, wt i →
        ‖blockDeriv f s z v B‖ ≤ R) →
      ‖iteratedFDerivWithin ℝ n (g ∘ f) s z v‖ ≤
        C * (1 + ∑ B ∈ Finset.univ.filter (fun B : Finset (Fin n) => B.Nonempty),
          ‖blockDeriv f s z v B‖) := by
  have hb : ∀ k : Fin (n + 1), ∃ M, ∀ y ∈ K, ‖iteratedFDerivWithin ℝ k g t y‖ ≤ M := fun k =>
    hK.exists_bound_of_continuousOn
      ((hg.continuousOn_iteratedFDerivWithin (by exact_mod_cast k.is_le) ht).mono hKt)
  choose M hM using hb
  set M₀ := ∑ k, max (M k) 0 with hM₀def
  have hM₀0 : 0 ≤ M₀ := Finset.sum_nonneg fun k _ => le_max_right _ _
  have hM₀ : ∀ k, k ≤ n → ∀ y ∈ K, ‖iteratedFDerivWithin ℝ k g t y‖ ≤ M₀ := by
    intro k hk y hy
    calc ‖iteratedFDerivWithin ℝ k g t y‖ ≤ M ⟨k, Nat.lt_succ_of_le hk⟩ := hM ⟨k, Nat.lt_succ_of_le hk⟩ y hy
      _ ≤ max (M ⟨k, Nat.lt_succ_of_le hk⟩) 0 := le_max_left _ _
      _ ≤ M₀ := Finset.single_le_sum (f := fun k => max (M k) 0)
          (fun k _ => le_max_right _ _) (Finset.mem_univ _)
  refine ⟨Fintype.card (OrderedFinpartition n) * (M₀ * (1 + R) ^ n), by positivity, ?_⟩
  intro f s hs hf hst z hz hfz v wt hsmall
  set S := ∑ B ∈ Finset.univ.filter (fun B : Finset (Fin n) => B.Nonempty),
    ‖blockDeriv f s z v B‖ with hS
  have hterm : ∀ c : OrderedFinpartition n,
      ‖iteratedFDerivWithin ℝ c.length g t (f z)
        (fun i => iteratedFDerivWithin ℝ (c.partSize i) f s z (v ∘ c.emb i))‖ ≤
        M₀ * ((1 + R) ^ n * (1 + S)) := by
    intro c
    refine ((iteratedFDerivWithin ℝ c.length g t (f z)).le_opNorm _).trans ?_
    exact mul_le_mul (hM₀ _ c.length_le _ hfz) (prod_norm_blocks_le c f s z v wt hR hsmall)
      (Finset.prod_nonneg fun _ _ => norm_nonneg _) hM₀0
  rw [iteratedFDerivWithin_comp_apply_eq_sum hg hf ht hs hst hz]
  calc ‖∑ c : OrderedFinpartition n, iteratedFDerivWithin ℝ c.length g t (f z)
        (fun i => iteratedFDerivWithin ℝ (c.partSize i) f s z (v ∘ c.emb i))‖
      ≤ ∑ c : OrderedFinpartition n, ‖iteratedFDerivWithin ℝ c.length g t (f z)
        (fun i => iteratedFDerivWithin ℝ (c.partSize i) f s z (v ∘ c.emb i))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _c : OrderedFinpartition n, M₀ * ((1 + R) ^ n * (1 + S)) :=
        Finset.sum_le_sum fun c _ => hterm c
    _ = Fintype.card (OrderedFinpartition n) * (M₀ * (1 + R) ^ n) * (1 + S) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-! ### The graph map `z ↦ (z, u z)` -/

/-- `‖D^k id(z) w‖ ≤ 1` for `k ≥ 1` and unit directions. -/
theorem norm_iteratedFDerivWithin_id_apply_le {s : Set X} {z : X} (hs : UniqueDiffOn ℝ s)
    (hz : z ∈ s) {k : ℕ} (hk : 1 ≤ k) (w : Fin k → X) (hw : ∀ j, ‖w j‖ ≤ 1) :
    ‖iteratedFDerivWithin ℝ k (fun x : X => x) s z w‖ ≤ 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [iteratedFDerivWithin_succ_apply_right hs hz]
  have heq : EqOn (fun y => fderivWithin ℝ (fun x : X => x) s y)
      (fun _ => ContinuousLinearMap.id ℝ X) s := fun y hy => fderivWithin_id (hs y hy)
  rw [iteratedFDerivWithin_congr heq hz]
  rcases m with _ | m
  · simpa [iteratedFDerivWithin_zero_apply] using hw _
  · rw [iteratedFDerivWithin_const_of_ne (by omega)]
    simp

/-- `‖D^k (z ↦ (z, u z))(z) w‖ ≤ 1 + ‖D^k u(z) w‖` for `k ≥ 1` and unit directions. -/
theorem norm_iteratedFDerivWithin_graph_apply_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {u : X → F} {s : Set X} {z : X} {k : ℕ} (hk : 1 ≤ k)
    (hu : ContDiffOn ℝ k u s) (hs : UniqueDiffOn ℝ s) (hz : z ∈ s) (w : Fin k → X)
    (hw : ∀ j, ‖w j‖ ≤ 1) :
    ‖iteratedFDerivWithin ℝ k (fun x => (x, u x)) s z w‖ ≤
      1 + ‖iteratedFDerivWithin ℝ k u s z w‖ := by
  rw [iteratedFDerivWithin_prodMk (f := fun x : X => x) contDiffWithinAt_id (hu z hz) hs hz
    le_rfl, ContinuousMultilinearMap.prod_apply, norm_prod_le_iff]
  refine ⟨?_, ?_⟩
  · have := norm_iteratedFDerivWithin_id_apply_le hs hz hk w hw
    have := norm_nonneg (iteratedFDerivWithin ℝ k u s z w)
    simp only
    linarith
  · simp only
    linarith [zero_le_one (α := ℝ)]

theorem graph_arith {C N S T : ℝ} (hC : 0 ≤ C) (hN : 0 ≤ N) (hS : 0 ≤ S) (hT : T ≤ N + S) :
    C * (1 + T) ≤ C * (1 + N) * (1 + S) := by
  have : 1 + T ≤ (1 + N) * (1 + S) := by nlinarith
  calc C * (1 + T) ≤ C * ((1 + N) * (1 + S)) := mul_le_mul_of_nonneg_left this hC
    _ = C * (1 + N) * (1 + S) := by ring

/-- **Tame Faà di Bruno bound** for `z ↦ Φ (z, u z)`, with `Φ` fixed and `u` varying. For every
`R ≥ 0` there is `C` (depending on `Φ, K, n, R` only) such that: if `(z, u z) ∈ K`, the directions
`v i` have norm `≤ 1`, and every small block of directions (`2 wt(B) ≤ wt(univ)`) satisfies
`‖D^{|B|} u(z) v_B‖ ≤ R`, then
`‖D^n (Φ ∘ (id, u))(z) v‖ ≤ C (1 + ∑_{B ≠ ∅} ‖D^{|B|} u(z) v_B‖)`. -/
theorem exists_tame_bound_graph {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : X × F → G} {t K : Set (X × F)} {n : ℕ} (hΦ : ContDiffOn ℝ n Φ t)
    (ht : UniqueDiffOn ℝ t) (hK : IsCompact K) (hKt : K ⊆ t) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C, 0 ≤ C ∧ ∀ (u : X → F) (s : Set X), UniqueDiffOn ℝ s → ContDiffOn ℝ n u s →
      MapsTo (fun x => (x, u x)) s t → ∀ z ∈ s, (z, u z) ∈ K →
      ∀ (v : Fin n → X), (∀ i, ‖v i‖ ≤ 1) → ∀ (wt : Fin n → ℕ),
      (∀ B : Finset (Fin n), B.Nonempty → 2 * ∑ i ∈ B, wt i ≤ ∑ i, wt i →
        ‖blockDeriv u s z v B‖ ≤ R) →
      ‖iteratedFDerivWithin ℝ n (fun x => Φ (x, u x)) s z v‖ ≤
        C * (1 + ∑ B ∈ Finset.univ.filter (fun B : Finset (Fin n) => B.Nonempty),
          ‖blockDeriv u s z v B‖) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_tame_bound_comp (X := X) hΦ ht hK hKt (R := 1 + R)
    (by linarith)
  set N : ℝ := ((Finset.univ.filter (fun B : Finset (Fin n) => B.Nonempty)).card : ℝ) with hN
  refine ⟨C₁ * (1 + N), by positivity, ?_⟩
  intro u s hs hu hst z hz hzK v hv wt hsmall
  have hU : ContDiffOn ℝ n (fun x => (x, u x)) s := contDiffOn_id.prodMk hu
  have hblock : ∀ B : Finset (Fin n), B.Nonempty →
      ‖blockDeriv (fun x => (x, u x)) s z v B‖ ≤ 1 + ‖blockDeriv u s z v B‖ := by
    intro B hB
    have hcard : B.card ≤ n := by
      simpa using Finset.card_le_univ B
    exact norm_iteratedFDerivWithin_graph_apply_le (Finset.card_pos.2 hB)
      (hu.of_le (by exact_mod_cast hcard)) hs hz _ (fun j => hv _)
  have key := hC₁ (fun x => (x, u x)) s hs hU hst z hz hzK v wt (fun B hB hw =>
    (hblock B hB).trans (by linarith [hsmall B hB hw]))
  have hsum : ∑ B ∈ Finset.univ.filter (fun B : Finset (Fin n) => B.Nonempty),
        ‖blockDeriv (fun x => (x, u x)) s z v B‖ ≤
      N + ∑ B ∈ Finset.univ.filter (fun B : Finset (Fin n) => B.Nonempty),
        ‖blockDeriv u s z v B‖ := by
    calc _ ≤ ∑ B ∈ Finset.univ.filter (fun B : Finset (Fin n) => B.Nonempty),
          (1 + ‖blockDeriv u s z v B‖) :=
          Finset.sum_le_sum fun B hB => hblock B (Finset.mem_filter.1 hB).2
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact key.trans (graph_arith hC₁0 (by positivity)
    (Finset.sum_nonneg fun _ _ => norm_nonneg _) hsum)

end ShortTime.FaaDiBruno
