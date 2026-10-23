import ShortTime.Nonlinear.FibreMap
import ShortTime.Nonlinear.FibreMapChart
import ShortTime.Nonlinear.FibreMapNorm
import ShortTime.Analysis.FaaDiBruno

/-!
# The pointwise tame bound for smooth fibre maps (Step 3 of `prop:nemytskii`)

`FibreMap.exists_tame_pointwise`: near a smooth reference tuple `W` with values in the domain, the
jets of `Φ[λ, V]` of weight at most `w` are bounded by the jets of `V`, linearly, as soon as the jets
of `V` of weight at most `w/2` are bounded.

The proof is local. In the chart and trivializations at `α`:

* `Φ[λ, V]` reads `(t, y) ↦ euclRep (t, y, valFam V (t, y))`, with `euclRep` smooth on a relatively
  open set (`exists_euclDom`);
* the jets of `V` and of `Φ[λ, V]` are compared with mixed coordinate derivatives
  (`FibreMapChart`), and these obey the Euclidean tame Faà di Bruno bound (`FaaDiBruno`);
* the tube condition `|V - W| ≤ δ` keeps the graph of `valFam V` in a compact subset of the domain.

Finally `M` is covered by finitely many patches.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter Topology
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Elliptic DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff

namespace ShortTime

/-! ### Uniform constants -/

theorem exists_const_forall_le {P : ℕ → ℝ → Prop} (hmono : ∀ a C C', C ≤ C' → P a C → P a C')
    (h : ∀ a, ∃ C, P a C) (A : ℕ) : ∃ C, 0 ≤ C ∧ ∀ a ≤ A, P a C := by
  induction A with
  | zero =>
    obtain ⟨C, hC⟩ := h 0
    refine ⟨max C 0, le_max_right _ _, fun a ha => ?_⟩
    obtain rfl : a = 0 := Nat.le_zero.mp ha
    exact hmono 0 _ _ (le_max_left _ _) hC
  | succ A ih =>
    obtain ⟨C₀, hC₀, h₀⟩ := ih
    obtain ⟨C₁, h₁⟩ := h (A + 1)
    refine ⟨max C₀ C₁, le_max_of_le_left hC₀, fun a ha => ?_⟩
    rcases Nat.lt_or_ge a (A + 1) with h' | h'
    · exact hmono a _ _ (le_max_left _ _) (h₀ a (by omega))
    · obtain rfl : a = A + 1 := by omega
      exact hmono _ _ _ (le_max_right _ _) h₁

theorem exists_const_forall_fintype {κ : Type*} [Fintype κ] {P : κ → ℝ → Prop}
    (hmono : ∀ a C C', C ≤ C' → P a C → P a C') (h : ∀ a, ∃ C, P a C) :
    ∃ C, 0 ≤ C ∧ ∀ a, P a C := by
  classical
  choose C hC using h
  refine ⟨∑ a, max (C a) 0, Finset.sum_nonneg fun _ _ => le_max_right _ _, fun a => ?_⟩
  exact hmono a _ _ ((le_max_left _ _).trans (Finset.single_le_sum
    (f := fun a => max (C a) 0) (fun _ _ => le_max_right _ _) (Finset.mem_univ a))) (hC a)

/-- Iterated derivatives of a function into a product, componentwise. -/
theorem iteratedFDerivWithin_pi_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {κ : Type*} [Fintype κ] {F : κ → Type*} [∀ c, NormedAddCommGroup (F c)]
    [∀ c, NormedSpace ℝ (F c)] {n : ℕ} {u : X → ∀ c, F c} {s : Set X} {z : X}
    (hu : ContDiffWithinAt ℝ n u s z) (hs : UniqueDiffOn ℝ s) (hz : z ∈ s) (m : Fin n → X)
    (c : κ) :
    iteratedFDerivWithin ℝ n u s z m c = iteratedFDerivWithin ℝ n (fun x => u x c) s z m := by
  have h := (ContinuousLinearMap.proj (R := ℝ) (φ := F) c).iteratedFDerivWithin_comp_left hu hs hz
    le_rfl
  have e : (fun x => u x c) = (ContinuousLinearMap.proj (R := ℝ) (φ := F) c) ∘ u := rfl
  rw [e, h]
  rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

variable {ι : Type*} [Fintype ι]

namespace FibreMap

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] {b : ι → ℕ} {b' : ℕ}
variable {g : SmoothRiemannianMetric I M}

theorem mem_trivAt_baseSet_of_target {α : M} {y : E} (hy : y ∈ (extChartAt I α).target) (a : ℕ) :
    (extChartAt I α).symm y ∈ (trivAt I M 0 a α).baseSet :=
  ⟨mem_tangent_baseSet_of_target α hy, mem_tangent_baseSet_of_target α hy⟩

theorem mem_prodBase_of_target {α : M} {y : E} (hy : y ∈ (extChartAt I α).target) :
    (extChartAt I α).symm y ∈ prodBase (I := I) b b' α :=
  ⟨mem_trivAt_baseSet_of_target hy b', mem_iInter.2 fun c => mem_trivAt_baseSet_of_target hy (b c)⟩

/-- `F` read in the chart and the trivializations at `α`, as a function of `((t, y), z)`. -/
def euclRep (Φ : FibreMap I M Λ b b') (lam : Λ) (α : M) (p : (ℝ × E) × ProdModel E b) :
    TensorRSModel 0 b' ℝ E :=
  (trivAt I M 0 b' α).continuousLinearMapAt ℝ ((extChartAt I α).symm p.1.2)
    (Φ.F lam p.1.1 ((extChartAt I α).symm p.1.2)
      (prodOfModel b α ((extChartAt I α).symm p.1.2) p.2))

/-- **The Euclidean representative is smooth on a relatively open domain.** -/
theorem exists_euclDom (Φ : FibreMap I M Λ b b') (lam : Λ) (α : M) {T : ℝ} (hT : T ≤ Φ.T₀) :
    ∃ Wd : Set ((ℝ × E) × ProdModel E b), IsOpen Wd ∧
      ContDiffOn ℝ ∞ (Φ.euclRep lam α) (((Icc 0 T ×ˢ (extChartAt I α).target) ×ˢ univ) ∩ Wd) ∧
      (∀ p ∈ ((Icc 0 T ×ˢ (extChartAt I α).target) ×ˢ univ) ∩ Wd,
        prodOfModel b α ((extChartAt I α).symm p.1.2) p.2 ∈
          Φ.dom lam p.1.1 ((extChartAt I α).symm p.1.2)) ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ (extChartAt I α).target, ∀ z : ProdModel E b,
        prodOfModel b α ((extChartAt I α).symm y) z ∈ Φ.dom lam t ((extChartAt I α).symm y) →
          ((t, y), z) ∈ Wd := by
  obtain ⟨U, hU, hdom⟩ := Φ.dom_relOpen α
  set ψ : (ℝ × E) × ProdModel E b → Λ × ℝ × M × ProdModel E b :=
    fun p => (lam, p.1.1, (extChartAt I α).symm p.1.2, p.2) with hψ
  set Tg : Set ((ℝ × E) × ProdModel E b) := {p | p.1.2 ∈ (extChartAt I α).target} with hTg
  have hTgo : IsOpen Tg := (isOpen_extChartAt_target α).preimage (continuous_snd.comp continuous_fst)
  have hψc : ContinuousOn ψ Tg :=
    continuousOn_const.prodMk ((continuous_fst.comp continuous_fst).continuousOn.prodMk
      (((continuousOn_extChartAt_symm α).comp (continuous_snd.comp continuous_fst).continuousOn
        (fun p hp => hp)).prodMk continuous_snd.continuousOn))
  set D := {q ∈ prodSlab (I := I) Λ b b' Φ.T₀ α |
    prodOfModel b α q.2.2.1 q.2.2.2 ∈ Φ.dom q.1 q.2.1 q.2.2.1} with hD
  refine ⟨Tg ∩ ψ ⁻¹' U, hψc.isOpen_inter_preimage hTgo hU, ?_, ?_, ?_⟩
  · have hmem : MapsTo ψ (((Icc 0 T ×ˢ (extChartAt I α).target) ×ˢ univ) ∩ (Tg ∩ ψ ⁻¹' U)) D := by
      intro p hp
      have : ψ p ∈ U ∩ prodSlab (I := I) Λ b b' Φ.T₀ α :=
        ⟨hp.2.2, ⟨hp.1.1.1.1, hp.1.1.1.2.trans hT⟩, mem_prodBase_of_target hp.1.1.2⟩
      rw [← hdom] at this
      exact this
    have hψs : ContMDiffOn 𝓘(ℝ, (ℝ × E) × ProdModel E b)
        (𝓘(ℝ, Λ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, ProdModel E b)))) ∞ ψ Tg :=
      contMDiffOn_const.prodMk ((contDiff_fst.comp contDiff_fst).contMDiff.contMDiffOn.prodMk
        (((contMDiffOn_extChartAt_symm α).comp
          (contDiff_snd.comp contDiff_fst).contMDiff.contMDiffOn (fun p hp => hp)).prodMk
          contDiff_snd.contMDiff.contMDiffOn))
    have h := (Φ.smooth α).comp (hψs.mono fun p hp => hp.2.1) hmem
    exact contMDiffOn_iff_contDiffOn.mp h
  · intro p hp
    have : ψ p ∈ U ∩ prodSlab (I := I) Λ b b' Φ.T₀ α :=
      ⟨hp.2.2, ⟨hp.1.1.1.1, hp.1.1.1.2.trans hT⟩, mem_prodBase_of_target hp.1.1.2⟩
    rw [← hdom] at this
    exact this.2
  · intro t ht y hy z hz
    have : ψ ((t, y), z) ∈ D :=
      ⟨⟨⟨ht.1, ht.2.trans hT⟩, mem_prodBase_of_target hy⟩, hz⟩
    rw [hdom] at this
    exact ⟨hy, this.1⟩

/-- The chart readings of a tuple of families. -/
def valFam (α : M) (V : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)) (q : ℝ × E) : ProdModel E b :=
  fun c => chartFam g α (V c) q

theorem valFam_eq (α : M) (V : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)) (q : ℝ × E) :
    valFam α V q = prodTriv b α ((extChartAt I α).symm q.2)
      (valAt (fun c => V c q.1) ((extChartAt I α).symm q.2)) := rfl

theorem contDiffOn_valFam (α : M) {S : Set ℝ} {V : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)}
    (hV : ∀ c, JointlySmoothOn g 0 (b c) S (V c)) :
    ContDiffOn ℝ ∞ (valFam α V) (S ×ˢ (extChartAt I α).target) :=
  contDiffOn_pi.2 fun c => contDiffOn_chartFam α (hV c)

theorem prodOfModel_valFam {α : M} (V : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)) {q : ℝ × E}
    (hq : q.2 ∈ (extChartAt I α).target) :
    prodOfModel b α ((extChartAt I α).symm q.2) (valFam α V q) =
      valAt (fun c => V c q.1) ((extChartAt I α).symm q.2) := by
  rw [valFam_eq, prodOfModel_prodTriv (mem_prodBase_of_target (b := b) (b' := 0) hq)]

/-- `Φ[λ, V]`, read in the chart at `α`, is `euclRep` along the graph of `valFam V`. -/
theorem chartFam_apply_eq (Φ : FibreMap I M Λ b b') (lam : Λ) {T : ℝ} (hT : T ≤ Φ.T₀)
    {V : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)}
    (hV : ∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (V c))
    (hdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, valAt (fun c => V c t) x ∈ Φ.dom lam t x)
    {α : M} {q : ℝ × E} (hq : q ∈ Icc 0 T ×ˢ (extChartAt I α).target) :
    chartFam g α (Φ.apply lam V) q = Φ.euclRep lam α (q, valFam α V q) := by
  have hex := (Φ.jointlySmoothOn_fibreApply lam hT hV hdom).1 q.1 hq.1
  change (trivAt I M 0 b' α).continuousLinearMapAt ℝ ((extChartAt I α).symm q.2)
    ((Φ.apply lam V q.1).toSection ((extChartAt I α).symm q.2)) = _
  rw [Φ.apply_toSection lam V q.1 hex]
  simp only [euclRep]
  rw [prodOfModel_valFam V hq.2]

/-! ### Blocks of sorted directions -/

section Blocks

variable {g : SmoothRiemannianMetric I M}

theorem sum_wt_block (p m : ℕ) {j : ℕ} (Bs : Finset (Fin (m + j))) {sB : ℕ} (h1 : sB ≤ Bs.card)
    (hsp : ∀ l : Fin Bs.card, (l : ℕ) < sB → ((Bs.orderEmbOfFin rfl l : Fin (m + j)) : ℕ) < m)
    (htm : ∀ l : Fin Bs.card, sB ≤ (l : ℕ) → m ≤ ((Bs.orderEmbOfFin rfl l : Fin (m + j)) : ℕ)) :
    ∑ l ∈ Bs, (if (l : ℕ) < m then 1 else 2 * p) = sB + (Bs.card - sB) * (2 * p) := by
  rw [IterDir.sum_orderEmb Bs (fun l => if (l : ℕ) < m then 1 else 2 * p)]
  have h : ∀ l : Fin Bs.card,
      (if ((Bs.orderEmbOfFin rfl l : Fin (m + j)) : ℕ) < m then 1 else 2 * p) =
        (fun l : ℕ => if l < sB then 1 else 2 * p) l := by
    intro l
    rcases Nat.lt_or_ge (l : ℕ) sB with hl | hl
    · simp only [if_pos (hsp l hl), if_pos hl]
    · simp only [if_neg (not_lt.2 (htm l hl)), if_neg (not_lt.2 hl)]
  rw [Finset.sum_congr rfl fun l _ => h l, Fin.sum_univ_eq_sum_range
    (fun l : ℕ => if l < sB then 1 else 2 * p), IterDir.sum_range_ite_lt, min_eq_left h1, mul_one]

theorem sum_wt_univ (p m j : ℕ) :
    ∑ l : Fin (m + j), (if (l : ℕ) < m then 1 else 2 * p) = m + j * (2 * p) := by
  rw [Fin.sum_univ_eq_sum_range (fun l : ℕ => if l < m then 1 else 2 * p),
    IterDir.sum_range_ite_lt, min_eq_left (Nat.le_add_right _ _), mul_one, Nat.add_sub_cancel_left]

/-- A sorted block of the directions `(e, …, e, τ, …, τ)`. -/
theorem block_comp_le {α : M} {ρ T : ℝ}
    {B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯} (hT : 0 < T)
    (hball : Metric.closedBall (extChartAt I α α) ρ ⊆ (extChartAt I α).target)
    (hB : ∀ y ∈ Metric.closedBall (extChartAt I α α) ρ, ∀ k,
      trivToE I α ((extChartAt I α).symm y) (B k ((extChartAt I α).symm y)) = Module.finBasis ℝ E k)
    {a : ℕ} {u : ℝ → SmoothCcTensor g 0 a} (hu : JointlySmoothOn g 0 a (Icc 0 T) u) {m j : ℕ}
    (e : Fin m → E) (he : ∀ l, ‖e l‖ ≤ 1) (Bs : Finset (Fin (m + j))) {sB : ℕ}
    (h1 : sB ≤ Bs.card)
    (hsp : ∀ l : Fin Bs.card, (l : ℕ) < sB → ((Bs.orderEmbOfFin rfl l : Fin (m + j)) : ℕ) < m)
    (htm : ∀ l : Fin Bs.card, sB ≤ (l : ℕ) → m ≤ ((Bs.orderEmbOfFin rfl l : Fin (m + j)) : ℕ))
    {q : ℝ × E} (hq : q ∈ Icc 0 T ×ˢ Metric.ball (extChartAt I α α) ρ) :
    ‖iteratedFDerivWithin ℝ Bs.card (chartFam g α u) (Icc 0 T ×ˢ Metric.ball (extChartAt I α α) ρ) q
        (fun l => Fin.append (fun l => ((0 : ℝ), e l)) (fun _ : Fin j => ((1 : ℝ), (0 : E)))
          (Bs.orderEmbOfFin rfl l))‖ ≤
      ‖iteratedFDeriv ℝ sB (chartRd g α (timeDerivIter T u (Bs.card - sB) q.1)) q.2‖ := by
  refine norm_iteratedFDerivWithin_chartFam_sorted_le hT hball hB hu h1 _ (fun l hl => ?_)
    (fun l hl => ?_) hq
  · rw [IterDir.append_apply_lt _ _ _ (hsp l hl)]
    exact ⟨rfl, he _⟩
  · rw [IterDir.append_apply_ge _ _ _ (htm l hl)]

end Blocks

/-! ### Arithmetic -/

theorem div_aux {C x : ℝ} (hC : 0 ≤ C) : C * (x ^ 2 / (C + 1)) ≤ x ^ 2 := by
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg x]

theorem norm_le_sqrt_mul {X : Type*} [NormedAddCommGroup X] {z : X} {C a : ℝ} (hC : 0 ≤ C)
    (h : ‖z‖ ^ 2 ≤ C * a) : ‖z‖ ≤ Real.sqrt C * Real.sqrt a := by
  rw [← Real.sqrt_mul hC]
  have := Real.abs_le_sqrt h
  rwa [abs_norm] at this

theorem final_arith {K0 a J S Nt X : ℝ} (hK0 : 0 ≤ K0) (_ha : 0 ≤ a) (hJ0 : 0 ≤ J)
    (hS : 0 ≤ S) (_hNt : 0 ≤ Nt) (hJ : J ≤ Nt * Real.sqrt S) (hX : X ≤ K0 * (1 + a * J) ^ 2) :
    X ≤ (2 * K0 * (1 + a ^ 2 * Nt ^ 2)) * (1 + S) := by
  have h1 : (1 + a * J) ^ 2 ≤ 2 * (1 + a ^ 2 * J ^ 2) := by nlinarith [sq_nonneg (1 - a * J)]
  have h2 : J ^ 2 ≤ Nt ^ 2 * S := by
    have := pow_le_pow_left₀ hJ0 hJ 2
    rwa [mul_pow, Real.sq_sqrt hS] at this
  have h3 : a ^ 2 * J ^ 2 ≤ a ^ 2 * (Nt ^ 2 * S) := mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : 1 + a ^ 2 * (Nt ^ 2 * S) ≤ (1 + a ^ 2 * Nt ^ 2) * (1 + S) := by
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg a) (sq_nonneg Nt)) hS]
  calc X ≤ K0 * (1 + a * J) ^ 2 := hX
    _ ≤ K0 * (2 * (1 + a ^ 2 * J ^ 2)) := mul_le_mul_of_nonneg_left h1 hK0
    _ ≤ K0 * (2 * ((1 + a ^ 2 * Nt ^ 2) * (1 + S))) :=
        mul_le_mul_of_nonneg_left (by linarith) hK0
    _ = (2 * K0 * (1 + a ^ 2 * Nt ^ 2)) * (1 + S) := by ring

theorem sum3_le {κ : Type*} [Fintype κ] (f : κ → ℕ → ℕ → ℝ) (hf : ∀ c a b, 0 ≤ f c a b) {j i j₀ i₀ : ℕ}
    (hj : j₀ ≤ j) (hi : i₀ ≤ i) :
    ∑ c, ∑ k ∈ Finset.range (i₀ + 1), f c j₀ k ≤
      ∑ c, ∑ j' ∈ Finset.range (j + 1), ∑ i' ∈ Finset.range (i + 1), f c j' i' := by
  refine Finset.sum_le_sum fun c _ => ?_
  calc ∑ k ∈ Finset.range (i₀ + 1), f c j₀ k ≤ ∑ k ∈ Finset.range (i + 1), f c j₀ k :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          fun k _ _ => hf c j₀ k
    _ ≤ ∑ j' ∈ Finset.range (j + 1), ∑ i' ∈ Finset.range (i + 1), f c j' i' :=
        Finset.single_le_sum (f := fun j' => ∑ i' ∈ Finset.range (i + 1), f c j' i')
          (fun j' _ => Finset.sum_nonneg fun k _ => hf c j' k)
          (Finset.mem_range.2 (by omega))

theorem sum3_sqrt_le {κ : Type*} [Fintype κ] (f : κ → ℕ → ℕ → ℝ) (hf : ∀ c a b, 0 ≤ f c a b)
    (j i w : ℕ) (hj : j ≤ w) (hi : i ≤ w) :
    ∑ c, ∑ j' ∈ Finset.range (j + 1), ∑ i' ∈ Finset.range (i + 1), Real.sqrt (f c j' i') ≤
      (Fintype.card κ * ((w : ℝ) + 1) ^ 2) *
        Real.sqrt (∑ c, ∑ j' ∈ Finset.range (j + 1), ∑ i' ∈ Finset.range (i + 1), f c j' i') := by
  set S := ∑ c, ∑ j' ∈ Finset.range (j + 1), ∑ i' ∈ Finset.range (i + 1), f c j' i'
  have hle : ∀ c, ∀ j' ∈ Finset.range (j + 1), ∀ i' ∈ Finset.range (i + 1),
      Real.sqrt (f c j' i') ≤ Real.sqrt S := by
    intro c j' hj' i' hi'
    refine Real.sqrt_le_sqrt ?_
    calc f c j' i' ≤ ∑ i' ∈ Finset.range (i + 1), f c j' i' :=
          Finset.single_le_sum (f := fun i' => f c j' i') (fun k _ => hf c j' k) hi'
      _ ≤ ∑ j' ∈ Finset.range (j + 1), ∑ i' ∈ Finset.range (i + 1), f c j' i' :=
          Finset.single_le_sum (f := fun j' => ∑ i' ∈ Finset.range (i + 1), f c j' i')
            (fun j' _ => Finset.sum_nonneg fun k _ => hf c j' k) hj'
      _ ≤ S := Finset.single_le_sum
          (f := fun c => ∑ j' ∈ Finset.range (j + 1), ∑ i' ∈ Finset.range (i + 1), f c j' i')
          (fun c _ => Finset.sum_nonneg fun j' _ => Finset.sum_nonneg fun k _ => hf c j' k)
          (Finset.mem_univ c)
  calc ∑ c, ∑ j' ∈ Finset.range (j + 1), ∑ i' ∈ Finset.range (i + 1), Real.sqrt (f c j' i')
      ≤ ∑ _c : κ, ∑ _j' ∈ Finset.range (j + 1), ∑ _i' ∈ Finset.range (i + 1), Real.sqrt S :=
        Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun j' hj' => Finset.sum_le_sum
          fun i' hi' => hle c j' hj' i' hi'
    _ = (Fintype.card κ * (((j : ℝ) + 1) * ((i : ℝ) + 1))) * Real.sqrt S := by
        simp only [Finset.sum_const, Finset.card_range, Finset.card_univ, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ (Fintype.card κ * ((w : ℝ) + 1) ^ 2) * Real.sqrt S := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity))
          (Real.sqrt_nonneg _)
        have hj' : (j : ℝ) ≤ w := by exact_mod_cast hj
        have hi' : (i : ℝ) ≤ w := by exact_mod_cast hi
        rw [sq]
        exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)

/-! ### A normalized coordinate frame of the model space -/

variable (E) in
/-- The scale making the basis vectors of norm at most `1`. -/
def frameScale : ℝ := (1 + ∑ k, ‖Module.finBasis ℝ E k‖)⁻¹

theorem frameScale_pos : 0 < frameScale E := by
  unfold frameScale; positivity

variable (E) in
/-- Scaled basis vectors. -/
def eB (k : Fin (Module.finrank ℝ E)) : E := frameScale E • Module.finBasis ℝ E k

variable (E) in
/-- The dual functionals of `eB`. -/
def cB (k : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ := (frameScale E)⁻¹ • coordL k

theorem norm_eB_le (k : Fin (Module.finrank ℝ E)) : ‖eB E k‖ ≤ 1 := by
  have hS : ‖Module.finBasis ℝ E k‖ ≤ 1 + ∑ k, ‖Module.finBasis ℝ E k‖ := by
    have := Finset.single_le_sum (f := fun k => ‖Module.finBasis ℝ E k‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ k)
    linarith
  rw [eB, norm_smul, Real.norm_of_nonneg frameScale_pos.le, frameScale,
    inv_mul_le_iff₀ (by positivity), mul_one]
  exact hS

theorem sum_cB_eB (v : E) : ∑ k, cB E k v • eB E k = v := by
  have h0 : frameScale E ≠ 0 := frameScale_pos.ne'
  conv_rhs => rw [← sum_coordL_smul v]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [cB, eB, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, smul_smul]
  congr 1
  field_simp

theorem small_arith {sB c m j i w p k : ℕ} (hk : k ≤ sB)
    (hsm : 2 * (sB + c * (2 * p)) ≤ m + j * (2 * p)) (hm : m ≤ i) (hw : 2 * p * j + i ≤ w) :
    2 * (2 * p * c + k) ≤ w := by
  rw [Nat.mul_comm (2 * p) c]
  rw [Nat.mul_comm (2 * p) j] at hw
  generalize c * (2 * p) = X at *
  generalize j * (2 * p) = Y at *
  omega

/-! ### The bound on a patch -/

section Core

variable {g : SmoothRiemannianMetric I M}

/-- The block derivatives of `valFam V` along sorted directions, bounded by the jets of `V`. -/
theorem block_bound {α : M} {ρ T : ℝ}
    {B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯} (hT : 0 < T)
    (hball : Metric.closedBall (extChartAt I α α) ρ ⊆ (extChartAt I α).target)
    (hB : ∀ y ∈ Metric.closedBall (extChartAt I α α) ρ, ∀ k,
      trivToE I α ((extChartAt I α).symm y) (B k ((extChartAt I α).symm y)) = Module.finBasis ℝ E k)
    {w : ℕ} {C₂ Ctw : ℝ} (hC₂0 : 0 ≤ C₂) (hCtw0 : 0 ≤ Ctw)
    (hC₂ : ∀ c, ∀ S : SmoothCcTensor g 0 (b c), ∀ n ≤ w, ∀ y ∈ Metric.closedBall (extChartAt I α α) ρ,
      ‖iteratedFDeriv ℝ n (chartRd g α S) y‖ ≤
        C₂ * ∑ k ∈ Finset.range (n + 1), ‖chartRd g α (iteratedCovGrad g 0 (b c) k S) y‖)
    (hTw : ∀ c, ∀ k ≤ w, ∀ y ∈ Metric.closedBall (extChartAt I α α) ρ,
      ∀ S : SmoothCcTensor g 0 (b c + k), ‖chartRd g α S y‖ ^ 2 ≤
        Ctw * riemannianFiberNormSq (I := I) (M := M) g 0 (b c + k) ((extChartAt I α).symm y)
          (S.toSection ((extChartAt I α).symm y)))
    {V : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)}
    (hV : ∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (V c)) (p : ℕ) {m j : ℕ} (hmj : m ≤ w)
    (e : Fin m → E) (he : ∀ l, ‖e l‖ ≤ 1) (Bs : Finset (Fin (m + j))) {q : ℝ × E}
    (hq : q ∈ Icc 0 T ×ˢ Metric.ball (extChartAt I α α) ρ) :
    ∃ sB, sB ≤ m ∧ Bs.card - sB ≤ j ∧
      ∑ l ∈ Bs, (if (l : ℕ) < m then 1 else 2 * p) = sB + (Bs.card - sB) * (2 * p) ∧
      ‖FaaDiBruno.blockDeriv (valFam α V) (Icc 0 T ×ˢ Metric.ball (extChartAt I α α) ρ) q
          (Fin.append (fun l => ((0 : ℝ), e l)) (fun _ : Fin j => ((1 : ℝ), (0 : E)))) Bs‖ ≤
        C₂ * Real.sqrt Ctw * ∑ c, ∑ k ∈ Finset.range (sB + 1),
          Real.sqrt (jetSq g T (V c) (Bs.card - sB) k q.1 ((extChartAt I α).symm q.2)) := by
  obtain ⟨sB, h1, h2, h3, hsp, htm⟩ := IterDir.exists_split_orderEmb m Bs
  refine ⟨sB, h2, by omega, sum_wt_block p m Bs h1 hsp htm, ?_⟩
  have hs : UniqueDiffOn ℝ (Icc 0 T ×ˢ Metric.ball (extChartAt I α α) ρ) :=
    UniqueDiffOn.prod (uniqueDiffOn_Icc hT) Metric.isOpen_ball.uniqueDiffOn
  have hsub : Icc 0 T ×ˢ Metric.ball (extChartAt I α α) ρ ⊆ Icc 0 T ×ˢ (extChartAt I α).target :=
    prod_mono le_rfl (Metric.ball_subset_closedBall.trans hball)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun c => ?_
  have hcd : ContDiffWithinAt ℝ Bs.card (valFam α V)
      (Icc 0 T ×ˢ Metric.ball (extChartAt I α α) ρ) q :=
    (((contDiffOn_valFam α hV).mono hsub) q hq).of_le (JetRec.natCast_le_infty _)
  rw [FaaDiBruno.blockDeriv, iteratedFDerivWithin_pi_apply hcd hs hq]
  refine (block_comp_le hT hball hB (hV c) e he Bs h1 hsp htm hq).trans ?_
  refine (hC₂ c _ sB (by omega) q.2 (Metric.ball_subset_closedBall hq.2)).trans ?_
  have hk : ∀ k ∈ Finset.range (sB + 1),
      ‖chartRd g α (iteratedCovGrad g 0 (b c) k (timeDerivIter T (V c) (Bs.card - sB) q.1)) q.2‖ ≤
        Real.sqrt Ctw * Real.sqrt (jetSq g T (V c) (Bs.card - sB) k q.1 ((extChartAt I α).symm q.2)) :=
    fun k hk => norm_le_sqrt_mul hCtw0 (hTw c k (by have := Finset.mem_range.1 hk; omega) q.2
      (Metric.ball_subset_closedBall hq.2) _)
  calc C₂ * ∑ k ∈ Finset.range (sB + 1),
        ‖chartRd g α (iteratedCovGrad g 0 (b c) k (timeDerivIter T (V c) (Bs.card - sB) q.1)) q.2‖
      ≤ C₂ * ∑ k ∈ Finset.range (sB + 1), Real.sqrt Ctw *
          Real.sqrt (jetSq g T (V c) (Bs.card - sB) k q.1 ((extChartAt I α).symm q.2)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hk) hC₂0
    _ = C₂ * Real.sqrt Ctw * ∑ k ∈ Finset.range (sB + 1),
          Real.sqrt (jetSq g T (V c) (Bs.card - sB) k q.1 ((extChartAt I α).symm q.2)) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ C₂ * Real.sqrt Ctw * ∑ c, ∑ k ∈ Finset.range (sB + 1),
          Real.sqrt (jetSq g T (V c) (Bs.card - sB) k q.1 ((extChartAt I α).symm q.2)) :=
        mul_le_mul_of_nonneg_left (Finset.single_le_sum
          (f := fun c => ∑ k ∈ Finset.range (sB + 1),
            Real.sqrt (jetSq g T (V c) (Bs.card - sB) k q.1 ((extChartAt I α).symm q.2)))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _) (Finset.mem_univ c))
          (by positivity)

end Core

/-- The constant of the tame bound. -/
def tameConst (Cfr C₁ C₂ Ctw CF Ccb : ℝ) (w d nι : ℕ) : ℝ :=
  2 * (Cfr * (C₁ * ((w : ℝ) + 1) * ((1 + Ccb) ^ w * (1 + (d : ℝ)) ^ w) * CF) ^ 2) *
    (1 + (2 ^ w * (C₂ * Real.sqrt Ctw)) ^ 2 * ((nι : ℝ) * ((w : ℝ) + 1) ^ 2) ^ 2)

theorem tameConst_nonneg {Cfr C₁ C₂ Ctw CF Ccb : ℝ} (w d nι : ℕ) (hCfr : 0 ≤ Cfr) :
    0 ≤ tameConst Cfr C₁ C₂ Ctw CF Ccb w d nι := by
  unfold tameConst; positivity

theorem pow_aux {x : ℝ} (hx : 0 ≤ x) {m w : ℕ} (h : m ≤ w) : x ^ m ≤ (1 + x) ^ w :=
  (pow_le_pow_left₀ hx (by linarith) m).trans (pow_le_pow_right₀ (by linarith) h)

section Core2

variable {g : SmoothRiemannianMetric I M}

/-- **The tame bound on a patch**, with all constants given. -/
theorem core_bound (Φ : FibreMap I M Λ b b') (lam : Λ) {T : ℝ} (hT : 0 < T) (hTT : T ≤ Φ.T₀)
    {α : M} {r : ℝ} {B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (hball : Metric.closedBall (extChartAt I α α) r ⊆ (extChartAt I α).target)
    (hB : ∀ y ∈ Metric.closedBall (extChartAt I α α) r, ∀ k,
      trivToE I α ((extChartAt I α).symm y) (B k ((extChartAt I α).symm y)) = Module.finBasis ℝ E k)
    {p w : ℕ} (hp : 0 < p) {tα K : Set ((ℝ × E) × ProdModel E b)} (hKt : K ⊆ tα)
    {C₂ Ctw C₁ Cfr CF R' R : ℝ} (hC₂0 : 0 ≤ C₂) (hCtw0 : 0 ≤ Ctw) (hC₁0 : 0 ≤ C₁)
    (hCfr0 : 0 ≤ Cfr) (hCF0 : 0 ≤ CF)
    (hC₂ : ∀ c, ∀ S : SmoothCcTensor g 0 (b c), ∀ n ≤ w, ∀ y ∈ Metric.closedBall (extChartAt I α α) r,
      ‖iteratedFDeriv ℝ n (chartRd g α S) y‖ ≤
        C₂ * ∑ k ∈ Finset.range (n + 1), ‖chartRd g α (iteratedCovGrad g 0 (b c) k S) y‖)
    (hTw : ∀ c, ∀ k ≤ w, ∀ y ∈ Metric.closedBall (extChartAt I α α) r,
      ∀ S : SmoothCcTensor g 0 (b c + k), ‖chartRd g α S y‖ ^ 2 ≤
        Ctw * riemannianFiberNormSq (I := I) (M := M) g 0 (b c + k) ((extChartAt I α).symm y)
          (S.toSection ((extChartAt I α).symm y)))
    (hC₁ : ∀ i ≤ w, ∀ S : SmoothCcTensor g 0 b', ∀ y ∈ Metric.closedBall (extChartAt I α α) r,
      ‖chartRd g α (iteratedCovGrad g 0 b' i S) y‖ ≤
        C₁ * ∑ m ∈ Finset.range (i + 1), ‖iteratedFDeriv ℝ m (chartRd g α S) y‖)
    (hfr : ∀ i ≤ w, ∀ y ∈ Metric.closedBall (extChartAt I α α) r,
      ∀ v : TensorRSSpace 0 (b' + i) I ((extChartAt I α).symm y),
        riemannianFiberNormSq (I := I) (M := M) g 0 (b' + i) ((extChartAt I α).symm y) v ≤
          Cfr * ‖(trivAt I M 0 (b' + i) α).continuousLinearMapAt ℝ ((extChartAt I α).symm y) v‖ ^ 2)
    (hCF : ∀ n ≤ w, ∀ (u : ℝ × E → ProdModel E b) (s : Set (ℝ × E)), UniqueDiffOn ℝ s →
      ContDiffOn ℝ n u s → MapsTo (fun x => (x, u x)) s tα → ∀ z ∈ s, (z, u z) ∈ K →
      ∀ v : Fin n → ℝ × E, (∀ i, ‖v i‖ ≤ 1) → ∀ wt : Fin n → ℕ,
      (∀ Bs : Finset (Fin n), Bs.Nonempty → 2 * ∑ i ∈ Bs, wt i ≤ ∑ i, wt i →
        ‖FaaDiBruno.blockDeriv u s z v Bs‖ ≤ R') →
      ‖iteratedFDerivWithin ℝ n (fun x => Φ.euclRep lam α (x, u x)) s z v‖ ≤
        CF * (1 + ∑ Bs ∈ Finset.univ.filter (fun Bs : Finset (Fin n) => Bs.Nonempty),
          ‖FaaDiBruno.blockDeriv u s z v Bs‖))
    (hR' : C₂ * Real.sqrt Ctw * (Fintype.card ι * ((w : ℝ) + 1) * Real.sqrt (max R 0)) ≤ R')
    {V : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)}
    (hV : ∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (V c))
    (hdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, valAt (fun c => V c t) x ∈ Φ.dom lam t x)
    (hR : ∀ c j i, 2 * (2 * p * j + i) ≤ w → ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      jetSq g T (V c) j i t x ≤ R)
    (hVK : ∀ q ∈ Icc 0 T ×ˢ Metric.ball (extChartAt I α α) r, (q, valFam α V q) ∈ K)
    {j i : ℕ} (hji : 2 * p * j + i ≤ w) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {y : E}
    (hy : y ∈ Metric.ball (extChartAt I α α) r) :
    jetSq g T (Φ.apply lam V) j i t ((extChartAt I α).symm y) ≤
      tameConst Cfr C₁ C₂ Ctw CF (∑ k, ‖cB E k‖) w (Module.finrank ℝ E) (Fintype.card ι) *
        (1 + ∑ c, ∑ j' ∈ Finset.range (j + 1), ∑ i' ∈ Finset.range (i + 1),
          jetSq g T (V c) j' i' t ((extChartAt I α).symm y)) := by
  classical
  have hjp : j ≤ 2 * p * j := Nat.le_mul_of_pos_left j (by omega)
  have hj : j ≤ w := hjp.trans ((Nat.le_add_right _ _).trans hji)
  have hi : i ≤ w := (Nat.le_add_left i _).trans hji
  have hq : ((t, y) : ℝ × E) ∈ Icc 0 T ×ˢ Metric.ball (extChartAt I α α) r := ⟨ht, hy⟩
  have hs : UniqueDiffOn ℝ (Icc 0 T ×ˢ Metric.ball (extChartAt I α α) r) :=
    UniqueDiffOn.prod (uniqueDiffOn_Icc hT) Metric.isOpen_ball.uniqueDiffOn
  have hsub : Icc 0 T ×ˢ Metric.ball (extChartAt I α α) r ⊆ Icc 0 T ×ˢ (extChartAt I α).target :=
    prod_mono le_rfl (Metric.ball_subset_closedBall.trans hball)
  have hu := (Φ.jointlySmoothOn_fibreApply lam hTT hV hdom).2
  set x := (extChartAt I α).symm y with hx
  set J := ∑ c, ∑ j' ∈ Finset.range (j + 1), ∑ i' ∈ Finset.range (i + 1),
    Real.sqrt (jetSq g T (V c) j' i' t x) with hJ
  have hJ0 : 0 ≤ J := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  set a := 2 ^ w * (C₂ * Real.sqrt Ctw) with ha
  have ha0 : 0 ≤ a := by positivity
  -- derivatives along the frame directions
  have hdir : ∀ m ≤ i, ∀ κ : Fin m → Fin (Module.finrank ℝ E),
      ‖iteratedFDeriv ℝ m (chartRd g α (timeDerivIter T (Φ.apply lam V) j t)) y
        (fun l => eB E (κ l))‖ ≤ CF * (1 + a * J) := by
    intro m hm κ
    have hmw : m + j ≤ w := by
      have := hji
      generalize 2 * p * j = P at *
      omega
    have h1 := iteratedFDerivWithin_chartFam_append hT hball hB hu m j (fun l => eB E (κ l)) hq
    dsimp only at h1
    rw [← h1]
    have hcong : EqOn (chartFam g α (Φ.apply lam V)) (fun z => Φ.euclRep lam α (z, valFam α V z))
        (Icc 0 T ×ˢ Metric.ball (extChartAt I α α) r) := fun z hz =>
      chartFam_apply_eq Φ lam hTT hV hdom (hsub hz)
    rw [iteratedFDerivWithin_congr hcong hq]
    set v : Fin (m + j) → ℝ × E :=
      Fin.append (fun l => ((0 : ℝ), eB E (κ l))) (fun _ : Fin j => ((1 : ℝ), (0 : E))) with hv
    have hvn : ∀ l, ‖v l‖ ≤ 1 := by
      intro l
      rcases Nat.lt_or_ge (l : ℕ) m with h | h
      · rw [hv, IterDir.append_apply_lt _ _ _ h, norm_prod_le_iff]
        exact ⟨by simp, norm_eB_le _⟩
      · rw [hv, IterDir.append_apply_ge _ _ _ h, norm_prod_le_iff]
        exact ⟨by simp, by simp⟩
    have hsmall : ∀ Bs : Finset (Fin (m + j)), Bs.Nonempty →
        2 * ∑ l ∈ Bs, (fun l : Fin (m + j) => if (l : ℕ) < m then 1 else 2 * p) l ≤
          ∑ l, (fun l : Fin (m + j) => if (l : ℕ) < m then 1 else 2 * p) l →
        ‖FaaDiBruno.blockDeriv (valFam α V) (Icc 0 T ×ˢ Metric.ball (extChartAt I α α) r) (t, y)
          v Bs‖ ≤ R' := by
      intro Bs _ hsm
      obtain ⟨sB, h2, h3, hwB, hbd⟩ := block_bound hT hball hB hC₂0 hCtw0 hC₂ hTw hV p
        (by omega : m ≤ w) _ (fun l => norm_eB_le _) Bs hq
      beta_reduce at hsm
      rw [hwB, sum_wt_univ] at hsm
      refine hbd.trans (le_trans (mul_le_mul_of_nonneg_left ?_ (by positivity)) hR')
      calc ∑ c, ∑ k ∈ Finset.range (sB + 1),
            Real.sqrt (jetSq g T (V c) (Bs.card - sB) k (t, y).1
              ((extChartAt I α).symm (t, y).2))
          ≤ ∑ _c : ι, ∑ _k ∈ Finset.range (sB + 1), Real.sqrt (max R 0) :=
            Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun k hk =>
              Real.sqrt_le_sqrt ((hR c _ k (small_arith
                (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) hsm (by omega) hji) t ht x).trans
                (le_max_left _ _))
        _ = Fintype.card ι * ((sB : ℝ) + 1) * Real.sqrt (max R 0) := by
            simp only [Finset.sum_const, Finset.card_range, Finset.card_univ, nsmul_eq_mul]
            push_cast
            ring
        _ ≤ Fintype.card ι * ((w : ℝ) + 1) * Real.sqrt (max R 0) := by
            have : (sB : ℝ) ≤ w := by exact_mod_cast (by omega : sB ≤ w)
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith)
              (by positivity)) (Real.sqrt_nonneg _)
    have hmaps : MapsTo (fun z => (z, valFam α V z)) (Icc 0 T ×ˢ Metric.ball (extChartAt I α α) r)
        tα := fun z hz => hKt (hVK z hz)
    have hcdV : ContDiffOn ℝ ((m + j : ℕ) : WithTop ℕ∞) (valFam α V)
        (Icc 0 T ×ˢ Metric.ball (extChartAt I α α) r) :=
      ((contDiffOn_valFam α hV).mono hsub).of_le (JetRec.natCast_le_infty _)
    refine (hCF (m + j) hmw (valFam α V) _ hs hcdV hmaps (t, y) hq (hVK _ hq) v hvn _
      hsmall).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hCF0
    have hB1 : ∀ Bs ∈ Finset.univ.filter (fun Bs : Finset (Fin (m + j)) => Bs.Nonempty),
        ‖FaaDiBruno.blockDeriv (valFam α V) (Icc 0 T ×ˢ Metric.ball (extChartAt I α α) r) (t, y)
          v Bs‖ ≤ C₂ * Real.sqrt Ctw * J := by
      intro Bs _
      obtain ⟨sB, h2, h3, _, hbd⟩ := block_bound hT hball hB hC₂0 hCtw0 hC₂ hTw hV p
        (by omega : m ≤ w) _ (fun l => norm_eB_le _) Bs hq
      refine hbd.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact sum3_le (fun c a b => Real.sqrt (jetSq g T (V c) a b t x))
        (fun _ _ _ => Real.sqrt_nonneg _) (by omega : Bs.card - sB ≤ j) (by omega : sB ≤ i)
    have hcard : (((Finset.univ.filter
        (fun Bs : Finset (Fin (m + j)) => Bs.Nonempty)).card : ℕ) : ℝ) ≤ 2 ^ w := by
      have h1 : (Finset.univ.filter (fun Bs : Finset (Fin (m + j)) => Bs.Nonempty)).card ≤
          2 ^ (m + j) :=
        (Finset.card_filter_le _ _).trans (by simp [Finset.card_univ, Fintype.card_finset])
      calc _ ≤ ((2 ^ (m + j) : ℕ) : ℝ) := by exact_mod_cast h1
        _ ≤ 2 ^ w := by push_cast; exact pow_le_pow_right₀ (by norm_num) hmw
    have hsum := Finset.sum_le_sum hB1
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    have hCJ : 0 ≤ C₂ * Real.sqrt Ctw * J := by positivity
    have : (((Finset.univ.filter (fun Bs : Finset (Fin (m + j)) => Bs.Nonempty)).card : ℕ) : ℝ) *
        (C₂ * Real.sqrt Ctw * J) ≤ a * J := by
      rw [ha, mul_assoc (2 ^ w)]
      exact mul_le_mul_of_nonneg_right hcard hCJ
    linarith
  -- full derivatives
  set Q := (1 + ∑ k, ‖cB E k‖) ^ w * (1 + ((Module.finrank ℝ E : ℕ) : ℝ)) ^ w with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hL0 : 0 ≤ CF * (1 + a * J) := by positivity
  have hDm : ∀ m ≤ i,
      ‖iteratedFDeriv ℝ m (chartRd g α (timeDerivIter T (Φ.apply lam V) j t)) y‖ ≤
        Q * (CF * (1 + a * J)) := by
    intro m hm
    refine (JetRec.norm_le_sum_apply_frame (eB E) (cB E) sum_cB_eB m _).trans ?_
    have hcb0 : 0 ≤ ∑ k, ‖cB E k‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    calc (∑ k, ‖cB E k‖) ^ m * ∑ κ : Fin m → Fin (Module.finrank ℝ E),
          ‖iteratedFDeriv ℝ m (chartRd g α (timeDerivIter T (Φ.apply lam V) j t)) y
            (fun l => eB E (κ l))‖
        ≤ (∑ k, ‖cB E k‖) ^ m * ∑ _κ : Fin m → Fin (Module.finrank ℝ E), CF * (1 + a * J) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun κ _ => hdir m hm κ) (by positivity)
      _ = ((∑ k, ‖cB E k‖) ^ m * ((Module.finrank ℝ E : ℕ) : ℝ) ^ m) * (CF * (1 + a * J)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, nsmul_eq_mul]
          simp only [Fintype.card_fin]
          push_cast
          ring
      _ ≤ Q * (CF * (1 + a * J)) := by
          refine mul_le_mul_of_nonneg_right ?_ hL0
          exact mul_le_mul (pow_aux hcb0 (hm.trans hi)) (pow_aux (Nat.cast_nonneg _) (hm.trans hi))
            (by positivity) (by positivity)
  have hY : ‖chartRd g α (iteratedCovGrad g 0 b' i (timeDerivIter T (Φ.apply lam V) j t)) y‖ ≤
      C₁ * ((w : ℝ) + 1) * Q * CF * (1 + a * J) := by
    refine (hC₁ i hi _ y (Metric.ball_subset_closedBall hy)).trans ?_
    calc C₁ * ∑ m ∈ Finset.range (i + 1),
          ‖iteratedFDeriv ℝ m (chartRd g α (timeDerivIter T (Φ.apply lam V) j t)) y‖
        ≤ C₁ * ∑ _m ∈ Finset.range (i + 1), Q * (CF * (1 + a * J)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m hm =>
            hDm m (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm))) hC₁0
      _ = C₁ * ((i : ℝ) + 1) * (Q * (CF * (1 + a * J))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ C₁ * ((w : ℝ) + 1) * (Q * (CF * (1 + a * J))) := by
          have : (i : ℝ) ≤ w := by exact_mod_cast hi
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC₁0)
            (by positivity)
      _ = C₁ * ((w : ℝ) + 1) * Q * CF * (1 + a * J) := by ring
  have hjet : jetSq g T (Φ.apply lam V) j i t x ≤
      Cfr * ‖chartRd g α (iteratedCovGrad g 0 b' i (timeDerivIter T (Φ.apply lam V) j t)) y‖ ^ 2 :=
    hfr i hi y (Metric.ball_subset_closedBall hy) _
  have hX : jetSq g T (Φ.apply lam V) j i t x ≤
      (Cfr * (C₁ * ((w : ℝ) + 1) * Q * CF) ^ 2) * (1 + a * J) ^ 2 := by
    refine hjet.trans ?_
    have h2 := pow_le_pow_left₀ (norm_nonneg _) hY 2
    calc Cfr * ‖chartRd g α (iteratedCovGrad g 0 b' i
          (timeDerivIter T (Φ.apply lam V) j t)) y‖ ^ 2
        ≤ Cfr * (C₁ * ((w : ℝ) + 1) * Q * CF * (1 + a * J)) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 hCfr0
      _ = (Cfr * (C₁ * ((w : ℝ) + 1) * Q * CF) ^ 2) * (1 + a * J) ^ 2 := by ring
  have hJS := sum3_sqrt_le (fun c a b => jetSq g T (V c) a b t x)
    (fun c a b => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 _ _ _) j i w hj hi
  exact final_arith (by positivity) ha0 hJ0
    (Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 _ _ _) (by positivity) hJS hX

end Core2

section Patch

variable {g : SmoothRiemannianMetric I M}

/-- **The tame bound near a point `α`**: on a chart ball around `α`, the tube condition keeps `V` in
the domain, and the tame bound holds. -/
theorem patch_tame (Φ : FibreMap I M Λ b b') (lam : Λ) {T : ℝ} (hT : 0 < T) (hTT : T ≤ Φ.T₀)
    {W : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)} (hW : ∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (W c))
    (hWdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, valAt (fun c => W c t) x ∈ Φ.dom lam t x)
    {p : ℕ} (hp : 0 < p) (w : ℕ) (α : M) :
    ∃ r > 0, ∃ δ > 0,
      (∀ V : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c),
        (∀ c, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 0 (b c) x ((V c t - W c t).toSection x) ≤ δ) →
        ∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ Metric.closedBall (extChartAt I α α) r,
          valAt (fun c => V c t) ((extChartAt I α).symm y) ∈
            Φ.dom lam t ((extChartAt I α).symm y)) ∧
      ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ V : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c),
          (∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (V c)) →
          (∀ c, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g 0 (b c) x ((V c t - W c t).toSection x) ≤ δ) →
          (∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, valAt (fun c => V c t) x ∈ Φ.dom lam t x) →
          (∀ c j i, 2 * (2 * p * j + i) ≤ w → ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
            jetSq g T (V c) j i t x ≤ R) →
          ∀ j i, 2 * p * j + i ≤ w → ∀ t ∈ Icc (0 : ℝ) T,
            ∀ y ∈ Metric.ball (extChartAt I α α) r,
              jetSq g T (Φ.apply lam V) j i t ((extChartAt I α).symm y) ≤
                C * (1 + ∑ c, ∑ j' ∈ Finset.range (j + 1), ∑ i' ∈ Finset.range (i + 1),
                  jetSq g T (V c) j' i' t ((extChartAt I α).symm y)) := by
  classical
  -- the patch
  obtain ⟨Bf, hBf⟩ := exists_const_coord_fields (I := I) α (Module.finBasis ℝ E)
  have hfr : ∀ i : Fin (w + 1), ∃ C, 0 ≤ C ∧ ∀ᶠ x in 𝓝 α, ∀ v : TensorRSSpace 0 (b' + i) I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 (b' + i) x v ≤
        C * ‖(trivAt I M 0 (b' + i) α).continuousLinearMapAt ℝ x v‖ ^ 2 :=
    fun i => exists_fiberNormSq_le_triv (b' + i) α
  choose Cfr hCfr0 hCfr using hfr
  have hc : Tendsto (extChartAt I α).symm (𝓝 (extChartAt I α α)) (𝓝 α) := by
    have h := continuousAt_extChartAt_symm (I := I) α
    rwa [ContinuousAt, extChartAt_to_inv] at h
  have hev := (hc.eventually (hBf.and (Filter.eventually_all.2 hCfr))).and
    (extChartAt_target_mem_nhds (I := I) α)
  obtain ⟨r₀, hr₀, hball₀⟩ := Metric.nhds_basis_closedBall.eventually_iff.mp hev
  set c₀ := extChartAt I α α with hc₀
  have hr0 : 0 < r₀ / 2 := by positivity
  have hrr : r₀ / 2 < r₀ := by linarith
  have hball : Metric.closedBall c₀ r₀ ⊆ (extChartAt I α).target := fun y hy => (hball₀ hy).2
  have hB : ∀ y ∈ Metric.closedBall c₀ r₀, ∀ k,
      trivToE I α ((extChartAt I α).symm y) (Bf k ((extChartAt I α).symm y)) =
        Module.finBasis ℝ E k := fun y hy => (hball₀ hy).1.1
  have hsub : Metric.closedBall c₀ (r₀ / 2) ⊆ Metric.closedBall c₀ r₀ :=
    Metric.closedBall_subset_closedBall hrr.le
  have hball_r : Metric.closedBall c₀ (r₀ / 2) ⊆ (extChartAt I α).target := hsub.trans hball
  have hB_r : ∀ y ∈ Metric.closedBall c₀ (r₀ / 2), ∀ k,
      trivToE I α ((extChartAt I α).symm y) (Bf k ((extChartAt I α).symm y)) =
        Module.finBasis ℝ E k := fun y hy => hB y (hsub hy)
  set Cfrm := ∑ i, Cfr i with hCfrm
  have hCfrm0 : 0 ≤ Cfrm := Finset.sum_nonneg fun i _ => hCfr0 i
  have hfrb : ∀ i ≤ w, ∀ y ∈ Metric.closedBall c₀ (r₀ / 2),
      ∀ v : TensorRSSpace 0 (b' + i) I ((extChartAt I α).symm y),
        riemannianFiberNormSq (I := I) (M := M) g 0 (b' + i) ((extChartAt I α).symm y) v ≤
          Cfrm * ‖(trivAt I M 0 (b' + i) α).continuousLinearMapAt ℝ
            ((extChartAt I α).symm y) v‖ ^ 2 := by
    intro i hi y hy v
    refine ((hball₀ (hsub hy)).1.2 ⟨i, by omega⟩ v).trans
      (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
    exact Finset.single_le_sum (f := Cfr) (fun i _ => hCfr0 i) (Finset.mem_univ _)
  -- chart readings are bounded by the fibre norm
  set Kx := (extChartAt I α).symm '' Metric.closedBall c₀ (r₀ / 2) with hKxdef
  have hKx : IsCompact Kx := (isCompact_closedBall c₀ (r₀ / 2)).image_of_continuousOn
    ((continuousOn_extChartAt_symm α).mono hball_r)
  have hKxs : Kx ⊆ (chartAt H α).source := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I α).map_target (hball_r hy)
  obtain ⟨Ctw, hCtw0, hCtw⟩ := exists_const_forall_le
    (P := fun a C => ∀ y ∈ Metric.closedBall c₀ (r₀ / 2), ∀ S : SmoothCcTensor g 0 a,
      ‖chartRd g α S y‖ ^ 2 ≤ C * riemannianFiberNormSq (I := I) (M := M) g 0 a
        ((extChartAt I α).symm y) (S.toSection ((extChartAt I α).symm y)))
    (fun a C C' hCC' h y hy S => (h y hy S).trans (mul_le_mul_of_nonneg_right hCC'
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 a _ _)))
    (fun a => by
      obtain ⟨C, _, hC⟩ := exists_norm_twist_le (g := g) α a hKx hKxs
      exact ⟨C, fun y hy S => by
        rw [chartRd_eq_twist α S (hball_r hy)]
        exact hC _ ⟨y, hy, rfl⟩ _⟩) ((∑ c, b c) + w)
  have hbA : ∀ c, ∀ k ≤ w, b c + k ≤ (∑ c, b c) + w := fun c k hk =>
    Nat.add_le_add (Finset.single_le_sum (f := b) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)) hk
  have hTw : ∀ c, ∀ k ≤ w, ∀ y ∈ Metric.closedBall c₀ (r₀ / 2),
      ∀ S : SmoothCcTensor g 0 (b c + k), ‖chartRd g α S y‖ ^ 2 ≤
        Ctw * riemannianFiberNormSq (I := I) (M := M) g 0 (b c + k) ((extChartAt I α).symm y)
          (S.toSection ((extChartAt I α).symm y)) := fun c k hk => hCtw _ (hbA c k hk)
  -- the Euclidean domain and the tube
  obtain ⟨Wd, hWdo, hsmooth, hdomW, hinW⟩ := Φ.exists_euclDom lam α hTT
  set tα := ((Icc 0 T ×ˢ (extChartAt I α).target) ×ˢ (univ : Set (ProdModel E b))) ∩ Wd with htαdef
  have htα : UniqueDiffOn ℝ tα :=
    (UniqueDiffOn.prod (UniqueDiffOn.prod (uniqueDiffOn_Icc hT)
      (isOpen_extChartAt_target α).uniqueDiffOn) uniqueDiffOn_univ).inter hWdo
  have hUW := contDiffOn_valFam α hW
  set Gr := (fun q : ℝ × E => (q, valFam α W q)) '' (Icc 0 T ×ˢ Metric.closedBall c₀ (r₀ / 2))
    with hGrdef
  have hGc : IsCompact Gr := (isCompact_Icc.prod (isCompact_closedBall c₀ (r₀ / 2))).image_of_continuousOn
    (continuousOn_id.prodMk (hUW.continuousOn.mono (prod_mono le_rfl hball_r)))
  have hGW : Gr ⊆ Wd := by
    rintro _ ⟨q, hq, rfl⟩
    refine hinW q.1 hq.1 q.2 (hball_r hq.2) _ ?_
    rw [prodOfModel_valFam W (hball_r hq.2)]
    exact hWdom q.1 hq.1 _
  obtain ⟨ε, hε, hεW⟩ := hGc.exists_cthickening_subset_open hWdo hGW
  set K := Metric.cthickening ε Gr ∩
    ((Icc 0 T ×ˢ Metric.closedBall c₀ (r₀ / 2)) ×ˢ (univ : Set (ProdModel E b))) with hKdef
  have hK : IsCompact K := hGc.cthickening.inter_right
    ((isClosed_Icc.prod Metric.isClosed_closedBall).prod isClosed_univ)
  have hKt : K ⊆ tα := fun p hp => ⟨⟨⟨hp.2.1.1, hball_r hp.2.1.2⟩, mem_univ _⟩, hεW hp.1⟩
  set δ := ε ^ 2 / (Ctw + 1) with hδdef
  have hδ : 0 < δ := by positivity
  have htube : ∀ V : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c),
      (∀ c, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 0 (b c) x ((V c t - W c t).toSection x) ≤ δ) →
      ∀ q ∈ Icc 0 T ×ˢ Metric.closedBall c₀ (r₀ / 2), (q, valFam α V q) ∈ K := by
    intro V hVδ q hq
    refine ⟨Metric.mem_cthickening_of_dist_le _ (q, valFam α W q) ε Gr ⟨q, hq, rfl⟩ ?_,
      ⟨hq, mem_univ _⟩⟩
    rw [Prod.dist_eq, dist_self, dist_eq_norm]
    refine max_le hε.le ((pi_norm_le_iff_of_nonneg hε.le).2 fun c => ?_)
    have h1 := hTw c 0 (Nat.zero_le _) q.2 hq.2 (V c q.1 - W c q.1)
    have h2 := hVδ c q.1 hq.1 ((extChartAt I α).symm q.2)
    have h3 : ‖chartRd g α (V c q.1 - W c q.1) q.2‖ ^ 2 ≤ ε ^ 2 :=
      h1.trans ((mul_le_mul_of_nonneg_left h2 hCtw0).trans (div_aux hCtw0))
    rw [chartRd_sub] at h3
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hε.le (by norm_num)).mp h3
  have hdomV : ∀ V : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c),
      (∀ c, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 0 (b c) x ((V c t - W c t).toSection x) ≤ δ) →
      ∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ Metric.closedBall c₀ (r₀ / 2),
        valAt (fun c => V c t) ((extChartAt I α).symm y) ∈
          Φ.dom lam t ((extChartAt I α).symm y) := by
    intro V hVδ t ht y hy
    have h := hdomW _ (hKt (htube V hVδ (t, y) ⟨ht, hy⟩))
    dsimp only at h
    rwa [prodOfModel_valFam V (q := (t, y)) (hball_r hy)] at h
  refine ⟨r₀ / 2, hr0, δ, hδ, hdomV, fun R => ?_⟩
  -- the constants
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_const_forall_fintype
    (P := fun c C => ∀ S : SmoothCcTensor g 0 (b c), ∀ n ≤ w, ∀ y ∈ Metric.closedBall c₀ (r₀ / 2),
      ‖iteratedFDeriv ℝ n (chartRd g α S) y‖ ≤
        C * ∑ k ∈ Finset.range (n + 1), ‖chartRd g α (iteratedCovGrad g 0 (b c) k S) y‖)
    (fun c C C' h H S n hn y hy => (H S n hn y hy).trans
      (mul_le_mul_of_nonneg_right h (Finset.sum_nonneg fun _ _ => norm_nonneg _)))
    (fun c => by
      obtain ⟨C, _, hC⟩ := exists_const_forall_le
        (P := fun n C => ∀ S : SmoothCcTensor g 0 (b c), ∀ y ∈ Metric.closedBall c₀ (r₀ / 2),
          ‖iteratedFDeriv ℝ n (chartRd g α S) y‖ ≤
            C * ∑ k ∈ Finset.range (n + 1), ‖chartRd g α (iteratedCovGrad g 0 (b c) k S) y‖)
        (fun n C C' h H S y hy => (H S y hy).trans
          (mul_le_mul_of_nonneg_right h (Finset.sum_nonneg fun _ _ => norm_nonneg _)))
        (fun n => by
          obtain ⟨C, _, hC⟩ := exists_iter_chartRd_le hball hB hrr (b c) n
          exact ⟨C, fun S y hy => hC S n le_rfl y hy⟩) w
      exact ⟨C, fun S n hn y hy => hC n hn S y hy⟩)
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_const_forall_le
    (P := fun i C => ∀ S : SmoothCcTensor g 0 b', ∀ y ∈ Metric.closedBall c₀ (r₀ / 2),
      ‖chartRd g α (iteratedCovGrad g 0 b' i S) y‖ ≤
        C * ∑ m ∈ Finset.range (i + 1), ‖iteratedFDeriv ℝ m (chartRd g α S) y‖)
    (fun i C C' h H S y hy => (H S y hy).trans
      (mul_le_mul_of_nonneg_right h (Finset.sum_nonneg fun _ _ => norm_nonneg _)))
    (fun i => by
      obtain ⟨C, _, hC⟩ := exists_chartRd_iter_le hball hB hrr b' i
      exact ⟨C, hC⟩) w
  set R' := C₂ * Real.sqrt Ctw * (Fintype.card ι * ((w : ℝ) + 1) * Real.sqrt (max R 0)) with hR'def
  have hR'0 : 0 ≤ R' := by positivity
  obtain ⟨CF, hCF0, hCF⟩ := exists_const_forall_le
    (P := fun n C => ∀ (u : ℝ × E → ProdModel E b) (s : Set (ℝ × E)), UniqueDiffOn ℝ s →
      ContDiffOn ℝ n u s → MapsTo (fun x => (x, u x)) s tα → ∀ z ∈ s, (z, u z) ∈ K →
      ∀ v : Fin n → ℝ × E, (∀ i, ‖v i‖ ≤ 1) → ∀ wt : Fin n → ℕ,
      (∀ Bs : Finset (Fin n), Bs.Nonempty → 2 * ∑ i ∈ Bs, wt i ≤ ∑ i, wt i →
        ‖FaaDiBruno.blockDeriv u s z v Bs‖ ≤ R') →
      ‖iteratedFDerivWithin ℝ n (fun x => Φ.euclRep lam α (x, u x)) s z v‖ ≤
        C * (1 + ∑ Bs ∈ Finset.univ.filter (fun Bs : Finset (Fin n) => Bs.Nonempty),
          ‖FaaDiBruno.blockDeriv u s z v Bs‖))
    (fun n C C' h H u s h1 h2 h3 z hz hzK v hv wt hsm => (H u s h1 h2 h3 z hz hzK v hv wt hsm).trans
      (mul_le_mul_of_nonneg_right h (by positivity)))
    (fun n => by
      obtain ⟨C, _, hC⟩ := FaaDiBruno.exists_tame_bound_graph
        (hsmooth.of_le (JetRec.natCast_le_infty n)) htα hK hKt hR'0
      exact ⟨C, hC⟩) w
  refine ⟨tameConst Cfrm C₁ C₂ Ctw CF (∑ k, ‖cB E k‖) w (Module.finrank ℝ E) (Fintype.card ι),
    tameConst_nonneg _ _ _ hCfrm0, fun V hV hVδ hdom hR j i hji t ht y hy => ?_⟩
  exact core_bound Φ lam hT hTT hball_r hB_r hp hKt hC₂0 hCtw0 hC₁0 hCfrm0 hCF0
    (fun c S n hn y hy => hC₂ c S n hn y hy) hTw (fun i hi S y hy => hC₁ i hi S y hy)
    hfrb hCF le_rfl hV hdom hR
    (fun q hq => htube V hVδ q ⟨hq.1, Metric.ball_subset_closedBall hq.2⟩) hji ht hy

end Patch

/-! ### The pointwise tame bound -/

section Main

variable {g : SmoothRiemannianMetric I M}

/-- **The pointwise tame bound** (Step 3 of `prop:nemytskii`). Near a smooth reference tuple `W`
with values in the domain, if the jets of `V` of weight `2pj + i` at most `w/2` are bounded by `R`,
then every jet of `Φ[λ, V]` of weight at most `w` is bounded by the jets of `V` of lower order,
linearly. Moreover the tube `|V - W| ≤ δ` lies in the domain. -/
theorem exists_tame_pointwise (Φ : FibreMap I M Λ b b') (lam : Λ) {T : ℝ} (hT : 0 < T)
    (hTT : T ≤ Φ.T₀) {W : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)}
    (hW : ∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (W c))
    (hWdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, valAt (fun c => W c t) x ∈ Φ.dom lam t x)
    {p : ℕ} (hp : 0 < p) (w : ℕ) :
    ∃ δ > 0, (∀ V : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c),
        (∀ c, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 0 (b c) x ((V c t - W c t).toSection x) ≤ δ) →
        ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, valAt (fun c => V c t) x ∈ Φ.dom lam t x) ∧
      ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ V : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c), (∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (V c)) →
        (∀ c, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 0 (b c) x ((V c t - W c t).toSection x) ≤ δ) →
        (∀ c j i, 2 * (2 * p * j + i) ≤ w → ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
          jetSq g T (V c) j i t x ≤ R) →
        ∀ j i, 2 * p * j + i ≤ w → ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
          jetSq g T (Φ.apply lam V) j i t x ≤
            C * (1 + ∑ c, ∑ j' ∈ Finset.range (j + 1), ∑ i' ∈ Finset.range (i + 1),
              jetSq g T (V c) j' i' t x) := by
  classical
  have hpatch := fun α => Φ.patch_tame lam hT hTT hW hWdom hp w α
  choose r hr δ hδ hdomP hbound using hpatch
  set O : M → Set M := fun α =>
    (extChartAt I α).source ∩ extChartAt I α ⁻¹' Metric.ball (extChartAt I α α) (r α) with hOdef
  have hO : ∀ α, IsOpen (O α) := fun α => isOpen_extChartAt_preimage' α Metric.isOpen_ball
  have hαO : ∀ α, α ∈ O α := fun α => ⟨mem_extChartAt_source α, Metric.mem_ball_self (hr α)⟩
  obtain ⟨A, hA⟩ := isCompact_univ.elim_finite_subcover O hO
    (fun x _ => mem_iUnion.2 ⟨x, hαO x⟩)
  have hcov : ∀ x : M, ∃ α ∈ A, x ∈ O α := fun x => by
    have := hA (mem_univ x)
    simp only [mem_iUnion] at this
    obtain ⟨α, hα, hx⟩ := this
    exact ⟨α, hα, hx⟩
  set δ₀ := (1 + ∑ α ∈ A, (δ α)⁻¹)⁻¹ with hδ₀def
  have hS0 : 0 ≤ ∑ α ∈ A, (δ α)⁻¹ := Finset.sum_nonneg fun α _ => (inv_pos.2 (hδ α)).le
  have hδ₀ : 0 < δ₀ := by positivity
  have hδ₀le : ∀ α ∈ A, δ₀ ≤ δ α := by
    intro α hα
    have h1 : (δ α)⁻¹ ≤ 1 + ∑ α ∈ A, (δ α)⁻¹ := by
      have := Finset.single_le_sum (f := fun α => (δ α)⁻¹) (fun α _ => (inv_pos.2 (hδ α)).le) hα
      linarith
    calc δ₀ = (1 + ∑ α ∈ A, (δ α)⁻¹)⁻¹ := rfl
      _ ≤ ((δ α)⁻¹)⁻¹ := inv_anti₀ (inv_pos.2 (hδ α)) h1
      _ = δ α := inv_inv _
  have hleft : ∀ α, ∀ x ∈ O α, (extChartAt I α).symm (extChartAt I α x) = x := fun α x hx =>
    (extChartAt I α).left_inv hx.1
  have hdomall : ∀ V : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c),
      (∀ c, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 0 (b c) x ((V c t - W c t).toSection x) ≤ δ₀) →
      ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, valAt (fun c => V c t) x ∈ Φ.dom lam t x := by
    intro V hVδ t ht x
    obtain ⟨α, hα, hx⟩ := hcov x
    have h := hdomP α V (fun c t ht x => (hVδ c t ht x).trans (hδ₀le α hα)) t ht
      (extChartAt I α x) (Metric.ball_subset_closedBall hx.2)
    rwa [hleft α x hx] at h
  refine ⟨δ₀, hδ₀, hdomall, fun R => ?_⟩
  choose C hC0 hC using fun α => hbound α R
  refine ⟨∑ α ∈ A, C α, Finset.sum_nonneg fun α _ => hC0 α,
    fun V hV hVδ hR j i hji t ht x => ?_⟩
  obtain ⟨α, hα, hx⟩ := hcov x
  have h := hC α V hV (fun c t ht x => (hVδ c t ht x).trans (hδ₀le α hα)) (hdomall V hVδ) hR
    j i hji t ht (extChartAt I α x) hx.2
  rw [hleft α x hx] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · exact Finset.single_le_sum (f := C) (fun α _ => hC0 α) hα
  · have : 0 ≤ ∑ c, ∑ j' ∈ Finset.range (j + 1), ∑ i' ∈ Finset.range (i + 1),
        jetSq g T (V c) j' i' t x :=
      Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 _ _ _
    linarith

end Main

end FibreMap

end ShortTime
