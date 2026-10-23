import ShortTime.Linear.LegendreGeneral
import ShortTime.Linear.Interp

/-!
# Gårding's inequality for operators of any order (`lem:garding`)

For `L ∈ 𝓛` of order `2p` with Legendre constant `λ`,

  `⟨u, L(t) u⟩ + λ/2 ‖∇^p u‖² ≤ C ‖u‖²`                              (`LinearOp.garding_top`)

and hence the inequality of the paper, `-⟨u, L(t) u⟩ ≥ λ/4 ‖u‖²_{H^p} - C ‖u‖²`
(`LinearOp.garding`). The proof follows the paper:

* the terms `⟨u, A_k ∇^k u⟩` with `k < 2p` are balanced pairings, bounded by `C N_p N_{p-1}`
  (`exists_bound_pairing`);
* the principal term is integrated by parts `p` times (`principal_iter`), giving
  `(-1)^p ⟨∇^p u, P^{(p)} ∇^p u⟩`. Pointwise, `⟨ρξ, P^{(p)} ξ⟩` is the Legendre form `B_P(ξ, ξ)`,
  where `ρ` reverses the first `p` slots (`legendreForm_eq_integrand`), and replacing `ρ∇^p u` by
  `∇^p u` costs `C ‖∇^p u‖ N_{p-2}` by the Ricci identity (`exists_perm_bound`). Together:
  `⟨u, P ∇^{2p} u⟩ = (-1)^p ∫ B_P(∇^p u, ∇^p u) + E(u)` (`principal_ibp`), and the Legendre
  condition makes the main term coercive (`LinearOp.coercive`);
* interpolation (`exists_jetSum_pred_le`) absorbs `C N_p N_{p-1}` into `λ/2 ‖∇^p u‖² + C' ‖u‖²`.

Gårding's inequality gives the energy bound `⟨u, L u⟩ ≤ C ‖u‖²`, hence uniqueness for parabolic
operators of every order (`LinearOp.unique_of_isParabolic`).
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Spectral DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Elliptic DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff BigOperators

namespace ShortTime

/-! ### Absorbing the cross terms (real arithmetic) -/

/-- `C (y + a) y ≤ λ/2 a² + C' b²` when `y ≤ δ a + D b` and `δ` is small. -/
theorem absorb_aux {lam C₂ D δ a b y : ℝ} (hC₂ : 0 ≤ C₂) (hD : 0 ≤ D) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) (hδ : 8 * C₂ * δ ≤ lam) (ha : 0 ≤ a) (hb : 0 ≤ b) (hy0 : 0 ≤ y)
    (hy : y ≤ δ * a + D * b) :
    C₂ * ((y + a) * y) ≤ lam / 2 * a ^ 2 + C₂ * (2 * D ^ 2 + D ^ 2 / (4 * δ)) * b ^ 2 := by
  have hq0 : 0 ≤ δ * a + D * b := by positivity
  have h1 : (y + a) * y ≤ (δ * a + D * b + a) * (δ * a + D * b) := by nlinarith
  have h3 : D * a * b ≤ δ * a ^ 2 + D ^ 2 / (4 * δ) * b ^ 2 := by
    have hnn : 0 ≤ (2 * δ * a - D * b) ^ 2 / (4 * δ) := by positivity
    have e : (2 * δ * a - D * b) ^ 2 / (4 * δ) =
        δ * a ^ 2 - D * a * b + D ^ 2 / (4 * δ) * b ^ 2 := by
      field_simp
      ring
    linarith
  have h4 : (δ * a + D * b + a) * (δ * a + D * b) ≤
      (2 * δ ^ 2 + 2 * δ) * a ^ 2 + (2 * D ^ 2 + D ^ 2 / (4 * δ)) * b ^ 2 := by
    nlinarith [sq_nonneg (δ * a - D * b)]
  have hδ2 : δ ^ 2 ≤ δ := by nlinarith
  have h5 : C₂ * (2 * δ ^ 2 + 2 * δ) ≤ lam / 2 := by nlinarith
  calc C₂ * ((y + a) * y) ≤ C₂ * ((δ * a + D * b + a) * (δ * a + D * b)) :=
        mul_le_mul_of_nonneg_left h1 hC₂
    _ ≤ C₂ * ((2 * δ ^ 2 + 2 * δ) * a ^ 2 + (2 * D ^ 2 + D ^ 2 / (4 * δ)) * b ^ 2) :=
        mul_le_mul_of_nonneg_left h4 hC₂
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right h5 (sq_nonneg a)]

/-- The bookkeeping of `principal_ibp`: replacing `ρ∇^p u` by `∇^p u` costs
`√K C_R N_{p-2} ‖∇^p u‖`. -/
theorem ibp_combine {I J Jρ Jd σ r a N N' N'' C₁ K CR : ℝ} (hJ : J = Jρ - Jd)
    (h1 : |I - σ * J| ≤ C₁ * N * N') (hσ : |σ| = 1) (h2 : |Jd| ≤ Real.sqrt K * r * a)
    (h3 : r ≤ CR * N'') (hN'' : N'' ≤ N') (haN : a ≤ N) (ha : 0 ≤ a) (hN'0 : 0 ≤ N')
    (hCR : 0 ≤ CR) :
    |I - σ * Jρ| ≤ (C₁ + Real.sqrt K * CR) * N * N' := by
  have hsK := Real.sqrt_nonneg K
  have e4 : Real.sqrt K * r * a ≤ Real.sqrt K * CR * N * N' := by
    have hr' : r ≤ CR * N' := h3.trans (mul_le_mul_of_nonneg_left hN'' hCR)
    have := mul_le_mul hr' haN ha (mul_nonneg hCR hN'0)
    calc Real.sqrt K * r * a = Real.sqrt K * (r * a) := by ring
      _ ≤ Real.sqrt K * (CR * N' * N) := mul_le_mul_of_nonneg_left this hsK
      _ = _ := by ring
  have h : I - σ * Jρ = (I - σ * J) - σ * Jd := by rw [hJ]; ring
  rw [h]
  calc |(I - σ * J) - σ * Jd| ≤ |I - σ * J| + |σ * Jd| := abs_sub _ _
    _ = |I - σ * J| + |Jd| := by rw [abs_mul, hσ, one_mul]
    _ ≤ C₁ * N * N' + Real.sqrt K * CR * N * N' := by linarith
    _ = _ := by ring

/-- The bookkeeping of Gårding's inequality: lower-order terms, the principal term and the
Legendre condition, then absorption. -/
theorem garding_combine {IL Slow Itop B a b N N' Cs C₁ lam D δ σ : ℝ}
    (hsplit : IL = Slow + Itop) (hlow : |Slow| ≤ Cs * N * N')
    (hprin : |Itop - σ * B| ≤ C₁ * N * N') (hcoer : σ * B ≤ -lam * a ^ 2)
    (hNN : N ≤ N' + a) (hN' : N' ≤ δ * a + D * b)
    (hCs : 0 ≤ Cs) (hC₁ : 0 ≤ C₁) (hD : 0 ≤ D) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hδ : 8 * (Cs + C₁) * δ ≤ lam) (ha : 0 ≤ a) (hb : 0 ≤ b) (hN'0 : 0 ≤ N') :
    IL + lam / 2 * a ^ 2 ≤ (Cs + C₁) * (2 * D ^ 2 + D ^ 2 / (4 * δ)) * b ^ 2 := by
  have hC₂0 : 0 ≤ Cs + C₁ := by positivity
  have e1 := (abs_le.mp hlow).2
  have e2 := (abs_le.mp hprin).2
  have h1 : IL ≤ (Cs + C₁) * (N * N') - lam * a ^ 2 := by
    rw [hsplit]
    nlinarith
  have h2 : (Cs + C₁) * (N * N') ≤ (Cs + C₁) * ((N' + a) * N') :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hNN hN'0) hC₂0
  have h3 := absorb_aux hC₂0 hD hδ0 hδ1 hδ ha hb hN'0 hN'
  linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

variable {g : SmoothRiemannianMetric I M}

/-! ### Interpolation, summed over the lower jets -/

theorem jetSum_le_pred_add (s p : ℕ) (u : SmoothCcTensor g 0 s) :
    jetSum g s p u ≤ jetSum g s (p - 1) u + jetNorm g s p u := by
  rcases p with _ | p
  · rw [Nat.zero_sub]
    linarith [jetNorm_nonneg g s 0 u]
  · refine le_of_eq ?_
    rw [Nat.add_sub_cancel, jetSum, jetSum, Finset.sum_range_succ _ (p + 1)]

/-- `N_{p-1}(u) ≤ ε ‖∇^p u‖ + C ‖u‖`. -/
theorem exists_jetSum_pred_le (s p : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SmoothCcTensor g 0 s,
      jetSum g s (p - 1) u ≤ ε * jetNorm g s p u + C * jetNorm g s 0 u := by
  have hi : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SmoothCcTensor g 0 s, i < p →
      jetNorm g s i u ≤ ε / p * jetNorm g s p u + C * jetNorm g s 0 u := by
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · refine ⟨1, zero_le_one, fun u _ => ?_⟩
      have : 0 ≤ ε / p * jetNorm g s p u :=
        mul_nonneg (div_nonneg hε.le (Nat.cast_nonneg _)) (jetNorm_nonneg g s p u)
      linarith
    · by_cases hip : i < p
      · have hp : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
        obtain ⟨C, hC0, hC⟩ := jetNorm_le_interp g s i p hi0 hip (div_pos hε hp)
        exact ⟨C, hC0, fun u _ => hC u⟩
      · exact ⟨0, le_rfl, fun u h => absurd h hip⟩
  choose C hC0 hC using hi
  have hCs : 0 ≤ ∑ i ∈ Finset.range p, C i := Finset.sum_nonneg fun i _ => hC0 i
  refine ⟨1 + ∑ i ∈ Finset.range p, C i, by linarith, fun u => ?_⟩
  have hb := jetNorm_nonneg g s 0 u
  have ha := jetNorm_nonneg g s p u
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have h0 : jetSum g s (0 - 1) u = jetNorm g s 0 u := by simp [jetSum]
    rw [h0]
    nlinarith [mul_nonneg hε.le hb, mul_nonneg hCs hb]
  · have hsum : jetSum g s (p - 1) u = ∑ i ∈ Finset.range p, jetNorm g s i u := by
      rw [jetSum, Nat.sub_add_cancel hp]
    have hp' : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [hsum]
    calc ∑ i ∈ Finset.range p, jetNorm g s i u
        ≤ ∑ i ∈ Finset.range p, (ε / p * jetNorm g s p u + C i * jetNorm g s 0 u) :=
          Finset.sum_le_sum fun i hi => hC i u (Finset.mem_range.mp hi)
      _ = ε * jetNorm g s p u + (∑ i ∈ Finset.range p, C i) * jetNorm g s 0 u := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            ← Finset.sum_mul]
          congr 1
          field_simp
      _ ≤ _ := by
          rw [add_mul (1 : ℝ), one_mul]
          linarith

/-- `‖u‖²_{H^p} ≤ 2 ‖∇^p u‖² + C ‖u‖²`. -/
theorem exists_sobolevNormSq_le (s p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SmoothCcTensor g 0 s,
      sobolevNormSq g 0 s p u ≤ 2 * jetNorm g s p u ^ 2 + C * jetNorm g s 0 u ^ 2 := by
  have hi : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SmoothCcTensor g 0 s, i < p →
      jetNorm g s i u ^ 2 ≤ 1 / p * jetNorm g s p u ^ 2 + C * jetNorm g s 0 u ^ 2 := by
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · refine ⟨1, zero_le_one, fun u _ => ?_⟩
      have : 0 ≤ 1 / (p : ℝ) * jetNorm g s p u ^ 2 := by positivity
      linarith
    · by_cases hip : i < p
      · have hp : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
        have hp0 : (0 : ℝ) < p := by linarith
        obtain ⟨C, hC0, hC⟩ := jetNorm_le_interp g s i p hi0 hip (ε := 1 / (2 * p))
          (by positivity)
        refine ⟨2 * C ^ 2, by positivity, fun u _ => ?_⟩
        have ha := jetNorm_nonneg g s p u
        have hb := jetNorm_nonneg g s 0 u
        have h1 : jetNorm g s i u ^ 2 ≤
            (1 / (2 * p) * jetNorm g s p u + C * jetNorm g s 0 u) ^ 2 :=
          pow_le_pow_left₀ (jetNorm_nonneg g s i u) (hC u) 2
        have h2 : (1 / (2 * p) * jetNorm g s p u + C * jetNorm g s 0 u) ^ 2 ≤
            2 * (1 / (2 * p)) ^ 2 * jetNorm g s p u ^ 2 + 2 * C ^ 2 * jetNorm g s 0 u ^ 2 := by
          nlinarith [sq_nonneg (1 / (2 * p) * jetNorm g s p u - C * jetNorm g s 0 u)]
        have h3 : 2 * (1 / (2 * (p : ℝ))) ^ 2 ≤ 1 / p := by
          have e : 2 * (1 / (2 * (p : ℝ))) ^ 2 = 1 / (2 * p ^ 2) := by
            field_simp
          rw [e]
          exact one_div_le_one_div_of_le hp0 (by nlinarith)
        nlinarith [mul_le_mul_of_nonneg_right h3 (sq_nonneg (jetNorm g s p u))]
      · exact ⟨0, le_rfl, fun u h => absurd h hip⟩
  choose C hC0 hC using hi
  have hCs : 0 ≤ ∑ i ∈ Finset.range p, C i := Finset.sum_nonneg fun i _ => hC0 i
  refine ⟨∑ i ∈ Finset.range p, C i, hCs, fun u => ?_⟩
  have ha := sq_nonneg (jetNorm g s p u)
  have hb := sq_nonneg (jetNorm g s 0 u)
  have hsplit : sobolevNormSq g 0 s p u =
      ∑ i ∈ Finset.range p, jetNorm g s i u ^ 2 + jetNorm g s p u ^ 2 := by
    rw [sobolevNormSq, Finset.sum_range_succ]
  have hpp : (p : ℝ) * (1 / p) ≤ 1 := by
    rcases Nat.eq_zero_or_pos p with h | h
    · simp [h]
    · rw [mul_one_div_cancel (Nat.cast_ne_zero.mpr (by omega))]
  rw [hsplit]
  calc ∑ i ∈ Finset.range p, jetNorm g s i u ^ 2 + jetNorm g s p u ^ 2
      ≤ ∑ i ∈ Finset.range p, (1 / p * jetNorm g s p u ^ 2 + C i * jetNorm g s 0 u ^ 2) +
          jetNorm g s p u ^ 2 := by
        gcongr with i hi
        exact hC i u (Finset.mem_range.mp hi)
    _ = (p : ℝ) * (1 / p) * jetNorm g s p u ^ 2 +
          (∑ i ∈ Finset.range p, C i) * jetNorm g s 0 u ^ 2 + jetNorm g s p u ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ← Finset.sum_mul, mul_assoc]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hpp ha]

/-- `‖u‖²_{H^{k-1}} ≤ ε ‖u‖²_{H^k} + C ‖u‖²`. -/
theorem exists_sobolevNormSq_pred_le (s k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SmoothCcTensor g 0 s,
      sobolevNormSq g 0 s (k - 1) u ≤ ε * sobolevNormSq g 0 s k u + C * jetNorm g s 0 u ^ 2 := by
  have hm0 : 0 < min 1 ε := lt_min one_pos hε
  have hm1 : min 1 ε ≤ 1 := min_le_left _ _
  have hmε : min 1 ε ≤ ε := min_le_right _ _
  have hδ0 : 0 < min 1 ε / 2 := by positivity
  have hδε : 2 * (min 1 ε / 2) ^ 2 ≤ ε := by nlinarith
  obtain ⟨D, hD0, hD⟩ := exists_jetSum_pred_le (g := g) s k hδ0
  refine ⟨2 * D ^ 2, by positivity, fun u => ?_⟩
  have hN0 := jetSum_nonneg s (k - 1) u
  have h1 : sobolevNormSq g 0 s (k - 1) u ≤ jetSum g s (k - 1) u ^ 2 := by
    unfold sobolevNormSq
    calc ∑ i ∈ Finset.range (k - 1 + 1), jetNorm g s i u ^ 2
        ≤ ∑ i ∈ Finset.range (k - 1 + 1), jetNorm g s i u * jetSum g s (k - 1) u :=
          Finset.sum_le_sum fun i hi => by
            rw [sq]
            exact mul_le_mul_of_nonneg_left
              (jetNorm_le_jetSum s (k - 1) i (by simp at hi; omega) u) (jetNorm_nonneg g s i u)
      _ = jetSum g s (k - 1) u ^ 2 := by
          rw [← Finset.sum_mul, sq]
          rfl
  have h2 : jetNorm g s k u ^ 2 ≤ sobolevNormSq g 0 s k u := by
    unfold sobolevNormSq
    exact Finset.single_le_sum (f := fun i => jetNorm g s i u ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_range.mpr (by omega))
  have h3 : jetSum g s (k - 1) u ^ 2 ≤
      2 * (min 1 ε / 2) ^ 2 * jetNorm g s k u ^ 2 + 2 * D ^ 2 * jetNorm g s 0 u ^ 2 := by
    have := pow_le_pow_left₀ hN0 (hD u) 2
    nlinarith [sq_nonneg (min 1 ε / 2 * jetNorm g s k u - D * jetNorm g s 0 u)]
  nlinarith [mul_le_mul_of_nonneg_right hδε (sq_nonneg (jetNorm g s k u)),
    mul_le_mul_of_nonneg_left h2 hε.le]

/-! ### Inner-product bookkeeping -/

theorem tensorL2Inner_eq_sub {a : ℕ} (A B X : SmoothCcTensor g 0 a) :
    tensorL2Inner (I := I) (M := M) g 0 a B.toFun X.toFun =
      tensorL2Inner (I := I) (M := M) g 0 a A.toFun X.toFun -
        tensorL2Inner (I := I) (M := M) g 0 a (A - B).toFun X.toFun := by
  change inner ℝ B X = inner ℝ A X - inner ℝ (A - B) X
  rw [inner_sub_left]
  ring

variable [CompleteSpace E]

/-! ### The principal term (`lem:ibp`) -/

section Principal

variable {s p : ℕ} {T : ℝ}

/-- Pointwise, the Legendre form `B_P(Ψ, Ψ)` is the integrand of `⟨ρΨ, P^{(p)} Ψ⟩`, where `ρ`
reverses the first `p` slots. -/
theorem legendreForm_eq_integrand (P : SmoothCcTensor g (s + 2 * p) s)
    (Ψ : SmoothCcTensor g 0 (s + p)) :
    (fun x => legendreForm g 0 s p x
        ((opFieldHom (P.toSection x)).comp
          (EquationData.castIdx (r := 0) (by omega : s + p + p = s + 2 * p) x).toContinuousLinearMap)
        (Ψ.toSection x) (Ψ.toSection x)) =
      fun x => tensorInnerPointwise (I := I) (M := M) g 0 (s + p) x
        ((domDomCongrSection (I := I) g (extPerm s p Fin.revPerm) Ψ).toFun x)
        ((operatorFieldApply (I := I) (M := M) g (s + p) (s + p)
          (flipIter g s p p p (by omega) P) Ψ).toFun x) := by
  funext x
  rw [legendreForm_eq_fiberInner_flipIter g s p x P _ _ _ _
    (fun w => evalFirst_rev_domDomCongrSection g Ψ x w)]
  rfl

/-- **Integration by parts in the principal term** (`lem:ibp`):
`⟨u, P ∇^{2p} u⟩ = (-1)^p ∫ B_P(∇^p u, ∇^p u) + E(u)` with `|E(u)| ≤ C N_p(u) N_{p-1}(u)`,
uniformly for `t ∈ [0, T]`. Here `B_P(ξ, ξ) = ⟨ξ, P̂ ξ⟩` is the Legendre form (`def:legendre`). -/
theorem principal_ibp {P : ℝ → SmoothCcTensor g (s + 2 * p) s}
    (hP : JointlySmoothOn g (s + 2 * p) s (Icc 0 T) P) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ u : SmoothCcTensor g 0 s,
      |tensorL2Inner (I := I) (M := M) g 0 s u.toFun
          (operatorFieldApply (I := I) (M := M) g (s + 2 * p) s (P t)
            (iteratedCovGrad g 0 s (2 * p) u)).toFun -
        (-1) ^ p * ∫ x, legendreForm g 0 s p x
            ((opFieldHom ((P t).toSection x)).comp
              (EquationData.castIdx (r := 0) (by omega : s + p + p = s + 2 * p) x).toContinuousLinearMap)
            ((iteratedCovGrad g 0 s p u).toSection x) ((iteratedCovGrad g 0 s p u).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)| ≤
        C * jetSum g s p u * jetSum g s (p - 1) u := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := principal_iter (g := g) hP p le_rfl p (by omega)
  obtain ⟨CR, hCR0, hCR⟩ := exists_perm_bound (g := g) s p Fin.revPerm
  obtain ⟨K, hK0, hK⟩ := exists_bound_of_jointlySmoothOn
    (jointlySmoothOn_flipIter g s p hP p p (by omega))
  refine ⟨C₁ + Real.sqrt K * CR, by positivity, fun t ht u => ?_⟩
  set Ψ := iteratedCovGrad g 0 s p u with hΨ
  have hint : ∫ x, legendreForm g 0 s p x
        ((opFieldHom ((P t).toSection x)).comp
          (EquationData.castIdx (r := 0) (by omega : s + p + p = s + 2 * p) x).toContinuousLinearMap)
        (Ψ.toSection x) (Ψ.toSection x) ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      tensorL2Inner (I := I) (M := M) g 0 (s + p)
        (domDomCongrSection (I := I) g (extPerm s p Fin.revPerm) Ψ).toFun
        (operatorFieldApply (I := I) (M := M) g (s + p) (s + p)
          (flipIter g s p p p (by omega) (P t)) Ψ).toFun := by
    rw [legendreForm_eq_integrand (P t) Ψ]
    rfl
  rw [hint]
  exact ibp_combine
    (tensorL2Inner_eq_sub (domDomCongrSection (I := I) g (extPerm s p Fin.revPerm) Ψ) Ψ _)
    (hC₁ t ht u) (by simp)
    (abs_inner_operatorFieldApply_le g (s + p) (s + p) _ hK0 (hK t ht) _ _) (hCR u)
    (jetSum_mono s (by omega) u) (jetNorm_le_jetSum s p p le_rfl u) (jetNorm_nonneg g s p u)
    (jetSum_nonneg s (p - 1) u) hCR0

end Principal

namespace LinearOp

variable {s p : ℕ} {T : ℝ} (L : LinearOp g s p T)

/-- The top-order coefficient `A_{2p}(t)`, with its rank written `s + 2p`. -/
abbrev topCoeff (t : ℝ) : SmoothCcTensor g (s + 2 * p) s := L.coeff (Fin.last (2 * p)) t

theorem smooth_topCoeff : JointlySmoothOn g (s + 2 * p) s (Icc 0 T) L.topCoeff :=
  L.smooth (Fin.last (2 * p))

/-- `⟨u, L u⟩ = Σ_{k < 2p} ⟨u, A_k ∇^k u⟩ + ⟨u, A_{2p} ∇^{2p} u⟩`. -/
theorem inner_apply_split (t : ℝ) (u : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 s u.toFun (L.apply t u).toFun =
      ∑ k : Fin (2 * p), tensorL2Inner (I := I) (M := M) g 0 s u.toFun
          (operatorFieldApply (I := I) (M := M) g (s + k) s (L.coeff k.castSucc t)
            (iteratedCovGrad g 0 s k u)).toFun +
        tensorL2Inner (I := I) (M := M) g 0 s u.toFun
          (operatorFieldApply (I := I) (M := M) g (s + 2 * p) s (L.topCoeff t)
            (iteratedCovGrad g 0 s (2 * p) u)).toFun := by
  have e : ∀ X : SmoothCcTensor g 0 s,
      tensorL2Inner (I := I) (M := M) g 0 s u.toFun X.toFun = inner ℝ u X := fun X => rfl
  rw [e, LinearOp.apply, inner_sum, Fin.sum_univ_castSucc]
  rfl

/-- **The Legendre condition, integrated.** `(-1)^p ∫ B_P(∇^p u, ∇^p u) ≤ -λ ‖∇^p u‖²`. -/
theorem coercive {lam : ℝ} (hL : L.IsParabolic lam) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (u : SmoothCcTensor g 0 s) :
    (-1) ^ p * ∫ x, legendreForm g 0 s p x
        ((opFieldHom ((L.topCoeff t).toSection x)).comp
          (EquationData.castIdx (r := 0) (by omega : s + p + p = s + 2 * p) x).toContinuousLinearMap)
        ((iteratedCovGrad g 0 s p u).toSection x) ((iteratedCovGrad g 0 s p u).toSection x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
    -lam * jetNorm g s p u ^ 2 := by
  set Ψ := iteratedCovGrad g 0 s p u with hΨ
  have hint : Integrable (fun x => legendreForm g 0 s p x
        ((opFieldHom ((L.topCoeff t).toSection x)).comp
          (EquationData.castIdx (r := 0) (by omega : s + p + p = s + 2 * p) x).toContinuousLinearMap)
        (Ψ.toSection x) (Ψ.toSection x)) (riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [legendreForm_eq_integrand]
    exact SmoothCcTensor.integrable_inner_cross _ _
  show _ ≤ -lam * tensorL2Norm (I := I) (M := M) g 0 (s + p) Ψ.toFun ^ 2
  rw [← tensorL2Inner_self_eq_sq_norm, ← integral_const_mul]
  unfold tensorL2Inner
  rw [← integral_const_mul]
  refine integral_mono (hint.const_mul _)
    ((SmoothCcTensor.integrable_inner_cross _ _).const_mul _) fun x => ?_
  have hx : lam * tensorInnerPointwise (I := I) (M := M) g 0 (s + p) x (Ψ.toFun x) (Ψ.toFun x) ≤
      (-1) ^ (p + 1) * legendreForm g 0 s p x
        ((opFieldHom ((L.topCoeff t).toSection x)).comp
          (EquationData.castIdx (r := 0) (by omega : s + p + p = s + 2 * p) x).toContinuousLinearMap)
        (Ψ.toSection x) (Ψ.toSection x) :=
    (hL.2 t ht x).2 (Ψ.toSection x)
  rw [pow_succ] at hx
  linarith

/-- **Gårding's inequality, top-order form.** `⟨u, L(t) u⟩ + λ/2 ‖∇^p u‖² ≤ C ‖u‖²`. -/
theorem garding_top {lam : ℝ} (hL : L.IsParabolic lam) :
    ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) T, ∀ u : SmoothCcTensor g 0 s,
      tensorL2Inner (I := I) (M := M) g 0 s u.toFun (L.apply t u).toFun +
          lam / 2 * jetNorm g s p u ^ 2 ≤ C * jetNorm g s 0 u ^ 2 := by
  have hlam := hL.1
  -- the terms of order `k < 2p` are balanced pairings
  have hlow : ∀ k : Fin (2 * p), ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) T,
      ∀ u : SmoothCcTensor g 0 s,
        |tensorL2Inner (I := I) (M := M) g 0 s u.toFun
            (operatorFieldApply (I := I) (M := M) g (s + k) s (L.coeff k.castSucc t)
              (iteratedCovGrad g 0 s k u)).toFun| ≤
          C * jetSum g s p u * jetSum g s (p - 1) u :=
    fun k => exists_bound_pairing (g := g) (s := s) (p := p) (T := T) k 0 (Nat.zero_le _)
      (by have := k.isLt; omega) (fun t => L.coeff k.castSucc t) (L.smooth k.castSucc)
  choose Cl hCl0 hCl using hlow
  have hlowb : ∀ t ∈ Icc (0 : ℝ) T, ∀ u : SmoothCcTensor g 0 s,
      |∑ k : Fin (2 * p), tensorL2Inner (I := I) (M := M) g 0 s u.toFun
          (operatorFieldApply (I := I) (M := M) g (s + k) s (L.coeff k.castSucc t)
            (iteratedCovGrad g 0 s k u)).toFun| ≤
        (∑ k, Cl k) * jetSum g s p u * jetSum g s (p - 1) u := by
    intro t ht u
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_le_sum fun k _ => hCl k t ht u
  have hCs : 0 ≤ ∑ k, Cl k := Finset.sum_nonneg fun k _ => hCl0 k
  -- the principal term
  obtain ⟨C₁, hC₁0, hC₁⟩ := principal_ibp (g := g) L.smooth_topCoeff
  -- interpolation, with `δ` small enough to absorb
  set δ : ℝ := min 1 (lam / (8 * (∑ k, Cl k + C₁) + 1)) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (div_pos hlam (by linarith))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδl : 8 * (∑ k, Cl k + C₁) * δ ≤ lam := by
    have h : δ ≤ lam / (8 * (∑ k, Cl k + C₁) + 1) := min_le_right _ _
    rw [le_div_iff₀ (by linarith)] at h
    nlinarith
  obtain ⟨D, hD0, hD⟩ := exists_jetSum_pred_le (g := g) s p hδ0
  refine ⟨(∑ k, Cl k + C₁) * (2 * D ^ 2 + D ^ 2 / (4 * δ)), fun t ht u => ?_⟩
  exact garding_combine (L.inner_apply_split t u) (hlowb t ht u) (hC₁ t ht u)
    (L.coercive hL ht u) (jetSum_le_pred_add s p u) (hD u) hCs hC₁0 hD0 hδ0 hδ1 hδl
    (jetNorm_nonneg g s p u) (jetNorm_nonneg g s 0 u) (jetSum_nonneg s (p - 1) u)

/-- **Gårding's inequality** (`lem:garding`): `-⟨u, L(t) u⟩ ≥ λ/4 ‖u‖²_{H^p} - C ‖u‖²`. -/
theorem garding {lam : ℝ} (hL : L.IsParabolic lam) :
    ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) T, ∀ u : SmoothCcTensor g 0 s,
      lam / 4 * sobolevNormSq g 0 s p u - C * jetNorm g s 0 u ^ 2 ≤
        -tensorL2Inner (I := I) (M := M) g 0 s u.toFun (L.apply t u).toFun := by
  obtain ⟨C, hC⟩ := L.garding_top hL
  obtain ⟨C', -, hC'⟩ := exists_sobolevNormSq_le (g := g) s p
  refine ⟨C + lam / 4 * C', fun t ht u => ?_⟩
  have h1 := hC t ht u
  have h2 := mul_le_mul_of_nonneg_left (hC' u) (by linarith [hL.1] : (0 : ℝ) ≤ lam / 4)
  nlinarith

/-- Parabolic operators satisfy the energy bound `⟨u, L(t) u⟩ ≤ C ‖u‖²`. -/
theorem energy_bound {lam : ℝ} (hL : L.IsParabolic lam) :
    ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) T, ∀ u : SmoothCcTensor g 0 s,
      tensorL2Inner (I := I) (M := M) g 0 s u.toFun (L.apply t u).toFun ≤
        C * tensorL2Inner (I := I) (M := M) g 0 s u.toFun u.toFun := by
  obtain ⟨C, hC⟩ := L.garding_top hL
  refine ⟨C, fun t ht u => ?_⟩
  have h := hC t ht u
  have hb : jetNorm g s 0 u ^ 2 = tensorL2Inner (I := I) (M := M) g 0 s u.toFun u.toFun :=
    (tensorL2Inner_self_eq_sq_norm g s u).symm
  have hnn : 0 ≤ lam / 2 * jetNorm g s p u ^ 2 :=
    mul_nonneg (by linarith [hL.1]) (sq_nonneg _)
  rw [← hb]
  linarith

/-- **Uniqueness for linear parabolic systems of any order** (`thm:linear` (ii)): two smooth
solutions of `∂ₜu = L u + f` on `M × [0, T]` with the same initial value coincide. -/
theorem unique_of_isParabolic {lam : ℝ} (hL : L.IsParabolic lam)
    {u w f : ℝ → SmoothCcTensor g 0 s} (hu : JointlySmoothOn g 0 s (Icc 0 T) u)
    (hw : JointlySmoothOn g 0 s (Icc 0 T) w) (h0 : u 0 = w 0)
    (hsu : L.Solves u f) (hsw : L.Solves w f) :
    ∀ t ∈ Icc (0 : ℝ) T, u t = w t :=
  let ⟨_, hC⟩ := L.energy_bound hL
  L.unique_of_energy hC hu hw h0 hsu hsw

end LinearOp

end ShortTime
