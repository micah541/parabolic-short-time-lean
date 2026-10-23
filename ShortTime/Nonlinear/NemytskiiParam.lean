import ShortTime.Nonlinear.NemytskiiParamDef

/-!
# The parametric nonlinear operator (`cor:N`, jointly in `(λ, u)`)

Let `Φ(λ, t, x, ζ)` be a smooth fibre map on covariant `2p`-jets with a parameter `λ ∈ Λ`,
`Λ` finite dimensional (e.g. the flow parameters of Angenent's trick), `w` a smooth family on
`[0,T]` whose jets lie in the domain of `Φ(0, ·)`, and `m ≥ ⌊n/2p⌋ + 4`. Then
`(λ, u) ↦ Φ[λ, u] = Φ(λ, t, x, j^{2p} u)` extends from `Λ × {smooth families near w}` to a map
`𝒩 : Λ × 𝒫^m → 𝒫^{m-1}` which is `C^∞` at `(0, w)` (`FibreMap.exists_nonlinOp_param`).

*Proof.* `λ` becomes extra scalar inputs of the fibre map `Ψ = Φ.paramLift`
(`NemytskiiParamFibre.lean`), so the joint derivatives in `(λ, u)` are fibre derivatives of `Ψ`,
and the bounds (M) (`FibreMap.exists_derivFam_bound`) and (T) (`FibreMap.exists_taylor_bound`) hold
uniformly near `(0, w)`. The scalar inputs are controlled by `‖λ‖` (`exists_parScal_bound`). The
extension is `SmoothExtension.exists_contDiffAt_extension` with `X₀ = Λ × smoothSub`.
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

open ParabolicSpace EquationData

namespace ParamNemytskii

/-! ### Arithmetic -/

theorem par_arith {c Kc l P Cu X : ℝ} (hP : 0 ≤ P) (hCu : 0 ≤ Cu) (hc : |c| ≤ Kc * l)
    (hX : X = c ^ 2 * P) :
    X ≤ (Cu + 1) * Kc ^ 2 * P * l ^ 2 ∧ Cu * X ≤ (Cu + 1) * Kc ^ 2 * P * l ^ 2 := by
  have h1 : c ^ 2 ≤ (Kc * l) ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg c) hc 2
    rwa [sq_abs] at this
  have hA : X ≤ (Kc * l) ^ 2 * P := by
    rw [hX]
    exact mul_le_mul_of_nonneg_right h1 hP
  have hA0 : 0 ≤ (Kc * l) ^ 2 * P := by positivity
  have e : (Cu + 1) * Kc ^ 2 * P * l ^ 2 = (Cu + 1) * ((Kc * l) ^ 2 * P) := by ring
  rw [e]
  constructor
  · nlinarith [mul_nonneg hCu hA0]
  · nlinarith [mul_le_mul_of_nonneg_left hA hCu]

theorem mul_sq_le {C K a r : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) (ha : 0 ≤ a) (h : a ≤ r) :
    C * a ^ 2 ≤ (C + K) * r ^ 2 := by
  have h1 : a ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ ha h 2
  have hr : 0 ≤ r ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 hC, mul_nonneg hK hr]

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [FiniteDimensional ℝ Λ]
variable {s p : ℕ} {T : ℝ} {N : ℕ}

/-! ### Bounds for the scalar inputs -/

/-- The scalar inputs `λ_i · 1` are bounded by `‖λ‖`, pointwise and in `𝒫^N`. -/
theorem exists_parScal_bound (hT : 0 < T) (hp : 1 ≤ p)
    (hN : Module.finrank ℝ E / (2 * p) + 3 ≤ N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (lam : Λ) (i : Fin (Module.finrank ℝ Λ)),
      (∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 0 x
        ((FibreMap.parScal (g := g) Λ lam i).toSection x) ≤ K * ‖lam‖ ^ 2) ∧
      parabolicInner g 0 p N T (fun _ => FibreMap.parScal (g := g) Λ lam i)
        (fun _ => FibreMap.parScal (g := g) Λ lam i) ≤ K * ‖lam‖ ^ 2 := by
  obtain ⟨Cu, hCu0, hCu⟩ := exists_jetSq_le_parabolicInner (g := g) hT hp hN 0
  obtain ⟨P, hP⟩ : ∃ P, P = parabolicInner g 0 p N T (fun _ => unitSec I g)
      (fun _ => unitSec I g) := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hP]; exact parabolicInner_self_nonneg p N _
  obtain ⟨cf, hcf⟩ : ∃ cf : Fin (Module.finrank ℝ Λ) → (Λ →L[ℝ] ℝ), ∀ i,
      cf i = LinearMap.toContinuousLinearMap ((Module.finBasis ℝ Λ).coord i) := ⟨_, fun _ => rfl⟩
  obtain ⟨Kc, hKc⟩ : ∃ Kc : ℝ, Kc = ∑ i, ‖cf i‖ := ⟨_, rfl⟩
  have hrepr : ∀ (lam : Λ) i, |(Module.finBasis ℝ Λ).repr lam i| ≤ Kc * ‖lam‖ := by
    intro lam i
    have h1 : ‖cf i lam‖ ≤ ‖cf i‖ * ‖lam‖ := (cf i).le_opNorm lam
    have h2 : cf i lam = (Module.finBasis ℝ Λ).repr lam i := by
      rw [hcf]
      simp [Module.Basis.coord_apply]
    rw [h2, Real.norm_eq_abs] at h1
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    rw [hKc]
    exact Finset.single_le_sum (f := fun j => ‖cf j‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ i)
  have hu : JointlySmoothOn g 0 0 (Icc 0 T) (fun _ : ℝ => unitSec I g) := jointlySmoothOn_const g _ _
  refine ⟨(Cu + 1) * Kc ^ 2 * P, by positivity, fun lam i => ?_⟩
  have hX : parabolicInner g 0 p N T (fun _ => FibreMap.parScal (g := g) Λ lam i)
      (fun _ => FibreMap.parScal (g := g) Λ lam i) = ((Module.finBasis ℝ Λ).repr lam i) ^ 2 * P := by
    rw [hP]
    exact parabolicInner_smul_self hu _ p N
  obtain ⟨h1, h2⟩ := par_arith hP0 hCu0 (hrepr lam i) hX
  refine ⟨fun t ht x => ?_, h1⟩
  have h3 := hCu (fun _ => FibreMap.parScal (g := g) Λ lam i) (jointlySmoothOn_const g _ _) 0 0
    (by simp) t ht x
  rw [jetSq_zero_zero] at h3
  exact h3.trans h2

/-- `Σ_c ‖pin q c‖²_{𝒫^N} ≤ K ‖q‖²`. -/
theorem exists_sum_pin_le (hT : 0 < T) (hp : 1 ≤ p)
    (hN : Module.finrank ℝ E / (2 * p) + 3 ≤ N) :
    ∃ Kp : ℝ, 0 ≤ Kp ∧ ∀ q : Λ × smoothSub g s p (N + 1) T,
      ∑ c, parabolicInner g (parRanks (jetRanks s p) (Module.finrank ℝ Λ) c) p N T (pin q c)
        (pin q c) ≤ Kp * ‖q‖ ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := exists_parScal_bound (Λ := Λ) (g := g) hT hp hN
  refine ⟨((2 * p + 1 : ℕ) : ℝ) + Module.finrank ℝ Λ * K, by positivity, fun q => ?_⟩
  rw [Fintype.sum_sum_type]
  have h1 : ∑ k : Fin (2 * p + 1), parabolicInner g
      (parRanks (jetRanks s p) (Module.finrank ℝ Λ) (.inl k)) p N T (pin q (.inl k))
      (pin q (.inl k)) ≤ ((2 * p + 1 : ℕ) : ℝ) * ‖q‖ ^ 2 :=
    (sum_repJet_le hT q.2).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_snd_le q) 2) (Nat.cast_nonneg _))
  have h2 : ∑ i : Fin (Module.finrank ℝ Λ), parabolicInner g
      (parRanks (jetRanks s p) (Module.finrank ℝ Λ) (.inr i)) p N T (pin q (.inr i))
      (pin q (.inr i)) ≤ Module.finrank ℝ Λ * (K * ‖q‖ ^ 2) := by
    refine (Finset.sum_le_sum fun i _ => ((hK q.1 i).2.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_fst_le q) 2) hK0))).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc _ ≤ ((2 * p + 1 : ℕ) : ℝ) * ‖q‖ ^ 2 + Module.finrank ℝ Λ * (K * ‖q‖ ^ 2) :=
        add_le_add h1 h2
    _ = _ := by ring

/-! ### Pointwise bounds of the inputs -/

theorem pin_tube_le {Ce K : ℝ} (hCe0 : 0 ≤ Ce) (hK0 : 0 ≤ K) {w : ℝ → SmoothCcTensor g 0 s}
    (hw : JointlySmoothOn g 0 s (Icc 0 T) w)
    (hCe : ∀ (v : smoothSub g s p (N + 1) T) (c : Fin (2 * p + 1)), ∀ t ∈ Icc (0 : ℝ) T,
      ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (jetRanks s p c) x
        ((repJet v c t - jetFamily (p := p) w c t).toSection x) ≤
        Ce * ‖(v : ParabolicSpace g s p (N + 1) T) - ofSmooth w hw‖ ^ 2)
    (hK : ∀ (lam : Λ) (i : Fin (Module.finrank ℝ Λ)), ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 0 x
        ((FibreMap.parScal (g := g) Λ lam i).toSection x) ≤ K * ‖lam‖ ^ 2)
    (q : Λ × smoothSub g s p (N + 1) T) (c : Fin (2 * p + 1) ⊕ Fin (Module.finrank ℝ Λ)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (parRanks (jetRanks s p) (Module.finrank ℝ Λ) c) x
      ((pin q c t - FibreMap.parFam (0 : Λ) (jetFamily (p := p) w) c t).toSection x) ≤
      (Ce + K) * ‖q - ((0 : Λ), smoothElt w hw)‖ ^ 2 := by
  rcases c with c | i
  · have h1 : ‖(q.2 : ParabolicSpace g s p (N + 1) T) - ofSmooth w hw‖ ≤
        ‖q - ((0 : Λ), smoothElt w hw)‖ := norm_snd_le (q - ((0 : Λ), smoothElt w hw))
    exact (hCe q.2 c t ht x).trans (mul_sq_le hCe0 hK0 (norm_nonneg _) h1)
  · have e : FibreMap.parScal (g := g) Λ (0 : Λ) i = 0 := by simp [FibreMap.parScal]
    change riemannianFiberNormSq (I := I) (M := M) g 0 0 x ((FibreMap.parScal (g := g) Λ q.1 i -
      FibreMap.parScal (g := g) Λ 0 i).toSection x) ≤ _
    rw [e, sub_zero]
    have h1 : ‖q.1‖ ≤ ‖q - ((0 : Λ), smoothElt w hw)‖ := by
      have := norm_fst_le (q - ((0 : Λ), smoothElt w hw))
      simpa using this
    have h2 := mul_sq_le hK0 hCe0 (norm_nonneg _) h1
    rw [add_comm K Ce] at h2
    exact (hK q.1 i t ht x).trans h2

theorem pin_small_le {Ce K : ℝ} (hCe0 : 0 ≤ Ce) (hK0 : 0 ≤ K)
    (hCe : ∀ (v : smoothSub g s p (N + 1) T) (c : Fin (2 * p + 1)), ∀ t ∈ Icc (0 : ℝ) T,
      ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (jetRanks s p c) x
        ((repJet v c t).toSection x) ≤ Ce * ‖v‖ ^ 2)
    (hK : ∀ (lam : Λ) (i : Fin (Module.finrank ℝ Λ)), ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 0 x
        ((FibreMap.parScal (g := g) Λ lam i).toSection x) ≤ K * ‖lam‖ ^ 2)
    (q : Λ × smoothSub g s p (N + 1) T) (c : Fin (2 * p + 1) ⊕ Fin (Module.finrank ℝ Λ)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (parRanks (jetRanks s p) (Module.finrank ℝ Λ) c) x
      ((pin q c t).toSection x) ≤ (Ce + K) * ‖q‖ ^ 2 := by
  rcases c with c | i
  · exact (hCe q.2 c t ht x).trans (mul_sq_le hCe0 hK0 (norm_nonneg _) (norm_snd_le q))
  · have h2 := mul_sq_le hK0 hCe0 (norm_nonneg _) (norm_fst_le q)
    rw [add_comm K Ce] at h2
    exact (hK q.1 i t ht x).trans h2

variable (Φ : FibreMap I M Λ (jetRanks s p) s)

/-! ### Bound (M) -/

/-- **Bound (M)** for `g_k` near `(0, w)`. -/
theorem exists_pgfun_bound (hT : 0 < T) (hTD : T ≤ Φ.T₀) (hp : 1 ≤ p)
    (hN : Module.finrank ℝ E / (2 * p) + 3 ≤ N) {w : ℝ → SmoothCcTensor g 0 s}
    (hw : JointlySmoothOn g 0 s (Icc 0 T) w)
    (hwdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (w t) x ∈ Φ.dom 0 t x) (k : ℕ) :
    ∃ δ > 0, ∀ B : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ q : Λ × smoothSub g s p (N + 1) T,
      (∀ c, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 0
          (parRanks (jetRanks s p) (Module.finrank ℝ Λ) c) x
          ((pin q c t - FibreMap.parFam (0 : Λ) (jetFamily (p := p) w) c t).toSection x) ≤ δ) →
      ‖q‖ ^ 2 ≤ B → PRepInDom Φ q →
      ∀ h : Fin k → Λ × smoothSub g s p (N + 1) T, ‖pgfun Φ k q h‖ ≤ C * ∏ l, ‖h l‖ := by
  obtain ⟨Kp, hKp0, hKp⟩ := exists_sum_pin_le (Λ := Λ) (g := g) (s := s) hT hp hN
  obtain ⟨δ, hδ, hB⟩ := Φ.paramLift.exists_derivFam_bound k 0 hT hTD hp hN
    (w := FibreMap.parFam (0 : Λ) (jetFamily (p := p) w))
    (FibreMap.jointlySmoothOn_parFam 0 fun c => jointlySmoothOn_iteratedCovGrad hw c)
    (fun t ht x => (FibreMap.mem_paramLift_dom_parFam Φ 0 0 _ t x).2 (hwdom t ht x))
  refine ⟨δ, hδ, fun B => ?_⟩
  obtain ⟨C₀, hC₀, hC⟩ := hB (Kp * B)
  refine ⟨Real.sqrt (C₀ * Kp ^ k), Real.sqrt_nonneg _, fun q htube hqB hq h => ?_⟩
  have hsum := (hKp q).trans (mul_le_mul_of_nonneg_left hqB hKp0)
  have h1 := hC (pin q) (pin_smooth q) htube hsum (pin_dom Φ hq) (fun l => pin (h l))
    (fun l => pin_smooth (h l))
  have h2 : ∏ l, ∑ c, parabolicInner g (parRanks (jetRanks s p) (Module.finrank ℝ Λ) c) p N T
      (pin (h l) c) (pin (h l) c) ≤ Kp ^ k * (∏ l, ‖h l‖) ^ 2 :=
    prod_bound_aux _ _ (fun l => Finset.sum_nonneg fun c _ => parabolicInner_self_nonneg _ _ _)
      fun l => hKp (h l)
  refine le_sqrt_mul_of_sq (norm_nonneg _)
    (Finset.prod_nonneg fun l _ => norm_nonneg _) (mul_nonneg hC₀ (pow_nonneg hKp0 k)) ?_
  rw [norm_pgfun_sq Φ hTD k hq]
  calc parabolicInner g s p N T (pgfam Φ k q h) (pgfam Φ k q h)
      ≤ C₀ * ∏ l, ∑ c, parabolicInner g (parRanks (jetRanks s p) (Module.finrank ℝ Λ) c) p N T
          (pin (h l) c) (pin (h l) c) := h1
    _ ≤ C₀ * (Kp ^ k * (∏ l, ‖h l‖) ^ 2) := mul_le_mul_of_nonneg_left h2 hC₀
    _ = C₀ * Kp ^ k * (∏ l, ‖h l‖) ^ 2 := by ring

/-! ### Bound (T) -/

theorem pgfam_cons (k : ℕ) (q η : Λ × smoothSub g s p (N + 1) T)
    (hs : Fin k → Λ × smoothSub g s p (N + 1) T) :
    pgfam Φ (k + 1) q (Fin.cons η hs) =
      Φ.paramLift.derivFam (k + 1) 0 (pin q) (Fin.cons (pin η) fun l => pin (hs l)) := by
  rw [pgfam, fun_fin_cons]

theorem pgfam_add_eqOn (hT : 0 < T) (k : ℕ) (q η : Λ × smoothSub g s p (N + 1) T)
    (hs : Fin k → Λ × smoothSub g s p (N + 1) T) :
    ∀ t ∈ Icc (0 : ℝ) T, pgfam Φ k (q + η) hs t =
      Φ.paramLift.derivFam k 0 (fun c τ => pin q c τ + pin η c τ) (fun l => pin (hs l)) t := by
  intro t ht
  refine FibreMap.apply_congr_time _ _ fun c => ?_
  rcases c with c | c
  · exact pin_add_apply hT q η ht c
  · rfl

/-- **Bound (T)** for `g_k` near `(0, w)`. -/
theorem exists_pgfun_taylor (hT : 0 < T) (hTD : T ≤ Φ.T₀) (hp : 1 ≤ p)
    (hN : Module.finrank ℝ E / (2 * p) + 3 ≤ N) {w : ℝ → SmoothCcTensor g 0 s}
    (hw : JointlySmoothOn g 0 s (Icc 0 T) w)
    (hwdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (w t) x ∈ Φ.dom 0 t x) (k : ℕ) :
    ∃ δ > 0, ∀ B : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ q η : Λ × smoothSub g s p (N + 1) T,
      (∀ c, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 0
          (parRanks (jetRanks s p) (Module.finrank ℝ Λ) c) x
          ((pin q c t - FibreMap.parFam (0 : Λ) (jetFamily (p := p) w) c t).toSection x) ≤ δ) →
      (∀ c, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 0
          (parRanks (jetRanks s p) (Module.finrank ℝ Λ) c) x ((pin η c t).toSection x) ≤ δ) →
      ‖q‖ ^ 2 + ‖η‖ ^ 2 ≤ B → (∀ τ ∈ Icc (0 : ℝ) 1, PRepInDom Φ (q + τ • η)) →
      ∀ hs : Fin k → Λ × smoothSub g s p (N + 1) T,
        ‖pgfun Φ k (q + η) hs - pgfun Φ k q hs - pgfun Φ (k + 1) q (Fin.cons η hs)‖ ≤
          C * (‖η‖ ^ 2 * ∏ l, ‖hs l‖) := by
  obtain ⟨Kp, hKp0, hKp⟩ := exists_sum_pin_le (Λ := Λ) (g := g) (s := s) hT hp hN
  obtain ⟨δ, hδ, hB⟩ := Φ.paramLift.exists_taylor_bound k 0 hT hTD hp hN
    (w := FibreMap.parFam (0 : Λ) (jetFamily (p := p) w))
    (FibreMap.jointlySmoothOn_parFam 0 fun c => jointlySmoothOn_iteratedCovGrad hw c)
    (fun t ht x => (FibreMap.mem_paramLift_dom_parFam Φ 0 0 _ t x).2 (hwdom t ht x))
  refine ⟨δ, hδ, fun B => ?_⟩
  obtain ⟨C₀, hC₀, hC⟩ := hB (Kp * B)
  refine ⟨Real.sqrt (C₀ * Kp ^ (k + 2)), Real.sqrt_nonneg _,
    fun q η htube hηδ hqηB hseg hs => ?_⟩
  have hq : PRepInDom Φ q := by
    have := hseg 0 ⟨le_rfl, zero_le_one⟩
    rwa [zero_smul, add_zero] at this
  have hqη : PRepInDom Φ (q + η) := by
    have := hseg 1 ⟨zero_le_one, le_rfl⟩
    rwa [one_smul] at this
  have hsegF : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ τ ∈ Icc (0 : ℝ) 1,
      FibreMap.valAt (fun c => pin q c t) x + τ • FibreMap.valAt (fun c => pin η c t) x ∈
        Φ.paramLift.dom 0 t x := by
    intro t ht x τ hτ
    have h1 := pin_dom Φ (hseg τ hτ) t ht x
    rwa [valAt_pin_add hT q (τ • η) ht, valAt_pin_smul hT τ η ht] at h1
  have hsum : ∑ c, parabolicInner g (parRanks (jetRanks s p) (Module.finrank ℝ Λ) c) p N T
        (pin q c) (pin q c) + ∑ c, parabolicInner g
        (parRanks (jetRanks s p) (Module.finrank ℝ Λ) c) p N T (pin η c) (pin η c) ≤ Kp * B := by
    refine (add_le_add (hKp q) (hKp η)).trans ?_
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left hqηB hKp0
  have h1 := hC (pin q) (pin η) (pin_smooth q) (pin_smooth η) htube hηδ hsum hsegF
    (fun l => pin (hs l)) (fun l => pin_smooth (hs l))
  obtain ⟨A, hA⟩ : ∃ A, A = Φ.paramLift.derivFam k 0 (fun c τ => pin q c τ + pin η c τ)
      (fun l => pin (hs l)) := ⟨_, rfl⟩
  obtain ⟨Cf, hCf⟩ : ∃ Cf, Cf = Φ.paramLift.derivFam (k + 1) 0 (pin q)
      (Fin.cons (pin η) fun l => pin (hs l)) := ⟨_, rfl⟩
  have hAeq : ∀ t ∈ Icc (0 : ℝ) T, pgfam Φ k (q + η) hs t = A t := fun t ht => by
    rw [hA]
    exact pgfam_add_eqOn Φ hT k q η hs t ht
  have hAs : JointlySmoothOn g 0 s (Icc 0 T) A :=
    jointlySmoothOn_congr_Icc (pgfam_spec Φ hTD k hqη hs).2 fun t ht => (hAeq t ht).symm
  have hBs : JointlySmoothOn g 0 s (Icc 0 T) (pgfam Φ k q hs) := (pgfam_spec Φ hTD k hq hs).2
  have hCeq : pgfam Φ (k + 1) q (Fin.cons η hs) = Cf := by rw [hCf, pgfam_cons]
  have hCs : JointlySmoothOn g 0 s (Icc 0 T) Cf := by
    rw [← hCeq]
    exact (pgfam_spec Φ hTD (k + 1) hq (Fin.cons η hs)).2
  have hR := jointlySmoothOn_sub (jointlySmoothOn_sub hAs hBs) hCs
  have e1 : ofSmooth (p := p) (m := N) (pgfam Φ k (q + η) hs) (pgfam_spec Φ hTD k hqη hs).2 =
      ofSmooth A hAs := ofSmooth_congr hT _ _ hAeq
  have e3 : ofSmooth (p := p) (m := N) (pgfam Φ (k + 1) q (Fin.cons η hs))
      (pgfam_spec Φ hTD (k + 1) hq (Fin.cons η hs)).2 = ofSmooth Cf hCs :=
    ofSmooth_congr hT _ _ fun t _ => by rw [hCeq]
  have heq : pgfun Φ k (q + η) hs - pgfun Φ k q hs - pgfun Φ (k + 1) q (Fin.cons η hs) =
      ofSmooth (p := p) (m := N) (fun t => A t - pgfam Φ k q hs t - Cf t) hR := by
    rw [ofSmooth_sub (jointlySmoothOn_sub hAs hBs) hCs, ofSmooth_sub hAs hBs,
      pgfun_eq Φ hTD k hqη, pgfun_eq Φ hTD k hq, pgfun_eq Φ hTD (k + 1) hq, e1, e3]
  rw [heq]
  have hP := prod_bound_aux _ (fun l => ‖hs l‖)
    (fun l => Finset.sum_nonneg fun c _ => parabolicInner_self_nonneg (g := g) (T := T) p N
      (pin (hs l) c)) fun l => hKp (hs l)
  refine le_sqrt_mul_of_sq (norm_nonneg _)
    (mul_nonneg (sq_nonneg _) (Finset.prod_nonneg fun l _ => norm_nonneg _))
    (mul_nonneg hC₀ (pow_nonneg hKp0 _)) ?_
  rw [norm_ofSmooth_sq]
  rw [hA, hCf]
  exact taylor_arith k hC₀ (Finset.sum_nonneg fun c _ => parabolicInner_self_nonneg _ _ _)
    (Finset.prod_nonneg fun l _ => Finset.sum_nonneg fun c _ => parabolicInner_self_nonneg _ _ _)
    h1 (hKp η) hP

end ParamNemytskii

end ShortTime
