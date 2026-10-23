import ShortTime.Nonlinear.UniformTubeBound
import ShortTime.Nonlinear.NemytskiiParamOp

/-!
# The parametric Nemytskii operator on a fixed ball (stage 5)

`FibreMap.exists_nonlinOp_param_ball`: like `exists_nonlinOp_param`, but `𝒩` is `C^∞` on the whole
ball `ball (0, w) δ`, with `δ` independent of the order of differentiation. The tube radii of the
bounds (M) and (T) are uniform in `k` (`exists_derivFam_bound_unif`, `exists_taylor_bound_unif`).
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

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [FiniteDimensional ℝ Λ]
variable {s p : ℕ} {T : ℝ} {N : ℕ}

variable (Φ : FibreMap I M Λ (jetRanks s p) s)

/-- **Bound (M)** for `g_k` near `(0, w)`. -/
theorem exists_pgfun_bound_unif (hT : 0 < T) (hTD : T ≤ Φ.T₀) (hp : 1 ≤ p)
    (hN : Module.finrank ℝ E / (2 * p) + 3 ≤ N) {w : ℝ → SmoothCcTensor g 0 s}
    (hw : JointlySmoothOn g 0 s (Icc 0 T) w)
    (hwdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (w t) x ∈ Φ.dom 0 t x) :
    ∃ δ > 0, ∀ k : ℕ, ∀ B : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ q : Λ × smoothSub g s p (N + 1) T,
      (∀ c, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 0
          (parRanks (jetRanks s p) (Module.finrank ℝ Λ) c) x
          ((pin q c t - FibreMap.parFam (0 : Λ) (jetFamily (p := p) w) c t).toSection x) ≤ δ) →
      ‖q‖ ^ 2 ≤ B → PRepInDom Φ q →
      ∀ h : Fin k → Λ × smoothSub g s p (N + 1) T, ‖pgfun Φ k q h‖ ≤ C * ∏ l, ‖h l‖ := by
  obtain ⟨Kp, hKp0, hKp⟩ := exists_sum_pin_le (Λ := Λ) (g := g) (s := s) hT hp hN
  obtain ⟨δ, hδ, hB⟩ := Φ.paramLift.exists_derivFam_bound_unif 0 hT hTD hp hN
    (w := FibreMap.parFam (0 : Λ) (jetFamily (p := p) w))
    (FibreMap.jointlySmoothOn_parFam 0 fun c => jointlySmoothOn_iteratedCovGrad hw c)
    (fun t ht x => (FibreMap.mem_paramLift_dom_parFam Φ 0 0 _ t x).2 (hwdom t ht x))
  refine ⟨δ, hδ, fun k B => ?_⟩
  obtain ⟨C₀, hC₀, hC⟩ := hB k (Kp * B)
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


/-- **Bound (T)** for `g_k` near `(0, w)`. -/
theorem exists_pgfun_taylor_unif (hT : 0 < T) (hTD : T ≤ Φ.T₀) (hp : 1 ≤ p)
    (hN : Module.finrank ℝ E / (2 * p) + 3 ≤ N) {w : ℝ → SmoothCcTensor g 0 s}
    (hw : JointlySmoothOn g 0 s (Icc 0 T) w)
    (hwdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (w t) x ∈ Φ.dom 0 t x) :
    ∃ δ > 0, ∀ k : ℕ, ∀ B : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ q η : Λ × smoothSub g s p (N + 1) T,
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
  obtain ⟨δ, hδ, hB⟩ := Φ.paramLift.exists_taylor_bound_unif 0 hT hTD hp hN
    (w := FibreMap.parFam (0 : Λ) (jetFamily (p := p) w))
    (FibreMap.jointlySmoothOn_parFam 0 fun c => jointlySmoothOn_iteratedCovGrad hw c)
    (fun t ht x => (FibreMap.mem_paramLift_dom_parFam Φ 0 0 _ t x).2 (hwdom t ht x))
  refine ⟨δ, hδ, fun k B => ?_⟩
  obtain ⟨C₀, hC₀, hC⟩ := hB k (Kp * B)
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


theorem exists_nonlinOp_param_ball_aux (hp : 1 ≤ p) (hT : 0 < T) (hTD : T ≤ Φ.T₀)
    (hN : Module.finrank ℝ E / (2 * p) + 3 ≤ N) {w : ℝ → SmoothCcTensor g 0 s}
    (hw : JointlySmoothOn g 0 s (Icc 0 T) w)
    (hwdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (w t) x ∈ Φ.dom 0 t x) :
    ∃ δ > 0, ∃ 𝒩 : Λ × ParabolicSpace g s p (N + 1) T → ParabolicSpace g s p N T,
      ContDiffOn ℝ ∞ 𝒩 (ball ((0 : Λ), ofSmooth w hw) δ) ∧
      (∀ (lam : Λ) (u : ℝ → SmoothCcTensor g 0 s) (hu : JointlySmoothOn g 0 s (Icc 0 T) u),
        ‖lam‖ < δ → dist (ofSmooth (p := p) (m := N + 1) u hu) (ofSmooth w hw) < δ →
        (∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (u t) x ∈ Φ.dom lam t x) ∧
        ∃ hF, 𝒩 (lam, ofSmooth u hu) = ofSmooth (Φ.apply lam (jetFamily (p := p) u)) hF) ∧
      (∀ (μ : Λ) (h : ℝ → SmoothCcTensor g 0 s) (hh : JointlySmoothOn g 0 s (Icc 0 T) h), ∃ hL,
        fderiv ℝ 𝒩 (0, ofSmooth w hw) (μ, ofSmooth h hh) =
          ofSmooth (Φ.paramLift.derivFam 1 0 (FibreMap.parFam (0 : Λ) (jetFamily (p := p) w))
            (fun _ => FibreMap.parFam μ (jetFamily (p := p) h))) hL) := by
  have hm : 1 ≤ N + 1 := by omega
  obtain ⟨Ce, hCe0, hCe, hCe'⟩ := exists_fiberNormSq_repJet_le (g := g) (s := s) hT hp hN
  obtain ⟨K, hK0, hK⟩ := exists_parScal_bound (Λ := Λ) (g := g) hT hp hN
  have hWs := FibreMap.jointlySmoothOn_parFam (u := jetFamily (p := p) w) (0 : Λ)
    fun c => jointlySmoothOn_iteratedCovGrad hw c
  have hWdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      FibreMap.valAt (fun c => FibreMap.parFam (0 : Λ) (jetFamily (p := p) w) c t) x ∈
        Φ.paramLift.dom 0 t x :=
    fun t ht x => (FibreMap.mem_paramLift_dom_parFam Φ 0 0 _ t x).2 (hwdom t ht x)
  obtain ⟨δ₁, hδ₁, hδ₁dom, -⟩ := Φ.paramLift.exists_tame_pointwise 0 hT hTD hWs hWdom
    (p := p) (by omega) 0
  obtain ⟨δM0, hδM0, hMb⟩ := exists_pgfun_bound_unif Φ hT hTD hp hN hw hwdom
  obtain ⟨δT0, hδT0, hTb⟩ := exists_pgfun_taylor_unif Φ hT hTD hp hN hw hwdom
  choose CM hCM0 hCM using hMb
  choose CT hCT0 hCT using hTb
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : Λ × smoothSub g s p (N + 1) T, w₀ = ((0 : Λ), smoothElt w hw) :=
    ⟨_, rfl⟩
  have hCt0 : 0 ≤ Ce + K := add_nonneg hCe0 hK0
  have htube : ∀ q : Λ × smoothSub g s p (N + 1) T, ∀ r : ℝ, dist q w₀ < r →
      ∀ c, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 0
          (parRanks (jetRanks s p) (Module.finrank ℝ Λ) c) x
          ((pin q c t - FibreMap.parFam (0 : Λ) (jetFamily (p := p) w) c t).toSection x) ≤
          (Ce + K) * (2 * r) ^ 2 := by
    intro q r hq c t ht x
    have hd : ‖q - ((0 : Λ), smoothElt w hw)‖ < r := by
      rw [← hw₀, ← dist_eq_norm]
      exact hq
    exact (pin_tube_le hCe0 hK0 hw (hCe w hw) (fun lam i => (hK lam i).1) q c ht x).trans
      (mul_le_mul_of_nonneg_left (sq_le_two_mul_sq (norm_nonneg _) hd) hCt0)
  have hdomv : ∀ q : Λ × smoothSub g s p (N + 1) T, ∀ r : ℝ, dist q w₀ < r →
      (Ce + K) * (2 * r) ^ 2 ≤ δ₁ → PRepInDom Φ q := fun q r hq hr =>
    pRepInDom_of_dom Φ (hδ₁dom (pin q) fun c t ht x => (htube q r hq c t ht x).trans hr)
  obtain ⟨δs, hδs⟩ : ∃ δs : ℝ, δs = min δ₁ (min δM0 δT0) := ⟨_, rfl⟩
  have hδspos : 0 < δs := by rw [hδs]; exact lt_min hδ₁ (lt_min hδM0 hδT0)
  obtain ⟨r, hr, hrδ⟩ := exists_radius hCt0 hδspos
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = (‖w₀‖ + r) ^ 2 + (2 * r) ^ 2 := ⟨_, rfl⟩
  have hb : ∀ n : ℕ,
      (∀ k ≤ n + 1, ∀ u ∈ ball w₀ r, ‖pgCML Φ hT hTD k u‖ ≤ max (CM k B) (CT k B)) ∧
      (∀ k ≤ n, ∀ u ∈ ball w₀ r, ∀ h, u + h ∈ ball w₀ r →
        ‖pgCML Φ hT hTD k (u + h) - pgCML Φ hT hTD k u -
          (pgCML Φ hT hTD (k + 1) u).curryLeft h‖ ≤ max (CM k B) (CT k B) * ‖h‖ ^ 2) := by
    intro n
    have hδsle : ∀ k ≤ n + 1, δs ≤ min δ₁ (min δM0 δT0) := fun k _ => by rw [hδs]
    have hle1 : (Ce + K) * (2 * r) ^ 2 ≤ δ₁ :=
      hrδ.trans ((hδsle 0 (Nat.zero_le _)).trans (min_le_left _ _))
    have hleM : ∀ k ≤ n + 1, (Ce + K) * (2 * r) ^ 2 ≤ δM0 := fun k hk =>
      hrδ.trans ((hδsle k hk).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hleT : ∀ k ≤ n + 1, (Ce + K) * (2 * r) ^ 2 ≤ δT0 := fun k hk =>
      hrδ.trans ((hδsle k hk).trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hdomb : ∀ u ∈ ball w₀ r, PRepInDom Φ u := fun u hu => hdomv u r hu hle1
    have hnorm : ∀ u ∈ ball w₀ r, ‖u‖ ≤ ‖w₀‖ + r := fun u hu => by
      have h1 := norm_sub_norm_le u w₀
      have h2 : ‖u - w₀‖ < r := by rw [← dist_eq_norm]; exact hu
      linarith
    have hnormB : ∀ u ∈ ball w₀ r, ‖u‖ ^ 2 ≤ B := fun u hu => by
      rw [hB]
      exact (pow_le_pow_left₀ (norm_nonneg _) (hnorm u hu) 2).trans
        (le_add_of_nonneg_right (sq_nonneg _))
    have hbound : ∀ k ≤ n + 1, ∀ u ∈ ball w₀ r, ∀ h : Fin k → Λ × smoothSub g s p (N + 1) T,
        ‖pgfun Φ k u h‖ ≤ CM k B * ∏ l, ‖h l‖ := fun k hk u hu h =>
      hCM k B u (fun c t ht x => (htube u r hu c t ht x).trans (hleM k hk)) (hnormB u hu)
        (hdomb u hu) h
    have happly : ∀ k ≤ n + 1, ∀ u ∈ ball w₀ r, ∀ h : Fin k → Λ × smoothSub g s p (N + 1) T,
        pgCML Φ hT hTD k u h = pgfun Φ k u h :=
      fun k hk u hu h => pgCML_apply Φ hT hTD k (hdomb u hu) ⟨_, hbound k hk u hu⟩ h
    refine ⟨fun k hk u hu => ?_, fun k hk u hu h huh => ?_⟩
    · refine (ContinuousMultilinearMap.opNorm_le_bound (hCM0 k B) fun h => ?_).trans
        (le_max_left _ _)
      rw [happly k hk u hu]
      exact hbound k hk u hu h
    · have hh : ‖h‖ < 2 * r := by
        have h1 : ‖h‖ = dist (u + h) u := by rw [dist_eq_norm, add_sub_cancel_left]
        have h2 := dist_triangle_right (u + h) u w₀
        rw [mem_ball] at hu huh
        linarith
      have hseg : ∀ τ ∈ Icc (0 : ℝ) 1, PRepInDom Φ (u + τ • h) := by
        intro τ hτ
        have hmem : u + τ • h ∈ ball w₀ r := by
          have := (convex_ball w₀ r).add_smul_sub_mem hu huh hτ
          rwa [add_sub_cancel_left] at this
        exact hdomb _ hmem
      have hBh : ‖u‖ ^ 2 + ‖h‖ ^ 2 ≤ B := by
        rw [hB]
        exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) (hnorm u hu) 2)
          (pow_le_pow_left₀ (norm_nonneg _) hh.le 2)
      have hhpt : ∀ c, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 0
            (parRanks (jetRanks s p) (Module.finrank ℝ Λ) c) x
            ((pin h c t).toSection x) ≤ δT0 := fun c t ht x =>
        (pin_small_le hCe0 hK0 hCe' (fun lam i => (hK lam i).1) h c ht x).trans
          ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hh.le 2) hCt0).trans
            (hleT k (by omega)))
      refine (ContinuousMultilinearMap.opNorm_le_bound
        (mul_nonneg (hCT0 k B) (sq_nonneg _)) fun hs => ?_).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))
      rw [sub_apply, sub_apply,
        ContinuousMultilinearMap.curryLeft_apply, happly k (by omega) (u + h) huh,
        happly k (by omega) u hu, happly (k + 1) (by omega) u hu, mul_assoc]
      exact hCT k B u h (fun c t ht x => (htube u r hu c t ht x).trans (hleT k (by omega)))
        hhpt hBh hseg hs
  obtain ⟨𝒩, h𝒩, h𝒩e, h𝒩d⟩ := SmoothExtension.exists_contDiffOn_extension
    (incl (Λ := Λ) (g := g) (s := s) (p := p) (N := N) (T := T)) norm_incl denseRange_incl w₀ r
    (fun k => pgCML Φ hT hTD k) (fun k => max (CM k B) (CT k B))
    (fun k u hu => (hb k).1 k (by omega) u hu)
    (fun k u hu h huh => (hb k).2 k le_rfl u hu h huh)
  have hιw : incl w₀ = ((0 : Λ), ofSmooth (p := p) (m := N + 1) w hw) := by rw [hw₀]; rfl
  obtain ⟨rD, hrD, hrDδ⟩ := exists_radius hCt0 hδ₁
  have h𝒩' : ContDiffOn ℝ ∞ 𝒩 (ball ((0 : Λ), ofSmooth (p := p) (m := N + 1) w hw) (min r rD)) := by
    rw [← hιw]
    exact h𝒩.mono (ball_subset_ball (min_le_left _ _))
  refine ⟨min r rD, lt_min hr hrD, 𝒩, h𝒩', fun lam u hu hlam hdist => ?_, ?_⟩
  · obtain ⟨q, hq⟩ : ∃ q : Λ × smoothSub g s p (N + 1) T, q = (lam, smoothElt u hu) := ⟨_, rfl⟩
    have hqd : dist q w₀ < min r rD := by
      rw [hq, hw₀, Prod.dist_eq]
      refine max_lt ?_ hdist
      rw [dist_zero_right]
      exact hlam
    have hdomq : PRepInDom Φ q := hdomv q rD (lt_of_lt_of_le hqd (min_le_right _ _)) hrDδ
    have hrep : ∀ t ∈ Icc (0 : ℝ) T, ParabolicSpace.rep q.2 t = u t := by
      intro t ht
      rw [hq]
      exact rep_smoothElt hT hm u hu ht
    have hdomu : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (u t) x ∈ Φ.dom lam t x := by
      intro t ht x
      have h1 := hdomq t ht x
      rw [hrep t ht] at h1
      rw [hq] at h1
      exact h1
    obtain ⟨hex, hF⟩ := Φ.jointlySmoothOn_fibreApply lam hTD
      (V := jetFamily (p := p) u) (fun c => jointlySmoothOn_iteratedCovGrad hu c) (fun t ht x => hdomu t ht x)
    refine ⟨hdomu, hF, ?_⟩
    have hιq : incl q = (lam, ofSmooth (p := p) (m := N + 1) u hu) := by rw [hq]; rfl
    have e1 : 𝒩 (lam, ofSmooth u hu) = pgCML Φ hT hTD 0 q 0 := by
      rw [← hιq]
      exact h𝒩e q (lt_of_lt_of_le hqd (min_le_left _ _))
    have hb0 : ∃ C, ∀ h : Fin 0 → Λ × smoothSub g s p (N + 1) T,
        ‖pgfun Φ 0 q h‖ ≤ C * ∏ l, ‖h l‖ :=
      ⟨‖pgfun Φ 0 q 0‖, fun h => by rw [Subsingleton.elim h 0]; simp⟩
    rw [e1, pgCML_apply Φ hT hTD 0 hdomq hb0, pgfun_eq Φ hTD 0 hdomq]
    refine ofSmooth_congr hT _ _ fun t ht => smoothCcTensor_eq_of_toSection fun x => ?_
    rw [(pgfam_spec Φ hTD 0 hdomq 0).1 t ht x, FibreMap.derivF_zero_eq, fbase_joinPt,
      FibreMap.apply_toSection Φ lam _ t (hex t ht) x, valAt_jetFamily]
    have e2 : Φ.paramLift.F 0 t x (FibreMap.valAt (fun c => pin q c t) x) =
        Φ.F q.1 t x (covJet g 0 s (2 * p) (ParabolicSpace.rep q.2 t) x) :=
      FibreMap.paramLift_F_parFam Φ 0 q.1 (repJet q.2) t x
    rw [e2, hrep t ht, hq]
  · intro μ h hh
    obtain ⟨η, hη⟩ : ∃ η : Λ × smoothSub g s p (N + 1) T, η = (μ, smoothElt h hh) := ⟨_, rfl⟩
    have hdomw : PRepInDom Φ w₀ := hdomv w₀ rD (by rw [dist_self]; exact hrD) hrDδ
    have hw0t : ∀ c, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 0
          (parRanks (jetRanks s p) (Module.finrank ℝ Λ) c) x
          ((pin w₀ c t - FibreMap.parFam (0 : Λ) (jetFamily (p := p) w) c t).toSection x) ≤
          δM0 := by
      intro c t ht x
      have h1 := pin_tube_le hCe0 hK0 hw (hCe w hw) (fun lam i => (hK lam i).1) w₀ c ht x
      rw [← hw₀, sub_self, norm_zero] at h1
      have h2 : (Ce + K) * (0 : ℝ) ^ 2 = 0 := by ring
      rw [h2] at h1
      exact h1.trans hδM0.le
    have hb1 : ∃ C, ∀ hs : Fin 1 → Λ × smoothSub g s p (N + 1) T,
        ‖pgfun Φ 1 w₀ hs‖ ≤ C * ∏ l, ‖hs l‖ :=
      ⟨CM 1 (‖w₀‖ ^ 2), hCM 1 _ w₀ hw0t le_rfl hdomw⟩
    have hL := (Φ.paramLift.jointlySmoothOn_derivFam 1 0 hTD hWs hWdom
      (h := fun _ => FibreMap.parFam μ (jetFamily (p := p) h))
      (fun _ => FibreMap.jointlySmoothOn_parFam (u := jetFamily (p := p) h) μ
        fun c => jointlySmoothOn_iteratedCovGrad hh c)).2
    refine ⟨hL, ?_⟩
    have hιη : incl η = (μ, ofSmooth (p := p) (m := N + 1) h hh) := by rw [hη]; rfl
    have e1 : fderiv ℝ 𝒩 ((0 : Λ), ofSmooth w hw) (μ, ofSmooth h hh) =
        pgCML Φ hT hTD 1 w₀ (fun _ => η) := by
      rw [← hιw, ← hιη]
      exact h𝒩d w₀ (mem_ball_self hr) η
    rw [e1, pgCML_apply Φ hT hTD 1 hdomw hb1, pgfun_eq Φ hTD 1 hdomw]
    have hrepw : ∀ t ∈ Icc (0 : ℝ) T, ParabolicSpace.rep w₀.2 t = w t := by
      intro t ht
      rw [hw₀]
      exact rep_smoothElt hT hm w hw ht
    have hreph : ∀ t ∈ Icc (0 : ℝ) T, ParabolicSpace.rep η.2 t = h t := by
      intro t ht
      rw [hη]
      exact rep_smoothElt hT hm h hh ht
    refine ofSmooth_congr hT _ _ fun t ht => FibreMap.apply_congr_time _ _ fun c => ?_
    rcases c with (c | i) | ⟨l, c | i⟩
    · change iteratedCovGrad g 0 s (c : ℕ) (ParabolicSpace.rep w₀.2 t) =
        iteratedCovGrad g 0 s (c : ℕ) (w t)
      rw [hrepw t ht]
    · change FibreMap.parScal (g := g) Λ w₀.1 i = FibreMap.parScal (g := g) Λ 0 i
      rw [hw₀]
    · change iteratedCovGrad g 0 s (c : ℕ) (ParabolicSpace.rep η.2 t) =
        iteratedCovGrad g 0 s (c : ℕ) (h t)
      rw [hreph t ht]
    · change FibreMap.parScal (g := g) Λ η.1 i = FibreMap.parScal (g := g) Λ μ i
      rw [hη]

end ParamNemytskii

/-- **The parametric nonlinear operator on a fixed ball** (`cor:N`, jointly in `(λ, u)`). As
`exists_nonlinOp_param`, but `𝒩` is `C^∞` on the whole ball `ball (0, w) δ`, with the same `δ` as in
the second conclusion. -/
theorem FibreMap.exists_nonlinOp_param_ball {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ]
    [FiniteDimensional ℝ Λ] {s p : ℕ} {T : ℝ} (Φ : FibreMap I M Λ (jetRanks s p) s)
    (hp : 1 ≤ p) (hT : 0 < T) (hTD : T ≤ Φ.T₀) {m : ℕ}
    (hm : Module.finrank ℝ E / (2 * p) + 4 ≤ m) {w : ℝ → SmoothCcTensor g 0 s}
    (hw : JointlySmoothOn g 0 s (Icc 0 T) w)
    (hwdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (w t) x ∈ Φ.dom 0 t x) :
    ∃ δ > 0, ∃ 𝒩 : Λ × ParabolicSpace g s p m T → ParabolicSpace g s p (m - 1) T,
      ContDiffOn ℝ ∞ 𝒩 (ball ((0 : Λ), ofSmooth w hw) δ) ∧
      (∀ (lam : Λ) (u : ℝ → SmoothCcTensor g 0 s) (hu : JointlySmoothOn g 0 s (Icc 0 T) u),
        ‖lam‖ < δ → dist (ofSmooth (p := p) (m := m) u hu) (ofSmooth w hw) < δ →
        (∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (u t) x ∈ Φ.dom lam t x) ∧
        ∃ hF, 𝒩 (lam, ofSmooth u hu) = ofSmooth (Φ.apply lam (jetFamily (p := p) u)) hF) ∧
      (∀ (μ : Λ) (h : ℝ → SmoothCcTensor g 0 s) (hh : JointlySmoothOn g 0 s (Icc 0 T) h), ∃ hL,
        fderiv ℝ 𝒩 (0, ofSmooth w hw) (μ, ofSmooth h hh) =
          ofSmooth (Φ.paramLift.derivFam 1 0 (FibreMap.parFam (0 : Λ) (jetFamily (p := p) w))
            (fun _ => FibreMap.parFam μ (jetFamily (p := p) h))) hL) := by
  have h4 : 4 ≤ m := le_trans (Nat.le_add_left 4 _) hm
  obtain ⟨N, rfl⟩ : ∃ N, m = N + 1 := ⟨m - 1, by omega⟩
  have hN : Module.finrank ℝ E / (2 * p) + 3 ≤ N := by omega
  exact ParamNemytskii.exists_nonlinOp_param_ball_aux Φ hp hT hTD hN hw hwdom

end ShortTime
