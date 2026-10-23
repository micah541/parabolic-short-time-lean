import ShortTime.Nonlinear.NemytskiiParam

/-!
# The parametric nonlinear operator on the parabolic spaces (`cor:N`, jointly in `(λ, u)`)

`FibreMap.exists_nonlinOp_param`: for a smooth fibre map `Φ(λ, t, x, ζ)` on covariant `2p`-jets
with a finite-dimensional parameter `λ ∈ Λ`, and a smooth family `w` with jets in the domain of
`Φ(0, ·)`, the map `(λ, u) ↦ Φ[λ, u]` extends from `Λ × {smooth families near w}` to a map
`𝒩 : Λ × 𝒫^m → 𝒫^{m-1}`, `C^∞` at `(0, w)`. Its derivative at `(0, w)` in the direction `(μ, h)`
(`h` smooth) is the fibre derivative `D_{(λ,ζ)} Φ(0, t, j w)[(μ, j h)]`, computed through the lift
`Φ.paramLift` of `λ` to scalar inputs.
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

/-- The inclusion `Λ × smoothSub → Λ × 𝒫^{N+1}` (built with `mkContinuous`, so that its
instances are the normed ones). -/
def incl :=
  LinearMap.mkContinuous (𝕜 := ℝ) (σ := RingHom.id ℝ) (E := Λ × smoothSub g s p (N + 1) T)
    (F := Λ × ParabolicSpace g s p (N + 1) T)
    { toFun := fun q => (q.1, (q.2 : ParabolicSpace g s p (N + 1) T))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1 fun q => by
    rw [one_mul]
    exact le_of_eq rfl

theorem incl_apply (q : Λ × smoothSub g s p (N + 1) T) :
    incl q = (q.1, (q.2 : ParabolicSpace g s p (N + 1) T)) := rfl

theorem norm_incl (q : Λ × smoothSub g s p (N + 1) T) : ‖incl q‖ = ‖q‖ := by
  rw [incl_apply, Prod.norm_def, Prod.norm_def]
  rfl

theorem denseRange_incl : DenseRange (incl (Λ := Λ) (g := g) (s := s) (p := p) (N := N) (T := T)) := by
  have h : ⇑(incl (Λ := Λ) (g := g) (s := s) (p := p) (N := N) (T := T)) =
      Prod.map id (smoothSub g s p (N + 1) T).subtypeL := by
    funext q
    rfl
  rw [h]
  exact DenseRange.prodMap (Function.Surjective.denseRange fun y => ⟨y, rfl⟩) denseRange_smoothSub

variable (Φ : FibreMap I M Λ (jetRanks s p) s)

/-- `cor:N` with a parameter, at the level `𝒫^{N+1} → 𝒫^N`. -/
theorem exists_nonlinOp_param_aux (hp : 1 ≤ p) (hT : 0 < T) (hTD : T ≤ Φ.T₀)
    (hN : Module.finrank ℝ E / (2 * p) + 3 ≤ N) {w : ℝ → SmoothCcTensor g 0 s}
    (hw : JointlySmoothOn g 0 s (Icc 0 T) w)
    (hwdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (w t) x ∈ Φ.dom 0 t x) :
    ∃ δ > 0, ∃ 𝒩 : Λ × ParabolicSpace g s p (N + 1) T → ParabolicSpace g s p N T,
      ContDiffAt ℝ ∞ 𝒩 (0, ofSmooth w hw) ∧
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
  choose δM hδM CM hCM0 hCM using fun k => exists_pgfun_bound Φ hT hTD hp hN hw hwdom k
  choose δT hδT CT hCT0 hCT using fun k => exists_pgfun_taylor Φ hT hTD hp hN hw hwdom k
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
  have hb : ∀ n : ℕ, ∃ δ > 0, ∃ C : ℕ → ℝ,
      (∀ k ≤ n + 1, ∀ u ∈ ball w₀ δ, ‖pgCML Φ hT hTD k u‖ ≤ C k) ∧
      (∀ k ≤ n, ∀ u ∈ ball w₀ δ, ∀ h, u + h ∈ ball w₀ δ →
        ‖pgCML Φ hT hTD k (u + h) - pgCML Φ hT hTD k u -
          (pgCML Φ hT hTD (k + 1) u).curryLeft h‖ ≤ C k * ‖h‖ ^ 2) := by
    intro n
    obtain ⟨δs, hδs, hδsle⟩ := exists_pos_le_fin (fun k => min δ₁ (min (δM k) (δT k)))
      (fun k => lt_min hδ₁ (lt_min (hδM k) (hδT k))) (n + 1)
    obtain ⟨r, hr, hrδ⟩ := exists_radius hCt0 hδs
    obtain ⟨B, hB⟩ : ∃ B : ℝ, B = (‖w₀‖ + r) ^ 2 + (2 * r) ^ 2 := ⟨_, rfl⟩
    have hle1 : (Ce + K) * (2 * r) ^ 2 ≤ δ₁ :=
      hrδ.trans ((hδsle 0 (Nat.zero_le _)).trans (min_le_left _ _))
    have hleM : ∀ k ≤ n + 1, (Ce + K) * (2 * r) ^ 2 ≤ δM k := fun k hk =>
      hrδ.trans ((hδsle k hk).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hleT : ∀ k ≤ n + 1, (Ce + K) * (2 * r) ^ 2 ≤ δT k := fun k hk =>
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
            ((pin h c t).toSection x) ≤ δT k := fun c t ht x =>
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
  obtain ⟨δ₀, hδ₀, 𝒩, h𝒩, -, h𝒩e, h𝒩d⟩ := SmoothExtension.exists_contDiffAt_extension
    (incl (Λ := Λ) (g := g) (s := s) (p := p) (N := N) (T := T)) norm_incl denseRange_incl w₀
    (fun k => pgCML Φ hT hTD k) hb
  have hιw : incl w₀ = ((0 : Λ), ofSmooth (p := p) (m := N + 1) w hw) := by rw [hw₀]; rfl
  obtain ⟨rD, hrD, hrDδ⟩ := exists_radius hCt0 hδ₁
  have h𝒩' : ContDiffAt ℝ ∞ 𝒩 ((0 : Λ), ofSmooth (p := p) (m := N + 1) w hw) := by
    rw [← hιw]
    exact h𝒩
  refine ⟨min δ₀ rD, lt_min hδ₀ hrD, 𝒩, h𝒩', fun lam u hu hlam hdist => ?_, ?_⟩
  · obtain ⟨q, hq⟩ : ∃ q : Λ × smoothSub g s p (N + 1) T, q = (lam, smoothElt u hu) := ⟨_, rfl⟩
    have hqd : dist q w₀ < min δ₀ rD := by
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
          δM 1 := by
      intro c t ht x
      have h1 := pin_tube_le hCe0 hK0 hw (hCe w hw) (fun lam i => (hK lam i).1) w₀ c ht x
      rw [← hw₀, sub_self, norm_zero] at h1
      have h2 : (Ce + K) * (0 : ℝ) ^ 2 = 0 := by ring
      rw [h2] at h1
      exact h1.trans (hδM 1).le
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
      exact h𝒩d η
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

/-- **The parametric nonlinear operator on the parabolic spaces** (`cor:N`, jointly in `(λ, u)`).
Let `Φ(λ, t, x, ζ)` be a smooth fibre map on covariant `2p`-jets with a parameter `λ` in a
finite-dimensional space `Λ`, `w` a jointly smooth family on `[0,T]` whose `2p`-jets lie in the
domain of `Φ(0, ·)`, and `m ≥ ⌊n/2p⌋ + 4`. There are `δ > 0` and `𝒩 : Λ × 𝒫^m → 𝒫^{m-1}` such that

* `𝒩` is `C^∞` at `(0, w)`;
* for `‖λ‖ < δ` and every smooth family `u` within `δ` of `w` in `𝒫^m`, the jets of `u` lie in the
  domain of `Φ(λ, ·)` and `𝒩(λ, u) = Φ[λ, u]`;
* the derivative of `𝒩` at `(0, w)` in the direction `(μ, h)`, `h` smooth, is
  `D_{(λ,ζ)}Φ(0, t, j w)[(μ, j h)]`, the first fibre derivative of the lift `Φ.paramLift`. -/
theorem FibreMap.exists_nonlinOp_param {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ]
    [FiniteDimensional ℝ Λ] {s p : ℕ} {T : ℝ} (Φ : FibreMap I M Λ (jetRanks s p) s)
    (hp : 1 ≤ p) (hT : 0 < T) (hTD : T ≤ Φ.T₀) {m : ℕ}
    (hm : Module.finrank ℝ E / (2 * p) + 4 ≤ m) {w : ℝ → SmoothCcTensor g 0 s}
    (hw : JointlySmoothOn g 0 s (Icc 0 T) w)
    (hwdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (w t) x ∈ Φ.dom 0 t x) :
    ∃ δ > 0, ∃ 𝒩 : Λ × ParabolicSpace g s p m T → ParabolicSpace g s p (m - 1) T,
      ContDiffAt ℝ ∞ 𝒩 (0, ofSmooth w hw) ∧
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
  exact ParamNemytskii.exists_nonlinOp_param_aux Φ hp hT hTD hN hw hwdom

end ShortTime
