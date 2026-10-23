import ShortTime.Nonlinear.FibreCalcBound
import ShortTime.Analysis.ParamIntegralManifold
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The Taylor remainder of a fibre map

For a fibre map `F` and `k ∈ ℕ`, the **Taylor remainder**
`Q_k(ζ, η; η', η'', η⃗) = ∫₀¹ (1 - τ) D^{k+2}_ζ F(ζ + τη)[η', η'', η⃗] dτ`
is a fibre map (`FibreMap.taylorMap`) on the inputs `(ι ⊕ ι) ⊕ (Fin (k+2) × ι)`, defined on
`{ζ + τη ∈ dom for all τ ∈ [0,1]}` and multilinear in the `k + 2` blocks. By Taylor's formula
(`taylor_iteratedFDeriv`, `derivF_taylor`),
`G_k(ζ + η)[η⃗] - G_k(ζ)[η⃗] - G_{k+1}(ζ)[η, η⃗] = Q_k(ζ, η; η, η, η⃗)`.

* `taylor_iteratedFDeriv`: Taylor's formula with integral remainder for iterated derivatives in a
  normed space, along a segment in an open set where the map is smooth.
* `contMDiffOn_integral_slab`: smoothness of `q ↦ ∫₀¹ f(q, σ) dσ` on a set
  `{q ∈ O | t ∈ [0, T₀]}` of `Λ × ℝ × M × Z` (from `contMDiffOn_integral_Icc`).
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter Topology MeasureTheory
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Elliptic
open scoped Manifold ContDiff BigOperators

universe u uΛ uZ

namespace ShortTime

/-! ### Taylor's formula in a normed space -/

section ModelTaylor

variable {Z Y : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

theorem hasDerivAt_iteratedFDeriv_line {f : Z → Y} {O : Set Z} (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ f O) {z w : Z} {τ : ℝ} (hτ : z + τ • w ∈ O) (j : ℕ) (v : Fin j → Z) :
    HasDerivAt (fun σ : ℝ => iteratedFDeriv ℝ j f (z + σ • w) v)
      (iteratedFDeriv ℝ (j + 1) f (z + τ • w) (Fin.cons w v)) τ := by
  have hfa : ContDiffAt ℝ ∞ f (z + τ • w) := hf.contDiffAt (hO.mem_nhds hτ)
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ j f) (z + τ • w) :=
    hfa.differentiableAt_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top j)
  have hg : HasDerivAt (fun σ : ℝ => z + σ • w) w τ := by
    simpa using ((hasDerivAt_id τ).smul_const w).const_add z
  have h1 := hd.hasFDerivAt.comp_hasDerivAt τ hg
  have h2 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Z) Y v).hasFDerivAt.comp_hasDerivAt
    τ h1
  have e : iteratedFDeriv ℝ (j + 1) f (z + τ • w) (Fin.cons w v) =
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Z) Y v)
        (fderiv ℝ (iteratedFDeriv ℝ j f) (z + τ • w) w) := by
    rw [iteratedFDeriv_succ_apply_left]
    simp only [Fin.cons_zero, Fin.tail_cons, ContinuousMultilinearMap.apply_apply]
  rw [e]
  exact h2

/-- **Taylor's formula with integral remainder** for iterated derivatives along a segment. -/
theorem taylor_iteratedFDeriv [CompleteSpace Y] {f : Z → Y} {O : Set Z} (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ f O) {z w : Z} (hseg : ∀ τ ∈ Icc (0 : ℝ) 1, z + τ • w ∈ O) (k : ℕ)
    (v : Fin k → Z) :
    iteratedFDeriv ℝ k f (z + w) v - iteratedFDeriv ℝ k f z v -
        iteratedFDeriv ℝ (k + 1) f z (Fin.cons w v) =
      ∫ τ in (0 : ℝ)..1, (1 - τ) • iteratedFDeriv ℝ (k + 2) f (z + τ • w) (Fin.cons w (Fin.cons w v)) := by
  have hd : ∀ (j : ℕ) (v : Fin j → Z), ∀ τ ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun σ : ℝ => iteratedFDeriv ℝ j f (z + σ • w) v)
        (iteratedFDeriv ℝ (j + 1) f (z + τ • w) (Fin.cons w v)) τ := by
    intro j v τ hτ
    rw [uIcc_of_le zero_le_one] at hτ
    exact hasDerivAt_iteratedFDeriv_line hO hf (hseg τ hτ) j v
  have hc : ∀ (j : ℕ) (v : Fin j → Z),
      ContinuousOn (fun σ : ℝ => iteratedFDeriv ℝ j f (z + σ • w) v) (uIcc (0 : ℝ) 1) := by
    intro j v τ hτ
    exact (hd j v τ hτ).continuousAt.continuousWithinAt
  have ibp := intervalIntegral.integral_smul_deriv_eq_deriv_smul (a := 0) (b := 1)
    (u := fun τ : ℝ => 1 - τ) (u' := fun _ => (-1 : ℝ))
    (v := fun σ : ℝ => iteratedFDeriv ℝ (k + 1) f (z + σ • w) (Fin.cons w v))
    (v' := fun σ : ℝ => iteratedFDeriv ℝ (k + 2) f (z + σ • w) (Fin.cons w (Fin.cons w v)))
    (fun τ _ => by simpa using (hasDerivAt_id τ).const_sub (1 : ℝ))
    (fun τ hτ => hd (k + 1) (Fin.cons w v) τ hτ) intervalIntegrable_const
    ((hc (k + 2) (Fin.cons w (Fin.cons w v))).intervalIntegrable)
  have ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ hτ => hd k v τ hτ)
    ((hc (k + 1) (Fin.cons w v)).intervalIntegrable)
  rw [ibp]
  simp only [sub_self, zero_smul, one_smul, sub_zero, zero_sub, neg_one_smul,
    intervalIntegral.integral_neg, ftc, add_zero]
  abel

end ModelTaylor

/-! ### Smoothness of parametric integrals on a slab -/

section Integral

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]

theorem continuousLinearEquiv_intervalIntegral {F F' : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [CompleteSpace F'] (L : F ≃L[ℝ] F') (f : ℝ → F) (a b : ℝ) :
    L (∫ τ in a..b, f τ) = ∫ τ in a..b, L (f τ) := by
  simp only [intervalIntegral, L.integral_comp_comm, map_sub]

/-- **Smoothness of `q ↦ ∫₀¹ f(q, σ) dσ`** on `{q ∈ O | t ∈ [0, T₀]}` in `Λ × ℝ × M × Z`. -/
theorem contMDiffOn_integral_slab {Λ : Type uΛ} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ]
    {Z : Type uZ} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {O : Set (Λ × ℝ × M × Z)} (hO : IsOpen O) {T₀ : ℝ} {f : Λ × ℝ × M × Z → ℝ → Y}
    (hf : ContMDiffOn ((𝓘(ℝ, Λ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, Z)))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Y) ∞
      (fun p : (Λ × ℝ × M × Z) × ℝ => f p.1 p.2)
      ({q | q ∈ O ∧ q.2.1 ∈ Icc 0 T₀} ×ˢ Icc (0 : ℝ) 1)) :
    ContMDiffOn (𝓘(ℝ, Λ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, Z)))) 𝓘(ℝ, Y) ∞
      (fun q => ∫ σ in (0 : ℝ)..1, f q σ) {q | q ∈ O ∧ q.2.1 ∈ Icc 0 T₀} := by
  set A := {q : Λ × ℝ × M × Z | q ∈ O ∧ q.2.1 ∈ Icc 0 T₀} with hA_def
  let r : (Λ × M × Z) × ℝ → Λ × ℝ × M × Z := fun p => (p.1.1, p.2, p.1.2.1, p.1.2.2)
  let ψ : Λ × ℝ × M × Z → (Λ × M × Z) × ℝ := fun q => ((q.1, q.2.2.1, q.2.2.2), q.2.1)
  have hr : ContMDiff ((𝓘(ℝ, Λ).prod (I.prod 𝓘(ℝ, Z))).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, Λ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, Z)))) ∞ r :=
    (contMDiff_fst.comp contMDiff_fst).prodMk (contMDiff_snd.prodMk
      ((contMDiff_fst.comp (contMDiff_snd.comp contMDiff_fst)).prodMk
        (contMDiff_snd.comp (contMDiff_snd.comp contMDiff_fst))))
  have hψ : ContMDiff (𝓘(ℝ, Λ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, Z))))
      ((𝓘(ℝ, Λ).prod (I.prod 𝓘(ℝ, Z))).prod 𝓘(ℝ, ℝ)) ∞ ψ :=
    (contMDiff_fst.prodMk ((contMDiff_fst.comp (contMDiff_snd.comp contMDiff_snd)).prodMk
      (contMDiff_snd.comp (contMDiff_snd.comp contMDiff_snd)))).prodMk
      (contMDiff_fst.comp contMDiff_snd)
  let Lu : ULift.{max uΛ uZ} Y ≃ₗᵢ[ℝ] Y := LinearIsometryEquiv.ulift ℝ Y
  have hLu : ∀ (F : ℝ → Y), ∫ σ in (0 : ℝ)..1, F σ = Lu (∫ σ in (0 : ℝ)..1, Lu.symm (F σ)) := by
    intro F
    have h := Lu.symm.toLinearIsometry.intervalIntegral_comp_comm (a := 0) (b := 1) (μ := volume) F
    change ∫ σ in (0 : ℝ)..1, Lu.symm (F σ) = Lu.symm (∫ σ in (0 : ℝ)..1, F σ) at h
    rw [h, Lu.apply_symm_apply]
  have hLc : ContDiff ℝ ∞ (fun y : ULift.{max uΛ uZ} Y => Lu y) := Lu.contDiff
  have hLc' : ContDiff ℝ ∞ (fun y : Y => Lu.symm y) := Lu.symm.contDiff
  by_cases hT : 0 < T₀
  · intro q₀ hq₀
    have hrc : Continuous r := hr.continuous
    obtain ⟨W, S₀, hW, hmW, hS₀, htS₀, hWS⟩ :=
      mem_nhds_prod_iff'.mp ((hO.preimage hrc).mem_nhds (show r (ψ q₀) ∈ O from hq₀.1))
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hS₀ _ htS₀
    set t₀ := q₀.2.1 with ht₀
    have ht₀I : t₀ ∈ Icc 0 T₀ := hq₀.2
    set S := Icc (max 0 (t₀ - ε / 2)) (min T₀ (t₀ + ε / 2)) with hS_def
    have hSsub : ∀ s ∈ S, s ∈ Icc 0 T₀ ∧ s ∈ S₀ := by
      intro s hs
      refine ⟨⟨le_trans (le_max_left _ _) hs.1, hs.2.trans (min_le_left _ _)⟩, hball ?_⟩
      have h1 := le_trans (le_max_right _ _) hs.1
      have h2 := hs.2.trans (min_le_right _ _)
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hab : max 0 (t₀ - ε / 2) < min T₀ (t₀ + ε / 2) := by
      rw [max_lt_iff, lt_min_iff, lt_min_iff]
      exact ⟨⟨hT, by linarith [ht₀I.1]⟩, ⟨by linarith [ht₀I.2], by linarith⟩⟩
    have hmap : ContMDiff (((𝓘(ℝ, Λ).prod (I.prod 𝓘(ℝ, Z))).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ))
        ((𝓘(ℝ, Λ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, Z)))).prod 𝓘(ℝ, ℝ)) ∞
        (fun p : ((Λ × M × Z) × ℝ) × ℝ => (r p.1, p.2)) :=
      (hr.comp contMDiff_fst).prodMk contMDiff_snd
    have hmaps : MapsTo (fun p : ((Λ × M × Z) × ℝ) × ℝ => (r p.1, p.2))
        ((W ×ˢ S) ×ˢ Icc (0 : ℝ) 1) (A ×ˢ Icc (0 : ℝ) 1) := by
      rintro ⟨⟨m, s⟩, σ⟩ ⟨⟨hm, hs⟩, hσ⟩
      exact ⟨⟨hWS (mk_mem_prod hm (hSsub s hs).2), (hSsub s hs).1⟩, hσ⟩
    have hf' : ContMDiffOn (((𝓘(ℝ, Λ).prod (I.prod 𝓘(ℝ, Z))).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ))
        𝓘(ℝ, ULift.{max uΛ uZ} Y) ∞
        (fun p : ((Λ × M × Z) × ℝ) × ℝ => Lu.symm (f (r (p.1.1, p.1.2)) p.2))
        ((W ×ˢ S) ×ˢ Icc (0 : ℝ) 1) :=
      hLc'.contMDiff.comp_contMDiffOn (hf.comp hmap.contMDiffOn hmaps)
    have hG := contMDiffOn_integral_Icc (I := 𝓘(ℝ, Λ).prod (I.prod 𝓘(ℝ, Z))) hW (convex_Icc _ _)
      (uniqueDiffOn_Icc hab) (f := fun m s σ => Lu.symm (f (r (m, s)) σ)) hf'
    have hmaps2 : MapsTo ψ (A ∩ ψ ⁻¹' (W ×ˢ Metric.ball t₀ (ε / 2))) (W ×ˢ S) := by
      rintro q ⟨hqA, hqm, hqb⟩
      refine ⟨hqm, ?_⟩
      have hb : |q.2.1 - t₀| < ε / 2 := by
        have := hqb
        rwa [Metric.mem_ball, Real.dist_eq] at this
      rw [abs_lt] at hb
      exact ⟨max_le hqA.2.1 (by linarith), le_min hqA.2.2 (by linarith)⟩
    have hcomp := hLc.contMDiff.comp_contMDiffOn (hG.comp hψ.contMDiffOn hmaps2)
    have hnhds : A ∩ ψ ⁻¹' (W ×ˢ Metric.ball t₀ (ε / 2)) ∈ 𝓝[A] q₀ :=
      inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds
        (hψ.continuous.continuousAt.preimage_mem_nhds
          ((hW.prod Metric.isOpen_ball).mem_nhds ⟨hmW, Metric.mem_ball_self (half_pos hε)⟩)))
    refine ((hcomp q₀ ⟨hq₀, hmW, Metric.mem_ball_self (half_pos hε)⟩).congr (fun q _ => ?_)
      ?_).mono_of_mem_nhdsWithin hnhds
    · exact hLu _
    · exact hLu _
  · have hT0 : ∀ q ∈ A, T₀ = 0 ∧ q.2.1 = 0 := fun q hq => by
      have h1 := hq.2.1
      have h2 := hq.2.2
      constructor <;> linarith
    have hrc : Continuous fun m : Λ × M × Z => r (m, 0) :=
      hr.continuous.comp (continuous_id.prodMk continuous_const)
    set W := {m : Λ × M × Z | r (m, 0) ∈ O} with hW_def
    have hW : IsOpen W := hO.preimage hrc
    intro q₀ hq₀
    have hTz : T₀ = 0 := (hT0 q₀ hq₀).1
    have hmap : ContMDiff (((𝓘(ℝ, Λ).prod (I.prod 𝓘(ℝ, Z))).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ))
        ((𝓘(ℝ, Λ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, Z)))).prod 𝓘(ℝ, ℝ)) ∞
        (fun p : ((Λ × M × Z) × ℝ) × ℝ => (r (p.1.1, 0), p.2)) :=
      (hr.comp ((contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_const)).prodMk contMDiff_snd
    have hmaps : MapsTo (fun p : ((Λ × M × Z) × ℝ) × ℝ => (r (p.1.1, 0), p.2))
        ((W ×ˢ univ) ×ˢ Icc (0 : ℝ) 1) (A ×ˢ Icc (0 : ℝ) 1) := by
      rintro ⟨⟨m, s⟩, σ⟩ ⟨⟨hm, -⟩, hσ⟩
      refine ⟨⟨hm, ?_⟩, hσ⟩
      change (0 : ℝ) ∈ Icc 0 T₀
      rw [hTz]
      exact ⟨le_rfl, le_rfl⟩
    have hf' : ContMDiffOn (((𝓘(ℝ, Λ).prod (I.prod 𝓘(ℝ, Z))).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ))
        𝓘(ℝ, ULift.{max uΛ uZ} Y) ∞
        (fun p : ((Λ × M × Z) × ℝ) × ℝ => Lu.symm (f (r (p.1.1, 0)) p.2))
        ((W ×ˢ univ) ×ˢ Icc (0 : ℝ) 1) :=
      hLc'.contMDiff.comp_contMDiffOn (hf.comp hmap.contMDiffOn hmaps)
    have hG := contMDiffOn_integral_Icc (I := 𝓘(ℝ, Λ).prod (I.prod 𝓘(ℝ, Z))) hW convex_univ
      uniqueDiffOn_univ (f := fun m _ σ => Lu.symm (f (r (m, 0)) σ)) hf'
    have hmaps2 : MapsTo ψ A (W ×ˢ univ) := by
      intro q hq
      refine ⟨?_, mem_univ _⟩
      have e : r ((ψ q).1, 0) = q := by
        obtain ⟨l, t, y, z⟩ := q
        have : t = 0 := (hT0 _ hq).2
        subst this
        rfl
      change r ((ψ q).1, 0) ∈ O
      rw [e]
      exact hq.1
    have hcomp := hLc.contMDiff.comp_contMDiffOn (hG.comp hψ.contMDiffOn hmaps2)
    refine (hcomp.congr fun q hq => ?_) q₀ hq₀
    have e : r ((ψ q).1, 0) = q := by
      obtain ⟨l, t, y, z⟩ := q
      have : t = 0 := (hT0 _ hq).2
      subst this
      rfl
    rw [hLu]
    simp only [Function.comp_apply, e]

end Integral

/-! ### The Taylor remainder as a fibre map -/

section Remainder

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

variable {ι : Type*} [Fintype ι]

/-- The ranks of a pair of tuples `(ζ, η)`. -/
abbrev pairRanks (b : ι → ℕ) : ι ⊕ ι → ℕ := Sum.elim b b

variable {b : ι → ℕ}

/-- The first tuple of a pair. -/
def pfst {x : M} (W : ProdFiber I (pairRanks b) x) : ProdFiber I b x := fun c => W (.inl c)

/-- The second tuple of a pair. -/
def psnd {x : M} (W : ProdFiber I (pairRanks b) x) : ProdFiber I b x := fun c => W (.inr c)

/-- The first tuple of a pair, in model coordinates. -/
def mfst (z : ProdModel E (pairRanks b)) : ProdModel E b := fun c => z (.inl c)

/-- The second tuple of a pair, in model coordinates. -/
def msnd (z : ProdModel E (pairRanks b)) : ProdModel E b := fun c => z (.inr c)

theorem prodBase_taylorRanks (b' k : ℕ) (x₀ : M) :
    prodBase (I := I) (blkRanks (pairRanks b) b k) b' x₀ = prodBase (I := I) b b' x₀ := by
  ext y
  simp only [prodBase, mem_inter_iff, mem_iInter]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, fun c => h₂ (.inl (.inl c))⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨h₁, fun q => ?_⟩
    rcases q with (c | c) | ⟨l, c⟩
    · exact h₂ c
    · exact h₂ c
    · exact h₂ c

theorem prodOfModel_add_smul (x₀ y : M) (z z' : ProdModel E b) (τ : ℝ) :
    prodOfModel (I := I) b x₀ y (z + τ • z') = prodOfModel b x₀ y z + τ • prodOfModel b x₀ y z' := by
  funext c
  simp only [prodOfModel, Pi.add_apply, Pi.smul_apply, map_add, map_smul]

/-- The point of the segment at `τ`, in the coordinates at `x₀`. -/
def taylorPt {Λ : Type*} {k : ℕ} (q : Λ × ℝ × M × ProdModel E (blkRanks (pairRanks b) b k))
    (τ : ℝ) : Λ × ℝ × M × ProdModel E b :=
  (q.1, q.2.1, q.2.2.1, mfst (mbase q.2.2.2) + τ • msnd (mbase q.2.2.2))

theorem contDiff_seg {k : ℕ} :
    ContDiff ℝ ∞ (fun p : ProdModel E (blkRanks (pairRanks b) b k) × ℝ =>
      mfst (mbase p.1) + p.2 • msnd (mbase p.1)) := by
  have h1 : ContDiff ℝ ∞ (fun z : ProdModel E (blkRanks (pairRanks b) b k) => mfst (mbase z)) :=
    contDiff_pi.mpr fun c => (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun q => TensorRSModel 0 (blkRanks (pairRanks b) b k q) ℝ E) (.inl (.inl c))).contDiff
  have h2 : ContDiff ℝ ∞ (fun z : ProdModel E (blkRanks (pairRanks b) b k) => msnd (mbase z)) :=
    contDiff_pi.mpr fun c => (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun q => TensorRSModel 0 (blkRanks (pairRanks b) b k q) ℝ E) (.inl (.inr c))).contDiff
  exact (h1.comp contDiff_fst).add (contDiff_snd.smul (h2.comp contDiff_fst))

theorem contMDiff_taylorPt {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] {k : ℕ} :
    ContMDiff ((𝓘(ℝ, Λ).prod (𝓘(ℝ, ℝ).prod
        (I.prod 𝓘(ℝ, ProdModel E (blkRanks (pairRanks b) b k))))).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, Λ).prod (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, ProdModel E b)))) ∞
      (fun p : (Λ × ℝ × M × ProdModel E (blkRanks (pairRanks b) b k)) × ℝ => taylorPt p.1 p.2) := by
  have hs : ContMDiff ((𝓘(ℝ, Λ).prod (𝓘(ℝ, ℝ).prod
        (I.prod 𝓘(ℝ, ProdModel E (blkRanks (pairRanks b) b k))))).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, ProdModel E (blkRanks (pairRanks b) b k) × ℝ) ∞
      (fun p : (Λ × ℝ × M × ProdModel E (blkRanks (pairRanks b) b k)) × ℝ => (p.1.2.2.2, p.2)) :=
    ((contMDiff_snd.comp (contMDiff_snd.comp (contMDiff_snd.comp contMDiff_fst))).prodMk_space
      contMDiff_snd)
  exact (contMDiff_fst.comp contMDiff_fst).prodMk ((contMDiff_fst.comp (contMDiff_snd.comp
    contMDiff_fst)).prodMk ((contMDiff_fst.comp (contMDiff_snd.comp (contMDiff_snd.comp
      contMDiff_fst))).prodMk ((contDiff_seg (E := E) (b := b) (k := k)).contMDiff.comp hs)))

theorem isOpen_setOf_forall_Icc {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {U : Set Y} (hU : IsOpen U) {φ : X → ℝ → Y} (hφ : Continuous fun p : X × ℝ => φ p.1 p.2) :
    IsOpen {x | ∀ τ ∈ Icc (0 : ℝ) 1, φ x τ ∈ U} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  exact isCompact_Icc.eventually_forall_of_forall_eventually fun τ hτ =>
    hφ.continuousAt.preimage_mem_nhds (hU.mem_nhds (hx τ hτ))

namespace FibreMap

variable {Λ : Type uΛ} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] {b' : ℕ}

/-- `Q_k(ζ, η; η', η'', η⃗) = ∫₀¹ (1 - τ) D^{k+2}_ζ F(ζ + τη)[η', η'', η⃗] dτ`, in model
coordinates of the fibres. -/
def taylorF (Φ : FibreMap I M Λ b b') (k : ℕ) (lam : Λ) (t : ℝ) (x : M)
    (V : ProdFiber I (blkRanks (pairRanks b) b (k + 2)) x) : TensorRSSpace 0 b' I x :=
  (fibL I b' x).symm (∫ τ in (0 : ℝ)..1, (1 - τ) • iteratedFDeriv ℝ (k + 2) (Φ.modelRep lam t x)
    (prodL I b x (pfst (fbase V)) + τ • prodL I b x (psnd (fbase V)))
      fun l => prodL I b x (fblk V l))

/-- The domain of the Taylor remainder: the segment `ζ + [0,1] η` lies in the domain. -/
def taylorDom (Φ : FibreMap I M Λ b b') (k : ℕ) (lam : Λ) (t : ℝ) (x : M) :
    Set (ProdFiber I (blkRanks (pairRanks b) b (k + 2)) x) :=
  {V | ∀ τ ∈ Icc (0 : ℝ) 1, pfst (fbase V) + τ • psnd (fbase V) ∈ Φ.dom lam t x}

theorem mem_relOpen_iff (Φ : FibreMap I M Λ b b') (x₀ : M) {q : Λ × ℝ × M × ProdModel E b}
    (hq : q ∈ prodSlab (I := I) Λ b b' Φ.T₀ x₀) :
    prodOfModel b x₀ q.2.2.1 q.2.2.2 ∈ Φ.dom q.1 q.2.1 q.2.2.1 ↔ q ∈ (Φ.dom_relOpen x₀).choose := by
  have h := Set.ext_iff.mp (Φ.dom_relOpen x₀).choose_spec.2 q
  exact ⟨fun hd => (h.mp ⟨hq, hd⟩).1, fun hU => (h.mpr ⟨hU, hq⟩).2⟩

/-- The open set of `q` whose segment lies in the open set of `Φ.dom_relOpen`. -/
def taylorU (Φ : FibreMap I M Λ b b') (k : ℕ) (x₀ : M) :
    Set (Λ × ℝ × M × ProdModel E (blkRanks (pairRanks b) b (k + 2))) :=
  {q | ∀ τ ∈ Icc (0 : ℝ) 1, taylorPt q τ ∈ (Φ.dom_relOpen x₀).choose}

theorem isOpen_taylorU (Φ : FibreMap I M Λ b b') (k : ℕ) (x₀ : M) :
    IsOpen (Φ.taylorU k x₀) :=
  isOpen_setOf_forall_Icc (Φ.dom_relOpen x₀).choose_spec.1
    (contMDiff_taylorPt (I := I) (Λ := Λ) (b := b) (k := k + 2)).continuous

theorem mem_taylorDomSet_iff (Φ : FibreMap I M Λ b b') (k : ℕ) (x₀ : M)
    (q : Λ × ℝ × M × ProdModel E (blkRanks (pairRanks b) b (k + 2))) :
    (q ∈ prodSlab (I := I) Λ (blkRanks (pairRanks b) b (k + 2)) b' Φ.T₀ x₀ ∧
      prodOfModel (blkRanks (pairRanks b) b (k + 2)) x₀ q.2.2.1 q.2.2.2 ∈
        Φ.taylorDom k q.1 q.2.1 q.2.2.1) ↔
      q ∈ Φ.taylorU k x₀ ∧ q.2.1 ∈ Icc 0 Φ.T₀ ∧ q.2.2.1 ∈ prodBase (I := I) b b' x₀ := by
  have hslab : ∀ τ : ℝ, q.2.1 ∈ Icc 0 Φ.T₀ → q.2.2.1 ∈ prodBase (I := I) b b' x₀ →
      taylorPt q τ ∈ prodSlab (I := I) Λ b b' Φ.T₀ x₀ := fun τ ht hy => ⟨ht, hy⟩
  have hpt : ∀ τ : ℝ,
      pfst (fbase (prodOfModel (I := I) (blkRanks (pairRanks b) b (k + 2)) x₀ q.2.2.1 q.2.2.2)) +
        τ • psnd (fbase (prodOfModel (I := I) (blkRanks (pairRanks b) b (k + 2)) x₀ q.2.2.1
          q.2.2.2)) = prodOfModel b x₀ q.2.2.1 (taylorPt q τ).2.2.2 := fun τ =>
    (prodOfModel_add_smul x₀ q.2.2.1 _ _ τ).symm
  simp only [prodSlab, mem_ofPred_eq, prodBase_taylorRanks, taylorDom, hpt]
  constructor
  · rintro ⟨⟨ht, hy⟩, hd⟩
    exact ⟨fun τ hτ => (Φ.mem_relOpen_iff x₀ (hslab τ ht hy)).mp (hd τ hτ), ht, hy⟩
  · rintro ⟨hU, ht, hy⟩
    exact ⟨⟨ht, hy⟩, fun τ hτ => (Φ.mem_relOpen_iff x₀ (hslab τ ht hy)).mpr (hU τ hτ)⟩

/-- The Taylor remainder read at `x₀` is the integral of the coordinate derivatives of the
representative. -/
theorem rep_taylorF (Φ : FibreMap I M Λ b b') (k : ℕ) {x₀ y : M}
    (hy : y ∈ prodBase (I := I) b b' x₀) (lam : Λ) (t : ℝ)
    (Z : ProdModel E (blkRanks (pairRanks b) b (k + 2))) :
    (trivAt I M 0 b' x₀).continuousLinearMapAt ℝ y
        (Φ.taylorF k lam t y (prodOfModel (blkRanks (pairRanks b) b (k + 2)) x₀ y Z)) =
      ∫ σ in (0 : ℝ)..1, (1 - σ) • iteratedFDeriv ℝ (k + 2) (fun z => Φ.rep x₀ (lam, t, y, z))
        (mfst (mbase Z) + σ • msnd (mbase Z)) (mblk Z) := by
  rw [taylorF, ← chgA_apply hy, continuousLinearEquiv_intervalIntegral]
  refine intervalIntegral.integral_congr fun σ _ => ?_
  simp only [map_smul, iteratedFDeriv_rep Φ hy, map_add, chgB_apply]
  rfl

/-- **The Taylor remainder** `Q_k` as a fibre map on `(ι ⊕ ι) ⊕ (Fin (k+2) × ι)`. -/
def taylorMap (Φ : FibreMap I M Λ b b') (k : ℕ) :
    FibreMap I M Λ (blkRanks (pairRanks b) b (k + 2)) b' where
  T₀ := Φ.T₀
  dom := Φ.taylorDom k
  F := Φ.taylorF k
  dom_relOpen x₀ := by
    refine ⟨Φ.taylorU k x₀, Φ.isOpen_taylorU k x₀, ?_⟩
    ext q
    have h := Φ.mem_taylorDomSet_iff k x₀ q
    simp only [mem_inter_iff]
    constructor
    · intro hq
      have h' := h.mp hq
      exact ⟨h'.1, hq.1⟩
    · intro hq
      have hy : q.2.2.1 ∈ prodBase (I := I) b b' x₀ := by
        have := hq.2.2
        rwa [prodBase_taylorRanks] at this
      exact ⟨hq.2, (h.mpr ⟨hq.1, hq.2.1, hy⟩).2⟩
  smooth x₀ := by
    obtain ⟨U, hU, hS⟩ := Φ.exists_domSet_eq x₀
    have hsm := Φ.smooth_rep x₀
    rw [hS] at hsm
    have hD := contMDiffOn_iteratedFDeriv_fibre (f := Φ.rep x₀)
      (P := fun _ t y => t ∈ Icc 0 Φ.T₀ ∧ y ∈ prodBase (I := I) b b' x₀) hU hsm (k + 2)
    rw [← hS] at hD
    set O := Φ.taylorU k x₀ ∩ {q | q.2.2.1 ∈ prodBase (I := I) b b' x₀} with hO_def
    have hO : IsOpen O := (Φ.isOpen_taylorU k x₀).inter
      ((prodBase_isOpen (I := I) b b' x₀).preimage
        (continuous_fst.comp (continuous_snd.comp continuous_snd)))
    have hset : {q ∈ prodSlab (I := I) Λ (blkRanks (pairRanks b) b (k + 2)) b' Φ.T₀ x₀ |
        prodOfModel (blkRanks (pairRanks b) b (k + 2)) x₀ q.2.2.1 q.2.2.2 ∈
          Φ.taylorDom k q.1 q.2.1 q.2.2.1} = {q | q ∈ O ∧ q.2.1 ∈ Icc 0 Φ.T₀} := by
      ext q
      rw [mem_ofPred_eq, Φ.mem_taylorDomSet_iff k x₀ q]
      exact ⟨fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩, fun h => ⟨h.1.1, h.2, h.1.2⟩⟩
    -- the integrand
    have hmaps : MapsTo (fun p : (Λ × ℝ × M × ProdModel E (blkRanks (pairRanks b) b (k + 2))) × ℝ =>
        taylorPt p.1 p.2) ({q | q ∈ O ∧ q.2.1 ∈ Icc 0 Φ.T₀} ×ˢ Icc (0 : ℝ) 1) (Φ.domSet x₀) := by
      rintro ⟨q, σ⟩ ⟨⟨⟨hU', hy⟩, ht⟩, hσ⟩
      exact ⟨⟨ht, hy⟩, (Φ.mem_relOpen_iff x₀ (q := taylorPt q σ) ⟨ht, hy⟩).mpr (hU' σ hσ)⟩
    have h1 := hD.comp contMDiff_taylorPt.contMDiffOn hmaps
    have h2 : ContMDiff ((𝓘(ℝ, Λ).prod (𝓘(ℝ, ℝ).prod
          (I.prod 𝓘(ℝ, ProdModel E (blkRanks (pairRanks b) b (k + 2)))))).prod 𝓘(ℝ, ℝ))
        𝓘(ℝ, Fin (k + 2) → ProdModel E b) ∞
        (fun p : (Λ × ℝ × M × ProdModel E (blkRanks (pairRanks b) b (k + 2))) × ℝ =>
          fun l => mblk p.1.2.2.2 l) :=
      (contDiff_mblk (E := E) (a := pairRanks b) (b₀ := b) (k := k + 2)).contMDiff.comp
        (contMDiff_snd.comp (contMDiff_snd.comp (contMDiff_snd.comp contMDiff_fst)))
    have h3 := contDiff_multilinear_eval.contMDiff.comp_contMDiffOn
      (h1.prodMk_space h2.contMDiffOn)
    have h4 : ContMDiff ((𝓘(ℝ, Λ).prod (𝓘(ℝ, ℝ).prod
          (I.prod 𝓘(ℝ, ProdModel E (blkRanks (pairRanks b) b (k + 2)))))).prod 𝓘(ℝ, ℝ))
        𝓘(ℝ, ℝ) ∞
        (fun p : (Λ × ℝ × M × ProdModel E (blkRanks (pairRanks b) b (k + 2))) × ℝ => 1 - p.2) :=
      (contDiff_const.sub contDiff_id).contMDiff.comp contMDiff_snd
    have h5 := contDiff_smul.contMDiff.comp_contMDiffOn (h4.contMDiffOn.prodMk_space h3)
    have hI := contMDiffOn_integral_slab (T₀ := Φ.T₀) (f := fun q σ => (1 - σ) •
      iteratedFDeriv ℝ (k + 2) (fun z => Φ.rep x₀ (q.1, q.2.1, q.2.2.1, z))
        (mfst (mbase q.2.2.2) + σ • msnd (mbase q.2.2.2)) (mblk q.2.2.2)) hO h5
    rw [hset]
    refine hI.congr fun q hq => ?_
    exact rep_taylorF Φ k hq.1.2 q.1 q.2.1 q.2.2.2

@[simp] theorem taylorMap_F (Φ : FibreMap I M Λ b b') (k : ℕ) :
    (Φ.taylorMap k).F = Φ.taylorF k := rfl

@[simp] theorem taylorMap_dom (Φ : FibreMap I M Λ b b') (k : ℕ) :
    (Φ.taylorMap k).dom = Φ.taylorDom k := rfl

/-- The Taylor remainder is multilinear in its `k + 2` blocks. -/
theorem isBlockMultilinear_taylorMap (Φ : FibreMap I M Λ b b') (k : ℕ) :
    IsBlockMultilinear (Φ.taylorMap k) where
  dom_iff lam t x V V' hV := by
    show (∀ τ ∈ Icc (0 : ℝ) 1, pfst (fbase V) + τ • psnd (fbase V) ∈ Φ.dom lam t x) ↔
      (∀ τ ∈ Icc (0 : ℝ) 1, pfst (fbase V') + τ • psnd (fbase V') ∈ Φ.dom lam t x)
    rw [hV]
  smul lam t x s V := by
    have e : ∀ X, (∏ l, s l) • (fibL I b' x).symm X = (fibL I b' x).symm ((∏ l, s l) • X) :=
      fun X => (map_smul _ _ _).symm
    simp only [taylorMap_F, taylorF, fbase_scaleBlk, fblk_scaleBlk, map_smul]
    rw [e, ← intervalIntegral.integral_smul]
    congr 1
    refine intervalIntegral.integral_congr fun σ _ => ?_
    rw [ContinuousMultilinearMap.map_smul_univ, smul_comm]

end FibreMap

end Remainder

end ShortTime
