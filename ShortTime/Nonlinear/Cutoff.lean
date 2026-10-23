import ShortTime.Linear.TimeCalc
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Parametric.PathIntegralFibreNorm

/-!
# Cutting off a smooth family near `t = 0` (`lem:cutoff`)

Let `f` be a jointly smooth family on `[0,T]` with `∂ₜ^ℓ f(·,0) = 0` for `ℓ < N`, and let `χ` be
smooth with `χ = 0` on `(-∞,1]` and `χ = 1` on `[2,∞)`. Then `f_ε(t) = χ(t/ε) f(t)`
(`cutoffFamily χ ε f`) is jointly smooth, vanishes for `t ≤ ε`, and `f_ε → f` in `𝒫^{m'}` as
`ε → 0⁺` for every `m' ≤ N` (`ParabolicSpace.tendsto_cutoff`).

Proof, as in the paper.
* `Cutoff.timeDerivIter_fun_smul`: the Leibniz rule
  `∂ₜ^n(ψ F) = Σ_{q+r=n} C(n,q) ψ^{(q)} ∂ₜ^r F` for a smooth scalar `ψ`.
* `Cutoff.taylor_bound`: `|∂ₜ^r F(x,t)| ≤ C tᴺ⁻ʳ` (pointwise Riemannian norm), from the vanishing
  of `∂ₜ^l F(·,0)` for `l < N` and a mean value inequality.
* `Cutoff.exists_bound_leibniz`: with `ψ_ε(t) = ψ(t/ε)`, `ψ = 1 - χ`, the derivatives
  `∂ₜ^j(ψ_ε F)` (`j ≤ N`) are bounded uniformly in `ε` and vanish for `t > 2ε`.
* `Cutoff.mixedInner_le`: hence each pairing `∫₀ᵀ ‖∂ₜ^j ∇^i (f - f_ε)‖²` is `O(ε)`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev
open scoped Manifold ContDiff BigOperators

set_option linter.unusedSectionVars false

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

variable {g : SmoothRiemannianMetric I M}

namespace Cutoff

/-! ### Families with a smooth scalar factor -/

/-- `t ↦ a(t) F(t)` is jointly smooth when `a` is smooth and `F` jointly smooth. -/
theorem jointlySmoothOn_fun_smul {k : ℕ} {S : Set ℝ} {a : ℝ → ℝ} (ha : ContDiffOn ℝ ∞ a S)
    {F : ℝ → SmoothCcTensor g 0 k} (hF : JointlySmoothOn g 0 k S F) :
    JointlySmoothOn g 0 k S (fun t => a t • F t) := by
  let := tensorRSBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0 k
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (TensorRSModel 0 k ℝ E)
    (fun z : M => TensorRSSpace 0 k I z) x₀ with he
  have hF' := (Bundle.contMDiffWithinAt_totalSpace (F := TensorRSModel 0 k ℝ E)
    (E := fun z : M => TensorRSSpace 0 k I z)).mp (hF p₀ hp₀)
  have ha' : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun q : M × ℝ => a q.2)
      ((Set.univ : Set M) ×ˢ S) p₀ :=
    (ha p₀.2 hp₀.2).contMDiffWithinAt.comp p₀ contMDiffWithinAt_snd (fun q hq => hq.2)
  refine (ha'.smul hF'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
        p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_smul (a p.2) ((F p.2).toSection p.1)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_smul
      (a p₀.2) ((F p₀.2).toSection p₀.1)

/-- Product rule: `∂ₜ(a F) = a' F + a ∂ₜF` on `[0,T]`. -/
theorem timeDeriv_fun_smul {T : ℝ} (hT : 0 < T) {k : ℕ} {a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a)
    {F : ℝ → SmoothCcTensor g 0 k} (hF : JointlySmoothOn g 0 k (Icc 0 T) F) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    timeDeriv T (fun τ => a τ • F τ) t = deriv a t • F t + a t • timeDeriv T F t := by
  refine timeDeriv_eq hT (jointlySmoothOn_fun_smul ha.contDiffOn hF) ht fun x => ?_
  have hda : HasDerivAt a (deriv a t) t :=
    ((contDiff_infty_iff_deriv.mp ha).1 t).hasDerivAt
  have h := hda.hasDerivWithinAt.smul (hasDerivWithinAt_timeDeriv hT hF ht x)
  have e1 : (fun τ => (a τ • F τ).toFun x) =
      fun τ => a τ • TensorRSSpace.toModel ((F τ).toSection x) := by
    funext τ
    rw [SmoothCcTensor.toFun_smul, Pi.smul_apply]
    rfl
  have e2 : (deriv a t • F t + a t • timeDeriv T F t).toFun x =
      a t • TensorRSSpace.toModel ((timeDeriv T F t).toSection x) +
        deriv a t • TensorRSSpace.toModel ((F t).toSection x) := by
    rw [SmoothCcTensor.toFun_add, Pi.add_apply, SmoothCcTensor.toFun_smul,
      SmoothCcTensor.toFun_smul, Pi.smul_apply, Pi.smul_apply, add_comm]
    rfl
  show HasDerivWithinAt (fun τ => (a τ • F τ).toFun x)
    ((deriv a t • F t + a t • timeDeriv T F t).toFun x) (Icc 0 T) t
  rw [e1, e2]
  exact h

/-- **Leibniz rule** `∂ₜ^n(a F) = Σ_{q+r=n} C(n,q) a^{(q)} ∂ₜ^r F` on `[0,T]`. -/
theorem timeDerivIter_fun_smul {T : ℝ} (hT : 0 < T) {k : ℕ} (n : ℕ) :
    ∀ {a : ℝ → ℝ}, ContDiff ℝ ∞ a → ∀ {F : ℝ → SmoothCcTensor g 0 k},
      JointlySmoothOn g 0 k (Icc 0 T) F → ∀ t ∈ Icc 0 T,
      timeDerivIter T (fun τ => a τ • F τ) n t =
        ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
          n.choose ij.1 • (iteratedDeriv ij.1 a t • timeDerivIter T F ij.2 t) := by
  induction n with
  | zero =>
    intro a _ F _ t _
    simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, Nat.choose_self, one_smul,
      iteratedDeriv_zero]
    rfl
  | succ n ih =>
    intro a ha F hF t ht
    have ha' : ContDiff ℝ ∞ (deriv a) := (contDiff_infty_iff_deriv.mp ha).2
    have hF' := jointlySmoothOn_timeDeriv hT hF
    have hG1 := jointlySmoothOn_fun_smul ha'.contDiffOn hF
    have hG2 := jointlySmoothOn_fun_smul ha.contDiffOn hF'
    have hG := jointlySmoothOn_add hG1 hG2
    rw [timeDerivIter_succ']
    have hcongr := timeDerivIter_congr hT
      (jointlySmoothOn_timeDeriv hT (jointlySmoothOn_fun_smul ha.contDiffOn hF)) hG
      (fun τ hτ => timeDeriv_fun_smul hT ha hF hτ) n ht
    rw [hcongr, timeDerivIter_add hT hG1 hG2 n]
    dsimp only
    rw [ih ha' hF t ht, ih ha hF' t ht]
    refine (add_comm _ _).trans ?_
    rw [Finset.sum_antidiagonal_choose_succ_nsmul
        (fun i j => iteratedDeriv i a t • timeDerivIter T F j t) n]
    congr 1
    · refine Finset.sum_congr rfl fun ij _ => ?_
      rw [← timeDerivIter_succ']
    · refine Finset.sum_congr rfl fun ij hij => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
      rw [← iteratedDeriv_succ', Nat.choose_symm_of_eq_add hij.symm]

/-! ### Pointwise norms -/

theorem toFun_zero (k : ℕ) (x : M) : (0 : SmoothCcTensor g 0 k).toFun x = 0 := by
  have h := SmoothCcTensor.toFun_smul (0 : ℝ) (0 : SmoothCcTensor g 0 k)
  rw [zero_smul, zero_smul] at h
  simp only [h, Pi.zero_apply]

theorem pointwiseNorm_zero (k : ℕ) (x : M) :
    tensorPointwiseNorm (I := I) (M := M) g 0 k x 0 = 0 := by
  have h := tensorPointwiseNorm_smul (I := I) (M := M) g 0 k x 0 0
  rw [zero_smul, abs_zero, zero_mul] at h
  exact h

theorem pointwiseNorm_sum_le {k : ℕ} {ι : Type*} (S : Finset ι) (v : ι → SmoothCcTensor g 0 k)
    (x : M) :
    tensorPointwiseNorm (I := I) (M := M) g 0 k x ((∑ i ∈ S, v i).toFun x) ≤
      ∑ i ∈ S, tensorPointwiseNorm (I := I) (M := M) g 0 k x ((v i).toFun x) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, toFun_zero, pointwiseNorm_zero]
  | insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, SmoothCcTensor.toFun_add, Pi.add_apply]
    exact (tensorPointwiseNorm_add_le (I := I) (M := M) g 0 k x _ _).trans (add_le_add le_rfl ih)

theorem pointwiseNorm_nsmul_smul {k : ℕ} (n : ℕ) (c : ℝ) (v : SmoothCcTensor g 0 k) (x : M) :
    tensorPointwiseNorm (I := I) (M := M) g 0 k x ((n • (c • v)).toFun x) =
      (n : ℝ) * (|c| * tensorPointwiseNorm (I := I) (M := M) g 0 k x (v.toFun x)) := by
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, SmoothCcTensor.toFun_smul, Pi.smul_apply,
    tensorPointwiseNorm_smul, abs_mul, Nat.abs_cast, mul_assoc]

/-- A jointly smooth family is bounded in the pointwise norm on `M × [0,T]`. -/
theorem exists_pointwiseNorm_bound {T : ℝ} {k : ℕ} {F : ℝ → SmoothCcTensor g 0 k}
    (hF : JointlySmoothOn g 0 k (Icc 0 T) F) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Icc 0 T, ∀ x : M,
      tensorPointwiseNorm (I := I) (M := M) g 0 k x ((F t).toFun x) ≤ C := by
  obtain ⟨K, -, hK⟩ := exists_bound_of_jointlySmoothOn hF
  refine ⟨Real.sqrt K, Real.sqrt_nonneg _, fun t ht x => ?_⟩
  have h := hK t ht x
  rw [DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_eq_tensorInnerPointwise] at h
  exact Real.sqrt_le_sqrt h

theorem le_of_sq_le_mul_aux {n B : ℝ} (hB : 0 ≤ B) (h : n ^ 2 ≤ n * B) : n ≤ B := by
  nlinarith

/-- Mean value inequality in the pointwise norm at `x`: if `φ(0) = 0` and `|φ'(τ)| ≤ C τ^d`, then
`|φ(t)| ≤ C t^{d+1}`. -/
theorem pointwiseNorm_le_of_deriv {k : ℕ} (x : M) {φ φ' : ℝ → TensorRSModel 0 k ℝ E} {T C t : ℝ}
    {d : ℕ} (hφ : ∀ τ ∈ Icc 0 T, HasDerivWithinAt φ (φ' τ) (Icc 0 T) τ) (h0 : φ 0 = 0)
    (hb : ∀ τ ∈ Icc 0 T, tensorPointwiseNorm (I := I) (M := M) g 0 k x (φ' τ) ≤ C * τ ^ d)
    (hC : 0 ≤ C) (ht : t ∈ Icc 0 T) :
    tensorPointwiseNorm (I := I) (M := M) g 0 k x (φ t) ≤ C * t ^ (d + 1) := by
  obtain ⟨n, hn⟩ : ∃ n, n = tensorPointwiseNorm (I := I) (M := M) g 0 k x (φ t) := ⟨_, rfl⟩
  rw [← hn]
  have hn0 : 0 ≤ n := hn ▸ tensorPointwiseNorm_nonneg (I := I) (M := M) g 0 k x _
  obtain ⟨L, hL⟩ : ∃ L, L = ptInnerBilin g 0 k x (φ t) := ⟨_, rfl⟩
  have hd : ∀ τ ∈ Icc 0 t, HasDerivWithinAt (fun τ => L (φ τ)) (L (φ' τ)) (Icc 0 t) τ :=
    fun τ hτ => L.hasFDerivAt.comp_hasDerivWithinAt τ
      ((hφ τ ⟨hτ.1, hτ.2.trans ht.2⟩).mono (Icc_subset_Icc le_rfl ht.2))
  have hbd : ∀ τ ∈ Ico 0 t, ‖L (φ' τ)‖ ≤ n * (C * t ^ d) := fun τ hτ => by
    rw [Real.norm_eq_abs, hL, ptInnerBilin_apply]
    refine (abs_tensorInnerPointwise_le_mul (I := I) (M := M) g 0 k x _ _).trans ?_
    rw [← hn]
    refine mul_le_mul_of_nonneg_left ((hb τ ⟨hτ.1, hτ.2.le.trans ht.2⟩).trans ?_) hn0
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hτ.1 hτ.2.le d) hC
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hd hbd t (right_mem_Icc.mpr ht.1)
  have hL0 : L (φ 0) = 0 := by rw [h0, map_zero]
  have hLt : L (φ t) = n ^ 2 := by
    rw [hL, ptInnerBilin_apply, hn]
    unfold tensorPointwiseNorm
    rw [Real.sq_sqrt (tensorInnerPointwise_nonneg (I := I) (M := M) g 0 k x _)]
  rw [hL0, sub_zero, hLt, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sub_zero] at hmv
  have hB : 0 ≤ C * t ^ (d + 1) := mul_nonneg hC (pow_nonneg ht.1 _)
  refine le_of_sq_le_mul_aux hB ?_
  calc n ^ 2 ≤ n * (C * t ^ d) * t := hmv
    _ = n * (C * t ^ (d + 1)) := by rw [pow_succ]; ring

/-- **Taylor bound.** If `∂ₜ^l F(·,0) = 0` for `l < N`, then `|∂ₜ^r F(x,t)| ≤ C t^{N-r}` for
`r ≤ N`. -/
theorem taylor_bound {T : ℝ} (hT : 0 < T) {k N : ℕ} {F : ℝ → SmoothCcTensor g 0 k}
    (hF : JointlySmoothOn g 0 k (Icc 0 T) F) (h0 : ∀ l < N, timeDerivIter T F l 0 = 0) :
    ∀ d r, r + d = N → ∃ C, 0 ≤ C ∧ ∀ t ∈ Icc 0 T, ∀ x : M,
      tensorPointwiseNorm (I := I) (M := M) g 0 k x ((timeDerivIter T F r t).toFun x) ≤
        C * t ^ d
  | 0, r, _ => by
    obtain ⟨C, hC0, hC⟩ := exists_pointwiseNorm_bound (jointlySmoothOn_timeDerivIter hT hF r)
    exact ⟨C, hC0, fun t ht x => by rw [pow_zero, mul_one]; exact hC t ht x⟩
  | d + 1, r, h => by
    obtain ⟨C, hC0, hC⟩ := taylor_bound hT hF h0 d (r + 1) (by omega)
    refine ⟨C, hC0, fun t ht x => ?_⟩
    have hr : timeDerivIter T F r 0 = 0 := h0 r (by omega)
    refine pointwiseNorm_le_of_deriv x (φ := fun τ => (timeDerivIter T F r τ).toFun x)
      (φ' := fun τ => (timeDerivIter T F (r + 1) τ).toFun x)
      (fun τ hτ => hasDerivWithinAt_timeDeriv hT (jointlySmoothOn_timeDerivIter hT hF r) hτ x)
      ?_ (fun τ hτ => hC τ hτ x) hC0 ht
    rw [hr, toFun_zero]

/-- The Taylor bound for every `r`, with exponent `N - r` (truncated subtraction). -/
theorem taylor_bound' {T : ℝ} (hT : 0 < T) {k N : ℕ} {F : ℝ → SmoothCcTensor g 0 k}
    (hF : JointlySmoothOn g 0 k (Icc 0 T) F) (h0 : ∀ l < N, timeDerivIter T F l 0 = 0) (r : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Icc 0 T, ∀ x : M,
      tensorPointwiseNorm (I := I) (M := M) g 0 k x ((timeDerivIter T F r t).toFun x) ≤
        C * t ^ (N - r) := by
  rcases le_or_gt r N with hr | hr
  · exact taylor_bound hT hF h0 (N - r) r (by omega)
  · obtain ⟨C, hC0, hC⟩ := exists_pointwiseNorm_bound (jointlySmoothOn_timeDerivIter hT hF r)
    exact ⟨C, hC0, fun t ht x => by
      rw [show N - r = 0 by omega, pow_zero, mul_one]; exact hC t ht x⟩

/-! ### The rescaled cutoff -/

/-- Derivatives of a smooth function vanishing on `(c, ∞)` vanish there. -/
theorem iteratedDeriv_eq_zero_of_Ioi {φ : ℝ → ℝ} {c : ℝ} (h : ∀ τ, c < τ → φ τ = 0) :
    ∀ q τ, c < τ → iteratedDeriv q φ τ = 0
  | 0, τ, hτ => by rw [iteratedDeriv_zero]; exact h τ hτ
  | q + 1, τ, hτ => by
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv q φ =ᶠ[𝓝 τ] fun _ => 0 :=
      Filter.eventually_of_mem (Ioi_mem_nhds hτ) fun σ hσ =>
        iteratedDeriv_eq_zero_of_Ioi h q σ hσ
    rw [hev.deriv_eq, deriv_const]

theorem cutoff_arith {ε t T B C y a : ℝ} {e q : ℕ} (hε : 0 < ε) (ht0 : 0 ≤ t) (htT : t ≤ T)
    (ht2 : t ≤ 2 * ε) (hB : 0 ≤ B) (hC : 0 ≤ C) (ha : |a| ≤ ε⁻¹ ^ q * B) (hy0 : 0 ≤ y)
    (hy : y ≤ C * t ^ (e + q)) :
    |a| * y ≤ B * C * T ^ e * 2 ^ q := by
  have h1 : |a| * y ≤ (ε⁻¹ ^ q * B) * (C * t ^ (e + q)) :=
    mul_le_mul ha hy hy0 (mul_nonneg (pow_nonneg (inv_nonneg.mpr hε.le) _) hB)
  have h2 : (ε⁻¹ ^ q * B) * (C * t ^ (e + q)) = B * C * t ^ e * (ε⁻¹ * t) ^ q := by
    rw [pow_add, mul_pow]
    ring
  have h3 : ε⁻¹ * t ≤ 2 := by
    rw [inv_mul_le_iff₀ hε]
    linarith
  have h4 : (ε⁻¹ * t) ^ q ≤ 2 ^ q :=
    pow_le_pow_left₀ (mul_nonneg (inv_nonneg.mpr hε.le) ht0) h3 q
  have h5 : t ^ e ≤ T ^ e := pow_le_pow_left₀ ht0 htT e
  calc |a| * y ≤ B * C * t ^ e * (ε⁻¹ * t) ^ q := h2 ▸ h1
    _ ≤ B * C * T ^ e * 2 ^ q := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left h5 (mul_nonneg hB hC)) h4
        (pow_nonneg (mul_nonneg (inv_nonneg.mpr hε.le) ht0) _)
      exact mul_nonneg (mul_nonneg hB hC) (pow_nonneg (ht0.trans htT) _)

/-- **Uniform bound.** For `ψ` smooth with `ψ = 0` on `(2,∞)` and `ψ_ε(t) = ψ(t/ε)`,
the derivatives `∂ₜ^j(ψ_ε F)`, `j ≤ N`, are bounded uniformly in `ε > 0` and vanish for
`t > 2ε`. -/
theorem exists_bound_leibniz {T : ℝ} (hT : 0 < T) {k N j : ℕ} (hj : j ≤ N)
    {F : ℝ → SmoothCcTensor g 0 k} (hF : JointlySmoothOn g 0 k (Icc 0 T) F)
    (hF0 : ∀ l < N, timeDerivIter T F l 0 = 0) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψ2 : ∀ τ, 2 < τ → ψ τ = 0) :
    ∃ K, 0 ≤ K ∧ ∀ ε, 0 < ε → ∀ t ∈ Icc 0 T,
      (∀ x : M, tensorPointwiseNorm (I := I) (M := M) g 0 k x
        ((timeDerivIter T (fun τ => ψ (ε⁻¹ * τ) • F τ) j t).toFun x) ≤ K) ∧
      (2 * ε < t → timeDerivIter T (fun τ => ψ (ε⁻¹ * τ) • F τ) j t = 0) := by
  choose C hC0 hC using taylor_bound' hT hF hF0
  have hBex : ∀ q : ℕ, ∃ B, 0 ≤ B ∧ ∀ τ ∈ Icc (0 : ℝ) 2, |iteratedDeriv q ψ τ| ≤ B := by
    intro q
    obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2)).exists_bound_of_continuousOn
      ((hψ.continuous_iteratedDeriv q (by exact_mod_cast le_top)).continuousOn)
    refine ⟨max B 0, le_max_right _ _, fun τ hτ => ?_⟩
    have h := hB τ hτ
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  choose B hB0 hB using hBex
  refine ⟨∑ ij ∈ Finset.HasAntidiagonal.antidiagonal j,
      (j.choose ij.1 : ℝ) * (B ij.1 * C ij.2 * T ^ (N - j) * 2 ^ ij.1), ?_, ?_⟩
  · exact Finset.sum_nonneg fun ij _ => mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (mul_nonneg (mul_nonneg (hB0 _) (hC0 _)) (pow_nonneg hT.le _))
        (pow_nonneg (by norm_num) _))
  intro ε hε t ht
  have hψε : ContDiff ℝ ∞ (fun τ => ψ (ε⁻¹ * τ)) := hψ.comp (contDiff_const.mul contDiff_id)
  have hder : ∀ q, iteratedDeriv q (fun τ => ψ (ε⁻¹ * τ)) t =
      ε⁻¹ ^ q * iteratedDeriv q ψ (ε⁻¹ * t) := fun q =>
    congrFun (iteratedDeriv_comp_const_mul (n := q) (hψ.of_le (by exact_mod_cast le_top)) ε⁻¹) t
  rw [timeDerivIter_fun_smul hT j hψε hF t ht]
  have hzero : 2 * ε < t → ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal j,
      j.choose ij.1 • (iteratedDeriv ij.1 (fun τ => ψ (ε⁻¹ * τ)) t •
        timeDerivIter T F ij.2 t) = 0 := by
    intro h2
    have h2' : 2 < ε⁻¹ * t := by
      rw [lt_inv_mul_iff₀ hε]
      linarith
    refine Finset.sum_eq_zero fun ij _ => ?_
    rw [hder, iteratedDeriv_eq_zero_of_Ioi hψ2 ij.1 _ h2', mul_zero, zero_smul, smul_zero]
  refine ⟨fun x => ?_, hzero⟩
  rcases le_or_gt t (2 * ε) with h2 | h2
  · refine (pointwiseNorm_sum_le _ _ x).trans (Finset.sum_le_sum fun ij hij => ?_)
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    rw [pointwiseNorm_nsmul_smul]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have hτ : ε⁻¹ * t ∈ Icc (0 : ℝ) 2 := by
      refine ⟨mul_nonneg (inv_nonneg.mpr hε.le) ht.1, ?_⟩
      rw [inv_mul_le_iff₀ hε]
      linarith
    have ha : |iteratedDeriv ij.1 (fun τ => ψ (ε⁻¹ * τ)) t| ≤ ε⁻¹ ^ ij.1 * B ij.1 := by
      rw [hder, abs_mul, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hε.le) _)]
      exact mul_le_mul_of_nonneg_left (hB ij.1 _ hτ) (pow_nonneg (inv_nonneg.mpr hε.le) _)
    have hexp : N - ij.2 = (N - j) + ij.1 := by omega
    have hy := hC ij.2 t ht x
    rw [hexp] at hy
    exact cutoff_arith hε ht.1 ht.2 h2 (hB0 _) (hC0 _) ha
      (tensorPointwiseNorm_nonneg (I := I) (M := M) g 0 k x _) hy
  · rw [hzero h2, toFun_zero, pointwiseNorm_zero]
    exact Finset.sum_nonneg fun ij _ => mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (mul_nonneg (mul_nonneg (hB0 _) (hC0 _)) (pow_nonneg hT.le _))
        (pow_nonneg (by norm_num) _))

theorem min_arith {T ε K V : ℝ} (hV : 0 ≤ V) :
    K ^ 2 * V * (min T (2 * ε) - 0) ≤ K ^ 2 * V * 2 * ε := by
  have h : min T (2 * ε) - 0 ≤ 2 * ε := by
    rw [sub_zero]
    exact min_le_right _ _
  have := mul_le_mul_of_nonneg_left h (mul_nonneg (sq_nonneg K) hV)
  linarith

/-- **Each pairing is `O(ε)`.** -/
theorem mixedInner_le {s : ℕ} {T : ℝ} (hT : 0 < T) {N : ℕ} {f : ℝ → SmoothCcTensor g 0 s}
    (hf : JointlySmoothOn g 0 s (Icc 0 T) f) (hN : ∀ l < N, timeDerivIter T f l 0 = 0)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ2 : ∀ τ, 2 < τ → ψ τ = 0) {j : ℕ} (hj : j ≤ N)
    (i : ℕ) :
    ∃ K, 0 ≤ K ∧ ∀ ε, 0 < ε →
      mixedInner g s T (fun τ => ψ (ε⁻¹ * τ) • f τ) (fun τ => ψ (ε⁻¹ * τ) • f τ) j i ≤ K * ε := by
  have := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hF := jointlySmoothOn_iteratedCovGrad hf i
  have hF0 : ∀ l < N, timeDerivIter T (fun τ => iteratedCovGrad g 0 s i (f τ)) l 0 = 0 := by
    intro l hl
    rw [timeDerivIter_iteratedCovGrad hT hf i l ⟨le_rfl, hT.le⟩, hN l hl]
    have h := Analysis.Spectral.iteratedCovGrad_smul (I := I) (M := M) g 0 s i (0 : ℝ)
      (0 : SmoothCcTensor g 0 s)
    rw [zero_smul, zero_smul] at h
    exact h
  obtain ⟨K, hK0, hK⟩ := exists_bound_leibniz hT hj hF hF0 hψ hψ2
  obtain ⟨V, hV⟩ : ∃ V, V = (riemannianVolumeMeasure (I := I) (M := M) g).real univ := ⟨_, rfl⟩
  have hV0 : 0 ≤ V := by rw [hV]; exact measureReal_nonneg
  refine ⟨K ^ 2 * V * 2, by positivity, fun ε hε => ?_⟩
  have hψε : ContDiff ℝ ∞ (fun τ => ψ (ε⁻¹ * τ)) := hψ.comp (contDiff_const.mul contDiff_id)
  have hu := jointlySmoothOn_fun_smul hψε.contDiffOn hf
  rw [mixedInner_eq hT hu hu]
  have hfam : (fun τ => iteratedCovGrad g 0 s i (ψ (ε⁻¹ * τ) • f τ)) =
      fun τ => ψ (ε⁻¹ * τ) • iteratedCovGrad g 0 s i (f τ) :=
    funext fun τ => Analysis.Spectral.iteratedCovGrad_smul (I := I) (M := M) g 0 s i _ (f τ)
  rw [hfam]
  obtain ⟨D, hD⟩ : ∃ D : ℝ → SmoothCcTensor g 0 (s + i),
      D = timeDerivIter T (fun τ => ψ (ε⁻¹ * τ) • iteratedCovGrad g 0 s i (f τ)) j :=
    ⟨_, rfl⟩
  rw [← hD]
  have hK' : ∀ t ∈ Icc 0 T, (∀ x : M, tensorPointwiseNorm (I := I) (M := M) g 0 (s + i) x
      ((D t).toFun x) ≤ K) ∧ (2 * ε < t → D t = 0) := by
    rw [hD]
    exact hK ε hε
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc
    (Icc_subset_Icc le_rfl (min_le_left T (2 * ε)))]
  · have hbd : ∀ t ∈ Icc 0 (min T (2 * ε)),
        ‖∫ x, tensorInnerPointwise (I := I) (M := M) g 0 (s + i) x ((D t).toFun x) ((D t).toFun x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)‖ ≤ K ^ 2 * V := by
      intro t ht
      have htT : t ∈ Icc 0 T := ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
      rw [hV]
      refine norm_integral_le_of_norm_le_const (ae_of_all _ fun x => ?_)
      have hx := (hK' t htT).1 x
      unfold tensorPointwiseNorm at hx
      rw [Real.norm_eq_abs, abs_of_nonneg (tensorInnerPointwise_nonneg (I := I) (M := M) g 0
        (s + i) x _)]
      have h0 := Real.sqrt_nonneg (tensorInnerPointwise (I := I) (M := M) g 0 (s + i) x
        ((D t).toFun x) ((D t).toFun x))
      calc _ = Real.sqrt (tensorInnerPointwise (I := I) (M := M) g 0 (s + i) x
              ((D t).toFun x) ((D t).toFun x)) ^ 2 :=
            (Real.sq_sqrt (tensorInnerPointwise_nonneg (I := I) (M := M) g 0 (s + i) x _)).symm
        _ ≤ K ^ 2 := pow_le_pow_left₀ h0 hx 2
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) measure_Icc_lt_top hbd
    rw [Real.volume_real_Icc_of_le (le_min hT.le (by linarith))] at h
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans (h.trans (min_arith hV0))
  · intro t ht
    have htT : t ∈ Icc 0 T := ht.1
    have h2 : 2 * ε < t := by
      by_contra hcon
      push Not at hcon
      exact ht.2 ⟨htT.1, le_min htT.2 hcon⟩
    rw [(hK' t htT).2 h2]
    refine (integral_congr_ae (ae_of_all _ fun x => ?_)).trans (integral_zero _ _)
    rw [toFun_zero, ← ptInnerBilin_apply]
    simp only [map_zero, ContinuousLinearMap.zero_apply]

/-- `‖u‖_{𝒫^m} = √⟨u, u⟩_{𝒫^m}`. -/
theorem pre_norm_eq {s p m : ℕ} {T : ℝ} (u : ParabolicPre g s p m T) :
    ‖u‖ = Real.sqrt (parabolicInner g s p m T u.family u.family) := by
  have h : ‖u‖ ^ 2 = parabolicInner g s p m T u.family u.family := by
    rw [← real_inner_self_eq_norm_sq]
    rfl
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

end Cutoff

/-! ### The cutoff family -/

/-- `f_ε(t) = χ(t/ε) f(t)` (`lem:cutoff`). -/
def cutoffFamily {s : ℕ} (χ : ℝ → ℝ) (ε : ℝ) (f : ℝ → SmoothCcTensor g 0 s) :
    ℝ → SmoothCcTensor g 0 s :=
  fun t => χ (t / ε) • f t

theorem jointlySmoothOn_cutoffFamily {s : ℕ} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (ε : ℝ)
    {S : Set ℝ} {f : ℝ → SmoothCcTensor g 0 s} (hf : JointlySmoothOn g 0 s S f) :
    JointlySmoothOn g 0 s S (cutoffFamily χ ε f) := by
  have h : ContDiff ℝ ∞ (fun t : ℝ => χ (t / ε)) := hχ.comp (contDiff_id.div_const ε)
  exact Cutoff.jointlySmoothOn_fun_smul h.contDiffOn hf

/-- `f_ε` vanishes for `t ≤ ε`. -/
theorem cutoffFamily_eq_zero {s : ℕ} {χ : ℝ → ℝ} (hχ1 : ∀ τ ≤ 1, χ τ = 0) {ε : ℝ} (hε : 0 < ε)
    (f : ℝ → SmoothCcTensor g 0 s) {t : ℝ} (ht : t ≤ ε) : cutoffFamily χ ε f t = 0 := by
  unfold cutoffFamily
  rw [hχ1 _ ((div_le_one hε).mpr ht), zero_smul]

/-- **Cutoff, in parabolic norms** (`lem:cutoff`): `‖f - f_ε‖_{𝒫^{m'}} → 0` as `ε → 0⁺`, for
`m' ≤ N`. -/
theorem tendsto_parabolicInner_cutoff {s : ℕ} {T : ℝ} (hT : 0 < T) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχ2 : ∀ τ, 2 ≤ τ → χ τ = 1) {f : ℝ → SmoothCcTensor g 0 s}
    (hf : JointlySmoothOn g 0 s (Icc 0 T) f) {N : ℕ} (hN : ∀ l < N, timeDerivIter T f l 0 = 0)
    {m' : ℕ} (hm : m' ≤ N) (p : ℕ) :
    Tendsto (fun ε => parabolicInner g s p m' T (fun t => f t - cutoffFamily χ ε f t)
      (fun t => f t - cutoffFamily χ ε f t)) (𝓝[>] 0) (𝓝 0) := by
  have e : ∀ ε, (fun t => f t - cutoffFamily χ ε f t) =
      fun τ => (fun σ => 1 - χ σ) (ε⁻¹ * τ) • f τ := fun ε => funext fun t => by
    simp only [cutoffFamily, sub_smul, one_smul, div_eq_inv_mul]
  have hψ : ContDiff ℝ ∞ (fun σ => 1 - χ σ) := contDiff_const.sub hχ
  have hψ2 : ∀ τ, 2 < τ → (fun σ => 1 - χ σ) τ = 0 := fun τ hτ => by
    simp only [hχ2 τ hτ.le, sub_self]
  suffices H : Tendsto (fun ε => parabolicInner g s p m' T
      (fun τ => (fun σ => 1 - χ σ) (ε⁻¹ * τ) • f τ)
      (fun τ => (fun σ => 1 - χ σ) (ε⁻¹ * τ) • f τ)) (𝓝[>] 0) (𝓝 0) by
    refine H.congr fun ε => ?_
    rw [e ε]
  have key : ∀ j ∈ Finset.range (m' + 1), ∀ i : ℕ, Tendsto (fun ε => mixedInner g s T
      (fun τ => (fun σ => 1 - χ σ) (ε⁻¹ * τ) • f τ)
      (fun τ => (fun σ => 1 - χ σ) (ε⁻¹ * τ) • f τ) j i) (𝓝[>] 0) (𝓝 0) := by
    intro j hj i
    have hjN : j ≤ N := by
      rw [Finset.mem_range] at hj
      omega
    obtain ⟨K, -, hK⟩ := Cutoff.mixedInner_le hT hf hN hψ hψ2 hjN i
    have hup : Tendsto (fun ε : ℝ => K * ε) (𝓝[>] 0) (𝓝 0) := by
      have h : Tendsto (fun ε : ℝ => K * ε) (𝓝 0) (𝓝 (K * 0)) := (continuous_const_mul K).tendsto 0
      rw [mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (Eventually.of_forall fun ε => mixedInner_self_nonneg _ j i) ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hK ε hε
  have h := tendsto_finsetSum (Finset.range (m' + 1)) (fun j hj =>
    tendsto_finsetSum (Finset.range (2 * p * (m' - j) + 1)) (fun i _ => key j hj i))
  simp only [Finset.sum_const_zero] at h
  exact h

namespace ParabolicSpace

/-- **Cutoff** (`lem:cutoff`): if `∂ₜ^ℓ f(·,0) = 0` for `ℓ < N`, then `f_ε = χ(t/ε) f → f` in
`𝒫^{m'}` as `ε → 0⁺`, for every `m' ≤ N`. -/
theorem tendsto_cutoff {s p : ℕ} {T : ℝ} (hT : 0 < T) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχ2 : ∀ τ, 2 ≤ τ → χ τ = 1) {f : ℝ → SmoothCcTensor g 0 s}
    (hf : JointlySmoothOn g 0 s (Icc 0 T) f) {N : ℕ} (hN : ∀ l < N, timeDerivIter T f l 0 = 0)
    {m' : ℕ} (hm : m' ≤ N) :
    Tendsto (fun ε => ofSmooth (p := p) (m := m') (cutoffFamily χ ε f)
      (jointlySmoothOn_cutoffFamily hχ ε hf)) (𝓝[>] 0) (𝓝 (ofSmooth f hf)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have h := (Real.continuous_sqrt.tendsto 0).comp
    (tendsto_parabolicInner_cutoff hT hχ hχ2 hf hN hm p)
  rw [Real.sqrt_zero] at h
  refine h.congr fun ε => ?_
  simp only [Function.comp_apply]
  unfold ofSmooth
  rw [UniformSpace.Completion.dist_eq, dist_comm, dist_eq_norm, Cutoff.pre_norm_eq]
  rfl

end ParabolicSpace

end ShortTime
