import ShortTime.Nonlinear.ContLevel
import ShortTime.Nonlinear.UniquenessB

/-!
# Continuous dependence on covariant bundles (`cor:C`, `r = 0`)

`EquationData.continuous_dependence_cov` is the statement of `solution_continuous_dependence` for
covariant tensor bundles `T⁰_s`, assuming the regularity in trace form (`TraceRegularity`).

The proof, from `level_solution` (the solution at one Sobolev level `m ≥ ⌊n/2p⌋ + 4`):

* uniform parabolicity of `u` and of a neighbourhood of its jets (`exists_stab`);
* `a_n → u₀` in `C^∞` gives `‖a_n - u₀‖_{𝒫^m} → 0` for every `m` (`parabolicInner_const_le`);
* hence, for every `m`, a smooth parabolic solution `w'` with datum `a_n` that is close to `u` in
  `𝒫^m`, for large `n`;
* by uniqueness (Theorem B) all these solutions coincide with the solution `w n` chosen for `a_n`;
  closeness in `𝒫^m` for `m` large controls `∇^j (w n - u)` uniformly (`exists_jetSq_close`).
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

variable {g : SmoothRiemannianMetric I M} {s p : ℕ}

open ParabolicSpace

theorem fiberNorm_sq (r a : ℕ) (x : M) (v : TensorRSSpace r a I x) :
    fiberNorm g r a x v ^ 2 = riemannianFiberNormSq (I := I) (M := M) g r a x v := by
  have hfi : riemannianFiberNormSq (I := I) (M := M) g r a x v = fiberInner g r a x v v :=
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r a x v
  have h0 : 0 ≤ fiberInner g r a x v v := by
    rw [← hfi]
    exact riemannianFiberNormSq_nonneg (I := I) (M := M) g r a x v
  rw [fiberNorm, Real.sq_sqrt h0, hfi]

theorem fiberNorm_le_iff {r a : ℕ} {x : M} {v : TensorRSSpace r a I x} {ε : ℝ} (hε : 0 ≤ ε) :
    fiberNorm g r a x v ≤ ε ↔ riemannianFiberNormSq (I := I) (M := M) g r a x v ≤ ε ^ 2 := by
  rw [← fiberNorm_sq (g := g) r a x v]
  exact (pow_le_pow_iff_left₀ (show 0 ≤ fiberNorm g r a x v from Real.sqrt_nonneg _) hε
    two_ne_zero).symm

/-- **The norm of the time-independent family `a_n - u₀` tends to zero in `𝒫^m`.** -/
theorem eventually_norm_const_lt {T : ℝ} (hT : 0 < T) {u₀ : SmoothCcTensor g 0 s}
    {a : ℕ → SmoothCcTensor g 0 s}
    (ha : ∀ j : ℕ, ∀ ε > 0, ∀ᶠ n in atTop, ∀ x : M,
      fiberNorm g 0 (s + j) x ((iteratedCovGrad g 0 s j (a n - u₀)).toSection x) ≤ ε)
    (m : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ n in atTop, ‖ofSmooth (p := p) (m := m) (T := T) (fun _ => a n - u₀)
      (jointlySmoothOn_const (g := g) (Icc 0 T) (a n - u₀))‖ < ρ := by
  set K : ℝ := parabolicCount p m * (T * (riemannianVolumeMeasure (I := I) (M := M) g).real univ + 1)
    with hK
  have hKpos : 0 < K := by
    have h1 : (1 : ℝ) ≤ parabolicCount p m := by
      unfold parabolicCount
      have : 1 ≤ ∑ j ∈ Finset.range (m + 1), (2 * p * (m - j) + 1) :=
        Finset.single_le_sum (f := fun j => 2 * p * (m - j) + 1) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.2 (Nat.succ_pos m)) |>.trans' (by omega)
      exact_mod_cast this
    have h2 : 0 < T * (riemannianVolumeMeasure (I := I) (M := M) g).real univ + 1 :=
      add_pos_of_nonneg_of_pos (mul_nonneg hT.le measureReal_nonneg) one_pos
    exact mul_pos (lt_of_lt_of_le one_pos h1) h2
  set ε'' : ℝ := ρ ^ 2 / (2 * K) with hε''
  have hε''pos : 0 < ε'' := by positivity
  have hev : ∀ᶠ n in atTop, ∀ i ∈ Finset.range (2 * p * m + 1), ∀ x : M,
      fiberNorm g 0 (s + i) x ((iteratedCovGrad g 0 s i (a n - u₀)).toSection x) ≤
        Real.sqrt ε'' :=
    (Filter.eventually_all_finset _).2 fun i _ => ha i _ (Real.sqrt_pos.2 hε''pos)
  filter_upwards [hev] with n hn
  have hnorm := parabolicInner_const_le (g := g) (s := s) hT p m (a n - u₀) hε''pos.le
    (fun i hi x => by
      have h := hn i (Finset.mem_range.2 (Nat.lt_succ_of_le hi)) x
      rw [fiberNorm_le_iff (Real.sqrt_nonneg _), Real.sq_sqrt hε''pos.le] at h
      exact h)
  have hsq := norm_ofSmooth_sq (p := p) (m := m) (T := T)
    (jointlySmoothOn_const (g := g) (Icc 0 T) (a n - u₀))
  have hlt : ‖ofSmooth (p := p) (m := m) (T := T) (fun _ => a n - u₀)
      (jointlySmoothOn_const (g := g) (Icc 0 T) (a n - u₀))‖ ^ 2 < ρ ^ 2 := by
    rw [hsq]
    refine hnorm.trans_lt ?_
    have e : ε'' * (parabolicCount p m : ℝ) *
        (T * (riemannianVolumeMeasure (I := I) (M := M) g).real univ + 1) = ε'' * K := by
      rw [hK]; ring
    rw [e, hε'']
    have : ρ ^ 2 / (2 * K) * K = ρ ^ 2 / 2 := by field_simp
    rw [this]
    nlinarith [sq_nonneg ρ, mul_pos hρ hρ]
  exact lt_of_pow_lt_pow_left₀ 2 hρ.le hlt

/-- **Continuous dependence on covariant bundles** (`cor:C`, `r = 0`), assuming the regularity in
trace form. -/
theorem EquationData.continuous_dependence_cov (D : EquationData I M 0 s p) (hp : 1 ≤ p)
    (hreg : D.TraceRegularity g) {u₀ : SmoothCcTensor g 0 s} {T : ℝ}
    {u : ℝ → SmoothCcTensor g 0 s} (hu : D.IsParabolicSolution g u₀ T u)
    (a : ℕ → SmoothCcTensor g 0 s)
    (ha : ∀ j : ℕ, ∀ ε > 0, ∀ᶠ n in atTop, ∀ x : M,
      fiberNorm g 0 (s + j) x ((iteratedCovGrad g 0 s j (a n - u₀)).toSection x) ≤ ε) :
    ∃ w : ℕ → ℝ → SmoothCcTensor g 0 s,
      (∀ᶠ n in atTop, D.IsParabolicSolution g (a n) T (w n)) ∧
      ∀ j : ℕ, ∀ ε > 0, ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        fiberNorm g 0 (s + j) x ((iteratedCovGrad g 0 s j (w n t - u t)).toSection x) ≤ ε := by
  classical
  obtain ⟨hsol, hpar⟩ := hu
  have hT := hsol.pos
  obtain ⟨η, hη, lam, hlam, hstab⟩ := D.exists_stab hsol.le_T₀ hsol.smooth hpar
  have hleg : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (u t) x ∈ D.dom t x ∧
      LegendreAt g 0 s p x (D.principal t x (covJet g 0 s (2 * p) (u t) x)) lam := by
    intro t ht x
    refine hstab t ht x _ (fun k => ?_)
    rw [sub_self, riemannianFiberNormSq_zero]
    exact hη.le
  set w : ℕ → ℝ → SmoothCcTensor g 0 s := fun n =>
    if h : ∃ w, D.IsParabolicSolution g (a n) T w then h.choose else fun _ => 0 with hwdef
  have hwsol : ∀ n, (∃ w, D.IsParabolicSolution g (a n) T w) →
      D.IsParabolicSolution g (a n) T (w n) := fun n h => by
    simp only [hwdef, dif_pos h]
    exact h.choose_spec
  -- the solution at level `m`
  have hlevel : ∀ m, Module.finrank ℝ E / (2 * p) + 4 ≤ m → ∀ ε > 0, ∀ᶠ n in atTop,
      ∃ (w' : ℝ → SmoothCcTensor g 0 s) (hw' : JointlySmoothOn g 0 s (Icc 0 T) w'),
        D.IsParabolicSolution g (a n) T w' ∧
        dist (ofSmooth (p := p) (m := m) w' hw') (ofSmooth u hsol.smooth) < ε := by
    intro m hm ε hε
    obtain ⟨ρ, hρ, hρp⟩ := D.level_solution hp hreg hsol hlam hη hleg hstab hm hε
    filter_upwards [eventually_norm_const_lt hT ha m hρ] with n hn
    exact hρp (a n) hn
  refine ⟨w, ?_, ?_⟩
  · filter_upwards [hlevel _ le_rfl 1 one_pos] with n hn
    obtain ⟨w', -, hw', -⟩ := hn
    exact hwsol n ⟨w', hw'⟩
  · intro j ε hε
    set m := max (Module.finrank ℝ E / (2 * p) + 4) (Module.finrank ℝ E / (2 * p) + 3 + j) with hm
    have hm1 : Module.finrank ℝ E / (2 * p) + 4 ≤ m := le_max_left _ _
    have hm2 : Module.finrank ℝ E / (2 * p) + 3 + j ≤ m := le_max_right _ _
    have hm0 : 0 < m := lt_of_lt_of_le (by norm_num) (le_trans (Nat.le_add_left 4 _) hm1)
    obtain ⟨C, hC0, hC⟩ := exists_jetSq_close (g := g) (s := s) (p := p) (i := j) hT hp hm0
      (emb_arith' hp hm2)
    set ε₁ : ℝ := ε / (C + 1) with hε₁
    have hε₁pos : 0 < ε₁ := by positivity
    filter_upwards [hlevel m hm1 ε₁ hε₁pos] with n hn
    obtain ⟨w', hw', hw'sol, hdist⟩ := hn
    have hwn := hwsol n ⟨w', hw'sol⟩
    have hequ := D.solution_unique_cov g hwn hw'sol
    intro t ht x
    rw [hequ t ht, fiberNorm_le_iff hε.le]
    refine (hC w' u hw' hsol.smooth t ht x).trans ?_
    have hd0 : 0 ≤ dist (ofSmooth (p := p) (m := m) w' hw') (ofSmooth u hsol.smooth) := dist_nonneg
    have h1 : dist (ofSmooth (p := p) (m := m) w' hw') (ofSmooth u hsol.smooth) ^ 2 ≤ ε₁ ^ 2 :=
      pow_le_pow_left₀ hd0 hdist.le 2
    calc C * dist (ofSmooth (p := p) (m := m) w' hw') (ofSmooth u hsol.smooth) ^ 2
        ≤ C * ε₁ ^ 2 := mul_le_mul_of_nonneg_left h1 hC0
      _ ≤ ε ^ 2 := by
          rw [hε₁, div_pow]
          have hC1 : 0 < (C + 1) ^ 2 := by positivity
          rw [mul_div_assoc', div_le_iff₀ hC1]
          nlinarith [sq_nonneg ε, sq_nonneg C, mul_nonneg hC0 (sq_nonneg ε)]

end ShortTime
