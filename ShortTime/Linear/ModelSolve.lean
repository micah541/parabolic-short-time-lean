import ShortTime.Linear.ModelSpectral

/-!
# Solving the model problem (`prop:model`) and the linear theorem (`thm:linear` (i))

For an operator `L₀` that acts on the eigenfunctions by `L₀ φ_i = -μ_i φ_i`, the equation
`∂ₜu - L₀u = Π_F f`, `u(0) = 0`, is solved mode by mode (`modeSol`), and the truncations `Π_F f`
converge to `f` in `𝒫^n` (`tendsto_integral_proj_sub`). Hence `∂ₜ - L₀` has dense range on smooth
families vanishing at `t = 0` (`LinearOp.approx_of_eigen`). The polyharmonic operator
(`exists_polyharmonic`) is such an operator, with `μ_i = λ_i^p` (`LinearOp.exists_model`), and the
method of continuity gives `LinearOp.isomorphism`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open scoped Manifold ContDiff BigOperators

set_option linter.unusedSectionVars false

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

variable {g : SmoothRiemannianMetric I M} {s p : ℕ} {T : ℝ}

section Solve

variable [CompleteSpace E]

/-- `‖u‖²_{𝒫^n}` only depends on `u` on `[0,T]`. -/
theorem parabolicInner_congr (hT : 0 < T) {u v : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (hv : JointlySmoothOn g 0 s (Icc 0 T) v)
    (h : EqOn u v (Icc 0 T)) (n : ℕ) :
    parabolicInner g s p n T u u = parabolicInner g s p n T v v := by
  rw [parabolicInner_self_eq hT hu, parabolicInner_self_eq hT hv]
  refine Finset.sum_congr rfl fun j _ => intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hT.le] at ht
  rw [timeDerivIter_congr hT hu hv h j ht]

namespace LinearOp

theorem apply_zero (L : LinearOp g s p T) (t : ℝ) : L.apply t 0 = 0 := by
  have h := L.apply_smul t 0 0
  rwa [zero_smul, zero_smul] at h

theorem apply_finset_sum (L : LinearOp g s p T) (t : ℝ) {ι : Type*} (F : Finset ι)
    (v : ι → SmoothCcTensor g 0 s) : L.apply t (∑ i ∈ F, v i) = ∑ i ∈ F, L.apply t (v i) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, L.apply_zero]
  | insert i F hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, L.apply_add, ih]

/-- **Solving mode by mode**: if `L₀ φ_i = -μ_i φ_i`, then for every finite set `F` of modes there
is a smooth `u` with `u(0) = 0` and `(∂ₜ - L₀)u = Π_F f` on `[0,T]`. -/
theorem exists_solution_proj (hT : 0 < T) (L₀ : LinearOp g s p T) (μ : EIdx g s → ℝ)
    (hμ : ∀ t i, L₀.apply t (eig g s i) = (-μ i) • eig g s i) (F : Finset (EIdx g s))
    {f : ℝ → SmoothCcTensor g 0 s} (hf : JointlySmoothOn g 0 s (Icc 0 T) f) :
    ∃ u : ℝ → SmoothCcTensor g 0 s, JointlySmoothOn g 0 s (Icc 0 T) u ∧ u 0 = 0 ∧
      EqOn (L₀.heatOp u) (fun t => proj F (f t)) (Icc 0 T) := by
  set a : EIdx g s → ℝ → ℝ := fun i => modeSol T (μ i) (fun τ => ShortTime.coeff (f τ) i) with ha
  have hu : JointlySmoothOn g 0 s (Icc 0 T) (fun t => ∑ i ∈ F, a i t • eig g s i) :=
    jointlySmoothOn_sum F fun i _ =>
      jointlySmoothOn_scalar_smul (contDiffOn_modeSol hT (contDiffOn_coeff hT hf i)) _
  refine ⟨fun t => ∑ i ∈ F, a i t • eig g s i, hu, ?_, fun t ht => ?_⟩
  · simp only [ha, modeSol_zero, zero_smul, Finset.sum_const_zero]
  · have hd : timeDeriv T (fun t => ∑ i ∈ F, a i t • eig g s i) t =
        ∑ i ∈ F, (ShortTime.coeff (f t) i - μ i * a i t) • eig g s i := by
      refine timeDeriv_eq hT hu ht fun x => ?_
      simp only [toFun_finset_sum, SmoothCcTensor.toFun_smul, Pi.smul_apply]
      exact HasDerivWithinAt.fun_sum fun i _ =>
        (hasDerivWithinAt_modeSol hT (continuousOn_coeff hT hf i) ht).smul_const
          ((eig g s i).toFun x)
    simp only [heatOp, hd, L₀.apply_finset_sum, L₀.apply_smul, hμ, proj, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    module

/-- **`∂ₜ - L₀` has dense range** on smooth families vanishing at `t = 0`, in every `𝒫^n`, when
`L₀ φ_i = -μ_i φ_i`. -/
theorem approx_of_eigen (hT : 0 < T) (L₀ : LinearOp g s p T) (μ : EIdx g s → ℝ)
    (hμ : ∀ t i, L₀.apply t (eig g s i) = (-μ i) • eig g s i) (n : ℕ)
    {f : ℝ → SmoothCcTensor g 0 s} (hf : JointlySmoothOn g 0 s (Icc 0 T) f) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ℝ → SmoothCcTensor g 0 s, JointlySmoothOn g 0 s (Icc 0 T) u ∧ u 0 = 0 ∧
      parabolicInner g s p n T (fun t => L₀.heatOp u t - f t) (fun t => L₀.heatOp u t - f t) < ε := by
  have hε' : 0 < ε / (n + 1) := by positivity
  have hev : ∀ j ∈ Finset.range (n + 1), ∀ᶠ F : Finset (EIdx g s) in atTop,
      ∫ t in (0 : ℝ)..T, sobolevNormSq g 0 s (2 * p * (n - j))
        (proj F (timeDerivIter T f j t) - timeDerivIter T f j t) < ε / (n + 1) := fun j _ =>
    (tendsto_order.1 (tendsto_integral_proj_sub hT _ (jointlySmoothOn_timeDerivIter hT hf j))).2 _ hε'
  obtain ⟨F, hF⟩ := ((Filter.eventually_all_finset _).2 hev).exists
  obtain ⟨u, hu, hu0, heq⟩ := exists_solution_proj hT L₀ μ hμ F hf
  refine ⟨u, hu, hu0, ?_⟩
  have hP : JointlySmoothOn g 0 s (Icc 0 T) (fun t => proj F (f t)) := jointlySmoothOn_proj hT F hf
  have hw : JointlySmoothOn g 0 s (Icc 0 T) (fun t => proj F (f t) - f t) := jointlySmoothOn_sub hP hf
  rw [parabolicInner_congr hT (jointlySmoothOn_sub (L₀.jointlySmoothOn_heatOp hT hu) hf) hw
    (fun t ht => by simp only [heq ht]) n, parabolicInner_self_eq hT hw]
  have hsplit : (fun t => proj F (f t) - f t) =
      fun t => proj F (f t) + (-1 : ℝ) • f t := funext fun t => by rw [neg_one_smul, sub_eq_add_neg]
  calc ∑ j ∈ Finset.range (n + 1), ∫ t in (0 : ℝ)..T,
        sobolevNormSq g 0 s (2 * p * (n - j)) (timeDerivIter T (fun t => proj F (f t) - f t) j t)
      = ∑ j ∈ Finset.range (n + 1), ∫ t in (0 : ℝ)..T, sobolevNormSq g 0 s (2 * p * (n - j))
          (proj F (timeDerivIter T f j t) - timeDerivIter T f j t) := by
        refine Finset.sum_congr rfl fun j _ => intervalIntegral.integral_congr fun t ht => ?_
        rw [uIcc_of_le hT.le] at ht
        rw [hsplit, timeDerivIter_add hT hP (jointlySmoothOn_smul (-1) hf),
          timeDerivIter_smul hT (-1) hf]
        dsimp only
        rw [timeDerivIter_proj hT F hf j ht, neg_one_smul, ← sub_eq_add_neg]
    _ < ∑ j ∈ Finset.range (n + 1), ε / (n + 1) :=
        Finset.sum_lt_sum_of_nonempty ⟨0, by simp⟩ fun j hj => hF j hj
    _ = ε := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        field_simp

/-- **The model operator** (`prop:model`): the polyharmonic operator `L₀ = -(Δ)^p` is parabolic with
Legendre constant `1`, and `∂ₜ - L₀` has dense range on smooth families vanishing at `t = 0`, in
every `𝒫^n`. -/
theorem exists_model (hT : 0 < T) (hp : 1 ≤ p) :
    ∃ L₀ : LinearOp g s p T, L₀.IsParabolic 1 ∧ ∀ n : ℕ, ∀ f : ℝ → SmoothCcTensor g 0 s,
      JointlySmoothOn g 0 s (Icc 0 T) f → ∀ ε > 0, ∃ u : ℝ → SmoothCcTensor g 0 s,
        JointlySmoothOn g 0 s (Icc 0 T) u ∧ u 0 = 0 ∧
          parabolicInner g s p n T (fun t => L₀.heatOp u t - f t)
            (fun t => L₀.heatOp u t - f t) < ε := by
  obtain ⟨L₀, hL₀, hpar⟩ := exists_polyharmonic (g := g) s hp T
  refine ⟨L₀, hpar, fun n f hf ε hε =>
    approx_of_eigen hT L₀ (fun i => (TensorEigenIdx.lambda i) ^ p) (fun t i => ?_) n hf hε⟩
  have h1 : ((-1 : ℝ)) ^ (p + 1) * (-1) ^ p = -1 := by
    rw [← pow_add, show p + 1 + p = 2 * p + 1 by ring, pow_succ, pow_mul]
    norm_num
  rw [hL₀, rawLapIter_eig, smul_smul, neg_pow (TensorEigenIdx.lambda i), ← mul_assoc, h1]
  congr 1
  ring

end LinearOp

end Solve

namespace LinearOp

variable (L : LinearOp g s p T)

/-- **Linear parabolic theory, Hilbert space form** (`thm:linear` (i)). For a parabolic operator
with smooth coefficients, `∂ₜ - L : 𝒫^m_0 → 𝒫^{m-1}` is a linear homeomorphism. It is the unique
continuous extension of `∂ₜ - L` from smooth families: it sends `u` to `w` whenever `∂ₜu = Lu + w`. -/
theorem isomorphism (hp : 1 ≤ p) (hT : 0 < T) {lam : ℝ} (hL : L.IsParabolic lam) (m : ℕ)
    (hm : 1 ≤ m) :
    ∃ Φ : ParabolicSpace.zeroAtStart g s p m T ≃L[ℝ] ParabolicSpace g s p (m - 1) T,
      ∀ (u w : ℝ → SmoothCcTensor g 0 s) (hu : JointlySmoothOn g 0 s (Icc 0 T) u)
        (hw : JointlySmoothOn g 0 s (Icc 0 T) w) (h0 : u 0 = 0), L.Solves u w →
        (Φ ⟨ParabolicSpace.ofSmooth u hu, ParabolicSpace.ofSmooth_mem_zeroAtStart u hu h0⟩ :
          ParabolicSpace g s p (m - 1) T) = ParabolicSpace.ofSmooth w hw := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨L₀, h₀, happrox⟩ := exists_model (g := g) (s := s) hT hp
  exact isomorphism_of_base hT hp hm L₀ L h₀ hL (happrox (m - 1))

end LinearOp

end ShortTime
