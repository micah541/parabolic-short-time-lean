import ShortTime.Nonlinear.StabLocal
import ShortTime.Linear.LimitSmooth

/-!
# Uniform stability of parabolicity (`lem:legendre-basic` (iii), global form)

`EquationData.exists_stab`: let `u` be a smooth family on `[0, T]` whose jets are parabolic at every
`(t, x)`. There are `η > 0` and `lam > 0` such that for every smooth family `w` on `[0, T]` with
`|∇^k (w - u)|² ≤ η` pointwise for `k ≤ 2p`, the jets of `w` lie in the domain and satisfy the
Legendre condition with constant `lam`. Taking `w = u` gives a uniform Legendre constant for `u`.

The local statement `stab_local` is transported to jets of families through the trivializations at
`x₀` (`exists_triv_small`); compactness of `M × [0, T]` gives uniform constants.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter Topology
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Elliptic DifferentialGeometry.Geometry.Connection
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

/-- **Coordinates are bounded by the fibre norm near `x₀`.** -/
theorem exists_norm_triv_le (a : ℕ) (x₀ : M) :
    ∃ K ∈ 𝓝 x₀, ∃ C, 0 ≤ C ∧ ∀ y ∈ K, ∀ v : TensorRSSpace 0 a I y,
      ‖(trivAt I M 0 a x₀).continuousLinearMapAt ℝ y v‖ ^ 2 ≤
        C * riemannianFiberNormSq (I := I) (M := M) g 0 a y v := by
  obtain ⟨K, hK, hKn, hKs⟩ := exists_compact_subset (chartAt H x₀).open_source
    (mem_chart_source H x₀)
  obtain ⟨C, hC0, hC⟩ := exists_norm_twist_le (g := g) x₀ a hK hKs
  refine ⟨K, mem_interior_iff_mem_nhds.mp hKn, C, hC0, fun y hy v => ?_⟩
  have h := hC y hy v
  have hb : y ∈ (chartAt H x₀).source := hKs hy
  have e : (trivAt I M 0 a x₀).continuousLinearMapAt ℝ y v =
      chartRSTwistInv (I := I) (M := M) x₀ y 0 a (TensorRSSpace.toModel v) :=
    triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel 0 a x₀ hb v
  rw [e]
  exact h

/-- **Small jets have small coordinates near `x₀`.** -/
theorem exists_triv_small (s N : ℕ) (x₀ : M) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∃ K ∈ 𝓝 x₀, ∀ y ∈ K, ∀ ζ : CovJetFiber I 0 s N y,
      (∀ k : Fin (N + 1), riemannianFiberNormSq (I := I) (M := M) g 0 (s + k) y (ζ k) ≤ δ) →
        ‖EquationData.trivJet x₀ y ζ‖ < ε := by
  have hex : ∀ k : Fin (N + 1), ∃ K ∈ 𝓝 x₀, ∃ C, 0 ≤ C ∧ ∀ y ∈ K, ∀ v : TensorRSSpace 0 (s + k) I y,
      ‖(trivAt I M 0 (s + k) x₀).continuousLinearMapAt ℝ y v‖ ^ 2 ≤
        C * riemannianFiberNormSq (I := I) (M := M) g 0 (s + k) y v :=
    fun k => exists_norm_triv_le (g := g) (s + k) x₀
  choose K hK C hC0 hC using hex
  set Cm := ∑ k, C k with hCm
  have hCm0 : 0 ≤ Cm := Finset.sum_nonneg fun k _ => hC0 k
  refine ⟨ε ^ 2 / (2 * (Cm + 1)), by positivity, ⋂ k, K k, Filter.iInter_mem.2 hK,
    fun y hy ζ hζ => ?_⟩
  unfold EquationData.trivJet
  refine (pi_norm_lt_iff hε).2 fun k => ?_
  have hyk := mem_iInter.1 hy k
  have h1 := hC k y hyk (ζ k)
  have hCk : C k ≤ Cm := Finset.single_le_sum (f := C) (fun k _ => hC0 k) (Finset.mem_univ k)
  have h2 : ‖(trivAt I M 0 (s + k) x₀).continuousLinearMapAt ℝ y (ζ k)‖ ^ 2 < ε ^ 2 := by
    refine h1.trans_lt ?_
    have h3 : C k * riemannianFiberNormSq (I := I) (M := M) g 0 (s + k) y (ζ k) ≤
        Cm * (ε ^ 2 / (2 * (Cm + 1))) :=
      (mul_le_mul_of_nonneg_left (hζ k) (hC0 k)).trans
        (mul_le_mul_of_nonneg_right hCk (by positivity))
    refine h3.trans_lt ?_
    rw [mul_div_assoc']
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [sq_nonneg ε, mul_pos hε hε]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le h2

end ShortTime
