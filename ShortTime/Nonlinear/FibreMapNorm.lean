import ShortTime.Nonlinear.Tube

/-!
# The fibre norm is bounded by the coordinates

Near `x₀`, the fibre norm of `T⁰_a M` is bounded by the norm of the coordinates in the trivialization
at `x₀` (`exists_fiberNormSq_le_triv`). The proof expands in smooth sections with constant
coordinates (`exists_tensor_frame`), whose pairwise inner products are continuous.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter Topology
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Elliptic
open scoped Manifold ContDiff

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

variable {g : SmoothRiemannianMetric I M}

/-- **The fibre norm is bounded by the coordinates near `x₀`.** -/
theorem exists_fiberNormSq_le_triv (a : ℕ) (x₀ : M) :
    ∃ C, 0 ≤ C ∧ ∀ᶠ y in 𝓝 x₀, ∀ v : TensorRSSpace 0 a I y,
      riemannianFiberNormSq (I := I) (M := M) g 0 a y v ≤
        C * ‖(trivAt I M 0 a x₀).continuousLinearMapAt ℝ y v‖ ^ 2 := by
  classical
  set bz := Module.finBasis ℝ (TensorRSModel 0 a ℝ E) with hbz
  obtain ⟨Ψ, hΨ⟩ := exists_tensor_frame (g := g) a x₀ bz
  set f : Fin (Module.finrank ℝ (TensorRSModel 0 a ℝ E)) →
      Fin (Module.finrank ℝ (TensorRSModel 0 a ℝ E)) → M → ℝ :=
    fun j l y => fiberInner g 0 a y ((Ψ j).toSection y) ((Ψ l).toSection y) with hf
  set Mb := ∑ j, ∑ l, (|f j l x₀| + 1) with hMb
  set cj := fun j => LinearMap.toContinuousLinearMap (bz.coord j) with hcj
  set Cc := ∑ j, ‖cj j‖ with hCc
  have hMb0 : 0 ≤ Mb := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have hCc0 : 0 ≤ Cc := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨Cc ^ 2 * Mb, by positivity, ?_⟩
  have hcont : ∀ j l, ∀ᶠ y in 𝓝 x₀, |f j l y| ≤ |f j l x₀| + 1 := by
    intro j l
    have hc := (continuous_fiberInner_sections g (Ψ j) (Ψ l)).continuousAt (x := x₀)
    filter_upwards [Metric.tendsto_nhds.mp hc 1 one_pos] with y hy
    have h1 := abs_sub_abs_le_abs_sub (f j l y) (f j l x₀)
    rw [Real.dist_eq] at hy
    change |f j l y - f j l x₀| < 1 at hy
    linarith
  filter_upwards [hΨ, Filter.eventually_all.2 fun j => Filter.eventually_all.2 fun l => hcont j l,
    (trivAt I M 0 a x₀).open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ x₀)]
    with y hy hb hbase v
  set z := (trivAt I M 0 a x₀).continuousLinearMapAt ℝ y v with hz
  have hv : v = (trivAt I M 0 a x₀).symmL ℝ y z :=
    (Trivialization.symmL_continuousLinearMapAt _ hbase v).symm
  have hfi : riemannianFiberNormSq (I := I) (M := M) g 0 a y v = fiberInner g 0 a y v v :=
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 a y v
  have hcz : ∀ j, |bz.repr z j| ≤ Cc * ‖z‖ := by
    intro j
    have h1 : ‖cj j z‖ ≤ ‖cj j‖ * ‖z‖ := (cj j).le_opNorm z
    have h2 : cj j z = bz.repr z j := by
      simp [hcj, Module.Basis.coord_apply]
    rw [h2, Real.norm_eq_abs] at h1
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact Finset.single_le_sum (f := fun j => ‖cj j‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ j)
  rw [hfi, hv, fiberInner_symmL_expand g bz Ψ hy z]
  set X := Cc * ‖z‖ with hX
  have hX0 : 0 ≤ X := by positivity
  have hj : ∀ j, bz.repr z j * ∑ l, bz.repr z l * f j l y ≤
      ∑ l, X * (X * (|f j l x₀| + 1)) := by
    intro j
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun l _ => ?_
    calc bz.repr z j * (bz.repr z l * f j l y)
        ≤ |bz.repr z j * (bz.repr z l * f j l y)| := le_abs_self _
      _ = |bz.repr z j| * (|bz.repr z l| * |f j l y|) := by rw [abs_mul, abs_mul]
      _ ≤ X * (X * (|f j l x₀| + 1)) :=
          mul_le_mul (hcz j) (mul_le_mul (hcz l) (hb j l) (abs_nonneg _) hX0)
            (by positivity) hX0
  calc ∑ j, bz.repr z j * ∑ l, bz.repr z l * f j l y
      ≤ ∑ j, ∑ l, X * (X * (|f j l x₀| + 1)) := Finset.sum_le_sum fun j _ => hj j
    _ = Cc ^ 2 * Mb * ‖z‖ ^ 2 := by
        have : ∀ j l, X * (X * (|f j l x₀| + 1)) = X ^ 2 * (|f j l x₀| + 1) := fun j l => by ring
        simp_rw [this, ← Finset.mul_sum]
        rw [hX, hMb]
        ring

end ShortTime
