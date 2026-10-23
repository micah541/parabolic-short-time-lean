import ShortTime.Sanity.LegendreTrace

/-!
# Basic properties of the Legendre condition (`lem:legendre-basic` (i))

The Legendre form is linear in the coefficient `P`. Hence the Legendre condition is preserved under
nonnegative combinations, which is what the method of continuity needs along
`(1-s) L₀ + s L`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open scoped Manifold ContDiff BigOperators

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

variable (g : SmoothRiemannianMetric I M) (r s p : ℕ) (x : M)

theorem fiberInner_add_right (v w w' : TensorRSSpace r s I x) :
    fiberInner g r s x v (w + w') = fiberInner g r s x v w + fiberInner g r s x v w' :=
  map_add _ _ _

theorem fiberInner_smul_right (v w : TensorRSSpace r s I x) (c : ℝ) :
    fiberInner g r s x v (c • w) = c * fiberInner g r s x v w := by
  simp [fiberInner, map_smul]

/-- The Legendre form is additive in `P`. -/
theorem legendreForm_add (P Q : TensorRSSpace r (s + p + p) I x →L[ℝ] TensorRSSpace r s I x)
    (ξ η : TensorRSSpace r (s + p) I x) :
    legendreForm g r s p x (P + Q) ξ η = legendreForm g r s p x P ξ η + legendreForm g r s p x Q ξ η := by
  simp only [legendreForm_eq, FunLike.coe_add, Pi.add_apply, fiberInner_add_right,
    Finset.sum_add_distrib]

/-- The Legendre form is homogeneous in `P`. -/
theorem legendreForm_smul (c : ℝ) (P : TensorRSSpace r (s + p + p) I x →L[ℝ] TensorRSSpace r s I x)
    (ξ η : TensorRSSpace r (s + p) I x) :
    legendreForm g r s p x (c • P) ξ η = c * legendreForm g r s p x P ξ η := by
  simp only [legendreForm_eq, FunLike.coe_smul, Pi.smul_apply, fiberInner_smul_right,
    Finset.mul_sum]

/-- **The Legendre condition is convex.** If `P` and `Q` satisfy it with constants `λ` and `μ`,
then `a P + b Q` satisfies it with constant `a λ + b μ` (`a, b ≥ 0`, `a + b > 0`). -/
theorem LegendreAt.combo {P Q : TensorRSSpace r (s + p + p) I x →L[ℝ] TensorRSSpace r s I x}
    {lam mu : ℝ} (hP : LegendreAt g r s p x P lam) (hQ : LegendreAt g r s p x Q mu)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) :
    LegendreAt g r s p x (a • P + b • Q) (a * lam + b * mu) := by
  refine ⟨?_, fun ξ => ?_⟩
  · rcases ha.lt_or_eq with ha' | ha'
    · nlinarith [hP.1, hQ.1, mul_pos ha' hP.1, mul_nonneg hb hQ.1.le]
    · subst ha'
      simp only [zero_add] at hab
      nlinarith [mul_pos hab hQ.1]
  · have h1 := hP.2 ξ
    have h2 := hQ.2 ξ
    rw [legendreForm_add, legendreForm_smul, legendreForm_smul]
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

end ShortTime
