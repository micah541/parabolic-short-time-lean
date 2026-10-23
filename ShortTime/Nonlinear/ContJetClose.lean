import ShortTime.Nonlinear.ContNorm
import ShortTime.Nonlinear.ContAbstract
import ShortTime.Linear.Embedding

/-!
# Closeness in `𝒫^m` controls the jets uniformly (`cor:C`)

For `m ≥ ⌊n/2p⌋ + 4` and `k ≤ 2p`, `|∇^k (w - u)|² ≤ C ‖w - u‖²_{𝒫^m}` pointwise
(`exists_jet_close`, from `lem:embedding`). Also the same for `∇^j` with `j` arbitrary and `m` large
(`exists_jetSq_close`).
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

/-- The embedding condition for `∇^i`, `i ≤ 2p`, from `m ≥ ⌊n/2p⌋ + 4`. -/
theorem emb_arith {n p m i : ℕ} (hp : 1 ≤ p) (hm : n / (2 * p) + 4 ≤ m) (hi : i ≤ 2 * p) :
    n / 2 + 1 + i ≤ 2 * p * (m - 0 - 1) := by
  have h1 := Nat.div_add_mod n (2 * p)
  have h2 := Nat.mod_lt n (show 0 < 2 * p by omega)
  have h3 : 2 * p * (n / (2 * p) + 3) ≤ 2 * p * (m - 0 - 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have h4 : 2 * p * (n / (2 * p) + 3) = 2 * p * (n / (2 * p)) + 6 * p := by ring
  generalize 2 * p * (n / (2 * p)) = A at h1 h4
  generalize n % (2 * p) = B at h1 h2
  omega

/-- The embedding condition for `∇^i` in terms of a bound `i ≤ N` on the derivative order, for `m`
large. -/
theorem emb_arith' {n p m i : ℕ} (hp : 1 ≤ p) (hm : n / (2 * p) + 3 + i ≤ m) :
    n / 2 + 1 + i ≤ 2 * p * (m - 0 - 1) := by
  have h1 := Nat.div_add_mod n (2 * p)
  have h2 := Nat.mod_lt n (show 0 < 2 * p by omega)
  have h3 : 2 * p * (n / (2 * p) + 2 + i) ≤ 2 * p * (m - 0 - 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have h4 : 2 * p * (n / (2 * p) + 2 + i) = 2 * p * (n / (2 * p)) + 4 * p + 2 * p * i := by ring
  have h5 : i ≤ 2 * p * i := by nlinarith
  generalize 2 * p * (n / (2 * p)) = A at h1 h4
  generalize n % (2 * p) = B at h1 h2
  omega

/-- **Jets are controlled by the `𝒫^m` distance.** -/
theorem exists_jetSq_close {T : ℝ} (hT : 0 < T) (hp : 1 ≤ p) {m i : ℕ} (hm0 : 0 < m)
    (hk : Module.finrank ℝ E / 2 + 1 + i ≤ 2 * p * (m - 0 - 1)) :
    ∃ C, 0 ≤ C ∧ ∀ (w u : ℝ → SmoothCcTensor g 0 s) (hw : JointlySmoothOn g 0 s (Icc 0 T) w)
      (hu : JointlySmoothOn g 0 s (Icc 0 T) u), ∀ t ∈ Icc (0 : ℝ) T, ∀ y : M,
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) y
          ((iteratedCovGrad g 0 s i (w t - u t)).toSection y) ≤
          C * dist (ofSmooth (p := p) (m := m) w hw) (ofSmooth u hu) ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_fiberNormSq_le_parabolicInner (g := g) (s := s) hT p
    (m := m) (j := 0) (i := i) hm0 (by simpa using hk)
  refine ⟨C, hC0, fun w u hw hu t ht y => ?_⟩
  have hv := jointlySmoothOn_sub hw hu
  have h := hC (fun t => w t - u t) hv t ht y
  have e : timeDerivIter T (fun t => w t - u t) 0 t = w t - u t := rfl
  rw [e] at h
  refine h.trans (le_of_eq ?_)
  rw [← norm_ofSmooth_sq hv, ofSmooth_sub hw hu, dist_eq_norm]

end ShortTime
