import ShortTime.Nonlinear.FlowsParabolicSmooth
import ShortTime.Nonlinear.FlowsParabolicVolume

/-!
# Uniform bounds for the horizontal pullback on smooth families

Paper: Lemma `lem:flows` (b): for `|σ| ≤ 1` the operators `Π_σ` are uniformly bounded on `𝒫^m`.

* `exists_parabolicInner_hpull_le_small`: `‖Π_σ u‖²_{𝒫^m} ≤ C ‖u‖²_{𝒫^m}` for `|σ| ≤ δ`.
* `exists_parabolicInner_hpull_le`: the same for `|σ| ≤ R`, any `R`, by the group law.

Proof: `∂ₜ^j Π_σ u = Π_σ ∂ₜ^j u` (`timeDerivIter_hpull`); the pointwise jet bound
`exists_jet_bound_hpull_unif` bounds `|∇^i Π_σ w|²(x)` by the jets of `w` at `φ_σ x`, and the change
of variables `exists_integral_comp_flow_le` moves the integral back to `M`.
-/

noncomputable section

open Bundle Manifold Set Filter MeasureTheory
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral DifferentialGeometry.Analysis.Elliptic
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

namespace ShortTime

namespace HFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

variable (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
variable (g : SmoothRiemannianMetric I M) (s : ℕ)

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The spatial step: `∫ |∇^i Π_σ w|² ≤ C_J C_V Σ_{k ≤ N'} ‖∇^k w‖²` for `i ≤ N'`. -/
theorem integral_jet_hpull_le {CJ CV : ℝ} (hCJ0 : 0 ≤ CJ) {σ : ℝ} (w : SmoothCcTensor g 0 s)
    {i N' : ℕ} (hi : i ≤ N')
    (hJ : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
        ((iteratedCovGrad g 0 s i (hpull X g s σ w)).toSection x) ≤
      CJ * ∑ k : Fin (i + 1), riemannianFiberNormSq (I := I) (M := M) g 0 (s + k)
        (flow X σ x) ((iteratedCovGrad g 0 s k w).toSection (flow X σ x)))
    (hV : ∀ F : M → ℝ, Continuous F → (∀ x, 0 ≤ F x) →
      ∫ x, F (flow X σ x) ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
        CV * ∫ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) :
    ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
        ((iteratedCovGrad g 0 s i (hpull X g s σ w)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
      CJ * (CV * ∑ k ∈ Finset.range (N' + 1), ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0
        (s + k) x ((iteratedCovGrad g 0 s k w).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  have := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  set G : M → ℝ := fun y => ∑ k ∈ Finset.range (N' + 1), riemannianFiberNormSq (I := I) (M := M)
    g 0 (s + k) y ((iteratedCovGrad g 0 s k w).toSection y) with hG
  have hGc : Continuous G := continuous_finset_sum _ fun k _ =>
    continuous_fiberNormSq g (iteratedCovGrad g 0 s k w)
  have hG0 : ∀ y, 0 ≤ G y := fun y =>
    Finset.sum_nonneg fun k _ => riemannianFiberNormSq_nonneg g 0 (s + k) _ _
  have hpt : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
      ((iteratedCovGrad g 0 s i (hpull X g s σ w)).toSection x) ≤ CJ * G (flow X σ x) := by
    intro x
    refine (hJ x).trans (mul_le_mul_of_nonneg_left ?_ hCJ0)
    rw [Fin.sum_univ_eq_sum_range (fun k => riemannianFiberNormSq (I := I) (M := M) g 0 (s + k)
      (flow X σ x) ((iteratedCovGrad g 0 s k w).toSection (flow X σ x))) (i + 1)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      fun k _ _ => riemannianFiberNormSq_nonneg g 0 (s + k) _ _
  have hint1 : Integrable (fun x => riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
      ((iteratedCovGrad g 0 s i (hpull X g s σ w)).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    (continuous_fiberNormSq g _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hφc : Continuous (flow X σ) :=
    ((contMDiff_flow X).comp (contMDiff_const.prodMk contMDiff_id)).continuous
  have hint2 : Integrable (fun x => CJ * G (flow X σ x)) (riemannianVolumeMeasure (I := I) (M := M) g) :=
    (continuous_const.mul (hGc.comp hφc)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  refine (integral_mono hint1 hint2 hpt).trans ?_
  rw [integral_const_mul]
  refine mul_le_mul_of_nonneg_left ((hV G hGc hG0).trans (le_of_eq ?_)) hCJ0
  rw [hG, integral_finset_sum _ fun k _ => (continuous_fiberNormSq g _).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)]

variable {p m : ℕ} {T : ℝ}

/-- **Uniform bound for small `|σ|`**: `‖Π_σ u‖²_{𝒫^m} ≤ C ‖u‖²_{𝒫^m}`. -/
theorem exists_parabolicInner_hpull_le_small (hT : 0 < T) (p m : ℕ) :
    ∃ δ > 0, ∃ C, 0 ≤ C ∧ ∀ σ : ℝ, |σ| ≤ δ → ∀ {u : ℝ → SmoothCcTensor g 0 s}
      (hu : JointlySmoothOn g 0 s (Icc 0 T) u),
      parabolicInner g s p m T (fun t => hpull X g s σ (u t)) (fun t => hpull X g s σ (u t)) ≤
        C * parabolicInner g s p m T u u := by
  classical
  set N := 2 * p * m with hN
  choose δJ hδJ CJ hCJ0 hCJ using fun i : ℕ => exists_jet_bound_hpull_unif X g s i
  obtain ⟨δV, hδV, CV, hCV0, hCV⟩ := exists_integral_comp_flow_le X g
  obtain ⟨δ₀, hδ₀, hδ₀le⟩ : ∃ δ₀ > 0, ∀ i ∈ Finset.range (N + 1), δ₀ ≤ δJ i := by
    obtain ⟨i₀, -, hmin⟩ := (Finset.range (N + 1)).exists_min_image δJ
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
    exact ⟨δJ i₀, hδJ i₀, hmin⟩
  set CJs := ∑ i ∈ Finset.range (N + 1), CJ i with hCJs
  have hCJs0 : 0 ≤ CJs := Finset.sum_nonneg fun i _ => hCJ0 i
  have hCJle : ∀ i ∈ Finset.range (N + 1), CJ i ≤ CJs := fun i hi =>
    Finset.single_le_sum (f := CJ) (fun i _ => hCJ0 i) hi
  refine ⟨min δV δ₀, lt_min hδV hδ₀, (N + 1) * (CJs * CV), by positivity,
    fun σ hσ u hu => ?_⟩
  have hσV : |σ| ≤ δV := hσ.trans (min_le_left _ _)
  have hσJ : ∀ i ∈ Finset.range (N + 1), |σ| ≤ δJ i := fun i hi =>
    (hσ.trans (min_le_right _ _)).trans (hδ₀le i hi)
  have hP := jointlySmoothOn_hpull X g s σ hu
  -- pointwise in time
  have hpt : ∀ t ∈ Icc (0 : ℝ) T, parabolicJetInt g p m T (fun t => hpull X g s σ (u t)) t ≤
      (N + 1) * (CJs * CV) * parabolicJetInt g p m T u t := by
    intro t ht
    unfold parabolicJetInt
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    set Nj := 2 * p * (m - j) with hNj
    have hNjN : Nj ≤ N := Nat.mul_le_mul_left _ (Nat.sub_le m j)
    have hS0 : 0 ≤ ∑ k ∈ Finset.range (Nj + 1), jetNorm g s k (timeDerivIter T u j t) ^ 2 :=
      Finset.sum_nonneg fun k _ => sq_nonneg _
    have hterm : ∀ i ∈ Finset.range (Nj + 1),
        jetNorm g s i (timeDerivIter T (fun t => hpull X g s σ (u t)) j t) ^ 2 ≤
          CJs * CV * ∑ k ∈ Finset.range (Nj + 1), jetNorm g s k (timeDerivIter T u j t) ^ 2 := by
      intro i hi
      have hiNj : i ≤ Nj := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hiN : i ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
      rw [← integral_jetSq (T := T) (fun t => hpull X g s σ (u t)) j i t]
      have hjs : ∀ x, jetSq g T (fun t => hpull X g s σ (u t)) j i t x =
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
            ((iteratedCovGrad g 0 s i (hpull X g s σ (timeDerivIter T u j t))).toSection x) := by
        intro x
        unfold jetSq
        rw [timeDerivIter_hpull X g s hT hu σ j ht]
      simp only [hjs]
      refine (integral_jet_hpull_le X g s (hCJ0 i) (timeDerivIter T u j t) hiNj
        (hCJ i σ (hσJ i hiN) _) (hCV σ hσV)).trans ?_
      have hk : ∀ k, ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 (s + k) x
          ((iteratedCovGrad g 0 s k (timeDerivIter T u j t)).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
          jetNorm g s k (timeDerivIter T u j t) ^ 2 := fun k => integral_jetSq u j k t
      simp only [hk]
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hCJle i hiN) hCV0) hS0
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hcast : ((Nj + 1 : ℕ) : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hNjN
    calc ((Nj + 1 : ℕ) : ℝ) * (CJs * CV * ∑ k ∈ Finset.range (Nj + 1),
          jetNorm g s k (timeDerivIter T u j t) ^ 2)
        ≤ ((N : ℝ) + 1) * (CJs * CV * ∑ k ∈ Finset.range (Nj + 1),
          jetNorm g s k (timeDerivIter T u j t) ^ 2) :=
          mul_le_mul_of_nonneg_right hcast (mul_nonneg (mul_nonneg hCJs0 hCV0) hS0)
      _ = ((N : ℝ) + 1) * (CJs * CV) * ∑ k ∈ Finset.range (Nj + 1),
          jetNorm g s k (timeDerivIter T u j t) ^ 2 := by ring
  rw [← integral_parabolicJetInt hT hP, ← integral_parabolicJetInt hT hu,
    ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_mono_on hT.le
    ((continuousOn_parabolicJetInt hT hP p m).intervalIntegrable_of_Icc hT.le)
    ((continuousOn_const.mul (continuousOn_parabolicJetInt hT hu p m)).intervalIntegrable_of_Icc
      hT.le) hpt

/-- **Uniform bound on bounded parameter ranges**, by the group law. -/
theorem exists_parabolicInner_hpull_le (hT : 0 < T) (p m : ℕ) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ σ : ℝ, |σ| ≤ R → ∀ {u : ℝ → SmoothCcTensor g 0 s}
      (hu : JointlySmoothOn g 0 s (Icc 0 T) u),
      parabolicInner g s p m T (fun t => hpull X g s σ (u t)) (fun t => hpull X g s σ (u t)) ≤
        C * parabolicInner g s p m T u u := by
  obtain ⟨δ, hδ, C, hC0, hC⟩ := exists_parabolicInner_hpull_le_small X g s hT p m
  have hstep : ∀ n : ℕ, ∀ σ : ℝ, |σ| ≤ n * δ → ∀ {u : ℝ → SmoothCcTensor g 0 s}
      (hu : JointlySmoothOn g 0 s (Icc 0 T) u),
      parabolicInner g s p m T (fun t => hpull X g s σ (u t)) (fun t => hpull X g s σ (u t)) ≤
        C ^ n * parabolicInner g s p m T u u := by
    intro n
    induction n with
    | zero =>
      intro σ hσ u hu
      have hσ0 : σ = 0 := by
        have : |σ| ≤ 0 := by simpa using hσ
        exact abs_nonpos_iff.mp this
      subst hσ0
      simp only [hpull_zero, pow_zero, one_mul, le_refl]
    | succ n ih =>
      intro σ hσ u hu
      have hn : (0 : ℝ) < n + 1 := by positivity
      have hn' : (n : ℝ) + 1 ≠ 0 := hn.ne'
      set σ₁ := σ / (n + 1) with hσ₁
      set σ₂ := σ - σ₁ with hσ₂
      have h1 : |σ₁| ≤ δ := by
        rw [hσ₁, abs_div, abs_of_pos hn, div_le_iff₀ hn]
        push_cast at hσ
        linarith
      have h2 : |σ₂| ≤ n * δ := by
        have e : σ₂ = σ * (n / (n + 1)) := by
          have hc : σ / (↑n + 1) * (↑n + 1) = σ := div_mul_cancel₀ σ hn'
          rw [hσ₂, hσ₁]
          linear_combination -hc
        rw [e, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n / (n + 1))]
        push_cast at hσ
        calc |σ| * (n / (n + 1)) ≤ ((n + 1) * δ) * (n / (n + 1)) :=
              mul_le_mul_of_nonneg_right hσ (by positivity)
          _ = n * δ := by
              have hc : ((n : ℝ) + 1) * ((n : ℝ) + 1)⁻¹ = 1 := mul_inv_cancel₀ hn'
              rw [div_eq_mul_inv]
              linear_combination (n : ℝ) * δ * hc
      have hsum : σ₁ + σ₂ = σ := by rw [hσ₂]; ring
      have hgrp : (fun t => hpull X g s σ (u t)) =
          fun t => hpull X g s σ₁ (hpull X g s σ₂ (u t)) := by
        funext t; rw [hpull_hpull, hsum]
      have hu₂ := jointlySmoothOn_hpull X g s σ₂ hu
      rw [hgrp]
      refine (hC σ₁ h1 hu₂).trans ?_
      calc C * parabolicInner g s p m T (fun t => hpull X g s σ₂ (u t))
            (fun t => hpull X g s σ₂ (u t))
          ≤ C * (C ^ n * parabolicInner g s p m T u u) :=
            mul_le_mul_of_nonneg_left (ih σ₂ h2 hu) hC0
        _ = C ^ (n + 1) * parabolicInner g s p m T u u := by ring
  obtain ⟨n, hn⟩ := exists_nat_ge (R / δ)
  refine ⟨C ^ n, pow_nonneg hC0 n, fun σ hσ u hu => hstep n σ ?_ hu⟩
  calc |σ| ≤ R := hσ
    _ ≤ n * δ := by rwa [div_le_iff₀ hδ] at hn

end HFlow

end ShortTime
