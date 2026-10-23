import ShortTime.Nonlinear.Regularity

/-!
# Theorem A on covariant bundles, assembled (`thm:A`, `r = 0`)

From `prop:existence` (`EquationData.exists_parabolicSpace_solution`) and `prop:regularity`
(`EquationData.parabolicSpace_solution_smooth`):

* the abstract solution `v ∈ 𝒫^m_0` of `G(v) = f_ε` is a smooth family `vt`, and `u = w + vt`;
* `vt(0) = 0`, since `v ∈ 𝒫^m_0` (evaluation at `t = 0`), so `u(0) = u₀`;
* `∂ₜu - F[u] - f_ε` is a smooth family that is `0` in `𝒫^{m-1}`, hence vanishes on `[0, T₁]`
  (`ParabolicSpace.eq_zero_of_ofSmooth_eq_zero`), and `f_ε = 0` on `[0, ε]`;
* `u(0) = w(0)` is parabolic, so `u` stays parabolic on a short interval `[0, η]`
  (`EquationData.exists_parabolic_segment_of_smooth`). The final time is `min ε η`.
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

namespace EquationData

variable {s p : ℕ}

open ParabolicSpace

/-- The embedding condition for the values at `t = 0`, from `m ≥ ⌊n/2p⌋ + 4`. -/
theorem evalJet_dim_arith {n p m : ℕ} (hp : 1 ≤ p) (hm : n / (2 * p) + 4 ≤ m) :
    n / 2 + 1 + 0 ≤ 2 * p * (m - 1) := by
  have h1 := Nat.div_add_mod n (2 * p)
  have h2 := Nat.mod_lt n (show 0 < 2 * p by omega)
  have h3 : 2 * p * (n / (2 * p) + 3) ≤ 2 * p * (m - 1) := Nat.mul_le_mul_left _ (by omega)
  have h4 : 2 * p * (n / (2 * p) + 3) = 2 * p * (n / (2 * p)) + 6 * p := by ring
  generalize 2 * p * (n / (2 * p)) = A at h1 h4
  generalize n % (2 * p) = B at h1 h2
  omega

/-- **Theorem A on covariant bundles** (`thm:A`, `r = 0`), from `prop:existence` and
`prop:regularity`. -/
theorem exists_solution_cov' (D : EquationData I M 0 s p) (hp : 1 ≤ p)
    (g : SmoothRiemannianMetric I M) (u₀ : SmoothCcTensor g 0 s)
    (h₀ : ∀ x : M, D.IsParabolicAt g 0 x (covJet g 0 s (2 * p) u₀ x)) :
    ∃ T > 0, ∃ u : ℝ → SmoothCcTensor g 0 s, D.IsParabolicSolution g u₀ T u := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank ℝ E / (2 * p) + 4 ≤ m := ⟨_, le_rfl⟩
  obtain ⟨T₁, hT₁, hT₁D, lam, hlam, w, hw, hw0, hleg, -, hf, hm1, δ, hδ, 𝒩, h𝒩, hagree, hL, -,
    hsol⟩ := D.exists_parabolicSpace_solution (g := g) hp u₀ h₀ hm
  obtain ⟨V, hV, hreg⟩ :=
    D.parabolicSpace_solution_smooth hp hm hm1 hT₁ hT₁D hlam hw hleg hδ h𝒩 hagree hL
  have hball : ball (0 : zeroAtStart g s p m T₁) δ ∈ 𝓝 (0 : zeroAtStart g s p m T₁) :=
    ball_mem_nhds _ hδ
  obtain ⟨ε, ⟨v, ⟨hvV, hvδ⟩, hve⟩, hεmem⟩ :=
    ((hsol _ (inter_mem hV hball)).and self_mem_nhdsWithin).exists
  have hεpos : 0 < ε := hεmem
  set fε := cutoffFamily cutoffProfile ε (fun t => timeDeriv T₁ w t - D.nonlinFamily w t)
    with hfε_def
  have hfε : JointlySmoothOn g 0 s (Icc 0 T₁) fε :=
    jointlySmoothOn_cutoffFamily contDiff_cutoffProfile ε hf
  obtain ⟨vt, hvt, hvvt⟩ := hreg v hvV fε hfε hve
  -- `vt(0) = 0`
  have hk := evalJet_dim_arith (n := Module.finrank ℝ E) hp hm
  have hm2 : 2 ≤ m := le_trans (by norm_num) (le_trans (Nat.le_add_left 4 _) hm)
  have hm0 : 0 < m := by omega
  have hvt0 : vt 0 = 0 := by
    have hmem : ofSmooth (p := p) (m := m) vt hvt ∈ zeroAtStart g s p m T₁ := hvvt ▸ v.2
    refine smoothCcTensor_eq_of_toFun fun x => ?_
    have h1 := evalJet_eq_zero_of_mem_zeroAtStart hT₁ hm0 hk x hmem
    rw [evalJet_ofSmooth hT₁ hm0 (by rwa [Nat.sub_zero]) ⟨le_rfl, hT₁.le⟩ x hvt] at h1
    rw [Cutoff.toFun_zero]
    exact h1
  -- the solution `u = w + vt`
  set u : ℝ → SmoothCcTensor g 0 s := fun t => w t + vt t with hu_def
  have hu : JointlySmoothOn g 0 s (Icc 0 T₁) u := jointlySmoothOn_add hw hvt
  have hWv : ofSmooth (p := p) (m := m) u hu = ofSmooth w hw + (v : ParabolicSpace g s p m T₁) := by
    rw [hvvt]
    exact ofSmooth_add hw hvt
  have hvn : ‖(v : ParabolicSpace g s p m T₁)‖ < δ := by
    rw [mem_ball, dist_zero_right] at hvδ
    exact hvδ
  have hdist : dist (ofSmooth (p := p) (m := m) u hu) (ofSmooth w hw) < δ := by
    rw [hWv, dist_eq_norm, add_sub_cancel_left]
    exact hvn
  obtain ⟨hdom, hF, h𝒩u⟩ := hagree u hu hdist
  have hG : timeDerivExt hT₁ hm1 (ofSmooth (p := p) u hu) - 𝒩 (ofSmooth u hu) = ofSmooth fε hfε := by
    rw [hWv]
    exact hve
  -- `∂ₜu - F[u] - f_ε = 0` on `[0, T₁]`
  have hdiff : ∀ t ∈ Icc (0 : ℝ) T₁, timeDeriv T₁ u t - D.nonlinFamily u t - fε t = 0 := by
    have hTD := jointlySmoothOn_timeDeriv hT₁ hu
    have h1 : ofSmooth (p := p) (m := m - 1)
        (fun t => timeDeriv T₁ u t - D.nonlinFamily u t - fε t)
        (jointlySmoothOn_sub (jointlySmoothOn_sub hTD hF) hfε) = 0 := by
      rw [ofSmooth_sub (jointlySmoothOn_sub hTD hF) hfε, ofSmooth_sub hTD hF,
        ← timeDerivExt_ofSmooth hT₁ hm1 hu, ← h𝒩u, sub_eq_zero]
      exact hG
    intro t ht
    exact eq_zero_of_ofSmooth_eq_zero hT₁ (by omega) _ h1 ht
  have hFspec := (D.nonlinFamily_spec hT₁D hu hdom).1
  -- parabolicity for a short time
  have hpar0 : ∀ x, D.IsParabolicAt g 0 x (covJet g 0 s (2 * p) (w 0) x) := by
    rw [hw0]
    exact h₀
  have hwu : w 0 = u 0 := by
    change w 0 = w 0 + vt 0
    rw [hvt0, add_zero]
  obtain ⟨η, hη, hηT, lam', hlam', hseg⟩ :=
    D.exists_parabolic_segment_of_smooth g hw hu hT₁D ⟨le_rfl, hT₁⟩ hpar0 hwu
  -- the final time
  set T := min ε η with hT_def
  have hTpos : 0 < T := lt_min hεpos hη
  have hTε : T ≤ ε := min_le_left _ _
  have hTη : T ≤ η := min_le_right _ _
  have hTT₁ : T ≤ T₁ := by linarith
  have hsub : Icc (0 : ℝ) T ⊆ Icc 0 T₁ := Icc_subset_Icc le_rfl hTT₁
  refine ⟨T, hTpos, u, ⟨hTpos, hTT₁.trans hT₁D, ?_, ?_, fun t ht x => hdom t (hsub ht) x, ?_⟩, ?_⟩
  · exact ContMDiffOn.mono hu (prod_mono subset_rfl hsub)
  · change w 0 + vt 0 = u₀
    rw [hw0, hvt0, add_zero]
  · intro t ht x
    have htT₁ : t ∈ Icc (0 : ℝ) T₁ := hsub ht
    have h0 : fε t = 0 :=
      cutoffFamily_eq_zero (fun τ hτ => cutoffProfile_eq_zero hτ) hεpos _ (ht.2.trans hTε)
    have hd := hdiff t htT₁
    rw [h0, sub_zero, sub_eq_zero] at hd
    have h := hasDerivWithinAt_timeDeriv hT₁ hu htT₁ x
    rw [hd, hFspec t htT₁ x] at h
    exact h.mono hsub
  · intro t ht x
    have h := hseg t ⟨ht.1, by rw [zero_add]; exact ht.2.trans hTη⟩ x 0 ⟨le_rfl, zero_le_one⟩
    rw [zero_smul, add_zero] at h
    exact ⟨h.1, lam', h.2⟩

end EquationData

end ShortTime
