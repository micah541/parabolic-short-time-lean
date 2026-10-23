import ShortTime.Nonlinear.StabGlobal

/-!
# Uniform stability of parabolicity: the box lemma and compactness (`cor:C`)

`EquationData.stab_box`: near a point `(x₀, t₀)` of `M × [0, T]`, jets of smooth families that are
pointwise close to the jets of `u` (which are parabolic) are parabolic with a common constant.
`EquationData.exists_stab`: the same on all of `M × [0, T]`, by compactness.
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

theorem exists_pos_le_finset {α : Type*} (f : α → ℝ) (hf : ∀ a, 0 < f a) (t : Finset α) :
    ∃ c > 0, ∀ a ∈ t, c ≤ f a := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun a ha => absurd ha (Finset.notMem_empty a)⟩
  | insert a t _ ih =>
    obtain ⟨c, hc, hct⟩ := ih
    refine ⟨min c (f a), lt_min hc (hf a), fun b hb => ?_⟩
    rcases Finset.mem_insert.1 hb with rfl | hb
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hct b hb)

namespace EquationData

variable {s p : ℕ} (D : EquationData I M 0 s p)

/-- **The box lemma.** -/
theorem stab_box {T : ℝ} (hTD : T ≤ D.T₀) {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u)
    (hpar : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, D.IsParabolicAt g t x (covJet g 0 s (2 * p) (u t) x))
    (x₀ : M) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) T) :
    ∃ lam > 0, ∃ η > 0, ∃ W ∈ 𝓝 (x₀, t₀), ∀ y : M, ∀ t : ℝ, (y, t) ∈ W → t ∈ Icc (0 : ℝ) T →
      ∀ ζ : CovJetFiber I 0 s (2 * p) y,
        (∀ k : Fin (2 * p + 1), riemannianFiberNormSq (I := I) (M := M) g 0 (s + k) y
          (ζ k - covJet g 0 s (2 * p) (u t) y k) ≤ η) →
        ζ ∈ D.dom t y ∧ LegendreAt g 0 s p y (D.principal t y ζ) lam := by
  obtain ⟨hdom₀, lam₁, hL₁⟩ := hpar t₀ ht₀ x₀
  have hx₀J : x₀ ∈ jetBase (I := I) 0 s (2 * p) x₀ := mem_jetBase_self 0 s (2 * p) x₀
  set J₀ := EquationData.trivJet (I := I) x₀ x₀ (covJet g 0 s (2 * p) (u t₀) x₀) with hJ₀
  have hjet₀ : jetOfModel 0 s (2 * p) x₀ x₀ J₀ = covJet g 0 s (2 * p) (u t₀) x₀ :=
    jetOfModel_trivJet hx₀J _
  have ht₀D : t₀ ∈ Icc (0 : ℝ) D.T₀ := ⟨ht₀.1, ht₀.2.trans hTD⟩
  obtain ⟨lam, hlam, N, hN, ε, hε, hloc⟩ := D.stab_local g x₀ ht₀D J₀ (by rw [hjet₀]; exact hdom₀)
    (lam₁ := lam₁) (by rw [hjet₀]; exact hL₁)
  obtain ⟨δ, hδ, K, hK, hsmall⟩ := exists_triv_small (g := g) s (2 * p) x₀ (half_pos hε)
  refine ⟨lam, hlam, δ, hδ, ?_⟩
  -- continuity of the centre
  have hc := contMDiffOn_trivJet_covJet (N := 2 * p) hu x₀
  set S' : Set (M × ℝ) := jetBase (I := I) 0 s (2 * p) x₀ ×ˢ Icc (0 : ℝ) T with hS'
  have hq₀ : (x₀, t₀) ∈ S' := ⟨hx₀J, ht₀⟩
  have hcw := hc.continuousOn (x₀, t₀) hq₀
  have hev : ∀ᶠ q in 𝓝 (x₀, t₀), q ∈ S' → EquationData.trivJet (I := I) x₀ q.1
      (covJet g 0 s (2 * p) (u q.2) q.1) ∈ Metric.ball J₀ (ε / 2) := by
    have h := hcw.eventually (Metric.ball_mem_nhds J₀ (half_pos hε))
    exact eventually_nhdsWithin_iff.1 h
  have hfst : Tendsto (fun q : M × ℝ => q.1) (𝓝 (x₀, t₀)) (𝓝 x₀) := continuous_fst.tendsto _
  have hsnd : Tendsto (fun q : M × ℝ => q.2) (𝓝 (x₀, t₀)) (𝓝 t₀) := continuous_snd.tendsto _
  have hW : ∀ᶠ q in 𝓝 (x₀, t₀), q.1 ∈ N ∧ q.1 ∈ K ∧ q.1 ∈ jetBase (I := I) 0 s (2 * p) x₀ ∧
      |q.2 - t₀| < ε ∧ (q ∈ S' → EquationData.trivJet (I := I) x₀ q.1
        (covJet g 0 s (2 * p) (u q.2) q.1) ∈ Metric.ball J₀ (ε / 2)) := by
    refine (hfst.eventually hN).and ((hfst.eventually hK).and
      ((hfst.eventually ((isOpen_jetBase 0 s (2 * p) x₀).mem_nhds hx₀J)).and
        ((hsnd.eventually (Metric.ball_mem_nhds t₀ hε)).and hev)))
  refine ⟨_, hW, fun y t hyt ht ζ hζ => ?_⟩
  obtain ⟨hyN, hyK, hyJ, htε, hcen⟩ := hyt
  have hcen' := hcen ⟨hyJ, ht⟩
  set c := EquationData.trivJet (I := I) x₀ y (covJet g 0 s (2 * p) (u t) y) with hcdef
  have hsm : ‖EquationData.trivJet (I := I) x₀ y (ζ - covJet g 0 s (2 * p) (u t) y)‖ < ε / 2 :=
    hsmall y hyK _ (fun k => hζ k)
  have hsub : EquationData.trivJet (I := I) x₀ y (ζ - covJet g 0 s (2 * p) (u t) y) =
      EquationData.trivJet (I := I) x₀ y ζ - c := by
    funext k
    simp only [EquationData.trivJet, Pi.sub_apply, map_sub, hcdef]
  rw [hsub] at hsm
  have hJJ : ‖EquationData.trivJet (I := I) x₀ y ζ - J₀‖ < ε := by
    have h1 := Metric.mem_ball.1 hcen'
    rw [dist_eq_norm] at h1
    calc ‖EquationData.trivJet (I := I) x₀ y ζ - J₀‖
        = ‖(EquationData.trivJet (I := I) x₀ y ζ - c) + (c - J₀)‖ := by congr 1; abel
      _ ≤ ‖EquationData.trivJet (I := I) x₀ y ζ - c‖ + ‖c - J₀‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hsm h1
      _ = ε := by ring
  have htD : t ∈ Icc (0 : ℝ) D.T₀ := ⟨ht.1, ht.2.trans hTD⟩
  have hres := hloc y hyN t htD (by simpa [Real.dist_eq] using htε)
    (EquationData.trivJet (I := I) x₀ y ζ) hJJ
  rwa [jetOfModel_trivJet hyJ] at hres

end EquationData

end ShortTime
