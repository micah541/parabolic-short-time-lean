import ShortTime.Nonlinear.UniformTubeData

/-!
# Uniform tube radius for the tame bound (stage 2)

* `TameGood Φ lam T W p w δ`: the conclusion of `exists_tame_pointwise` holds with tube radius `δ`.
  It is monotone in `δ`.
* `PatchGood`: the same on one chart patch.
* `tame_cover_gen`: patch data over a *given* finite cover give `TameGood` for every `δ₀` below all
  the patch radii.
* `exists_margin`: a margin `ε` of the graph of `W` to the domain, in a chart ball.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter Topology
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Elliptic DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff

namespace ShortTime


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

variable {ι : Type*} [Fintype ι]

namespace FibreMap

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] {b : ι → ℕ} {b' : ℕ}

section UT2

variable {g : SmoothRiemannianMetric I M}

/-- The conclusion of `exists_tame_pointwise` with tube radius `δ`. -/
def TameGood (Φ : FibreMap I M Λ b b') (lam : Λ) (T : ℝ)
    (W : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)) (p w : ℕ) (δ : ℝ) : Prop :=
  (∀ V : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c),
      (∀ c, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 0 (b c) x ((V c t - W c t).toSection x) ≤ δ) →
      ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, FibreMap.valAt (fun c => V c t) x ∈ Φ.dom lam t x) ∧
    ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ V : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c), (∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (V c)) →
        (∀ c, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 0 (b c) x ((V c t - W c t).toSection x) ≤ δ) →
        (∀ c j i, 2 * (2 * p * j + i) ≤ w → ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
          jetSq g T (V c) j i t x ≤ R) →
        ∀ j i, 2 * p * j + i ≤ w → ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
          jetSq g T (Φ.apply lam V) j i t x ≤
            C * (1 + ∑ c, ∑ j' ∈ Finset.range (j + 1), ∑ i' ∈ Finset.range (i + 1),
              jetSq g T (V c) j' i' t x)

theorem TameGood.mono {Φ : FibreMap I M Λ b b'} {lam : Λ} {T : ℝ}
    {W : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)} {p w : ℕ} {δ δ' : ℝ}
    (h : TameGood Φ lam T W p w δ) (hδ : δ' ≤ δ) : TameGood Φ lam T W p w δ' := by
  refine ⟨fun V hV => h.1 V fun c t ht x => (hV c t ht x).trans hδ, fun R => ?_⟩
  obtain ⟨C, hC0, hC⟩ := h.2 R
  exact ⟨C, hC0, fun V hVs hV hR => hC V hVs (fun c t ht x => (hV c t ht x).trans hδ) hR⟩

/-- The conclusion of `patch_tame` with radii `r`, `δ` at `α`. -/
def PatchGood (Φ : FibreMap I M Λ b b') (lam : Λ) (T : ℝ)
    (W : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)) (p w : ℕ) (α : M) (r δ : ℝ) : Prop :=
  (∀ V : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c),
        (∀ c, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 0 (b c) x ((V c t - W c t).toSection x) ≤ δ) →
        ∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ Metric.closedBall (extChartAt I α α) r,
          FibreMap.valAt (fun c => V c t) ((extChartAt I α).symm y) ∈
            Φ.dom lam t ((extChartAt I α).symm y)) ∧
      ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ V : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c),
          (∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (V c)) →
          (∀ c, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g 0 (b c) x ((V c t - W c t).toSection x) ≤ δ) →
          (∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, FibreMap.valAt (fun c => V c t) x ∈ Φ.dom lam t x) →
          (∀ c j i, 2 * (2 * p * j + i) ≤ w → ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
            jetSq g T (V c) j i t x ≤ R) →
          ∀ j i, 2 * p * j + i ≤ w → ∀ t ∈ Icc (0 : ℝ) T,
            ∀ y ∈ Metric.ball (extChartAt I α α) r,
              jetSq g T (Φ.apply lam V) j i t ((extChartAt I α).symm y) ≤
                C * (1 + ∑ c, ∑ j' ∈ Finset.range (j + 1), ∑ i' ∈ Finset.range (i + 1),
                  jetSq g T (V c) j' i' t ((extChartAt I α).symm y))

/-- **Covering by given patches**: patch data over a finite cover, with positive radii `r α`, give
`TameGood` for every `δ₀` below all patch radii `δ α`, `α ∈ A`. -/
theorem tame_cover_gen (Φ : FibreMap I M Λ b b') (lam : Λ) {T : ℝ}
    {W : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)} {p w : ℕ}
    {r δ : M → ℝ} (hP : ∀ α, PatchGood Φ lam T W p w α (r α) (δ α))
    (A : Finset M)
    (hcov : ∀ x : M, ∃ α ∈ A, x ∈ (extChartAt I α).source ∩
      extChartAt I α ⁻¹' Metric.ball (extChartAt I α α) (r α))
    {δ₀ : ℝ} (hδ₀le : ∀ α ∈ A, δ₀ ≤ δ α) : TameGood Φ lam T W p w δ₀ := by
  classical
  have hleft : ∀ α, ∀ x ∈ (extChartAt I α).source ∩
      extChartAt I α ⁻¹' Metric.ball (extChartAt I α α) (r α),
      (extChartAt I α).symm (extChartAt I α x) = x := fun α x hx =>
    (extChartAt I α).left_inv hx.1
  have hdomall : ∀ V : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c),
      (∀ c, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 0 (b c) x ((V c t - W c t).toSection x) ≤ δ₀) →
      ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, FibreMap.valAt (fun c => V c t) x ∈ Φ.dom lam t x := by
    intro V hVδ t ht x
    obtain ⟨α, hα, hx⟩ := hcov x
    have h := (hP α).1 V (fun c t ht x => (hVδ c t ht x).trans (hδ₀le α hα)) t ht
      (extChartAt I α x) (Metric.ball_subset_closedBall hx.2)
    rwa [hleft α x hx] at h
  refine ⟨hdomall, fun R => ?_⟩
  choose C hC0 hC using fun α => (hP α).2 R
  refine ⟨∑ α ∈ A, C α, Finset.sum_nonneg fun α _ => hC0 α,
    fun V hV hVδ hR j i hji t ht x => ?_⟩
  obtain ⟨α, hα, hx⟩ := hcov x
  have h := hC α V hV (fun c t ht x => (hVδ c t ht x).trans (hδ₀le α hα)) (hdomall V hVδ) hR
    j i hji t ht (extChartAt I α x) hx.2
  rw [hleft α x hx] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · exact Finset.single_le_sum (f := C) (fun α _ => hC0 α) hα
  · have : 0 ≤ ∑ c, ∑ j' ∈ Finset.range (j + 1), ∑ i' ∈ Finset.range (i + 1),
        jetSq g T (V c) j' i' t x :=
      Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 _ _ _
    linarith

/-- A finite cover of `M` by the chart balls of radii `r α > 0`. -/
theorem exists_finite_cover (r : M → ℝ) (hr : ∀ α, 0 < r α) :
    ∃ A : Finset M, ∀ x : M, ∃ α ∈ A, x ∈ (extChartAt I α).source ∩
      extChartAt I α ⁻¹' Metric.ball (extChartAt I α α) (r α) := by
  set O : M → Set M := fun α =>
    (extChartAt I α).source ∩ extChartAt I α ⁻¹' Metric.ball (extChartAt I α α) (r α) with hOdef
  have hO : ∀ α, IsOpen (O α) := fun α => isOpen_extChartAt_preimage' α Metric.isOpen_ball
  have hαO : ∀ α, α ∈ O α := fun α => ⟨mem_extChartAt_source α, Metric.mem_ball_self (hr α)⟩
  obtain ⟨A, hA⟩ := isCompact_univ.elim_finite_subcover O hO
    (fun x _ => mem_iUnion.2 ⟨x, hαO x⟩)
  refine ⟨A, fun x => ?_⟩
  have := hA (mem_univ x)
  simp only [mem_iUnion] at this
  obtain ⟨α, hα, hx⟩ := this
  exact ⟨α, hα, hx⟩

/-- **A margin of the graph of `W` to the domain** inside a chart ball. -/
theorem exists_margin (Φ : FibreMap I M Λ b b') (lam : Λ) {T : ℝ} (hT : 0 < T) (hTT : T ≤ Φ.T₀)
    {W : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)} (hW : ∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (W c))
    (hWdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, FibreMap.valAt (fun c => W c t) x ∈ Φ.dom lam t x)
    (α : M) {r₀ : ℝ} (hr0' : 0 < r₀)
    (hball : Metric.closedBall (extChartAt I α α) r₀ ⊆ (extChartAt I α).target) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ q : (ℝ × E) × ProdModel E b,
      q ∈ Metric.cthickening ε ((fun q : ℝ × E => (q, valFam α W q)) ''
        (Icc 0 T ×ˢ Metric.closedBall (extChartAt I α α) (r₀ / 2))) →
      q.1.1 ∈ Icc (0 : ℝ) T → q.1.2 ∈ Metric.closedBall (extChartAt I α α) (r₀ / 2) →
      prodOfModel b α ((extChartAt I α).symm q.1.2) q.2 ∈
        Φ.dom lam q.1.1 ((extChartAt I α).symm q.1.2) := by
  classical
  set c₀ := extChartAt I α α with hc₀
  have hrr : r₀ / 2 < r₀ := by linarith
  have hsub : Metric.closedBall c₀ (r₀ / 2) ⊆ Metric.closedBall c₀ r₀ :=
    Metric.closedBall_subset_closedBall hrr.le
  have hball_r : Metric.closedBall c₀ (r₀ / 2) ⊆ (extChartAt I α).target := hsub.trans hball

  obtain ⟨Wd, hWdo, hsmooth, hdomW, hinW⟩ := Φ.exists_euclDom lam α hTT
  set tα := ((Icc 0 T ×ˢ (extChartAt I α).target) ×ˢ (univ : Set (ProdModel E b))) ∩ Wd with htαdef
  have htα : UniqueDiffOn ℝ tα :=
    (UniqueDiffOn.prod (UniqueDiffOn.prod (uniqueDiffOn_Icc hT)
      (isOpen_extChartAt_target α).uniqueDiffOn) uniqueDiffOn_univ).inter hWdo
  have hUW := contDiffOn_valFam α hW
  set Gr := (fun q : ℝ × E => (q, valFam α W q)) '' (Icc 0 T ×ˢ Metric.closedBall c₀ (r₀ / 2))
    with hGrdef
  have hGc : IsCompact Gr := (isCompact_Icc.prod (isCompact_closedBall c₀ (r₀ / 2))).image_of_continuousOn
    (continuousOn_id.prodMk (hUW.continuousOn.mono (prod_mono le_rfl hball_r)))
  have hGW : Gr ⊆ Wd := by
    rintro _ ⟨q, hq, rfl⟩
    refine hinW q.1 hq.1 q.2 (hball_r hq.2) _ ?_
    rw [prodOfModel_valFam W (hball_r hq.2)]
    exact hWdom q.1 hq.1 _
  obtain ⟨ε, hε, hεW⟩ := hGc.exists_cthickening_subset_open hWdo hGW
  exact ⟨ε, hε, fun q hq ht hy => hdomW q ⟨⟨⟨ht, hball_r hy⟩, mem_univ _⟩, hεW hq⟩⟩

end UT2

end FibreMap

end ShortTime
