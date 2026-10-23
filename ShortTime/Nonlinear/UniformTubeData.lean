import ShortTime.Nonlinear.FibreMapTame

/-!
# Uniform tube radius for the tame bound (stage 1)

`patch_tame` chooses the patch radius, the chart-vs-fibre constant and the margin to the domain
internally, so its tube radius is an arbitrary existential. Here the proof is factored so that these
choices are inputs (`patch_frame_data`, `patch_twist_data`, `patch_tame_gen`); the tube radius is then
`ε² / (Ctw + 1)`.
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
variable {g : SmoothRiemannianMetric I M}

section UT

variable {g : SmoothRiemannianMetric I M}

/-- **Frame data at `α`**: a chart ball with a constant-coordinate frame and the chart-vs-fibre
constant for `T⁰_{b'+i}`, `i ≤ w`. Independent of any fibre map. -/
theorem patch_frame_data (b' w : ℕ) (α : M) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      ∃ Bf : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
        Metric.closedBall (extChartAt I α α) r₀ ⊆ (extChartAt I α).target ∧
        (∀ y ∈ Metric.closedBall (extChartAt I α α) r₀, ∀ k,
          trivToE I α ((extChartAt I α).symm y) (Bf k ((extChartAt I α).symm y)) =
            Module.finBasis ℝ E k) ∧
        ∃ Cfrm : ℝ, 0 ≤ Cfrm ∧ ∀ i ≤ w, ∀ y ∈ Metric.closedBall (extChartAt I α α) (r₀ / 2),
          ∀ v : TensorRSSpace 0 (b' + i) I ((extChartAt I α).symm y),
            riemannianFiberNormSq (I := I) (M := M) g 0 (b' + i) ((extChartAt I α).symm y) v ≤
              Cfrm * ‖(trivAt I M 0 (b' + i) α).continuousLinearMapAt ℝ
                ((extChartAt I α).symm y) v‖ ^ 2 := by
  classical

  obtain ⟨Bf, hBf⟩ := exists_const_coord_fields (I := I) α (Module.finBasis ℝ E)
  have hfr : ∀ i : Fin (w + 1), ∃ C, 0 ≤ C ∧ ∀ᶠ x in 𝓝 α, ∀ v : TensorRSSpace 0 (b' + i) I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 (b' + i) x v ≤
        C * ‖(trivAt I M 0 (b' + i) α).continuousLinearMapAt ℝ x v‖ ^ 2 :=
    fun i => exists_fiberNormSq_le_triv (b' + i) α
  choose Cfr hCfr0 hCfr using hfr
  have hc : Tendsto (extChartAt I α).symm (𝓝 (extChartAt I α α)) (𝓝 α) := by
    have h := continuousAt_extChartAt_symm (I := I) α
    rwa [ContinuousAt, extChartAt_to_inv] at h
  have hev := (hc.eventually (hBf.and (Filter.eventually_all.2 hCfr))).and
    (extChartAt_target_mem_nhds (I := I) α)
  obtain ⟨r₀, hr₀, hball₀⟩ := Metric.nhds_basis_closedBall.eventually_iff.mp hev
  set c₀ := extChartAt I α α with hc₀
  have hr0 : 0 < r₀ / 2 := by positivity
  have hrr : r₀ / 2 < r₀ := by linarith
  have hball : Metric.closedBall c₀ r₀ ⊆ (extChartAt I α).target := fun y hy => (hball₀ hy).2
  have hB : ∀ y ∈ Metric.closedBall c₀ r₀, ∀ k,
      trivToE I α ((extChartAt I α).symm y) (Bf k ((extChartAt I α).symm y)) =
        Module.finBasis ℝ E k := fun y hy => (hball₀ hy).1.1
  have hsub : Metric.closedBall c₀ (r₀ / 2) ⊆ Metric.closedBall c₀ r₀ :=
    Metric.closedBall_subset_closedBall hrr.le
  have hball_r : Metric.closedBall c₀ (r₀ / 2) ⊆ (extChartAt I α).target := hsub.trans hball
  have hB_r : ∀ y ∈ Metric.closedBall c₀ (r₀ / 2), ∀ k,
      trivToE I α ((extChartAt I α).symm y) (Bf k ((extChartAt I α).symm y)) =
        Module.finBasis ℝ E k := fun y hy => hB y (hsub hy)
  set Cfrm := ∑ i, Cfr i with hCfrm
  have hCfrm0 : 0 ≤ Cfrm := Finset.sum_nonneg fun i _ => hCfr0 i
  have hfrb : ∀ i ≤ w, ∀ y ∈ Metric.closedBall c₀ (r₀ / 2),
      ∀ v : TensorRSSpace 0 (b' + i) I ((extChartAt I α).symm y),
        riemannianFiberNormSq (I := I) (M := M) g 0 (b' + i) ((extChartAt I α).symm y) v ≤
          Cfrm * ‖(trivAt I M 0 (b' + i) α).continuousLinearMapAt ℝ
            ((extChartAt I α).symm y) v‖ ^ 2 := by
    intro i hi y hy v
    refine ((hball₀ (hsub hy)).1.2 ⟨i, by omega⟩ v).trans
      (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
    exact Finset.single_le_sum (f := Cfr) (fun i _ => hCfr0 i) (Finset.mem_univ _)
  exact ⟨r₀, hr₀, Bf, hball, hB, Cfrm, hCfrm0, hfrb⟩

/-- **Chart-vs-fibre constants** on the half ball, for all ranks up to `A`. -/
theorem patch_twist_data (α : M) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hball : Metric.closedBall (extChartAt I α α) r₀ ⊆ (extChartAt I α).target) (A : ℕ) :
    ∃ Ctw : ℝ, 0 ≤ Ctw ∧ ∀ a ≤ A, ∀ y ∈ Metric.closedBall (extChartAt I α α) (r₀ / 2),
      ∀ S : SmoothCcTensor g 0 a, ‖chartRd g α S y‖ ^ 2 ≤
        Ctw * riemannianFiberNormSq (I := I) (M := M) g 0 a ((extChartAt I α).symm y)
          (S.toSection ((extChartAt I α).symm y)) := by
  classical
  set c₀ := extChartAt I α α with hc₀
  have hrr : r₀ / 2 < r₀ := by linarith

  have hsub : Metric.closedBall c₀ (r₀ / 2) ⊆ Metric.closedBall c₀ r₀ :=
    Metric.closedBall_subset_closedBall hrr.le
  have hball_r : Metric.closedBall c₀ (r₀ / 2) ⊆ (extChartAt I α).target := hsub.trans hball
  set Kx := (extChartAt I α).symm '' Metric.closedBall c₀ (r₀ / 2) with hKxdef
  have hKx : IsCompact Kx := (isCompact_closedBall c₀ (r₀ / 2)).image_of_continuousOn
    ((continuousOn_extChartAt_symm α).mono hball_r)
  have hKxs : Kx ⊆ (chartAt H α).source := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I α).map_target (hball_r hy)
  obtain ⟨Ctw, hCtw0, hCtw⟩ := exists_const_forall_le
    (P := fun a C => ∀ y ∈ Metric.closedBall c₀ (r₀ / 2), ∀ S : SmoothCcTensor g 0 a,
      ‖chartRd g α S y‖ ^ 2 ≤ C * riemannianFiberNormSq (I := I) (M := M) g 0 a
        ((extChartAt I α).symm y) (S.toSection ((extChartAt I α).symm y)))
    (fun a C C' hCC' h y hy S => (h y hy S).trans (mul_le_mul_of_nonneg_right hCC'
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 a _ _)))
    (fun a => by
      obtain ⟨C, _, hC⟩ := exists_norm_twist_le (g := g) α a hKx hKxs
      exact ⟨C, fun y hy S => by
        rw [chartRd_eq_twist α S (hball_r hy)]
        exact hC _ ⟨y, hy, rfl⟩ _⟩) A
  exact ⟨Ctw, hCtw0, hCtw⟩

/-- **The tame bound on a patch, with all choices as inputs.** The tube radius is
`ε² / (Ctw + 1)`, where `ε` is a margin of the graph of `W` to the domain. -/
theorem patch_tame_gen (Φ : FibreMap I M Λ b b') (lam : Λ) {T : ℝ} (hT : 0 < T) (hTT : T ≤ Φ.T₀)
    {W : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)} (hW : ∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (W c))
    (hWdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, valAt (fun c => W c t) x ∈ Φ.dom lam t x)
    {p : ℕ} (hp : 0 < p) (w : ℕ) (α : M)
    {r₀ : ℝ} (hr0' : 0 < r₀)
    {Bf : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (hball : Metric.closedBall (extChartAt I α α) r₀ ⊆ (extChartAt I α).target)
    (hB : ∀ y ∈ Metric.closedBall (extChartAt I α α) r₀, ∀ k,
      trivToE I α ((extChartAt I α).symm y) (Bf k ((extChartAt I α).symm y)) =
        Module.finBasis ℝ E k)
    {Cfrm : ℝ} (hCfrm0 : 0 ≤ Cfrm)
    (hfrb : ∀ i ≤ w, ∀ y ∈ Metric.closedBall (extChartAt I α α) (r₀ / 2),
      ∀ v : TensorRSSpace 0 (b' + i) I ((extChartAt I α).symm y),
        riemannianFiberNormSq (I := I) (M := M) g 0 (b' + i) ((extChartAt I α).symm y) v ≤
          Cfrm * ‖(trivAt I M 0 (b' + i) α).continuousLinearMapAt ℝ
            ((extChartAt I α).symm y) v‖ ^ 2)
    {A : ℕ} (hbA : ∀ c, b c + w ≤ A) {Ctw : ℝ} (hCtw0 : 0 ≤ Ctw)
    (hTwA : ∀ a ≤ A, ∀ y ∈ Metric.closedBall (extChartAt I α α) (r₀ / 2),
      ∀ S : SmoothCcTensor g 0 a, ‖chartRd g α S y‖ ^ 2 ≤
        Ctw * riemannianFiberNormSq (I := I) (M := M) g 0 a ((extChartAt I α).symm y)
          (S.toSection ((extChartAt I α).symm y)))
    {ε : ℝ} (hε : 0 < ε)
    (hεD : ∀ q : (ℝ × E) × ProdModel E b,
      q ∈ Metric.cthickening ε ((fun q : ℝ × E => (q, valFam α W q)) ''
        (Icc 0 T ×ˢ Metric.closedBall (extChartAt I α α) (r₀ / 2))) →
      q.1.1 ∈ Icc (0 : ℝ) T → q.1.2 ∈ Metric.closedBall (extChartAt I α α) (r₀ / 2) →
      prodOfModel b α ((extChartAt I α).symm q.1.2) q.2 ∈
        Φ.dom lam q.1.1 ((extChartAt I α).symm q.1.2)) :
    ∃ δ > 0, δ = ε ^ 2 / (Ctw + 1) ∧
      (∀ V : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c),
        (∀ c, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g 0 (b c) x ((V c t - W c t).toSection x) ≤ δ) →
        ∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ Metric.closedBall (extChartAt I α α) (r₀ / 2),
          valAt (fun c => V c t) ((extChartAt I α).symm y) ∈
            Φ.dom lam t ((extChartAt I α).symm y)) ∧
      ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ V : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c),
          (∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (V c)) →
          (∀ c, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g 0 (b c) x ((V c t - W c t).toSection x) ≤ δ) →
          (∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, valAt (fun c => V c t) x ∈ Φ.dom lam t x) →
          (∀ c j i, 2 * (2 * p * j + i) ≤ w → ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
            jetSq g T (V c) j i t x ≤ R) →
          ∀ j i, 2 * p * j + i ≤ w → ∀ t ∈ Icc (0 : ℝ) T,
            ∀ y ∈ Metric.ball (extChartAt I α α) (r₀ / 2),
              jetSq g T (Φ.apply lam V) j i t ((extChartAt I α).symm y) ≤
                C * (1 + ∑ c, ∑ j' ∈ Finset.range (j + 1), ∑ i' ∈ Finset.range (i + 1),
                  jetSq g T (V c) j' i' t ((extChartAt I α).symm y)) := by
  classical
  set c₀ := extChartAt I α α with hc₀
  have hr0 : 0 < r₀ / 2 := by positivity
  have hrr : r₀ / 2 < r₀ := by linarith

  have hsub : Metric.closedBall c₀ (r₀ / 2) ⊆ Metric.closedBall c₀ r₀ :=
    Metric.closedBall_subset_closedBall hrr.le
  have hball_r : Metric.closedBall c₀ (r₀ / 2) ⊆ (extChartAt I α).target := hsub.trans hball
  have hB_r : ∀ y ∈ Metric.closedBall c₀ (r₀ / 2), ∀ k,
      trivToE I α ((extChartAt I α).symm y) (Bf k ((extChartAt I α).symm y)) =
        Module.finBasis ℝ E k := fun y hy => hB y (hsub hy)
  have hTw : ∀ c, ∀ k ≤ w, ∀ y ∈ Metric.closedBall c₀ (r₀ / 2),
      ∀ S : SmoothCcTensor g 0 (b c + k), ‖chartRd g α S y‖ ^ 2 ≤
        Ctw * riemannianFiberNormSq (I := I) (M := M) g 0 (b c + k) ((extChartAt I α).symm y)
          (S.toSection ((extChartAt I α).symm y)) := fun c k hk =>
    hTwA _ ((Nat.add_le_add_left hk _).trans (hbA c))

  -- the Euclidean domain and the tube
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
  set K := Metric.cthickening ε Gr ∩
    ((Icc 0 T ×ˢ Metric.closedBall c₀ (r₀ / 2)) ×ˢ (univ : Set (ProdModel E b))) with hKdef
  have hK : IsCompact K := hGc.cthickening.inter_right
    ((isClosed_Icc.prod Metric.isClosed_closedBall).prod isClosed_univ)
  have hKt : K ⊆ tα := fun p hp => ⟨⟨⟨hp.2.1.1, hball_r hp.2.1.2⟩, mem_univ _⟩,
    hinW p.1.1 hp.2.1.1 p.1.2 (hball_r hp.2.1.2) p.2 (hεD p hp.1 hp.2.1.1 hp.2.1.2)⟩

  set δ := ε ^ 2 / (Ctw + 1) with hδdef
  have hδ : 0 < δ := by positivity
  have htube : ∀ V : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c),
      (∀ c, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 0 (b c) x ((V c t - W c t).toSection x) ≤ δ) →
      ∀ q ∈ Icc 0 T ×ˢ Metric.closedBall c₀ (r₀ / 2), (q, valFam α V q) ∈ K := by
    intro V hVδ q hq
    refine ⟨Metric.mem_cthickening_of_dist_le _ (q, valFam α W q) ε Gr ⟨q, hq, rfl⟩ ?_,
      ⟨hq, mem_univ _⟩⟩
    rw [Prod.dist_eq, dist_self, dist_eq_norm]
    refine max_le hε.le ((pi_norm_le_iff_of_nonneg hε.le).2 fun c => ?_)
    have h1 := hTw c 0 (Nat.zero_le _) q.2 hq.2 (V c q.1 - W c q.1)
    have h2 := hVδ c q.1 hq.1 ((extChartAt I α).symm q.2)
    have h3 : ‖chartRd g α (V c q.1 - W c q.1) q.2‖ ^ 2 ≤ ε ^ 2 :=
      h1.trans ((mul_le_mul_of_nonneg_left h2 hCtw0).trans (div_aux hCtw0))
    rw [chartRd_sub] at h3
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hε.le (by norm_num)).mp h3
  have hdomV : ∀ V : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c),
      (∀ c, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g 0 (b c) x ((V c t - W c t).toSection x) ≤ δ) →
      ∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ Metric.closedBall c₀ (r₀ / 2),
        valAt (fun c => V c t) ((extChartAt I α).symm y) ∈
          Φ.dom lam t ((extChartAt I α).symm y) := by
    intro V hVδ t ht y hy
    have h := hdomW _ (hKt (htube V hVδ (t, y) ⟨ht, hy⟩))
    dsimp only at h
    rwa [prodOfModel_valFam V (q := (t, y)) (hball_r hy)] at h
  refine ⟨δ, hδ, rfl, hdomV, fun R => ?_⟩
  -- the constants
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_const_forall_fintype
    (P := fun c C => ∀ S : SmoothCcTensor g 0 (b c), ∀ n ≤ w, ∀ y ∈ Metric.closedBall c₀ (r₀ / 2),
      ‖iteratedFDeriv ℝ n (chartRd g α S) y‖ ≤
        C * ∑ k ∈ Finset.range (n + 1), ‖chartRd g α (iteratedCovGrad g 0 (b c) k S) y‖)
    (fun c C C' h H S n hn y hy => (H S n hn y hy).trans
      (mul_le_mul_of_nonneg_right h (Finset.sum_nonneg fun _ _ => norm_nonneg _)))
    (fun c => by
      obtain ⟨C, _, hC⟩ := exists_const_forall_le
        (P := fun n C => ∀ S : SmoothCcTensor g 0 (b c), ∀ y ∈ Metric.closedBall c₀ (r₀ / 2),
          ‖iteratedFDeriv ℝ n (chartRd g α S) y‖ ≤
            C * ∑ k ∈ Finset.range (n + 1), ‖chartRd g α (iteratedCovGrad g 0 (b c) k S) y‖)
        (fun n C C' h H S y hy => (H S y hy).trans
          (mul_le_mul_of_nonneg_right h (Finset.sum_nonneg fun _ _ => norm_nonneg _)))
        (fun n => by
          obtain ⟨C, _, hC⟩ := exists_iter_chartRd_le hball hB hrr (b c) n
          exact ⟨C, fun S y hy => hC S n le_rfl y hy⟩) w
      exact ⟨C, fun S n hn y hy => hC n hn S y hy⟩)
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_const_forall_le
    (P := fun i C => ∀ S : SmoothCcTensor g 0 b', ∀ y ∈ Metric.closedBall c₀ (r₀ / 2),
      ‖chartRd g α (iteratedCovGrad g 0 b' i S) y‖ ≤
        C * ∑ m ∈ Finset.range (i + 1), ‖iteratedFDeriv ℝ m (chartRd g α S) y‖)
    (fun i C C' h H S y hy => (H S y hy).trans
      (mul_le_mul_of_nonneg_right h (Finset.sum_nonneg fun _ _ => norm_nonneg _)))
    (fun i => by
      obtain ⟨C, _, hC⟩ := exists_chartRd_iter_le hball hB hrr b' i
      exact ⟨C, hC⟩) w
  set R' := C₂ * Real.sqrt Ctw * (Fintype.card ι * ((w : ℝ) + 1) * Real.sqrt (max R 0)) with hR'def
  have hR'0 : 0 ≤ R' := by positivity
  obtain ⟨CF, hCF0, hCF⟩ := exists_const_forall_le
    (P := fun n C => ∀ (u : ℝ × E → ProdModel E b) (s : Set (ℝ × E)), UniqueDiffOn ℝ s →
      ContDiffOn ℝ n u s → MapsTo (fun x => (x, u x)) s tα → ∀ z ∈ s, (z, u z) ∈ K →
      ∀ v : Fin n → ℝ × E, (∀ i, ‖v i‖ ≤ 1) → ∀ wt : Fin n → ℕ,
      (∀ Bs : Finset (Fin n), Bs.Nonempty → 2 * ∑ i ∈ Bs, wt i ≤ ∑ i, wt i →
        ‖FaaDiBruno.blockDeriv u s z v Bs‖ ≤ R') →
      ‖iteratedFDerivWithin ℝ n (fun x => Φ.euclRep lam α (x, u x)) s z v‖ ≤
        C * (1 + ∑ Bs ∈ Finset.univ.filter (fun Bs : Finset (Fin n) => Bs.Nonempty),
          ‖FaaDiBruno.blockDeriv u s z v Bs‖))
    (fun n C C' h H u s h1 h2 h3 z hz hzK v hv wt hsm => (H u s h1 h2 h3 z hz hzK v hv wt hsm).trans
      (mul_le_mul_of_nonneg_right h (by positivity)))
    (fun n => by
      obtain ⟨C, _, hC⟩ := FaaDiBruno.exists_tame_bound_graph
        (hsmooth.of_le (JetRec.natCast_le_infty n)) htα hK hKt hR'0
      exact ⟨C, hC⟩) w
  refine ⟨tameConst Cfrm C₁ C₂ Ctw CF (∑ k, ‖cB E k‖) w (Module.finrank ℝ E) (Fintype.card ι),
    tameConst_nonneg _ _ _ hCfrm0, fun V hV hVδ hdom hR j i hji t ht y hy => ?_⟩
  exact core_bound Φ lam hT hTT hball_r hB_r hp hKt hC₂0 hCtw0 hC₁0 hCfrm0 hCF0
    (fun c S n hn y hy => hC₂ c S n hn y hy) hTw (fun i hi S y hy => hC₁ i hi S y hy)
    hfrb hCF le_rfl hV hdom hR
    (fun q hq => htube V hVδ q ⟨hq.1, Metric.ball_subset_closedBall hq.2⟩) hji ht hy

end UT

end FibreMap

end ShortTime
