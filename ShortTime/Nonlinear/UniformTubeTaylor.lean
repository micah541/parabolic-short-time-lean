import ShortTime.Nonlinear.UniformTubeDeriv
import ShortTime.Nonlinear.FibreCalcRemainder

/-!
# Uniform tube radius for the tame bound (stage 3c): the Taylor remainders

For every fibre map `Φ` there is one `δ > 0` such that `TameGood (Φ.taylorMap k)` holds with tube
radius `δ` for all `k`.
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

section UT5

variable {g : SmoothRiemannianMetric I M}

namespace FibreMap

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] {ι : Type*} [Fintype ι]
  {b : ι → ℕ} {b' : ℕ}

theorem chartRd_zero' (α : M) {a : ℕ} (y : E) : chartRd g α (0 : SmoothCcTensor g 0 a) y = 0 := by
  have h := chartRd_sub (g := g) α (0 : SmoothCcTensor g 0 a) 0 y
  rw [sub_self, sub_self] at h
  exact h

/-- The first component of the pair in model coordinates. -/
def mfst {k : ℕ} (z : ProdModel E (blkRanks (pairRanks b) b k)) : ProdModel E b :=
  fun c => z (.inl (.inl c))

/-- The second component of the pair in model coordinates. -/
def msnd {k : ℕ} (z : ProdModel E (blkRanks (pairRanks b) b k)) : ProdModel E b :=
  fun c => z (.inl (.inr c))

theorem pair_prodOfModel {k : ℕ} (x₀ y : M) (τ : ℝ)
    (z : ProdModel E (blkRanks (pairRanks b) b k)) :
    pfst (I := I) (fbase (I := I) (prodOfModel (I := I) (blkRanks (pairRanks b) b k) x₀ y z)) +
      τ • psnd (I := I) (fbase (I := I) (prodOfModel (I := I) (blkRanks (pairRanks b) b k) x₀ y z)) =
      prodOfModel (I := I) b x₀ y (mfst z + τ • msnd z) := by
  funext c
  change (trivAt I M 0 (b c) x₀).symmL ℝ y (mfst z c) +
      τ • (trivAt I M 0 (b c) x₀).symmL ℝ y (msnd z c) =
    (trivAt I M 0 (b c) x₀).symmL ℝ y (mfst z c + τ • msnd z c)
  rw [map_add, map_smul]

theorem dist_mfst_msnd_le {k : ℕ} {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1)
    (z z' : ProdModel E (blkRanks (pairRanks b) b k)) :
    dist (mfst z + τ • msnd z) (mfst z' + τ • msnd z') ≤ 2 * dist z z' := by
  have h1 : dist (mfst z) (mfst z') ≤ dist z z' :=
    (dist_pi_le_iff dist_nonneg).2 fun c => dist_le_pi_dist z z' (Sum.inl (Sum.inl c))
  have h2 : dist (msnd z) (msnd z') ≤ dist z z' :=
    (dist_pi_le_iff dist_nonneg).2 fun c => dist_le_pi_dist z z' (Sum.inl (Sum.inr c))
  have h3 : dist (τ • msnd z) (τ • msnd z') ≤ dist z z' := by
    rw [dist_smul₀, Real.norm_of_nonneg hτ.1]
    calc τ * dist (msnd z) (msnd z') ≤ 1 * dist (msnd z) (msnd z') :=
          mul_le_mul_of_nonneg_right hτ.2 dist_nonneg
      _ ≤ dist z z' := by rw [one_mul]; exact h2
  calc dist (mfst z + τ • msnd z) (mfst z' + τ • msnd z')
      ≤ dist (mfst z) (mfst z') + dist (τ • msnd z) (τ • msnd z') := dist_add_add_le _ _ _ _
    _ ≤ 2 * dist z z' := by linarith

/-- **A uniform tube radius for all the Taylor remainders.** -/
theorem exists_uniform_good_taylor (Φ : FibreMap I M Λ b b') (lam : Λ) {T : ℝ} (hT : 0 < T)
    (hTT : T ≤ Φ.T₀) {W : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)}
    (hW : ∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (W c))
    (hWdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, valAt (fun c => W c t) x ∈ Φ.dom lam t x)
    {p : ℕ} (hp : 0 < p) (w : ℕ) :
    ∃ δ > 0, ∀ k : ℕ, TameGood (Φ.taylorMap k) lam T
      (joinFam (pairFam W (fun _ _ => 0)) (zeroBlk (g := g) (b₀ := b) (k := k + 2))) p w δ := by
  classical
  obtain ⟨D⟩ := PatchData.nonempty (I := I) (M := M) (g := g) b' w ((∑ c, b c) + w)
  have hmar := fun α : M => exists_margin Φ lam hT hTT hW hWdom α (D.hr₀ α) (D.hball α)
  choose ε hε hεΦ using hmar
  obtain ⟨Afin, hcov⟩ := exists_finite_cover (I := I) (M := M) (fun α => D.r₀ α / 2)
    (fun α => by have := D.hr₀ α; positivity)
  obtain ⟨δ₀, hδ₀, hδ₀le⟩ := exists_inv_sum_radius (Aset := Afin)
    (fun α => (ε α / 2) ^ 2 / (D.Ctw α + 1))
    (fun α => by have := hε α; have := D.hCtw0 α; positivity)
  refine ⟨δ₀, hδ₀, fun k => ?_⟩
  have hz : ∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (fun _ : ℝ => (0 : SmoothCcTensor g 0 (b c))) :=
    fun c => jointlySmoothOn_const g _ (0 : SmoothCcTensor g 0 (b c))
  have hbA : ∀ q, blkRanks (pairRanks b) b (k + 2) q + w ≤ (∑ c, b c) + w := by
    intro q
    refine Nat.add_le_add_right ?_ w
    rcases q with (c | c) | ⟨l, c⟩
    · exact Finset.single_le_sum (f := b) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
    · exact Finset.single_le_sum (f := b) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
    · exact Finset.single_le_sum (f := b) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
  refine tame_good_of_data D (Φ.taylorMap k) lam hT hTT
    (jointlySmoothOn_joinFam (jointlySmoothOn_pairFam hW hz) jointlySmoothOn_zeroBlk)
    (fun t ht x τ _ => by
      have e : psnd (fbase (valAt (fun q => joinFam (pairFam W fun _ _ => 0)
          (zeroBlk (g := g) (b₀ := b) (k := k + 2)) q t) x)) = 0 := by
        funext c
        exact toSection_zero_apply x
      show pfst (fbase _) + τ • psnd (fbase _) ∈ Φ.dom lam t x
      rw [e, smul_zero, add_zero]
      exact hWdom t ht x) hp hbA (fun α => ε α / 2) (fun α => by have := hε α; positivity)
    (fun α q hq ht hy => ?_) Afin hcov hδ₀le
  intro τ hτ
  set f : (ℝ × E) × ProdModel E (blkRanks (pairRanks b) b (k + 2)) → (ℝ × E) × ProdModel E b :=
    fun q => (q.1, mfst q.2 + τ • msnd q.2) with hf
  have hlip : ∀ x y, dist (f x) (f y) ≤ 2 * dist x y := by
    intro x y
    have h := dist_mfst_msnd_le hτ x.2 y.2
    rw [Prod.dist_eq, Prod.dist_eq]
    change max (dist x.1 y.1) (dist (mfst x.2 + τ • msnd x.2) (mfst y.2 + τ • msnd y.2)) ≤
      2 * max (dist x.1 y.1) (dist x.2 y.2)
    have hm1 := le_max_left (dist x.1 y.1) (dist x.2 y.2)
    have hm2 := le_max_right (dist x.1 y.1) (dist x.2 y.2)
    have hd := dist_nonneg (x := x.1) (y := y.1)
    refine max_le (by linarith) ?_
    linarith
  have h1 := cthickening_image_le f two_pos hlip (by have := hε α; positivity) hq
  rw [show 2 * (ε α / 2) = ε α by ring] at h1
  have h2 : f '' ((fun q : ℝ × E => (q, valFam α (joinFam (pairFam W (fun _ _ => 0))
      (zeroBlk (g := g) (b₀ := b) (k := k + 2))) q)) ''
      (Icc 0 T ×ˢ Metric.closedBall (extChartAt I α α) (D.r₀ α / 2))) ⊆
      (fun q : ℝ × E => (q, valFam α W q)) ''
        (Icc 0 T ×ˢ Metric.closedBall (extChartAt I α α) (D.r₀ α / 2)) := by
    rintro _ ⟨_, ⟨q, hq', rfl⟩, rfl⟩
    refine ⟨q, hq', ?_⟩
    simp only [hf]
    refine Prod.ext rfl ?_
    funext c
    show chartFam g α (W c) q = chartFam g α (W c) q +
      τ • chartFam g α (fun _ => (0 : SmoothCcTensor g 0 (b c))) q
    rw [show chartFam g α (fun _ => (0 : SmoothCcTensor g 0 (b c))) q = 0 from
      chartRd_zero' α q.2, smul_zero, add_zero]
  have h3 := hεΦ α (f q) (Metric.cthickening_subset_of_subset _ h2 h1) ht hy
  have e := pair_prodOfModel (I := I) (b := b) (k := k + 2) α ((extChartAt I α).symm q.1.2) τ q.2
  rw [e]
  exact h3

end FibreMap

end UT5

end ShortTime
