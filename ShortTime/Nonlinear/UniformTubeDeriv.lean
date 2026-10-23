import ShortTime.Nonlinear.UniformTubeGen
import ShortTime.Nonlinear.FibreCalcBound

/-!
# Uniform tube radius for the tame bound (stage 3b): the fibre derivatives

For every fibre map `Φ` there is one `δ > 0` such that `TameGood (Φ.fibreDeriv k)` holds with tube
radius `δ` for **all** `k`.
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

section UT4

variable {g : SmoothRiemannianMetric I M}

/-- The radius obtained from a finite family of patch radii. -/
theorem exists_inv_sum_radius {Aset : Finset M} (δ : M → ℝ) (hδ : ∀ α, 0 < δ α) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ α ∈ Aset, δ₀ ≤ δ α := by
  have hS0 : 0 ≤ ∑ α ∈ Aset, (δ α)⁻¹ := Finset.sum_nonneg fun α _ => (inv_pos.2 (hδ α)).le
  refine ⟨(1 + ∑ α ∈ Aset, (δ α)⁻¹)⁻¹, by positivity, fun α hα => ?_⟩
  have h1 : (δ α)⁻¹ ≤ 1 + ∑ α ∈ Aset, (δ α)⁻¹ := by
    have := Finset.single_le_sum (f := fun α => (δ α)⁻¹) (fun α _ => (inv_pos.2 (hδ α)).le) hα
    linarith
  calc (1 + ∑ α ∈ Aset, (δ α)⁻¹)⁻¹ ≤ ((δ α)⁻¹)⁻¹ := inv_anti₀ (inv_pos.2 (hδ α)) h1
    _ = δ α := inv_inv _

namespace FibreMap

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] {ι : Type*} [Fintype ι]
  {b : ι → ℕ} {b' : ℕ}

theorem dist_mbase_le {a : ι → ℕ} {b₀ : ι → ℕ} {k : ℕ}
    (z z' : ProdModel E (blkRanks a b₀ k)) :
    dist (mbase z) (mbase z') ≤ dist z z' := by
  refine (dist_pi_le_iff dist_nonneg).2 fun c => ?_
  exact dist_le_pi_dist z z' (Sum.inl c)

/-- **A uniform tube radius for all the fibre derivatives.** -/
theorem exists_uniform_good_deriv (Φ : FibreMap I M Λ b b') (lam : Λ) {T : ℝ} (hT : 0 < T)
    (hTT : T ≤ Φ.T₀) {W : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)}
    (hW : ∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (W c))
    (hWdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, valAt (fun c => W c t) x ∈ Φ.dom lam t x)
    {p : ℕ} (hp : 0 < p) (w : ℕ) :
    ∃ δ > 0, ∀ k : ℕ, TameGood (Φ.fibreDeriv k) lam T
      (joinFam W (zeroBlk (g := g) (b₀ := b) (k := k))) p w δ := by
  classical
  obtain ⟨D⟩ := PatchData.nonempty (I := I) (M := M) (g := g) b' w ((∑ c, b c) + w)
  have hmar := fun α : M => exists_margin Φ lam hT hTT hW hWdom α (D.hr₀ α) (D.hball α)
  choose ε hε hεΦ using hmar
  obtain ⟨Afin, hcov⟩ := exists_finite_cover (I := I) (M := M) (fun α => D.r₀ α / 2)
    (fun α => by have := D.hr₀ α; positivity)
  obtain ⟨δ₀, hδ₀, hδ₀le⟩ := exists_inv_sum_radius (Aset := Afin)
    (fun α => ε α ^ 2 / (D.Ctw α + 1))
    (fun α => by have := hε α; have := D.hCtw0 α; positivity)
  refine ⟨δ₀, hδ₀, fun k => ?_⟩
  have hbA : ∀ q, blkRanks b b k q + w ≤ (∑ c, b c) + w := by
    intro q
    refine Nat.add_le_add_right ?_ w
    rcases q with c | ⟨l, c⟩
    · exact Finset.single_le_sum (f := b) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
    · exact Finset.single_le_sum (f := b) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
  refine tame_good_of_data D (Φ.fibreDeriv k) lam hT hTT
    (jointlySmoothOn_joinFam hW jointlySmoothOn_zeroBlk) (fun t ht x => hWdom t ht x) hp hbA ε hε
    (fun α q hq ht hy => ?_) Afin hcov hδ₀le
  set f : (ℝ × E) × ProdModel E (blkRanks b b k) → (ℝ × E) × ProdModel E b :=
    fun q => (q.1, mbase q.2) with hf
  have hlip : ∀ x y, dist (f x) (f y) ≤ 1 * dist x y := by
    intro x y
    rw [one_mul, Prod.dist_eq, Prod.dist_eq]
    exact max_le_max le_rfl (dist_mbase_le _ _)
  have h1 := cthickening_image_le f one_pos hlip (hε α).le hq
  rw [one_mul] at h1
  have h2 : f '' ((fun q : ℝ × E => (q, valFam α (joinFam W (zeroBlk (g := g) (b₀ := b)
      (k := k))) q)) '' (Icc 0 T ×ˢ Metric.closedBall (extChartAt I α α) (D.r₀ α / 2))) ⊆
      (fun q : ℝ × E => (q, valFam α W q)) ''
        (Icc 0 T ×ˢ Metric.closedBall (extChartAt I α α) (D.r₀ α / 2)) := by
    rintro _ ⟨_, ⟨q, hq', rfl⟩, rfl⟩
    exact ⟨q, hq', rfl⟩
  have h3 := hεΦ α (f q) (Metric.cthickening_subset_of_subset _ h2 h1) ht hy
  have h4 : fbase (I := I) (prodOfModel (I := I) (blkRanks b b k) α
      ((extChartAt I α).symm q.1.2) q.2) ∈ Φ.dom lam q.1.1 ((extChartAt I α).symm q.1.2) := by
    rw [fbase_prodOfModel]
    exact h3
  exact h4

end FibreMap

end UT4

end ShortTime
