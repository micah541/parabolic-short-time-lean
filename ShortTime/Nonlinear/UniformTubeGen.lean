import ShortTime.Nonlinear.UniformTubeCover

/-!
# Uniform tube radius for the tame bound (stage 3a)

`PatchData`: the choices of `patch_tame` that do not depend on the fibre map (patch radii, frames,
chart-vs-fibre constants for all ranks up to `A`). `tame_good_of_data`: with such data, margins `ε α`
for a fibre map `G`, and a finite cover, `TameGood` holds for every `δ₀ ≤ ε α ^ 2 / (Ctw α + 1)`,
`α` in the cover. The radius depends on `G` only through `ε`.

`cthickening_image_le`: Lipschitz images of thickenings.
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

section UT3

variable {g : SmoothRiemannianMetric I M}

/-- Lipschitz images of thickenings: `f q ∈ cthickening (L ε) (f '' S)` if `q ∈ cthickening ε S`. -/
theorem cthickening_image_le {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : X → Y) {L : ℝ} (hL : 0 < L) (hf : ∀ x y, dist (f x) (f y) ≤ L * dist x y)
    {S : Set X} {ε : ℝ} (hε : 0 ≤ ε) {q : X} (hq : q ∈ Metric.cthickening ε S) :
    f q ∈ Metric.cthickening (L * ε) (f '' S) := by
  rw [Metric.cthickening_eq_iInter_thickening (mul_nonneg hL.le hε)]
  rw [Metric.cthickening_eq_iInter_thickening hε] at hq
  simp only [mem_iInter] at hq ⊢
  intro ε'' hε''
  have h1 : ε < ε'' / L := by
    rw [lt_div_iff₀ hL]; linarith [hε'']
  obtain ⟨y, hyS, hy⟩ := Metric.mem_thickening_iff.mp (hq (ε'' / L) h1)
  refine Metric.mem_thickening_iff.mpr ⟨f y, ⟨y, hyS, rfl⟩, ?_⟩
  calc dist (f q) (f y) ≤ L * dist q y := hf q y
    _ < L * (ε'' / L) := mul_lt_mul_of_pos_left hy hL
    _ = ε'' := by field_simp

namespace FibreMap

/-- **Patch data independent of the fibre map.** -/
structure PatchData (g : SmoothRiemannianMetric I M) (b' w A : ℕ) where
  r₀ : M → ℝ
  hr₀ : ∀ α, 0 < r₀ α
  Bf : ∀ α : M, Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯
  hball : ∀ α, Metric.closedBall (extChartAt I α α) (r₀ α) ⊆ (extChartAt I α).target
  hB : ∀ α, ∀ y ∈ Metric.closedBall (extChartAt I α α) (r₀ α), ∀ k,
    trivToE I α ((extChartAt I α).symm y) (Bf α k ((extChartAt I α).symm y)) =
      Module.finBasis ℝ E k
  Cfrm : M → ℝ
  hCfrm0 : ∀ α, 0 ≤ Cfrm α
  hfrb : ∀ α, ∀ i ≤ w, ∀ y ∈ Metric.closedBall (extChartAt I α α) (r₀ α / 2),
    ∀ v : TensorRSSpace 0 (b' + i) I ((extChartAt I α).symm y),
      riemannianFiberNormSq (I := I) (M := M) g 0 (b' + i) ((extChartAt I α).symm y) v ≤
        Cfrm α * ‖(trivAt I M 0 (b' + i) α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm y) v‖ ^ 2
  Ctw : M → ℝ
  hCtw0 : ∀ α, 0 ≤ Ctw α
  hTwA : ∀ α, ∀ a ≤ A, ∀ y ∈ Metric.closedBall (extChartAt I α α) (r₀ α / 2),
    ∀ S : SmoothCcTensor g 0 a, ‖chartRd g α S y‖ ^ 2 ≤
      Ctw α * riemannianFiberNormSq (I := I) (M := M) g 0 a ((extChartAt I α).symm y)
        (S.toSection ((extChartAt I α).symm y))

theorem PatchData.nonempty (b' w A : ℕ) : Nonempty (PatchData (I := I) (M := M) g b' w A) := by
  choose r₀ hr₀ Bf hball hB hrest using fun α : M => patch_frame_data (g := g) b' w α
  choose Cfrm hCfrm0 hfrb using hrest
  choose Ctw hCtw0 hTwA using fun α : M => patch_twist_data (g := g) α (hr₀ α) (hball α) A
  exact ⟨⟨r₀, hr₀, Bf, hball, hB, Cfrm, hCfrm0, hfrb, Ctw, hCtw0, hTwA⟩⟩

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] {ι : Type*} [Fintype ι]
  {b : ι → ℕ} {b' : ℕ}

/-- **`TameGood` from patch data, margins and a finite cover.** -/
theorem tame_good_of_data {w A : ℕ} (D : PatchData (I := I) (M := M) g b' w A)
    (G : FibreMap I M Λ b b') (lam : Λ) {T : ℝ} (hT : 0 < T) (hTT : T ≤ G.T₀)
    {W : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)}
    (hW : ∀ c, JointlySmoothOn g 0 (b c) (Icc 0 T) (W c))
    (hWdom : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, valAt (fun c => W c t) x ∈ G.dom lam t x)
    {p : ℕ} (hp : 0 < p) (hbA : ∀ c, b c + w ≤ A) (ε : M → ℝ) (hε : ∀ α, 0 < ε α)
    (hεD : ∀ α, ∀ q : (ℝ × E) × ProdModel E b,
      q ∈ Metric.cthickening (ε α) ((fun q : ℝ × E => (q, valFam α W q)) ''
        (Icc 0 T ×ˢ Metric.closedBall (extChartAt I α α) (D.r₀ α / 2))) →
      q.1.1 ∈ Icc (0 : ℝ) T → q.1.2 ∈ Metric.closedBall (extChartAt I α α) (D.r₀ α / 2) →
      prodOfModel b α ((extChartAt I α).symm q.1.2) q.2 ∈
        G.dom lam q.1.1 ((extChartAt I α).symm q.1.2))
    (Afin : Finset M)
    (hcov : ∀ x : M, ∃ α ∈ Afin, x ∈ (extChartAt I α).source ∩
      extChartAt I α ⁻¹' Metric.ball (extChartAt I α α) (D.r₀ α / 2))
    {δ₀ : ℝ} (hδ₀ : ∀ α ∈ Afin, δ₀ ≤ ε α ^ 2 / (D.Ctw α + 1)) :
    TameGood G lam T W p w δ₀ := by
  refine tame_cover_gen G lam (r := fun α => D.r₀ α / 2)
    (δ := fun α => ε α ^ 2 / (D.Ctw α + 1)) (fun α => ?_) Afin hcov hδ₀
  obtain ⟨δ', hδ', hδe, h1, h2⟩ := G.patch_tame_gen lam hT hTT hW hWdom hp w α (D.hr₀ α)
    (D.hball α) (D.hB α) (D.hCfrm0 α) (D.hfrb α) hbA (D.hCtw0 α) (D.hTwA α) (hε α) (hεD α)
  subst hδe
  exact ⟨h1, h2⟩

end FibreMap

end UT3

end ShortTime
