import ShortTime.Nonlinear.IterPullExt
import ShortTime.Nonlinear.Evaluation
import ShortTime.Nonlinear.Tube
import ShortTime.Linear.LimitFamily
import ShortTime.Nonlinear.SmoothRepEuclid

/-!
# Spatial smoothness of the continuous representative (`prop:regularity`, step 2)

Let `v ∈ 𝒫^m` and let `B` be a frame with constant chart coordinates on a chart patch at `α`
(`exists_chart_patch`). Suppose `σ ↦ Π_σ v` (`HFlow.iterPullExt`) is `C^∞` from a ball around
`0 ∈ ℝⁿ` into `𝒫^m` (Angenent's trick). Then the continuous representative `v̂(t, x)`
(`evalJet 0 0 t x v`), read in the chart and trivialization at `α` (`repChart`), is spatially smooth
near the chart centre, with all spatial derivatives continuous in `(t, y)`
(`exists_spatialSmooth`, in the sense of `SpatialReg.SpC 0`).

Proof.
* `evalJet_iterPullExt`: `v̂_σ(t, α) = P_σ⁻¹ v̂(t, φ_σ α)`, where `Π_σ v` has representative
  `v̂_σ`, `φ_σ = iterFlow B σ` and `P_σ⁻¹ = transL` is the composite parallel transport. Both sides
  are continuous linear in `v` and agree on smooth families (`iterPull_toSection`).
* In the trivialization at `α` this reads `κ(v̂_σ(t, α)) = M_σ (v̂(t, φ_σ α))` with a linear
  isomorphism `M_σ` (`transM`). `M_σ` is smooth in `σ`: on the sections `w_c` with constant
  coordinates `c` near `α` (`exists_tensor_frame`), `M_σ c` is the reading of `(Π_σ w_c)(α)`, which
  is smooth in `σ` (`contMDiff_iterPull_const`).
* `φ_σ α = chart⁻¹(chart α + ∑ σ_k e_k)` (`iterFlow_chart_patch`), so with `σ(y)` the coordinates of
  `y - chart α`, `v̂(t, chart⁻¹ y) = M_{σ(y)}⁻¹ κ(ev_{t,α}(Π_{σ(y)} v))`. The map
  `y ↦ Π_{σ(y)} v` is `C^∞` into `𝒫^m` and `ev_{t,α}` is bounded uniformly in `t` and continuous in
  `t` (`SpatialReg.SpC_clm`).
-/

noncomputable section

open Bundle Manifold Set Filter Topology Metric
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff BigOperators

set_option linter.unusedSectionVars false

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

variable {g : SmoothRiemannianMetric I M} {s p m : ℕ} {T : ℝ}

open ParabolicSpace HFlow

namespace SmoothRep

/-! ### Readings of the continuous representative -/

variable (g s p m T) in
/-- The continuous representative of `v` at `(t, x)`, read in the trivialization at `α`. -/
def repTriv (α : M) (v : ParabolicSpace g s p m T) (t : ℝ) (x : M) : TensorRSModel 0 s ℝ E :=
  (trivAt I M 0 s α).continuousLinearMapAt ℝ x
    (TensorRSSpace.ofModel (evalJet g s p m T 0 0 t x v))

variable (g s p m T) in
/-- The continuous representative of `v`, read in the chart and trivialization at `α`. -/
def repChart (α : M) (v : ParabolicSpace g s p m T) (t : ℝ) (y : E) : TensorRSModel 0 s ℝ E :=
  repTriv g s p m T α v t ((extChartAt I α).symm y)

/-! ### The composite parallel transport -/

variable (g s) in
/-- The composite parallel transport `P_σ⁻¹ : T⁰_s|_{φ_σ x} → T⁰_s|_x` of `iterPull`. -/
def transL {n : ℕ} (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (σ : Fin n → ℝ)
    (x : M) : TensorRSSpace 0 s I (iterFlow B σ x) ≃L[ℝ] TensorRSSpace 0 s I x :=
  (iterPull_toSection g s B σ x).choose

theorem transL_spec {n : ℕ} (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (σ : Fin n → ℝ) (x : M) (u : SmoothCcTensor g 0 s) :
    (iterPull B g s σ u).toSection x = transL g s B σ x (u.toSection (iterFlow B σ x)) :=
  (iterPull_toSection g s B σ x).choose_spec u

variable (g s) in
/-- The transport, in the model fibres, as a linear map. -/
def transModelLin {n : ℕ} (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (σ : Fin n → ℝ) (x : M) : TensorRSModel 0 s ℝ E →ₗ[ℝ] TensorRSModel 0 s ℝ E :=
  (tensorRSSpaceContinuousLinearEquiv (I := I) 0 s x).toLinearEquiv.toLinearMap ∘ₗ
    (transL g s B σ x).toLinearEquiv.toLinearMap ∘ₗ
    (tensorRSSpaceContinuousLinearEquiv (I := I) 0 s (iterFlow B σ x)).symm.toLinearEquiv.toLinearMap

variable (g s) in
/-- The transport in the model fibres, as a continuous linear map. -/
def transModel {n : ℕ} (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (σ : Fin n → ℝ) (x : M) : TensorRSModel 0 s ℝ E →L[ℝ] TensorRSModel 0 s ℝ E :=
  LinearMap.toContinuousLinearMap (transModelLin g s B σ x)

theorem transModel_apply {n : ℕ} (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (σ : Fin n → ℝ) (x : M) (z : TensorRSModel 0 s ℝ E) :
    transModel g s B σ x z =
      TensorRSSpace.toModel (transL g s B σ x (TensorRSSpace.ofModel z)) := rfl

/-- **The representative of `Π_σ v`**: `v̂_σ(t, x) = P_σ⁻¹ v̂(t, φ_σ x)`. -/
theorem evalJet_iterPullExt (hT : 0 < T) (hm : 0 < m)
    (hk : Module.finrank ℝ E / 2 + 1 ≤ 2 * p * (m - 1)) {n : ℕ}
    (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (σ : Fin n → ℝ) (x : M) {t : ℝ}
    (ht : t ∈ Icc 0 T) (v : ParabolicSpace g s p m T) :
    evalJet g s p m T 0 0 t x (iterPullExt g s p m T B σ v) =
      transModel g s B σ x (evalJet g s p m T 0 0 t (iterFlow B σ x) v) := by
  have hk' : Module.finrank ℝ E / 2 + 1 + 0 ≤ 2 * p * (m - 0 - 1) := by simpa using hk
  refine UniformSpace.Completion.induction_on v
    (isClosed_eq ((evalJet g s p m T 0 0 t x).continuous.comp
      (iterPullExt g s p m T B σ).continuous)
      ((transModel g s B σ x).continuous.comp
        (evalJet g s p m T 0 0 t (iterFlow B σ x)).continuous)) fun u => ?_
  have hu : (u : ParabolicSpace g s p m T) = ofSmooth _ u.2 := rfl
  have e1 := evalJet_ofSmooth hT hm hk' ht x (jointlySmoothOn_iterPull g s B σ u.2)
  have e2 := evalJet_ofSmooth hT hm hk' ht (iterFlow B σ x) u.2
  rw [hu, iterPullExt_ofSmooth g s p m hT B σ u.2, e1]
  erw [e2]
  rw [transModel_apply, TensorRSSpace.ofModel_toModel]
  change TensorRSSpace.toModel ((iterPull B g s σ (u.family t)).toSection x) = _
  rw [transL_spec]
  rfl

/-! ### The transport in the trivialization at `α` -/

variable (g s) in
/-- `M_σ = τ_α ∘ P_σ⁻¹ ∘ τ_{φ_σ α}⁻¹`, the transport read in the trivialization at `α`. -/
def transM {n : ℕ} (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (α : M)
    (σ : Fin n → ℝ) : TensorRSModel 0 s ℝ E →L[ℝ] TensorRSModel 0 s ℝ E :=
  LinearMap.toContinuousLinearMap
    (((trivAt I M 0 s α).continuousLinearMapAt ℝ α).toLinearMap ∘ₗ
      (transL g s B σ α).toLinearEquiv.toLinearMap ∘ₗ
      ((trivAt I M 0 s α).symmL ℝ (iterFlow B σ α)).toLinearMap)

theorem transM_apply {n : ℕ} (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (α : M)
    (σ : Fin n → ℝ) (c : TensorRSModel 0 s ℝ E) :
    transM g s B α σ c = (trivAt I M 0 s α).continuousLinearMapAt ℝ α
      (transL g s B σ α ((trivAt I M 0 s α).symmL ℝ (iterFlow B σ α) c)) := rfl

theorem mem_baseSet_self (α : M) : α ∈ (trivAt I M 0 s α).baseSet :=
  mem_baseSet_trivializationAt _ _ α

/-- `M_σ` is an isomorphism when `φ_σ α` lies in the trivialization domain. -/
def transMEquiv {n : ℕ} (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (α : M)
    (σ : Fin n → ℝ) (hσ : iterFlow B σ α ∈ (trivAt I M 0 s α).baseSet) :
    TensorRSModel 0 s ℝ E ≃L[ℝ] TensorRSModel 0 s ℝ E :=
  LinearEquiv.toContinuousLinearEquiv
    (((trivAt I M 0 s α).continuousLinearEquivAt ℝ (iterFlow B σ α) hσ).symm.toLinearEquiv.trans
      ((transL g s B σ α).toLinearEquiv.trans
        ((trivAt I M 0 s α).continuousLinearEquivAt ℝ α (mem_baseSet_self α)).toLinearEquiv))

theorem coe_transMEquiv {n : ℕ} (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (α : M) (σ : Fin n → ℝ) (hσ : iterFlow B σ α ∈ (trivAt I M 0 s α).baseSet) :
    (transMEquiv (g := g) B α σ hσ : TensorRSModel 0 s ℝ E →L[ℝ] TensorRSModel 0 s ℝ E) =
      transM g s B α σ := by
  refine ContinuousLinearMap.ext fun c => ?_
  rw [transM_apply]
  change ((trivAt I M 0 s α).continuousLinearEquivAt ℝ α (mem_baseSet_self α))
    (transL g s B σ α (((trivAt I M 0 s α).continuousLinearEquivAt ℝ (iterFlow B σ α) hσ).symm c))
    = _
  rw [Trivialization.symm_continuousLinearEquivAt_eq _ hσ,
    Trivialization.coe_continuousLinearEquivAt_eq _ (mem_baseSet_self α)]

/-- `κ = τ_α ∘ ofModel`: the model fibre at `α` read in the trivialization at `α`. -/
def kappa (s : ℕ) (α : M) : TensorRSModel 0 s ℝ E →L[ℝ] TensorRSModel 0 s ℝ E :=
  LinearMap.toContinuousLinearMap
    (((trivAt I M 0 s α).continuousLinearMapAt ℝ α).toLinearMap ∘ₗ
      (tensorRSSpaceContinuousLinearEquiv (I := I) 0 s α).symm.toLinearEquiv.toLinearMap)

theorem kappa_apply (α : M) (z : TensorRSModel 0 s ℝ E) :
    kappa (I := I) s α z =
      (trivAt I M 0 s α).continuousLinearMapAt ℝ α (TensorRSSpace.ofModel (x := α) z) := rfl

/-- **The key identity**: `κ(v̂_σ(t, α)) = M_σ (v̂(t, φ_σ α))` in the trivialization at `α`. -/
theorem kappa_evalJet_iterPullExt (hT : 0 < T) (hm : 0 < m)
    (hk : Module.finrank ℝ E / 2 + 1 ≤ 2 * p * (m - 1)) {n : ℕ}
    (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (α : M) (σ : Fin n → ℝ)
    (hσ : iterFlow B σ α ∈ (trivAt I M 0 s α).baseSet) {t : ℝ} (ht : t ∈ Icc 0 T)
    (v : ParabolicSpace g s p m T) :
    kappa (I := I) s α (evalJet g s p m T 0 0 t α (iterPullExt g s p m T B σ v)) =
      transM g s B α σ (repTriv g s p m T α v t (iterFlow B σ α)) := by
  rw [evalJet_iterPullExt hT hm hk B σ α ht v, kappa_apply, transModel_apply,
    TensorRSSpace.ofModel_toModel, transM_apply, repTriv,
    Trivialization.symmL_continuousLinearMapAt _ hσ]

/-! ### Smoothness of `M_σ` -/

theorem contDiff_reading_iterPull {n : ℕ}
    (B : Fin n → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (α : M) (w : SmoothCcTensor g 0 s) :
    ContDiff ℝ ∞ (fun σ : Fin n → ℝ =>
      (trivAt I M 0 s α).continuousLinearMapAt ℝ α ((iterPull B g s σ w).toSection α)) := by
  have h := contMDiff_iterPull_const g s B w
  have hψ : ContMDiff 𝓘(ℝ, Fin n → ℝ) (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun σ : Fin n → ℝ => ((α, σ) : M × (Fin n → ℝ))) :=
    contMDiff_const.prodMk contMDiff_id
  have h2 := h.comp hψ
  rw [contDiff_iff_contDiffAt]
  intro σ₀
  have h3 := HFlow.contMDiffWithinAt_clmAt_apply (a := s) (J := 𝓘(ℝ, Fin n → ℝ)) α
    (fun _ : Fin n → ℝ => α) (fun σ => (iterPull B g s σ w).toSection α) (S := univ) (n₀ := σ₀)
    (h2 σ₀).contMDiffWithinAt (mem_baseSet_self α)
  rw [contMDiffWithinAt_iff_contDiffWithinAt, contDiffWithinAt_univ] at h3
  exact h3

/-! ### Spatial smoothness -/

/-- The chart coordinates `σ(y)` of `y - chart α` in the standard basis. -/
def sigmaOf (c₀ : E) (y : E) : Fin (Module.finrank ℝ E) → ℝ :=
  (Module.finBasis ℝ E).equivFunL (y - c₀)

theorem contDiff_sigmaOf (c₀ : E) : ContDiff ℝ ∞ (sigmaOf c₀) :=
  (Module.finBasis ℝ E).equivFunL.contDiff.comp (contDiff_id.sub contDiff_const)

theorem sigmaOf_self (c₀ : E) : sigmaOf c₀ c₀ = 0 := by
  simp [sigmaOf]

theorem add_sum_sigmaOf (c₀ y : E) :
    c₀ + ∑ k, sigmaOf c₀ y k • Module.finBasis ℝ E k = y := by
  have h := (Module.finBasis ℝ E).sum_equivFun (y - c₀)
  have e : ∀ k, sigmaOf c₀ y k = (Module.finBasis ℝ E).equivFun (y - c₀) k := fun k => rfl
  simp only [e, h]
  abel

theorem norm_kappa_comp_evalJet_le (hT : 0 < T) (hm : 0 < m)
    (hk : Module.finrank ℝ E / 2 + 1 ≤ 2 * p * (m - 1)) (α : M) :
    ∃ C, ∀ t ∈ Icc (0 : ℝ) T,
      ‖(kappa (I := I) s α).comp (evalJet g s p m T 0 0 t α)‖ ≤ C := by
  have hk' : Module.finrank ℝ E / 2 + 1 + 0 ≤ 2 * p * (m - 0 - 1) := by simpa using hk
  obtain ⟨C, hC0, hC⟩ := exists_norm_evalJet_le (g := g) (s := s) hT hm hk' α
  refine ⟨‖kappa (I := I) s α‖ * C, fun t ht => ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) hC0) fun w => ?_
  rw [ContinuousLinearMap.comp_apply]
  calc ‖kappa (I := I) s α (evalJet g s p m T 0 0 t α w)‖
      ≤ ‖kappa (I := I) s α‖ * ‖evalJet g s p m T 0 0 t α w‖ := (kappa (I := I) s α).le_opNorm _
    _ ≤ ‖kappa (I := I) s α‖ * (C * ‖w‖) := mul_le_mul_of_nonneg_left (hC t ht w) (norm_nonneg _)
    _ = ‖kappa (I := I) s α‖ * C * ‖w‖ := by ring

/-- **Spatial smoothness of the continuous representative** near the centre of a chart patch,
given that `σ ↦ Π_σ v` is `C^∞` into `𝒫^m` near `0`. -/
theorem exists_spatialSmooth (hT : 0 < T) (hm : 0 < m)
    (hk : Module.finrank ℝ E / 2 + 1 ≤ 2 * p * (m - 1)) (α : M)
    {r : ℝ} (hr : 0 < r)
    {B : Fin (Module.finrank ℝ E) → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (hball : Metric.closedBall (extChartAt I α α) r ⊆ (extChartAt I α).target)
    (hB : ∀ y ∈ Metric.closedBall (extChartAt I α α) r, ∀ k,
      trivToE I α ((extChartAt I α).symm y) (B k ((extChartAt I α).symm y)) =
        Module.finBasis ℝ E k)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ ε > 0, Metric.ball (extChartAt I α α) ε ⊆ (extChartAt I α).target ∧
      ∀ v : ParabolicSpace g s p m T,
        ContDiffOn ℝ ∞ (fun σ => iterPullExt g s p m T B σ v) (Metric.ball 0 ρ) →
        ∀ n, SpatialReg.SpC 0 (Icc 0 T) (Metric.ball (extChartAt I α α) ε) n
          (TensorRSModel 0 s ℝ E) (repChart g s p m T α v) := by
  set c₀ := extChartAt I α α with hc₀
  -- sections with constant coordinates near `α`
  obtain ⟨w, hw⟩ := exists_tensor_frame (g := g) s α (ι := TensorRSModel 0 s ℝ E) (fun c => c)
  obtain ⟨N, hNmem, hNP⟩ := hw.exists_mem
  -- the neighbourhood
  have hσc : Continuous (sigmaOf c₀) := (contDiff_sigmaOf c₀).continuous
  have hsumc : Continuous fun y => ∑ k, |sigmaOf c₀ y k| * ‖Module.finBasis ℝ E k‖ :=
    continuous_finset_sum _ fun k _ => ((continuous_apply k).comp hσc).abs.mul continuous_const
  have ev1 : ∀ᶠ y in 𝓝 c₀, ∑ k, |sigmaOf c₀ y k| * ‖Module.finBasis ℝ E k‖ < r := by
    refine hsumc.continuousAt.eventually_lt continuousAt_const ?_
    simp [sigmaOf_self, hr]
  have ev2 : ∀ᶠ y in 𝓝 c₀, sigmaOf c₀ y ∈ Metric.ball 0 ρ := by
    refine hσc.continuousAt.preimage_mem_nhds ?_
    rw [sigmaOf_self]
    exact Metric.ball_mem_nhds _ hρ
  have ev3 : ∀ᶠ y in 𝓝 c₀, (extChartAt I α).symm y ∈ N := by
    have hcs := continuousAt_extChartAt_symm (I := I) α
    rw [ContinuousAt, extChartAt_to_inv] at hcs
    exact hcs hNmem
  have ev4 : ∀ᶠ y in 𝓝 c₀, y ∈ Metric.ball c₀ r :=
    Metric.ball_mem_nhds _ hr
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff_ball.1 (((ev1.and ev2).and ev3).and ev4)
  set U := Metric.ball c₀ ε with hU
  have hUo : IsOpen U := Metric.isOpen_ball
  have hUt : ∀ y ∈ U, y ∈ (extChartAt I α).target := fun y hy =>
    hball (Metric.ball_subset_closedBall (hεP y hy).2)
  have hflowy : ∀ y ∈ U, iterFlow B (sigmaOf c₀ y) α = (extChartAt I α).symm y := by
    intro y hy
    rw [iterFlow_chart_patch α B hball hB (hεP y hy).1.1.1, add_sum_sigmaOf]
  have hbase : ∀ y ∈ U, iterFlow B (sigmaOf c₀ y) α ∈ (trivAt I M 0 s α).baseSet := by
    intro y hy
    rw [hflowy y hy]
    have h1 : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target (hUt y hy)
    rw [extChartAt_source] at h1
    change (extChartAt I α).symm y ∈ (trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) α).baseSet ∩
        (trivializationAt (Tensor0SBundle.Tensor0SModel s ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace s I y) α).baseSet
    refine ⟨?_, ?_⟩ <;>
      · change (extChartAt I α).symm y ∈ (trivializationAt E (TangentSpace I) α).baseSet
        rw [TangentBundle.trivializationAt_baseSet]
        exact h1
  -- `M_{σ(y)}` is smooth on `U`
  have hMc : ∀ c : TensorRSModel 0 s ℝ E, ContDiffOn ℝ ∞ (fun y => transM g s B α (sigmaOf c₀ y) c) U := by
    intro c
    refine ((contDiff_reading_iterPull B α (w c)).comp (contDiff_sigmaOf c₀)).contDiffOn.congr ?_
    intro y hy
    simp only [Function.comp_apply]
    have hmem : iterFlow B (sigmaOf c₀ y) α ∈ N := by rw [hflowy y hy]; exact (hεP y hy).1.2
    rw [transM_apply, transL_spec, hNP _ hmem c]
  have hM : ContDiffOn ℝ ∞ (fun y => transM g s B α (sigmaOf c₀ y)) U :=
    contDiffOn_clm_apply.2 hMc
  have hN : ContDiffOn ℝ ∞ (fun y => ContinuousLinearMap.inverse
      (transM g s B α (sigmaOf c₀ y))) U := by
    intro y hy
    have he := coe_transMEquiv (g := g) B α (sigmaOf c₀ y) (hbase y hy)
    have hinv := contDiffAt_map_inverse (𝕜 := ℝ) (n := ∞)
      (transMEquiv (g := g) B α (sigmaOf c₀ y) (hbase y hy))
    rw [he] at hinv
    exact hinv.comp_contDiffWithinAt y (hM y hy)
  -- the evaluation functionals
  obtain ⟨C, hC⟩ := norm_kappa_comp_evalJet_le (g := g) (s := s) hT hm hk α
  have hk' : Module.finrank ℝ E / 2 + 1 + 0 ≤ 2 * p * (m - 0 - 1) := by simpa using hk
  have hℓc : ∀ z : ParabolicSpace g s p m T, ContinuousOn
      (fun t => ((kappa (I := I) s α).comp (evalJet g s p m T 0 0 t α)) z) (Icc 0 T) :=
    fun z => (kappa (I := I) s α).continuous.comp_continuousOn
      (continuousOn_evalJet_time hT hm hk' α z)
  refine ⟨ε, hε, hUt, fun v hflow n => ?_⟩
  have hW : ContDiffOn ℝ ∞ (fun y => iterPullExt g s p m T B (sigmaOf c₀ y) v) U :=
    hflow.comp (contDiff_sigmaOf c₀).contDiffOn fun y hy => (hεP y hy).1.1.2
  have h1 := SpatialReg.SpC_clm (S := Icc 0 T) hUo (V := TensorRSModel 0 s ℝ E) hC hℓc hW n
  have h2 := SpatialReg.SpC.comp (uniqueDiffOn_Icc hT) hUo (O := U ×ˢ (univ : Set (TensorRSModel 0 s ℝ E)))
    (Ψ := fun q : ℝ × E × TensorRSModel 0 s ℝ E => ContinuousLinearMap.inverse
      (transM g s B α (sigmaOf c₀ q.2.1)) q.2.2)
    (hUo.prod isOpen_univ)
    ((hN.comp (contDiff_fst.comp contDiff_snd).contDiffOn fun q hq => hq.2.1).clm_apply
      (contDiff_snd.comp contDiff_snd).contDiffOn)
    (fun t _ y hy => ⟨hy, trivial⟩) h1
  refine SpatialReg.SpC.congr hUo n (fun t ht y hy => ?_) h2
  show ContinuousLinearMap.inverse (transM g s B α (sigmaOf c₀ y))
    (kappa (I := I) s α (evalJet g s p m T 0 0 t α (iterPullExt g s p m T B (sigmaOf c₀ y) v))) =
      repChart g s p m T α v t y
  rw [kappa_evalJet_iterPullExt hT hm hk B α (sigmaOf c₀ y) (hbase y hy) ht v,
    ← coe_transMEquiv (g := g) B α (sigmaOf c₀ y) (hbase y hy),
    ContinuousLinearMap.inverse_equiv]
  change (transMEquiv (g := g) B α (sigmaOf c₀ y) (hbase y hy)).symm
    ((transMEquiv (g := g) B α (sigmaOf c₀ y) (hbase y hy))
      (repTriv g s p m T α v t (iterFlow B (sigmaOf c₀ y) α))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply, repChart, hflowy y hy]

end SmoothRep

end ShortTime
