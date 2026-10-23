import ShortTime.Linear.Garding
import ShortTime.Nonlinear.Tube
import ShortTime.Nonlinear.Lowering

/-!
# Theorem B: uniqueness of parabolic solutions (`thm:B`)

For equations on a covariant bundle `T⁰_s M`, the proof follows the paper:

* two parabolic solutions that agree at a time `t₀ < T` agree on `[t₀, t₀ + η]`
  (`EquationData.local_unique`). Their difference solves a linear parabolic equation whose
  coefficients average `D_k F` along the segment between the two jets, and Gårding's inequality
  with Grönwall's inequality forces it to vanish;
* the set of times where they agree is closed and contains `0`, so it is all of `[0, T]`
  (`EquationData.solution_unique_cov`).

General tensor bundles reduce to this case by lowering indices (`solution_unique_of_covariant`).
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Sobolev
open scoped Manifold ContDiff Topology

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

namespace EquationData

variable {g : SmoothRiemannianMetric I M}

/-- The model value of a solution at a fixed point is continuous in time. -/
theorem IsSolution.continuousOn_toModel {r s p : ℕ} {D : EquationData I M r s p}
    {u₀ : SmoothCcTensor g r s} {T : ℝ} {u : ℝ → SmoothCcTensor g r s}
    (hu : D.IsSolution g u₀ T u) (x : M) :
    ContinuousOn (fun τ => TensorRSSpace.toModel ((u τ).toSection x)) (Icc 0 T) :=
  fun t ht => (hu.eqn t ht x).continuousWithinAt

/-- The times at which two solutions agree form a closed subset of `[0, T]`. -/
theorem IsSolution.isClosed_eq {r s p : ℕ} {D : EquationData I M r s p}
    {u₀ u₀' : SmoothCcTensor g r s} {T : ℝ} {u v : ℝ → SmoothCcTensor g r s}
    (hu : D.IsSolution g u₀ T u) (hv : D.IsSolution g u₀' T v) :
    IsClosed ({τ | u τ = v τ} ∩ Icc 0 T) := by
  set F : ℝ → M → TensorRSModel r s ℝ E := fun τ x => TensorRSSpace.toModel ((u τ).toSection x)
  set G : ℝ → M → TensorRSModel r s ℝ E := fun τ x => TensorRSSpace.toModel ((v τ).toSection x)
  have hF : ContinuousOn F (Icc 0 T) := continuousOn_pi.mpr fun x => hu.continuousOn_toModel x
  have hG : ContinuousOn G (Icc 0 T) := continuousOn_pi.mpr fun x => hv.continuousOn_toModel x
  have hcl := (hF.prodMk hG).preimage_isClosed_of_isClosed isClosed_Icc isClosed_diagonal
  have heq : {τ | u τ = v τ} ∩ Icc 0 T =
      Icc 0 T ∩ (fun τ => (F τ, G τ)) ⁻¹' {q | q.1 = q.2} := by
    ext τ
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage]
    constructor
    · rintro ⟨h, hτ⟩
      exact ⟨hτ, by simp [F, G, h]⟩
    · rintro ⟨hτ, h⟩
      refine ⟨?_, hτ⟩
      apply SmoothCcTensor.ext
      apply ContMDiffSection.ext
      intro x
      exact TensorRSSpace.toModel_injective (congrFun h x)
  rw [heq]
  exact hcl

variable {s p : ℕ} (D : EquationData I M 0 s p) (g)

variable [CompleteSpace E]

/-- **Local uniqueness** (`lem:local-unique`). Two parabolic solutions on `[0, T]` that agree at a
time `t₀ < T` agree on `[t₀, t₀ + η] ∩ [0, T]` for some `η > 0`. -/
theorem local_unique {u₀ u₀' : SmoothCcTensor g 0 s} {T : ℝ} {u v : ℝ → SmoothCcTensor g 0 s}
    (hu : D.IsParabolicSolution g u₀ T u) (hv : D.IsParabolicSolution g u₀' T v)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico 0 T) (h : u t₀ = v t₀) :
    ∃ η > 0, ∀ t ∈ Icc t₀ (t₀ + η), t ≤ T → u t = v t := by
  obtain ⟨η, hη, hηT, lam, hlam, hseg⟩ := D.exists_parabolic_segment g hu hv ht₀ h
  obtain ⟨L, hL, hLeq⟩ := D.exists_linearized hu.1 hv.1 ht₀.1 hη hηT hlam hseg
  have hmaps : ∀ τ ∈ Icc (0 : ℝ) η, t₀ + τ ∈ Icc (0 : ℝ) T :=
    fun τ hτ => ⟨by linarith [ht₀.1, hτ.1], by linarith [hτ.2]⟩
  -- the difference, shifted to start at `t₀`
  set w : ℝ → SmoothCcTensor g 0 s := fun τ => u (t₀ + τ) - v (t₀ + τ) with hw
  have hws : JointlySmoothOn g 0 s (Icc 0 η) w :=
    jointlySmoothOn_sub (jointlySmoothOn_shift hu.1.smooth t₀ hmaps)
      (jointlySmoothOn_shift hv.1.smooth t₀ hmaps)
  have hshift : ∀ τ : ℝ, HasDerivWithinAt (fun σ : ℝ => t₀ + σ) 1 (Icc 0 η) τ :=
    fun τ => (hasDerivWithinAt_id τ _).const_add t₀
  have hsol : L.Solves w (fun _ => 0) := by
    intro τ hτ x
    have hu' := (hu.1.eqn (t₀ + τ) (hmaps τ hτ) x).scomp τ (hshift τ) hmaps
    have hv' := (hv.1.eqn (t₀ + τ) (hmaps τ hτ) x).scomp τ (hshift τ) hmaps
    have hd := hu'.sub hv'
    simp only [one_smul] at hd
    have hfun : (fun σ => (w σ).toFun x) =
        ((fun σ => TensorRSSpace.toModel ((u σ).toSection x)) ∘ fun σ => t₀ + σ) -
          ((fun σ => TensorRSSpace.toModel ((v σ).toSection x)) ∘ fun σ => t₀ + σ) := by
      funext σ
      simp only [hw, SmoothCcTensor.toFun_sub, Pi.sub_apply, Function.comp_apply]
      rfl
    rw [hfun, add_zero]
    refine hd.congr_deriv ?_
    change _ = TensorRSSpace.toModel ((L.apply τ (w τ)).toSection x)
    rw [hLeq τ hτ x, TensorRSSpace.toModel_sub]
  have hsol0 : L.Solves (fun _ => (0 : SmoothCcTensor g 0 s)) (fun _ => 0) := by
    intro τ _ x
    have h00 : L.apply τ 0 = 0 := by
      have := L.apply_sub τ 0 0
      rwa [sub_self, sub_self] at this
    rw [h00, add_zero]
    simpa using (hasDerivWithinAt_const τ (Icc 0 η) (0 : TensorRSModel 0 s ℝ E))
  have hzero := L.unique_of_isParabolic hL hws (jointlySmoothOn_const g (Icc 0 η) 0)
    (by simp [hw, h]) hsol hsol0
  refine ⟨η, hη, fun t ht _ => ?_⟩
  have := hzero (t - t₀) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  simp only [hw, add_sub_cancel] at this
  exact sub_eq_zero.mp this

/-- **Theorem B on covariant bundles.** Two parabolic solutions on `[0, T]` with the same initial
datum coincide. -/
theorem solution_unique_cov {u₀ : SmoothCcTensor g 0 s} {T : ℝ} {u v : ℝ → SmoothCcTensor g 0 s}
    (hu : D.IsParabolicSolution g u₀ T u) (hv : D.IsParabolicSolution g u₀ T v) :
    ∀ t ∈ Icc (0 : ℝ) T, u t = v t := by
  have hsub : Icc (0 : ℝ) T ⊆ {τ | u τ = v τ} := by
    refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin (hu.1.isClosed_eq hv.1) ?_ ?_
    · show u 0 = v 0
      rw [hu.1.initial, hv.1.initial]
    · rintro x ⟨hx, hxI⟩
      obtain ⟨η, hη, hloc⟩ := D.local_unique g hu hv hxI hx
      have hT : 0 < T - x := by linarith [hxI.2]
      have hm := lt_min hη hT
      refine mem_of_superset (Ioo_mem_nhdsGT (show x < x + min η (T - x) by linarith)) ?_
      intro τ hτ
      exact hloc τ ⟨hτ.1.le, by linarith [hτ.2, min_le_left η (T - x)]⟩
        (by linarith [hτ.2, min_le_right η (T - x)])
  exact fun t ht => hsub ht

end EquationData

end ShortTime
