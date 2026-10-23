import ShortTime.Linear.Energy
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Iterated.Linear

/-!
# Uniqueness for linear parabolic equations (`thm:linear` (ii))

If `L` satisfies an energy bound `⟨u, L(t) u⟩ ≤ C ‖u‖²`, `u` is jointly smooth on `M × [0, T]`,
solves `∂ₜu = L u` and `u(0) = 0`, then `u = 0` (`eq_zero_of_solves_of_energy`). By linearity,
two smooth solutions of `∂ₜu = L u + f` with the same initial value coincide. The energy bound
follows from Gårding's inequality: here for second-order operators (`energy_bound_one`), in
`ShortTime.Linear.Garding` for every order.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set MeasureTheory Filter
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Spectral DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Elliptic
open scoped Manifold ContDiff BigOperators Topology

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

variable {g : SmoothRiemannianMetric I M}

/-! ### Algebra of jointly smooth families -/

theorem jointlySmoothOn_add {a b : ℕ} {S : Set ℝ} {A B : ℝ → SmoothCcTensor g a b}
    (hA : JointlySmoothOn g a b S A) (hB : JointlySmoothOn g a b S B) :
    JointlySmoothOn g a b S (fun t => A t + B t) := by
  have h := Vendor.joint_rs_add (I := I) (r := a) (s := b) (S := S)
    (fun p : M × ℝ => (A p.2).toSection p.1) (fun p : M × ℝ => (B p.2).toSection p.1) hA hB
  refine h.congr (fun p _ => ?_)
  rfl

theorem jointlySmoothOn_sub {a b : ℕ} {S : Set ℝ} {A B : ℝ → SmoothCcTensor g a b}
    (hA : JointlySmoothOn g a b S A) (hB : JointlySmoothOn g a b S B) :
    JointlySmoothOn g a b S (fun t => A t - B t) := by
  have h := Vendor.joint_rs_sub (I := I) (r := a) (s := b) (S := S)
    (fun p : M × ℝ => (A p.2).toSection p.1) (fun p : M × ℝ => (B p.2).toSection p.1) hA hB
  refine h.congr (fun p _ => ?_)
  rfl

theorem jointlySmoothOn_sum {ι : Type*} {a b : ℕ} {S : Set ℝ} (s : Finset ι)
    {F : ι → ℝ → SmoothCcTensor g a b} (hF : ∀ i ∈ s, JointlySmoothOn g a b S (F i)) :
    JointlySmoothOn g a b S (fun t => ∑ i ∈ s, F i t) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty] using jointlySmoothOn_const g S (0 : SmoothCcTensor g a b)
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact jointlySmoothOn_add (hF i (Finset.mem_insert_self i s))
      (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

variable [CompleteSpace E]

theorem jointlySmoothOn_operatorFieldApply {a b : ℕ} {S : Set ℝ}
    {Φ : ℝ → SmoothCcTensor g a b} {W : ℝ → SmoothCcTensor g 0 a}
    (hΦ : JointlySmoothOn g a b S Φ) (hW : JointlySmoothOn g 0 a S W) :
    JointlySmoothOn g 0 b S (fun t => operatorFieldApply (I := I) (M := M) g a b (Φ t) (W t)) := by
  have h := jointlySmoothOn_comp g hΦ hW
  simpa only [operatorFieldComposition_zero_eq_operatorFieldApply] using h

namespace LinearOp

variable {s p : ℕ} {T : ℝ} (L : LinearOp g s p T)

theorem jointlySmoothOn_apply {u : ℝ → SmoothCcTensor g 0 s}
    (hu : JointlySmoothOn g 0 s (Icc 0 T) u) :
    JointlySmoothOn g 0 s (Icc 0 T) (fun t => L.apply t (u t)) :=
  jointlySmoothOn_sum _ fun k _ => jointlySmoothOn_operatorFieldApply (L.smooth k)
    (Vendor.covGrad_iter_joint (I := I) (M := M) g 0 s k u (Icc 0 T) hu)

theorem apply_sub (t : ℝ) (u w : SmoothCcTensor g 0 s) :
    L.apply t (u - w) = L.apply t u - L.apply t w := by
  simp only [apply, iteratedCovGrad_sub, operatorFieldApplication_sub_right,
    Finset.sum_sub_distrib]

/-- **Uniqueness, homogeneous form.** If `L` satisfies the energy bound
`⟨u, L(t) u⟩ ≤ C ‖u‖²` (a consequence of Gårding's inequality), a smooth solution of `∂ₜu = L u`
with `u(0) = 0` vanishes on `[0, T]`. -/
theorem eq_zero_of_solves_of_energy {C : ℝ}
    (hC : ∀ t ∈ Icc (0 : ℝ) T, ∀ u : SmoothCcTensor g 0 s,
      tensorL2Inner (I := I) (M := M) g 0 s u.toFun (L.apply t u).toFun ≤
        C * tensorL2Inner (I := I) (M := M) g 0 s u.toFun u.toFun)
    {u : ℝ → SmoothCcTensor g 0 s} (hu : JointlySmoothOn g 0 s (Icc 0 T) u) (h0 : u 0 = 0)
    (hsol : L.Solves u (fun _ => 0)) :
    ∀ t ∈ Icc (0 : ℝ) T, u t = 0 := by
  set v : ℝ → SmoothCcTensor g 0 s := fun t => L.apply t (u t) + 0 with hv
  have hvs : JointlySmoothOn g 0 s (Icc 0 T) v := by
    simpa only [hv, add_zero] using L.jointlySmoothOn_apply hu
  set e : ℝ → ℝ := fun τ => tensorL2Inner (I := I) (M := M) g 0 s (u τ).toFun (u τ).toFun
  have hzero : ∀ t ∈ Icc (0 : ℝ) T, e t = 0 := by
    refine eq_zero_of_hasDerivAt_le (e' := fun t =>
        2 * tensorL2Inner (I := I) (M := M) g 0 s (u t).toFun (v t).toFun) (C := 2 * C)
      (continuousOn_normSq g hu hsol)
      (fun t _ => tensorL2Inner_nonneg (I := I) (M := M) g 0 s _) ?_
      (fun t ht => hasDerivAt_normSq g hu hvs hsol ht) ?_
    · simp only [e, h0, SmoothCcTensor.toFun_zero]
      exact tensorL2Inner_zero_left (I := I) (M := M) g 0 s _
    · intro t ht
      have h := hC t (Ioo_subset_Icc_self ht) (u t)
      simp only [v, add_zero, e]
      linarith
  intro t ht
  have he : tensorL2Inner (I := I) (M := M) g 0 s (u t).toFun (u t).toFun = 0 := hzero t ht
  apply SmoothCcTensor.smoothCcTensor_eq_of_toL2_eq
  rw [map_zero, ← norm_eq_zero, SmoothCcTensor.norm_toL2, SmoothCcTensor.norm_def,
    tensorL2Norm_def, he, Real.sqrt_zero]

/-- **Uniqueness from an energy bound.** Two smooth solutions of `∂ₜu = L u + f` with the same
initial value agree on `[0, T]`. -/
theorem unique_of_energy {C : ℝ}
    (hC : ∀ t ∈ Icc (0 : ℝ) T, ∀ u : SmoothCcTensor g 0 s,
      tensorL2Inner (I := I) (M := M) g 0 s u.toFun (L.apply t u).toFun ≤
        C * tensorL2Inner (I := I) (M := M) g 0 s u.toFun u.toFun)
    {u w f : ℝ → SmoothCcTensor g 0 s} (hu : JointlySmoothOn g 0 s (Icc 0 T) u)
    (hw : JointlySmoothOn g 0 s (Icc 0 T) w) (h0 : u 0 = w 0)
    (hsu : L.Solves u f) (hsw : L.Solves w f) :
    ∀ t ∈ Icc (0 : ℝ) T, u t = w t := by
  have hd : ∀ t ∈ Icc (0 : ℝ) T, u t - w t = 0 := by
    refine L.eq_zero_of_solves_of_energy hC (u := fun t => u t - w t) (jointlySmoothOn_sub hu hw)
      (by simp [h0]) ?_
    intro t ht x
    have h := (hsu t ht x).sub (hsw t ht x)
    have hfun : ((fun τ => (u τ).toFun x) - fun τ => (w τ).toFun x) =
        fun τ => (u τ - w τ).toFun x := by
      funext τ
      simp only [Pi.sub_apply, SmoothCcTensor.toFun_sub]
    rw [hfun] at h
    refine h.congr_deriv ?_
    rw [add_zero, apply_sub, SmoothCcTensor.toFun_sub, SmoothCcTensor.toFun_add,
      SmoothCcTensor.toFun_add]
    simp only [Pi.sub_apply, Pi.add_apply]
    abel
  intro t ht
  exact sub_eq_zero.mp (hd t ht)

/-- Second-order operators with a flip-coercive principal part satisfy the energy bound. -/
theorem energy_bound_one (L : LinearOp g s 1 T) {lam : ℝ} (hL : L.FlipCoercive lam) :
    ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) T, ∀ u : SmoothCcTensor g 0 s,
      tensorL2Inner (I := I) (M := M) g 0 s u.toFun (L.apply t u).toFun ≤
        C * tensorL2Inner (I := I) (M := M) g 0 s u.toFun u.toFun := by
  obtain ⟨C, hC⟩ := L.garding_one hL
  refine ⟨C, fun t ht u => ?_⟩
  have h := hC t ht u
  have hnn : 0 ≤ lam / 2 * tensorL2Inner (I := I) (M := M) g 0 (s + 1)
      (covGrad (I := I) (M := M) g 0 s u).toFun (covGrad (I := I) (M := M) g 0 s u).toFun :=
    mul_nonneg (by linarith [hL.1]) (tensorL2Inner_nonneg (I := I) (M := M) g 0 (s + 1) _)
  linarith

/-- **Uniqueness** for second-order operators with a flip-coercive principal part: two smooth
solutions of `∂ₜu = L u + f` with the same initial value agree on `[0, T]`. -/
theorem unique (L : LinearOp g s 1 T) {lam : ℝ} (hL : L.FlipCoercive lam)
    {u w f : ℝ → SmoothCcTensor g 0 s} (hu : JointlySmoothOn g 0 s (Icc 0 T) u)
    (hw : JointlySmoothOn g 0 s (Icc 0 T) w) (h0 : u 0 = w 0)
    (hsu : L.Solves u f) (hsw : L.Solves w f) :
    ∀ t ∈ Icc (0 : ℝ) T, u t = w t :=
  let ⟨_, hC⟩ := L.energy_bound_one hL
  L.unique_of_energy hC hu hw h0 hsu hsw

end LinearOp

end ShortTime
