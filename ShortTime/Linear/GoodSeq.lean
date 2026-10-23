import ShortTime.Linear.Embedding
import ShortTime.Linear.InsField

/-!
# Sequences of smooth families with all derivatives uniformly Cauchy

`Good T w` says that each `w m` is jointly smooth on `M × [0,T]` and that, for all `i, j`, the
sequence `∇^i ∂ₜ^j w m` is uniformly Cauchy on `M × [0,T]` in the fibre norm. Such sequences have
jointly smooth limits (`ShortTime.Linear.LimitSmooth`). Here: the class is closed under `∂ₜ`
(`Good.timeDeriv`) and under `w ↦ Φ(∇w)` for a fixed operator field `Φ` (`Good.opField_covGrad`),
in particular under covariant derivatives along a vector field.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral DifferentialGeometry.Analysis.Elliptic
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

variable {g : SmoothRiemannianMetric I M} {T : ℝ}

variable (T) in
/-- `wₘ` is uniformly Cauchy on `M × [0,T]` in the fibre norm. -/
def UCauchy {a : ℕ} (w : ℕ → ℝ → SmoothCcTensor g 0 a) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ m' ≥ N, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
    riemannianFiberNormSq (I := I) (M := M) g 0 a x ((w m t - w m' t).toSection x) ≤ ε

variable (T) in
/-- Jointly smooth families whose derivatives `∇^i ∂ₜ^j wₘ` are all uniformly Cauchy. -/
def Good {a : ℕ} (w : ℕ → ℝ → SmoothCcTensor g 0 a) : Prop :=
  (∀ m, JointlySmoothOn g 0 a (Icc 0 T) (w m)) ∧
    ∀ i j, UCauchy T (fun m t => iteratedCovGrad g 0 a i (timeDerivIter T (w m) j t))

namespace UCauchy

variable {a : ℕ}

theorem congr {w w' : ℕ → ℝ → SmoothCcTensor g 0 a} (hw : UCauchy T w)
    (h : ∀ m, ∀ t ∈ Icc (0 : ℝ) T, w' m t = w m t) : UCauchy T w' := fun ε hε => by
  obtain ⟨N, hN⟩ := hw ε hε
  exact ⟨N, fun m hm m' hm' t ht x => by rw [h m t ht, h m' t ht]; exact hN m hm m' hm' t ht x⟩

theorem add {w w' : ℕ → ℝ → SmoothCcTensor g 0 a} (hw : UCauchy T w) (hw' : UCauchy T w') :
    UCauchy T (fun m t => w m t + w' m t) := fun ε hε => by
  obtain ⟨N, hN⟩ := hw (ε / 4) (by positivity)
  obtain ⟨N', hN'⟩ := hw' (ε / 4) (by positivity)
  refine ⟨max N N', fun m hm m' hm' t ht x => ?_⟩
  have e : (w m t + w' m t - (w m' t + w' m' t)).toSection x =
      (w m t - w m' t).toSection x + (w' m t - w' m' t).toSection x := by
    simp only [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_sub,
      ContMDiffSection.coe_add, ContMDiffSection.coe_sub, Pi.add_apply, Pi.sub_apply]
    abel
  rw [e]
  refine (riemannianFiberNormSq_add_le (I := I) (M := M) g 0 a x _ _).trans ?_
  have h1 := hN m (le_of_max_le_left hm) m' (le_of_max_le_left hm') t ht x
  have h2 := hN' m (le_of_max_le_right hm) m' (le_of_max_le_right hm') t ht x
  linarith

theorem zero : UCauchy T (fun (_ : ℕ) (_ : ℝ) => (0 : SmoothCcTensor g 0 a)) := fun ε hε =>
  ⟨0, fun m _ m' _ t _ x => by
    simp only [sub_self, SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero, Pi.zero_apply]
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise]
    have h0 : TensorRSSpace.toModel (0 : TensorRSSpace 0 a I x) =
        (0 : ℝ) • TensorRSSpace.toModel (0 : TensorRSSpace 0 a I x) := by
      rw [← TensorRSSpace.toModel_smul, zero_smul]
    nth_rewrite 1 [h0]
    rw [tensorInnerPointwise_smul_left, zero_mul]
    exact hε.le⟩

theorem sum {ι : Type*} (F : Finset ι) {w : ι → ℕ → ℝ → SmoothCcTensor g 0 a}
    (hw : ∀ i ∈ F, UCauchy T (w i)) : UCauchy T (fun m t => ∑ i ∈ F, w i m t) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (zero : UCauchy T _)
  | insert i F hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hw i (Finset.mem_insert_self i F)).add (ih fun j hj => hw j (Finset.mem_insert_of_mem hj))

/-- A fixed operator field preserves uniform Cauchy sequences. -/
theorem opField {b : ℕ} (Φ : SmoothCcTensor g a b) {w : ℕ → ℝ → SmoothCcTensor g 0 a}
    (hw : UCauchy T w) :
    UCauchy T (fun m t => operatorFieldApply (I := I) (M := M) g a b Φ (w m t)) := fun ε hε => by
  obtain ⟨K, hK0, hK⟩ := exists_bound_of_jointlySmoothOn (T := T)
    (jointlySmoothOn_const g (Icc 0 T) Φ)
  obtain ⟨N, hN⟩ := hw (ε / (K + 1)) (by positivity)
  refine ⟨N, fun m hm m' hm' t ht x => ?_⟩
  rw [← operatorFieldApplication_sub_right, operatorFieldApplication_toSection]
  by_cases hT : (0 : ℝ) ≤ T
  · refine (riemannianFiberNormSq_comp_le_mul (I := I) (M := M) g a b x _ _).trans ?_
    have h1 := hK 0 ⟨le_rfl, hT⟩ x
    have h2 := hN m hm m' hm' t ht x
    have h3 := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 a x ((w m t - w m' t).toSection x)
    calc _ ≤ K * (ε / (K + 1)) := mul_le_mul h1 h2 h3 hK0
      _ ≤ ε := by
        rw [mul_div_assoc']
        rw [div_le_iff₀ (by positivity)]
        nlinarith
  · exact absurd (ht.1.trans ht.2) hT

end UCauchy

theorem timeDeriv_const_family (hT : 0 < T) {a b : ℕ} (Φ : SmoothCcTensor g a b) {t : ℝ}
    (ht : t ∈ Icc 0 T) : timeDeriv T (fun _ => Φ) t = 0 :=
  timeDeriv_eq hT (jointlySmoothOn_const g _ Φ) ht fun x => by
    simpa using hasDerivWithinAt_const t (Icc 0 T) (Φ.toFun x)

/-- `∂ₜ^j (Φ(∇w)) = Φ(∇ ∂ₜ^j w)` for a fixed operator field `Φ`. -/
theorem timeDerivIter_opField_covGrad (hT : 0 < T) {a b : ℕ} (Φ : SmoothCcTensor g (a + 1) b)
    {w : ℝ → SmoothCcTensor g 0 a} (hw : JointlySmoothOn g 0 a (Icc 0 T) w) :
    ∀ j, ∀ t ∈ Icc (0 : ℝ) T,
      timeDerivIter T (fun τ => operatorFieldApply (I := I) (M := M) g (a + 1) b Φ
        (covGrad (I := I) (M := M) g 0 a (w τ))) j t =
      operatorFieldApply (I := I) (M := M) g (a + 1) b Φ
        (covGrad (I := I) (M := M) g 0 a (timeDerivIter T w j t))
  | 0, _, _ => rfl
  | j + 1, t, ht => by
    have hwj := jointlySmoothOn_timeDerivIter hT hw j
    have hgr : JointlySmoothOn g 0 (a + 1) (Icc 0 T)
        (fun τ => covGrad (I := I) (M := M) g 0 a (timeDerivIter T w j τ)) :=
      jointlySmoothOn_iteratedCovGrad hwj 1
    have hL : JointlySmoothOn g 0 b (Icc 0 T) (timeDerivIter T (fun τ =>
        operatorFieldApply (I := I) (M := M) g (a + 1) b Φ (covGrad (I := I) (M := M) g 0 a (w τ))) j) :=
      jointlySmoothOn_timeDerivIter hT (jointlySmoothOn_operatorFieldApply
        (jointlySmoothOn_const g _ Φ) (jointlySmoothOn_iteratedCovGrad hw 1)) j
    change timeDeriv T (timeDerivIter T _ j) t = _
    rw [timeDeriv_congr hT hL (jointlySmoothOn_operatorFieldApply (jointlySmoothOn_const g _ Φ) hgr)
      (fun τ hτ => timeDerivIter_opField_covGrad hT Φ hw j τ hτ) ht,
      timeDeriv_operatorFieldApply hT (jointlySmoothOn_const g _ Φ) hgr ht,
      timeDeriv_const_family hT Φ ht, operatorFieldApplication_zero_left, zero_add,
      timeDeriv_covGrad hT hwj ht]
    rfl

namespace Good

variable {a : ℕ}

theorem timeDeriv (hT : 0 < T) {w : ℕ → ℝ → SmoothCcTensor g 0 a} (hw : Good T w) :
    Good T (fun m => ShortTime.timeDeriv T (w m)) :=
  ⟨fun m => jointlySmoothOn_timeDeriv hT (hw.1 m), fun i j =>
    (hw.2 i (j + 1)).congr fun m t _ => by rw [timeDerivIter_succ']⟩

/-- `w ↦ Φ(∇w)` preserves good sequences. -/
theorem opField_covGrad (hT : 0 < T) {b : ℕ} (Φ : SmoothCcTensor g (a + 1) b)
    {w : ℕ → ℝ → SmoothCcTensor g 0 a} (hw : Good T w) :
    Good T (fun m t => operatorFieldApply (I := I) (M := M) g (a + 1) b Φ
      (covGrad (I := I) (M := M) g 0 a (w m t))) := by
  refine ⟨fun m => jointlySmoothOn_operatorFieldApply (jointlySmoothOn_const g _ Φ)
    (jointlySmoothOn_iteratedCovGrad (hw.1 m) 1), fun i j => ?_⟩
  obtain ⟨F, -, hDF⟩ := (IsDiffOp.field_grad (g := g) (S := univ) (a := a) (b := b) 1
    (G := fun _ => Φ) (jointlySmoothOn_const g univ Φ)).iterGrad i
  refine (UCauchy.sum (Finset.range (1 + i + 1)) fun c _ =>
    UCauchy.opField (F c 0) (hw.2 c j)).congr fun m t ht => ?_
  dsimp only
  rw [timeDerivIter_opField_covGrad hT Φ (hw.1 m) j t ht]
  exact hDF 0 (timeDerivIter T (w m) j t)

end Good

end ShortTime
