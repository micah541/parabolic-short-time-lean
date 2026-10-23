import ShortTime.Linear.ModelOp
import ShortTime.Analysis.IccCalculus
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Jet.Bounds.IteratedCovariantDerivative
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.Pairing.FaithfulH1Embedding
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Spectral.Plancherel
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.SmoothRepresentative.Basic

/-!
# Eigenfunction expansions of tensor fields (`fact:eigen`, `fact:elliptic`)

The library's smooth eigenfunctions `φ_i` (`eigenvectorSmooth`) of the rough Laplacian form a
Hilbert basis of `L²(T⁰_s)`, with `Δ_raw φ_i = -λ_i φ_i`.

* `coeff v i = ⟨φ_i, v⟩` is the `i`-th coefficient (`tensorL2Coeff_toL2`); `coeff (φ_j) i = δ_ij`.
* `rawLapIter_eigen`: `Δ_raw^k φ_i = (-λ_i)^k φ_i`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open scoped Manifold ContDiff BigOperators RealInnerProductSpace

set_option linter.unusedSectionVars false

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

variable {g : SmoothRiemannianMetric I M} {s : ℕ}

/-- The index set of the eigenbasis. -/
abbrev EIdx (g : SmoothRiemannianMetric I M) (s : ℕ) : Type :=
  Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 s

/-- The smooth eigenfunctions. -/
abbrev eig (g : SmoothRiemannianMetric I M) (s : ℕ) (i : EIdx g s) :
    SmoothCcTensor g 0 s :=
  eigenvectorSmooth (I := I) (M := M) g 0 s i

/-- The `i`-th eigen-coefficient `⟨φ_i, v⟩_{L²}`. -/
def coeff (v : SmoothCcTensor g 0 s) (i : EIdx g s) : ℝ :=
  inner ℝ (eig g s i) v

theorem tensorL2Coeff_toL2 (v : SmoothCcTensor g 0 s) (i : EIdx g s) :
    tensorL2Coeff (I := I) (M := M) (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 s)
      (SmoothCcTensor.toL2 v) i = coeff v i := by
  rw [tensorL2Coeff_eq_inner, tensorResolventHilbertEigenbasisSigma_apply,
    ← eigenvectorSmooth_toL2, SmoothCcTensor.toL2_apply, UniformSpace.Completion.inner_coe]
  rfl

theorem coeff_add (v w : SmoothCcTensor g 0 s) (i) : coeff (v + w) i = coeff v i + coeff w i :=
  inner_add_right _ _ _

theorem coeff_smul (c : ℝ) (v : SmoothCcTensor g 0 s) (i) : coeff (c • v) i = c * coeff v i :=
  real_inner_smul_right _ _ _

theorem coeff_sub (v w : SmoothCcTensor g 0 s) (i) : coeff (v - w) i = coeff v i - coeff w i :=
  inner_sub_right _ _ _

theorem coeff_sum {ι : Type*} (F : Finset ι) (v : ι → SmoothCcTensor g 0 s) (i) :
    coeff (∑ j ∈ F, v j) i = ∑ j ∈ F, coeff (v j) i :=
  inner_sum _ _ _

open scoped Classical in
/-- Orthonormality: `⟨φ_i, φ_j⟩ = δ_ij`. -/
theorem coeff_eig (i j : EIdx g s) :
    coeff (eig g s j) i = if i = j then 1 else 0 := by
  classical
  rw [← tensorL2Coeff_toL2, tensorL2Coeff, SmoothCcTensor.toL2_apply, eigenvectorSmooth_toL2,
    ← tensorResolventHilbertEigenbasisSigma_apply, HilbertBasis.repr_self, lp.single_apply,
    Pi.single_apply]

/-- A smooth tensor field is determined by its eigen-coefficients. -/
theorem eq_of_coeff_eq {v w : SmoothCcTensor g 0 s} (h : ∀ i, coeff v i = coeff w i) : v = w := by
  refine SmoothCcTensor.smoothCcTensor_eq_of_toL2_eq v w ?_
  set b := tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 s)
  apply b.repr.injective
  ext i
  have hv := tensorL2Coeff_toL2 v i
  have hw := tensorL2Coeff_toL2 w i
  rw [tensorL2Coeff] at hv hw
  rw [hv, hw, h i]

/-- `coeff (Δ_raw^k v) i = (-λ_i)^k coeff v i`. -/
theorem coeff_rawLapIter (v : SmoothCcTensor g 0 s) (i : EIdx g s) :
    ∀ k : ℕ, coeff (rawTensorConnLapIter (I := I) g 0 s k v) i = (-i.lambda) ^ k * coeff v i
  | 0 => by rw [rawTensorConnLapIter_zero, pow_zero, one_mul]
  | k + 1 => by
    rw [rawTensorConnLapIter_succ, ← tensorL2Coeff_toL2, rawLap_coeff, tensorL2Coeff_toL2,
      coeff_rawLapIter v i k, pow_succ]
    ring

/-- **Eigenfunctions**: `Δ_raw^k φ_i = (-λ_i)^k φ_i`. -/
theorem rawLapIter_eig (i : EIdx g s) (k : ℕ) :
    rawTensorConnLapIter (I := I) g 0 s k (eig g s i) = (-i.lambda) ^ k • eig g s i := by
  classical
  refine eq_of_coeff_eq fun j => ?_
  rw [coeff_rawLapIter, coeff_smul, coeff_eig]
  split_ifs with h
  · rw [h]
  · simp

/-! ### Families with smooth scalar coefficients -/

/-- `t ↦ a(t) W` is jointly smooth when `a` is smooth on `S`. -/
theorem jointlySmoothOn_scalar_smul {S : Set ℝ} {a : ℝ → ℝ} (ha : ContDiffOn ℝ ∞ a S)
    (W : SmoothCcTensor g 0 s) : JointlySmoothOn g 0 s S (fun t => a t • W) := by
  have hW := jointlySmoothOn_const g S W
  let := tensorRSBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 0 s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (TensorRSModel 0 s ℝ E)
    (fun z : M => TensorRSSpace 0 s I z) x₀ with he
  have hW' := (Bundle.contMDiffWithinAt_totalSpace (F := TensorRSModel 0 s ℝ E)
    (E := fun z : M => TensorRSSpace 0 s I z)).mp (hW p₀ hp₀)
  have ha' : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun q : M × ℝ => a q.2)
      ((Set.univ : Set M) ×ˢ S) p₀ :=
    (ha p₀.2 hp₀.2).contMDiffWithinAt.comp p₀ contMDiffWithinAt_snd (fun q hq => hq.2)
  refine (ha'.smul hW'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
        p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_smul (a p.2) (W.toSection p.1)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_smul
      (a p₀.2) (W.toSection p₀.1)

theorem toFun_finset_sum {ι : Type*} (F : Finset ι) (v : ι → SmoothCcTensor g 0 s) (x : M) :
    (∑ i ∈ F, v i).toFun x = ∑ i ∈ F, (v i).toFun x := by
  classical
  induction F using Finset.induction_on with
  | empty => rfl
  | insert i F hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, SmoothCcTensor.toFun_add,
      Pi.add_apply, ih]

/-! ### Time dependence of the coefficients -/

variable {T : ℝ}

theorem continuousOn_coeff (hT : 0 < T) {f : ℝ → SmoothCcTensor g 0 s}
    (hf : JointlySmoothOn g 0 s (Icc 0 T) f) (i : EIdx g s) :
    ContinuousOn (fun τ => coeff (f τ) i) (Icc 0 T) :=
  (continuousOn_l2Pairing hT hf (jointlySmoothOn_const g _ (eig g s i))).congr fun τ _ => by
    rw [coeff, real_inner_comm, SmoothCcTensor.inner_def]
    rfl

theorem hasDerivWithinAt_coeff (hT : 0 < T) {f : ℝ → SmoothCcTensor g 0 s}
    (hf : JointlySmoothOn g 0 s (Icc 0 T) f) (i : EIdx g s) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun τ => coeff (f τ) i) (coeff (timeDeriv T f t) i) (Icc 0 T) t := by
  have hd := jointlySmoothOn_timeDeriv hT hf
  refine hasDerivWithinAt_Icc_of_interior hT (continuousOn_coeff hT hf i)
    (continuousOn_coeff hT hd i) (fun τ hτ => ?_) ht
  have h := hasDerivAt_inner_const hf hd (fun t ht x => hasDerivWithinAt_timeDeriv hT hf ht x)
    (eig g s i) hτ
  have e1 : (fun τ => coeff (f τ) i) = fun τ => inner ℝ (f τ) (eig g s i) :=
    funext fun τ => real_inner_comm _ _
  rw [e1, coeff, real_inner_comm]
  exact h

theorem contDiffOn_coeff_nat (hT : 0 < T) (i : EIdx g s) : ∀ (n : ℕ) {f : ℝ → SmoothCcTensor g 0 s},
    JointlySmoothOn g 0 s (Icc 0 T) f → ContDiffOn ℝ n (fun τ => coeff (f τ) i) (Icc 0 T)
  | 0, f, hf => by
    rw [Nat.cast_zero, contDiffOn_zero]
    exact continuousOn_coeff hT hf i
  | n + 1, f, hf => contDiffOn_Icc_of_hasDerivWithinAt hT
      (contDiffOn_coeff_nat hT i n (jointlySmoothOn_timeDeriv hT hf))
      (fun _ ht => hasDerivWithinAt_coeff hT hf i ht)

theorem contDiffOn_coeff (hT : 0 < T) {f : ℝ → SmoothCcTensor g 0 s}
    (hf : JointlySmoothOn g 0 s (Icc 0 T) f) (i : EIdx g s) :
    ContDiffOn ℝ ∞ (fun τ => coeff (f τ) i) (Icc 0 T) :=
  contDiffOn_infty.mpr fun n => contDiffOn_coeff_nat hT i n hf

/-! ### Spectral truncation -/

/-- `Π_F v = Σ_{i ∈ F} ⟨φ_i, v⟩ φ_i`. -/
def proj (F : Finset (EIdx g s)) (v : SmoothCcTensor g 0 s) : SmoothCcTensor g 0 s :=
  ∑ i ∈ F, coeff v i • eig g s i

open scoped Classical in
theorem coeff_proj (F : Finset (EIdx g s)) (v : SmoothCcTensor g 0 s) (j : EIdx g s) :
    coeff (proj F v) j = if j ∈ F then coeff v j else 0 := by
  rw [proj, coeff_sum]
  simp only [coeff_smul, coeff_eig, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]

theorem jointlySmoothOn_proj (hT : 0 < T) (F : Finset (EIdx g s)) {f : ℝ → SmoothCcTensor g 0 s}
    (hf : JointlySmoothOn g 0 s (Icc 0 T) f) :
    JointlySmoothOn g 0 s (Icc 0 T) (fun t => proj F (f t)) :=
  jointlySmoothOn_sum F fun i _ => jointlySmoothOn_scalar_smul (contDiffOn_coeff hT hf i) _

theorem timeDeriv_proj (hT : 0 < T) (F : Finset (EIdx g s)) {f : ℝ → SmoothCcTensor g 0 s}
    (hf : JointlySmoothOn g 0 s (Icc 0 T) f) {t : ℝ} (ht : t ∈ Icc 0 T) :
    timeDeriv T (fun τ => proj F (f τ)) t = proj F (timeDeriv T f t) := by
  refine timeDeriv_eq hT (jointlySmoothOn_proj hT F hf) ht fun x => ?_
  simp only [proj, toFun_finset_sum, SmoothCcTensor.toFun_smul, Pi.smul_apply]
  exact HasDerivWithinAt.fun_sum fun i _ =>
    (hasDerivWithinAt_coeff hT hf i ht).smul_const ((eig g s i).toFun x)

theorem timeDerivIter_proj (hT : 0 < T) (F : Finset (EIdx g s)) {f : ℝ → SmoothCcTensor g 0 s}
    (hf : JointlySmoothOn g 0 s (Icc 0 T) f) :
    ∀ j, EqOn (timeDerivIter T (fun τ => proj F (f τ)) j)
      (fun τ => proj F (timeDerivIter T f j τ)) (Icc 0 T)
  | 0 => fun _ _ => rfl
  | j + 1 => fun t ht => by
    change timeDeriv T (timeDerivIter T (fun τ => proj F (f τ)) j) t =
      proj F (timeDeriv T (timeDerivIter T f j) t)
    rw [timeDeriv_congr hT (jointlySmoothOn_timeDerivIter hT (jointlySmoothOn_proj hT F hf) j)
      (jointlySmoothOn_proj hT F (jointlySmoothOn_timeDerivIter hT hf j))
      (timeDerivIter_proj hT F hf j) ht, timeDeriv_proj hT F (jointlySmoothOn_timeDerivIter hT hf j) ht]

/-! ### Sobolev norms and spectral weights (`fact:elliptic`) -/

/-- The spectral weight `(1 + λ_i)^n`. -/
abbrev wt (n : ℕ) (i : EIdx g s) : ℝ := tensorSobolevWeight (I := I) (M := M) i (n : ℝ)

theorem wt_nonneg (n : ℕ) (i : EIdx g s) : 0 ≤ wt n i := tensorSobolevWeight_nonneg _ _

theorem summable_wt_coeff (n : ℕ) (v : SmoothCcTensor g 0 s) :
    Summable fun i : EIdx g s => wt n i * coeff v i ^ 2 := by
  have h := (ccTensorToHs (I := I) (M := M) g s (n : ℝ) v).weighted_summable
  simp only [ccTensorToHs_coeff, tensorL2Coeff_toL2] at h
  exact h

theorem norm_ccTensorToHs_sq (n : ℕ) (v : SmoothCcTensor g 0 s) :
    ‖ccTensorToHs (I := I) (M := M) g s (n : ℝ) v‖ ^ 2 = ∑' i : EIdx g s, wt n i * coeff v i ^ 2 := by
  rw [ccToHs_norm_sq]
  simp only [tensorL2Coeff_toL2]

theorem jetNorm_eq_norm (i : ℕ) (v : SmoothCcTensor g 0 s) :
    jetNorm g s i v = ‖iteratedCovGrad g 0 s i v‖ := (SmoothCcTensor.norm_def _).symm

theorem sum_sq_le_sq_sum {n : ℕ} (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) :
    ∑ j ∈ Finset.range n, a j ^ 2 ≤ (∑ j ∈ Finset.range n, a j) ^ 2 := by
  rw [sq, Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  rw [sq]
  exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun k _ => ha k) hj) (ha j)

/-- `‖v‖²_{H^n} ≤ C Σ_i (1 + λ_i)^n ⟨φ_i, v⟩²`. -/
theorem exists_sobolevNormSq_le_spectral (n : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ v : SmoothCcTensor g 0 s,
      sobolevNormSq g 0 s n v ≤ C * ∑' i : EIdx g s, wt n i * coeff v i ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := hsJet_le (I := I) (M := M) g s n
  refine ⟨C ^ 2, sq_nonneg _, fun v => ?_⟩
  rw [sobolevNormSq_eq_sum, ← norm_ccTensorToHs_sq, ← mul_pow]
  simp only [jetNorm_eq_norm]
  refine (sum_sq_le_sq_sum _ fun j => norm_nonneg _).trans ?_
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun j _ => norm_nonneg _) (hC v) 2

/-- `Σ_i (1 + λ_i)^n ⟨φ_i, v⟩² ≤ C ‖v‖²_{H^n}`. -/
theorem exists_spectral_le_sobolevNormSq (n : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ v : SmoothCcTensor g 0 s,
      ∑' i : EIdx g s, wt n i * coeff v i ^ 2 ≤ C * sobolevNormSq g 0 s n v := by
  obtain ⟨C, hC0, hC⟩ := hs_le_jet (I := I) (M := M) g s n
  refine ⟨C ^ 2 * (n + 1), by positivity, fun v => ?_⟩
  rw [← norm_ccTensorToHs_sq, sobolevNormSq_eq_sum]
  simp only [jetNorm_eq_norm]
  calc ‖ccTensorToHs (I := I) (M := M) g s (n : ℝ) v‖ ^ 2
      ≤ (C * ∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad g 0 s j v‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hC v) 2
    _ = C ^ 2 * (∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad g 0 s j v‖) ^ 2 := by ring
    _ ≤ C ^ 2 * ((n + 1) * ∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad g 0 s j v‖ ^ 2) := by
        gcongr
        have h := sq_sum_le_card_mul_sum_sq (s := Finset.range (n + 1))
          (f := fun j => ‖iteratedCovGrad g 0 s j v‖)
        simpa using h
    _ = _ := by ring

/-! ### Convergence of the truncations -/

/-- The tail `Σ_{i ∉ F} a_i` of a summable family tends to `0`. -/
theorem tendsto_tsum_ite_zero {ι : Type*} [DecidableEq ι] {a : ι → ℝ} (ha : Summable a) :
    Tendsto (fun F : Finset ι => ∑' i, if i ∈ F then 0 else a i) atTop (𝓝 0) := by
  have key : ∀ F : Finset ι, (∑' i, if i ∈ F then 0 else a i) = ∑' i, a i - ∑ i ∈ F, a i := by
    intro F
    have h1 : (∑' i, if i ∈ F then a i else 0) = ∑ i ∈ F, a i := by
      rw [tsum_eq_sum (s := F) (fun i hi => if_neg hi)]
      exact Finset.sum_congr rfl fun i hi => if_pos hi
    have hs1 : Summable fun i => if i ∈ F then a i else 0 :=
      summable_of_ne_finset_zero (s := F) fun i hi => if_neg hi
    have hs2 : Summable fun i => if i ∈ F then 0 else a i := by
      have := ha.sub hs1
      refine this.congr fun i => ?_
      split_ifs <;> ring
    have hsplit : ∑' i, a i =
        ∑' i, ((if i ∈ F then 0 else a i) + (if i ∈ F then a i else 0)) :=
      tsum_congr fun i => by split_ifs <;> ring
    rw [← h1, hsplit, hs2.tsum_add hs1]
    ring
  simp only [key]
  have h2 : Tendsto (fun F : Finset ι => ∑ i ∈ F, a i) atTop (𝓝 (∑' i, a i)) := ha.hasSum
  simpa using h2.const_sub (∑' i, a i)

open scoped Classical in
theorem sobolevNormSq_proj_sub_le {C : ℝ} {n : ℕ} (hC : ∀ v : SmoothCcTensor g 0 s,
      sobolevNormSq g 0 s n v ≤ C * ∑' i : EIdx g s, wt n i * coeff v i ^ 2)
    (F : Finset (EIdx g s)) (v : SmoothCcTensor g 0 s) :
    sobolevNormSq g 0 s n (proj F v - v) ≤
      C * ∑' i : EIdx g s, if i ∈ F then 0 else wt n i * coeff v i ^ 2 := by
  refine (hC _).trans (le_of_eq ?_)
  congr 1
  refine tsum_congr fun i => ?_
  rw [coeff_sub, coeff_proj]
  split_ifs <;> ring

theorem summable_ite_wt {n : ℕ} (F : Finset (EIdx g s)) (v : SmoothCcTensor g 0 s) [DecidablePred (· ∈ F)] :
    Summable fun i : EIdx g s => if i ∈ F then 0 else wt n i * coeff v i ^ 2 :=
  (summable_wt_coeff n v).of_nonneg_of_le
    (fun i => by split_ifs; exacts [le_rfl, mul_nonneg (wt_nonneg n i) (sq_nonneg _)])
    (fun i => by split_ifs; exacts [mul_nonneg (wt_nonneg n i) (sq_nonneg _), le_rfl])

open scoped Classical in
/-- **Spectral truncations converge in `L²(0,T; H^n)`.** -/
theorem tendsto_integral_proj_sub (hT : 0 < T) (n : ℕ) {h : ℝ → SmoothCcTensor g 0 s}
    (hh : JointlySmoothOn g 0 s (Icc 0 T) h) :
    Tendsto (fun F : Finset (EIdx g s) =>
      ∫ t in (0 : ℝ)..T, sobolevNormSq g 0 s n (proj F (h t) - h t)) atTop (𝓝 0) := by
  have : Countable (EIdx g s) := Analysis.Parabolic.MaximalRegularity.countable_tensorEigenIdx
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 s)
  obtain ⟨C, hC0, hC⟩ := exists_sobolevNormSq_le_spectral (g := g) (s := s) n
  obtain ⟨C', hC'0, hC'⟩ := exists_spectral_le_sobolevNormSq (g := g) (s := s) n
  have hsub : Set.uIoc 0 T ⊆ Icc 0 T := by
    rw [Set.uIoc_of_le hT.le]
    exact Ioc_subset_Icc_self
  suffices key : Tendsto (fun F : Finset (EIdx g s) =>
      ∫ t in (0 : ℝ)..T, sobolevNormSq g 0 s n (proj F (h t) - h t)) atTop
      (𝓝 (∫ t in (0 : ℝ)..T, (fun _ => (0 : ℝ)) t)) by
    simpa using key
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (E := ℝ) (l := (atTop : Filter (Finset (EIdx g s)))) (fun t => C * (C' * sobolevNormSq g 0 s n (h t))) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun F => ?_
    exact ((continuousOn_sobolevNormSq hT (jointlySmoothOn_sub (jointlySmoothOn_proj hT F hh) hh) n).mono
      hsub).aestronglyMeasurable measurableSet_uIoc
  · refine Eventually.of_forall fun F => Eventually.of_forall fun t _ => ?_
    rw [Real.norm_of_nonneg (sobolevNormSq_nonneg s _ _)]
    refine (sobolevNormSq_proj_sub_le hC F (h t)).trans ?_
    refine mul_le_mul_of_nonneg_left ((Summable.tsum_le_tsum (fun i => ?_) (summable_ite_wt F (h t))
      (summable_wt_coeff n (h t))).trans (hC' (h t))) hC0
    split_ifs
    · exact mul_nonneg (wt_nonneg n i) (sq_nonneg _)
    · exact le_rfl
  · exact ((continuousOn_const.mul (continuousOn_const.mul
      (continuousOn_sobolevNormSq hT hh n))).intervalIntegrable_of_Icc hT.le)
  · refine Eventually.of_forall fun t _ => ?_
    have hlim := (tendsto_tsum_ite_zero (summable_wt_coeff n (h t))).const_mul C
    rw [mul_zero] at hlim
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun F => sobolevNormSq_nonneg s _ _) (fun F => sobolevNormSq_proj_sub_le hC F (h t))

end ShortTime
