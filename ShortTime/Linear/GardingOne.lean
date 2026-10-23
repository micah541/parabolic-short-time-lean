import ShortTime.Linear.Operator
import ShortTime.Linear.Bounds
import ShortTime.Linear.Family
import ShortTime.Vendor.ParametricJets

/-!
# Gårding's inequality for second-order operators (`lem:garding`, `p = 1`)

For `L ∈ 𝓛` of order two with flip-coercive principal part,

  `⟨u, L(t) u⟩ + (λ/2) ‖∇u‖² ≤ C ‖u‖²`   for all `t ∈ [0, T]`.

Proof: one integration by parts (`inner_apply_covGrad`) turns the principal term into
`-⟨∇u, Ǎ₂ ∇u⟩ - ⟨u, R ∇u⟩`; coercivity bounds the first by `-λ ‖∇u‖²`, and the remaining terms are
`O(‖u‖ ‖∇u‖ + ‖u‖²)` with constants uniform in `t` because all coefficient families are jointly
smooth on the compact set `M × [0, T]`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Spectral DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Elliptic
open scoped Manifold ContDiff BigOperators

namespace ShortTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

variable {g : SmoothRiemannianMetric I M}

/-- A jointly smooth family of operator fields is bounded on `M × [0, T]`. -/
theorem exists_bound_of_jointlySmoothOn {a b : ℕ} {T : ℝ} {Φ : ℝ → SmoothCcTensor g a b}
    (hΦ : JointlySmoothOn g a b (Icc 0 T) Φ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g a b x ((Φ t).toSection x) ≤ K := by
  obtain ⟨B, hB0, hB⟩ := Vendor.joint_jet_bdd (I := I) (M := M) g a b Φ isCompact_Icc subset_rfl hΦ
  exact ⟨B 0, hB0 0, fun t ht x => hB 0 t ht x⟩

/-- The remainder coefficients `R(t) = tr₁₂ ∘ ∇Ǎ(t)` of a jointly smooth family are jointly
smooth. -/
theorem jointlySmoothOn_flipRemainder {m n : ℕ} {S : Set ℝ} {A : ℝ → SmoothCcTensor g (m + 1) n}
    (hA : JointlySmoothOn g (m + 1) n S A) :
    JointlySmoothOn g m n S (fun t => flipRemainder g m n (A t)) := by
  have h1 : JointlySmoothOn g m (n + 1 + 1) S
      (fun t => covGrad (I := I) (M := M) g m (n + 1) (flipField g m n (A t))) :=
    Vendor.covGrad_step_jointContMDiffOn (I := I) (M := M) g m (n + 1)
      (fun t => flipField g m n (A t)) S (jointlySmoothOn_flipField g hA)
  exact jointlySmoothOn_comp g
    (jointlySmoothOn_const g S (cometricDoubleTraceField (I := I) g n)) h1

namespace LinearOp

variable {s : ℕ} {T : ℝ} (L : LinearOp g s 1 T)

/-- `L(t) u = A₀ u + A₁ ∇u + A₂ ∇²u` for a second-order operator. -/
theorem apply_one (t : ℝ) (u : SmoothCcTensor g 0 s) :
    L.apply t u = operatorFieldApply (I := I) (M := M) g s s (L.coeff 0 t) u +
      operatorFieldApply (I := I) (M := M) g (s + 1) s (L.coeff 1 t)
        (covGrad (I := I) (M := M) g 0 s u) +
      operatorFieldApply (I := I) (M := M) g (s + 1 + 1) s (L.coeff 2 t)
        (covGrad (I := I) (M := M) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s u)) := by
  simp only [LinearOp.apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  rw [add_assoc]
  rfl

/-- The three terms of `⟨u, L u⟩` for a second-order operator, after one integration by parts in
the principal term. -/
theorem inner_apply_eq (t : ℝ) (u : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 s u.toFun (L.apply t u).toFun =
      tensorL2Inner (I := I) (M := M) g 0 s u.toFun
          (operatorFieldApply (I := I) (M := M) g s s (L.coeff 0 t) u).toFun +
        tensorL2Inner (I := I) (M := M) g 0 s u.toFun
          (operatorFieldApply (I := I) (M := M) g (s + 1) s (L.coeff 1 t)
            (covGrad (I := I) (M := M) g 0 s u)).toFun +
        (- tensorL2Inner (I := I) (M := M) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s u).toFun
            (operatorFieldApply (I := I) (M := M) g (s + 1) (s + 1)
              (flipField g (s + 1) s (L.coeff 2 t)) (covGrad (I := I) (M := M) g 0 s u)).toFun
          - tensorL2Inner (I := I) (M := M) g 0 s u.toFun
            (operatorFieldApply (I := I) (M := M) g (s + 1) s
              (flipRemainder g (s + 1) s (L.coeff 2 t)) (covGrad (I := I) (M := M) g 0 s u)).toFun) := by
  have e : ∀ X : SmoothCcTensor g 0 s,
      tensorL2Inner (I := I) (M := M) g 0 s u.toFun X.toFun = inner ℝ u X := fun X => rfl
  rw [← inner_apply_covGrad g (s + 1) s (L.coeff 2 t) u (covGrad (I := I) (M := M) g 0 s u),
    apply_one, e, inner_add_right, inner_add_right]
  rfl

/-- **Gårding's inequality** for second-order operators. -/
theorem garding_one {lam : ℝ} (hL : L.FlipCoercive lam) :
    ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) T, ∀ u : SmoothCcTensor g 0 s,
      tensorL2Inner (I := I) (M := M) g 0 s u.toFun (L.apply t u).toFun +
          lam / 2 * tensorL2Inner (I := I) (M := M) g 0 (s + 1)
            (covGrad (I := I) (M := M) g 0 s u).toFun (covGrad (I := I) (M := M) g 0 s u).toFun ≤
        C * tensorL2Inner (I := I) (M := M) g 0 s u.toFun u.toFun := by
  obtain ⟨hlam, hcoer⟩ := hL
  obtain ⟨K₀, hK₀, hb₀⟩ := exists_bound_of_jointlySmoothOn (L.smooth 0)
  obtain ⟨K₁, hK₁, hb₁⟩ := exists_bound_of_jointlySmoothOn (L.smooth 1)
  obtain ⟨K₂, hK₂, hb₂⟩ := exists_bound_of_jointlySmoothOn
    (jointlySmoothOn_flipRemainder (L.smooth 2))
  set c := Real.sqrt K₁ + Real.sqrt K₂ with hc
  refine ⟨Real.sqrt K₀ + c ^ 2 / (2 * lam), fun t ht u => ?_⟩
  set Du := covGrad (I := I) (M := M) g 0 s u
  set a := tensorL2Norm (I := I) (M := M) g 0 s u.toFun
  set b := tensorL2Norm (I := I) (M := M) g 0 (s + 1) Du.toFun
  have ha0 : 0 ≤ a := tensorL2Norm_nonneg (I := I) (M := M) g 0 s _
  have hb0 : 0 ≤ b := tensorL2Norm_nonneg (I := I) (M := M) g 0 (s + 1) _
  have ha2 : tensorL2Inner (I := I) (M := M) g 0 s u.toFun u.toFun = a ^ 2 :=
    (Real.sq_sqrt (tensorL2Inner_nonneg (I := I) (M := M) g 0 s _)).symm
  have hb2 : tensorL2Inner (I := I) (M := M) g 0 (s + 1) Du.toFun Du.toFun = b ^ 2 :=
    (Real.sq_sqrt (tensorL2Inner_nonneg (I := I) (M := M) g 0 (s + 1) _)).symm
  -- the three lower-order pieces
  have h0 := abs_inner_operatorFieldApply_le g s s (L.coeff 0 t) hK₀ (hb₀ t ht) u u
  have h1 := abs_inner_operatorFieldApply_le g (s + 1) s (L.coeff 1 t) hK₁ (hb₁ t ht) u Du
  have h2 := abs_inner_operatorFieldApply_le g (s + 1) s (flipRemainder g (s + 1) s (L.coeff 2 t))
    hK₂ (hb₂ t ht) u Du
  -- coercivity of the flipped principal part
  have hco : lam * b ^ 2 ≤ tensorL2Inner (I := I) (M := M) g 0 (s + 1) Du.toFun
      (operatorFieldApply (I := I) (M := M) g (s + 1) (s + 1)
        (flipField g (s + 1) s (L.coeff 2 t)) Du).toFun := by
    rw [← hb2]
    unfold tensorL2Inner
    rw [← integral_const_mul]
    refine integral_mono ((SmoothCcTensor.integrable_inner_cross Du Du).const_mul lam)
      (SmoothCcTensor.integrable_inner_cross Du _) fun x => ?_
    exact hcoer t ht x (Du.toSection x)
  rw [inner_apply_eq, ha2, hb2]
  have hab : c * a * b ≤ lam / 2 * b ^ 2 + c ^ 2 / (2 * lam) * a ^ 2 := by
    have hsq : (lam * b - c * a) ^ 2 / (2 * lam) =
        lam / 2 * b ^ 2 - c * a * b + c ^ 2 / (2 * lam) * a ^ 2 := by
      field_simp
      ring
    have hnn : 0 ≤ (lam * b - c * a) ^ 2 / (2 * lam) := by positivity
    linarith
  have hc0 : 0 ≤ c := by positivity
  have e0 := (abs_le.mp h0).2
  have e1 := (abs_le.mp h1).2
  have e2 := (abs_le.mp h2).1
  nlinarith [e0, e1, e2, hco, hab, mul_nonneg ha0 hb0, Real.sqrt_nonneg K₀,
    Real.sqrt_nonneg K₁, Real.sqrt_nonneg K₂]

end LinearOp

end ShortTime
