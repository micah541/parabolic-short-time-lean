import ShortTime.Nonlinear.NemytskiiParamFibre

/-!
# The would-be derivatives of the parametric nonlinear operator

Let `Φ` be a smooth fibre map on covariant `2p`-jets with a parameter `λ ∈ Λ`, `Λ` finite
dimensional, and `Ψ = Φ.paramLift` the fibre map with `λ` as scalar inputs. For
`q = (λ, v) ∈ Λ × smoothSub` (with jets in the domain, `PRepInDom`) and directions
`q_l = (μ_l, h_l)`,

  `g_k(q)(q₁, …, q_k) = D^k_{(λ,ζ)} F(λ, t, j^{2p} v)[(μ_l, j^{2p} h_l)]_l ∈ 𝒫^N`

(`ParamNemytskii.pgfun`) is the `k`-th fibre derivative of `Ψ` at the inputs `pin q`, in the
directions `pin q_l`. It is multilinear (`pgML`), and continuous whenever it is bounded (`pgCML`).
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter Topology MeasureTheory Metric
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Spectral
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

open ParabolicSpace EquationData

namespace ParamNemytskii

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [FiniteDimensional ℝ Λ]
variable {s p : ℕ} {T : ℝ} {N : ℕ}

/-! ### Inputs -/

/-- The inputs `(j^{2p} v, λ)` of `Ψ` for `q = (λ, v)`. -/
def pin (q : Λ × smoothSub g s p (N + 1) T) :
    ∀ c : Fin (2 * p + 1) ⊕ Fin (Module.finrank ℝ Λ), ℝ →
      SmoothCcTensor g 0 (parRanks (jetRanks s p) (Module.finrank ℝ Λ) c) :=
  FibreMap.parFam q.1 (repJet q.2)

theorem pin_smooth (q : Λ × smoothSub g s p (N + 1) T) :
    ∀ c, JointlySmoothOn g 0 (parRanks (jetRanks s p) (Module.finrank ℝ Λ) c) (Icc 0 T)
      (pin q c) :=
  FibreMap.jointlySmoothOn_parFam q.1 fun c => repJet_smooth q.2 c

theorem pin_add_apply (hT : 0 < T) (q η : Λ × smoothSub g s p (N + 1) T) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) (c : Fin (2 * p + 1) ⊕ Fin (Module.finrank ℝ Λ)) :
    pin (q + η) c t = pin q c t + pin η c t := by
  rcases c with c | i
  · change iteratedCovGrad g 0 s (c : ℕ) (ParabolicSpace.rep (q.2 + η.2) t) =
      iteratedCovGrad g 0 s (c : ℕ) (ParabolicSpace.rep q.2 t) +
        iteratedCovGrad g 0 s (c : ℕ) (ParabolicSpace.rep η.2 t)
    rw [show ParabolicSpace.rep (q.2 + η.2) t =
        ParabolicSpace.rep q.2 t + ParabolicSpace.rep η.2 t from
      rep_add hT (by omega) q.2 η.2 ht, iteratedCovGrad_add]
  · change FibreMap.parScal (g := g) Λ (q.1 + η.1) i =
      FibreMap.parScal (g := g) Λ q.1 i + FibreMap.parScal (g := g) Λ η.1 i
    simp only [FibreMap.parScal, map_add, Finsupp.add_apply, add_smul]

theorem pin_smul_apply (hT : 0 < T) (a : ℝ) (q : Λ × smoothSub g s p (N + 1) T) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) (c : Fin (2 * p + 1) ⊕ Fin (Module.finrank ℝ Λ)) :
    pin (a • q) c t = a • pin q c t := by
  rcases c with c | i
  · change iteratedCovGrad g 0 s (c : ℕ) (ParabolicSpace.rep (a • q.2) t) =
      a • iteratedCovGrad g 0 s (c : ℕ) (ParabolicSpace.rep q.2 t)
    rw [show ParabolicSpace.rep (a • q.2) t = a • ParabolicSpace.rep q.2 t from
      rep_smul hT (by omega) a q.2 ht, iteratedCovGrad_smul]
  · change FibreMap.parScal (g := g) Λ (a • q.1) i = a • FibreMap.parScal (g := g) Λ q.1 i
    simp only [FibreMap.parScal, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_smul]

theorem valAt_pin_add (hT : 0 < T) (q η : Λ × smoothSub g s p (N + 1) T) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) (x : M) :
    FibreMap.valAt (fun c => pin (q + η) c t) x =
      FibreMap.valAt (fun c => pin q c t) x + FibreMap.valAt (fun c => pin η c t) x := by
  funext c
  change (pin (q + η) c t).toSection x = (pin q c t).toSection x + (pin η c t).toSection x
  rw [pin_add_apply hT q η ht c, toSection_add_apply]

theorem valAt_pin_smul (hT : 0 < T) (a : ℝ) (q : Λ × smoothSub g s p (N + 1) T) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) (x : M) :
    FibreMap.valAt (fun c => pin (a • q) c t) x = a • FibreMap.valAt (fun c => pin q c t) x := by
  funext c
  change (pin (a • q) c t).toSection x = a • (pin q c t).toSection x
  rw [pin_smul_apply hT a q ht c, toSection_smul_apply]

variable (Φ : FibreMap I M Λ (jetRanks s p) s)

/-- The jets of the representative lie in the domain of `Φ(λ, ·)` on `[0,T]`. -/
def PRepInDom (q : Λ × smoothSub g s p (N + 1) T) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (ParabolicSpace.rep q.2 t) x ∈ Φ.dom q.1 t x

theorem pin_dom {q : Λ × smoothSub g s p (N + 1) T} (hq : PRepInDom Φ q) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      FibreMap.valAt (fun c => pin q c t) x ∈ Φ.paramLift.dom 0 t x :=
  fun t ht x => (FibreMap.mem_paramLift_dom_parFam Φ 0 q.1 (repJet q.2) t x).2 (hq t ht x)

theorem pRepInDom_of_dom {q : Λ × smoothSub g s p (N + 1) T}
    (h : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      FibreMap.valAt (fun c => pin q c t) x ∈ Φ.paramLift.dom 0 t x) : PRepInDom Φ q :=
  fun t ht x => (FibreMap.mem_paramLift_dom_parFam Φ 0 q.1 (repJet q.2) t x).1 (h t ht x)

/-! ### The would-be derivatives -/

/-- The family `D^k_{(λ,ζ)} F(λ, t, j v)[(μ_l, j h_l)]_l`. -/
def pgfam (k : ℕ) (q : Λ × smoothSub g s p (N + 1) T)
    (h : Fin k → Λ × smoothSub g s p (N + 1) T) : ℝ → SmoothCcTensor g 0 s :=
  Φ.paramLift.derivFam k 0 (pin q) fun l => pin (h l)

/-- `g_k(q)(q₁, …, q_k)` in `𝒫^N`. -/
def pgfun (k : ℕ) (q : Λ × smoothSub g s p (N + 1) T)
    (h : Fin k → Λ × smoothSub g s p (N + 1) T) : ParabolicSpace g s p N T :=
  ofSmooth' (pgfam Φ k q h)

theorem pgfam_spec (hTD : T ≤ Φ.T₀) (k : ℕ) {q : Λ × smoothSub g s p (N + 1) T}
    (hq : PRepInDom Φ q) (h : Fin k → Λ × smoothSub g s p (N + 1) T) :
    (∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, (pgfam Φ k q h t).toSection x =
      Φ.paramLift.derivF k 0 t x
        (joinPt (FibreMap.valAt (fun c => pin q c t) x)
          fun l => FibreMap.valAt (fun c => pin (h l) c t) x)) ∧
    JointlySmoothOn g 0 s (Icc 0 T) (pgfam Φ k q h) := by
  have hj := Φ.paramLift.jointlySmoothOn_derivFam k 0 hTD (u := pin q) (pin_smooth q)
    (pin_dom Φ hq) (h := fun l => pin (h l)) (fun l => pin_smooth (h l))
  refine ⟨fun t ht x => ?_, hj.2⟩
  rw [pgfam, hj.1 t ht x, valAt_joinFam]

theorem pgfun_eq (hTD : T ≤ Φ.T₀) (k : ℕ) {q : Λ × smoothSub g s p (N + 1) T}
    (hq : PRepInDom Φ q) (h : Fin k → Λ × smoothSub g s p (N + 1) T) :
    pgfun Φ k q h = ofSmooth (pgfam Φ k q h) (pgfam_spec Φ hTD k hq h).2 :=
  ofSmooth'_eq _

theorem norm_pgfun_sq (hTD : T ≤ Φ.T₀) (k : ℕ) {q : Λ × smoothSub g s p (N + 1) T}
    (hq : PRepInDom Φ q) (h : Fin k → Λ × smoothSub g s p (N + 1) T) :
    ‖pgfun Φ k q h‖ ^ 2 = parabolicInner g s p N T (pgfam Φ k q h) (pgfam Φ k q h) := by
  rw [pgfun_eq Φ hTD k hq, norm_ofSmooth_sq]

theorem pin_update (k : ℕ) [DecidableEq (Fin k)] (h : Fin k → Λ × smoothSub g s p (N + 1) T)
    (i : Fin k) (a : Λ × smoothSub g s p (N + 1) T) (t : ℝ) (x : M) :
    (fun l => FibreMap.valAt (fun c => pin (Function.update h i a l) c t) x) =
      Function.update (fun l => FibreMap.valAt (fun c => pin (h l) c t) x) i
        (FibreMap.valAt (fun c => pin a c t) x) :=
  funext fun l => Function.apply_update (fun _ a => FibreMap.valAt (fun c => pin a c t) x) h i a l

/-- `g_k(q)` as a multilinear map. -/
def pgML (hT : 0 < T) (hTD : T ≤ Φ.T₀) (k : ℕ) (q : Λ × smoothSub g s p (N + 1) T)
    (hq : PRepInDom Φ q) :
    MultilinearMap ℝ (fun _ : Fin k => Λ × smoothSub g s p (N + 1) T)
      (ParabolicSpace g s p N T) where
  toFun h := pgfun Φ k q h
  map_update_add' h i a a' := by
    rw [pgfun_eq Φ hTD k hq, pgfun_eq Φ hTD k hq, pgfun_eq Φ hTD k hq]
    refine ofSmooth_eq_add_of hT _ _ _ fun t ht x => ?_
    rw [(pgfam_spec Φ hTD k hq _).1 t ht x, (pgfam_spec Φ hTD k hq _).1 t ht x,
      (pgfam_spec Φ hTD k hq _).1 t ht x, pin_update, pin_update, pin_update,
      valAt_pin_add hT a a' ht, FibreMap.derivF_joinPt_update_add]
  map_update_smul' h i c a := by
    rw [pgfun_eq Φ hTD k hq, pgfun_eq Φ hTD k hq]
    refine ofSmooth_eq_smul_of hT c _ _ fun t ht x => ?_
    rw [(pgfam_spec Φ hTD k hq _).1 t ht x, (pgfam_spec Φ hTD k hq _).1 t ht x,
      pin_update, pin_update, valAt_pin_smul hT c a ht, FibreMap.derivF_joinPt_update_smul]

open Classical in
/-- `g_k(q)` as a continuous multilinear map when `q` has jets in the domain and `g_k(q)` is
bounded (and `0` otherwise). -/
def pgCML (hT : 0 < T) (hTD : T ≤ Φ.T₀) (k : ℕ) (q : Λ × smoothSub g s p (N + 1) T) :=
  if hq : PRepInDom Φ q then
    if hb : ∃ C, ∀ h : Fin k → Λ × smoothSub g s p (N + 1) T,
        ‖pgfun Φ k q h‖ ≤ C * ∏ l, ‖h l‖ then
      MultilinearMap.mkContinuous (𝕜 := ℝ) (E := fun _ : Fin k => Λ × smoothSub g s p (N + 1) T)
        (G := ParabolicSpace g s p N T)
        { toFun := fun h => pgfun Φ k q h
          map_update_add' := (pgML Φ hT hTD k q hq).map_update_add'
          map_update_smul' := (pgML Φ hT hTD k q hq).map_update_smul' } hb.choose hb.choose_spec
    else 0
  else 0

theorem pgCML_apply (hT : 0 < T) (hTD : T ≤ Φ.T₀) (k : ℕ) {q : Λ × smoothSub g s p (N + 1) T}
    (hq : PRepInDom Φ q) (hb : ∃ C, ∀ h, ‖pgfun Φ k q h‖ ≤ C * ∏ l, ‖h l‖)
    (h : Fin k → Λ × smoothSub g s p (N + 1) T) : pgCML Φ hT hTD k q h = pgfun Φ k q h := by
  rw [pgCML, dif_pos hq, dif_pos hb]
  rfl

end ParamNemytskii

end ShortTime
