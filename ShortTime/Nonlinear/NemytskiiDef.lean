import ShortTime.Nonlinear.NemytskiiRep
import ShortTime.Nonlinear.ModelCoords

/-!
# The would-be derivatives of the nonlinear operator on smooth families

For equation data `D` on `T⁰_s M` and `v` in the subspace `smoothSub` of smooth families in
`𝒫^{N+1}`, with jets in the domain (`RepInDom`),

  `g_k(v)(h₁, …, h_k) = D^k_ζ F(t, j^{2p} v)[j^{2p} h₁, …, j^{2p} h_k] ∈ 𝒫^N`

(`EquationData.gfun`), computed on chosen representatives. It is multilinear in the `h_l`
(`EquationData.gML`), and continuous whenever it is bounded (`EquationData.gCML`).

* `derivF_zero_eq`: `g_0(v) = F[v]`.
* `derivF_one_jet`: `D_ζ F(t, ζ)[η] = Σ_k D_k F(t, ζ) η_k`, so `g_1(w)(h) = L_w h`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter Topology MeasureTheory
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

open ParabolicSpace

/-! ### Fibre level -/

namespace FibreMap

variable {ι : Type*} [Fintype ι] {b : ι → ℕ} {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ]
  {b' : ℕ}

theorem derivF_joinPt_update_add (Φ : FibreMap I M Λ b b') (k : ℕ) (lam : Λ) (t : ℝ) (x : M)
    (ζ : ProdFiber I b x) [DecidableEq (Fin k)] (η : Fin k → ProdFiber I b x) (i : Fin k)
    (a a' : ProdFiber I b x) :
    Φ.derivF k lam t x (joinPt ζ (Function.update η i (a + a'))) =
      Φ.derivF k lam t x (joinPt ζ (Function.update η i a)) +
        Φ.derivF k lam t x (joinPt ζ (Function.update η i a')) := by
  simp only [derivF, fbase_joinPt, fblk_joinPt]
  have e : ∀ v, (fun l => prodL I b x (Function.update η i v l)) =
      Function.update (fun l => prodL I b x (η l)) i (prodL I b x v) :=
    fun v => funext fun l => Function.apply_update (fun _ => prodL I b x) η i v l
  rw [e, e, e, map_add, ContinuousMultilinearMap.map_update_add, map_add]

theorem derivF_joinPt_update_smul (Φ : FibreMap I M Λ b b') (k : ℕ) (lam : Λ) (t : ℝ) (x : M)
    (ζ : ProdFiber I b x) [DecidableEq (Fin k)] (η : Fin k → ProdFiber I b x) (i : Fin k)
    (c : ℝ) (a : ProdFiber I b x) :
    Φ.derivF k lam t x (joinPt ζ (Function.update η i (c • a))) =
      c • Φ.derivF k lam t x (joinPt ζ (Function.update η i a)) := by
  simp only [derivF, fbase_joinPt, fblk_joinPt]
  have e : ∀ v, (fun l => prodL I b x (Function.update η i v l)) =
      Function.update (fun l => prodL I b x (η l)) i (prodL I b x v) :=
    fun v => funext fun l => Function.apply_update (fun _ => prodL I b x) η i v l
  rw [e, e, map_smul, ContinuousMultilinearMap.map_update_smul, map_smul]

/-- `G_0 = F`. -/
theorem derivF_zero_eq (Φ : FibreMap I M Λ b b') (lam : Λ) (t : ℝ) (x : M)
    (V : ProdFiber I (blkRanks b b 0) x) : Φ.derivF 0 lam t x V = Φ.F lam t x (fbase V) := by
  simp only [derivF, iteratedFDeriv_zero_apply, modelRep, LinearEquiv.symm_apply_apply]

/-- `Φ.apply` at `t` only depends on the values at `t`. -/
theorem apply_congr_time (Φ : FibreMap I M Λ b b') (lam : Λ)
    {V V' : ∀ c : ι, ℝ → SmoothCcTensor g 0 (b c)} {t : ℝ} (h : ∀ c, V c t = V' c t) :
    Φ.apply lam V t = Φ.apply lam V' t := by
  have e1 : Φ.apply lam V t = Φ.apply lam (fun c _ => V c t) t := rfl
  have e2 : Φ.apply lam V' t = Φ.apply lam (fun c _ => V' c t) t := rfl
  have e3 : (fun c (_ : ℝ) => V c t) = fun c _ => V' c t := funext fun c => funext fun _ => h c
  rw [e1, e2, e3]

end FibreMap

/-! ### Jets -/

theorem covJet_add' {s N : ℕ} (u v : SmoothCcTensor g 0 s) (x : M) :
    covJet g 0 s N (u + v) x = covJet g 0 s N u x + covJet g 0 s N v x := by
  funext k
  simp only [covJet, Pi.add_apply, iteratedCovGrad_add]
  exact toSection_add_apply _ _ x

theorem covJet_smul' {s N : ℕ} (c : ℝ) (u : SmoothCcTensor g 0 s) (x : M) :
    covJet g 0 s N (c • u) x = c • covJet g 0 s N u x := by
  funext k
  simp only [covJet, Pi.smul_apply, iteratedCovGrad_smul]
  exact toSection_smul_apply _ _ x

namespace EquationData

variable {s p : ℕ} (D : EquationData I M 0 s p) {T : ℝ} {N : ℕ}

/-- `D_ζ F(t, ζ)[η] = Σ_k D_k F(t, ζ) η_k`. -/
theorem derivF_one_jet (t : ℝ) (x : M) (ζ η : CovJetFiber I 0 s (2 * p) x) :
    D.toFibreMap.derivF 1 0 t x (joinPt ζ fun _ => η) =
      ∑ k : Fin (2 * p + 1), D.partialDeriv k t x ζ (η k) := by
  apply (fibIso I 0 s x).injective
  rw [map_sum]
  simp only [fibIso_partialDeriv]
  have e1 : fibIso I 0 s x (D.toFibreMap.derivF 1 0 t x (joinPt ζ fun _ => η)) =
      iteratedFDeriv ℝ 1 (D.Fmod t x) (jetIso I 0 s (2 * p) x ζ)
        (fun _ => jetIso I 0 s (2 * p) x η) := by
    simp only [FibreMap.derivF, fbase_joinPt, fblk_joinPt]
    exact (fibL I s x).apply_symm_apply _
  rw [e1, iteratedFDeriv_one_apply, ← map_sum]
  congr 1
  rw [← Finset.univ_sum_single (jetIso I 0 s (2 * p) x η)]
  rfl

/-- The jets of the representative of `v`. -/
def repJet (v : smoothSub g s p (N + 1) T) :
    ∀ c : Fin (2 * p + 1), ℝ → SmoothCcTensor g 0 (jetRanks s p c) :=
  jetFamily (p := p) (rep v)

theorem repJet_smooth (v : smoothSub g s p (N + 1) T) (c : Fin (2 * p + 1)) :
    JointlySmoothOn g 0 (jetRanks s p c) (Icc 0 T) (repJet v c) :=
  jointlySmoothOn_iteratedCovGrad (rep_smooth v) c

/-- The jets of the representative lie in the domain on `[0,T]`. -/
def RepInDom (v : smoothSub g s p (N + 1) T) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, covJet g 0 s (2 * p) (rep v t) x ∈ D.dom t x

/-- The family `D^k_ζ F(t, j v)[j h₁, …, j h_k]`. -/
def gfam (k : ℕ) (v : smoothSub g s p (N + 1) T) (h : Fin k → smoothSub g s p (N + 1) T) :
    ℝ → SmoothCcTensor g 0 s :=
  D.toFibreMap.derivFam k 0 (repJet v) fun l => repJet (h l)

/-- `g_k(v)(h) = D^k_ζ F(t, j v)[j h₁, …, j h_k]` in `𝒫^N`. -/
def gfun (k : ℕ) (v : smoothSub g s p (N + 1) T) (h : Fin k → smoothSub g s p (N + 1) T) :
    ParabolicSpace g s p N T :=
  ofSmooth' (D.gfam k v h)

theorem gfam_spec (hTD : T ≤ D.T₀) (k : ℕ) {v : smoothSub g s p (N + 1) T} (hv : D.RepInDom v)
    (h : Fin k → smoothSub g s p (N + 1) T) :
    (∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, (D.gfam k v h t).toSection x =
      D.toFibreMap.derivF k 0 t x
        (joinPt (covJet g 0 s (2 * p) (rep v t) x) fun l => covJet g 0 s (2 * p) (rep (h l) t) x)) ∧
    JointlySmoothOn g 0 s (Icc 0 T) (D.gfam k v h) := by
  have hj := D.toFibreMap.jointlySmoothOn_derivFam k 0 hTD (u := repJet v)
    (fun c => repJet_smooth v c) (fun t ht x => hv t ht x) (h := fun l => repJet (h l))
    (fun l c => repJet_smooth (h l) c)
  refine ⟨fun t ht x => ?_, hj.2⟩
  rw [gfam, hj.1 t ht x, valAt_joinFam]
  rfl

theorem gfun_eq (hTD : T ≤ D.T₀) (k : ℕ) {v : smoothSub g s p (N + 1) T} (hv : D.RepInDom v)
    (h : Fin k → smoothSub g s p (N + 1) T) :
    D.gfun k v h = ofSmooth (D.gfam k v h) (D.gfam_spec hTD k hv h).2 :=
  ofSmooth'_eq _

/-! ### Multilinearity -/

theorem ofSmooth_eq_add_of (hT : 0 < T) {A B C : ℝ → SmoothCcTensor g 0 s}
    (hA : JointlySmoothOn g 0 s (Icc 0 T) A) (hB : JointlySmoothOn g 0 s (Icc 0 T) B)
    (hC : JointlySmoothOn g 0 s (Icc 0 T) C)
    (h : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, (A t).toSection x = (B t).toSection x + (C t).toSection x) :
    ofSmooth (p := p) (m := N) A hA = ofSmooth B hB + ofSmooth C hC := by
  rw [← ofSmooth_add hB hC]
  exact ofSmooth_congr hT hA _ fun t ht =>
    smoothCcTensor_eq_of_toSection fun x => by rw [h t ht x, toSection_add_apply]

theorem ofSmooth_eq_smul_of (hT : 0 < T) {A B : ℝ → SmoothCcTensor g 0 s} (c : ℝ)
    (hA : JointlySmoothOn g 0 s (Icc 0 T) A) (hB : JointlySmoothOn g 0 s (Icc 0 T) B)
    (h : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, (A t).toSection x = c • (B t).toSection x) :
    ofSmooth (p := p) (m := N) A hA = c • ofSmooth B hB := by
  rw [← ofSmooth_smul c hB]
  exact ofSmooth_congr hT hA _ fun t ht =>
    smoothCcTensor_eq_of_toSection fun x => by rw [h t ht x, toSection_smul_apply]

theorem covJet_rep_update (k : ℕ) [DecidableEq (Fin k)] (h : Fin k → smoothSub g s p (N + 1) T)
    (i : Fin k) (a : smoothSub g s p (N + 1) T) (t : ℝ) (x : M) :
    (fun l => covJet g 0 s (2 * p) (rep (Function.update h i a l) t) x) =
      Function.update (fun l => covJet g 0 s (2 * p) (rep (h l) t) x) i
        (covJet g 0 s (2 * p) (rep a t) x) :=
  funext fun l => Function.apply_update (fun _ a => covJet g 0 s (2 * p) (rep a t) x) h i a l

/-- `g_k(v)` as a multilinear map. -/
def gML (hT : 0 < T) (hTD : T ≤ D.T₀) (k : ℕ) (v : smoothSub g s p (N + 1) T)
    (hv : D.RepInDom v) :
    MultilinearMap ℝ (fun _ : Fin k => smoothSub g s p (N + 1) T) (ParabolicSpace g s p N T) where
  toFun h := D.gfun k v h
  map_update_add' h i a a' := by
    rw [D.gfun_eq hTD k hv, D.gfun_eq hTD k hv, D.gfun_eq hTD k hv]
    refine ofSmooth_eq_add_of hT _ _ _ fun t ht x => ?_
    rw [(D.gfam_spec hTD k hv _).1 t ht x, (D.gfam_spec hTD k hv _).1 t ht x,
      (D.gfam_spec hTD k hv _).1 t ht x, covJet_rep_update, covJet_rep_update, covJet_rep_update,
      rep_add hT (by omega) a a' ht, covJet_add', FibreMap.derivF_joinPt_update_add]
  map_update_smul' h i c a := by
    rw [D.gfun_eq hTD k hv, D.gfun_eq hTD k hv]
    refine ofSmooth_eq_smul_of hT c _ _ fun t ht x => ?_
    rw [(D.gfam_spec hTD k hv _).1 t ht x, (D.gfam_spec hTD k hv _).1 t ht x,
      covJet_rep_update, covJet_rep_update, rep_smul hT (by omega) c a ht, covJet_smul',
      FibreMap.derivF_joinPt_update_smul]

open Classical in
/-- `g_k(v)` as a continuous multilinear map when `v` has jets in the domain and `g_k(v)` is
bounded (and `0` otherwise). -/
def gCML (hT : 0 < T) (hTD : T ≤ D.T₀) (k : ℕ) (v : smoothSub g s p (N + 1) T) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => smoothSub g s p (N + 1) T)
      (ParabolicSpace g s p N T) :=
  if hv : D.RepInDom v then
    if hb : ∃ C, ∀ h, ‖D.gfun k v h‖ ≤ C * ∏ l, ‖h l‖ then
      (D.gML hT hTD k v hv).mkContinuous hb.choose hb.choose_spec
    else 0
  else 0

theorem gCML_apply (hT : 0 < T) (hTD : T ≤ D.T₀) (k : ℕ) {v : smoothSub g s p (N + 1) T}
    (hv : D.RepInDom v) (hb : ∃ C, ∀ h, ‖D.gfun k v h‖ ≤ C * ∏ l, ‖h l‖)
    (h : Fin k → smoothSub g s p (N + 1) T) : D.gCML hT hTD k v h = D.gfun k v h := by
  rw [gCML, dif_pos hv, dif_pos hb]
  rfl

end EquationData

end ShortTime
