# Short-time existence for higher-order parabolic equations on manifolds

A Lean 4 formalization project, together with a companion paper, for one theorem that geometric
analysis uses constantly and rarely proves:

> **Theorem.** Let `(M, g)` be a closed Riemannian manifold, `V → M` a tensor bundle, and
> `∂ₜu = F(t, u, ∇u, …, ∇^{2p}u)` a fully nonlinear equation of any even order `2p`.
> Suppose the equation is parabolic at a smooth initial datum `u₀`, in the sense of the
> *Legendre condition* on its linearization. Then:
>
> 1. **(A)** there is a smooth solution on `M × [0,T]` for some `T > 0`;
> 2. **(B)** it is unique among parabolic solutions;
> 3. **(C)** it depends continuously on `u₀` in `C^∞` (the paper also shows smooth dependence in Sobolev
>    norms; that part is not formalized, see Status).

This covers, for example:

- the quasilinear equations of Mantegazza–Martinazzi, *A note on quasilinear parabolic equations
  on manifolds*, Ann. SNS Pisa (2012);
- polyharmonic map flows of every order;
- the Ricci–DeTurck flow;
- parabolic Monge–Ampère equations.

## The companion paper

**[`paper/main.pdf`](paper/main.pdf)** ([source](paper/main.tex)) contains the full mathematical
argument. It is written as a classical paper, and it is also the **blueprint** of the
formalization: every definition, lemma and theorem carries a machine-readable annotation naming its
Lean counterpart and its dependencies. It is also meant to be readable on its own.

The proof is arranged for formalization. Compared with the literature, it avoids:

- trace, interpolation and fractional Sobolev spaces;
- Fourier analysis;
- linear theory with non-smooth coefficients.

Regularity comes from the implicit function theorem via Angenent's parameter trick.

## The blueprint map

**[`blueprint/map.md`](blueprint/map.md)** shows the dependency graph of the whole proof, with the
formalization status of every item. It is generated from the paper and the Lean sources:

```sh
python scripts/blueprint.py map     # regenerate blueprint/map.md
python scripts/blueprint.py check   # dangling references, cycles, axioms, pinned statements
python scripts/blueprint.py pin <Decl> ...   # freeze an approved statement
```

A statement is *pinned* once it has been reviewed. `check` then fails if its text changes, so the
target cannot drift while proofs are being filled in.

## Status

**All three trusted theorems and the Mantegazza–Martinazzi corollary are proved in Lean, with no
`sorry`.** `lake build` succeeds, and `#print axioms` of each lists only `propext`,
`Classical.choice` and `Quot.sound`. The blueprint check reports 0 declarations with `sorry`.

| Result | Lean | Status |
|---|---|---|
| Theorem A (existence, regularity) | `ShortTime.exists_solution` | proved |
| Theorem B (uniqueness) | `ShortTime.solution_unique` | proved |
| Corollary C (continuous dependence, sequential form) | `ShortTime.solution_continuous_dependence` | proved |
| Maximal solutions | `ShortTime.exists_maximal_solution` | proved |
| Mantegazza–Martinazzi | `ShortTime.mantegazza_martinazzi` | proved |

The statements of A, B, C and every definition they use are **pinned**
(`blueprint/pinned.json`), so the proofs cannot silently change what is claimed. The design choices
are in [`blueprint/DECISIONS.md`](blueprint/DECISIONS.md).

What the statements say, in the main file `ShortTime/MainTheorems.lean`: for an equation
`∂ₜu = F(t, x, u, ∇u, …, ∇^{2p}u)` on a tensor bundle over a closed Riemannian manifold, a smooth
datum at which the equation is parabolic in the Legendre sense has a smooth solution on some
`[0,T]` (A); two parabolic solutions with the same datum coincide (B); and if the data converge in
`C^∞` then, for large `n`, the solutions exist on the same `[0,T]` and converge in `C^∞` (C).

`ShortTime.mantegazza_martinazzi` (`ShortTime/MM/Main.lean`) applies this to the scalar quasilinear
equation with product-form positive definite coefficients `E₁⊗⋯⊗E_p`. MM's index pairing is
rewritten, using the Ricci identity as an exact smooth function of the jet, into one whose principal
coefficient satisfies the Legendre condition. The rewritten equation has the same solutions. The
formal hypothesis is pointwise positive definiteness of the `E_ℓ`, which is the paper's locally
uniform positivity by continuity.

**Not formalized.** Theorem C in the paper's full form (a smooth solution map on `H^{2pm}` data) is
not pinned and is not needed for the results above. The Lean proof of Corollary C takes a different
route, documented in `DECISIONS.md`: it perturbs the fixed solution by a time-independent family,
applies the implicit function theorem with a parameter, and uses regularity in trace form at the
fixed base solution.

## Roadmap

**Theorem C (smooth dependence) is a goal of this project that is not yet done.** In the paper
(`thm:C`) it says that, near a given solution `u`, the data-to-solution map is a `C^∞` map
`𝒮 : {a ∈ H^{2pm} : ‖a - u₀‖ < δ} → 𝒫^m` into the parabolic Sobolev space, and `𝒮(a)` is the smooth
solution for smooth `a`. It is not one of the pinned statements, and nothing proved here depends on
it: Corollary C (sequential continuous dependence in `C^∞`), and hence the Mantegazza–Martinazzi
theorem, are proved by a different route that needs only the implicit function theorem at the fixed
base solution (see `blueprint/DECISIONS.md`). Formalizing `thm:C` itself needs:

- the Sobolev space `H^{2pm}` of initial data, with an extension operator into `𝒫^m`;
- the parametric version of the regularity argument, to see that `𝒮(a)` is smooth for smooth `a`.

The parametric Nemytskii operator, the smooth-dependence input of the IFT, and the regularity
machinery it builds on are already in the repository (`exists_nonlinOp_param_ball`,
`regularity_of_time`), so the remaining work is a matter of assembly. Contributions are welcome.

Other items marked `planned` or `partial` in [`blueprint/map.md`](blueprint/map.md) are
intermediate lemmas whose statements are not pinned.

**Trust boundary.** The result is only as good as the pinned definitions. These are
`EquationData`, `IsParabolicSolution`, `LegendreAt`, `covJet` and the Fréchet-type convergence in
the statement of C. `ShortTime/Sanity/` checks non-vacuity of the pinned definitions: the heat equation is a
parabolic equation with a solution, and the Legendre condition holds for the polyharmonic principal
part in every order. The hypotheses of the MM theorem are satisfiable: `MMData.polyharmonic` (`ShortTime/Sanity/MMInstance.lean`)
is the polyharmonic flow with `E_ℓ = g⁻¹`, and `polyharmonic_short_time` is the MM theorem instantiated
there. (Not checked in Lean: that its right side agrees with the textbook formula for `(-Δ)^p`.)

| Layer | Content | Paper |
|---|---|---|
| L1 | jets, equation data, Legendre condition | §2 |
| L2 | Sobolev and parabolic Sobolev spaces, composition operators | §3 |
| L3 | linear theory: Gårding, energy estimates, method of continuity | §4 |
| L4 | existence, regularity, uniqueness, smooth dependence | §5 |

## Building

Requirements: [elan](https://github.com/leanprover/elan). The toolchain is pinned in
`lean-toolchain` (Lean `v4.33.1`).

```sh
lake exe cache get   # prebuilt Mathlib
lake build           # also compiles the needed part of the differential-geometry library
```

The project depends on the Lean library
[`qinz1yang/differential-geometry`](https://github.com/qinz1yang/differential-geometry), pinned at
`v0.1.3` (Mathlib `v4.33.1`). That library ships no build cache, so the first build compiles about
500 of its files locally. This takes one to two hours on a laptop. Three of its files, whose library
versions import about 400 unrelated modules, are vendored with trimmed imports in
`ShortTime/Vendor/`.

On machines with 16 GB of RAM or less, limit parallelism: `LEAN_NUM_THREADS=4 lake build`.
Otherwise Lean runs one process per core and the build fails with spurious
"failed to read file …olean" errors.

To rebuild the paper: `cd paper && latexmk -pdf main.tex`.

## Layout

```
README.md            this file
CLAUDE.md            rules and task order for AI agents working on the repo
paper/               companion paper (the blueprint): main.tex, main.pdf
blueprint/map.md     generated dependency graph and status table
blueprint/pinned.json  frozen statements (created by `blueprint.py pin`)
blueprint/DECISIONS.md log of design decisions and of any change to a pinned statement
ShortTime/           Lean sources
  Setting/           jets, Legendre condition, equation data and solutions
  Analysis/          general analysis lemmas (smooth parametric integrals up to the boundary)
  Linear/            linear theory: operators, integration by parts, Gårding, energy, uniqueness
  Nonlinear/         nonlinear theory: existence, regularity, uniqueness, continuous dependence
  Sanity/            non-vacuity checks: the heat equation satisfies the pinned hypotheses
  Vendor/            library files copied with trimmed imports (see file headers)
  MM/                the Mantegazza–Martinazzi corollary
  Maximal.lean       maximal solutions
  MainTheorems.lean  Theorems A, B, C
scripts/blueprint.py map generator and checks
```
