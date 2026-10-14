# QCALean

Quantum cellular automata on a lattice, formalized in Lean 4 over Mathlib. The first instance is
bosonic: Gaussian quantum cellular automata, the translation-invariant, finite-range, quasi-free
dynamics of an infinite lattice of harmonic oscillators, following Chapter 4 of O. Krüger,
*Quantum Information Theory with Gaussian Systems* (PhD thesis, TU Braunschweig, 2006).

A reversible Gaussian automaton acts on the Weyl operators of the lattice through a linear map `L`
of the classical phase space, `α_L(W(u)) = W(Lu)`. Translation invariance makes `L` a convolution,
`(Lu)(x) = Σ_m ℓ_m u(x − m)`, with finitely many coefficient matrices `ℓ_m`, so that `L` is a
matrix `L̂(z) = Σ_m ℓ_m z^m` of Laurent polynomials, its **symbol**, and `L` preserves the
symplectic form exactly when

```
L̂(z⁻¹)ᵀ Ω L̂(z) = Ω,      Ω = [[0, I], [−I, 0]].
```

The library proves this criterion and the structure of the one-mode nearest-neighbour rules, the
Fourier criterion for translation-invariant covariance forms, and the principal result of the
chapter in the form of covariances and characteristic functions: for the example system of the
thesis, a reversible nearest-neighbour dynamics on the chain, the covariance of a
translation-invariant Gaussian state converges to limit cells built from an invariant matrix
function of the wave number, and
the states converge on every observable to a Gaussian state with that covariance. It ends with
irreversible automata, where each step is a Gaussian channel.

## What is proved

| | Main results | Notes |
|---|---|---|
| Symbols | Translation-invariant maps of the lattice phase space are matrices over the group algebra, composites have product symbols and finite range; the twisted criterion `M⋆ᵀ B M = B` for preserving a lifted form (thesis (4.9)–(4.11)), the inverse `B⁻¹ M⋆ᵀ B` and the group of such symbols | §1 |
| One mode, nearest neighbour | Thesis Prop. 4.4, corrected: the symplectic rules `ℓ₋z⁻¹ + ℓ₀ + ℓ₊z` are the pure shifts (a case the thesis omits) and those with `ℓ₀` symplectic, `ℓ₊ = ℓ₋` of rank at most one and `ℓ₊ᵀΩℓ₀ + ℓ₀ᵀΩℓ₊ = 0`; every Fourier mode of a symplectic symbol is symplectic; the symbol of the lattice Klein–Gordon leapfrog | §1 |
| Reversible automata | Reversible QCA (thesis Def. 4.1) and their composites (Cor. 4.3); the lattice CCR net is generating, causal, isotone and translation covariant; a symplectic rule is a reversible QCA with the range of its symbol as neighbourhood; a rule is determined by one site and is symplectic exactly when that site satisfies the commutation relations with its translates (Lemma 4.2 in Gaussian form); shifts, on-site rotations and squeezing, the example system and the leapfrog | §2 |
| Weyl type and the leapfrog | On the lattice CCR algebra, `T(W(u)) = c(u) W(Γu)` forces `Γ` symplectic and `c` a character of modulus one (the content of (4.7), with the character the thesis omits); the leapfrog is a symplectic bijection of Cauchy data, and one step of time translation acts on them as `F⁻¹` | §2 |
| Gaussian states on the lattice | Translation invariance of states and of characteristic functions; the action of a rule on Gaussian data; the covariance matrix `Ωᵀ γ_O Ω` of a region and the state condition as its admissibility; Lemma 4.5(i): the Fourier condition `γ̂(k) + iΩ ≥ 0` implies the state condition, and conversely for cells of finite range; the one-mode saturation conditions (Lemma 4.5(ii)); `γ̂′(k) = L̂(k)† γ̂(k) L̂(k)` ((4.17)) | §3 |
| The example system | `L̂(k) = Γ₀ + 2λ cos k Γ±` (4.18): ellipticity exactly when `\|cos φ\| + \|λ sin φ\| < 1`, the critical coupling (4.20) and the regime; the rotation angle, powers and projectors (Lemma 4.6, (4.21)–(4.24)); the invariant form `ε̂(k)` (4.28); Theorem 4.8 in both directions: in the regime, reflection-symmetric cell data are stationary and satisfy the Fourier condition exactly when `γ̂(k) = g(k) ε̂(k)` with `g` continuous, even and `g ≥ 1`; the leapfrog and its inverse have a mode that is not elliptic for every real `m²`, and for `m² = 0` the inverse is the example rule at `(π/2, 1)`, on the boundary of the regime | §4 |
| Convergence | A Riemann–Lebesgue lemma for an injective phase with nonvanishing derivative; in the regime, the evolved cells of cell data converge to the Fourier coefficients of `C(k) = ½(γ̂(k) + N(k)ᵀ γ̂(k) N(k))` (Prop. 4.7), which is invariant, inherits the Fourier condition and, for reflection-symmetric cell data, is a multiple `g ε̂(k)` with `g ≥ 1` at every `k` where `γ̂(k) + iΩ ≥ 0`; without coupling the covariance need not converge; for a Gaussian initial state with zero displacement given by such cells, the characteristic functions converge and the states converge on every element of the CCR algebra to a Gaussian state (the weak-* part of Theorem 4.9) | §5 |
| Irreversible automata | QCA (Def. 4.1) and the locality notions (I) and (II); lattice channels are QCA; Lemma 4.11 in both directions; the shift shows that factorization does not imply finite propagation, and the rule `0` gives the converse for every lattice channel with its data, whose existence is not proved (Lemma 4.10(v)); concatenation and the range inclusions of p. 96; the two-step claim of p. 97 corrected (true for isotropic noise, false for noise `diag(0, b)`); the data of a lossy chain satisfy the channel condition; the Fourier form of the channel condition (4.34); Lemma 4.12 at the level of covariances | §6–7 |

The precise statements are the 60 theorems of [`verify/CORE.md`](verify/CORE.md), under headings
that refine the rows of this table. Gaussian states and Gaussian channels with prescribed data enter
as hypotheses: the core constructs no Gaussian state, and Gaussian channels only without noise;
Lemma 4.12 is proved for the covariance data, without the dilating channel; complete positivity is
part of the definition of a Gaussian channel. Conventions, including the dictionary to the letters of the
thesis, are listed in `CONVENTIONS.md`.

## Verification

The 60 theorems of the core are 31 main results, 24 statements that describe the library's
definitions in Mathlib's terms (some with further facts, such as the formulas of the example
system), and 5 examples (a pure shift and a nearest-neighbour rule of the second kind, cells
satisfying the Fourier condition, a parameter point in the regime with vacuum cell data, a
noiseless lattice channel for every example rule, and a reversible automaton that is not on site),
which show that the hypotheses on parameters, cells and noiseless channels can be met and that the
objects are not degenerate; no Gaussian state is exhibited. `verify/Challenge.lean` states them without proofs, and `verify/Solution.lean`
proves them from the library. The command

```
lake comparator --config verify/comparator.json --paranoid
```

checks that every proved theorem has exactly the stated form, that no axioms beyond `propext`,
`Classical.choice` and `Quot.sound` are used, and that Lean's kernel and four independently
written proof checkers accept every proof. A reader who accepts the 60 statements therefore need
not read any proof. Besides the definitions described in the core, two kinds of structure are
taken from the libraries: the C*-algebra structure of the CCR algebra, a closed star subalgebra of
the bounded operators on `ℓ²(V)`, with its order as a star-ordered ring (needed for completely
positive maps), and the group structure of the automorphisms of a causal index, whose product the
core describes. The same check runs on GitHub at every change.

`lake comparator` is the proof judge maintained by the Lean developers for proofs whose author is
not trusted, including proofs produced by AI; see
[leanprover/comparator](https://github.com/leanprover/comparator) and the chapter
[Validating a Lean Proof](https://lean-lang.org/doc/reference/latest/ValidatingProofs/#validating-comparator)
of the Lean reference manual. Among its checkers are
[lean4lean](https://github.com/digama0/lean4lean) and [nanoda](https://github.com/ammkrn/nanoda_lib).
On Linux it isolates the compiled code in a sandbox; elsewhere it needs the option
`--inadvisably-no-sandbox`.

## Build and verify

With the Lean installer `elan`:

```
git clone https://github.com/etjoa002/QCALean
cd QCALean
lake exe cache get          # download the precompiled Mathlib
lake build QCALean
lake comparator --config verify/comparator.json --paranoid
```

The library depends on [Mathlib](https://github.com/leanprover-community/mathlib4),
[LocalAlgebrasLean](https://github.com/etjoa002/LocalAlgebrasLean) (regions, nets of local
algebras), [BosonicLean](https://github.com/etjoa002/BosonicLean) (the CCR algebra, its states,
Gaussian states and Gaussian channels, covariance matrices) and
[LinearAQFT](https://github.com/etjoa002/LinearAQFT) (causal indices and nets, the lattice
Klein–Gordon field); their versions, and that of Lean, are fixed in `lakefile.toml`,
`lake-manifest.json` and `lean-toolchain`, and are only ever changed together.

## Methods of proof

Everything rests on the Weyl relations `W(u) W(w) = e^{−iσ(u,w)/2} W(u+w)`: a symplectic rule
relabels the Weyl operators, and the relabelling is a star automorphism of the CCR algebra, so that
the statements about reversible automata reduce to linear algebra of the symbol over the ring of
Laurent polynomials, where symplecticity, inverses and the range of a rule are polynomial
identities. A Gaussian state is a prescription on labels, its characteristic function
`χ(u) = exp(i d(u) − γ(u,u)/4)`, and on the chain Parseval's identity turns the uncertainty
relation `γ + iσ ≥ 0` into the positivity of a Hermitian matrix at each wave number. For the
example system each Fourier mode is a rotation, so the evolved symbol splits into a
time-independent part and parts oscillating like `e^{±2itθ(k)}`, which vanish in the limit by the
Riemann–Lebesgue lemma; convergence of the states then follows from the bound `|ω(a)| ≤ ‖a‖` and
the density of the Weyl operators.

## The notes

[`docs/lecture-notes/QCALean.pdf`](docs/lecture-notes/QCALean.pdf) gives the account with full
proofs, examples and a dictionary to the thesis, in the sections listed in the table above, after a
reading guide on the translation between forms on phase space and the familiar covariance and
channel matrices. A tag beside a theorem links to the Lean declarations that prove it; every
example is marked as proved in Lean, checked by a script, or checked on paper. A few pinpoint
citations to secondary sources are marked in the text as not yet checked against the source.

## Numerical checks

The scripts in `checks/` (Python with SymPy and NumPy; `checks/requirements.txt`) test the
formulas of the thesis and the statements of the library independently of Lean, including the
transposes, signs and index conventions where the thesis and the libraries it is compared with
differ: `symbols_check.py` the symbol calculus, the twisted criterion and the nearest-neighbour
rules; `reversible_check.py` the reversible automata and the leapfrog; `states_check.py` the
conventions of Gaussian states, the covariance matrices of regions and the Fourier criterion;
`stationary_check.py` the example system, its regime, projectors and stationary states;
`convergence_check.py` the convergence of the covariance and of the characteristic functions (in
floating point, at tolerance `1e-9`, since these are statements about limits and integrals);
`channels_check.py` the Gaussian channels and the lattice results of thesis §4.3, in exact
arithmetic. Each script asserts every identity it tests and stops at the first failure; run, for
example, `python -X utf8 checks/channels_check.py`.

## Library layout

`Core/` the phase-space layer, which needs Mathlib only (lattice phase space, symbols, lifted
forms, Fourier series, the Riemann–Lebesgue lemma); `Net/` quantum cellular automata on a net of
local algebras and their locality; `Bosonic/` the Gaussian instance; `verify/` the core.

<details>
<summary>Lean files and their imports</summary>

<!-- depgraph:start -->
- `Core/`
  - `Core.Form` imports `Core.Symbol`
  - `Core.FourierSeries` imports Mathlib only
  - `Core.Lattice` imports Mathlib only
  - `Core.RiemannLebesgue` imports Mathlib only
  - `Core.Symbol` imports `Core.Lattice`
- `Net/`
  - `Net.Automaton` imports files of LocalAlgebrasLean and LinearAQFT only
- `Bosonic/`
  - `Bosonic.Automaton` imports `Bosonic.PhaseSpace`
  - `Bosonic.CellForm` imports `Bosonic.Covariance`, `Core.FourierSeries`
  - `Bosonic.Cells` imports `Bosonic.State`
  - `Bosonic.Convergence` imports `Bosonic.Stationary`, `Core.RiemannLebesgue`
  - `Bosonic.Covariance` imports `Bosonic.Cells` and files of BosonicLean
  - `Bosonic.ExampleSystem` imports `Bosonic.CellForm`, `Bosonic.Examples`
  - `Bosonic.Examples` imports `Bosonic.Automaton`, `Bosonic.Fourier`
  - `Bosonic.Fourier` imports `Bosonic.NearestNeighbour`
  - `Bosonic.Irreversible` imports `Bosonic.Kernels`, `Bosonic.Automaton` and files of LinearAQFT and BosonicLean
  - `Bosonic.Kernels` imports `Bosonic.CellForm`, `Bosonic.Examples`, `Bosonic.Fourier`
  - `Bosonic.Leapfrog` imports `Bosonic.Examples` and files of LinearAQFT
  - `Bosonic.NearestNeighbour` imports `Core.Form` and files of BosonicLean
  - `Bosonic.PhaseSpace` imports `Net.Automaton`, `Bosonic.Translation` and files of LinearAQFT
  - `Bosonic.State` imports `Bosonic.WeylAutomorphism`, `Bosonic.Fourier` and files of BosonicLean
  - `Bosonic.Stationary` imports `Bosonic.ExampleSystem`
  - `Bosonic.Translation` imports `Bosonic.NearestNeighbour`
  - `Bosonic.WeylAutomorphism` imports `Bosonic.Automaton` and files of BosonicLean
<!-- depgraph:end -->

</details>

## Status

The library is under development, and this repository is updated as the work progresses; see
`CONTRIBUTING.md` for problem reports and suggestions. Planned next are quantum cellular automata
of qudits and matrix product unitaries, on the quasi-local algebra of LocalAlgebrasLean, and the
Clifford and fermionic Gaussian instances on the same phase-space layer. Candidates for later
theorems: a Gaussian state for every form satisfying `γ + iσ ≥ 0`, and complete positivity of every
map whose data satisfy the channel condition (B. Demoen, P. Vanheuverzwijn and A. Verbeure,
Lett. Math. Phys. 2 (1977) 161–166), both in
BosonicLean, which would make the results on the lattice unconditional; convergence in trace norm
on finite regions ((4.30)–(4.31) of Theorem 4.9); Lemma 4.2 and Cor. 4.3 for general cells, which
need infinite tensor products of the cell algebras; the locality notions (III) and (IV) and Lemma
4.10(i)–(iv); the dilating channel of Lemma 4.12 on the algebra; the structure theorem for
reversible QCA (B. Schumacher and R. F. Werner, arXiv:quant-ph/0405174).

## Citation and licence

Erickson Tjoa, *QCALean: quantum cellular automata in Lean*, 2026,
https://github.com/etjoa002/QCALean. Apache 2.0 (`LICENSE`, `NOTICE`); `CITATION.cff` gives the
reference in machine-readable form. The mathematics follows O. Krüger, *Quantum Information Theory
with Gaussian Systems*, PhD thesis, TU Braunschweig (2006), Chapter 4, published in part as
O. Krüger and R. F. Werner, "Gaussian quantum cellular automata", in N. J. Cerf, G. Leuchs and
E. S. Polzik (eds.), *Quantum Information with Continuous Variables of Atoms and Light*, Imperial
College Press (2007); the definition of a quantum cellular automaton is that of B. Schumacher and
R. F. Werner, arXiv:quant-ph/0405174. The other sources are cited in the notes and in the Lean
files.

Developed with AI assistance. The author approved every definition and theorem statement and is
responsible for the content; every proof is checked by Lean.
