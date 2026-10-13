# Conventions

## Mathematics

### Phase space and the CCR algebra

- The lattice `G` is an additive abelian group (`ℤ` for chains), with points `x`. Each site carries
  `n` modes; the coordinates of a cell list all positions before all momenta, and the symplectic
  matrix of a cell is `Ω = [[0, I], [−I, 0]]` (the negative of Mathlib's `Matrix.J`, BosonicLean's
  `Gaussian.symplecticForm n`), with `Ωᵀ = −Ω = Ω⁻¹`. For one mode all orderings agree; for `n > 1`
  the mode-by-mode ordering of the thesis's (2.3) differs from this one by a permutation.
- The phase space `V` consists of the finitely supported maps `u : G → ℝ^{2n}`, with vectors `u, w`
  and the form `σ(u, w) = Σ_x u(x)ᵀ Ω w(x)`. In the phase-space layer the same objects are written
  over any commutative ring `R`, as vectors of elements of the group algebra `R[G]`; "alternating"
  means `vᵀBv = 0` for all `v`, which differs from skew-symmetry over `ℤ/2`.
- Weyl operators satisfy `W(u) W(w) = e^{−iσ(u,w)/2} W(u + w)` and `W(u)* = W(−u)`, with `ħ = 1`
  and `[R_k, R_l] = iσ_kl`; `CCR(V, σ)` is the C*-algebra they generate on `ℓ²(V)`.
- Translation by `a` pushes forward: `(κ_{a*}u)(x) = u(x − a)` on `V`, `α_a` on `CCR(V, σ)`, and
  `κ_a O = O + a` on regions. The thesis's `τ_Δ`, `(τ_Δ ξ)_x = ξ_{x+Δ}`, is `κ_{a*}` at `a = −Δ`.
- Regions are sets of sites `O`; a neighbourhood `N` is a finite set of sites, and `𝒜(O)` is the
  local algebra of `O`. Regions are orthogonal when disjoint.
- C*-algebras are unital and complex; inner products are linear in the second argument.

### Rules and symbols

- A rule is a translation-invariant linear map `L` of `V`, `(Lu)(x) = Σ_m ℓ_m u(x − m)`, with
  coefficients `ℓ_m`; its symbol is `L̂(z) = Σ_m ℓ_m z^m`, so that `z^m` is translation by `+m`.
  On the circle, `z = e^{−ik}` and `L̂(k) = Σ_m ℓ_m e^{−ikm}`, the sign of the thesis's (4.14).
- `M⋆` is the symbol with `z` replaced by `z⁻¹` (the involution of `R[G]` induced by `g ↦ −g`);
  on the circle it becomes complex conjugation. A rule preserves the lifted form of `B` exactly when
  `M⋆ᵀ B M = B`.
- One step of an automaton is the forward Heisenberg map, `α_L(W(u)) = W(Lu)`; automorphisms and
  channels compose as `T₂ ∘ T₁`, and the rule of a composite is `L₂L₁`. For the lattice
  Klein–Gordon field, whose leapfrog step `F` maps the Cauchy data of one time slice to the next,
  the forward rule in this convention is `F⁻¹`.
- The coupling of a nearest-neighbour rule is `λ` (the thesis's `f`); the range of a rule is
  `N_L = {m : ℓ_m ≠ 0}`.

### States and covariances

- A state `ω` has the characteristic function `χ_ω(u) = ω(W(u))`. A Gaussian state has
  `χ_ω(u) = exp(i d(u) − γ(u,u)/4)`, with displacement `d` and covariance **form** `γ`, a symmetric
  bilinear form on `V` (the thesis's `γ`); the vacuum has `γ(u,u) = Σ_x |u(x)|²`. The state condition
  is `γ + iσ ≥ 0`, meaning that `[γ(u_j,u_k) + iσ(u_j,u_k)]_{j,k}` is positive semidefinite for every
  finite family of vectors.
- The covariance **matrix** of a finite region `O` is `cov_O(γ) = Ωᵀ γ_O Ω`, where `γ_O` is the
  matrix of `γ` on the site vectors of `O`, reordered to all positions before all momenta. It is
  BosonicLean's covariance matrix of `n|O|` modes, twice the symmetrized second moments (vacuum
  `I`), and it is admissible when `γ_B − iΩ ≥ 0`. The state condition on `O` is admissibility of
  `cov_O(γ)`, since `Ωᵀ(γ_O − iΩ)Ω = Ωᵀγ_OΩ − iΩ`. The two conventions meet in one Lean file,
  `Bosonic/Covariance`.
- Under a rule, the form transforms as `γ ↦ γ(L·, L·)` and the displacement as `d ↦ d ∘ L`; the
  relabelling `W(u) ↦ W(Su)` by a symplectic matrix `S` acts on a covariance matrix as
  `M ↦ S⁻¹MS⁻ᵀ`, with `S⁻¹ = ΩᵀSᵀΩ`.
- A translation-invariant form on the chain is given by its cells `γ_x`,
  `γ(u, w) = Σ_{x,y} u(x)ᵀ γ_{x−y} w(y)`, with `γ_{−x} = γ_xᵀ`; cell data are absolutely summable.
  The symbol is `γ̂(k) = Σ_x γ_x e^{−ikx}`, and under a rule
  `γ̂′(k) = L̂(−k)ᵀ γ̂(k) L̂(k) = L̂(k)† γ̂(k) L̂(k)`; the thesis's (4.17b) is the reflection-symmetric
  case.
- A Gaussian channel acts by `T(W(u)) = exp(i μ(u) − ν(u,u)/4) W(Lu)`, with displacement `μ` and
  noise form `ν` (the thesis's `g`); complete positivity is part of its definition, and the
  condition on its data is `ν + iσ − iσ(L·, L·) ≥ 0`.

### Dictionary to the thesis

| Object | Here | Krüger's thesis |
|---|---|---|
| phase space, vectors | `V`; `u, w` | `Ξ`; `ξ, η` |
| one-mode symplectic matrix | `Ω` | `σ₀`, `σ_s` |
| modes per cell | `n` | `f` |
| region | `O` | `Λ` |
| translation | `κ_{a*}` | `τ_Δ`, with `a = −Δ` |
| rule, global rule | `L`, `α_L` | `Γ`, `T` |
| coefficients, symbol | `ℓ_m`, `L̂(z)` with `z = e^{−ik}` | `Γ_m`, `Γ̂(k)` |
| coupling | `λ` | `f` |
| rotation angle, factor of a stationary state | `θ(k)`, `η(k)` (notes) | `α(k)`, `g(k)` |
| noise form | `ν` | `g` |

The letter `Γ` is not used for rules (it is a group in LinearAQFT and a covariance in BosonicLean),
`Λ` not for regions, `τ` not for translations, and `f` neither for modes nor for couplings. In the
Lean files of the example system the rotation angle is `alpha`, the thesis's letter.

## Lean

- One definition per concept: QCALean imports what LocalAlgebrasLean, LinearAQFT and BosonicLean
  define, and defines only what none of them has. A declaration lives in the most general library
  that can state it; general bosonic results belong to BosonicLean.
- Namespaces `QCALean.Core`, `QCALean.Net` and `QCALean.Bosonic`, matching the folders. QCALean
  defines no names in the namespace `Gaussian`, and six lattice-specific results carry
  BosonicLean's namespace `BosonicLean.Weyl` so that dot notation works on its objects:
  `GaussianState.evolve`, `GaussianState.evolve_cov`, `GaussianState.evolve_disp`,
  `GaussianState.evolve_cov_const`, `GaussianState.isAdmissible_covarianceMatrix` and
  `IsStateCondition.isStateConditionOn`.
- `Core/` imports Mathlib only; `Net/` imports Mathlib, LocalAlgebrasLean and the nets of
  LinearAQFT; `Bosonic/` imports all of these and BosonicLean.
- Maps of phase space are `≃ₗ[ℝ]`, forms are `LinearMap.BilinForm`, and preservation of a form is
  stated as `∀ u w, σ (L u) (L w) = σ u w`.
- Declaration names are ASCII and follow Mathlib's naming and style.
- No unfinished proofs, no added axioms, no unchecked computation, no blanket import of Mathlib;
  assumptions (the existence of a state, complete positivity) are hypotheses or structure fields.
