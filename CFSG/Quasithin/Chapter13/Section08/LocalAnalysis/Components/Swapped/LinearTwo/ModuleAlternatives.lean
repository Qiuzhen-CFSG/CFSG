module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.Orbit
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.Projection
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.MaximalSection
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.SeedProjection
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.SourceAction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.SourceSeed
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.SeedTransport
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.FactorSpaces

/-!
# Source actions and section constructions for the swapped linear-two case

Conjugation constructs the binary action on the literal U_H/V₁, descending
through H/O₂(H). The actual subgroup seed gives a nonzero irreducible marked
submodule, with its fixation and commutator generation transported from group
statements modulo V₁. Its H*-orbit spans the whole module. Maximal invariant
quotients retain an injective equivariant seed projection and its marked
properties; no K₀-irreducibility is inferred from H*-maximality.

The generated overgroup and L₁ ≤ K₀ make K₀ normal relative to H, and the
source seed then proves Ũ_H = [Ũ_H,K₀]. Canonical commutator submodules
provide the factor sum and its exchange by the actual conjugation operator.
Together with cross-factor fixation, they feed the existing obstruction from
equal marked projections, without assuming the sum is direct.

The applications of the full F.9.18 and B.4/B.5 implications are still
outstanding. In particular this module does not yet prove the three
classification alternatives or an orthogonal-module identification. Those
must provide cross-factor fixation in (a)/(b1), and an actual marked group
and module equivalence with the natural POmegaPlus(2,F) action in (b2).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
standing setup on printed pp.946–947, proof of 13.8.16(1) on p.952
(PDF p.969), and F.9.18(5–6) on pp.325–326.
-/
