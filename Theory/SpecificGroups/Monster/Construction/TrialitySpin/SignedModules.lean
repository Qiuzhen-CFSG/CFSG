module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.Core
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.Spin
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.SpinActions
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.DirectSum
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.Natural
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.Irreducibility

/-!
# Signed real modules for the Parker triality construction

The actual Parker axes give `B1A2`, `B1A3`, and `SpinSpace`, of dimensions
2048, 2048, and 4096. Restriction is an isometric linear equivalence with
`SpinDirectSum`, carrying signed axis vectors to their respective summands.
Both realizations have constructed monomial actions, normalized positive
forms, and kernels characterized by fixation of every actual `k1` orbit.

`SpinActions` also constructs `B3A2` and proves the generator formulas of
27.3(1)–(4), including odd transport between the correct source and target
spaces and the effects of the generators listed in 27.3(5)–(6).
`SignedModules.Natural` constructs the 24-dimensional space on the actual
Golay coordinate halfspaces, identifies its positive basis with `Omega`,
and proves the halfspace formulas of 27.4(1)–(3) and the exact geometric
kernel criterion. On spin and natural space respectively, `z1` acts as
minus identity and identity, while `psi2(sπ)` acts as identity and minus
identity.

The real extraspecial trace-duality argument proves spin irreducibility from
an explicit extraspecial quotient of order `2^25` whose nonidentity central
involution acts as minus identity. The adapter to the constructed signed
representation derives this sign from `z1` and identifies the quotient kernel.
It does not assume irreducibility.

Source: Aschbacher, *Sporadic Groups*, Lemma 14.6, Exercise 4.3, and the
signed-module constructions in Section 27, printed pp. 146–147 (PDF p. 79).
The unconditional `N1` actions, structural subgroup-kernel identifications,
discharge of the explicit extraspecial-quotient hypotheses, and tensor kernel
of Lemma 27.5 belong to the parent triality-spin assembly.
-/
