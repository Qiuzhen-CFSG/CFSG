module

public import Theory.SpecificGroups.Monster.Construction.Symmetric
public import Theory.SpecificGroups.Monster.Construction.GriessCarrier
public import Theory.SpecificGroups.Monster.Construction.LocalEmbedding
public import Theory.SpecificGroups.Monster.Construction.LocalC.SourceConstruction

/-!
# The explicit Griess algebra and its local automorphisms

The fixed 196884-dimensional real space, positive form, exact five-block
symmetric trilinear form and recovered multiplication are constructed in
`GriessCarrier`. Their simultaneous stabilizer is the parameter-free group
`Sporadic.Monster.GriessGroup`.

`CInvariance` proves source 28.13 for the actual spin–Leech local group.
`LocalEmbedding` embeds this group and its literal `N₁/K` and extraspecial
subgroups into the Griess group. The specified `griessZ` is a nonidentity
involution with source signs and fixed space. `LocalC.SourceConstruction`
identifies the local tensor image with the determinant-one source pullback.

The full `N/K` action and its form-preservation proofs from Sections 29–30
remain to be assembled. The reverse centralizer containment, finiteness and
simplicity belong to their separate consumers.

Source: Aschbacher, *Sporadic Groups*, Sections 27–30.
-/
