module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.Basic
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.OddSubgroups
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.Tori
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.Automorphisms
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.Covers
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.Source
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.MarkedField

/-!
# Concrete model inputs to GLS Section 16

The exports identify perfect odd central covers of the simple Bender models
with the actual PSL₂, Suzuki, PSU₃ or SU₃ carriers, retaining their source
parameters and the possible center of order three. Their Sylow omega
subgroups are the embedded centers and the normalizers' involution cores.
The two-point tori, commutator tori and fixed tori have the source orders.

The literal subgroup `rootGenerated` is the whole group in the linear and
Suzuki cases, and an actual PSL₂ subgroup in both unitary cases. The marked
generation and fixed-involution implications hold on the original covering
group. Arbitrary outer involutions of a linear model have square-root-field
fixed groups and act on the marked torus by square-root Frobenius. `MarkedField`
deduces inversion on the ambient p-core for primes dividing the square-root
field order plus one. The
odd-subgroup cyclicity results retain the precise relative normalization
and inverter containment needed in Proposition 16.5.

`Source` assembles the common geometry from perfectness, odd center and an
actual model of the central quotient. Applying these results to the ambient
ZD centralizer closures and proving Proposition 16.5 remain with `RankOne`.

Source: GLS, Volume 4, Chapter 2, Section 16; Chapter 4, Sections 2–3.
-/
