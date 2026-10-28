module

public import Theory.SpecificGroups.HaradaNorton.Construction
public import Theory.SpecificGroups.HaradaNorton.Generators
public import Theory.SpecificGroups.HaradaNorton.Order
public import Theory.SpecificGroups.HaradaNorton.Simplicity

/-!
# Harada–Norton model interface

`HaradaNorton.HN` is the fixed finite group constructed from the explicit ATLAS
133-dimensional matrices over `ZMod 5`. This interface exports its group and
finiteness instances, an injective matrix homomorphism, the certified generating
pair, and noncommutativity. Checked word relations prove perfectness and normal
generation by the involution `a`; a matrix commutant certificate proves that the
center is trivial. The explicit ATLAS word subgroup `OrderCertificate.localSubgroup`
is identified with the alternating group on twelve letters.

The source data, transcription and action convention are documented in
`MatrixSources.md`. The remaining order obligation is
`OrderCertificate.localSubgroup.index = 1140000`, by
`OrderCertificate.card_HN_iff_local_index`. The remaining premise of
`simple_of_maximal_centralizer` is `IsCoatom generatorCentralizer`.
Neither certificate is yet supplied, so this interface makes no unconditional
simplicity or exact-order claim. The construction uses the fixed source matrices,
not the ATLAS order or subgroup labels as assumptions.
-/
