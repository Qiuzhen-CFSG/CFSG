module

public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.NormalizerGeometry.DerivedEightConjugacy.LocalCentralizers.Reduction
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.NormalizerGeometry.DerivedEightConjugacy.LocalCentralizers.Representatives
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.NormalizerGeometry.DerivedEightConjugacy.LocalCentralizers.Sieve

/-!
# Derived normality for Rudvalis local centralizers with central involutions

For a square-one element of the fixed `localP`, suppose its local centralizer
has order 256 and every square-one element of that centralizer is central.
The checked sieve conjugates it inside `localP` to one of three actual words.
Their derived subgroups equal the marked `elementary 2`, which `localP`
normalizes. Local conjugation therefore proves the exact relative normality
criterion, with no remaining certificate premises.

The conditional transport and assembly APIs remain publicly available from
`Reduction`. The parent `DerivedEightConjugacy` owns the transport from the
ambient involution centralizer and the source conjugacy conclusion.

Source motivation: GLS3 Table 5.3r and pp.291–292; Aschbacher–Smith I.2.2(7),
pp.412–413. The criterion in `LocalCriterion` is a sufficient concrete lemma,
not itself a statement quoted from these sources.
-/

namespace Rudvalis.CoveringIncidence.NormalizerGeometry

/-- In the fixed local subgroup, an order-256 involution centralizer with
central square-one elements has derived subgroup normalized by `localP`. -/
public theorem localCentralizerDerivedNormal : LocalCentralizerDerivedNormal :=
  localCentralizerDerivedNormal_of_certificates
    LocalCentralizers.representativeCover LocalCentralizers.representativeDerived

end Rudvalis.CoveringIncidence.NormalizerGeometry
