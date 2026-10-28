module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.ElementTests.Positives
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.ElementTests.Obstructions

/-!
# The elementary-element test for all Rudvalis binary normal forms

For every one of the 16384 coordinate masks, a kernel-checked witness either
refutes its square/commutation test or supplies membership in a fixed candidate
and a local conjugator to its marked generator. All positive equalities are
checked on every point of the original degree-4060 carrier and transferred by
`PcComparison` and `ElementaryComparison`. No normal-form coverage, cardinality,
ambient normalizer or Sylow assumption enters this proof.

Source: the preserved ATLAS words and untrusted witnesses documented in
`ElementaryCatalogue/source/README.md` and `Generate.g`; the intended local
application is GLS3 Table 5.3r and quasithin printed p.511, citing [Asc86b].
The independent `NormalFormCover` obligation remains with the catalogue assembly.
-/

namespace Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.CatalogueCertificate

/-- Unconditional certification of the exact normal-form element test. -/
public theorem normalFormTest : NormalFormTest := by
  intro n ht
  exact ElementChecks.result_of_rowCheck ElementChecks.positiveResults n
    (ElementChecks.checked n) ht

end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.CatalogueCertificate
