module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.PcComparison
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.Coverage.Collection

/-!
# Coverage by the fixed Rudvalis binary normal forms

The certified square and inverse-conjugate relations make the fourteen
coordinate words triangular. Successive two-coset extensions therefore
cover their generated subgroup by ascending binary products. The existing
word comparison identifies that subgroup with the unchanged `localP`.

This proves surjectivity without an order calculation or uniqueness claim.
The ATLAS words and point convention are preserved in the adjacent `source/`
directory; the local application is [Asc86b], quasithin printed p.511,
and GLS3 Table 5.3r.
-/

namespace Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.CatalogueCertificate

/-- Every element of the fixed local subgroup has the specified ascending
binary normal form. -/
public theorem normalFormCover : NormalFormCover := by
  intro x hx
  have hx' : x ∈ Subgroup.closure (Set.range pcGenerator) := by
    rwa [closure_pcGenerator_eq]
  exact Theory.GroupTheory.BinaryCollection.cover_ofFn pcGenerator
    Coverage.pcGenerator_triangular x hx'

end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.CatalogueCertificate
