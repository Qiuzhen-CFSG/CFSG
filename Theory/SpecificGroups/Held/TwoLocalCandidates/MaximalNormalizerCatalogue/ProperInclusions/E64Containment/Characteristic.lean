module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ElementaryWords
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralWord

/-!+# Characteristic subgroups of Held centralizers

The normalizer of a subgroup acts on its ambient centralizer. A characteristic
subgroup of that centralizer is therefore normalized as well. The containment
in the centralizer is explicit: characteristicity of a `subgroupOf` alone
would concern only an intersection.

This supplies the transport step for catalogue rows 1, 3 and 5. Their concrete
centralizer and characteristicity facts remain independent certificates.
Source context: GLS3 Table 5.3p and the literal ATLAS Held subgroup words.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment
open Subgroup

public theorem normalizer_le_of_characteristic_centralizer (X E : Subgroup He)
    (hle : E ≤ centralizer (X : Set He))
    (hchar : (E.subgroupOf (centralizer (X : Set He))).Characteristic) :
    normalizer (X : Set He) ≤ normalizer (E : Set He) := by
  let C := centralizer (X : Set He)
  have hn : normalizer (X : Set He) ≤ normalizer (C : Set He) :=
    (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer _)).mp inferInstance
  apply le_normalizer_iff.mpr
  intro g hg x hx
  let a := C.normalizerMonoidHom ⟨g, hn hg⟩
  have hmem : (⟨x, hle hx⟩ : C) ∈ E.subgroupOf C := hx
  exact characteristic_iff_le_comap.mp hchar a hmem

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment
