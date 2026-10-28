module

public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.LocalSubgroups
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.Coordinates

/-!
# Fixed words for the remaining max4 core calculations

These eleven words use the existing binary normal forms of the actual local
Sylow subgroup. Their containment in max4 follows from the checked word API.
This module makes no assertion that they belong to the core, generate it, or
satisfy a special-group presentation. Those are the concrete certificate
obligations, shared by the special-group and Steinberg calculations.

The candidate sequence was discovered by centralizing the marked eight-group
in the existing permutation data with GAP. GAP output is not a proof premise.
The first eight words are prospective quotient generators; the last three
are prospective center generators. Original ATLAS word attribution and the
inverse point-action convention are inherited from LocalCover.Data and
ElementaryCatalogue.Coordinates.
Source application: Aschbacher--Smith I.2.2(7), printed pp.412--413.
-/

namespace Rudvalis.CoveringIncidence.Max4Words
open SylowOvergroups SylowOvergroups.RadicalCoverage.LocalCover

/-- Indices into the published fourteen-generator binary normal forms. -/
@[expose] public def masks : Fin 11 → Fin 16384 :=
  ![15582, 3411, 768, 16101, 1149, 6192, 15920, 64, 11200, 8192, 12288]

/-- Candidate core generators, as literal elements of the original model. -/
@[expose] public def generator (i : Fin 11) : Model :=
  CatalogueCertificate.normalForm (masks i)

public theorem generator_mem_localP (i : Fin 11) : generator i ∈ localP :=
  CatalogueCertificate.normalForm_mem _

/-- The shared candidate words lie in the fixed max4, with its original embedding. -/
public theorem generator_mem_max4 (i : Fin 11) : generator i ∈ max4 :=
  localP_le_max4 (generator_mem_localP i)

end Rudvalis.CoveringIncidence.Max4Words
