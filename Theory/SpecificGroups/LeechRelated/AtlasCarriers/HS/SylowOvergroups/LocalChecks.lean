module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowOvergroups.Data

/-!
# Coordinates for the HS elementary local representatives

The packed maps used in the Sylow double-coset certificate are identified
with the existing eight-element elementary subgroup. Every equality is
checked on the actual 100-point permutation representation.

Source: ATLAS HSG1-p100B0; Aschbacher--Smith A.3.12(18), pp.47--48.
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS.SylowOvergroups
open Data EvenLocalCandidates.SylowCatalogueData
set_option Elab.async false

set_option maxRecDepth 100000 in
theorem small_values : ∀ (i : Fin 8) (p : Fin 100),
    packedMap (eCode i) p = (small i : Equiv.Perm (Fin 100)) p := by
  apply allFin
  decide +kernel

end Sporadic.LeechRelated.HS.SylowOvergroups
