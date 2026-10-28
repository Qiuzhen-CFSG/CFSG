module

public import Theory.GroupTheory.SubgroupConjugation

/-!
# Right conjugation of subgroups

The right-conjugation convention used in Huppert X.4 is inverse left
conjugation. This definition is promoted from Peterfalvi's Chapter I §1
interfaces, retaining its public name and exposed body for compatibility.
-/

namespace BenderSuzuki.PFchapter1section1

universe u

/--
The right-conjugate `H^g = g⁻¹ H g`, matching the exponent convention in the
Peterfalvi text. The project-level `Subgroup.conjBy g` is left conjugation
`g H g⁻¹`, so right conjugation is `conjBy g⁻¹`.
-/
@[expose] public def rightConjugate {G : Type u} [Group G] (H : Subgroup G) (g : G) : Subgroup G :=
  H.conjBy g⁻¹


end BenderSuzuki.PFchapter1section1
