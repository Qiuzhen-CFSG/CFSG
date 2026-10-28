module

public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max4.Checks00
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max4.Checks01
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max4.Checks02
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max4.Checks03
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max4.Checks04

import Mathlib.Tactic.FinCases

/-!
# All max4 right-coset transitions

The bounded slices cover every stored right-coset representative and
both ambient generators. `Base` converts these checks into group coverage.
Source: primary ATLAS Tits max4/max8 programs and the fixed words in
`FiveOvergroups/Representatives`. See `DoubleCosetCover/source/` for generation.
-/

namespace Tits.MinimumIndexFiveOvergroups.DoubleCosetCertificate.Max4

public theorem transitions_checked (r : Fin 2304) (g : Fin 2) :
    test genMaps repMaps nodes steps r g = true := by
  have h : ∀ r : Fin 2304, ∀ g : Fin 2, test genMaps repMaps nodes steps r g = true := by
    apply all_of_blocks (n := 2304) (k := 128) (b := 18) (by decide)
    intro block
    fin_cases block
    · exact check0
    · exact check1
    · exact check2
    · exact check3
    · exact check4
    · exact check5
    · exact check6
    · exact check7
    · exact check8
    · exact check9
    · exact check10
    · exact check11
    · exact check12
    · exact check13
    · exact check14
    · exact check15
    · exact check16
    · exact check17
  exact h r g

end Tits.MinimumIndexFiveOvergroups.DoubleCosetCertificate.Max4
