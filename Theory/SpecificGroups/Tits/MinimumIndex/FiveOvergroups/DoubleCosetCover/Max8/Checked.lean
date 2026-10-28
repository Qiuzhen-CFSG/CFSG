module

public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max8.Checks00
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max8.Checks01
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max8.Checks02
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max8.Checks03
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max8.Checks04
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max8.Checks05
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max8.Checks06
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max8.Checks07
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max8.Checks08
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max8.Checks09
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max8.Checks10
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max8.Checks11
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max8.Checks12
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max8.Checks13
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max8.Checks14
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max8.Checks15
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max8.Checks16
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max8.Checks17
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max8.Checks18
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max8.Checks19
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max8.Checks20
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max8.Checks21
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max8.Checks22
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max8.Checks23
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max8.Checks24
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max8.Checks25
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max8.Checks26
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max8.Checks27
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max8.Checks28
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max8.Checks29

import Mathlib.Tactic.FinCases

/-!
# All max8 right-coset transitions

The bounded slices cover every stored right-coset representative and
both ambient generators. `Base` converts these checks into group coverage.
Source: primary ATLAS Tits max4/max8 programs and the fixed words in
`FiveOvergroups/Representatives`. See `DoubleCosetCover/source/` for generation.
-/

namespace Tits.MinimumIndexFiveOvergroups.DoubleCosetCertificate.Max8

public theorem transitions_checked (r : Fin 14976) (g : Fin 2) :
    test genMaps repMaps nodes steps r g = true := by
  have h : ∀ r : Fin 14976, ∀ g : Fin 2, test genMaps repMaps nodes steps r g = true := by
    apply all_of_blocks (n := 14976) (k := 128) (b := 117) (by decide)
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
    · exact check18
    · exact check19
    · exact check20
    · exact check21
    · exact check22
    · exact check23
    · exact check24
    · exact check25
    · exact check26
    · exact check27
    · exact check28
    · exact check29
    · exact check30
    · exact check31
    · exact check32
    · exact check33
    · exact check34
    · exact check35
    · exact check36
    · exact check37
    · exact check38
    · exact check39
    · exact check40
    · exact check41
    · exact check42
    · exact check43
    · exact check44
    · exact check45
    · exact check46
    · exact check47
    · exact check48
    · exact check49
    · exact check50
    · exact check51
    · exact check52
    · exact check53
    · exact check54
    · exact check55
    · exact check56
    · exact check57
    · exact check58
    · exact check59
    · exact check60
    · exact check61
    · exact check62
    · exact check63
    · exact check64
    · exact check65
    · exact check66
    · exact check67
    · exact check68
    · exact check69
    · exact check70
    · exact check71
    · exact check72
    · exact check73
    · exact check74
    · exact check75
    · exact check76
    · exact check77
    · exact check78
    · exact check79
    · exact check80
    · exact check81
    · exact check82
    · exact check83
    · exact check84
    · exact check85
    · exact check86
    · exact check87
    · exact check88
    · exact check89
    · exact check90
    · exact check91
    · exact check92
    · exact check93
    · exact check94
    · exact check95
    · exact check96
    · exact check97
    · exact check98
    · exact check99
    · exact check100
    · exact check101
    · exact check102
    · exact check103
    · exact check104
    · exact check105
    · exact check106
    · exact check107
    · exact check108
    · exact check109
    · exact check110
    · exact check111
    · exact check112
    · exact check113
    · exact check114
    · exact check115
    · exact check116
  exact h r g

end Tits.MinimumIndexFiveOvergroups.DoubleCosetCertificate.Max8
