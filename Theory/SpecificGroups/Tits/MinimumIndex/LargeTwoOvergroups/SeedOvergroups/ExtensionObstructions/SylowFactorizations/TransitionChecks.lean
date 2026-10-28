module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.Transitions

/-!
# Kernel checks for the shared Sylow transitions

The 5,940 distinct transitions are checked on the certified base 0, 1, 2.
Blocks of 64 bound the size of each kernel reduction.

Source: Parrott (1972), section 5, p.683; the candidate JSON in
`ExtensionObstructions/source/`. Reproduce with `source/generate.py`.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizationCertificate

private theorem transition_check_000 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 0 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_001 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 1 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_002 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 2 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_003 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 3 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_004 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 4 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_005 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 5 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_006 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 6 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_007 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 7 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_008 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 8 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_009 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 9 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_010 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 10 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_011 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 11 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_012 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 12 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_013 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 13 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_014 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 14 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_015 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 15 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_016 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 16 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_017 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 17 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_018 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 18 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_019 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 19 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_020 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 20 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_021 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 21 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_022 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 22 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_023 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 23 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_024 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 24 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_025 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 25 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_026 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 26 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_027 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 27 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_028 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 28 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_029 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 29 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_030 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 30 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_031 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 31 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_032 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 32 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_033 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 33 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_034 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 34 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_035 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 35 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_036 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 36 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_037 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 37 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_038 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 38 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_039 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 39 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_040 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 40 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_041 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 41 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_042 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 42 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_043 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 43 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_044 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 44 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_045 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 45 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_046 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 46 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_047 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 47 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_048 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 48 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_049 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 49 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_050 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 50 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_051 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 51 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_052 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 52 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_053 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 53 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_054 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 54 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_055 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 55 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_056 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 56 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_057 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 57 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_058 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 58 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_059 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 59 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_060 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 60 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_061 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 61 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_062 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 62 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_063 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 63 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_064 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 64 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_065 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 65 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_066 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 66 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_067 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 67 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_068 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 68 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_069 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 69 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_070 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 70 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_071 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 71 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_072 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 72 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_073 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 73 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_074 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 74 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_075 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 75 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_076 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 76 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_077 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 77 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_078 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 78 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_079 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 79 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_080 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 80 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_081 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 81 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_082 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 82 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_083 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 83 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_084 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 84 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_085 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 85 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_086 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 86 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_087 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 87 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_088 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 88 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_089 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 89 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_090 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 90 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_091 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 91 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem transition_check_092 : ∀ j : Fin 64,
    transitionTest (transitionCode (transitionIndex 92 j)) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

theorem transition_checks (k : Fin 5940) : transitionTest (transitionCode k) = true := by
  have rows (b : Fin 93) : ∀ j : Fin 64,
      transitionTest (transitionCode (transitionIndex b j)) = true := by
    fin_cases b
    · exact transition_check_000
    · exact transition_check_001
    · exact transition_check_002
    · exact transition_check_003
    · exact transition_check_004
    · exact transition_check_005
    · exact transition_check_006
    · exact transition_check_007
    · exact transition_check_008
    · exact transition_check_009
    · exact transition_check_010
    · exact transition_check_011
    · exact transition_check_012
    · exact transition_check_013
    · exact transition_check_014
    · exact transition_check_015
    · exact transition_check_016
    · exact transition_check_017
    · exact transition_check_018
    · exact transition_check_019
    · exact transition_check_020
    · exact transition_check_021
    · exact transition_check_022
    · exact transition_check_023
    · exact transition_check_024
    · exact transition_check_025
    · exact transition_check_026
    · exact transition_check_027
    · exact transition_check_028
    · exact transition_check_029
    · exact transition_check_030
    · exact transition_check_031
    · exact transition_check_032
    · exact transition_check_033
    · exact transition_check_034
    · exact transition_check_035
    · exact transition_check_036
    · exact transition_check_037
    · exact transition_check_038
    · exact transition_check_039
    · exact transition_check_040
    · exact transition_check_041
    · exact transition_check_042
    · exact transition_check_043
    · exact transition_check_044
    · exact transition_check_045
    · exact transition_check_046
    · exact transition_check_047
    · exact transition_check_048
    · exact transition_check_049
    · exact transition_check_050
    · exact transition_check_051
    · exact transition_check_052
    · exact transition_check_053
    · exact transition_check_054
    · exact transition_check_055
    · exact transition_check_056
    · exact transition_check_057
    · exact transition_check_058
    · exact transition_check_059
    · exact transition_check_060
    · exact transition_check_061
    · exact transition_check_062
    · exact transition_check_063
    · exact transition_check_064
    · exact transition_check_065
    · exact transition_check_066
    · exact transition_check_067
    · exact transition_check_068
    · exact transition_check_069
    · exact transition_check_070
    · exact transition_check_071
    · exact transition_check_072
    · exact transition_check_073
    · exact transition_check_074
    · exact transition_check_075
    · exact transition_check_076
    · exact transition_check_077
    · exact transition_check_078
    · exact transition_check_079
    · exact transition_check_080
    · exact transition_check_081
    · exact transition_check_082
    · exact transition_check_083
    · exact transition_check_084
    · exact transition_check_085
    · exact transition_check_086
    · exact transition_check_087
    · exact transition_check_088
    · exact transition_check_089
    · exact transition_check_090
    · exact transition_check_091
    · exact transition_check_092
  have he : transitionIndex ⟨k.val / 64, by omega⟩ ⟨k.val % 64, Nat.mod_lt _ (by decide)⟩ = k := by
    apply Fin.ext
    simp only [transitionIndex]
    omega
  exact he ▸ rows _ _

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizationCertificate
