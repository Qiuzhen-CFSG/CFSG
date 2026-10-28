module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeChecks.Obstructions.CachedActions
import Mathlib.Tactic.FinCases

/-!
# Prime-order obstructions for Held representatives 64 through 255

For every nonlocal row, kernel reduction verifies a nontrivial prime orbit
of a word in the actual marked generators and representative. The orbit
lemma then constructs an element of that prime order in their generated
subgroup. The cached marked actions are proved equal to the originals.

Source: `../source/orbits.json`, generated from the unchanged ATLAS carrier
by `../source/search_orbits.py`. Emitted by `source/generate.py`; the generator
and JSON are not trusted proof inputs.
-/

namespace Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeVerification

set_option Elab.async false

set_option maxRecDepth 16000 in
private theorem obstruction_0064 : HasPrimeObstruction (representative 64) := by
  apply obstruction_of_cachedAction 64 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0065 : HasPrimeObstruction (representative 65) := by
  apply obstruction_of_cachedAction 65 [5, 3] 5 1
    (by decide) (by decide) (by decide) 18
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0066 : HasPrimeObstruction (representative 66) := by
  apply obstruction_of_cachedAction 66 [5, 1] 7 1
    (by decide) (by decide) (by decide) 19
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0067 : HasPrimeObstruction (representative 67) := by
  apply obstruction_of_cachedAction 67 [5, 2] 7 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0068 : HasPrimeObstruction (representative 68) := by
  apply obstruction_of_cachedAction 68 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0069 : HasPrimeObstruction (representative 69) := by
  apply obstruction_of_cachedAction 69 [5] 5 1
    (by decide) (by decide) (by decide) 6
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0070 : HasPrimeObstruction (representative 70) := by
  apply obstruction_of_cachedAction 70 [5, 4] 5 1
    (by decide) (by decide) (by decide) 11
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0071 : HasPrimeObstruction (representative 71) := by
  apply obstruction_of_cachedAction 71 [5, 4] 7 1
    (by decide) (by decide) (by decide) 108
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0077 : HasPrimeObstruction (representative 77) := by
  apply obstruction_of_cachedAction 77 [5, 1] 5 1
    (by decide) (by decide) (by decide) 26
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0078 : HasPrimeObstruction (representative 78) := by
  apply obstruction_of_cachedAction 78 [5, 2] 5 1
    (by decide) (by decide) (by decide) 10
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0079 : HasPrimeObstruction (representative 79) := by
  apply obstruction_of_cachedAction 79 [5, 3] 5 1
    (by decide) (by decide) (by decide) 28
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0080 : HasPrimeObstruction (representative 80) := by
  apply obstruction_of_cachedAction 80 [5] 5 1
    (by decide) (by decide) (by decide) 31
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0081 : HasPrimeObstruction (representative 81) := by
  apply obstruction_of_cachedAction 81 [5, 2] 7 1
    (by decide) (by decide) (by decide) 480
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0082 : HasPrimeObstruction (representative 82) := by
  apply obstruction_of_cachedAction 82 [5, 2] 5 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0083 : HasPrimeObstruction (representative 83) := by
  apply obstruction_of_cachedAction 83 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0084 : HasPrimeObstruction (representative 84) := by
  apply obstruction_of_cachedAction 84 [5] 7 1
    (by decide) (by decide) (by decide) 35
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0085 : HasPrimeObstruction (representative 85) := by
  apply obstruction_of_cachedAction 85 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0086 : HasPrimeObstruction (representative 86) := by
  apply obstruction_of_cachedAction 86 [5] 7 1
    (by decide) (by decide) (by decide) 85
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0087 : HasPrimeObstruction (representative 87) := by
  apply obstruction_of_cachedAction 87 [5, 1] 7 1
    (by decide) (by decide) (by decide) 11
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0088 : HasPrimeObstruction (representative 88) := by
  apply obstruction_of_cachedAction 88 [5, 4] 5 1
    (by decide) (by decide) (by decide) 91
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0089 : HasPrimeObstruction (representative 89) := by
  apply obstruction_of_cachedAction 89 [5] 7 1
    (by decide) (by decide) (by decide) 49
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0090 : HasPrimeObstruction (representative 90) := by
  apply obstruction_of_cachedAction 90 [5] 7 1
    (by decide) (by decide) (by decide) 31
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0091 : HasPrimeObstruction (representative 91) := by
  apply obstruction_of_cachedAction 91 [5, 4] 5 1
    (by decide) (by decide) (by decide) 35
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0092 : HasPrimeObstruction (representative 92) := by
  apply obstruction_of_cachedAction 92 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0093 : HasPrimeObstruction (representative 93) := by
  apply obstruction_of_cachedAction 93 [5] 7 1
    (by decide) (by decide) (by decide) 27
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0094 : HasPrimeObstruction (representative 94) := by
  apply obstruction_of_cachedAction 94 [5] 7 1
    (by decide) (by decide) (by decide) 194
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0095 : HasPrimeObstruction (representative 95) := by
  apply obstruction_of_cachedAction 95 [5] 5 1
    (by decide) (by decide) (by decide) 59
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0096 : HasPrimeObstruction (representative 96) := by
  apply obstruction_of_cachedAction 96 [5] 7 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0097 : HasPrimeObstruction (representative 97) := by
  apply obstruction_of_cachedAction 97 [5] 7 1
    (by decide) (by decide) (by decide) 39
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0098 : HasPrimeObstruction (representative 98) := by
  apply obstruction_of_cachedAction 98 [5, 3] 7 1
    (by decide) (by decide) (by decide) 114
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0099 : HasPrimeObstruction (representative 99) := by
  apply obstruction_of_cachedAction 99 [5] 5 1
    (by decide) (by decide) (by decide) 12
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0100 : HasPrimeObstruction (representative 100) := by
  apply obstruction_of_cachedAction 100 [5, 4] 5 1
    (by decide) (by decide) (by decide) 31
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0101 : HasPrimeObstruction (representative 101) := by
  apply obstruction_of_cachedAction 101 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0102 : HasPrimeObstruction (representative 102) := by
  apply obstruction_of_cachedAction 102 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0103 : HasPrimeObstruction (representative 103) := by
  apply obstruction_of_cachedAction 103 [5] 5 1
    (by decide) (by decide) (by decide) 24
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0104 : HasPrimeObstruction (representative 104) := by
  apply obstruction_of_cachedAction 104 [5, 1] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0105 : HasPrimeObstruction (representative 105) := by
  apply obstruction_of_cachedAction 105 [5] 5 1
    (by decide) (by decide) (by decide) 32
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0106 : HasPrimeObstruction (representative 106) := by
  apply obstruction_of_cachedAction 106 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0107 : HasPrimeObstruction (representative 107) := by
  apply obstruction_of_cachedAction 107 [5] 7 1
    (by decide) (by decide) (by decide) 8
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0108 : HasPrimeObstruction (representative 108) := by
  apply obstruction_of_cachedAction 108 [5] 5 1
    (by decide) (by decide) (by decide) 31
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0109 : HasPrimeObstruction (representative 109) := by
  apply obstruction_of_cachedAction 109 [5] 7 1
    (by decide) (by decide) (by decide) 8
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0110 : HasPrimeObstruction (representative 110) := by
  apply obstruction_of_cachedAction 110 [5] 7 1
    (by decide) (by decide) (by decide) 109
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0111 : HasPrimeObstruction (representative 111) := by
  apply obstruction_of_cachedAction 111 [5, 1] 5 1
    (by decide) (by decide) (by decide) 19
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0112 : HasPrimeObstruction (representative 112) := by
  apply obstruction_of_cachedAction 112 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0113 : HasPrimeObstruction (representative 113) := by
  apply obstruction_of_cachedAction 113 [5] 5 1
    (by decide) (by decide) (by decide) 18
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0114 : HasPrimeObstruction (representative 114) := by
  apply obstruction_of_cachedAction 114 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0115 : HasPrimeObstruction (representative 115) := by
  apply obstruction_of_cachedAction 115 [5, 1] 7 1
    (by decide) (by decide) (by decide) 190
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0116 : HasPrimeObstruction (representative 116) := by
  apply obstruction_of_cachedAction 116 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0117 : HasPrimeObstruction (representative 117) := by
  apply obstruction_of_cachedAction 117 [5] 5 1
    (by decide) (by decide) (by decide) 50
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0118 : HasPrimeObstruction (representative 118) := by
  apply obstruction_of_cachedAction 118 [5] 5 1
    (by decide) (by decide) (by decide) 47
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0119 : HasPrimeObstruction (representative 119) := by
  apply obstruction_of_cachedAction 119 [5, 3] 5 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0120 : HasPrimeObstruction (representative 120) := by
  apply obstruction_of_cachedAction 120 [5] 5 1
    (by decide) (by decide) (by decide) 11
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0121 : HasPrimeObstruction (representative 121) := by
  apply obstruction_of_cachedAction 121 [5, 2] 5 1
    (by decide) (by decide) (by decide) 16
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0122 : HasPrimeObstruction (representative 122) := by
  apply obstruction_of_cachedAction 122 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0123 : HasPrimeObstruction (representative 123) := by
  apply obstruction_of_cachedAction 123 [5] 5 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0124 : HasPrimeObstruction (representative 124) := by
  apply obstruction_of_cachedAction 124 [5, 2] 7 1
    (by decide) (by decide) (by decide) 61
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0125 : HasPrimeObstruction (representative 125) := by
  apply obstruction_of_cachedAction 125 [5] 7 1
    (by decide) (by decide) (by decide) 35
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0126 : HasPrimeObstruction (representative 126) := by
  apply obstruction_of_cachedAction 126 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0127 : HasPrimeObstruction (representative 127) := by
  apply obstruction_of_cachedAction 127 [5, 3] 5 1
    (by decide) (by decide) (by decide) 14
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0128 : HasPrimeObstruction (representative 128) := by
  apply obstruction_of_cachedAction 128 [5, 3] 5 1
    (by decide) (by decide) (by decide) 10
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0129 : HasPrimeObstruction (representative 129) := by
  apply obstruction_of_cachedAction 129 [5] 7 1
    (by decide) (by decide) (by decide) 17
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0130 : HasPrimeObstruction (representative 130) := by
  apply obstruction_of_cachedAction 130 [5] 7 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0131 : HasPrimeObstruction (representative 131) := by
  apply obstruction_of_cachedAction 131 [5] 5 1
    (by decide) (by decide) (by decide) 14
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0132 : HasPrimeObstruction (representative 132) := by
  apply obstruction_of_cachedAction 132 [5] 7 1
    (by decide) (by decide) (by decide) 14
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0133 : HasPrimeObstruction (representative 133) := by
  apply obstruction_of_cachedAction 133 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0134 : HasPrimeObstruction (representative 134) := by
  apply obstruction_of_cachedAction 134 [5, 2] 5 1
    (by decide) (by decide) (by decide) 18
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0135 : HasPrimeObstruction (representative 135) := by
  apply obstruction_of_cachedAction 135 [5] 5 1
    (by decide) (by decide) (by decide) 18
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0136 : HasPrimeObstruction (representative 136) := by
  apply obstruction_of_cachedAction 136 [5] 5 1
    (by decide) (by decide) (by decide) 14
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0137 : HasPrimeObstruction (representative 137) := by
  apply obstruction_of_cachedAction 137 [5, 2] 7 1
    (by decide) (by decide) (by decide) 44
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0138 : HasPrimeObstruction (representative 138) := by
  apply obstruction_of_cachedAction 138 [5] 7 1
    (by decide) (by decide) (by decide) 232
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0139 : HasPrimeObstruction (representative 139) := by
  apply obstruction_of_cachedAction 139 [5] 5 1
    (by decide) (by decide) (by decide) 39
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0140 : HasPrimeObstruction (representative 140) := by
  apply obstruction_of_cachedAction 140 [5, 3] 5 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0141 : HasPrimeObstruction (representative 141) := by
  apply obstruction_of_cachedAction 141 [5, 4] 5 1
    (by decide) (by decide) (by decide) 18
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0142 : HasPrimeObstruction (representative 142) := by
  apply obstruction_of_cachedAction 142 [5] 5 1
    (by decide) (by decide) (by decide) 3
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0143 : HasPrimeObstruction (representative 143) := by
  apply obstruction_of_cachedAction 143 [5] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0144 : HasPrimeObstruction (representative 144) := by
  apply obstruction_of_cachedAction 144 [5, 4] 5 1
    (by decide) (by decide) (by decide) 18
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0145 : HasPrimeObstruction (representative 145) := by
  apply obstruction_of_cachedAction 145 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0146 : HasPrimeObstruction (representative 146) := by
  apply obstruction_of_cachedAction 146 [5] 5 1
    (by decide) (by decide) (by decide) 32
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0147 : HasPrimeObstruction (representative 147) := by
  apply obstruction_of_cachedAction 147 [5] 7 1
    (by decide) (by decide) (by decide) 14
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0148 : HasPrimeObstruction (representative 148) := by
  apply obstruction_of_cachedAction 148 [5] 5 1
    (by decide) (by decide) (by decide) 13
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0149 : HasPrimeObstruction (representative 149) := by
  apply obstruction_of_cachedAction 149 [5, 2] 5 1
    (by decide) (by decide) (by decide) 100
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0150 : HasPrimeObstruction (representative 150) := by
  apply obstruction_of_cachedAction 150 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0151 : HasPrimeObstruction (representative 151) := by
  apply obstruction_of_cachedAction 151 [5] 7 1
    (by decide) (by decide) (by decide) 84
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0152 : HasPrimeObstruction (representative 152) := by
  apply obstruction_of_cachedAction 152 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0153 : HasPrimeObstruction (representative 153) := by
  apply obstruction_of_cachedAction 153 [5, 1] 5 1
    (by decide) (by decide) (by decide) 6
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0154 : HasPrimeObstruction (representative 154) := by
  apply obstruction_of_cachedAction 154 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0155 : HasPrimeObstruction (representative 155) := by
  apply obstruction_of_cachedAction 155 [5, 1] 5 1
    (by decide) (by decide) (by decide) 110
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0156 : HasPrimeObstruction (representative 156) := by
  apply obstruction_of_cachedAction 156 [5, 1, 5, 3, 4] 7 1
    (by decide) (by decide) (by decide) 38
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0157 : HasPrimeObstruction (representative 157) := by
  apply obstruction_of_cachedAction 157 [5, 2] 5 1
    (by decide) (by decide) (by decide) 13
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0158 : HasPrimeObstruction (representative 158) := by
  apply obstruction_of_cachedAction 158 [5, 1] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0159 : HasPrimeObstruction (representative 159) := by
  apply obstruction_of_cachedAction 159 [5, 2] 5 1
    (by decide) (by decide) (by decide) 36
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0160 : HasPrimeObstruction (representative 160) := by
  apply obstruction_of_cachedAction 160 [5] 5 1
    (by decide) (by decide) (by decide) 22
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0161 : HasPrimeObstruction (representative 161) := by
  apply obstruction_of_cachedAction 161 [5] 5 1
    (by decide) (by decide) (by decide) 5
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0162 : HasPrimeObstruction (representative 162) := by
  apply obstruction_of_cachedAction 162 [5] 5 1
    (by decide) (by decide) (by decide) 4
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0163 : HasPrimeObstruction (representative 163) := by
  apply obstruction_of_cachedAction 163 [5, 1] 7 1
    (by decide) (by decide) (by decide) 52
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0164 : HasPrimeObstruction (representative 164) := by
  apply obstruction_of_cachedAction 164 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0165 : HasPrimeObstruction (representative 165) := by
  apply obstruction_of_cachedAction 165 [5, 2] 5 1
    (by decide) (by decide) (by decide) 171
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0166 : HasPrimeObstruction (representative 166) := by
  apply obstruction_of_cachedAction 166 [5, 3] 5 1
    (by decide) (by decide) (by decide) 4
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0167 : HasPrimeObstruction (representative 167) := by
  apply obstruction_of_cachedAction 167 [5, 3] 5 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0168 : HasPrimeObstruction (representative 168) := by
  apply obstruction_of_cachedAction 168 [5] 7 1
    (by decide) (by decide) (by decide) 10
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0169 : HasPrimeObstruction (representative 169) := by
  apply obstruction_of_cachedAction 169 [5, 1] 7 1
    (by decide) (by decide) (by decide) 66
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0170 : HasPrimeObstruction (representative 170) := by
  apply obstruction_of_cachedAction 170 [5, 1] 5 1
    (by decide) (by decide) (by decide) 8
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0171 : HasPrimeObstruction (representative 171) := by
  apply obstruction_of_cachedAction 171 [5] 7 1
    (by decide) (by decide) (by decide) 4
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0172 : HasPrimeObstruction (representative 172) := by
  apply obstruction_of_cachedAction 172 [5] 7 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0173 : HasPrimeObstruction (representative 173) := by
  apply obstruction_of_cachedAction 173 [5, 1] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0174 : HasPrimeObstruction (representative 174) := by
  apply obstruction_of_cachedAction 174 [5] 7 1
    (by decide) (by decide) (by decide) 49
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0175 : HasPrimeObstruction (representative 175) := by
  apply obstruction_of_cachedAction 175 [5] 5 1
    (by decide) (by decide) (by decide) 4
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0176 : HasPrimeObstruction (representative 176) := by
  apply obstruction_of_cachedAction 176 [5] 7 1
    (by decide) (by decide) (by decide) 12
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0177 : HasPrimeObstruction (representative 177) := by
  apply obstruction_of_cachedAction 177 [5] 5 1
    (by decide) (by decide) (by decide) 31
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0178 : HasPrimeObstruction (representative 178) := by
  apply obstruction_of_cachedAction 178 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0179 : HasPrimeObstruction (representative 179) := by
  apply obstruction_of_cachedAction 179 [5] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0180 : HasPrimeObstruction (representative 180) := by
  apply obstruction_of_cachedAction 180 [5, 4] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0181 : HasPrimeObstruction (representative 181) := by
  apply obstruction_of_cachedAction 181 [5, 2] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0182 : HasPrimeObstruction (representative 182) := by
  apply obstruction_of_cachedAction 182 [5, 3] 5 1
    (by decide) (by decide) (by decide) 17
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0183 : HasPrimeObstruction (representative 183) := by
  apply obstruction_of_cachedAction 183 [5] 7 1
    (by decide) (by decide) (by decide) 46
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0184 : HasPrimeObstruction (representative 184) := by
  apply obstruction_of_cachedAction 184 [5] 5 1
    (by decide) (by decide) (by decide) 102
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0185 : HasPrimeObstruction (representative 185) := by
  apply obstruction_of_cachedAction 185 [5] 5 1
    (by decide) (by decide) (by decide) 11
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0186 : HasPrimeObstruction (representative 186) := by
  apply obstruction_of_cachedAction 186 [5] 7 1
    (by decide) (by decide) (by decide) 16
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0187 : HasPrimeObstruction (representative 187) := by
  apply obstruction_of_cachedAction 187 [5, 1] 7 1
    (by decide) (by decide) (by decide) 8
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0188 : HasPrimeObstruction (representative 188) := by
  apply obstruction_of_cachedAction 188 [5] 5 1
    (by decide) (by decide) (by decide) 57
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0189 : HasPrimeObstruction (representative 189) := by
  apply obstruction_of_cachedAction 189 [5, 2] 5 1
    (by decide) (by decide) (by decide) 4
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0190 : HasPrimeObstruction (representative 190) := by
  apply obstruction_of_cachedAction 190 [5, 3] 5 1
    (by decide) (by decide) (by decide) 27
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0191 : HasPrimeObstruction (representative 191) := by
  apply obstruction_of_cachedAction 191 [5] 5 1
    (by decide) (by decide) (by decide) 17
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0192 : HasPrimeObstruction (representative 192) := by
  apply obstruction_of_cachedAction 192 [5] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0193 : HasPrimeObstruction (representative 193) := by
  apply obstruction_of_cachedAction 193 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0194 : HasPrimeObstruction (representative 194) := by
  apply obstruction_of_cachedAction 194 [5, 4] 5 1
    (by decide) (by decide) (by decide) 31
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0195 : HasPrimeObstruction (representative 195) := by
  apply obstruction_of_cachedAction 195 [5, 2] 5 1
    (by decide) (by decide) (by decide) 8
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0196 : HasPrimeObstruction (representative 196) := by
  apply obstruction_of_cachedAction 196 [5] 5 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0197 : HasPrimeObstruction (representative 197) := by
  apply obstruction_of_cachedAction 197 [5] 7 1
    (by decide) (by decide) (by decide) 11
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0198 : HasPrimeObstruction (representative 198) := by
  apply obstruction_of_cachedAction 198 [5] 7 1
    (by decide) (by decide) (by decide) 178
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0199 : HasPrimeObstruction (representative 199) := by
  apply obstruction_of_cachedAction 199 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0200 : HasPrimeObstruction (representative 200) := by
  apply obstruction_of_cachedAction 200 [5] 5 1
    (by decide) (by decide) (by decide) 20
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0201 : HasPrimeObstruction (representative 201) := by
  apply obstruction_of_cachedAction 201 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0202 : HasPrimeObstruction (representative 202) := by
  apply obstruction_of_cachedAction 202 [5] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0203 : HasPrimeObstruction (representative 203) := by
  apply obstruction_of_cachedAction 203 [5] 5 1
    (by decide) (by decide) (by decide) 64
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0204 : HasPrimeObstruction (representative 204) := by
  apply obstruction_of_cachedAction 204 [5] 5 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0205 : HasPrimeObstruction (representative 205) := by
  apply obstruction_of_cachedAction 205 [5, 2] 5 1
    (by decide) (by decide) (by decide) 104
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0206 : HasPrimeObstruction (representative 206) := by
  apply obstruction_of_cachedAction 206 [5, 2] 5 1
    (by decide) (by decide) (by decide) 7
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0207 : HasPrimeObstruction (representative 207) := by
  apply obstruction_of_cachedAction 207 [5, 1] 5 1
    (by decide) (by decide) (by decide) 60
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0208 : HasPrimeObstruction (representative 208) := by
  apply obstruction_of_cachedAction 208 [5, 4] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0209 : HasPrimeObstruction (representative 209) := by
  apply obstruction_of_cachedAction 209 [5] 7 1
    (by decide) (by decide) (by decide) 6
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0210 : HasPrimeObstruction (representative 210) := by
  apply obstruction_of_cachedAction 210 [5] 5 1
    (by decide) (by decide) (by decide) 53
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0211 : HasPrimeObstruction (representative 211) := by
  apply obstruction_of_cachedAction 211 [5, 1] 5 1
    (by decide) (by decide) (by decide) 7
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0212 : HasPrimeObstruction (representative 212) := by
  apply obstruction_of_cachedAction 212 [5, 3] 5 1
    (by decide) (by decide) (by decide) 16
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0213 : HasPrimeObstruction (representative 213) := by
  apply obstruction_of_cachedAction 213 [5, 2] 5 1
    (by decide) (by decide) (by decide) 8
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0214 : HasPrimeObstruction (representative 214) := by
  apply obstruction_of_cachedAction 214 [5] 7 1
    (by decide) (by decide) (by decide) 10
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0215 : HasPrimeObstruction (representative 215) := by
  apply obstruction_of_cachedAction 215 [5] 7 1
    (by decide) (by decide) (by decide) 17
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0216 : HasPrimeObstruction (representative 216) := by
  apply obstruction_of_cachedAction 216 [5] 5 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0217 : HasPrimeObstruction (representative 217) := by
  apply obstruction_of_cachedAction 217 [5] 7 1
    (by decide) (by decide) (by decide) 32
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0218 : HasPrimeObstruction (representative 218) := by
  apply obstruction_of_cachedAction 218 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0219 : HasPrimeObstruction (representative 219) := by
  apply obstruction_of_cachedAction 219 [5, 2] 5 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0220 : HasPrimeObstruction (representative 220) := by
  apply obstruction_of_cachedAction 220 [5] 7 1
    (by decide) (by decide) (by decide) 53
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0221 : HasPrimeObstruction (representative 221) := by
  apply obstruction_of_cachedAction 221 [5] 7 1
    (by decide) (by decide) (by decide) 9
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0222 : HasPrimeObstruction (representative 222) := by
  apply obstruction_of_cachedAction 222 [5] 7 1
    (by decide) (by decide) (by decide) 38
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0223 : HasPrimeObstruction (representative 223) := by
  apply obstruction_of_cachedAction 223 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0224 : HasPrimeObstruction (representative 224) := by
  apply obstruction_of_cachedAction 224 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0225 : HasPrimeObstruction (representative 225) := by
  apply obstruction_of_cachedAction 225 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0226 : HasPrimeObstruction (representative 226) := by
  apply obstruction_of_cachedAction 226 [5] 7 1
    (by decide) (by decide) (by decide) 65
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0227 : HasPrimeObstruction (representative 227) := by
  apply obstruction_of_cachedAction 227 [5] 5 1
    (by decide) (by decide) (by decide) 10
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0228 : HasPrimeObstruction (representative 228) := by
  apply obstruction_of_cachedAction 228 [5] 7 1
    (by decide) (by decide) (by decide) 34
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0229 : HasPrimeObstruction (representative 229) := by
  apply obstruction_of_cachedAction 229 [5, 1] 5 1
    (by decide) (by decide) (by decide) 34
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0230 : HasPrimeObstruction (representative 230) := by
  apply obstruction_of_cachedAction 230 [5] 7 1
    (by decide) (by decide) (by decide) 27
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0231 : HasPrimeObstruction (representative 231) := by
  apply obstruction_of_cachedAction 231 [5, 1] 5 1
    (by decide) (by decide) (by decide) 123
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0232 : HasPrimeObstruction (representative 232) := by
  apply obstruction_of_cachedAction 232 [5, 2] 5 1
    (by decide) (by decide) (by decide) 21
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0233 : HasPrimeObstruction (representative 233) := by
  apply obstruction_of_cachedAction 233 [5, 3] 5 1
    (by decide) (by decide) (by decide) 6
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0234 : HasPrimeObstruction (representative 234) := by
  apply obstruction_of_cachedAction 234 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0235 : HasPrimeObstruction (representative 235) := by
  apply obstruction_of_cachedAction 235 [5] 7 1
    (by decide) (by decide) (by decide) 3
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0236 : HasPrimeObstruction (representative 236) := by
  apply obstruction_of_cachedAction 236 [5] 5 1
    (by decide) (by decide) (by decide) 44
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0237 : HasPrimeObstruction (representative 237) := by
  apply obstruction_of_cachedAction 237 [5, 1] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0238 : HasPrimeObstruction (representative 238) := by
  apply obstruction_of_cachedAction 238 [5, 2] 5 1
    (by decide) (by decide) (by decide) 16
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0239 : HasPrimeObstruction (representative 239) := by
  apply obstruction_of_cachedAction 239 [5, 4] 5 1
    (by decide) (by decide) (by decide) 14
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0240 : HasPrimeObstruction (representative 240) := by
  apply obstruction_of_cachedAction 240 [5, 1] 5 1
    (by decide) (by decide) (by decide) 171
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0241 : HasPrimeObstruction (representative 241) := by
  apply obstruction_of_cachedAction 241 [5, 1] 7 1
    (by decide) (by decide) (by decide) 73
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0242 : HasPrimeObstruction (representative 242) := by
  apply obstruction_of_cachedAction 242 [5, 1] 5 1
    (by decide) (by decide) (by decide) 12
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0243 : HasPrimeObstruction (representative 243) := by
  apply obstruction_of_cachedAction 243 [5] 7 1
    (by decide) (by decide) (by decide) 138
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0244 : HasPrimeObstruction (representative 244) := by
  apply obstruction_of_cachedAction 244 [5] 7 1
    (by decide) (by decide) (by decide) 16
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0245 : HasPrimeObstruction (representative 245) := by
  apply obstruction_of_cachedAction 245 [5, 2] 5 1
    (by decide) (by decide) (by decide) 43
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0246 : HasPrimeObstruction (representative 246) := by
  apply obstruction_of_cachedAction 246 [5] 7 1
    (by decide) (by decide) (by decide) 55
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0247 : HasPrimeObstruction (representative 247) := by
  apply obstruction_of_cachedAction 247 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0248 : HasPrimeObstruction (representative 248) := by
  apply obstruction_of_cachedAction 248 [5, 1] 7 1
    (by decide) (by decide) (by decide) 119
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0249 : HasPrimeObstruction (representative 249) := by
  apply obstruction_of_cachedAction 249 [5, 2] 5 1
    (by decide) (by decide) (by decide) 11
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0250 : HasPrimeObstruction (representative 250) := by
  apply obstruction_of_cachedAction 250 [5, 1] 5 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0251 : HasPrimeObstruction (representative 251) := by
  apply obstruction_of_cachedAction 251 [5] 5 1
    (by decide) (by decide) (by decide) 31
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0252 : HasPrimeObstruction (representative 252) := by
  apply obstruction_of_cachedAction 252 [5] 7 1
    (by decide) (by decide) (by decide) 4
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0253 : HasPrimeObstruction (representative 253) := by
  apply obstruction_of_cachedAction 253 [5] 7 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0254 : HasPrimeObstruction (representative 254) := by
  apply obstruction_of_cachedAction 254 [5, 3] 5 1
    (by decide) (by decide) (by decide) 51
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_0255 : HasPrimeObstruction (representative 255) := by
  apply obstruction_of_cachedAction 255 [5] 5 1
    (by decide) (by decide) (by decide) 11
  · decide +kernel
  · decide +kernel

/-- Every nonlocal representative in this interval has a forbidden prime order. -/
public theorem obstruction_block00_from64 (j : Fin 192)
    (h : localBranch ⟨64 + j.val, by omega⟩ = none) :
    HasPrimeObstruction (representative ⟨64 + j.val, by omega⟩) := by
  fin_cases j
  · exact obstruction_0064
  · exact obstruction_0065
  · exact obstruction_0066
  · exact obstruction_0067
  · exact obstruction_0068
  · exact obstruction_0069
  · exact obstruction_0070
  · exact obstruction_0071
  · simp [localBranch] at h
  · simp [localBranch] at h
  · simp [localBranch] at h
  · simp [localBranch] at h
  · simp [localBranch] at h
  · exact obstruction_0077
  · exact obstruction_0078
  · exact obstruction_0079
  · exact obstruction_0080
  · exact obstruction_0081
  · exact obstruction_0082
  · exact obstruction_0083
  · exact obstruction_0084
  · exact obstruction_0085
  · exact obstruction_0086
  · exact obstruction_0087
  · exact obstruction_0088
  · exact obstruction_0089
  · exact obstruction_0090
  · exact obstruction_0091
  · exact obstruction_0092
  · exact obstruction_0093
  · exact obstruction_0094
  · exact obstruction_0095
  · exact obstruction_0096
  · exact obstruction_0097
  · exact obstruction_0098
  · exact obstruction_0099
  · exact obstruction_0100
  · exact obstruction_0101
  · exact obstruction_0102
  · exact obstruction_0103
  · exact obstruction_0104
  · exact obstruction_0105
  · exact obstruction_0106
  · exact obstruction_0107
  · exact obstruction_0108
  · exact obstruction_0109
  · exact obstruction_0110
  · exact obstruction_0111
  · exact obstruction_0112
  · exact obstruction_0113
  · exact obstruction_0114
  · exact obstruction_0115
  · exact obstruction_0116
  · exact obstruction_0117
  · exact obstruction_0118
  · exact obstruction_0119
  · exact obstruction_0120
  · exact obstruction_0121
  · exact obstruction_0122
  · exact obstruction_0123
  · exact obstruction_0124
  · exact obstruction_0125
  · exact obstruction_0126
  · exact obstruction_0127
  · exact obstruction_0128
  · exact obstruction_0129
  · exact obstruction_0130
  · exact obstruction_0131
  · exact obstruction_0132
  · exact obstruction_0133
  · exact obstruction_0134
  · exact obstruction_0135
  · exact obstruction_0136
  · exact obstruction_0137
  · exact obstruction_0138
  · exact obstruction_0139
  · exact obstruction_0140
  · exact obstruction_0141
  · exact obstruction_0142
  · exact obstruction_0143
  · exact obstruction_0144
  · exact obstruction_0145
  · exact obstruction_0146
  · exact obstruction_0147
  · exact obstruction_0148
  · exact obstruction_0149
  · exact obstruction_0150
  · exact obstruction_0151
  · exact obstruction_0152
  · exact obstruction_0153
  · exact obstruction_0154
  · exact obstruction_0155
  · exact obstruction_0156
  · exact obstruction_0157
  · exact obstruction_0158
  · exact obstruction_0159
  · exact obstruction_0160
  · exact obstruction_0161
  · exact obstruction_0162
  · exact obstruction_0163
  · exact obstruction_0164
  · exact obstruction_0165
  · exact obstruction_0166
  · exact obstruction_0167
  · exact obstruction_0168
  · exact obstruction_0169
  · exact obstruction_0170
  · exact obstruction_0171
  · exact obstruction_0172
  · exact obstruction_0173
  · exact obstruction_0174
  · exact obstruction_0175
  · exact obstruction_0176
  · exact obstruction_0177
  · exact obstruction_0178
  · exact obstruction_0179
  · exact obstruction_0180
  · exact obstruction_0181
  · exact obstruction_0182
  · exact obstruction_0183
  · exact obstruction_0184
  · exact obstruction_0185
  · exact obstruction_0186
  · exact obstruction_0187
  · exact obstruction_0188
  · exact obstruction_0189
  · exact obstruction_0190
  · exact obstruction_0191
  · exact obstruction_0192
  · exact obstruction_0193
  · exact obstruction_0194
  · exact obstruction_0195
  · exact obstruction_0196
  · exact obstruction_0197
  · exact obstruction_0198
  · exact obstruction_0199
  · exact obstruction_0200
  · exact obstruction_0201
  · exact obstruction_0202
  · exact obstruction_0203
  · exact obstruction_0204
  · exact obstruction_0205
  · exact obstruction_0206
  · exact obstruction_0207
  · exact obstruction_0208
  · exact obstruction_0209
  · exact obstruction_0210
  · exact obstruction_0211
  · exact obstruction_0212
  · exact obstruction_0213
  · exact obstruction_0214
  · exact obstruction_0215
  · exact obstruction_0216
  · exact obstruction_0217
  · exact obstruction_0218
  · exact obstruction_0219
  · exact obstruction_0220
  · exact obstruction_0221
  · exact obstruction_0222
  · exact obstruction_0223
  · exact obstruction_0224
  · exact obstruction_0225
  · exact obstruction_0226
  · exact obstruction_0227
  · exact obstruction_0228
  · exact obstruction_0229
  · exact obstruction_0230
  · exact obstruction_0231
  · exact obstruction_0232
  · exact obstruction_0233
  · exact obstruction_0234
  · exact obstruction_0235
  · exact obstruction_0236
  · exact obstruction_0237
  · exact obstruction_0238
  · exact obstruction_0239
  · exact obstruction_0240
  · exact obstruction_0241
  · exact obstruction_0242
  · exact obstruction_0243
  · exact obstruction_0244
  · exact obstruction_0245
  · exact obstruction_0246
  · exact obstruction_0247
  · exact obstruction_0248
  · exact obstruction_0249
  · exact obstruction_0250
  · exact obstruction_0251
  · exact obstruction_0252
  · exact obstruction_0253
  · exact obstruction_0254
  · exact obstruction_0255

end Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeVerification
