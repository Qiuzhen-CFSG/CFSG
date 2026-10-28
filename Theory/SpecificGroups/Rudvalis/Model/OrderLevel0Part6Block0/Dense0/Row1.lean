module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.FactorMaps
import Mathlib.Tactic.FinCases

/-!
# Rudvalis block-0 dense row 1

Certify transition (0, 552) on all 4060 points using 203 slices of
twenty points and the certified factor cache. Representative-word witnesses
come from the saved PreparedDrafts/Batch3.lean; their decoding is checked below
against OrderLevel0Data. Source: the ATLAS witnesses in FactorWords.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.Dense0.Row1
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 1600000

@[expose] public def w : List (Fin 4) := [3, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0]

@[expose] public def v : List (Fin 4) := [1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0]

private theorem slice0 : FactorMaps.slice 1 w v 0 = true := by
  decide +kernel

private theorem slice1 : FactorMaps.slice 1 w v 1 = true := by
  decide +kernel

private theorem slice2 : FactorMaps.slice 1 w v 2 = true := by
  decide +kernel

private theorem slice3 : FactorMaps.slice 1 w v 3 = true := by
  decide +kernel

private theorem slice4 : FactorMaps.slice 1 w v 4 = true := by
  decide +kernel

private theorem slice5 : FactorMaps.slice 1 w v 5 = true := by
  decide +kernel

private theorem slice6 : FactorMaps.slice 1 w v 6 = true := by
  decide +kernel

private theorem slice7 : FactorMaps.slice 1 w v 7 = true := by
  decide +kernel

private theorem slice8 : FactorMaps.slice 1 w v 8 = true := by
  decide +kernel

private theorem slice9 : FactorMaps.slice 1 w v 9 = true := by
  decide +kernel

private theorem slice10 : FactorMaps.slice 1 w v 10 = true := by
  decide +kernel

private theorem slice11 : FactorMaps.slice 1 w v 11 = true := by
  decide +kernel

private theorem slice12 : FactorMaps.slice 1 w v 12 = true := by
  decide +kernel

private theorem slice13 : FactorMaps.slice 1 w v 13 = true := by
  decide +kernel

private theorem slice14 : FactorMaps.slice 1 w v 14 = true := by
  decide +kernel

private theorem slice15 : FactorMaps.slice 1 w v 15 = true := by
  decide +kernel

private theorem slice16 : FactorMaps.slice 1 w v 16 = true := by
  decide +kernel

private theorem slice17 : FactorMaps.slice 1 w v 17 = true := by
  decide +kernel

private theorem slice18 : FactorMaps.slice 1 w v 18 = true := by
  decide +kernel

private theorem slice19 : FactorMaps.slice 1 w v 19 = true := by
  decide +kernel

private theorem slice20 : FactorMaps.slice 1 w v 20 = true := by
  decide +kernel

private theorem slice21 : FactorMaps.slice 1 w v 21 = true := by
  decide +kernel

private theorem slice22 : FactorMaps.slice 1 w v 22 = true := by
  decide +kernel

private theorem slice23 : FactorMaps.slice 1 w v 23 = true := by
  decide +kernel

private theorem slice24 : FactorMaps.slice 1 w v 24 = true := by
  decide +kernel

private theorem slice25 : FactorMaps.slice 1 w v 25 = true := by
  decide +kernel

private theorem slice26 : FactorMaps.slice 1 w v 26 = true := by
  decide +kernel

private theorem slice27 : FactorMaps.slice 1 w v 27 = true := by
  decide +kernel

private theorem slice28 : FactorMaps.slice 1 w v 28 = true := by
  decide +kernel

private theorem slice29 : FactorMaps.slice 1 w v 29 = true := by
  decide +kernel

private theorem slice30 : FactorMaps.slice 1 w v 30 = true := by
  decide +kernel

private theorem slice31 : FactorMaps.slice 1 w v 31 = true := by
  decide +kernel

private theorem slice32 : FactorMaps.slice 1 w v 32 = true := by
  decide +kernel

private theorem slice33 : FactorMaps.slice 1 w v 33 = true := by
  decide +kernel

private theorem slice34 : FactorMaps.slice 1 w v 34 = true := by
  decide +kernel

private theorem slice35 : FactorMaps.slice 1 w v 35 = true := by
  decide +kernel

private theorem slice36 : FactorMaps.slice 1 w v 36 = true := by
  decide +kernel

private theorem slice37 : FactorMaps.slice 1 w v 37 = true := by
  decide +kernel

private theorem slice38 : FactorMaps.slice 1 w v 38 = true := by
  decide +kernel

private theorem slice39 : FactorMaps.slice 1 w v 39 = true := by
  decide +kernel

private theorem slice40 : FactorMaps.slice 1 w v 40 = true := by
  decide +kernel

private theorem slice41 : FactorMaps.slice 1 w v 41 = true := by
  decide +kernel

private theorem slice42 : FactorMaps.slice 1 w v 42 = true := by
  decide +kernel

private theorem slice43 : FactorMaps.slice 1 w v 43 = true := by
  decide +kernel

private theorem slice44 : FactorMaps.slice 1 w v 44 = true := by
  decide +kernel

private theorem slice45 : FactorMaps.slice 1 w v 45 = true := by
  decide +kernel

private theorem slice46 : FactorMaps.slice 1 w v 46 = true := by
  decide +kernel

private theorem slice47 : FactorMaps.slice 1 w v 47 = true := by
  decide +kernel

private theorem slice48 : FactorMaps.slice 1 w v 48 = true := by
  decide +kernel

private theorem slice49 : FactorMaps.slice 1 w v 49 = true := by
  decide +kernel

private theorem slice50 : FactorMaps.slice 1 w v 50 = true := by
  decide +kernel

private theorem slice51 : FactorMaps.slice 1 w v 51 = true := by
  decide +kernel

private theorem slice52 : FactorMaps.slice 1 w v 52 = true := by
  decide +kernel

private theorem slice53 : FactorMaps.slice 1 w v 53 = true := by
  decide +kernel

private theorem slice54 : FactorMaps.slice 1 w v 54 = true := by
  decide +kernel

private theorem slice55 : FactorMaps.slice 1 w v 55 = true := by
  decide +kernel

private theorem slice56 : FactorMaps.slice 1 w v 56 = true := by
  decide +kernel

private theorem slice57 : FactorMaps.slice 1 w v 57 = true := by
  decide +kernel

private theorem slice58 : FactorMaps.slice 1 w v 58 = true := by
  decide +kernel

private theorem slice59 : FactorMaps.slice 1 w v 59 = true := by
  decide +kernel

private theorem slice60 : FactorMaps.slice 1 w v 60 = true := by
  decide +kernel

private theorem slice61 : FactorMaps.slice 1 w v 61 = true := by
  decide +kernel

private theorem slice62 : FactorMaps.slice 1 w v 62 = true := by
  decide +kernel

private theorem slice63 : FactorMaps.slice 1 w v 63 = true := by
  decide +kernel

private theorem slice64 : FactorMaps.slice 1 w v 64 = true := by
  decide +kernel

private theorem slice65 : FactorMaps.slice 1 w v 65 = true := by
  decide +kernel

private theorem slice66 : FactorMaps.slice 1 w v 66 = true := by
  decide +kernel

private theorem slice67 : FactorMaps.slice 1 w v 67 = true := by
  decide +kernel

private theorem slice68 : FactorMaps.slice 1 w v 68 = true := by
  decide +kernel

private theorem slice69 : FactorMaps.slice 1 w v 69 = true := by
  decide +kernel

private theorem slice70 : FactorMaps.slice 1 w v 70 = true := by
  decide +kernel

private theorem slice71 : FactorMaps.slice 1 w v 71 = true := by
  decide +kernel

private theorem slice72 : FactorMaps.slice 1 w v 72 = true := by
  decide +kernel

private theorem slice73 : FactorMaps.slice 1 w v 73 = true := by
  decide +kernel

private theorem slice74 : FactorMaps.slice 1 w v 74 = true := by
  decide +kernel

private theorem slice75 : FactorMaps.slice 1 w v 75 = true := by
  decide +kernel

private theorem slice76 : FactorMaps.slice 1 w v 76 = true := by
  decide +kernel

private theorem slice77 : FactorMaps.slice 1 w v 77 = true := by
  decide +kernel

private theorem slice78 : FactorMaps.slice 1 w v 78 = true := by
  decide +kernel

private theorem slice79 : FactorMaps.slice 1 w v 79 = true := by
  decide +kernel

private theorem slice80 : FactorMaps.slice 1 w v 80 = true := by
  decide +kernel

private theorem slice81 : FactorMaps.slice 1 w v 81 = true := by
  decide +kernel

private theorem slice82 : FactorMaps.slice 1 w v 82 = true := by
  decide +kernel

private theorem slice83 : FactorMaps.slice 1 w v 83 = true := by
  decide +kernel

private theorem slice84 : FactorMaps.slice 1 w v 84 = true := by
  decide +kernel

private theorem slice85 : FactorMaps.slice 1 w v 85 = true := by
  decide +kernel

private theorem slice86 : FactorMaps.slice 1 w v 86 = true := by
  decide +kernel

private theorem slice87 : FactorMaps.slice 1 w v 87 = true := by
  decide +kernel

private theorem slice88 : FactorMaps.slice 1 w v 88 = true := by
  decide +kernel

private theorem slice89 : FactorMaps.slice 1 w v 89 = true := by
  decide +kernel

private theorem slice90 : FactorMaps.slice 1 w v 90 = true := by
  decide +kernel

private theorem slice91 : FactorMaps.slice 1 w v 91 = true := by
  decide +kernel

private theorem slice92 : FactorMaps.slice 1 w v 92 = true := by
  decide +kernel

private theorem slice93 : FactorMaps.slice 1 w v 93 = true := by
  decide +kernel

private theorem slice94 : FactorMaps.slice 1 w v 94 = true := by
  decide +kernel

private theorem slice95 : FactorMaps.slice 1 w v 95 = true := by
  decide +kernel

private theorem slice96 : FactorMaps.slice 1 w v 96 = true := by
  decide +kernel

private theorem slice97 : FactorMaps.slice 1 w v 97 = true := by
  decide +kernel

private theorem slice98 : FactorMaps.slice 1 w v 98 = true := by
  decide +kernel

private theorem slice99 : FactorMaps.slice 1 w v 99 = true := by
  decide +kernel

private theorem slice100 : FactorMaps.slice 1 w v 100 = true := by
  decide +kernel

private theorem slice101 : FactorMaps.slice 1 w v 101 = true := by
  decide +kernel

private theorem slice102 : FactorMaps.slice 1 w v 102 = true := by
  decide +kernel

private theorem slice103 : FactorMaps.slice 1 w v 103 = true := by
  decide +kernel

private theorem slice104 : FactorMaps.slice 1 w v 104 = true := by
  decide +kernel

private theorem slice105 : FactorMaps.slice 1 w v 105 = true := by
  decide +kernel

private theorem slice106 : FactorMaps.slice 1 w v 106 = true := by
  decide +kernel

private theorem slice107 : FactorMaps.slice 1 w v 107 = true := by
  decide +kernel

private theorem slice108 : FactorMaps.slice 1 w v 108 = true := by
  decide +kernel

private theorem slice109 : FactorMaps.slice 1 w v 109 = true := by
  decide +kernel

private theorem slice110 : FactorMaps.slice 1 w v 110 = true := by
  decide +kernel

private theorem slice111 : FactorMaps.slice 1 w v 111 = true := by
  decide +kernel

private theorem slice112 : FactorMaps.slice 1 w v 112 = true := by
  decide +kernel

private theorem slice113 : FactorMaps.slice 1 w v 113 = true := by
  decide +kernel

private theorem slice114 : FactorMaps.slice 1 w v 114 = true := by
  decide +kernel

private theorem slice115 : FactorMaps.slice 1 w v 115 = true := by
  decide +kernel

private theorem slice116 : FactorMaps.slice 1 w v 116 = true := by
  decide +kernel

private theorem slice117 : FactorMaps.slice 1 w v 117 = true := by
  decide +kernel

private theorem slice118 : FactorMaps.slice 1 w v 118 = true := by
  decide +kernel

private theorem slice119 : FactorMaps.slice 1 w v 119 = true := by
  decide +kernel

private theorem slice120 : FactorMaps.slice 1 w v 120 = true := by
  decide +kernel

private theorem slice121 : FactorMaps.slice 1 w v 121 = true := by
  decide +kernel

private theorem slice122 : FactorMaps.slice 1 w v 122 = true := by
  decide +kernel

private theorem slice123 : FactorMaps.slice 1 w v 123 = true := by
  decide +kernel

private theorem slice124 : FactorMaps.slice 1 w v 124 = true := by
  decide +kernel

private theorem slice125 : FactorMaps.slice 1 w v 125 = true := by
  decide +kernel

private theorem slice126 : FactorMaps.slice 1 w v 126 = true := by
  decide +kernel

private theorem slice127 : FactorMaps.slice 1 w v 127 = true := by
  decide +kernel

private theorem slice128 : FactorMaps.slice 1 w v 128 = true := by
  decide +kernel

private theorem slice129 : FactorMaps.slice 1 w v 129 = true := by
  decide +kernel

private theorem slice130 : FactorMaps.slice 1 w v 130 = true := by
  decide +kernel

private theorem slice131 : FactorMaps.slice 1 w v 131 = true := by
  decide +kernel

private theorem slice132 : FactorMaps.slice 1 w v 132 = true := by
  decide +kernel

private theorem slice133 : FactorMaps.slice 1 w v 133 = true := by
  decide +kernel

private theorem slice134 : FactorMaps.slice 1 w v 134 = true := by
  decide +kernel

private theorem slice135 : FactorMaps.slice 1 w v 135 = true := by
  decide +kernel

private theorem slice136 : FactorMaps.slice 1 w v 136 = true := by
  decide +kernel

private theorem slice137 : FactorMaps.slice 1 w v 137 = true := by
  decide +kernel

private theorem slice138 : FactorMaps.slice 1 w v 138 = true := by
  decide +kernel

private theorem slice139 : FactorMaps.slice 1 w v 139 = true := by
  decide +kernel

private theorem slice140 : FactorMaps.slice 1 w v 140 = true := by
  decide +kernel

private theorem slice141 : FactorMaps.slice 1 w v 141 = true := by
  decide +kernel

private theorem slice142 : FactorMaps.slice 1 w v 142 = true := by
  decide +kernel

private theorem slice143 : FactorMaps.slice 1 w v 143 = true := by
  decide +kernel

private theorem slice144 : FactorMaps.slice 1 w v 144 = true := by
  decide +kernel

private theorem slice145 : FactorMaps.slice 1 w v 145 = true := by
  decide +kernel

private theorem slice146 : FactorMaps.slice 1 w v 146 = true := by
  decide +kernel

private theorem slice147 : FactorMaps.slice 1 w v 147 = true := by
  decide +kernel

private theorem slice148 : FactorMaps.slice 1 w v 148 = true := by
  decide +kernel

private theorem slice149 : FactorMaps.slice 1 w v 149 = true := by
  decide +kernel

private theorem slice150 : FactorMaps.slice 1 w v 150 = true := by
  decide +kernel

private theorem slice151 : FactorMaps.slice 1 w v 151 = true := by
  decide +kernel

private theorem slice152 : FactorMaps.slice 1 w v 152 = true := by
  decide +kernel

private theorem slice153 : FactorMaps.slice 1 w v 153 = true := by
  decide +kernel

private theorem slice154 : FactorMaps.slice 1 w v 154 = true := by
  decide +kernel

private theorem slice155 : FactorMaps.slice 1 w v 155 = true := by
  decide +kernel

private theorem slice156 : FactorMaps.slice 1 w v 156 = true := by
  decide +kernel

private theorem slice157 : FactorMaps.slice 1 w v 157 = true := by
  decide +kernel

private theorem slice158 : FactorMaps.slice 1 w v 158 = true := by
  decide +kernel

private theorem slice159 : FactorMaps.slice 1 w v 159 = true := by
  decide +kernel

private theorem slice160 : FactorMaps.slice 1 w v 160 = true := by
  decide +kernel

private theorem slice161 : FactorMaps.slice 1 w v 161 = true := by
  decide +kernel

private theorem slice162 : FactorMaps.slice 1 w v 162 = true := by
  decide +kernel

private theorem slice163 : FactorMaps.slice 1 w v 163 = true := by
  decide +kernel

private theorem slice164 : FactorMaps.slice 1 w v 164 = true := by
  decide +kernel

private theorem slice165 : FactorMaps.slice 1 w v 165 = true := by
  decide +kernel

private theorem slice166 : FactorMaps.slice 1 w v 166 = true := by
  decide +kernel

private theorem slice167 : FactorMaps.slice 1 w v 167 = true := by
  decide +kernel

private theorem slice168 : FactorMaps.slice 1 w v 168 = true := by
  decide +kernel

private theorem slice169 : FactorMaps.slice 1 w v 169 = true := by
  decide +kernel

private theorem slice170 : FactorMaps.slice 1 w v 170 = true := by
  decide +kernel

private theorem slice171 : FactorMaps.slice 1 w v 171 = true := by
  decide +kernel

private theorem slice172 : FactorMaps.slice 1 w v 172 = true := by
  decide +kernel

private theorem slice173 : FactorMaps.slice 1 w v 173 = true := by
  decide +kernel

private theorem slice174 : FactorMaps.slice 1 w v 174 = true := by
  decide +kernel

private theorem slice175 : FactorMaps.slice 1 w v 175 = true := by
  decide +kernel

private theorem slice176 : FactorMaps.slice 1 w v 176 = true := by
  decide +kernel

private theorem slice177 : FactorMaps.slice 1 w v 177 = true := by
  decide +kernel

private theorem slice178 : FactorMaps.slice 1 w v 178 = true := by
  decide +kernel

private theorem slice179 : FactorMaps.slice 1 w v 179 = true := by
  decide +kernel

private theorem slice180 : FactorMaps.slice 1 w v 180 = true := by
  decide +kernel

private theorem slice181 : FactorMaps.slice 1 w v 181 = true := by
  decide +kernel

private theorem slice182 : FactorMaps.slice 1 w v 182 = true := by
  decide +kernel

private theorem slice183 : FactorMaps.slice 1 w v 183 = true := by
  decide +kernel

private theorem slice184 : FactorMaps.slice 1 w v 184 = true := by
  decide +kernel

private theorem slice185 : FactorMaps.slice 1 w v 185 = true := by
  decide +kernel

private theorem slice186 : FactorMaps.slice 1 w v 186 = true := by
  decide +kernel

private theorem slice187 : FactorMaps.slice 1 w v 187 = true := by
  decide +kernel

private theorem slice188 : FactorMaps.slice 1 w v 188 = true := by
  decide +kernel

private theorem slice189 : FactorMaps.slice 1 w v 189 = true := by
  decide +kernel

private theorem slice190 : FactorMaps.slice 1 w v 190 = true := by
  decide +kernel

private theorem slice191 : FactorMaps.slice 1 w v 191 = true := by
  decide +kernel

private theorem slice192 : FactorMaps.slice 1 w v 192 = true := by
  decide +kernel

private theorem slice193 : FactorMaps.slice 1 w v 193 = true := by
  decide +kernel

private theorem slice194 : FactorMaps.slice 1 w v 194 = true := by
  decide +kernel

private theorem slice195 : FactorMaps.slice 1 w v 195 = true := by
  decide +kernel

private theorem slice196 : FactorMaps.slice 1 w v 196 = true := by
  decide +kernel

private theorem slice197 : FactorMaps.slice 1 w v 197 = true := by
  decide +kernel

private theorem slice198 : FactorMaps.slice 1 w v 198 = true := by
  decide +kernel

private theorem slice199 : FactorMaps.slice 1 w v 199 = true := by
  decide +kernel

private theorem slice200 : FactorMaps.slice 1 w v 200 = true := by
  decide +kernel

private theorem slice201 : FactorMaps.slice 1 w v 201 = true := by
  decide +kernel

private theorem slice202 : FactorMaps.slice 1 w v 202 = true := by
  decide +kernel

/-- The dense transition follows from its exhaustive cached slice checks. -/
public theorem checked : stepCheck (FactorWords.row 1).1 (FactorWords.row 1).2 := by
  apply FactorMaps.ofSlices 1 w v
  · decide +kernel
  · decide +kernel
  · intro b
    fin_cases b
    · exact slice0
    · exact slice1
    · exact slice2
    · exact slice3
    · exact slice4
    · exact slice5
    · exact slice6
    · exact slice7
    · exact slice8
    · exact slice9
    · exact slice10
    · exact slice11
    · exact slice12
    · exact slice13
    · exact slice14
    · exact slice15
    · exact slice16
    · exact slice17
    · exact slice18
    · exact slice19
    · exact slice20
    · exact slice21
    · exact slice22
    · exact slice23
    · exact slice24
    · exact slice25
    · exact slice26
    · exact slice27
    · exact slice28
    · exact slice29
    · exact slice30
    · exact slice31
    · exact slice32
    · exact slice33
    · exact slice34
    · exact slice35
    · exact slice36
    · exact slice37
    · exact slice38
    · exact slice39
    · exact slice40
    · exact slice41
    · exact slice42
    · exact slice43
    · exact slice44
    · exact slice45
    · exact slice46
    · exact slice47
    · exact slice48
    · exact slice49
    · exact slice50
    · exact slice51
    · exact slice52
    · exact slice53
    · exact slice54
    · exact slice55
    · exact slice56
    · exact slice57
    · exact slice58
    · exact slice59
    · exact slice60
    · exact slice61
    · exact slice62
    · exact slice63
    · exact slice64
    · exact slice65
    · exact slice66
    · exact slice67
    · exact slice68
    · exact slice69
    · exact slice70
    · exact slice71
    · exact slice72
    · exact slice73
    · exact slice74
    · exact slice75
    · exact slice76
    · exact slice77
    · exact slice78
    · exact slice79
    · exact slice80
    · exact slice81
    · exact slice82
    · exact slice83
    · exact slice84
    · exact slice85
    · exact slice86
    · exact slice87
    · exact slice88
    · exact slice89
    · exact slice90
    · exact slice91
    · exact slice92
    · exact slice93
    · exact slice94
    · exact slice95
    · exact slice96
    · exact slice97
    · exact slice98
    · exact slice99
    · exact slice100
    · exact slice101
    · exact slice102
    · exact slice103
    · exact slice104
    · exact slice105
    · exact slice106
    · exact slice107
    · exact slice108
    · exact slice109
    · exact slice110
    · exact slice111
    · exact slice112
    · exact slice113
    · exact slice114
    · exact slice115
    · exact slice116
    · exact slice117
    · exact slice118
    · exact slice119
    · exact slice120
    · exact slice121
    · exact slice122
    · exact slice123
    · exact slice124
    · exact slice125
    · exact slice126
    · exact slice127
    · exact slice128
    · exact slice129
    · exact slice130
    · exact slice131
    · exact slice132
    · exact slice133
    · exact slice134
    · exact slice135
    · exact slice136
    · exact slice137
    · exact slice138
    · exact slice139
    · exact slice140
    · exact slice141
    · exact slice142
    · exact slice143
    · exact slice144
    · exact slice145
    · exact slice146
    · exact slice147
    · exact slice148
    · exact slice149
    · exact slice150
    · exact slice151
    · exact slice152
    · exact slice153
    · exact slice154
    · exact slice155
    · exact slice156
    · exact slice157
    · exact slice158
    · exact slice159
    · exact slice160
    · exact slice161
    · exact slice162
    · exact slice163
    · exact slice164
    · exact slice165
    · exact slice166
    · exact slice167
    · exact slice168
    · exact slice169
    · exact slice170
    · exact slice171
    · exact slice172
    · exact slice173
    · exact slice174
    · exact slice175
    · exact slice176
    · exact slice177
    · exact slice178
    · exact slice179
    · exact slice180
    · exact slice181
    · exact slice182
    · exact slice183
    · exact slice184
    · exact slice185
    · exact slice186
    · exact slice187
    · exact slice188
    · exact slice189
    · exact slice190
    · exact slice191
    · exact slice192
    · exact slice193
    · exact slice194
    · exact slice195
    · exact slice196
    · exact slice197
    · exact slice198
    · exact slice199
    · exact slice200
    · exact slice201
    · exact slice202

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.Dense0.Row1
