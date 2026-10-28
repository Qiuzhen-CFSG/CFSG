module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Data

/-!
# Shared subgroup words for the Fi23 fixed-point loops

Every register is an actual element of the unchanged two-generator
`KernelUpperData.first`. Register sharing avoids exponentially long expanded
words. This proves membership of the words, but does not identify their actions
with the candidate tables or with the Schreier loops.

Source: retained ATLAS F23G1-p31671B0, inverse-cycle convention; GLS3
Table 5.3u and the Fischer paragraph of `refs/KGroup/GLS3/Chapter5(sec3-).tex`.
The untrusted witnesses and their provenance are retained in `Loops/source/`.
-/

set_option Elab.async false

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Loops

def word1 : KernelUpperData.first :=
  ⟨KernelUpperData.One0.permutation, Subgroup.subset_closure ⟨0, rfl⟩⟩

def word2 : KernelUpperData.first :=
  ⟨KernelUpperData.One1.permutation, Subgroup.subset_closure ⟨1, rfl⟩⟩

def word3 : KernelUpperData.first := word1⁻¹
def word4 : KernelUpperData.first := word2⁻¹
def word5 : KernelUpperData.first := word3 * word3
def word6 : KernelUpperData.first := word5 * word3
def word7 : KernelUpperData.first := word6 * word3
def word8 : KernelUpperData.first := word7⁻¹
def word9 : KernelUpperData.first := word8 * word1
def word10 : KernelUpperData.first := word1⁻¹
def word11 : KernelUpperData.first := word10 * word7
def word12 : KernelUpperData.first := word3 * word3
def word13 : KernelUpperData.first := word12 * word4
def word14 : KernelUpperData.first := word13 * word3
def word15 : KernelUpperData.first := word14 * word3
def word16 : KernelUpperData.first := word15 * word3
def word17 : KernelUpperData.first := word16⁻¹
def word18 : KernelUpperData.first := word17 * word2
def word19 : KernelUpperData.first := word2⁻¹
def word20 : KernelUpperData.first := word19 * word16
def word21 : KernelUpperData.first := 1
def word22 : KernelUpperData.first := word2
def word23 : KernelUpperData.first := word21 * word22
def word24 : KernelUpperData.first := 1
def word25 : KernelUpperData.first := word23 * word24
def word26 : KernelUpperData.first := word11
def word27 : KernelUpperData.first := word25 * word26
def word28 : KernelUpperData.first := word1
def word29 : KernelUpperData.first := word27 * word28
def word30 : KernelUpperData.first := word4
def word31 : KernelUpperData.first := word29 * word30
def word32 : KernelUpperData.first := word20
def word33 : KernelUpperData.first := word31 * word32
def word34 : KernelUpperData.first := 1
def word35 : KernelUpperData.first := word33 * word34
def word36 : KernelUpperData.first := word1 * word4
def word37 : KernelUpperData.first := word36 * word20
def word38 : KernelUpperData.first := word37 * word1
def word39 : KernelUpperData.first := word38 * word20
def word40 : KernelUpperData.first := word39 * word2
def word41 : KernelUpperData.first := word40 * word9
def word42 : KernelUpperData.first := word41 * word35
def word43 : KernelUpperData.first := word42 * word2
def word44 : KernelUpperData.first := word43 * word9
def word45 : KernelUpperData.first := word44 * word2
def word46 : KernelUpperData.first := word45 * word1
def word47 : KernelUpperData.first := word46 * word18
def word48 : KernelUpperData.first := word47 * word1
def word49 : KernelUpperData.first := word48⁻¹
def word50 : KernelUpperData.first := word49 * word49
def word51 : KernelUpperData.first := word50⁻¹
def word52 : KernelUpperData.first := word51 * word48
def word53 : KernelUpperData.first := word48⁻¹
def word54 : KernelUpperData.first := word53 * word50
def word55 : KernelUpperData.first := word1 * word4
def word56 : KernelUpperData.first := word55 * word20
def word57 : KernelUpperData.first := word56 * word4
def word58 : KernelUpperData.first := word57 * word20
def word59 : KernelUpperData.first := word58 * word20
def word60 : KernelUpperData.first := word59 * word35
def word61 : KernelUpperData.first := word60 * word4
def word62 : KernelUpperData.first := word61 * word4
def word63 : KernelUpperData.first := word62 * word3
def word64 : KernelUpperData.first := word63 * word4
def word65 : KernelUpperData.first := word64 * word11
def word66 : KernelUpperData.first := word65 * word4
def word67 : KernelUpperData.first := word66⁻¹
def word68 : KernelUpperData.first := word49 * word49
def word69 : KernelUpperData.first := word68 * word67
def word70 : KernelUpperData.first := word69 * word54
def word71 : KernelUpperData.first := word70 * word49
def word72 : KernelUpperData.first := word71 * word49
def word73 : KernelUpperData.first := word72⁻¹
def word74 : KernelUpperData.first := word73 * word66
def word75 : KernelUpperData.first := word66⁻¹
def word76 : KernelUpperData.first := word75 * word72
def word77 : KernelUpperData.first := 1
def word78 : KernelUpperData.first := word52
def word79 : KernelUpperData.first := word77 * word78
def word80 : KernelUpperData.first := 1
def word81 : KernelUpperData.first := word79 * word80
def word82 : KernelUpperData.first := word67
def word83 : KernelUpperData.first := word81 * word82
def word84 : KernelUpperData.first := 1
def word85 : KernelUpperData.first := word83 * word84
def word86 : KernelUpperData.first := word49
def word87 : KernelUpperData.first := word85 * word86
def word88 : KernelUpperData.first := 1
def word89 : KernelUpperData.first := word87 * word88
def word90 : KernelUpperData.first := word54
def word91 : KernelUpperData.first := word89 * word90
def word92 : KernelUpperData.first := word48 * word54
def word93 : KernelUpperData.first := word92 * word74
def word94 : KernelUpperData.first := word93 * word48
def word95 : KernelUpperData.first := word94 * word76
def word96 : KernelUpperData.first := word95 * word66
def word97 : KernelUpperData.first := word96 * word91
def word98 : KernelUpperData.first := word97 * word52
def word99 : KernelUpperData.first := word98 * word49
def word100 : KernelUpperData.first := word99 * word76
def word101 : KernelUpperData.first := word100 * word49
def word102 : KernelUpperData.first := word101⁻¹
def word103 : KernelUpperData.first := word102 * word102
def word104 : KernelUpperData.first := word103⁻¹
def word105 : KernelUpperData.first := word104 * word101
def word106 : KernelUpperData.first := word101⁻¹
def word107 : KernelUpperData.first := word106 * word103
def word108 : KernelUpperData.first := word52 * word74
def word109 : KernelUpperData.first := word108 * word66
def word110 : KernelUpperData.first := word109 * word76
def word111 : KernelUpperData.first := word110 * word49
def word112 : KernelUpperData.first := word111 * word91
def word113 : KernelUpperData.first := word112 * word52
def word114 : KernelUpperData.first := word113 * word76
def word115 : KernelUpperData.first := word114 * word52
def word116 : KernelUpperData.first := word115 * word48
def word117 : KernelUpperData.first := word116⁻¹
def word118 : KernelUpperData.first := word116
def word119 : KernelUpperData.first := 1
def word120 : KernelUpperData.first := word118 * word119
def word121 : KernelUpperData.first := word105
def word122 : KernelUpperData.first := word120 * word121
def word123 : KernelUpperData.first := word117
def word124 : KernelUpperData.first := word122 * word123
def word125 : KernelUpperData.first := word101
def word126 : KernelUpperData.first := word124 * word125
def word127 : KernelUpperData.first := word102
def word128 : KernelUpperData.first := word126 * word127
def word129 : KernelUpperData.first := word117 * word107
def word130 : KernelUpperData.first := word129 * word116
def word131 : KernelUpperData.first := word130 * word116
def word132 : KernelUpperData.first := word131 * word128
def word133 : KernelUpperData.first := word132 * word105
def word134 : KernelUpperData.first := word133 * word116
def word135 : KernelUpperData.first := word134 * word107
def word136 : KernelUpperData.first := word135 * word117
def word137 : KernelUpperData.first := word136 * word102
def word138 : KernelUpperData.first := word137⁻¹
def word139 : KernelUpperData.first := word138 * word138
def word140 : KernelUpperData.first := word139⁻¹
def word141 : KernelUpperData.first := word140 * word137
def word142 : KernelUpperData.first := word137⁻¹
def word143 : KernelUpperData.first := word142 * word139
def word144 : KernelUpperData.first := word105 * word117
def word145 : KernelUpperData.first := word144 * word117
def word146 : KernelUpperData.first := word145 * word101
def word147 : KernelUpperData.first := word146 * word128
def word148 : KernelUpperData.first := word147 * word102
def word149 : KernelUpperData.first := word148 * word117
def word150 : KernelUpperData.first := word149 * word105
def word151 : KernelUpperData.first := word150 * word117
def word152 : KernelUpperData.first := word151 * word102
def word153 : KernelUpperData.first := word152 * word138
def word154 : KernelUpperData.first := word153 * word138
def word155 : KernelUpperData.first := word143⁻¹
def word156 : KernelUpperData.first := word155 * word154
def word157 : KernelUpperData.first := word154⁻¹
def word158 : KernelUpperData.first := word157 * word143
def word159 : KernelUpperData.first := word154⁻¹
def word160 : KernelUpperData.first := 1
def word161 : KernelUpperData.first := word158
def word162 : KernelUpperData.first := word160 * word161
def word163 : KernelUpperData.first := 1
def word164 : KernelUpperData.first := word162 * word163
def word165 : KernelUpperData.first := word141
def word166 : KernelUpperData.first := word164 * word165
def word167 : KernelUpperData.first := 1
def word168 : KernelUpperData.first := word166 * word167
def word169 : KernelUpperData.first := word137
def word170 : KernelUpperData.first := word168 * word169
def word171 : KernelUpperData.first := 1
def word172 : KernelUpperData.first := word170 * word171
def word173 : KernelUpperData.first := word154
def word174 : KernelUpperData.first := word172 * word173
def word175 : KernelUpperData.first := word141 * word174
def word176 : KernelUpperData.first := word175 * word138
def word177 : KernelUpperData.first := word176 * word138
def word178 : KernelUpperData.first := word177 * word154
def word179 : KernelUpperData.first := word178 * word154
def word180 : KernelUpperData.first := word179⁻¹
def word181 : KernelUpperData.first := word180 * word159
def word182 : KernelUpperData.first := word179⁻¹
def word183 : KernelUpperData.first := word101 * word101
def word184 : KernelUpperData.first := word183 * word116
def word185 : KernelUpperData.first := word184 * word107
def word186 : KernelUpperData.first := word185 * word128
def word187 : KernelUpperData.first := word186 * word105
def word188 : KernelUpperData.first := word187 * word117
def word189 : KernelUpperData.first := word188 * word117
def word190 : KernelUpperData.first := word189 * word138
def word191 : KernelUpperData.first := word190 * word159
def word192 : KernelUpperData.first := word191 * word159
def word193 : KernelUpperData.first := word192⁻¹
def word194 : KernelUpperData.first := 1
def word195 : KernelUpperData.first := word192
def word196 : KernelUpperData.first := word194 * word195
def word197 : KernelUpperData.first := 1
def word198 : KernelUpperData.first := word196 * word197
def word199 : KernelUpperData.first := 1
def word200 : KernelUpperData.first := word198 * word199
def word201 : KernelUpperData.first := word179 * word200
def word202 : KernelUpperData.first := word201 * word179
def word203 : KernelUpperData.first := word202⁻¹
def word204 : KernelUpperData.first := 1
def word205 : KernelUpperData.first := word203
def word206 : KernelUpperData.first := word204 * word205
def word207 : KernelUpperData.first := word193
def word208 : KernelUpperData.first := word206 * word207
def word209 : KernelUpperData.first := 1
def word210 : KernelUpperData.first := word208 * word209
def word211 : KernelUpperData.first := word192 * word203
def word212 : KernelUpperData.first := word211 * word210
def word213 : KernelUpperData.first := word212 * word203
def word214 : KernelUpperData.first := word213⁻¹
def word215 : KernelUpperData.first := word182 * word200
def word216 : KernelUpperData.first := word215 * word182
def word217 : KernelUpperData.first := word216 * word193
def word218 : KernelUpperData.first := word217⁻¹

/-- Shared registers; unused indices denote the identity. -/
def coreWord (i : Nat) : KernelUpperData.first :=
  match i with
  | 1 => word1
  | 2 => word2
  | 3 => word3
  | 4 => word4
  | 7 => word7
  | 9 => word9
  | 11 => word11
  | 16 => word16
  | 18 => word18
  | 20 => word20
  | 35 => word35
  | 48 => word48
  | 49 => word49
  | 50 => word50
  | 52 => word52
  | 54 => word54
  | 66 => word66
  | 67 => word67
  | 72 => word72
  | 74 => word74
  | 76 => word76
  | 91 => word91
  | 101 => word101
  | 102 => word102
  | 103 => word103
  | 105 => word105
  | 107 => word107
  | 116 => word116
  | 117 => word117
  | 128 => word128
  | 137 => word137
  | 138 => word138
  | 139 => word139
  | 141 => word141
  | 143 => word143
  | 154 => word154
  | 158 => word158
  | 159 => word159
  | 179 => word179
  | 181 => word181
  | 182 => word182
  | 192 => word192
  | 193 => word193
  | 200 => word200
  | 202 => word202
  | 203 => word203
  | 214 => word214
  | 217 => word217
  | 218 => word218
  | _ => 1

/-- A packed list of eight-bit register indices, in multiplication order. -/
def factorWord : Nat → Nat → KernelUpperData.first
  | 0, _ => 1
  | d + 1, w => coreWord (w % 256) * factorWord d (w / 256)

end Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Loops
