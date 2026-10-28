module

public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.Conjugacy.WordValues.Program

/-!
# Soundness of certificates for the recovered-word program

A certificate supplies a matrix at each of the 242 program nodes and verifies
one matrix equation per operation. For an inverse node a left inverse equation
suffices: its operand is already known to be the value of a unit. Induction
along the straight-line program therefore identifies every certified matrix
with the corresponding group word, without trusting external inversion.

The program and source attribution are in `Program.lean` and
`../source/README.md`.
-/

@[expose] public section

namespace BabyMonster.OrderLowerBound.RecoveredWordProgram

/-- Matrix equations for the straight-line program. Inverse instructions
are checked by multiplication, rather than by a matrix inversion algorithm. -/
structure Certificate (v : Fin 242 → AtlasMatrix) : Prop where
  step0 : v 0 = 1
  step1 : v 1 = atlasA
  step2 : v 2 = atlasB
  step3 : v 3 = v 1 * v 1
  step4 : v 4 = v 2 * v 2
  step5 : v 5 = v 4 * v 2
  step6 : v 6 = v 1 * v 2
  step7 : v 7 = v 6 * v 6
  step8 : v 8 = v 7 * v 6
  step9 : v 9 = v 8 * v 8
  step10 : v 10 = v 9 * v 6
  step11 : v 11 = v 10 * v 10
  step12 : v 12 = v 11 * v 6
  step13 : v 13 = v 12 * v 2
  step14 : v 14 = v 13 * v 13
  step15 : v 15 = v 14 * v 14
  step16 : v 16 = v 15 * v 15
  step17 : v 17 = v 16 * v 13
  step18 : v 18 = v 17 * v 17
  step19 : v 19 = v 18 * v 13
  step20 : v 20 = v 1 * v 19
  step21 : v 21 = v 20 * v 20
  step22 : v 22 = v 21 * v 20
  step23 : v 23 = v 13 * v 13
  step24 : v 24 = v 23 * v 13
  step25 : v 25 = v 22 * v 24
  step26 : v 26 = v 25 * v 25
  step27 : v 27 = v 26 * v 26
  step28 : v 28 = v 27 * v 25
  step29 : v 29 = v 28 * v 28
  step30 : v 30 * v 13 = 1
  step31 : v 31 = v 30 * v 29
  step32 : v 32 = v 31 * v 13
  step33 : v 33 = v 32 * v 22
  step34 : v 34 = v 33 * v 33
  step35 : v 35 = v 34 * v 33
  step36 : v 36 = v 35 * v 35
  step37 : v 37 = v 36 * v 22
  step38 : v 38 = v 33 * v 33
  step39 : v 39 = v 38 * v 33
  step40 : v 40 = v 37 * v 39
  step41 : v 41 = v 40 * v 40
  step42 : v 42 = v 41 * v 32
  step43 : v 43 = v 42 * v 22
  step44 : v 44 = v 32 * v 32
  step45 : v 45 = v 43 * v 44
  step46 : v 46 = v 45 * v 22
  step47 : v 47 = v 46 * v 46
  step48 : v 48 = v 47 * v 47
  step49 : v 49 = v 48 * v 46
  step50 : v 50 = v 33 * v 33
  step51 : v 51 = v 50 * v 50
  step52 : v 52 * v 51 = 1
  step53 : v 53 = v 52 * v 49
  step54 : v 54 = v 53 * v 51
  step55 : v 55 = v 33 * v 33
  step56 : v 56 = v 55 * v 55
  step57 : v 57 = v 56 * v 56
  step58 : v 58 = v 57 * v 22
  step59 : v 59 = v 33 * v 33
  step60 : v 60 = v 59 * v 33
  step61 : v 61 = v 58 * v 60
  step62 : v 62 = v 32 * v 22
  step63 : v 63 = v 32 * v 32
  step64 : v 64 = v 62 * v 63
  step65 : v 65 = v 64 * v 22
  step66 : v 66 = v 65 * v 65
  step67 : v 67 * v 66 = 1
  step68 : v 68 = v 67 * v 61
  step69 : v 69 = v 68 * v 66
  step70 : v 70 = v 69 * v 54
  step71 : v 71 = v 70 * v 0
  step72 : v 72 * v 71 = 1
  step73 : v 73 = v 72 * v 54
  step74 : v 74 = v 73 * v 71
  step75 : v 75 = v 69 * v 54
  step76 : v 76 = v 75 * v 69
  step77 : v 77 * v 76 = 1
  step78 : v 78 = v 77 * v 54
  step79 : v 79 = v 78 * v 76
  step80 : v 80 = v 69 * v 54
  step81 : v 81 = v 69 * v 69
  step82 : v 82 = v 80 * v 81
  step83 : v 83 * v 82 = 1
  step84 : v 84 = v 83 * v 54
  step85 : v 85 = v 84 * v 82
  step86 : v 86 = v 69 * v 54
  step87 : v 87 = v 69 * v 69
  step88 : v 88 = v 87 * v 69
  step89 : v 89 = v 86 * v 88
  step90 : v 90 * v 89 = 1
  step91 : v 91 = v 90 * v 54
  step92 : v 92 = v 91 * v 89
  step93 : v 93 = v 69 * v 54
  step94 : v 94 = v 69 * v 69
  step95 : v 95 = v 94 * v 94
  step96 : v 96 = v 93 * v 95
  step97 : v 97 * v 96 = 1
  step98 : v 98 = v 97 * v 54
  step99 : v 99 = v 98 * v 96
  step100 : v 100 = v 69 * v 54
  step101 : v 101 = v 69 * v 69
  step102 : v 102 = v 101 * v 101
  step103 : v 103 = v 102 * v 69
  step104 : v 104 = v 100 * v 103
  step105 : v 105 * v 104 = 1
  step106 : v 106 = v 105 * v 54
  step107 : v 107 = v 106 * v 104
  step108 : v 108 = v 69 * v 54
  step109 : v 109 = v 69 * v 69
  step110 : v 110 = v 109 * v 69
  step111 : v 111 = v 110 * v 110
  step112 : v 112 = v 108 * v 111
  step113 : v 113 * v 112 = 1
  step114 : v 114 = v 113 * v 54
  step115 : v 115 = v 114 * v 112
  step116 : v 116 = v 6 * v 6
  step117 : v 117 = v 116 * v 116
  step118 : v 118 = v 117 * v 6
  step119 : v 119 = v 118 * v 19
  step120 : v 120 * v 118 = 1
  step121 : v 121 = v 119 * v 120
  step122 : v 122 = v 121 * v 54
  step123 : v 123 = v 122 * v 118
  step124 : v 124 * v 123 = 1
  step125 : v 125 = v 123 * v 13
  step126 : v 126 = v 125 * v 124
  step127 : v 127 = v 126 * v 126
  step128 : v 128 * v 127 = 1
  step129 : v 129 = v 128 * v 92
  step130 : v 130 = v 129 * v 127
  step131 : v 131 = v 79 * v 85
  step132 : v 132 * v 130 = 1
  step133 : v 133 * v 131 = 1
  step134 : v 134 = v 132 * v 133
  step135 : v 135 = v 134 * v 130
  step136 : v 136 = v 135 * v 131
  step137 : v 137 = v 126 * v 126
  step138 : v 138 = v 137 * v 137
  step139 : v 139 = v 138 * v 126
  step140 : v 140 * v 139 = 1
  step141 : v 141 = v 140 * v 92
  step142 : v 142 = v 141 * v 139
  step143 : v 143 = v 79 * v 85
  step144 : v 144 * v 142 = 1
  step145 : v 145 * v 143 = 1
  step146 : v 146 = v 144 * v 145
  step147 : v 147 = v 146 * v 142
  step148 : v 148 = v 147 * v 143
  step149 : v 149 = v 136 * v 148
  step150 : v 150 * v 149 = 1
  step151 : v 151 = v 150 * v 115
  step152 : v 152 = v 151 * v 149
  step153 : v 153 = v 99 * v 107
  step154 : v 154 * v 152 = 1
  step155 : v 155 * v 153 = 1
  step156 : v 156 = v 154 * v 155
  step157 : v 157 = v 156 * v 152
  step158 : v 158 = v 157 * v 153
  step159 : v 159 = v 148 * v 136
  step160 : v 160 * v 159 = 1
  step161 : v 161 = v 160 * v 115
  step162 : v 162 = v 161 * v 159
  step163 : v 163 = v 99 * v 107
  step164 : v 164 * v 162 = 1
  step165 : v 165 * v 163 = 1
  step166 : v 166 = v 164 * v 165
  step167 : v 167 = v 166 * v 162
  step168 : v 168 = v 167 * v 163
  step169 : v 169 = v 158 * v 168
  step170 : v 170 = v 136 * v 148
  step171 : v 171 = v 170 * v 170
  step172 : v 172 = v 171 * v 171
  step173 : v 173 * v 172 = 1
  step174 : v 174 = v 173 * v 115
  step175 : v 175 = v 174 * v 172
  step176 : v 176 = v 99 * v 107
  step177 : v 177 * v 175 = 1
  step178 : v 178 * v 176 = 1
  step179 : v 179 = v 177 * v 178
  step180 : v 180 = v 179 * v 175
  step181 : v 181 = v 180 * v 176
  step182 : v 182 = v 136 * v 148
  step183 : v 183 = v 182 * v 182
  step184 : v 184 = v 183 * v 182
  step185 : v 185 = v 184 * v 148
  step186 : v 186 = v 185 * v 136
  step187 : v 187 * v 186 = 1
  step188 : v 188 = v 187 * v 115
  step189 : v 189 = v 188 * v 186
  step190 : v 190 = v 169 * v 181
  step191 : v 191 = v 190 * v 189
  step192 : v 192 = v 191 * v 191
  step193 : v 193 = v 192 * v 191
  step194 : v 194 = v 193 * v 181
  step195 : v 195 = v 194 * v 189
  step196 : v 196 = v 195 * v 195
  step197 : v 197 = v 196 * v 196
  step198 : v 198 * v 197 = 1
  step199 : v 199 = v 198 * v 189
  step200 : v 200 = v 199 * v 197
  step201 : v 201 * v 195 = 1
  step202 : v 202 = v 201 * v 200
  step203 : v 203 = v 202 * v 195
  step204 : v 204 = v 203 * v 200
  step205 : v 205 = v 204 * v 189
  step206 : v 206 = v 205 * v 200
  step207 : v 207 = v 206 * v 203
  step208 : v 208 = v 189 * v 200
  step209 : v 209 = v 208 * v 207
  step210 : v 210 = v 209 * v 200
  step211 : v 211 = v 210 * v 189
  step212 : v 212 = v 54 * v 74
  step213 : v 213 = v 212 * v 79
  step214 : v 214 = v 213 * v 85
  step215 : v 215 = v 214 * v 92
  step216 : v 216 = v 215 * v 99
  step217 : v 217 = v 216 * v 107
  step218 : v 218 = v 217 * v 115
  step219 : v 219 = v 92 * v 211
  step220 : v 220 = v 219 * v 207
  step221 : v 221 = v 220 * v 19
  step222 : v 222 = v 218 * v 218
  step223 : v 223 = v 222 * v 218
  step224 : v 224 = v 223 * v 223
  step225 : v 225 = v 224 * v 218
  step226 : v 226 = v 225 * v 221
  step227 : v 227 = v 226 * v 226
  step228 : v 228 = v 227 * v 226
  step229 : v 229 = v 228 * v 228
  step230 : v 230 = v 229 * v 226
  step231 : v 231 = v 230 * v 230
  step232 : v 232 = v 231 * v 226
  step233 : v 233 = v 54 * v 74
  step234 : v 234 = v 221 * v 218
  step235 : v 235 = v 234 * v 234
  step236 : v 236 = v 235 * v 235
  step237 : v 237 = v 236 * v 234
  step238 : v 238 = v 237 * v 237
  step239 : v 239 * v 238 = 1
  step240 : v 240 = v 239 * v 233
  step241 : v 241 = v 240 * v 238

attribute [local irreducible] node0 node1 node2 node3 node4 node5 node6 node7 node8 node9 node10 node11 node12 node13 node14 node15 node16 node17 node18 node19 node20 node21 node22 node23 node24 node25 node26 node27 node28 node29 node30 node31 node32 node33 node34 node35 node36 node37 node38 node39 node40 node41 node42 node43 node44 node45 node46 node47 node48 node49 node50 node51 node52 node53 node54 node55 node56 node57 node58 node59 node60 node61 node62 node63 node64 node65 node66 node67 node68 node69 node70 node71 node72 node73 node74 node75 node76 node77 node78 node79 node80 node81 node82 node83 node84 node85 node86 node87 node88 node89 node90 node91 node92 node93 node94 node95 node96 node97 node98 node99 node100 node101 node102 node103 node104 node105 node106 node107 node108 node109 node110 node111 node112 node113 node114 node115 node116 node117 node118 node119 node120 node121 node122 node123 node124 node125 node126 node127 node128 node129 node130 node131 node132 node133 node134 node135 node136 node137 node138 node139 node140 node141 node142 node143 node144 node145 node146 node147 node148 node149 node150 node151 node152 node153 node154 node155 node156 node157 node158 node159 node160 node161 node162 node163 node164 node165 node166 node167 node168 node169 node170 node171 node172 node173 node174 node175 node176 node177 node178 node179 node180 node181 node182 node183 node184 node185 node186 node187 node188 node189 node190 node191 node192 node193 node194 node195 node196 node197 node198 node199 node200 node201 node202 node203 node204 node205 node206 node207 node208 node209 node210 node211 node212 node213 node214 node215 node216 node217 node218 node219 node220 node221 node222 node223 node224 node225 node226 node227 node228 node229 node230 node231 node232 node233 node234 node235 node236 node237 node238 node239 node240 node241

private theorem eq_unit_inv {M : Type*} [Monoid M] (u : Mˣ) (x : M)
    (h : x * (u : M) = 1) : x = ((u⁻¹ : Mˣ) : M) := by
  calc
    x = x * ((u : M) * ((u⁻¹ : Mˣ) : M)) := by rw [Units.mul_inv, mul_one]
    _ = (x * (u : M)) * ((u⁻¹ : Mˣ) : M) := (mul_assoc _ _ _).symm
    _ = ((u⁻¹ : Mˣ) : M) := by rw [h, one_mul]

private theorem mul_sound {M : Type*} [Monoid M] (u w : Mˣ) (x y z : M)
    (h : x = y * z) (hy : y = (u : M)) (hz : z = (w : M)) :
    x = ((u * w : Mˣ) : M) := by
  rw [Units.val_mul, ← hy, ← hz]
  exact h

private theorem inv_sound {M : Type*} [Monoid M] (u : Mˣ) (x y : M)
    (h : x * y = 1) (hy : y = (u : M)) : x = ((u⁻¹ : Mˣ) : M) := by
  apply eq_unit_inv
  rw [← hy]
  exact h

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Soundness at both output nodes, conditional only on the standard generators
being units and the explicitly supplied operation certificates. -/
theorem Certificate.outputs {v : Fin 242 → AtlasMatrix} (c : Certificate v)
    (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1) :
    v 232 = (↑(node232 (standardA ha) (standardB hb)) : AtlasMatrix) ∧
    v 241 = (↑(node241 (standardA ha) (standardB hb)) : AtlasMatrix) := by
  have h0 : v 0 = (↑(node0 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact c.step0 |>.trans (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
      (node0_spec (standardA ha) (standardB hb)).symm)
  have h1 : v 1 = (↑(node1 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact c.step1 |>.trans (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
      (node1_spec (standardA ha) (standardB hb)).symm)
  have h2 : v 2 = (↑(node2 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact c.step2 |>.trans (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
      (node2_spec (standardA ha) (standardB hb)).symm)
  have h6 : v 6 = (↑(node6 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node1 (standardA ha) (standardB hb))
      (node2 (standardA ha) (standardB hb)) (v 6) (v 1) (v 2) c.step6 h1 h2).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node6_spec (standardA ha) (standardB hb)).symm)
  have h7 : v 7 = (↑(node7 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node6 (standardA ha) (standardB hb))
      (node6 (standardA ha) (standardB hb)) (v 7) (v 6) (v 6) c.step7 h6 h6).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node7_spec (standardA ha) (standardB hb)).symm)
  have h8 : v 8 = (↑(node8 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node7 (standardA ha) (standardB hb))
      (node6 (standardA ha) (standardB hb)) (v 8) (v 7) (v 6) c.step8 h7 h6).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node8_spec (standardA ha) (standardB hb)).symm)
  have h9 : v 9 = (↑(node9 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node8 (standardA ha) (standardB hb))
      (node8 (standardA ha) (standardB hb)) (v 9) (v 8) (v 8) c.step9 h8 h8).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node9_spec (standardA ha) (standardB hb)).symm)
  have h10 : v 10 = (↑(node10 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node9 (standardA ha) (standardB hb))
      (node6 (standardA ha) (standardB hb)) (v 10) (v 9) (v 6) c.step10 h9 h6).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node10_spec (standardA ha) (standardB hb)).symm)
  have h11 : v 11 = (↑(node11 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node10 (standardA ha) (standardB hb))
      (node10 (standardA ha) (standardB hb)) (v 11) (v 10) (v 10) c.step11 h10 h10).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node11_spec (standardA ha) (standardB hb)).symm)
  have h12 : v 12 = (↑(node12 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node11 (standardA ha) (standardB hb))
      (node6 (standardA ha) (standardB hb)) (v 12) (v 11) (v 6) c.step12 h11 h6).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node12_spec (standardA ha) (standardB hb)).symm)
  have h13 : v 13 = (↑(node13 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node12 (standardA ha) (standardB hb))
      (node2 (standardA ha) (standardB hb)) (v 13) (v 12) (v 2) c.step13 h12 h2).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node13_spec (standardA ha) (standardB hb)).symm)
  have h14 : v 14 = (↑(node14 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node13 (standardA ha) (standardB hb))
      (node13 (standardA ha) (standardB hb)) (v 14) (v 13) (v 13) c.step14 h13 h13).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node14_spec (standardA ha) (standardB hb)).symm)
  have h15 : v 15 = (↑(node15 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node14 (standardA ha) (standardB hb))
      (node14 (standardA ha) (standardB hb)) (v 15) (v 14) (v 14) c.step15 h14 h14).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node15_spec (standardA ha) (standardB hb)).symm)
  have h16 : v 16 = (↑(node16 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node15 (standardA ha) (standardB hb))
      (node15 (standardA ha) (standardB hb)) (v 16) (v 15) (v 15) c.step16 h15 h15).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node16_spec (standardA ha) (standardB hb)).symm)
  have h17 : v 17 = (↑(node17 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node16 (standardA ha) (standardB hb))
      (node13 (standardA ha) (standardB hb)) (v 17) (v 16) (v 13) c.step17 h16 h13).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node17_spec (standardA ha) (standardB hb)).symm)
  have h18 : v 18 = (↑(node18 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node17 (standardA ha) (standardB hb))
      (node17 (standardA ha) (standardB hb)) (v 18) (v 17) (v 17) c.step18 h17 h17).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node18_spec (standardA ha) (standardB hb)).symm)
  have h19 : v 19 = (↑(node19 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node18 (standardA ha) (standardB hb))
      (node13 (standardA ha) (standardB hb)) (v 19) (v 18) (v 13) c.step19 h18 h13).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node19_spec (standardA ha) (standardB hb)).symm)
  have h20 : v 20 = (↑(node20 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node1 (standardA ha) (standardB hb))
      (node19 (standardA ha) (standardB hb)) (v 20) (v 1) (v 19) c.step20 h1 h19).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node20_spec (standardA ha) (standardB hb)).symm)
  have h21 : v 21 = (↑(node21 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node20 (standardA ha) (standardB hb))
      (node20 (standardA ha) (standardB hb)) (v 21) (v 20) (v 20) c.step21 h20 h20).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node21_spec (standardA ha) (standardB hb)).symm)
  have h22 : v 22 = (↑(node22 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node21 (standardA ha) (standardB hb))
      (node20 (standardA ha) (standardB hb)) (v 22) (v 21) (v 20) c.step22 h21 h20).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node22_spec (standardA ha) (standardB hb)).symm)
  have h23 : v 23 = (↑(node23 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node13 (standardA ha) (standardB hb))
      (node13 (standardA ha) (standardB hb)) (v 23) (v 13) (v 13) c.step23 h13 h13).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node23_spec (standardA ha) (standardB hb)).symm)
  have h24 : v 24 = (↑(node24 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node23 (standardA ha) (standardB hb))
      (node13 (standardA ha) (standardB hb)) (v 24) (v 23) (v 13) c.step24 h23 h13).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node24_spec (standardA ha) (standardB hb)).symm)
  have h25 : v 25 = (↑(node25 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node22 (standardA ha) (standardB hb))
      (node24 (standardA ha) (standardB hb)) (v 25) (v 22) (v 24) c.step25 h22 h24).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node25_spec (standardA ha) (standardB hb)).symm)
  have h26 : v 26 = (↑(node26 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node25 (standardA ha) (standardB hb))
      (node25 (standardA ha) (standardB hb)) (v 26) (v 25) (v 25) c.step26 h25 h25).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node26_spec (standardA ha) (standardB hb)).symm)
  have h27 : v 27 = (↑(node27 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node26 (standardA ha) (standardB hb))
      (node26 (standardA ha) (standardB hb)) (v 27) (v 26) (v 26) c.step27 h26 h26).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node27_spec (standardA ha) (standardB hb)).symm)
  have h28 : v 28 = (↑(node28 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node27 (standardA ha) (standardB hb))
      (node25 (standardA ha) (standardB hb)) (v 28) (v 27) (v 25) c.step28 h27 h25).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node28_spec (standardA ha) (standardB hb)).symm)
  have h29 : v 29 = (↑(node29 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node28 (standardA ha) (standardB hb))
      (node28 (standardA ha) (standardB hb)) (v 29) (v 28) (v 28) c.step29 h28 h28).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node29_spec (standardA ha) (standardB hb)).symm)
  have h30 : v 30 = (↑(node30 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (inv_sound (node13 (standardA ha) (standardB hb)) (v 30) (v 13) c.step30 h13).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node30_spec (standardA ha) (standardB hb)).symm)
  have h31 : v 31 = (↑(node31 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node30 (standardA ha) (standardB hb))
      (node29 (standardA ha) (standardB hb)) (v 31) (v 30) (v 29) c.step31 h30 h29).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node31_spec (standardA ha) (standardB hb)).symm)
  have h32 : v 32 = (↑(node32 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node31 (standardA ha) (standardB hb))
      (node13 (standardA ha) (standardB hb)) (v 32) (v 31) (v 13) c.step32 h31 h13).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node32_spec (standardA ha) (standardB hb)).symm)
  have h33 : v 33 = (↑(node33 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node32 (standardA ha) (standardB hb))
      (node22 (standardA ha) (standardB hb)) (v 33) (v 32) (v 22) c.step33 h32 h22).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node33_spec (standardA ha) (standardB hb)).symm)
  have h34 : v 34 = (↑(node34 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node33 (standardA ha) (standardB hb))
      (node33 (standardA ha) (standardB hb)) (v 34) (v 33) (v 33) c.step34 h33 h33).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node34_spec (standardA ha) (standardB hb)).symm)
  have h35 : v 35 = (↑(node35 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node34 (standardA ha) (standardB hb))
      (node33 (standardA ha) (standardB hb)) (v 35) (v 34) (v 33) c.step35 h34 h33).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node35_spec (standardA ha) (standardB hb)).symm)
  have h36 : v 36 = (↑(node36 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node35 (standardA ha) (standardB hb))
      (node35 (standardA ha) (standardB hb)) (v 36) (v 35) (v 35) c.step36 h35 h35).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node36_spec (standardA ha) (standardB hb)).symm)
  have h37 : v 37 = (↑(node37 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node36 (standardA ha) (standardB hb))
      (node22 (standardA ha) (standardB hb)) (v 37) (v 36) (v 22) c.step37 h36 h22).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node37_spec (standardA ha) (standardB hb)).symm)
  have h38 : v 38 = (↑(node38 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node33 (standardA ha) (standardB hb))
      (node33 (standardA ha) (standardB hb)) (v 38) (v 33) (v 33) c.step38 h33 h33).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node38_spec (standardA ha) (standardB hb)).symm)
  have h39 : v 39 = (↑(node39 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node38 (standardA ha) (standardB hb))
      (node33 (standardA ha) (standardB hb)) (v 39) (v 38) (v 33) c.step39 h38 h33).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node39_spec (standardA ha) (standardB hb)).symm)
  have h40 : v 40 = (↑(node40 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node37 (standardA ha) (standardB hb))
      (node39 (standardA ha) (standardB hb)) (v 40) (v 37) (v 39) c.step40 h37 h39).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node40_spec (standardA ha) (standardB hb)).symm)
  have h41 : v 41 = (↑(node41 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node40 (standardA ha) (standardB hb))
      (node40 (standardA ha) (standardB hb)) (v 41) (v 40) (v 40) c.step41 h40 h40).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node41_spec (standardA ha) (standardB hb)).symm)
  have h42 : v 42 = (↑(node42 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node41 (standardA ha) (standardB hb))
      (node32 (standardA ha) (standardB hb)) (v 42) (v 41) (v 32) c.step42 h41 h32).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node42_spec (standardA ha) (standardB hb)).symm)
  have h43 : v 43 = (↑(node43 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node42 (standardA ha) (standardB hb))
      (node22 (standardA ha) (standardB hb)) (v 43) (v 42) (v 22) c.step43 h42 h22).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node43_spec (standardA ha) (standardB hb)).symm)
  have h44 : v 44 = (↑(node44 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node32 (standardA ha) (standardB hb))
      (node32 (standardA ha) (standardB hb)) (v 44) (v 32) (v 32) c.step44 h32 h32).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node44_spec (standardA ha) (standardB hb)).symm)
  have h45 : v 45 = (↑(node45 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node43 (standardA ha) (standardB hb))
      (node44 (standardA ha) (standardB hb)) (v 45) (v 43) (v 44) c.step45 h43 h44).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node45_spec (standardA ha) (standardB hb)).symm)
  have h46 : v 46 = (↑(node46 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node45 (standardA ha) (standardB hb))
      (node22 (standardA ha) (standardB hb)) (v 46) (v 45) (v 22) c.step46 h45 h22).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node46_spec (standardA ha) (standardB hb)).symm)
  have h47 : v 47 = (↑(node47 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node46 (standardA ha) (standardB hb))
      (node46 (standardA ha) (standardB hb)) (v 47) (v 46) (v 46) c.step47 h46 h46).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node47_spec (standardA ha) (standardB hb)).symm)
  have h48 : v 48 = (↑(node48 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node47 (standardA ha) (standardB hb))
      (node47 (standardA ha) (standardB hb)) (v 48) (v 47) (v 47) c.step48 h47 h47).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node48_spec (standardA ha) (standardB hb)).symm)
  have h49 : v 49 = (↑(node49 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node48 (standardA ha) (standardB hb))
      (node46 (standardA ha) (standardB hb)) (v 49) (v 48) (v 46) c.step49 h48 h46).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node49_spec (standardA ha) (standardB hb)).symm)
  have h50 : v 50 = (↑(node50 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node33 (standardA ha) (standardB hb))
      (node33 (standardA ha) (standardB hb)) (v 50) (v 33) (v 33) c.step50 h33 h33).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node50_spec (standardA ha) (standardB hb)).symm)
  have h51 : v 51 = (↑(node51 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node50 (standardA ha) (standardB hb))
      (node50 (standardA ha) (standardB hb)) (v 51) (v 50) (v 50) c.step51 h50 h50).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node51_spec (standardA ha) (standardB hb)).symm)
  have h52 : v 52 = (↑(node52 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (inv_sound (node51 (standardA ha) (standardB hb)) (v 52) (v 51) c.step52 h51).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node52_spec (standardA ha) (standardB hb)).symm)
  have h53 : v 53 = (↑(node53 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node52 (standardA ha) (standardB hb))
      (node49 (standardA ha) (standardB hb)) (v 53) (v 52) (v 49) c.step53 h52 h49).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node53_spec (standardA ha) (standardB hb)).symm)
  have h54 : v 54 = (↑(node54 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node53 (standardA ha) (standardB hb))
      (node51 (standardA ha) (standardB hb)) (v 54) (v 53) (v 51) c.step54 h53 h51).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node54_spec (standardA ha) (standardB hb)).symm)
  have h55 : v 55 = (↑(node55 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node33 (standardA ha) (standardB hb))
      (node33 (standardA ha) (standardB hb)) (v 55) (v 33) (v 33) c.step55 h33 h33).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node55_spec (standardA ha) (standardB hb)).symm)
  have h56 : v 56 = (↑(node56 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node55 (standardA ha) (standardB hb))
      (node55 (standardA ha) (standardB hb)) (v 56) (v 55) (v 55) c.step56 h55 h55).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node56_spec (standardA ha) (standardB hb)).symm)
  have h57 : v 57 = (↑(node57 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node56 (standardA ha) (standardB hb))
      (node56 (standardA ha) (standardB hb)) (v 57) (v 56) (v 56) c.step57 h56 h56).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node57_spec (standardA ha) (standardB hb)).symm)
  have h58 : v 58 = (↑(node58 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node57 (standardA ha) (standardB hb))
      (node22 (standardA ha) (standardB hb)) (v 58) (v 57) (v 22) c.step58 h57 h22).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node58_spec (standardA ha) (standardB hb)).symm)
  have h59 : v 59 = (↑(node59 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node33 (standardA ha) (standardB hb))
      (node33 (standardA ha) (standardB hb)) (v 59) (v 33) (v 33) c.step59 h33 h33).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node59_spec (standardA ha) (standardB hb)).symm)
  have h60 : v 60 = (↑(node60 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node59 (standardA ha) (standardB hb))
      (node33 (standardA ha) (standardB hb)) (v 60) (v 59) (v 33) c.step60 h59 h33).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node60_spec (standardA ha) (standardB hb)).symm)
  have h61 : v 61 = (↑(node61 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node58 (standardA ha) (standardB hb))
      (node60 (standardA ha) (standardB hb)) (v 61) (v 58) (v 60) c.step61 h58 h60).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node61_spec (standardA ha) (standardB hb)).symm)
  have h62 : v 62 = (↑(node62 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node32 (standardA ha) (standardB hb))
      (node22 (standardA ha) (standardB hb)) (v 62) (v 32) (v 22) c.step62 h32 h22).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node62_spec (standardA ha) (standardB hb)).symm)
  have h63 : v 63 = (↑(node63 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node32 (standardA ha) (standardB hb))
      (node32 (standardA ha) (standardB hb)) (v 63) (v 32) (v 32) c.step63 h32 h32).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node63_spec (standardA ha) (standardB hb)).symm)
  have h64 : v 64 = (↑(node64 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node62 (standardA ha) (standardB hb))
      (node63 (standardA ha) (standardB hb)) (v 64) (v 62) (v 63) c.step64 h62 h63).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node64_spec (standardA ha) (standardB hb)).symm)
  have h65 : v 65 = (↑(node65 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node64 (standardA ha) (standardB hb))
      (node22 (standardA ha) (standardB hb)) (v 65) (v 64) (v 22) c.step65 h64 h22).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node65_spec (standardA ha) (standardB hb)).symm)
  have h66 : v 66 = (↑(node66 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node65 (standardA ha) (standardB hb))
      (node65 (standardA ha) (standardB hb)) (v 66) (v 65) (v 65) c.step66 h65 h65).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node66_spec (standardA ha) (standardB hb)).symm)
  have h67 : v 67 = (↑(node67 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (inv_sound (node66 (standardA ha) (standardB hb)) (v 67) (v 66) c.step67 h66).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node67_spec (standardA ha) (standardB hb)).symm)
  have h68 : v 68 = (↑(node68 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node67 (standardA ha) (standardB hb))
      (node61 (standardA ha) (standardB hb)) (v 68) (v 67) (v 61) c.step68 h67 h61).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node68_spec (standardA ha) (standardB hb)).symm)
  have h69 : v 69 = (↑(node69 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node68 (standardA ha) (standardB hb))
      (node66 (standardA ha) (standardB hb)) (v 69) (v 68) (v 66) c.step69 h68 h66).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node69_spec (standardA ha) (standardB hb)).symm)
  have h70 : v 70 = (↑(node70 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node69 (standardA ha) (standardB hb))
      (node54 (standardA ha) (standardB hb)) (v 70) (v 69) (v 54) c.step70 h69 h54).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node70_spec (standardA ha) (standardB hb)).symm)
  have h71 : v 71 = (↑(node71 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node70 (standardA ha) (standardB hb))
      (node0 (standardA ha) (standardB hb)) (v 71) (v 70) (v 0) c.step71 h70 h0).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node71_spec (standardA ha) (standardB hb)).symm)
  have h72 : v 72 = (↑(node72 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (inv_sound (node71 (standardA ha) (standardB hb)) (v 72) (v 71) c.step72 h71).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node72_spec (standardA ha) (standardB hb)).symm)
  have h73 : v 73 = (↑(node73 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node72 (standardA ha) (standardB hb))
      (node54 (standardA ha) (standardB hb)) (v 73) (v 72) (v 54) c.step73 h72 h54).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node73_spec (standardA ha) (standardB hb)).symm)
  have h74 : v 74 = (↑(node74 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node73 (standardA ha) (standardB hb))
      (node71 (standardA ha) (standardB hb)) (v 74) (v 73) (v 71) c.step74 h73 h71).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node74_spec (standardA ha) (standardB hb)).symm)
  have h75 : v 75 = (↑(node75 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node69 (standardA ha) (standardB hb))
      (node54 (standardA ha) (standardB hb)) (v 75) (v 69) (v 54) c.step75 h69 h54).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node75_spec (standardA ha) (standardB hb)).symm)
  have h76 : v 76 = (↑(node76 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node75 (standardA ha) (standardB hb))
      (node69 (standardA ha) (standardB hb)) (v 76) (v 75) (v 69) c.step76 h75 h69).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node76_spec (standardA ha) (standardB hb)).symm)
  have h77 : v 77 = (↑(node77 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (inv_sound (node76 (standardA ha) (standardB hb)) (v 77) (v 76) c.step77 h76).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node77_spec (standardA ha) (standardB hb)).symm)
  have h78 : v 78 = (↑(node78 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node77 (standardA ha) (standardB hb))
      (node54 (standardA ha) (standardB hb)) (v 78) (v 77) (v 54) c.step78 h77 h54).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node78_spec (standardA ha) (standardB hb)).symm)
  have h79 : v 79 = (↑(node79 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node78 (standardA ha) (standardB hb))
      (node76 (standardA ha) (standardB hb)) (v 79) (v 78) (v 76) c.step79 h78 h76).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node79_spec (standardA ha) (standardB hb)).symm)
  have h80 : v 80 = (↑(node80 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node69 (standardA ha) (standardB hb))
      (node54 (standardA ha) (standardB hb)) (v 80) (v 69) (v 54) c.step80 h69 h54).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node80_spec (standardA ha) (standardB hb)).symm)
  have h81 : v 81 = (↑(node81 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node69 (standardA ha) (standardB hb))
      (node69 (standardA ha) (standardB hb)) (v 81) (v 69) (v 69) c.step81 h69 h69).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node81_spec (standardA ha) (standardB hb)).symm)
  have h82 : v 82 = (↑(node82 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node80 (standardA ha) (standardB hb))
      (node81 (standardA ha) (standardB hb)) (v 82) (v 80) (v 81) c.step82 h80 h81).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node82_spec (standardA ha) (standardB hb)).symm)
  have h83 : v 83 = (↑(node83 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (inv_sound (node82 (standardA ha) (standardB hb)) (v 83) (v 82) c.step83 h82).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node83_spec (standardA ha) (standardB hb)).symm)
  have h84 : v 84 = (↑(node84 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node83 (standardA ha) (standardB hb))
      (node54 (standardA ha) (standardB hb)) (v 84) (v 83) (v 54) c.step84 h83 h54).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node84_spec (standardA ha) (standardB hb)).symm)
  have h85 : v 85 = (↑(node85 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node84 (standardA ha) (standardB hb))
      (node82 (standardA ha) (standardB hb)) (v 85) (v 84) (v 82) c.step85 h84 h82).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node85_spec (standardA ha) (standardB hb)).symm)
  have h86 : v 86 = (↑(node86 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node69 (standardA ha) (standardB hb))
      (node54 (standardA ha) (standardB hb)) (v 86) (v 69) (v 54) c.step86 h69 h54).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node86_spec (standardA ha) (standardB hb)).symm)
  have h87 : v 87 = (↑(node87 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node69 (standardA ha) (standardB hb))
      (node69 (standardA ha) (standardB hb)) (v 87) (v 69) (v 69) c.step87 h69 h69).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node87_spec (standardA ha) (standardB hb)).symm)
  have h88 : v 88 = (↑(node88 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node87 (standardA ha) (standardB hb))
      (node69 (standardA ha) (standardB hb)) (v 88) (v 87) (v 69) c.step88 h87 h69).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node88_spec (standardA ha) (standardB hb)).symm)
  have h89 : v 89 = (↑(node89 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node86 (standardA ha) (standardB hb))
      (node88 (standardA ha) (standardB hb)) (v 89) (v 86) (v 88) c.step89 h86 h88).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node89_spec (standardA ha) (standardB hb)).symm)
  have h90 : v 90 = (↑(node90 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (inv_sound (node89 (standardA ha) (standardB hb)) (v 90) (v 89) c.step90 h89).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node90_spec (standardA ha) (standardB hb)).symm)
  have h91 : v 91 = (↑(node91 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node90 (standardA ha) (standardB hb))
      (node54 (standardA ha) (standardB hb)) (v 91) (v 90) (v 54) c.step91 h90 h54).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node91_spec (standardA ha) (standardB hb)).symm)
  have h92 : v 92 = (↑(node92 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node91 (standardA ha) (standardB hb))
      (node89 (standardA ha) (standardB hb)) (v 92) (v 91) (v 89) c.step92 h91 h89).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node92_spec (standardA ha) (standardB hb)).symm)
  have h93 : v 93 = (↑(node93 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node69 (standardA ha) (standardB hb))
      (node54 (standardA ha) (standardB hb)) (v 93) (v 69) (v 54) c.step93 h69 h54).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node93_spec (standardA ha) (standardB hb)).symm)
  have h94 : v 94 = (↑(node94 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node69 (standardA ha) (standardB hb))
      (node69 (standardA ha) (standardB hb)) (v 94) (v 69) (v 69) c.step94 h69 h69).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node94_spec (standardA ha) (standardB hb)).symm)
  have h95 : v 95 = (↑(node95 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node94 (standardA ha) (standardB hb))
      (node94 (standardA ha) (standardB hb)) (v 95) (v 94) (v 94) c.step95 h94 h94).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node95_spec (standardA ha) (standardB hb)).symm)
  have h96 : v 96 = (↑(node96 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node93 (standardA ha) (standardB hb))
      (node95 (standardA ha) (standardB hb)) (v 96) (v 93) (v 95) c.step96 h93 h95).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node96_spec (standardA ha) (standardB hb)).symm)
  have h97 : v 97 = (↑(node97 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (inv_sound (node96 (standardA ha) (standardB hb)) (v 97) (v 96) c.step97 h96).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node97_spec (standardA ha) (standardB hb)).symm)
  have h98 : v 98 = (↑(node98 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node97 (standardA ha) (standardB hb))
      (node54 (standardA ha) (standardB hb)) (v 98) (v 97) (v 54) c.step98 h97 h54).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node98_spec (standardA ha) (standardB hb)).symm)
  have h99 : v 99 = (↑(node99 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node98 (standardA ha) (standardB hb))
      (node96 (standardA ha) (standardB hb)) (v 99) (v 98) (v 96) c.step99 h98 h96).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node99_spec (standardA ha) (standardB hb)).symm)
  have h100 : v 100 = (↑(node100 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node69 (standardA ha) (standardB hb))
      (node54 (standardA ha) (standardB hb)) (v 100) (v 69) (v 54) c.step100 h69 h54).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node100_spec (standardA ha) (standardB hb)).symm)
  have h101 : v 101 = (↑(node101 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node69 (standardA ha) (standardB hb))
      (node69 (standardA ha) (standardB hb)) (v 101) (v 69) (v 69) c.step101 h69 h69).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node101_spec (standardA ha) (standardB hb)).symm)
  have h102 : v 102 = (↑(node102 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node101 (standardA ha) (standardB hb))
      (node101 (standardA ha) (standardB hb)) (v 102) (v 101) (v 101) c.step102 h101 h101).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node102_spec (standardA ha) (standardB hb)).symm)
  have h103 : v 103 = (↑(node103 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node102 (standardA ha) (standardB hb))
      (node69 (standardA ha) (standardB hb)) (v 103) (v 102) (v 69) c.step103 h102 h69).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node103_spec (standardA ha) (standardB hb)).symm)
  have h104 : v 104 = (↑(node104 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node100 (standardA ha) (standardB hb))
      (node103 (standardA ha) (standardB hb)) (v 104) (v 100) (v 103) c.step104 h100 h103).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node104_spec (standardA ha) (standardB hb)).symm)
  have h105 : v 105 = (↑(node105 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (inv_sound (node104 (standardA ha) (standardB hb)) (v 105) (v 104) c.step105 h104).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node105_spec (standardA ha) (standardB hb)).symm)
  have h106 : v 106 = (↑(node106 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node105 (standardA ha) (standardB hb))
      (node54 (standardA ha) (standardB hb)) (v 106) (v 105) (v 54) c.step106 h105 h54).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node106_spec (standardA ha) (standardB hb)).symm)
  have h107 : v 107 = (↑(node107 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node106 (standardA ha) (standardB hb))
      (node104 (standardA ha) (standardB hb)) (v 107) (v 106) (v 104) c.step107 h106 h104).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node107_spec (standardA ha) (standardB hb)).symm)
  have h108 : v 108 = (↑(node108 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node69 (standardA ha) (standardB hb))
      (node54 (standardA ha) (standardB hb)) (v 108) (v 69) (v 54) c.step108 h69 h54).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node108_spec (standardA ha) (standardB hb)).symm)
  have h109 : v 109 = (↑(node109 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node69 (standardA ha) (standardB hb))
      (node69 (standardA ha) (standardB hb)) (v 109) (v 69) (v 69) c.step109 h69 h69).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node109_spec (standardA ha) (standardB hb)).symm)
  have h110 : v 110 = (↑(node110 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node109 (standardA ha) (standardB hb))
      (node69 (standardA ha) (standardB hb)) (v 110) (v 109) (v 69) c.step110 h109 h69).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node110_spec (standardA ha) (standardB hb)).symm)
  have h111 : v 111 = (↑(node111 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node110 (standardA ha) (standardB hb))
      (node110 (standardA ha) (standardB hb)) (v 111) (v 110) (v 110) c.step111 h110 h110).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node111_spec (standardA ha) (standardB hb)).symm)
  have h112 : v 112 = (↑(node112 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node108 (standardA ha) (standardB hb))
      (node111 (standardA ha) (standardB hb)) (v 112) (v 108) (v 111) c.step112 h108 h111).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node112_spec (standardA ha) (standardB hb)).symm)
  have h113 : v 113 = (↑(node113 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (inv_sound (node112 (standardA ha) (standardB hb)) (v 113) (v 112) c.step113 h112).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node113_spec (standardA ha) (standardB hb)).symm)
  have h114 : v 114 = (↑(node114 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node113 (standardA ha) (standardB hb))
      (node54 (standardA ha) (standardB hb)) (v 114) (v 113) (v 54) c.step114 h113 h54).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node114_spec (standardA ha) (standardB hb)).symm)
  have h115 : v 115 = (↑(node115 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node114 (standardA ha) (standardB hb))
      (node112 (standardA ha) (standardB hb)) (v 115) (v 114) (v 112) c.step115 h114 h112).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node115_spec (standardA ha) (standardB hb)).symm)
  have h116 : v 116 = (↑(node116 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node6 (standardA ha) (standardB hb))
      (node6 (standardA ha) (standardB hb)) (v 116) (v 6) (v 6) c.step116 h6 h6).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node116_spec (standardA ha) (standardB hb)).symm)
  have h117 : v 117 = (↑(node117 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node116 (standardA ha) (standardB hb))
      (node116 (standardA ha) (standardB hb)) (v 117) (v 116) (v 116) c.step117 h116 h116).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node117_spec (standardA ha) (standardB hb)).symm)
  have h118 : v 118 = (↑(node118 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node117 (standardA ha) (standardB hb))
      (node6 (standardA ha) (standardB hb)) (v 118) (v 117) (v 6) c.step118 h117 h6).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node118_spec (standardA ha) (standardB hb)).symm)
  have h119 : v 119 = (↑(node119 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node118 (standardA ha) (standardB hb))
      (node19 (standardA ha) (standardB hb)) (v 119) (v 118) (v 19) c.step119 h118 h19).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node119_spec (standardA ha) (standardB hb)).symm)
  have h120 : v 120 = (↑(node120 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (inv_sound (node118 (standardA ha) (standardB hb)) (v 120) (v 118) c.step120 h118).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node120_spec (standardA ha) (standardB hb)).symm)
  have h121 : v 121 = (↑(node121 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node119 (standardA ha) (standardB hb))
      (node120 (standardA ha) (standardB hb)) (v 121) (v 119) (v 120) c.step121 h119 h120).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node121_spec (standardA ha) (standardB hb)).symm)
  have h122 : v 122 = (↑(node122 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node121 (standardA ha) (standardB hb))
      (node54 (standardA ha) (standardB hb)) (v 122) (v 121) (v 54) c.step122 h121 h54).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node122_spec (standardA ha) (standardB hb)).symm)
  have h123 : v 123 = (↑(node123 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node122 (standardA ha) (standardB hb))
      (node118 (standardA ha) (standardB hb)) (v 123) (v 122) (v 118) c.step123 h122 h118).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node123_spec (standardA ha) (standardB hb)).symm)
  have h124 : v 124 = (↑(node124 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (inv_sound (node123 (standardA ha) (standardB hb)) (v 124) (v 123) c.step124 h123).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node124_spec (standardA ha) (standardB hb)).symm)
  have h125 : v 125 = (↑(node125 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node123 (standardA ha) (standardB hb))
      (node13 (standardA ha) (standardB hb)) (v 125) (v 123) (v 13) c.step125 h123 h13).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node125_spec (standardA ha) (standardB hb)).symm)
  have h126 : v 126 = (↑(node126 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node125 (standardA ha) (standardB hb))
      (node124 (standardA ha) (standardB hb)) (v 126) (v 125) (v 124) c.step126 h125 h124).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node126_spec (standardA ha) (standardB hb)).symm)
  have h127 : v 127 = (↑(node127 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node126 (standardA ha) (standardB hb))
      (node126 (standardA ha) (standardB hb)) (v 127) (v 126) (v 126) c.step127 h126 h126).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node127_spec (standardA ha) (standardB hb)).symm)
  have h128 : v 128 = (↑(node128 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (inv_sound (node127 (standardA ha) (standardB hb)) (v 128) (v 127) c.step128 h127).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node128_spec (standardA ha) (standardB hb)).symm)
  have h129 : v 129 = (↑(node129 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node128 (standardA ha) (standardB hb))
      (node92 (standardA ha) (standardB hb)) (v 129) (v 128) (v 92) c.step129 h128 h92).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node129_spec (standardA ha) (standardB hb)).symm)
  have h130 : v 130 = (↑(node130 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node129 (standardA ha) (standardB hb))
      (node127 (standardA ha) (standardB hb)) (v 130) (v 129) (v 127) c.step130 h129 h127).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node130_spec (standardA ha) (standardB hb)).symm)
  have h131 : v 131 = (↑(node131 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node79 (standardA ha) (standardB hb))
      (node85 (standardA ha) (standardB hb)) (v 131) (v 79) (v 85) c.step131 h79 h85).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node131_spec (standardA ha) (standardB hb)).symm)
  have h132 : v 132 = (↑(node132 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (inv_sound (node130 (standardA ha) (standardB hb)) (v 132) (v 130) c.step132 h130).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node132_spec (standardA ha) (standardB hb)).symm)
  have h133 : v 133 = (↑(node133 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (inv_sound (node131 (standardA ha) (standardB hb)) (v 133) (v 131) c.step133 h131).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node133_spec (standardA ha) (standardB hb)).symm)
  have h134 : v 134 = (↑(node134 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node132 (standardA ha) (standardB hb))
      (node133 (standardA ha) (standardB hb)) (v 134) (v 132) (v 133) c.step134 h132 h133).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node134_spec (standardA ha) (standardB hb)).symm)
  have h135 : v 135 = (↑(node135 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node134 (standardA ha) (standardB hb))
      (node130 (standardA ha) (standardB hb)) (v 135) (v 134) (v 130) c.step135 h134 h130).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node135_spec (standardA ha) (standardB hb)).symm)
  have h136 : v 136 = (↑(node136 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node135 (standardA ha) (standardB hb))
      (node131 (standardA ha) (standardB hb)) (v 136) (v 135) (v 131) c.step136 h135 h131).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node136_spec (standardA ha) (standardB hb)).symm)
  have h137 : v 137 = (↑(node137 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node126 (standardA ha) (standardB hb))
      (node126 (standardA ha) (standardB hb)) (v 137) (v 126) (v 126) c.step137 h126 h126).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node137_spec (standardA ha) (standardB hb)).symm)
  have h138 : v 138 = (↑(node138 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node137 (standardA ha) (standardB hb))
      (node137 (standardA ha) (standardB hb)) (v 138) (v 137) (v 137) c.step138 h137 h137).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node138_spec (standardA ha) (standardB hb)).symm)
  have h139 : v 139 = (↑(node139 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node138 (standardA ha) (standardB hb))
      (node126 (standardA ha) (standardB hb)) (v 139) (v 138) (v 126) c.step139 h138 h126).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node139_spec (standardA ha) (standardB hb)).symm)
  have h140 : v 140 = (↑(node140 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (inv_sound (node139 (standardA ha) (standardB hb)) (v 140) (v 139) c.step140 h139).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node140_spec (standardA ha) (standardB hb)).symm)
  have h141 : v 141 = (↑(node141 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node140 (standardA ha) (standardB hb))
      (node92 (standardA ha) (standardB hb)) (v 141) (v 140) (v 92) c.step141 h140 h92).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node141_spec (standardA ha) (standardB hb)).symm)
  have h142 : v 142 = (↑(node142 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node141 (standardA ha) (standardB hb))
      (node139 (standardA ha) (standardB hb)) (v 142) (v 141) (v 139) c.step142 h141 h139).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node142_spec (standardA ha) (standardB hb)).symm)
  have h143 : v 143 = (↑(node143 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node79 (standardA ha) (standardB hb))
      (node85 (standardA ha) (standardB hb)) (v 143) (v 79) (v 85) c.step143 h79 h85).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node143_spec (standardA ha) (standardB hb)).symm)
  have h144 : v 144 = (↑(node144 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (inv_sound (node142 (standardA ha) (standardB hb)) (v 144) (v 142) c.step144 h142).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node144_spec (standardA ha) (standardB hb)).symm)
  have h145 : v 145 = (↑(node145 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (inv_sound (node143 (standardA ha) (standardB hb)) (v 145) (v 143) c.step145 h143).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node145_spec (standardA ha) (standardB hb)).symm)
  have h146 : v 146 = (↑(node146 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node144 (standardA ha) (standardB hb))
      (node145 (standardA ha) (standardB hb)) (v 146) (v 144) (v 145) c.step146 h144 h145).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node146_spec (standardA ha) (standardB hb)).symm)
  have h147 : v 147 = (↑(node147 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node146 (standardA ha) (standardB hb))
      (node142 (standardA ha) (standardB hb)) (v 147) (v 146) (v 142) c.step147 h146 h142).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node147_spec (standardA ha) (standardB hb)).symm)
  have h148 : v 148 = (↑(node148 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node147 (standardA ha) (standardB hb))
      (node143 (standardA ha) (standardB hb)) (v 148) (v 147) (v 143) c.step148 h147 h143).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node148_spec (standardA ha) (standardB hb)).symm)
  have h149 : v 149 = (↑(node149 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node136 (standardA ha) (standardB hb))
      (node148 (standardA ha) (standardB hb)) (v 149) (v 136) (v 148) c.step149 h136 h148).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node149_spec (standardA ha) (standardB hb)).symm)
  have h150 : v 150 = (↑(node150 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (inv_sound (node149 (standardA ha) (standardB hb)) (v 150) (v 149) c.step150 h149).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node150_spec (standardA ha) (standardB hb)).symm)
  have h151 : v 151 = (↑(node151 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node150 (standardA ha) (standardB hb))
      (node115 (standardA ha) (standardB hb)) (v 151) (v 150) (v 115) c.step151 h150 h115).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node151_spec (standardA ha) (standardB hb)).symm)
  have h152 : v 152 = (↑(node152 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node151 (standardA ha) (standardB hb))
      (node149 (standardA ha) (standardB hb)) (v 152) (v 151) (v 149) c.step152 h151 h149).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node152_spec (standardA ha) (standardB hb)).symm)
  have h153 : v 153 = (↑(node153 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node99 (standardA ha) (standardB hb))
      (node107 (standardA ha) (standardB hb)) (v 153) (v 99) (v 107) c.step153 h99 h107).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node153_spec (standardA ha) (standardB hb)).symm)
  have h154 : v 154 = (↑(node154 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (inv_sound (node152 (standardA ha) (standardB hb)) (v 154) (v 152) c.step154 h152).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node154_spec (standardA ha) (standardB hb)).symm)
  have h155 : v 155 = (↑(node155 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (inv_sound (node153 (standardA ha) (standardB hb)) (v 155) (v 153) c.step155 h153).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node155_spec (standardA ha) (standardB hb)).symm)
  have h156 : v 156 = (↑(node156 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node154 (standardA ha) (standardB hb))
      (node155 (standardA ha) (standardB hb)) (v 156) (v 154) (v 155) c.step156 h154 h155).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node156_spec (standardA ha) (standardB hb)).symm)
  have h157 : v 157 = (↑(node157 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node156 (standardA ha) (standardB hb))
      (node152 (standardA ha) (standardB hb)) (v 157) (v 156) (v 152) c.step157 h156 h152).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node157_spec (standardA ha) (standardB hb)).symm)
  have h158 : v 158 = (↑(node158 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node157 (standardA ha) (standardB hb))
      (node153 (standardA ha) (standardB hb)) (v 158) (v 157) (v 153) c.step158 h157 h153).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node158_spec (standardA ha) (standardB hb)).symm)
  have h159 : v 159 = (↑(node159 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node148 (standardA ha) (standardB hb))
      (node136 (standardA ha) (standardB hb)) (v 159) (v 148) (v 136) c.step159 h148 h136).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node159_spec (standardA ha) (standardB hb)).symm)
  have h160 : v 160 = (↑(node160 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (inv_sound (node159 (standardA ha) (standardB hb)) (v 160) (v 159) c.step160 h159).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node160_spec (standardA ha) (standardB hb)).symm)
  have h161 : v 161 = (↑(node161 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node160 (standardA ha) (standardB hb))
      (node115 (standardA ha) (standardB hb)) (v 161) (v 160) (v 115) c.step161 h160 h115).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node161_spec (standardA ha) (standardB hb)).symm)
  have h162 : v 162 = (↑(node162 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node161 (standardA ha) (standardB hb))
      (node159 (standardA ha) (standardB hb)) (v 162) (v 161) (v 159) c.step162 h161 h159).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node162_spec (standardA ha) (standardB hb)).symm)
  have h163 : v 163 = (↑(node163 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node99 (standardA ha) (standardB hb))
      (node107 (standardA ha) (standardB hb)) (v 163) (v 99) (v 107) c.step163 h99 h107).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node163_spec (standardA ha) (standardB hb)).symm)
  have h164 : v 164 = (↑(node164 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (inv_sound (node162 (standardA ha) (standardB hb)) (v 164) (v 162) c.step164 h162).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node164_spec (standardA ha) (standardB hb)).symm)
  have h165 : v 165 = (↑(node165 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (inv_sound (node163 (standardA ha) (standardB hb)) (v 165) (v 163) c.step165 h163).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node165_spec (standardA ha) (standardB hb)).symm)
  have h166 : v 166 = (↑(node166 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node164 (standardA ha) (standardB hb))
      (node165 (standardA ha) (standardB hb)) (v 166) (v 164) (v 165) c.step166 h164 h165).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node166_spec (standardA ha) (standardB hb)).symm)
  have h167 : v 167 = (↑(node167 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node166 (standardA ha) (standardB hb))
      (node162 (standardA ha) (standardB hb)) (v 167) (v 166) (v 162) c.step167 h166 h162).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node167_spec (standardA ha) (standardB hb)).symm)
  have h168 : v 168 = (↑(node168 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node167 (standardA ha) (standardB hb))
      (node163 (standardA ha) (standardB hb)) (v 168) (v 167) (v 163) c.step168 h167 h163).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node168_spec (standardA ha) (standardB hb)).symm)
  have h169 : v 169 = (↑(node169 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node158 (standardA ha) (standardB hb))
      (node168 (standardA ha) (standardB hb)) (v 169) (v 158) (v 168) c.step169 h158 h168).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node169_spec (standardA ha) (standardB hb)).symm)
  have h170 : v 170 = (↑(node170 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node136 (standardA ha) (standardB hb))
      (node148 (standardA ha) (standardB hb)) (v 170) (v 136) (v 148) c.step170 h136 h148).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node170_spec (standardA ha) (standardB hb)).symm)
  have h171 : v 171 = (↑(node171 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node170 (standardA ha) (standardB hb))
      (node170 (standardA ha) (standardB hb)) (v 171) (v 170) (v 170) c.step171 h170 h170).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node171_spec (standardA ha) (standardB hb)).symm)
  have h172 : v 172 = (↑(node172 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node171 (standardA ha) (standardB hb))
      (node171 (standardA ha) (standardB hb)) (v 172) (v 171) (v 171) c.step172 h171 h171).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node172_spec (standardA ha) (standardB hb)).symm)
  have h173 : v 173 = (↑(node173 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (inv_sound (node172 (standardA ha) (standardB hb)) (v 173) (v 172) c.step173 h172).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node173_spec (standardA ha) (standardB hb)).symm)
  have h174 : v 174 = (↑(node174 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node173 (standardA ha) (standardB hb))
      (node115 (standardA ha) (standardB hb)) (v 174) (v 173) (v 115) c.step174 h173 h115).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node174_spec (standardA ha) (standardB hb)).symm)
  have h175 : v 175 = (↑(node175 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node174 (standardA ha) (standardB hb))
      (node172 (standardA ha) (standardB hb)) (v 175) (v 174) (v 172) c.step175 h174 h172).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node175_spec (standardA ha) (standardB hb)).symm)
  have h176 : v 176 = (↑(node176 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node99 (standardA ha) (standardB hb))
      (node107 (standardA ha) (standardB hb)) (v 176) (v 99) (v 107) c.step176 h99 h107).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node176_spec (standardA ha) (standardB hb)).symm)
  have h177 : v 177 = (↑(node177 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (inv_sound (node175 (standardA ha) (standardB hb)) (v 177) (v 175) c.step177 h175).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node177_spec (standardA ha) (standardB hb)).symm)
  have h178 : v 178 = (↑(node178 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (inv_sound (node176 (standardA ha) (standardB hb)) (v 178) (v 176) c.step178 h176).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node178_spec (standardA ha) (standardB hb)).symm)
  have h179 : v 179 = (↑(node179 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node177 (standardA ha) (standardB hb))
      (node178 (standardA ha) (standardB hb)) (v 179) (v 177) (v 178) c.step179 h177 h178).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node179_spec (standardA ha) (standardB hb)).symm)
  have h180 : v 180 = (↑(node180 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node179 (standardA ha) (standardB hb))
      (node175 (standardA ha) (standardB hb)) (v 180) (v 179) (v 175) c.step180 h179 h175).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node180_spec (standardA ha) (standardB hb)).symm)
  have h181 : v 181 = (↑(node181 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node180 (standardA ha) (standardB hb))
      (node176 (standardA ha) (standardB hb)) (v 181) (v 180) (v 176) c.step181 h180 h176).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node181_spec (standardA ha) (standardB hb)).symm)
  have h182 : v 182 = (↑(node182 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node136 (standardA ha) (standardB hb))
      (node148 (standardA ha) (standardB hb)) (v 182) (v 136) (v 148) c.step182 h136 h148).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node182_spec (standardA ha) (standardB hb)).symm)
  have h183 : v 183 = (↑(node183 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node182 (standardA ha) (standardB hb))
      (node182 (standardA ha) (standardB hb)) (v 183) (v 182) (v 182) c.step183 h182 h182).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node183_spec (standardA ha) (standardB hb)).symm)
  have h184 : v 184 = (↑(node184 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node183 (standardA ha) (standardB hb))
      (node182 (standardA ha) (standardB hb)) (v 184) (v 183) (v 182) c.step184 h183 h182).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node184_spec (standardA ha) (standardB hb)).symm)
  have h185 : v 185 = (↑(node185 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node184 (standardA ha) (standardB hb))
      (node148 (standardA ha) (standardB hb)) (v 185) (v 184) (v 148) c.step185 h184 h148).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node185_spec (standardA ha) (standardB hb)).symm)
  have h186 : v 186 = (↑(node186 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node185 (standardA ha) (standardB hb))
      (node136 (standardA ha) (standardB hb)) (v 186) (v 185) (v 136) c.step186 h185 h136).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node186_spec (standardA ha) (standardB hb)).symm)
  have h187 : v 187 = (↑(node187 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (inv_sound (node186 (standardA ha) (standardB hb)) (v 187) (v 186) c.step187 h186).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node187_spec (standardA ha) (standardB hb)).symm)
  have h188 : v 188 = (↑(node188 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node187 (standardA ha) (standardB hb))
      (node115 (standardA ha) (standardB hb)) (v 188) (v 187) (v 115) c.step188 h187 h115).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node188_spec (standardA ha) (standardB hb)).symm)
  have h189 : v 189 = (↑(node189 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node188 (standardA ha) (standardB hb))
      (node186 (standardA ha) (standardB hb)) (v 189) (v 188) (v 186) c.step189 h188 h186).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node189_spec (standardA ha) (standardB hb)).symm)
  have h190 : v 190 = (↑(node190 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node169 (standardA ha) (standardB hb))
      (node181 (standardA ha) (standardB hb)) (v 190) (v 169) (v 181) c.step190 h169 h181).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node190_spec (standardA ha) (standardB hb)).symm)
  have h191 : v 191 = (↑(node191 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node190 (standardA ha) (standardB hb))
      (node189 (standardA ha) (standardB hb)) (v 191) (v 190) (v 189) c.step191 h190 h189).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node191_spec (standardA ha) (standardB hb)).symm)
  have h192 : v 192 = (↑(node192 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node191 (standardA ha) (standardB hb))
      (node191 (standardA ha) (standardB hb)) (v 192) (v 191) (v 191) c.step192 h191 h191).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node192_spec (standardA ha) (standardB hb)).symm)
  have h193 : v 193 = (↑(node193 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node192 (standardA ha) (standardB hb))
      (node191 (standardA ha) (standardB hb)) (v 193) (v 192) (v 191) c.step193 h192 h191).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node193_spec (standardA ha) (standardB hb)).symm)
  have h194 : v 194 = (↑(node194 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node193 (standardA ha) (standardB hb))
      (node181 (standardA ha) (standardB hb)) (v 194) (v 193) (v 181) c.step194 h193 h181).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node194_spec (standardA ha) (standardB hb)).symm)
  have h195 : v 195 = (↑(node195 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node194 (standardA ha) (standardB hb))
      (node189 (standardA ha) (standardB hb)) (v 195) (v 194) (v 189) c.step195 h194 h189).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node195_spec (standardA ha) (standardB hb)).symm)
  have h196 : v 196 = (↑(node196 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node195 (standardA ha) (standardB hb))
      (node195 (standardA ha) (standardB hb)) (v 196) (v 195) (v 195) c.step196 h195 h195).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node196_spec (standardA ha) (standardB hb)).symm)
  have h197 : v 197 = (↑(node197 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node196 (standardA ha) (standardB hb))
      (node196 (standardA ha) (standardB hb)) (v 197) (v 196) (v 196) c.step197 h196 h196).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node197_spec (standardA ha) (standardB hb)).symm)
  have h198 : v 198 = (↑(node198 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (inv_sound (node197 (standardA ha) (standardB hb)) (v 198) (v 197) c.step198 h197).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node198_spec (standardA ha) (standardB hb)).symm)
  have h199 : v 199 = (↑(node199 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node198 (standardA ha) (standardB hb))
      (node189 (standardA ha) (standardB hb)) (v 199) (v 198) (v 189) c.step199 h198 h189).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node199_spec (standardA ha) (standardB hb)).symm)
  have h200 : v 200 = (↑(node200 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node199 (standardA ha) (standardB hb))
      (node197 (standardA ha) (standardB hb)) (v 200) (v 199) (v 197) c.step200 h199 h197).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node200_spec (standardA ha) (standardB hb)).symm)
  have h201 : v 201 = (↑(node201 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (inv_sound (node195 (standardA ha) (standardB hb)) (v 201) (v 195) c.step201 h195).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node201_spec (standardA ha) (standardB hb)).symm)
  have h202 : v 202 = (↑(node202 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node201 (standardA ha) (standardB hb))
      (node200 (standardA ha) (standardB hb)) (v 202) (v 201) (v 200) c.step202 h201 h200).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node202_spec (standardA ha) (standardB hb)).symm)
  have h203 : v 203 = (↑(node203 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node202 (standardA ha) (standardB hb))
      (node195 (standardA ha) (standardB hb)) (v 203) (v 202) (v 195) c.step203 h202 h195).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node203_spec (standardA ha) (standardB hb)).symm)
  have h204 : v 204 = (↑(node204 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node203 (standardA ha) (standardB hb))
      (node200 (standardA ha) (standardB hb)) (v 204) (v 203) (v 200) c.step204 h203 h200).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node204_spec (standardA ha) (standardB hb)).symm)
  have h205 : v 205 = (↑(node205 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node204 (standardA ha) (standardB hb))
      (node189 (standardA ha) (standardB hb)) (v 205) (v 204) (v 189) c.step205 h204 h189).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node205_spec (standardA ha) (standardB hb)).symm)
  have h206 : v 206 = (↑(node206 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node205 (standardA ha) (standardB hb))
      (node200 (standardA ha) (standardB hb)) (v 206) (v 205) (v 200) c.step206 h205 h200).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node206_spec (standardA ha) (standardB hb)).symm)
  have h207 : v 207 = (↑(node207 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node206 (standardA ha) (standardB hb))
      (node203 (standardA ha) (standardB hb)) (v 207) (v 206) (v 203) c.step207 h206 h203).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node207_spec (standardA ha) (standardB hb)).symm)
  have h208 : v 208 = (↑(node208 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node189 (standardA ha) (standardB hb))
      (node200 (standardA ha) (standardB hb)) (v 208) (v 189) (v 200) c.step208 h189 h200).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node208_spec (standardA ha) (standardB hb)).symm)
  have h209 : v 209 = (↑(node209 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node208 (standardA ha) (standardB hb))
      (node207 (standardA ha) (standardB hb)) (v 209) (v 208) (v 207) c.step209 h208 h207).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node209_spec (standardA ha) (standardB hb)).symm)
  have h210 : v 210 = (↑(node210 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node209 (standardA ha) (standardB hb))
      (node200 (standardA ha) (standardB hb)) (v 210) (v 209) (v 200) c.step210 h209 h200).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node210_spec (standardA ha) (standardB hb)).symm)
  have h211 : v 211 = (↑(node211 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node210 (standardA ha) (standardB hb))
      (node189 (standardA ha) (standardB hb)) (v 211) (v 210) (v 189) c.step211 h210 h189).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node211_spec (standardA ha) (standardB hb)).symm)
  have h212 : v 212 = (↑(node212 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node54 (standardA ha) (standardB hb))
      (node74 (standardA ha) (standardB hb)) (v 212) (v 54) (v 74) c.step212 h54 h74).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node212_spec (standardA ha) (standardB hb)).symm)
  have h213 : v 213 = (↑(node213 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node212 (standardA ha) (standardB hb))
      (node79 (standardA ha) (standardB hb)) (v 213) (v 212) (v 79) c.step213 h212 h79).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node213_spec (standardA ha) (standardB hb)).symm)
  have h214 : v 214 = (↑(node214 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node213 (standardA ha) (standardB hb))
      (node85 (standardA ha) (standardB hb)) (v 214) (v 213) (v 85) c.step214 h213 h85).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node214_spec (standardA ha) (standardB hb)).symm)
  have h215 : v 215 = (↑(node215 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node214 (standardA ha) (standardB hb))
      (node92 (standardA ha) (standardB hb)) (v 215) (v 214) (v 92) c.step215 h214 h92).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node215_spec (standardA ha) (standardB hb)).symm)
  have h216 : v 216 = (↑(node216 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node215 (standardA ha) (standardB hb))
      (node99 (standardA ha) (standardB hb)) (v 216) (v 215) (v 99) c.step216 h215 h99).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node216_spec (standardA ha) (standardB hb)).symm)
  have h217 : v 217 = (↑(node217 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node216 (standardA ha) (standardB hb))
      (node107 (standardA ha) (standardB hb)) (v 217) (v 216) (v 107) c.step217 h216 h107).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node217_spec (standardA ha) (standardB hb)).symm)
  have h218 : v 218 = (↑(node218 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node217 (standardA ha) (standardB hb))
      (node115 (standardA ha) (standardB hb)) (v 218) (v 217) (v 115) c.step218 h217 h115).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node218_spec (standardA ha) (standardB hb)).symm)
  have h219 : v 219 = (↑(node219 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node92 (standardA ha) (standardB hb))
      (node211 (standardA ha) (standardB hb)) (v 219) (v 92) (v 211) c.step219 h92 h211).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node219_spec (standardA ha) (standardB hb)).symm)
  have h220 : v 220 = (↑(node220 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node219 (standardA ha) (standardB hb))
      (node207 (standardA ha) (standardB hb)) (v 220) (v 219) (v 207) c.step220 h219 h207).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node220_spec (standardA ha) (standardB hb)).symm)
  have h221 : v 221 = (↑(node221 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node220 (standardA ha) (standardB hb))
      (node19 (standardA ha) (standardB hb)) (v 221) (v 220) (v 19) c.step221 h220 h19).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node221_spec (standardA ha) (standardB hb)).symm)
  have h222 : v 222 = (↑(node222 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node218 (standardA ha) (standardB hb))
      (node218 (standardA ha) (standardB hb)) (v 222) (v 218) (v 218) c.step222 h218 h218).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node222_spec (standardA ha) (standardB hb)).symm)
  have h223 : v 223 = (↑(node223 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node222 (standardA ha) (standardB hb))
      (node218 (standardA ha) (standardB hb)) (v 223) (v 222) (v 218) c.step223 h222 h218).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node223_spec (standardA ha) (standardB hb)).symm)
  have h224 : v 224 = (↑(node224 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node223 (standardA ha) (standardB hb))
      (node223 (standardA ha) (standardB hb)) (v 224) (v 223) (v 223) c.step224 h223 h223).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node224_spec (standardA ha) (standardB hb)).symm)
  have h225 : v 225 = (↑(node225 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node224 (standardA ha) (standardB hb))
      (node218 (standardA ha) (standardB hb)) (v 225) (v 224) (v 218) c.step225 h224 h218).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node225_spec (standardA ha) (standardB hb)).symm)
  have h226 : v 226 = (↑(node226 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node225 (standardA ha) (standardB hb))
      (node221 (standardA ha) (standardB hb)) (v 226) (v 225) (v 221) c.step226 h225 h221).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node226_spec (standardA ha) (standardB hb)).symm)
  have h227 : v 227 = (↑(node227 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node226 (standardA ha) (standardB hb))
      (node226 (standardA ha) (standardB hb)) (v 227) (v 226) (v 226) c.step227 h226 h226).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node227_spec (standardA ha) (standardB hb)).symm)
  have h228 : v 228 = (↑(node228 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node227 (standardA ha) (standardB hb))
      (node226 (standardA ha) (standardB hb)) (v 228) (v 227) (v 226) c.step228 h227 h226).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node228_spec (standardA ha) (standardB hb)).symm)
  have h229 : v 229 = (↑(node229 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node228 (standardA ha) (standardB hb))
      (node228 (standardA ha) (standardB hb)) (v 229) (v 228) (v 228) c.step229 h228 h228).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node229_spec (standardA ha) (standardB hb)).symm)
  have h230 : v 230 = (↑(node230 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node229 (standardA ha) (standardB hb))
      (node226 (standardA ha) (standardB hb)) (v 230) (v 229) (v 226) c.step230 h229 h226).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node230_spec (standardA ha) (standardB hb)).symm)
  have h231 : v 231 = (↑(node231 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node230 (standardA ha) (standardB hb))
      (node230 (standardA ha) (standardB hb)) (v 231) (v 230) (v 230) c.step231 h230 h230).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node231_spec (standardA ha) (standardB hb)).symm)
  have h232 : v 232 = (↑(node232 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node231 (standardA ha) (standardB hb))
      (node226 (standardA ha) (standardB hb)) (v 232) (v 231) (v 226) c.step232 h231 h226).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node232_spec (standardA ha) (standardB hb)).symm)
  have h233 : v 233 = (↑(node233 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node54 (standardA ha) (standardB hb))
      (node74 (standardA ha) (standardB hb)) (v 233) (v 54) (v 74) c.step233 h54 h74).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node233_spec (standardA ha) (standardB hb)).symm)
  have h234 : v 234 = (↑(node234 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node221 (standardA ha) (standardB hb))
      (node218 (standardA ha) (standardB hb)) (v 234) (v 221) (v 218) c.step234 h221 h218).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node234_spec (standardA ha) (standardB hb)).symm)
  have h235 : v 235 = (↑(node235 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node234 (standardA ha) (standardB hb))
      (node234 (standardA ha) (standardB hb)) (v 235) (v 234) (v 234) c.step235 h234 h234).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node235_spec (standardA ha) (standardB hb)).symm)
  have h236 : v 236 = (↑(node236 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node235 (standardA ha) (standardB hb))
      (node235 (standardA ha) (standardB hb)) (v 236) (v 235) (v 235) c.step236 h235 h235).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node236_spec (standardA ha) (standardB hb)).symm)
  have h237 : v 237 = (↑(node237 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node236 (standardA ha) (standardB hb))
      (node234 (standardA ha) (standardB hb)) (v 237) (v 236) (v 234) c.step237 h236 h234).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node237_spec (standardA ha) (standardB hb)).symm)
  have h238 : v 238 = (↑(node238 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node237 (standardA ha) (standardB hb))
      (node237 (standardA ha) (standardB hb)) (v 238) (v 237) (v 237) c.step238 h237 h237).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node238_spec (standardA ha) (standardB hb)).symm)
  have h239 : v 239 = (↑(node239 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (inv_sound (node238 (standardA ha) (standardB hb)) (v 239) (v 238) c.step239 h238).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node239_spec (standardA ha) (standardB hb)).symm)
  have h240 : v 240 = (↑(node240 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node239 (standardA ha) (standardB hb))
      (node233 (standardA ha) (standardB hb)) (v 240) (v 239) (v 233) c.step240 h239 h233).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node240_spec (standardA ha) (standardB hb)).symm)
  have h241 : v 241 = (↑(node241 (standardA ha) (standardB hb)) : AtlasMatrix) := by
    exact (mul_sound (node240 (standardA ha) (standardB hb))
      (node238 (standardA ha) (standardB hb)) (v 241) (v 240) (v 238) c.step241 h240 h238).trans
      (congrArg (fun u : MatrixGroup => (u : AtlasMatrix))
        (node241_spec (standardA ha) (standardB hb)).symm)
  exact ⟨h232, h241⟩

end BabyMonster.OrderLowerBound.RecoveredWordProgram
