module

public import Theory.SpecificGroups.Rudvalis.Model.ThreeConjugates.FusionData
import Mathlib.Tactic.FinCases

/-!
# Exhaustive checks for the Rudvalis involution forest

Every one of the 16384 normal-form indices is checked in blocks of 64.
The representative block used about 1.9 GB including imports. Sequential
elaboration keeps these independent kernel computations from overlapping.
The final theorem supplies the literal forest predicate to `Fusion`.

Source and witness generation: `ThreeConjugates/source/README.md`.
-/

namespace Rudvalis.ThreeConjugates.FusionCertificate
set_option Elab.async false

set_option maxRecDepth 3000 in
private theorem block0 : checkBlock 0 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block1 : checkBlock 1 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block2 : checkBlock 2 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block3 : checkBlock 3 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block4 : checkBlock 4 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block5 : checkBlock 5 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block6 : checkBlock 6 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block7 : checkBlock 7 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block8 : checkBlock 8 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block9 : checkBlock 9 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block10 : checkBlock 10 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block11 : checkBlock 11 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block12 : checkBlock 12 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block13 : checkBlock 13 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block14 : checkBlock 14 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block15 : checkBlock 15 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block16 : checkBlock 16 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block17 : checkBlock 17 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block18 : checkBlock 18 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block19 : checkBlock 19 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block20 : checkBlock 20 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block21 : checkBlock 21 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block22 : checkBlock 22 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block23 : checkBlock 23 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block24 : checkBlock 24 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block25 : checkBlock 25 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block26 : checkBlock 26 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block27 : checkBlock 27 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block28 : checkBlock 28 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block29 : checkBlock 29 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block30 : checkBlock 30 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block31 : checkBlock 31 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block32 : checkBlock 32 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block33 : checkBlock 33 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block34 : checkBlock 34 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block35 : checkBlock 35 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block36 : checkBlock 36 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block37 : checkBlock 37 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block38 : checkBlock 38 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block39 : checkBlock 39 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block40 : checkBlock 40 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block41 : checkBlock 41 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block42 : checkBlock 42 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block43 : checkBlock 43 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block44 : checkBlock 44 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block45 : checkBlock 45 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block46 : checkBlock 46 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block47 : checkBlock 47 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block48 : checkBlock 48 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block49 : checkBlock 49 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block50 : checkBlock 50 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block51 : checkBlock 51 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block52 : checkBlock 52 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block53 : checkBlock 53 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block54 : checkBlock 54 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block55 : checkBlock 55 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block56 : checkBlock 56 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block57 : checkBlock 57 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block58 : checkBlock 58 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block59 : checkBlock 59 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block60 : checkBlock 60 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block61 : checkBlock 61 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block62 : checkBlock 62 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block63 : checkBlock 63 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block64 : checkBlock 64 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block65 : checkBlock 65 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block66 : checkBlock 66 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block67 : checkBlock 67 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block68 : checkBlock 68 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block69 : checkBlock 69 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block70 : checkBlock 70 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block71 : checkBlock 71 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block72 : checkBlock 72 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block73 : checkBlock 73 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block74 : checkBlock 74 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block75 : checkBlock 75 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block76 : checkBlock 76 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block77 : checkBlock 77 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block78 : checkBlock 78 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block79 : checkBlock 79 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block80 : checkBlock 80 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block81 : checkBlock 81 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block82 : checkBlock 82 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block83 : checkBlock 83 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block84 : checkBlock 84 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block85 : checkBlock 85 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block86 : checkBlock 86 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block87 : checkBlock 87 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block88 : checkBlock 88 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block89 : checkBlock 89 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block90 : checkBlock 90 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block91 : checkBlock 91 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block92 : checkBlock 92 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block93 : checkBlock 93 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block94 : checkBlock 94 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block95 : checkBlock 95 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block96 : checkBlock 96 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block97 : checkBlock 97 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block98 : checkBlock 98 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block99 : checkBlock 99 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block100 : checkBlock 100 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block101 : checkBlock 101 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block102 : checkBlock 102 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block103 : checkBlock 103 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block104 : checkBlock 104 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block105 : checkBlock 105 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block106 : checkBlock 106 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block107 : checkBlock 107 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block108 : checkBlock 108 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block109 : checkBlock 109 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block110 : checkBlock 110 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block111 : checkBlock 111 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block112 : checkBlock 112 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block113 : checkBlock 113 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block114 : checkBlock 114 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block115 : checkBlock 115 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block116 : checkBlock 116 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block117 : checkBlock 117 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block118 : checkBlock 118 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block119 : checkBlock 119 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block120 : checkBlock 120 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block121 : checkBlock 121 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block122 : checkBlock 122 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block123 : checkBlock 123 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block124 : checkBlock 124 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block125 : checkBlock 125 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block126 : checkBlock 126 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block127 : checkBlock 127 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block128 : checkBlock 128 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block129 : checkBlock 129 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block130 : checkBlock 130 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block131 : checkBlock 131 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block132 : checkBlock 132 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block133 : checkBlock 133 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block134 : checkBlock 134 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block135 : checkBlock 135 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block136 : checkBlock 136 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block137 : checkBlock 137 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block138 : checkBlock 138 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block139 : checkBlock 139 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block140 : checkBlock 140 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block141 : checkBlock 141 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block142 : checkBlock 142 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block143 : checkBlock 143 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block144 : checkBlock 144 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block145 : checkBlock 145 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block146 : checkBlock 146 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block147 : checkBlock 147 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block148 : checkBlock 148 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block149 : checkBlock 149 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block150 : checkBlock 150 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block151 : checkBlock 151 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block152 : checkBlock 152 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block153 : checkBlock 153 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block154 : checkBlock 154 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block155 : checkBlock 155 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block156 : checkBlock 156 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block157 : checkBlock 157 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block158 : checkBlock 158 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block159 : checkBlock 159 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block160 : checkBlock 160 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block161 : checkBlock 161 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block162 : checkBlock 162 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block163 : checkBlock 163 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block164 : checkBlock 164 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block165 : checkBlock 165 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block166 : checkBlock 166 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block167 : checkBlock 167 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block168 : checkBlock 168 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block169 : checkBlock 169 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block170 : checkBlock 170 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block171 : checkBlock 171 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block172 : checkBlock 172 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block173 : checkBlock 173 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block174 : checkBlock 174 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block175 : checkBlock 175 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block176 : checkBlock 176 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block177 : checkBlock 177 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block178 : checkBlock 178 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block179 : checkBlock 179 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block180 : checkBlock 180 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block181 : checkBlock 181 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block182 : checkBlock 182 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block183 : checkBlock 183 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block184 : checkBlock 184 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block185 : checkBlock 185 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block186 : checkBlock 186 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block187 : checkBlock 187 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block188 : checkBlock 188 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block189 : checkBlock 189 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block190 : checkBlock 190 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block191 : checkBlock 191 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block192 : checkBlock 192 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block193 : checkBlock 193 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block194 : checkBlock 194 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block195 : checkBlock 195 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block196 : checkBlock 196 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block197 : checkBlock 197 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block198 : checkBlock 198 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block199 : checkBlock 199 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block200 : checkBlock 200 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block201 : checkBlock 201 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block202 : checkBlock 202 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block203 : checkBlock 203 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block204 : checkBlock 204 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block205 : checkBlock 205 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block206 : checkBlock 206 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block207 : checkBlock 207 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block208 : checkBlock 208 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block209 : checkBlock 209 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block210 : checkBlock 210 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block211 : checkBlock 211 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block212 : checkBlock 212 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block213 : checkBlock 213 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block214 : checkBlock 214 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block215 : checkBlock 215 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block216 : checkBlock 216 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block217 : checkBlock 217 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block218 : checkBlock 218 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block219 : checkBlock 219 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block220 : checkBlock 220 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block221 : checkBlock 221 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block222 : checkBlock 222 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block223 : checkBlock 223 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block224 : checkBlock 224 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block225 : checkBlock 225 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block226 : checkBlock 226 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block227 : checkBlock 227 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block228 : checkBlock 228 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block229 : checkBlock 229 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block230 : checkBlock 230 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block231 : checkBlock 231 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block232 : checkBlock 232 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block233 : checkBlock 233 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block234 : checkBlock 234 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block235 : checkBlock 235 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block236 : checkBlock 236 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block237 : checkBlock 237 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block238 : checkBlock 238 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block239 : checkBlock 239 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block240 : checkBlock 240 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block241 : checkBlock 241 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block242 : checkBlock 242 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block243 : checkBlock 243 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block244 : checkBlock 244 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block245 : checkBlock 245 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block246 : checkBlock 246 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block247 : checkBlock 247 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block248 : checkBlock 248 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block249 : checkBlock 249 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block250 : checkBlock 250 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block251 : checkBlock 251 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block252 : checkBlock 252 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block253 : checkBlock 253 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block254 : checkBlock 254 = true := by decide +kernel

set_option maxRecDepth 3000 in
private theorem block255 : checkBlock 255 = true := by decide +kernel

private theorem blocks (b : Fin 256) : checkBlock b.val = true := by
  fin_cases b
  · exact block0
  · exact block1
  · exact block2
  · exact block3
  · exact block4
  · exact block5
  · exact block6
  · exact block7
  · exact block8
  · exact block9
  · exact block10
  · exact block11
  · exact block12
  · exact block13
  · exact block14
  · exact block15
  · exact block16
  · exact block17
  · exact block18
  · exact block19
  · exact block20
  · exact block21
  · exact block22
  · exact block23
  · exact block24
  · exact block25
  · exact block26
  · exact block27
  · exact block28
  · exact block29
  · exact block30
  · exact block31
  · exact block32
  · exact block33
  · exact block34
  · exact block35
  · exact block36
  · exact block37
  · exact block38
  · exact block39
  · exact block40
  · exact block41
  · exact block42
  · exact block43
  · exact block44
  · exact block45
  · exact block46
  · exact block47
  · exact block48
  · exact block49
  · exact block50
  · exact block51
  · exact block52
  · exact block53
  · exact block54
  · exact block55
  · exact block56
  · exact block57
  · exact block58
  · exact block59
  · exact block60
  · exact block61
  · exact block62
  · exact block63
  · exact block64
  · exact block65
  · exact block66
  · exact block67
  · exact block68
  · exact block69
  · exact block70
  · exact block71
  · exact block72
  · exact block73
  · exact block74
  · exact block75
  · exact block76
  · exact block77
  · exact block78
  · exact block79
  · exact block80
  · exact block81
  · exact block82
  · exact block83
  · exact block84
  · exact block85
  · exact block86
  · exact block87
  · exact block88
  · exact block89
  · exact block90
  · exact block91
  · exact block92
  · exact block93
  · exact block94
  · exact block95
  · exact block96
  · exact block97
  · exact block98
  · exact block99
  · exact block100
  · exact block101
  · exact block102
  · exact block103
  · exact block104
  · exact block105
  · exact block106
  · exact block107
  · exact block108
  · exact block109
  · exact block110
  · exact block111
  · exact block112
  · exact block113
  · exact block114
  · exact block115
  · exact block116
  · exact block117
  · exact block118
  · exact block119
  · exact block120
  · exact block121
  · exact block122
  · exact block123
  · exact block124
  · exact block125
  · exact block126
  · exact block127
  · exact block128
  · exact block129
  · exact block130
  · exact block131
  · exact block132
  · exact block133
  · exact block134
  · exact block135
  · exact block136
  · exact block137
  · exact block138
  · exact block139
  · exact block140
  · exact block141
  · exact block142
  · exact block143
  · exact block144
  · exact block145
  · exact block146
  · exact block147
  · exact block148
  · exact block149
  · exact block150
  · exact block151
  · exact block152
  · exact block153
  · exact block154
  · exact block155
  · exact block156
  · exact block157
  · exact block158
  · exact block159
  · exact block160
  · exact block161
  · exact block162
  · exact block163
  · exact block164
  · exact block165
  · exact block166
  · exact block167
  · exact block168
  · exact block169
  · exact block170
  · exact block171
  · exact block172
  · exact block173
  · exact block174
  · exact block175
  · exact block176
  · exact block177
  · exact block178
  · exact block179
  · exact block180
  · exact block181
  · exact block182
  · exact block183
  · exact block184
  · exact block185
  · exact block186
  · exact block187
  · exact block188
  · exact block189
  · exact block190
  · exact block191
  · exact block192
  · exact block193
  · exact block194
  · exact block195
  · exact block196
  · exact block197
  · exact block198
  · exact block199
  · exact block200
  · exact block201
  · exact block202
  · exact block203
  · exact block204
  · exact block205
  · exact block206
  · exact block207
  · exact block208
  · exact block209
  · exact block210
  · exact block211
  · exact block212
  · exact block213
  · exact block214
  · exact block215
  · exact block216
  · exact block217
  · exact block218
  · exact block219
  · exact block220
  · exact block221
  · exact block222
  · exact block223
  · exact block224
  · exact block225
  · exact block226
  · exact block227
  · exact block228
  · exact block229
  · exact block230
  · exact block231
  · exact block232
  · exact block233
  · exact block234
  · exact block235
  · exact block236
  · exact block237
  · exact block238
  · exact block239
  · exact block240
  · exact block241
  · exact block242
  · exact block243
  · exact block244
  · exact block245
  · exact block246
  · exact block247
  · exact block248
  · exact block249
  · exact block250
  · exact block251
  · exact block252
  · exact block253
  · exact block254
  · exact block255

private theorem checkNat_sound (f : Nat → Bool) (n : Nat)
    (h : Data.checkNat f n = true) (k : Nat) (hk : k < n) : f k = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [Data.checkNat, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact ih h.1 hk
    · exact h.2

/-- Every normal form has a certified square obstruction, root, or descent step. -/
public theorem tests (n : Fin 16384) : Test n := by
  have hb : n.val / 64 < 256 := by omega
  have h := of_decide_eq_true (checkNat_sound _ 64
    (blocks ⟨n.val / 64, hb⟩) (n.val % 64) (Nat.mod_lt _ (by decide)))
  have he : (64 * (n.val / 64) + n.val % 64) % 16384 = n.val := by omega
  simpa only [he] using h

end Rudvalis.ThreeConjugates.FusionCertificate
