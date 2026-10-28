module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co1.CentralizerSection.OrthogonalEmbedding.Transport

/-!
# Checked transport of all nonzero singular binary vectors

The 135 singular vectors form one orbit under the literal small matrices.
Each reachability proof multiplies a previously certified isometry by a
single generator and checks its action on the vector, using column coordinates.
The exhaustive final check supplies exactly the `SingularTransport` premise.

Reproduce with `source/generate.py`; see `source/README.md` for provenance.
-/

@[expose] public section
set_option Elab.async false
namespace Sporadic.LeechRelated.Co1.CentralizerSection.OrthogonalEmbedding

private theorem reach1 : Reachable (decodeVector 1) := by
  have h : decodeVector 1 = e0 := by decide +kernel
  rw [h]
  exact reachable_e0

private theorem reach73 : Reachable (decodeVector 73) :=
  reachable_step true (decodeVector 1) (decodeVector 73)
    (by decide +kernel) reach1

private theorem reach117 : Reachable (decodeVector 117) :=
  reachable_step false (decodeVector 1) (decodeVector 117)
    (by decide +kernel) reach1

private theorem reach72 : Reachable (decodeVector 72) :=
  reachable_step true (decodeVector 73) (decodeVector 72)
    (by decide +kernel) reach73

private theorem reach190 : Reachable (decodeVector 190) :=
  reachable_step true (decodeVector 117) (decodeVector 190)
    (by decide +kernel) reach117

private theorem reach231 : Reachable (decodeVector 231) :=
  reachable_step false (decodeVector 73) (decodeVector 231)
    (by decide +kernel) reach73

private theorem reach16 : Reachable (decodeVector 16) :=
  reachable_step false (decodeVector 190) (decodeVector 16)
    (by decide +kernel) reach190

private theorem reach75 : Reachable (decodeVector 75) :=
  reachable_step true (decodeVector 231) (decodeVector 75)
    (by decide +kernel) reach231

private theorem reach146 : Reachable (decodeVector 146) :=
  reachable_step false (decodeVector 72) (decodeVector 146)
    (by decide +kernel) reach72

private theorem reach193 : Reachable (decodeVector 193) :=
  reachable_step true (decodeVector 190) (decodeVector 193)
    (by decide +kernel) reach190

private theorem reach32 : Reachable (decodeVector 32) :=
  reachable_step true (decodeVector 75) (decodeVector 32)
    (by decide +kernel) reach75

private theorem reach120 : Reachable (decodeVector 120) :=
  reachable_step false (decodeVector 75) (decodeVector 120)
    (by decide +kernel) reach75

private theorem reach171 : Reachable (decodeVector 171) :=
  reachable_step false (decodeVector 193) (decodeVector 171)
    (by decide +kernel) reach193

private theorem reach179 : Reachable (decodeVector 179) :=
  reachable_step true (decodeVector 193) (decodeVector 179)
    (by decide +kernel) reach193

private theorem reach194 : Reachable (decodeVector 194) :=
  reachable_step true (decodeVector 16) (decodeVector 194)
    (by decide +kernel) reach16

private theorem reach245 : Reachable (decodeVector 245) :=
  reachable_step true (decodeVector 146) (decodeVector 245)
    (by decide +kernel) reach146

private theorem reach37 : Reachable (decodeVector 37) :=
  reachable_step true (decodeVector 120) (decodeVector 37)
    (by decide +kernel) reach120

private theorem reach60 : Reachable (decodeVector 60) :=
  reachable_step true (decodeVector 171) (decodeVector 60)
    (by decide +kernel) reach171

private theorem reach65 : Reachable (decodeVector 65) :=
  reachable_step false (decodeVector 194) (decodeVector 65)
    (by decide +kernel) reach194

private theorem reach90 : Reachable (decodeVector 90) :=
  reachable_step false (decodeVector 179) (decodeVector 90)
    (by decide +kernel) reach179

private theorem reach103 : Reachable (decodeVector 103) :=
  reachable_step false (decodeVector 32) (decodeVector 103)
    (by decide +kernel) reach32

private theorem reach104 : Reachable (decodeVector 104) :=
  reachable_step false (decodeVector 245) (decodeVector 104)
    (by decide +kernel) reach245

private theorem reach225 : Reachable (decodeVector 225) :=
  reachable_step true (decodeVector 245) (decodeVector 225)
    (by decide +kernel) reach245

private theorem reach230 : Reachable (decodeVector 230) :=
  reachable_step true (decodeVector 32) (decodeVector 230)
    (by decide +kernel) reach32

private theorem reach2 : Reachable (decodeVector 2) :=
  reachable_step true (decodeVector 230) (decodeVector 2)
    (by decide +kernel) reach230

private theorem reach8 : Reachable (decodeVector 8) :=
  reachable_step false (decodeVector 37) (decodeVector 8)
    (by decide +kernel) reach37

private theorem reach20 : Reachable (decodeVector 20) :=
  reachable_step true (decodeVector 103) (decodeVector 20)
    (by decide +kernel) reach103

private theorem reach85 : Reachable (decodeVector 85) :=
  reachable_step true (decodeVector 225) (decodeVector 85)
    (by decide +kernel) reach225

private theorem reach204 : Reachable (decodeVector 204) :=
  reachable_step false (decodeVector 225) (decodeVector 204)
    (by decide +kernel) reach225

private theorem reach217 : Reachable (decodeVector 217) :=
  reachable_step true (decodeVector 37) (decodeVector 217)
    (by decide +kernel) reach37

private theorem reach236 : Reachable (decodeVector 236) :=
  reachable_step true (decodeVector 65) (decodeVector 236)
    (by decide +kernel) reach65

private theorem reach246 : Reachable (decodeVector 246) :=
  reachable_step true (decodeVector 60) (decodeVector 246)
    (by decide +kernel) reach60

private theorem reach40 : Reachable (decodeVector 40) :=
  reachable_step true (decodeVector 204) (decodeVector 40)
    (by decide +kernel) reach204

private theorem reach48 : Reachable (decodeVector 48) :=
  reachable_step false (decodeVector 217) (decodeVector 48)
    (by decide +kernel) reach217

private theorem reach88 : Reachable (decodeVector 88) :=
  reachable_step true (decodeVector 85) (decodeVector 88)
    (by decide +kernel) reach85

private theorem reach102 : Reachable (decodeVector 102) :=
  reachable_step false (decodeVector 85) (decodeVector 102)
    (by decide +kernel) reach85

private theorem reach130 : Reachable (decodeVector 130) :=
  reachable_step false (decodeVector 246) (decodeVector 130)
    (by decide +kernel) reach246

private theorem reach134 : Reachable (decodeVector 134) :=
  reachable_step false (decodeVector 236) (decodeVector 134)
    (by decide +kernel) reach236

private theorem reach159 : Reachable (decodeVector 159) :=
  reachable_step false (decodeVector 2) (decodeVector 159)
    (by decide +kernel) reach2

private theorem reach164 : Reachable (decodeVector 164) :=
  reachable_step true (decodeVector 8) (decodeVector 164)
    (by decide +kernel) reach8

private theorem reach180 : Reachable (decodeVector 180) :=
  reachable_step true (decodeVector 20) (decodeVector 180)
    (by decide +kernel) reach20

private theorem reach192 : Reachable (decodeVector 192) :=
  reachable_step true (decodeVector 246) (decodeVector 192)
    (by decide +kernel) reach246

private theorem reach206 : Reachable (decodeVector 206) :=
  reachable_step true (decodeVector 236) (decodeVector 206)
    (by decide +kernel) reach236

private theorem reach213 : Reachable (decodeVector 213) :=
  reachable_step true (decodeVector 217) (decodeVector 213)
    (by decide +kernel) reach217

private theorem reach7 : Reachable (decodeVector 7) :=
  reachable_step true (decodeVector 213) (decodeVector 7)
    (by decide +kernel) reach213

private theorem reach13 : Reachable (decodeVector 13) :=
  reachable_step true (decodeVector 180) (decodeVector 13)
    (by decide +kernel) reach180

private theorem reach15 : Reachable (decodeVector 15) :=
  reachable_step false (decodeVector 213) (decodeVector 15)
    (by decide +kernel) reach213

private theorem reach36 : Reachable (decodeVector 36) :=
  reachable_step true (decodeVector 48) (decodeVector 36)
    (by decide +kernel) reach48

private theorem reach44 : Reachable (decodeVector 44) :=
  reachable_step false (decodeVector 88) (decodeVector 44)
    (by decide +kernel) reach88

private theorem reach55 : Reachable (decodeVector 55) :=
  reachable_step true (decodeVector 130) (decodeVector 55)
    (by decide +kernel) reach130

private theorem reach64 : Reachable (decodeVector 64) :=
  reachable_step true (decodeVector 206) (decodeVector 64)
    (by decide +kernel) reach206

private theorem reach66 : Reachable (decodeVector 66) :=
  reachable_step false (decodeVector 40) (decodeVector 66)
    (by decide +kernel) reach40

private theorem reach93 : Reachable (decodeVector 93) :=
  reachable_step true (decodeVector 102) (decodeVector 93)
    (by decide +kernel) reach102

private theorem reach110 : Reachable (decodeVector 110) :=
  reachable_step true (decodeVector 159) (decodeVector 110)
    (by decide +kernel) reach159

private theorem reach126 : Reachable (decodeVector 126) :=
  reachable_step false (decodeVector 206) (decodeVector 126)
    (by decide +kernel) reach206

private theorem reach170 : Reachable (decodeVector 170) :=
  reachable_step false (decodeVector 180) (decodeVector 170)
    (by decide +kernel) reach180

private theorem reach195 : Reachable (decodeVector 195) :=
  reachable_step true (decodeVector 88) (decodeVector 195)
    (by decide +kernel) reach88

private theorem reach207 : Reachable (decodeVector 207) :=
  reachable_step true (decodeVector 164) (decodeVector 207)
    (by decide +kernel) reach164

private theorem reach222 : Reachable (decodeVector 222) :=
  reachable_step false (decodeVector 192) (decodeVector 222)
    (by decide +kernel) reach192

private theorem reach250 : Reachable (decodeVector 250) :=
  reachable_step true (decodeVector 192) (decodeVector 250)
    (by decide +kernel) reach192

private theorem reach9 : Reachable (decodeVector 9) :=
  reachable_step true (decodeVector 207) (decodeVector 9)
    (by decide +kernel) reach207

private theorem reach11 : Reachable (decodeVector 11) :=
  reachable_step false (decodeVector 207) (decodeVector 11)
    (by decide +kernel) reach207

private theorem reach18 : Reachable (decodeVector 18) :=
  reachable_step true (decodeVector 250) (decodeVector 18)
    (by decide +kernel) reach250

private theorem reach41 : Reachable (decodeVector 41) :=
  reachable_step false (decodeVector 55) (decodeVector 41)
    (by decide +kernel) reach55

private theorem reach52 : Reachable (decodeVector 52) :=
  reachable_step true (decodeVector 44) (decodeVector 52)
    (by decide +kernel) reach44

private theorem reach59 : Reachable (decodeVector 59) :=
  reachable_step true (decodeVector 126) (decodeVector 59)
    (by decide +kernel) reach126

private theorem reach67 : Reachable (decodeVector 67) :=
  reachable_step false (decodeVector 93) (decodeVector 67)
    (by decide +kernel) reach93

private theorem reach74 : Reachable (decodeVector 74) :=
  reachable_step false (decodeVector 13) (decodeVector 74)
    (by decide +kernel) reach13

private theorem reach87 : Reachable (decodeVector 87) :=
  reachable_step true (decodeVector 7) (decodeVector 87)
    (by decide +kernel) reach7

private theorem reach112 : Reachable (decodeVector 112) :=
  reachable_step false (decodeVector 110) (decodeVector 112)
    (by decide +kernel) reach110

private theorem reach115 : Reachable (decodeVector 115) :=
  reachable_step true (decodeVector 55) (decodeVector 115)
    (by decide +kernel) reach55

private theorem reach125 : Reachable (decodeVector 125) :=
  reachable_step false (decodeVector 36) (decodeVector 125)
    (by decide +kernel) reach36

private theorem reach144 : Reachable (decodeVector 144) :=
  reachable_step true (decodeVector 36) (decodeVector 144)
    (by decide +kernel) reach36

private theorem reach155 : Reachable (decodeVector 155) :=
  reachable_step true (decodeVector 13) (decodeVector 155)
    (by decide +kernel) reach13

private theorem reach165 : Reachable (decodeVector 165) :=
  reachable_step true (decodeVector 64) (decodeVector 165)
    (by decide +kernel) reach64

private theorem reach183 : Reachable (decodeVector 183) :=
  reachable_step false (decodeVector 64) (decodeVector 183)
    (by decide +kernel) reach64

private theorem reach189 : Reachable (decodeVector 189) :=
  reachable_step false (decodeVector 250) (decodeVector 189)
    (by decide +kernel) reach250

private theorem reach205 : Reachable (decodeVector 205) :=
  reachable_step true (decodeVector 66) (decodeVector 205)
    (by decide +kernel) reach66

private theorem reach219 : Reachable (decodeVector 219) :=
  reachable_step true (decodeVector 195) (decodeVector 219)
    (by decide +kernel) reach195

private theorem reach240 : Reachable (decodeVector 240) :=
  reachable_step false (decodeVector 7) (decodeVector 240)
    (by decide +kernel) reach7

private theorem reach243 : Reachable (decodeVector 243) :=
  reachable_step true (decodeVector 15) (decodeVector 243)
    (by decide +kernel) reach15

private theorem reach249 : Reachable (decodeVector 249) :=
  reachable_step true (decodeVector 110) (decodeVector 249)
    (by decide +kernel) reach110

private theorem reach252 : Reachable (decodeVector 252) :=
  reachable_step true (decodeVector 93) (decodeVector 252)
    (by decide +kernel) reach93

private theorem reach12 : Reachable (decodeVector 12) :=
  reachable_step true (decodeVector 252) (decodeVector 12)
    (by decide +kernel) reach252

private theorem reach22 : Reachable (decodeVector 22) :=
  reachable_step false (decodeVector 59) (decodeVector 22)
    (by decide +kernel) reach59

private theorem reach24 : Reachable (decodeVector 24) :=
  reachable_step false (decodeVector 155) (decodeVector 24)
    (by decide +kernel) reach155

private theorem reach26 : Reachable (decodeVector 26) :=
  reachable_step true (decodeVector 125) (decodeVector 26)
    (by decide +kernel) reach125

private theorem reach33 : Reachable (decodeVector 33) :=
  reachable_step false (decodeVector 18) (decodeVector 33)
    (by decide +kernel) reach18

private theorem reach51 : Reachable (decodeVector 51) :=
  reachable_step true (decodeVector 249) (decodeVector 51)
    (by decide +kernel) reach249

private theorem reach56 : Reachable (decodeVector 56) :=
  reachable_step false (decodeVector 252) (decodeVector 56)
    (by decide +kernel) reach252

private theorem reach80 : Reachable (decodeVector 80) :=
  reachable_step false (decodeVector 9) (decodeVector 80)
    (by decide +kernel) reach9

private theorem reach82 : Reachable (decodeVector 82) :=
  reachable_step true (decodeVector 52) (decodeVector 82)
    (by decide +kernel) reach52

private theorem reach97 : Reachable (decodeVector 97) :=
  reachable_step false (decodeVector 165) (decodeVector 97)
    (by decide +kernel) reach165

private theorem reach105 : Reachable (decodeVector 105) :=
  reachable_step true (decodeVector 74) (decodeVector 105)
    (by decide +kernel) reach74

private theorem reach129 : Reachable (decodeVector 129) :=
  reachable_step true (decodeVector 112) (decodeVector 129)
    (by decide +kernel) reach112

private theorem reach132 : Reachable (decodeVector 132) :=
  reachable_step false (decodeVector 115) (decodeVector 132)
    (by decide +kernel) reach115

private theorem reach133 : Reachable (decodeVector 133) :=
  reachable_step true (decodeVector 11) (decodeVector 133)
    (by decide +kernel) reach11

private theorem reach148 : Reachable (decodeVector 148) :=
  reachable_step false (decodeVector 205) (decodeVector 148)
    (by decide +kernel) reach205

private theorem reach157 : Reachable (decodeVector 157) :=
  reachable_step true (decodeVector 144) (decodeVector 157)
    (by decide +kernel) reach144

private theorem reach160 : Reachable (decodeVector 160) :=
  reachable_step true (decodeVector 115) (decodeVector 160)
    (by decide +kernel) reach115

private theorem reach161 : Reachable (decodeVector 161) :=
  reachable_step true (decodeVector 59) (decodeVector 161)
    (by decide +kernel) reach59

private theorem reach175 : Reachable (decodeVector 175) :=
  reachable_step false (decodeVector 219) (decodeVector 175)
    (by decide +kernel) reach219

private theorem reach215 : Reachable (decodeVector 215) :=
  reachable_step false (decodeVector 144) (decodeVector 215)
    (by decide +kernel) reach144

private theorem reach224 : Reachable (decodeVector 224) :=
  reachable_step true (decodeVector 189) (decodeVector 224)
    (by decide +kernel) reach189

private theorem reach237 : Reachable (decodeVector 237) :=
  reachable_step true (decodeVector 9) (decodeVector 237)
    (by decide +kernel) reach9

private theorem reach255 : Reachable (decodeVector 255) :=
  reachable_step true (decodeVector 243) (decodeVector 255)
    (by decide +kernel) reach243

private theorem reach4 : Reachable (decodeVector 4) :=
  reachable_step false (decodeVector 26) (decodeVector 4)
    (by decide +kernel) reach26

private theorem reach5 : Reachable (decodeVector 5) :=
  reachable_step true (decodeVector 51) (decodeVector 5)
    (by decide +kernel) reach51

private theorem reach6 : Reachable (decodeVector 6) :=
  reachable_step false (decodeVector 133) (decodeVector 6)
    (by decide +kernel) reach133

private theorem reach10 : Reachable (decodeVector 10) :=
  reachable_step true (decodeVector 97) (decodeVector 10)
    (by decide +kernel) reach97

private theorem reach14 : Reachable (decodeVector 14) :=
  reachable_step false (decodeVector 160) (decodeVector 14)
    (by decide +kernel) reach160

private theorem reach28 : Reachable (decodeVector 28) :=
  reachable_step true (decodeVector 224) (decodeVector 28)
    (by decide +kernel) reach224

private theorem reach45 : Reachable (decodeVector 45) :=
  reachable_step true (decodeVector 255) (decodeVector 45)
    (by decide +kernel) reach255

private theorem reach63 : Reachable (decodeVector 63) :=
  reachable_step false (decodeVector 12) (decodeVector 63)
    (by decide +kernel) reach12

private theorem reach96 : Reachable (decodeVector 96) :=
  reachable_step true (decodeVector 133) (decodeVector 96)
    (by decide +kernel) reach133

private theorem reach111 : Reachable (decodeVector 111) :=
  reachable_step true (decodeVector 215) (decodeVector 111)
    (by decide +kernel) reach215

private theorem reach123 : Reachable (decodeVector 123) :=
  reachable_step false (decodeVector 161) (decodeVector 123)
    (by decide +kernel) reach161

private theorem reach128 : Reachable (decodeVector 128) :=
  reachable_step false (decodeVector 105) (decodeVector 128)
    (by decide +kernel) reach105

private theorem reach135 : Reachable (decodeVector 135) :=
  reachable_step true (decodeVector 237) (decodeVector 135)
    (by decide +kernel) reach237

private theorem reach150 : Reachable (decodeVector 150) :=
  reachable_step false (decodeVector 82) (decodeVector 150)
    (by decide +kernel) reach82

private theorem reach174 : Reachable (decodeVector 174) :=
  reachable_step true (decodeVector 105) (decodeVector 174)
    (by decide +kernel) reach105

private theorem reach185 : Reachable (decodeVector 185) :=
  reachable_step true (decodeVector 160) (decodeVector 185)
    (by decide +kernel) reach160

private theorem reach210 : Reachable (decodeVector 210) :=
  reachable_step false (decodeVector 255) (decodeVector 210)
    (by decide +kernel) reach255

private theorem reach220 : Reachable (decodeVector 220) :=
  reachable_step true (decodeVector 22) (decodeVector 220)
    (by decide +kernel) reach22

private theorem reach235 : Reachable (decodeVector 235) :=
  reachable_step true (decodeVector 148) (decodeVector 235)
    (by decide +kernel) reach148

private theorem reach3 : Reachable (decodeVector 3) :=
  reachable_step true (decodeVector 174) (decodeVector 3)
    (by decide +kernel) reach174

private theorem reach30 : Reachable (decodeVector 30) :=
  reachable_step true (decodeVector 6) (decodeVector 30)
    (by decide +kernel) reach6

private theorem reach95 : Reachable (decodeVector 95) :=
  reachable_step false (decodeVector 220) (decodeVector 95)
    (by decide +kernel) reach220

private theorem reach118 : Reachable (decodeVector 118) :=
  reachable_step true (decodeVector 4) (decodeVector 118)
    (by decide +kernel) reach4

private theorem reach131 : Reachable (decodeVector 131) :=
  reachable_step true (decodeVector 150) (decodeVector 131)
    (by decide +kernel) reach150

private theorem reach153 : Reachable (decodeVector 153) :=
  reachable_step false (decodeVector 135) (decodeVector 153)
    (by decide +kernel) reach135

private theorem reach176 : Reachable (decodeVector 176) :=
  reachable_step true (decodeVector 111) (decodeVector 176)
    (by decide +kernel) reach111

private theorem reach186 : Reachable (decodeVector 186) :=
  reachable_step false (decodeVector 10) (decodeVector 186)
    (by decide +kernel) reach10

private theorem reach208 : Reachable (decodeVector 208) :=
  reachable_step false (decodeVector 96) (decodeVector 208)
    (by decide +kernel) reach96

private theorem reach234 : Reachable (decodeVector 234) :=
  reachable_step true (decodeVector 220) (decodeVector 234)
    (by decide +kernel) reach220

theorem encoded_singular_reachable (c : Fin 256) (hc : decodeVector c ≠ 0)
    (hq : Q (decodeVector c) = 0) : Reachable (decodeVector c) := by
  fin_cases c
  · exact (hc (by decide +kernel)).elim
  · exact reach1
  · exact reach2
  · exact reach3
  · exact reach4
  · exact reach5
  · exact reach6
  · exact reach7
  · exact reach8
  · exact reach9
  · exact reach10
  · exact reach11
  · exact reach12
  · exact reach13
  · exact reach14
  · exact reach15
  · exact reach16
  · exact ((by decide +kernel : Q (decodeVector 17) ≠ 0) hq).elim
  · exact reach18
  · exact ((by decide +kernel : Q (decodeVector 19) ≠ 0) hq).elim
  · exact reach20
  · exact ((by decide +kernel : Q (decodeVector 21) ≠ 0) hq).elim
  · exact reach22
  · exact ((by decide +kernel : Q (decodeVector 23) ≠ 0) hq).elim
  · exact reach24
  · exact ((by decide +kernel : Q (decodeVector 25) ≠ 0) hq).elim
  · exact reach26
  · exact ((by decide +kernel : Q (decodeVector 27) ≠ 0) hq).elim
  · exact reach28
  · exact ((by decide +kernel : Q (decodeVector 29) ≠ 0) hq).elim
  · exact reach30
  · exact ((by decide +kernel : Q (decodeVector 31) ≠ 0) hq).elim
  · exact reach32
  · exact reach33
  · exact ((by decide +kernel : Q (decodeVector 34) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 35) ≠ 0) hq).elim
  · exact reach36
  · exact reach37
  · exact ((by decide +kernel : Q (decodeVector 38) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 39) ≠ 0) hq).elim
  · exact reach40
  · exact reach41
  · exact ((by decide +kernel : Q (decodeVector 42) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 43) ≠ 0) hq).elim
  · exact reach44
  · exact reach45
  · exact ((by decide +kernel : Q (decodeVector 46) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 47) ≠ 0) hq).elim
  · exact reach48
  · exact ((by decide +kernel : Q (decodeVector 49) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 50) ≠ 0) hq).elim
  · exact reach51
  · exact reach52
  · exact ((by decide +kernel : Q (decodeVector 53) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 54) ≠ 0) hq).elim
  · exact reach55
  · exact reach56
  · exact ((by decide +kernel : Q (decodeVector 57) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 58) ≠ 0) hq).elim
  · exact reach59
  · exact reach60
  · exact ((by decide +kernel : Q (decodeVector 61) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 62) ≠ 0) hq).elim
  · exact reach63
  · exact reach64
  · exact reach65
  · exact reach66
  · exact reach67
  · exact ((by decide +kernel : Q (decodeVector 68) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 69) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 70) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 71) ≠ 0) hq).elim
  · exact reach72
  · exact reach73
  · exact reach74
  · exact reach75
  · exact ((by decide +kernel : Q (decodeVector 76) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 77) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 78) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 79) ≠ 0) hq).elim
  · exact reach80
  · exact ((by decide +kernel : Q (decodeVector 81) ≠ 0) hq).elim
  · exact reach82
  · exact ((by decide +kernel : Q (decodeVector 83) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 84) ≠ 0) hq).elim
  · exact reach85
  · exact ((by decide +kernel : Q (decodeVector 86) ≠ 0) hq).elim
  · exact reach87
  · exact reach88
  · exact ((by decide +kernel : Q (decodeVector 89) ≠ 0) hq).elim
  · exact reach90
  · exact ((by decide +kernel : Q (decodeVector 91) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 92) ≠ 0) hq).elim
  · exact reach93
  · exact ((by decide +kernel : Q (decodeVector 94) ≠ 0) hq).elim
  · exact reach95
  · exact reach96
  · exact reach97
  · exact ((by decide +kernel : Q (decodeVector 98) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 99) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 100) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 101) ≠ 0) hq).elim
  · exact reach102
  · exact reach103
  · exact reach104
  · exact reach105
  · exact ((by decide +kernel : Q (decodeVector 106) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 107) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 108) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 109) ≠ 0) hq).elim
  · exact reach110
  · exact reach111
  · exact reach112
  · exact ((by decide +kernel : Q (decodeVector 113) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 114) ≠ 0) hq).elim
  · exact reach115
  · exact ((by decide +kernel : Q (decodeVector 116) ≠ 0) hq).elim
  · exact reach117
  · exact reach118
  · exact ((by decide +kernel : Q (decodeVector 119) ≠ 0) hq).elim
  · exact reach120
  · exact ((by decide +kernel : Q (decodeVector 121) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 122) ≠ 0) hq).elim
  · exact reach123
  · exact ((by decide +kernel : Q (decodeVector 124) ≠ 0) hq).elim
  · exact reach125
  · exact reach126
  · exact ((by decide +kernel : Q (decodeVector 127) ≠ 0) hq).elim
  · exact reach128
  · exact reach129
  · exact reach130
  · exact reach131
  · exact reach132
  · exact reach133
  · exact reach134
  · exact reach135
  · exact ((by decide +kernel : Q (decodeVector 136) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 137) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 138) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 139) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 140) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 141) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 142) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 143) ≠ 0) hq).elim
  · exact reach144
  · exact ((by decide +kernel : Q (decodeVector 145) ≠ 0) hq).elim
  · exact reach146
  · exact ((by decide +kernel : Q (decodeVector 147) ≠ 0) hq).elim
  · exact reach148
  · exact ((by decide +kernel : Q (decodeVector 149) ≠ 0) hq).elim
  · exact reach150
  · exact ((by decide +kernel : Q (decodeVector 151) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 152) ≠ 0) hq).elim
  · exact reach153
  · exact ((by decide +kernel : Q (decodeVector 154) ≠ 0) hq).elim
  · exact reach155
  · exact ((by decide +kernel : Q (decodeVector 156) ≠ 0) hq).elim
  · exact reach157
  · exact ((by decide +kernel : Q (decodeVector 158) ≠ 0) hq).elim
  · exact reach159
  · exact reach160
  · exact reach161
  · exact ((by decide +kernel : Q (decodeVector 162) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 163) ≠ 0) hq).elim
  · exact reach164
  · exact reach165
  · exact ((by decide +kernel : Q (decodeVector 166) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 167) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 168) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 169) ≠ 0) hq).elim
  · exact reach170
  · exact reach171
  · exact ((by decide +kernel : Q (decodeVector 172) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 173) ≠ 0) hq).elim
  · exact reach174
  · exact reach175
  · exact reach176
  · exact ((by decide +kernel : Q (decodeVector 177) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 178) ≠ 0) hq).elim
  · exact reach179
  · exact reach180
  · exact ((by decide +kernel : Q (decodeVector 181) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 182) ≠ 0) hq).elim
  · exact reach183
  · exact ((by decide +kernel : Q (decodeVector 184) ≠ 0) hq).elim
  · exact reach185
  · exact reach186
  · exact ((by decide +kernel : Q (decodeVector 187) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 188) ≠ 0) hq).elim
  · exact reach189
  · exact reach190
  · exact ((by decide +kernel : Q (decodeVector 191) ≠ 0) hq).elim
  · exact reach192
  · exact reach193
  · exact reach194
  · exact reach195
  · exact ((by decide +kernel : Q (decodeVector 196) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 197) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 198) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 199) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 200) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 201) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 202) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 203) ≠ 0) hq).elim
  · exact reach204
  · exact reach205
  · exact reach206
  · exact reach207
  · exact reach208
  · exact ((by decide +kernel : Q (decodeVector 209) ≠ 0) hq).elim
  · exact reach210
  · exact ((by decide +kernel : Q (decodeVector 211) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 212) ≠ 0) hq).elim
  · exact reach213
  · exact ((by decide +kernel : Q (decodeVector 214) ≠ 0) hq).elim
  · exact reach215
  · exact ((by decide +kernel : Q (decodeVector 216) ≠ 0) hq).elim
  · exact reach217
  · exact ((by decide +kernel : Q (decodeVector 218) ≠ 0) hq).elim
  · exact reach219
  · exact reach220
  · exact ((by decide +kernel : Q (decodeVector 221) ≠ 0) hq).elim
  · exact reach222
  · exact ((by decide +kernel : Q (decodeVector 223) ≠ 0) hq).elim
  · exact reach224
  · exact reach225
  · exact ((by decide +kernel : Q (decodeVector 226) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 227) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 228) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 229) ≠ 0) hq).elim
  · exact reach230
  · exact reach231
  · exact ((by decide +kernel : Q (decodeVector 232) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 233) ≠ 0) hq).elim
  · exact reach234
  · exact reach235
  · exact reach236
  · exact reach237
  · exact ((by decide +kernel : Q (decodeVector 238) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 239) ≠ 0) hq).elim
  · exact reach240
  · exact ((by decide +kernel : Q (decodeVector 241) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 242) ≠ 0) hq).elim
  · exact reach243
  · exact ((by decide +kernel : Q (decodeVector 244) ≠ 0) hq).elim
  · exact reach245
  · exact reach246
  · exact ((by decide +kernel : Q (decodeVector 247) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 248) ≠ 0) hq).elim
  · exact reach249
  · exact reach250
  · exact ((by decide +kernel : Q (decodeVector 251) ≠ 0) hq).elim
  · exact reach252
  · exact ((by decide +kernel : Q (decodeVector 253) ≠ 0) hq).elim
  · exact ((by decide +kernel : Q (decodeVector 254) ≠ 0) hq).elim
  · exact reach255

theorem singularTransport : SingularTransport := by
  intro u hu hq
  have he := decodeVector_code u
  have h := encoded_singular_reachable (vectorCode u) (by simpa only [he] using hu)
    (by simpa only [he] using hq)
  obtain ⟨g, hg, hgu⟩ := h
  exact ⟨g, hg, hgu.trans he⟩

end Sporadic.LeechRelated.Co1.CentralizerSection.OrthogonalEmbedding
