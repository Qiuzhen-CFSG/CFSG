module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Reduction
import Mathlib.Tactic.FinCases

/-!
# Residual checks for Rudvalis level-0 transition part 3

Of the 1160 forward transitions in the 29 batches numbered 3 modulo 7,
889 follow by word reduction in the cyclic groups of orders 2 and 4.
This module proves these checks and reduces part 3 to the remaining 271
explicit transitions, grouped into four independent finite certificates.

The source witnesses are those of `OrderLevel0Data`, documented in
`OrderCertificate/GenerateChain.g`. The accompanying generator only selects
proof branches; the word reductions and final coverage are kernel-checked.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual
set_option maxRecDepth 30000
set_option Elab.async false

@[expose] public def target (k : Fin 271) : Fin 2 × Fin 4060 :=
  (if k.val < 135 then (if k.val < 67 then (if k.val < 33 then (if k.val < 16 then (if k.val < 8 then (if k.val < 4 then (if k.val < 2 then (if k.val < 1 then (0, 353) else (0, 358)) else (if k.val < 3 then (0, 485) else (0, 488))) else (if k.val < 6 then (if k.val < 5 then (0, 490) else (1, 484)) else (if k.val < 7 then (1, 487) else (1, 499)))) else (if k.val < 12 then (if k.val < 10 then (if k.val < 9 then (0, 767) else (0, 772)) else (if k.val < 11 then (0, 773) else (1, 777))) else (if k.val < 14 then (if k.val < 13 then (1, 778) else (0, 902)) else (if k.val < 15 then (0, 904) else (1, 908))))) else (if k.val < 24 then (if k.val < 20 then (if k.val < 18 then (if k.val < 17 then (1, 919) else (0, 1053)) else (if k.val < 19 then (0, 1055) else (1, 1040))) else (if k.val < 22 then (if k.val < 21 then (1, 1057) else (0, 1183)) else (if k.val < 23 then (0, 1188) else (0, 1191)))) else (if k.val < 28 then (if k.val < 26 then (if k.val < 25 then (1, 1181) else (1, 1185)) else (if k.val < 27 then (1, 1196) else (1, 1197))) else (if k.val < 30 then (if k.val < 29 then (0, 1320) else (0, 1327)) else (if k.val < 31 then (0, 1329) else (if k.val < 32 then (1, 1328) else (0, 1460))))))) else (if k.val < 50 then (if k.val < 41 then (if k.val < 37 then (if k.val < 35 then (if k.val < 34 then (0, 1461) else (0, 1466)) else (if k.val < 36 then (0, 1468) else (0, 1470))) else (if k.val < 39 then (if k.val < 38 then (0, 1473) else (0, 1475)) else (if k.val < 40 then (1, 1474) else (0, 1607)))) else (if k.val < 45 then (if k.val < 43 then (if k.val < 42 then (0, 1611) else (0, 1615)) else (if k.val < 44 then (1, 1603) else (1, 1616))) else (if k.val < 47 then (if k.val < 46 then (1, 1617) else (0, 1746)) else (if k.val < 48 then (0, 1749) else (if k.val < 49 then (0, 1757) else (0, 1759)))))) else (if k.val < 58 then (if k.val < 54 then (if k.val < 52 then (if k.val < 51 then (1, 1756) else (1, 1757)) else (if k.val < 53 then (1, 1758) else (0, 1884))) else (if k.val < 56 then (if k.val < 55 then (0, 1886) else (0, 1887)) else (if k.val < 57 then (0, 1889) else (0, 1894)))) else (if k.val < 62 then (if k.val < 60 then (if k.val < 59 then (1, 1882) else (1, 1883)) else (if k.val < 61 then (1, 1888) else (1, 1889))) else (if k.val < 64 then (if k.val < 63 then (1, 1891) else (1, 1892)) else (if k.val < 65 then (1, 1896) else (if k.val < 66 then (0, 2027) else (0, 2039)))))))) else (if k.val < 101 then (if k.val < 84 then (if k.val < 75 then (if k.val < 71 then (if k.val < 69 then (if k.val < 68 then (1, 2023) else (1, 2027)) else (if k.val < 70 then (1, 2032) else (1, 2038))) else (if k.val < 73 then (if k.val < 72 then (1, 2039) else (0, 2164)) else (if k.val < 74 then (0, 2166) else (0, 2168)))) else (if k.val < 79 then (if k.val < 77 then (if k.val < 76 then (0, 2169) else (0, 2173)) else (if k.val < 78 then (0, 2179) else (1, 2163))) else (if k.val < 81 then (if k.val < 80 then (1, 2167) else (1, 2173)) else (if k.val < 82 then (1, 2175) else (if k.val < 83 then (0, 2300) else (0, 2303)))))) else (if k.val < 92 then (if k.val < 88 then (if k.val < 86 then (if k.val < 85 then (0, 2307) else (0, 2309)) else (if k.val < 87 then (1, 2305) else (1, 2308))) else (if k.val < 90 then (if k.val < 89 then (1, 2309) else (1, 2311)) else (if k.val < 91 then (1, 2317) else (0, 2440)))) else (if k.val < 96 then (if k.val < 94 then (if k.val < 93 then (0, 2443) else (0, 2444)) else (if k.val < 95 then (0, 2447) else (0, 2449))) else (if k.val < 98 then (if k.val < 97 then (0, 2450) else (0, 2455)) else (if k.val < 99 then (0, 2457) else (if k.val < 100 then (1, 2441) else (1, 2444))))))) else (if k.val < 118 then (if k.val < 109 then (if k.val < 105 then (if k.val < 103 then (if k.val < 102 then (1, 2447) else (1, 2449)) else (if k.val < 104 then (1, 2456) else (0, 2583))) else (if k.val < 107 then (if k.val < 106 then (0, 2586) else (0, 2588)) else (if k.val < 108 then (0, 2591) else (0, 2594)))) else (if k.val < 113 then (if k.val < 111 then (if k.val < 110 then (0, 2597) else (1, 2581)) else (if k.val < 112 then (1, 2584) else (1, 2585))) else (if k.val < 115 then (if k.val < 114 then (1, 2592) else (1, 2594)) else (if k.val < 116 then (1, 2596) else (if k.val < 117 then (1, 2598) else (1, 2599)))))) else (if k.val < 126 then (if k.val < 122 then (if k.val < 120 then (if k.val < 119 then (0, 2726) else (0, 2728)) else (if k.val < 121 then (0, 2731) else (0, 2732))) else (if k.val < 124 then (if k.val < 123 then (0, 2733) else (0, 2734)) else (if k.val < 125 then (0, 2735) else (0, 2739)))) else (if k.val < 130 then (if k.val < 128 then (if k.val < 127 then (1, 2720) else (1, 2726)) else (if k.val < 129 then (1, 2729) else (1, 2733))) else (if k.val < 132 then (if k.val < 131 then (1, 2736) else (0, 2860)) else (if k.val < 133 then (0, 2862) else (if k.val < 134 then (0, 2863) else (0, 2865))))))))) else (if k.val < 203 then (if k.val < 169 then (if k.val < 152 then (if k.val < 143 then (if k.val < 139 then (if k.val < 137 then (if k.val < 136 then (0, 2869) else (0, 2875)) else (if k.val < 138 then (1, 2862) else (1, 2864))) else (if k.val < 141 then (if k.val < 140 then (1, 2865) else (1, 2868)) else (if k.val < 142 then (1, 2874) else (0, 3002)))) else (if k.val < 147 then (if k.val < 145 then (if k.val < 144 then (0, 3003) else (0, 3006)) else (if k.val < 146 then (0, 3014) else (0, 3016))) else (if k.val < 149 then (if k.val < 148 then (0, 3018) else (1, 3000)) else (if k.val < 150 then (1, 3001) else (if k.val < 151 then (1, 3003) else (1, 3005)))))) else (if k.val < 160 then (if k.val < 156 then (if k.val < 154 then (if k.val < 153 then (1, 3007) else (1, 3009)) else (if k.val < 155 then (1, 3015) else (1, 3017))) else (if k.val < 158 then (if k.val < 157 then (1, 3018) else (1, 3019)) else (if k.val < 159 then (0, 3149) else (0, 3153)))) else (if k.val < 164 then (if k.val < 162 then (if k.val < 161 then (0, 3154) else (0, 3156)) else (if k.val < 163 then (0, 3157) else (1, 3140))) else (if k.val < 166 then (if k.val < 165 then (1, 3142) else (1, 3143)) else (if k.val < 167 then (1, 3144) else (if k.val < 168 then (1, 3145) else (1, 3148))))))) else (if k.val < 186 then (if k.val < 177 then (if k.val < 173 then (if k.val < 171 then (if k.val < 170 then (1, 3150) else (1, 3151)) else (if k.val < 172 then (1, 3159) else (0, 3280))) else (if k.val < 175 then (if k.val < 174 then (0, 3283) else (0, 3285)) else (if k.val < 176 then (0, 3288) else (0, 3290)))) else (if k.val < 181 then (if k.val < 179 then (if k.val < 178 then (0, 3294) else (0, 3296)) else (if k.val < 180 then (0, 3297) else (0, 3299))) else (if k.val < 183 then (if k.val < 182 then (1, 3281) else (1, 3284)) else (if k.val < 184 then (1, 3289) else (if k.val < 185 then (1, 3291) else (1, 3292)))))) else (if k.val < 194 then (if k.val < 190 then (if k.val < 188 then (if k.val < 187 then (1, 3293) else (1, 3297)) else (if k.val < 189 then (0, 3424) else (0, 3426))) else (if k.val < 192 then (if k.val < 191 then (0, 3429) else (0, 3430)) else (if k.val < 193 then (0, 3438) else (1, 3423)))) else (if k.val < 198 then (if k.val < 196 then (if k.val < 195 then (1, 3424) else (1, 3425)) else (if k.val < 197 then (1, 3426) else (1, 3430))) else (if k.val < 200 then (if k.val < 199 then (1, 3432) else (1, 3433)) else (if k.val < 201 then (1, 3434) else (if k.val < 202 then (1, 3438) else (0, 3570)))))))) else (if k.val < 237 then (if k.val < 220 then (if k.val < 211 then (if k.val < 207 then (if k.val < 205 then (if k.val < 204 then (0, 3571) else (0, 3572)) else (if k.val < 206 then (0, 3575) else (0, 3577))) else (if k.val < 209 then (if k.val < 208 then (1, 3560) else (1, 3563)) else (if k.val < 210 then (1, 3571) else (1, 3574)))) else (if k.val < 215 then (if k.val < 213 then (if k.val < 212 then (1, 3576) else (0, 3700)) else (if k.val < 214 then (0, 3701) else (0, 3709))) else (if k.val < 217 then (if k.val < 216 then (0, 3710) else (0, 3714)) else (if k.val < 218 then (0, 3717) else (if k.val < 219 then (0, 3719) else (1, 3703)))))) else (if k.val < 228 then (if k.val < 224 then (if k.val < 222 then (if k.val < 221 then (1, 3705) else (1, 3711)) else (if k.val < 223 then (1, 3717) else (1, 3718))) else (if k.val < 226 then (if k.val < 225 then (0, 3840) else (0, 3841)) else (if k.val < 227 then (0, 3842) else (0, 3844)))) else (if k.val < 232 then (if k.val < 230 then (if k.val < 229 then (0, 3849) else (0, 3851)) else (if k.val < 231 then (0, 3852) else (0, 3853))) else (if k.val < 234 then (if k.val < 233 then (0, 3857) else (0, 3858)) else (if k.val < 235 then (1, 3843) else (if k.val < 236 then (1, 3846) else (1, 3847))))))) else (if k.val < 254 then (if k.val < 245 then (if k.val < 241 then (if k.val < 239 then (if k.val < 238 then (1, 3848) else (1, 3849)) else (if k.val < 240 then (1, 3851) else (1, 3853))) else (if k.val < 243 then (if k.val < 242 then (1, 3854) else (1, 3859)) else (if k.val < 244 then (0, 3980) else (0, 3982)))) else (if k.val < 249 then (if k.val < 247 then (if k.val < 246 then (0, 3983) else (0, 3984)) else (if k.val < 248 then (0, 3985) else (0, 3986))) else (if k.val < 251 then (if k.val < 250 then (0, 3988) else (0, 3989)) else (if k.val < 252 then (0, 3990) else (if k.val < 253 then (0, 3991) else (0, 3992)))))) else (if k.val < 262 then (if k.val < 258 then (if k.val < 256 then (if k.val < 255 then (0, 3993) else (0, 3994)) else (if k.val < 257 then (0, 3995) else (0, 3996))) else (if k.val < 260 then (if k.val < 259 then (0, 3997) else (0, 3998)) else (if k.val < 261 then (0, 3999) else (1, 3980)))) else (if k.val < 266 then (if k.val < 264 then (if k.val < 263 then (1, 3981) else (1, 3987)) else (if k.val < 265 then (1, 3990) else (1, 3992))) else (if k.val < 268 then (if k.val < 267 then (1, 3994) else (1, 3995)) else (if k.val < 269 then (1, 3997) else (if k.val < 270 then (1, 3998) else (1, 3999))))))))))

@[expose] public def residualCheck (k : Fin 271) : Prop :=
  stepCheck (target k).1 (target k).2

/-- Groups 0, 1, 2 contain 68 transitions; group 3 contains 67. -/
@[expose] public def residualBatch (g : Fin 4) : Prop :=
  ∀ (s : Fin 68) (h : 68 * g.val + s.val < 271),
    residualCheck ⟨68 * g.val + s.val, h⟩

public theorem all_of_batches (h : ∀ g : Fin 4, residualBatch g) :
    ∀ k : Fin 271, residualCheck k := by
  intro k
  let g : Fin 4 := ⟨k.val / 68, by omega⟩
  let s : Fin 68 := ⟨k.val % 68, by omega⟩
  have hlt : 68 * g.val + s.val < 271 := by dsimp [g, s]; omega
  have hk : (⟨68 * g.val + s.val, hlt⟩ : Fin 271) = k := by
    apply Fin.ext
    dsimp [g, s]
    omega
  simpa only [hk] using h g s hlt

set_option maxHeartbeats 1600000 in
private theorem point0_0_0 : stepCheck 0 60 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_1 : stepCheck 0 61 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_2 : stepCheck 0 62 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_3 : stepCheck 0 63 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_4 : stepCheck 0 64 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_5 : stepCheck 0 65 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_6 : stepCheck 0 66 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_7 : stepCheck 0 67 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_8 : stepCheck 0 68 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_9 : stepCheck 0 69 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_10 : stepCheck 0 70 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_11 : stepCheck 0 71 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_12 : stepCheck 0 72 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_13 : stepCheck 0 73 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_14 : stepCheck 0 74 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_15 : stepCheck 0 75 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_16 : stepCheck 0 76 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_17 : stepCheck 0 77 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_18 : stepCheck 0 78 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_19 : stepCheck 0 79 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_0 : stepCheck 1 60 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_1 : stepCheck 1 61 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_2 : stepCheck 1 62 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_3 : stepCheck 1 63 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_4 : stepCheck 1 64 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_5 : stepCheck 1 65 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_6 : stepCheck 1 66 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_7 : stepCheck 1 67 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_8 : stepCheck 1 68 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_9 : stepCheck 1 69 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_10 : stepCheck 1 70 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_11 : stepCheck 1 71 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_12 : stepCheck 1 72 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_13 : stepCheck 1 73 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_14 : stepCheck 1 74 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_15 : stepCheck 1 75 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_16 : stepCheck 1 76 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_17 : stepCheck 1 77 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_18 : stepCheck 1 78 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_19 : stepCheck 1 79 := by
  left
  decide +kernel

private theorem checked0 (_h : ∀ k : Fin 271, residualCheck k) : stepBatch 3 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point0_0_0
  · exact point0_0_1
  · exact point0_0_2
  · exact point0_0_3
  · exact point0_0_4
  · exact point0_0_5
  · exact point0_0_6
  · exact point0_0_7
  · exact point0_0_8
  · exact point0_0_9
  · exact point0_0_10
  · exact point0_0_11
  · exact point0_0_12
  · exact point0_0_13
  · exact point0_0_14
  · exact point0_0_15
  · exact point0_0_16
  · exact point0_0_17
  · exact point0_0_18
  · exact point0_0_19
  · exact point0_1_0
  · exact point0_1_1
  · exact point0_1_2
  · exact point0_1_3
  · exact point0_1_4
  · exact point0_1_5
  · exact point0_1_6
  · exact point0_1_7
  · exact point0_1_8
  · exact point0_1_9
  · exact point0_1_10
  · exact point0_1_11
  · exact point0_1_12
  · exact point0_1_13
  · exact point0_1_14
  · exact point0_1_15
  · exact point0_1_16
  · exact point0_1_17
  · exact point0_1_18
  · exact point0_1_19

set_option maxHeartbeats 1600000 in
private theorem point1_0_0 : stepCheck 0 200 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_1 : stepCheck 0 201 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_2 : stepCheck 0 202 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_3 : stepCheck 0 203 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_4 : stepCheck 0 204 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_5 : stepCheck 0 205 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_6 : stepCheck 0 206 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_7 : stepCheck 0 207 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_8 : stepCheck 0 208 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_9 : stepCheck 0 209 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_10 : stepCheck 0 210 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_11 : stepCheck 0 211 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_12 : stepCheck 0 212 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_13 : stepCheck 0 213 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_14 : stepCheck 0 214 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_15 : stepCheck 0 215 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_16 : stepCheck 0 216 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_17 : stepCheck 0 217 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_18 : stepCheck 0 218 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_19 : stepCheck 0 219 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_0 : stepCheck 1 200 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_1 : stepCheck 1 201 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_2 : stepCheck 1 202 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_3 : stepCheck 1 203 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_4 : stepCheck 1 204 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_5 : stepCheck 1 205 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_6 : stepCheck 1 206 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_7 : stepCheck 1 207 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_8 : stepCheck 1 208 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_9 : stepCheck 1 209 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_10 : stepCheck 1 210 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_11 : stepCheck 1 211 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_12 : stepCheck 1 212 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_13 : stepCheck 1 213 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_14 : stepCheck 1 214 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_15 : stepCheck 1 215 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_16 : stepCheck 1 216 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_17 : stepCheck 1 217 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_18 : stepCheck 1 218 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_19 : stepCheck 1 219 := by
  left
  decide +kernel

private theorem checked1 (_h : ∀ k : Fin 271, residualCheck k) : stepBatch 10 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point1_0_0
  · exact point1_0_1
  · exact point1_0_2
  · exact point1_0_3
  · exact point1_0_4
  · exact point1_0_5
  · exact point1_0_6
  · exact point1_0_7
  · exact point1_0_8
  · exact point1_0_9
  · exact point1_0_10
  · exact point1_0_11
  · exact point1_0_12
  · exact point1_0_13
  · exact point1_0_14
  · exact point1_0_15
  · exact point1_0_16
  · exact point1_0_17
  · exact point1_0_18
  · exact point1_0_19
  · exact point1_1_0
  · exact point1_1_1
  · exact point1_1_2
  · exact point1_1_3
  · exact point1_1_4
  · exact point1_1_5
  · exact point1_1_6
  · exact point1_1_7
  · exact point1_1_8
  · exact point1_1_9
  · exact point1_1_10
  · exact point1_1_11
  · exact point1_1_12
  · exact point1_1_13
  · exact point1_1_14
  · exact point1_1_15
  · exact point1_1_16
  · exact point1_1_17
  · exact point1_1_18
  · exact point1_1_19

set_option maxHeartbeats 1600000 in
private theorem point2_0_0 : stepCheck 0 340 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_1 : stepCheck 0 341 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_2 : stepCheck 0 342 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_3 : stepCheck 0 343 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_4 : stepCheck 0 344 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_5 : stepCheck 0 345 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_6 : stepCheck 0 346 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_7 : stepCheck 0 347 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_8 : stepCheck 0 348 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_9 : stepCheck 0 349 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_10 : stepCheck 0 350 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_11 : stepCheck 0 351 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_12 : stepCheck 0 352 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_14 : stepCheck 0 354 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_15 : stepCheck 0 355 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_16 : stepCheck 0 356 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_17 : stepCheck 0 357 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_19 : stepCheck 0 359 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_0 : stepCheck 1 340 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_1 : stepCheck 1 341 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_2 : stepCheck 1 342 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_3 : stepCheck 1 343 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_4 : stepCheck 1 344 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_5 : stepCheck 1 345 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_6 : stepCheck 1 346 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_7 : stepCheck 1 347 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_8 : stepCheck 1 348 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_9 : stepCheck 1 349 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_10 : stepCheck 1 350 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_11 : stepCheck 1 351 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_12 : stepCheck 1 352 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_13 : stepCheck 1 353 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_14 : stepCheck 1 354 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_15 : stepCheck 1 355 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_16 : stepCheck 1 356 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_17 : stepCheck 1 357 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_18 : stepCheck 1 358 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_19 : stepCheck 1 359 := by
  left
  decide +kernel

private theorem checked2 (_h : ∀ k : Fin 271, residualCheck k) : stepBatch 17 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point2_0_0
  · exact point2_0_1
  · exact point2_0_2
  · exact point2_0_3
  · exact point2_0_4
  · exact point2_0_5
  · exact point2_0_6
  · exact point2_0_7
  · exact point2_0_8
  · exact point2_0_9
  · exact point2_0_10
  · exact point2_0_11
  · exact point2_0_12
  · exact _h 0
  · exact point2_0_14
  · exact point2_0_15
  · exact point2_0_16
  · exact point2_0_17
  · exact _h 1
  · exact point2_0_19
  · exact point2_1_0
  · exact point2_1_1
  · exact point2_1_2
  · exact point2_1_3
  · exact point2_1_4
  · exact point2_1_5
  · exact point2_1_6
  · exact point2_1_7
  · exact point2_1_8
  · exact point2_1_9
  · exact point2_1_10
  · exact point2_1_11
  · exact point2_1_12
  · exact point2_1_13
  · exact point2_1_14
  · exact point2_1_15
  · exact point2_1_16
  · exact point2_1_17
  · exact point2_1_18
  · exact point2_1_19

set_option maxHeartbeats 1600000 in
private theorem point3_0_0 : stepCheck 0 480 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_1 : stepCheck 0 481 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_2 : stepCheck 0 482 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_3 : stepCheck 0 483 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_4 : stepCheck 0 484 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_6 : stepCheck 0 486 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_7 : stepCheck 0 487 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_9 : stepCheck 0 489 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_11 : stepCheck 0 491 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_12 : stepCheck 0 492 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_13 : stepCheck 0 493 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_14 : stepCheck 0 494 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_15 : stepCheck 0 495 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_16 : stepCheck 0 496 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_17 : stepCheck 0 497 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_18 : stepCheck 0 498 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_19 : stepCheck 0 499 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_0 : stepCheck 1 480 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_1 : stepCheck 1 481 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_2 : stepCheck 1 482 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_3 : stepCheck 1 483 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_5 : stepCheck 1 485 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_6 : stepCheck 1 486 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_8 : stepCheck 1 488 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_9 : stepCheck 1 489 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_10 : stepCheck 1 490 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_11 : stepCheck 1 491 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_12 : stepCheck 1 492 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_13 : stepCheck 1 493 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_14 : stepCheck 1 494 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_15 : stepCheck 1 495 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_16 : stepCheck 1 496 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_17 : stepCheck 1 497 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_18 : stepCheck 1 498 := by
  left
  decide +kernel

private theorem checked3 (_h : ∀ k : Fin 271, residualCheck k) : stepBatch 24 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point3_0_0
  · exact point3_0_1
  · exact point3_0_2
  · exact point3_0_3
  · exact point3_0_4
  · exact _h 2
  · exact point3_0_6
  · exact point3_0_7
  · exact _h 3
  · exact point3_0_9
  · exact _h 4
  · exact point3_0_11
  · exact point3_0_12
  · exact point3_0_13
  · exact point3_0_14
  · exact point3_0_15
  · exact point3_0_16
  · exact point3_0_17
  · exact point3_0_18
  · exact point3_0_19
  · exact point3_1_0
  · exact point3_1_1
  · exact point3_1_2
  · exact point3_1_3
  · exact _h 5
  · exact point3_1_5
  · exact point3_1_6
  · exact _h 6
  · exact point3_1_8
  · exact point3_1_9
  · exact point3_1_10
  · exact point3_1_11
  · exact point3_1_12
  · exact point3_1_13
  · exact point3_1_14
  · exact point3_1_15
  · exact point3_1_16
  · exact point3_1_17
  · exact point3_1_18
  · exact _h 7

set_option maxHeartbeats 1600000 in
private theorem point4_0_0 : stepCheck 0 620 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_1 : stepCheck 0 621 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_2 : stepCheck 0 622 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_3 : stepCheck 0 623 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_4 : stepCheck 0 624 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_5 : stepCheck 0 625 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_6 : stepCheck 0 626 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_7 : stepCheck 0 627 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_8 : stepCheck 0 628 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_9 : stepCheck 0 629 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_10 : stepCheck 0 630 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_11 : stepCheck 0 631 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_12 : stepCheck 0 632 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_13 : stepCheck 0 633 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_14 : stepCheck 0 634 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_15 : stepCheck 0 635 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_16 : stepCheck 0 636 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_17 : stepCheck 0 637 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_18 : stepCheck 0 638 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_19 : stepCheck 0 639 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_0 : stepCheck 1 620 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_1 : stepCheck 1 621 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_2 : stepCheck 1 622 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_3 : stepCheck 1 623 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_4 : stepCheck 1 624 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_5 : stepCheck 1 625 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_6 : stepCheck 1 626 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_7 : stepCheck 1 627 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_8 : stepCheck 1 628 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_9 : stepCheck 1 629 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_10 : stepCheck 1 630 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_11 : stepCheck 1 631 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_12 : stepCheck 1 632 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_13 : stepCheck 1 633 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_14 : stepCheck 1 634 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_15 : stepCheck 1 635 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_16 : stepCheck 1 636 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_17 : stepCheck 1 637 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_18 : stepCheck 1 638 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_19 : stepCheck 1 639 := by
  left
  decide +kernel

private theorem checked4 (_h : ∀ k : Fin 271, residualCheck k) : stepBatch 31 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point4_0_0
  · exact point4_0_1
  · exact point4_0_2
  · exact point4_0_3
  · exact point4_0_4
  · exact point4_0_5
  · exact point4_0_6
  · exact point4_0_7
  · exact point4_0_8
  · exact point4_0_9
  · exact point4_0_10
  · exact point4_0_11
  · exact point4_0_12
  · exact point4_0_13
  · exact point4_0_14
  · exact point4_0_15
  · exact point4_0_16
  · exact point4_0_17
  · exact point4_0_18
  · exact point4_0_19
  · exact point4_1_0
  · exact point4_1_1
  · exact point4_1_2
  · exact point4_1_3
  · exact point4_1_4
  · exact point4_1_5
  · exact point4_1_6
  · exact point4_1_7
  · exact point4_1_8
  · exact point4_1_9
  · exact point4_1_10
  · exact point4_1_11
  · exact point4_1_12
  · exact point4_1_13
  · exact point4_1_14
  · exact point4_1_15
  · exact point4_1_16
  · exact point4_1_17
  · exact point4_1_18
  · exact point4_1_19

set_option maxHeartbeats 1600000 in
private theorem point5_0_0 : stepCheck 0 760 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_1 : stepCheck 0 761 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_2 : stepCheck 0 762 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_3 : stepCheck 0 763 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_4 : stepCheck 0 764 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_5 : stepCheck 0 765 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_6 : stepCheck 0 766 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_8 : stepCheck 0 768 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_9 : stepCheck 0 769 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_10 : stepCheck 0 770 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_11 : stepCheck 0 771 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_14 : stepCheck 0 774 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_15 : stepCheck 0 775 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_16 : stepCheck 0 776 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_17 : stepCheck 0 777 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_18 : stepCheck 0 778 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_19 : stepCheck 0 779 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_0 : stepCheck 1 760 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_1 : stepCheck 1 761 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_2 : stepCheck 1 762 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_3 : stepCheck 1 763 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_4 : stepCheck 1 764 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_5 : stepCheck 1 765 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_6 : stepCheck 1 766 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_7 : stepCheck 1 767 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_8 : stepCheck 1 768 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_9 : stepCheck 1 769 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_10 : stepCheck 1 770 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_11 : stepCheck 1 771 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_12 : stepCheck 1 772 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_13 : stepCheck 1 773 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_14 : stepCheck 1 774 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_15 : stepCheck 1 775 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_16 : stepCheck 1 776 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_19 : stepCheck 1 779 := by
  left
  decide +kernel

private theorem checked5 (_h : ∀ k : Fin 271, residualCheck k) : stepBatch 38 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point5_0_0
  · exact point5_0_1
  · exact point5_0_2
  · exact point5_0_3
  · exact point5_0_4
  · exact point5_0_5
  · exact point5_0_6
  · exact _h 8
  · exact point5_0_8
  · exact point5_0_9
  · exact point5_0_10
  · exact point5_0_11
  · exact _h 9
  · exact _h 10
  · exact point5_0_14
  · exact point5_0_15
  · exact point5_0_16
  · exact point5_0_17
  · exact point5_0_18
  · exact point5_0_19
  · exact point5_1_0
  · exact point5_1_1
  · exact point5_1_2
  · exact point5_1_3
  · exact point5_1_4
  · exact point5_1_5
  · exact point5_1_6
  · exact point5_1_7
  · exact point5_1_8
  · exact point5_1_9
  · exact point5_1_10
  · exact point5_1_11
  · exact point5_1_12
  · exact point5_1_13
  · exact point5_1_14
  · exact point5_1_15
  · exact point5_1_16
  · exact _h 11
  · exact _h 12
  · exact point5_1_19

set_option maxHeartbeats 1600000 in
private theorem point6_0_0 : stepCheck 0 900 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_1 : stepCheck 0 901 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_3 : stepCheck 0 903 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_5 : stepCheck 0 905 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_6 : stepCheck 0 906 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_7 : stepCheck 0 907 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_8 : stepCheck 0 908 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_9 : stepCheck 0 909 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_10 : stepCheck 0 910 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_11 : stepCheck 0 911 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_12 : stepCheck 0 912 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_13 : stepCheck 0 913 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_14 : stepCheck 0 914 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_15 : stepCheck 0 915 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_16 : stepCheck 0 916 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_17 : stepCheck 0 917 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_18 : stepCheck 0 918 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_19 : stepCheck 0 919 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_0 : stepCheck 1 900 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_1 : stepCheck 1 901 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_2 : stepCheck 1 902 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_3 : stepCheck 1 903 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_4 : stepCheck 1 904 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_5 : stepCheck 1 905 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_6 : stepCheck 1 906 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_7 : stepCheck 1 907 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_9 : stepCheck 1 909 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_10 : stepCheck 1 910 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_11 : stepCheck 1 911 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_12 : stepCheck 1 912 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_13 : stepCheck 1 913 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_14 : stepCheck 1 914 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_15 : stepCheck 1 915 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_16 : stepCheck 1 916 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_17 : stepCheck 1 917 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_18 : stepCheck 1 918 := by
  left
  decide +kernel

private theorem checked6 (_h : ∀ k : Fin 271, residualCheck k) : stepBatch 45 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point6_0_0
  · exact point6_0_1
  · exact _h 13
  · exact point6_0_3
  · exact _h 14
  · exact point6_0_5
  · exact point6_0_6
  · exact point6_0_7
  · exact point6_0_8
  · exact point6_0_9
  · exact point6_0_10
  · exact point6_0_11
  · exact point6_0_12
  · exact point6_0_13
  · exact point6_0_14
  · exact point6_0_15
  · exact point6_0_16
  · exact point6_0_17
  · exact point6_0_18
  · exact point6_0_19
  · exact point6_1_0
  · exact point6_1_1
  · exact point6_1_2
  · exact point6_1_3
  · exact point6_1_4
  · exact point6_1_5
  · exact point6_1_6
  · exact point6_1_7
  · exact _h 15
  · exact point6_1_9
  · exact point6_1_10
  · exact point6_1_11
  · exact point6_1_12
  · exact point6_1_13
  · exact point6_1_14
  · exact point6_1_15
  · exact point6_1_16
  · exact point6_1_17
  · exact point6_1_18
  · exact _h 16

set_option maxHeartbeats 1600000 in
private theorem point7_0_0 : stepCheck 0 1040 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_1 : stepCheck 0 1041 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_2 : stepCheck 0 1042 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_3 : stepCheck 0 1043 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_4 : stepCheck 0 1044 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_5 : stepCheck 0 1045 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_6 : stepCheck 0 1046 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_7 : stepCheck 0 1047 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_8 : stepCheck 0 1048 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_9 : stepCheck 0 1049 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_10 : stepCheck 0 1050 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_11 : stepCheck 0 1051 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_12 : stepCheck 0 1052 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_14 : stepCheck 0 1054 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_16 : stepCheck 0 1056 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_17 : stepCheck 0 1057 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_18 : stepCheck 0 1058 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_19 : stepCheck 0 1059 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_1 : stepCheck 1 1041 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_2 : stepCheck 1 1042 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_3 : stepCheck 1 1043 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_4 : stepCheck 1 1044 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_5 : stepCheck 1 1045 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_6 : stepCheck 1 1046 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_7 : stepCheck 1 1047 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_8 : stepCheck 1 1048 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_9 : stepCheck 1 1049 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_10 : stepCheck 1 1050 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_11 : stepCheck 1 1051 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_12 : stepCheck 1 1052 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_13 : stepCheck 1 1053 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_14 : stepCheck 1 1054 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_15 : stepCheck 1 1055 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_16 : stepCheck 1 1056 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_18 : stepCheck 1 1058 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_19 : stepCheck 1 1059 := by
  left
  decide +kernel

private theorem checked7 (_h : ∀ k : Fin 271, residualCheck k) : stepBatch 52 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point7_0_0
  · exact point7_0_1
  · exact point7_0_2
  · exact point7_0_3
  · exact point7_0_4
  · exact point7_0_5
  · exact point7_0_6
  · exact point7_0_7
  · exact point7_0_8
  · exact point7_0_9
  · exact point7_0_10
  · exact point7_0_11
  · exact point7_0_12
  · exact _h 17
  · exact point7_0_14
  · exact _h 18
  · exact point7_0_16
  · exact point7_0_17
  · exact point7_0_18
  · exact point7_0_19
  · exact _h 19
  · exact point7_1_1
  · exact point7_1_2
  · exact point7_1_3
  · exact point7_1_4
  · exact point7_1_5
  · exact point7_1_6
  · exact point7_1_7
  · exact point7_1_8
  · exact point7_1_9
  · exact point7_1_10
  · exact point7_1_11
  · exact point7_1_12
  · exact point7_1_13
  · exact point7_1_14
  · exact point7_1_15
  · exact point7_1_16
  · exact _h 20
  · exact point7_1_18
  · exact point7_1_19

set_option maxHeartbeats 1600000 in
private theorem point8_0_0 : stepCheck 0 1180 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_1 : stepCheck 0 1181 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_2 : stepCheck 0 1182 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_4 : stepCheck 0 1184 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_5 : stepCheck 0 1185 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_6 : stepCheck 0 1186 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_7 : stepCheck 0 1187 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_9 : stepCheck 0 1189 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_10 : stepCheck 0 1190 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_12 : stepCheck 0 1192 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_13 : stepCheck 0 1193 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_14 : stepCheck 0 1194 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_15 : stepCheck 0 1195 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_16 : stepCheck 0 1196 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_17 : stepCheck 0 1197 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_18 : stepCheck 0 1198 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_19 : stepCheck 0 1199 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_0 : stepCheck 1 1180 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_2 : stepCheck 1 1182 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_3 : stepCheck 1 1183 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_4 : stepCheck 1 1184 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_6 : stepCheck 1 1186 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_7 : stepCheck 1 1187 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_8 : stepCheck 1 1188 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_9 : stepCheck 1 1189 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_10 : stepCheck 1 1190 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_11 : stepCheck 1 1191 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_12 : stepCheck 1 1192 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_13 : stepCheck 1 1193 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_14 : stepCheck 1 1194 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_15 : stepCheck 1 1195 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_18 : stepCheck 1 1198 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_19 : stepCheck 1 1199 := by
  left
  decide +kernel

private theorem checked8 (_h : ∀ k : Fin 271, residualCheck k) : stepBatch 59 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point8_0_0
  · exact point8_0_1
  · exact point8_0_2
  · exact _h 21
  · exact point8_0_4
  · exact point8_0_5
  · exact point8_0_6
  · exact point8_0_7
  · exact _h 22
  · exact point8_0_9
  · exact point8_0_10
  · exact _h 23
  · exact point8_0_12
  · exact point8_0_13
  · exact point8_0_14
  · exact point8_0_15
  · exact point8_0_16
  · exact point8_0_17
  · exact point8_0_18
  · exact point8_0_19
  · exact point8_1_0
  · exact _h 24
  · exact point8_1_2
  · exact point8_1_3
  · exact point8_1_4
  · exact _h 25
  · exact point8_1_6
  · exact point8_1_7
  · exact point8_1_8
  · exact point8_1_9
  · exact point8_1_10
  · exact point8_1_11
  · exact point8_1_12
  · exact point8_1_13
  · exact point8_1_14
  · exact point8_1_15
  · exact _h 26
  · exact _h 27
  · exact point8_1_18
  · exact point8_1_19

set_option maxHeartbeats 1600000 in
private theorem point9_0_1 : stepCheck 0 1321 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_2 : stepCheck 0 1322 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_3 : stepCheck 0 1323 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_4 : stepCheck 0 1324 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_5 : stepCheck 0 1325 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_6 : stepCheck 0 1326 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_8 : stepCheck 0 1328 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_10 : stepCheck 0 1330 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_11 : stepCheck 0 1331 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_12 : stepCheck 0 1332 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_13 : stepCheck 0 1333 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_14 : stepCheck 0 1334 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_15 : stepCheck 0 1335 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_16 : stepCheck 0 1336 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_17 : stepCheck 0 1337 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_18 : stepCheck 0 1338 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_19 : stepCheck 0 1339 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_0 : stepCheck 1 1320 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_1 : stepCheck 1 1321 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_2 : stepCheck 1 1322 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_3 : stepCheck 1 1323 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_4 : stepCheck 1 1324 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_5 : stepCheck 1 1325 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_6 : stepCheck 1 1326 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_7 : stepCheck 1 1327 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_9 : stepCheck 1 1329 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_10 : stepCheck 1 1330 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_11 : stepCheck 1 1331 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_12 : stepCheck 1 1332 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_13 : stepCheck 1 1333 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_14 : stepCheck 1 1334 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_15 : stepCheck 1 1335 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_16 : stepCheck 1 1336 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_17 : stepCheck 1 1337 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_18 : stepCheck 1 1338 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_19 : stepCheck 1 1339 := by
  left
  decide +kernel

private theorem checked9 (_h : ∀ k : Fin 271, residualCheck k) : stepBatch 66 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact _h 28
  · exact point9_0_1
  · exact point9_0_2
  · exact point9_0_3
  · exact point9_0_4
  · exact point9_0_5
  · exact point9_0_6
  · exact _h 29
  · exact point9_0_8
  · exact _h 30
  · exact point9_0_10
  · exact point9_0_11
  · exact point9_0_12
  · exact point9_0_13
  · exact point9_0_14
  · exact point9_0_15
  · exact point9_0_16
  · exact point9_0_17
  · exact point9_0_18
  · exact point9_0_19
  · exact point9_1_0
  · exact point9_1_1
  · exact point9_1_2
  · exact point9_1_3
  · exact point9_1_4
  · exact point9_1_5
  · exact point9_1_6
  · exact point9_1_7
  · exact _h 31
  · exact point9_1_9
  · exact point9_1_10
  · exact point9_1_11
  · exact point9_1_12
  · exact point9_1_13
  · exact point9_1_14
  · exact point9_1_15
  · exact point9_1_16
  · exact point9_1_17
  · exact point9_1_18
  · exact point9_1_19

set_option maxHeartbeats 1600000 in
private theorem point10_0_2 : stepCheck 0 1462 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_3 : stepCheck 0 1463 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_4 : stepCheck 0 1464 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_5 : stepCheck 0 1465 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_7 : stepCheck 0 1467 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_9 : stepCheck 0 1469 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_11 : stepCheck 0 1471 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_12 : stepCheck 0 1472 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_14 : stepCheck 0 1474 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_16 : stepCheck 0 1476 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_17 : stepCheck 0 1477 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_18 : stepCheck 0 1478 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_19 : stepCheck 0 1479 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_0 : stepCheck 1 1460 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_1 : stepCheck 1 1461 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_2 : stepCheck 1 1462 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_3 : stepCheck 1 1463 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_4 : stepCheck 1 1464 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_5 : stepCheck 1 1465 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_6 : stepCheck 1 1466 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_7 : stepCheck 1 1467 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_8 : stepCheck 1 1468 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_9 : stepCheck 1 1469 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_10 : stepCheck 1 1470 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_11 : stepCheck 1 1471 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_12 : stepCheck 1 1472 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_13 : stepCheck 1 1473 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_15 : stepCheck 1 1475 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_16 : stepCheck 1 1476 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_17 : stepCheck 1 1477 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_18 : stepCheck 1 1478 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_19 : stepCheck 1 1479 := by
  left
  decide +kernel

private theorem checked10 (_h : ∀ k : Fin 271, residualCheck k) : stepBatch 73 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact _h 32
  · exact _h 33
  · exact point10_0_2
  · exact point10_0_3
  · exact point10_0_4
  · exact point10_0_5
  · exact _h 34
  · exact point10_0_7
  · exact _h 35
  · exact point10_0_9
  · exact _h 36
  · exact point10_0_11
  · exact point10_0_12
  · exact _h 37
  · exact point10_0_14
  · exact _h 38
  · exact point10_0_16
  · exact point10_0_17
  · exact point10_0_18
  · exact point10_0_19
  · exact point10_1_0
  · exact point10_1_1
  · exact point10_1_2
  · exact point10_1_3
  · exact point10_1_4
  · exact point10_1_5
  · exact point10_1_6
  · exact point10_1_7
  · exact point10_1_8
  · exact point10_1_9
  · exact point10_1_10
  · exact point10_1_11
  · exact point10_1_12
  · exact point10_1_13
  · exact _h 39
  · exact point10_1_15
  · exact point10_1_16
  · exact point10_1_17
  · exact point10_1_18
  · exact point10_1_19

set_option maxHeartbeats 1600000 in
private theorem point11_0_0 : stepCheck 0 1600 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_1 : stepCheck 0 1601 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_2 : stepCheck 0 1602 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_3 : stepCheck 0 1603 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_4 : stepCheck 0 1604 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_5 : stepCheck 0 1605 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_6 : stepCheck 0 1606 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_8 : stepCheck 0 1608 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_9 : stepCheck 0 1609 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_10 : stepCheck 0 1610 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_12 : stepCheck 0 1612 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_13 : stepCheck 0 1613 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_14 : stepCheck 0 1614 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_16 : stepCheck 0 1616 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_17 : stepCheck 0 1617 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_18 : stepCheck 0 1618 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_19 : stepCheck 0 1619 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_0 : stepCheck 1 1600 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_1 : stepCheck 1 1601 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_2 : stepCheck 1 1602 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_4 : stepCheck 1 1604 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_5 : stepCheck 1 1605 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_6 : stepCheck 1 1606 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_7 : stepCheck 1 1607 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_8 : stepCheck 1 1608 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_9 : stepCheck 1 1609 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_10 : stepCheck 1 1610 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_11 : stepCheck 1 1611 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_12 : stepCheck 1 1612 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_13 : stepCheck 1 1613 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_14 : stepCheck 1 1614 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_15 : stepCheck 1 1615 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_18 : stepCheck 1 1618 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_19 : stepCheck 1 1619 := by
  left
  decide +kernel

private theorem checked11 (_h : ∀ k : Fin 271, residualCheck k) : stepBatch 80 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point11_0_0
  · exact point11_0_1
  · exact point11_0_2
  · exact point11_0_3
  · exact point11_0_4
  · exact point11_0_5
  · exact point11_0_6
  · exact _h 40
  · exact point11_0_8
  · exact point11_0_9
  · exact point11_0_10
  · exact _h 41
  · exact point11_0_12
  · exact point11_0_13
  · exact point11_0_14
  · exact _h 42
  · exact point11_0_16
  · exact point11_0_17
  · exact point11_0_18
  · exact point11_0_19
  · exact point11_1_0
  · exact point11_1_1
  · exact point11_1_2
  · exact _h 43
  · exact point11_1_4
  · exact point11_1_5
  · exact point11_1_6
  · exact point11_1_7
  · exact point11_1_8
  · exact point11_1_9
  · exact point11_1_10
  · exact point11_1_11
  · exact point11_1_12
  · exact point11_1_13
  · exact point11_1_14
  · exact point11_1_15
  · exact _h 44
  · exact _h 45
  · exact point11_1_18
  · exact point11_1_19

set_option maxHeartbeats 1600000 in
private theorem point12_0_0 : stepCheck 0 1740 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_1 : stepCheck 0 1741 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_2 : stepCheck 0 1742 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_3 : stepCheck 0 1743 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_4 : stepCheck 0 1744 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_5 : stepCheck 0 1745 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_7 : stepCheck 0 1747 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_8 : stepCheck 0 1748 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_10 : stepCheck 0 1750 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_11 : stepCheck 0 1751 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_12 : stepCheck 0 1752 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_13 : stepCheck 0 1753 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_14 : stepCheck 0 1754 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_15 : stepCheck 0 1755 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_16 : stepCheck 0 1756 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_18 : stepCheck 0 1758 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_0 : stepCheck 1 1740 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_1 : stepCheck 1 1741 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_2 : stepCheck 1 1742 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_3 : stepCheck 1 1743 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_4 : stepCheck 1 1744 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_5 : stepCheck 1 1745 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_6 : stepCheck 1 1746 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_7 : stepCheck 1 1747 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_8 : stepCheck 1 1748 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_9 : stepCheck 1 1749 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_10 : stepCheck 1 1750 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_11 : stepCheck 1 1751 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_12 : stepCheck 1 1752 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_13 : stepCheck 1 1753 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_14 : stepCheck 1 1754 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_15 : stepCheck 1 1755 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_19 : stepCheck 1 1759 := by
  left
  decide +kernel

private theorem checked12 (_h : ∀ k : Fin 271, residualCheck k) : stepBatch 87 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point12_0_0
  · exact point12_0_1
  · exact point12_0_2
  · exact point12_0_3
  · exact point12_0_4
  · exact point12_0_5
  · exact _h 46
  · exact point12_0_7
  · exact point12_0_8
  · exact _h 47
  · exact point12_0_10
  · exact point12_0_11
  · exact point12_0_12
  · exact point12_0_13
  · exact point12_0_14
  · exact point12_0_15
  · exact point12_0_16
  · exact _h 48
  · exact point12_0_18
  · exact _h 49
  · exact point12_1_0
  · exact point12_1_1
  · exact point12_1_2
  · exact point12_1_3
  · exact point12_1_4
  · exact point12_1_5
  · exact point12_1_6
  · exact point12_1_7
  · exact point12_1_8
  · exact point12_1_9
  · exact point12_1_10
  · exact point12_1_11
  · exact point12_1_12
  · exact point12_1_13
  · exact point12_1_14
  · exact point12_1_15
  · exact _h 50
  · exact _h 51
  · exact _h 52
  · exact point12_1_19

set_option maxHeartbeats 1600000 in
private theorem point13_0_0 : stepCheck 0 1880 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_1 : stepCheck 0 1881 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_2 : stepCheck 0 1882 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_3 : stepCheck 0 1883 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_5 : stepCheck 0 1885 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_8 : stepCheck 0 1888 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_10 : stepCheck 0 1890 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_11 : stepCheck 0 1891 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_12 : stepCheck 0 1892 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_13 : stepCheck 0 1893 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_15 : stepCheck 0 1895 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_16 : stepCheck 0 1896 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_17 : stepCheck 0 1897 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_18 : stepCheck 0 1898 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_19 : stepCheck 0 1899 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_0 : stepCheck 1 1880 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_1 : stepCheck 1 1881 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_4 : stepCheck 1 1884 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_5 : stepCheck 1 1885 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_6 : stepCheck 1 1886 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_7 : stepCheck 1 1887 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_10 : stepCheck 1 1890 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_13 : stepCheck 1 1893 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_14 : stepCheck 1 1894 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_15 : stepCheck 1 1895 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_17 : stepCheck 1 1897 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_18 : stepCheck 1 1898 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_19 : stepCheck 1 1899 := by
  left
  decide +kernel

private theorem checked13 (_h : ∀ k : Fin 271, residualCheck k) : stepBatch 94 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point13_0_0
  · exact point13_0_1
  · exact point13_0_2
  · exact point13_0_3
  · exact _h 53
  · exact point13_0_5
  · exact _h 54
  · exact _h 55
  · exact point13_0_8
  · exact _h 56
  · exact point13_0_10
  · exact point13_0_11
  · exact point13_0_12
  · exact point13_0_13
  · exact _h 57
  · exact point13_0_15
  · exact point13_0_16
  · exact point13_0_17
  · exact point13_0_18
  · exact point13_0_19
  · exact point13_1_0
  · exact point13_1_1
  · exact _h 58
  · exact _h 59
  · exact point13_1_4
  · exact point13_1_5
  · exact point13_1_6
  · exact point13_1_7
  · exact _h 60
  · exact _h 61
  · exact point13_1_10
  · exact _h 62
  · exact _h 63
  · exact point13_1_13
  · exact point13_1_14
  · exact point13_1_15
  · exact _h 64
  · exact point13_1_17
  · exact point13_1_18
  · exact point13_1_19

set_option maxHeartbeats 1600000 in
private theorem point14_0_0 : stepCheck 0 2020 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_1 : stepCheck 0 2021 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_2 : stepCheck 0 2022 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_3 : stepCheck 0 2023 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_4 : stepCheck 0 2024 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_5 : stepCheck 0 2025 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_6 : stepCheck 0 2026 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_8 : stepCheck 0 2028 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_9 : stepCheck 0 2029 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_10 : stepCheck 0 2030 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_11 : stepCheck 0 2031 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_12 : stepCheck 0 2032 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_13 : stepCheck 0 2033 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_14 : stepCheck 0 2034 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_15 : stepCheck 0 2035 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_16 : stepCheck 0 2036 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_17 : stepCheck 0 2037 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_18 : stepCheck 0 2038 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_0 : stepCheck 1 2020 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_1 : stepCheck 1 2021 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_2 : stepCheck 1 2022 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_4 : stepCheck 1 2024 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_5 : stepCheck 1 2025 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_6 : stepCheck 1 2026 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_8 : stepCheck 1 2028 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_9 : stepCheck 1 2029 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_10 : stepCheck 1 2030 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_11 : stepCheck 1 2031 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_13 : stepCheck 1 2033 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_14 : stepCheck 1 2034 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_15 : stepCheck 1 2035 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_16 : stepCheck 1 2036 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_17 : stepCheck 1 2037 := by
  left
  decide +kernel

private theorem checked14 (_h : ∀ k : Fin 271, residualCheck k) : stepBatch 101 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point14_0_0
  · exact point14_0_1
  · exact point14_0_2
  · exact point14_0_3
  · exact point14_0_4
  · exact point14_0_5
  · exact point14_0_6
  · exact _h 65
  · exact point14_0_8
  · exact point14_0_9
  · exact point14_0_10
  · exact point14_0_11
  · exact point14_0_12
  · exact point14_0_13
  · exact point14_0_14
  · exact point14_0_15
  · exact point14_0_16
  · exact point14_0_17
  · exact point14_0_18
  · exact _h 66
  · exact point14_1_0
  · exact point14_1_1
  · exact point14_1_2
  · exact _h 67
  · exact point14_1_4
  · exact point14_1_5
  · exact point14_1_6
  · exact _h 68
  · exact point14_1_8
  · exact point14_1_9
  · exact point14_1_10
  · exact point14_1_11
  · exact _h 69
  · exact point14_1_13
  · exact point14_1_14
  · exact point14_1_15
  · exact point14_1_16
  · exact point14_1_17
  · exact _h 70
  · exact _h 71

set_option maxHeartbeats 1600000 in
private theorem point15_0_0 : stepCheck 0 2160 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_1 : stepCheck 0 2161 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_2 : stepCheck 0 2162 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_3 : stepCheck 0 2163 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_5 : stepCheck 0 2165 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_7 : stepCheck 0 2167 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_10 : stepCheck 0 2170 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_11 : stepCheck 0 2171 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_12 : stepCheck 0 2172 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_14 : stepCheck 0 2174 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_15 : stepCheck 0 2175 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_16 : stepCheck 0 2176 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_17 : stepCheck 0 2177 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_18 : stepCheck 0 2178 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_0 : stepCheck 1 2160 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_1 : stepCheck 1 2161 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_2 : stepCheck 1 2162 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_4 : stepCheck 1 2164 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_5 : stepCheck 1 2165 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_6 : stepCheck 1 2166 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_8 : stepCheck 1 2168 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_9 : stepCheck 1 2169 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_10 : stepCheck 1 2170 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_11 : stepCheck 1 2171 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_12 : stepCheck 1 2172 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_14 : stepCheck 1 2174 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_16 : stepCheck 1 2176 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_17 : stepCheck 1 2177 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_18 : stepCheck 1 2178 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_19 : stepCheck 1 2179 := by
  left
  decide +kernel

private theorem checked15 (_h : ∀ k : Fin 271, residualCheck k) : stepBatch 108 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point15_0_0
  · exact point15_0_1
  · exact point15_0_2
  · exact point15_0_3
  · exact _h 72
  · exact point15_0_5
  · exact _h 73
  · exact point15_0_7
  · exact _h 74
  · exact _h 75
  · exact point15_0_10
  · exact point15_0_11
  · exact point15_0_12
  · exact _h 76
  · exact point15_0_14
  · exact point15_0_15
  · exact point15_0_16
  · exact point15_0_17
  · exact point15_0_18
  · exact _h 77
  · exact point15_1_0
  · exact point15_1_1
  · exact point15_1_2
  · exact _h 78
  · exact point15_1_4
  · exact point15_1_5
  · exact point15_1_6
  · exact _h 79
  · exact point15_1_8
  · exact point15_1_9
  · exact point15_1_10
  · exact point15_1_11
  · exact point15_1_12
  · exact _h 80
  · exact point15_1_14
  · exact _h 81
  · exact point15_1_16
  · exact point15_1_17
  · exact point15_1_18
  · exact point15_1_19

set_option maxHeartbeats 1600000 in
private theorem point16_0_1 : stepCheck 0 2301 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_2 : stepCheck 0 2302 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_4 : stepCheck 0 2304 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_5 : stepCheck 0 2305 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_6 : stepCheck 0 2306 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_8 : stepCheck 0 2308 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_10 : stepCheck 0 2310 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_11 : stepCheck 0 2311 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_12 : stepCheck 0 2312 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_13 : stepCheck 0 2313 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_14 : stepCheck 0 2314 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_15 : stepCheck 0 2315 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_16 : stepCheck 0 2316 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_17 : stepCheck 0 2317 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_18 : stepCheck 0 2318 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_19 : stepCheck 0 2319 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_0 : stepCheck 1 2300 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_1 : stepCheck 1 2301 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_2 : stepCheck 1 2302 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_3 : stepCheck 1 2303 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_4 : stepCheck 1 2304 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_6 : stepCheck 1 2306 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_7 : stepCheck 1 2307 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_10 : stepCheck 1 2310 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_12 : stepCheck 1 2312 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_13 : stepCheck 1 2313 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_14 : stepCheck 1 2314 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_15 : stepCheck 1 2315 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_16 : stepCheck 1 2316 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_18 : stepCheck 1 2318 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_19 : stepCheck 1 2319 := by
  left
  decide +kernel

private theorem checked16 (_h : ∀ k : Fin 271, residualCheck k) : stepBatch 115 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact _h 82
  · exact point16_0_1
  · exact point16_0_2
  · exact _h 83
  · exact point16_0_4
  · exact point16_0_5
  · exact point16_0_6
  · exact _h 84
  · exact point16_0_8
  · exact _h 85
  · exact point16_0_10
  · exact point16_0_11
  · exact point16_0_12
  · exact point16_0_13
  · exact point16_0_14
  · exact point16_0_15
  · exact point16_0_16
  · exact point16_0_17
  · exact point16_0_18
  · exact point16_0_19
  · exact point16_1_0
  · exact point16_1_1
  · exact point16_1_2
  · exact point16_1_3
  · exact point16_1_4
  · exact _h 86
  · exact point16_1_6
  · exact point16_1_7
  · exact _h 87
  · exact _h 88
  · exact point16_1_10
  · exact _h 89
  · exact point16_1_12
  · exact point16_1_13
  · exact point16_1_14
  · exact point16_1_15
  · exact point16_1_16
  · exact _h 90
  · exact point16_1_18
  · exact point16_1_19

set_option maxHeartbeats 1600000 in
private theorem point17_0_1 : stepCheck 0 2441 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_2 : stepCheck 0 2442 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_5 : stepCheck 0 2445 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_6 : stepCheck 0 2446 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_8 : stepCheck 0 2448 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_11 : stepCheck 0 2451 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_12 : stepCheck 0 2452 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_13 : stepCheck 0 2453 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_14 : stepCheck 0 2454 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_16 : stepCheck 0 2456 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_18 : stepCheck 0 2458 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_19 : stepCheck 0 2459 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_0 : stepCheck 1 2440 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_2 : stepCheck 1 2442 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_3 : stepCheck 1 2443 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_5 : stepCheck 1 2445 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_6 : stepCheck 1 2446 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_8 : stepCheck 1 2448 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_10 : stepCheck 1 2450 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_11 : stepCheck 1 2451 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_12 : stepCheck 1 2452 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_13 : stepCheck 1 2453 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_14 : stepCheck 1 2454 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_15 : stepCheck 1 2455 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_17 : stepCheck 1 2457 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_18 : stepCheck 1 2458 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_19 : stepCheck 1 2459 := by
  left
  decide +kernel

private theorem checked17 (_h : ∀ k : Fin 271, residualCheck k) : stepBatch 122 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact _h 91
  · exact point17_0_1
  · exact point17_0_2
  · exact _h 92
  · exact _h 93
  · exact point17_0_5
  · exact point17_0_6
  · exact _h 94
  · exact point17_0_8
  · exact _h 95
  · exact _h 96
  · exact point17_0_11
  · exact point17_0_12
  · exact point17_0_13
  · exact point17_0_14
  · exact _h 97
  · exact point17_0_16
  · exact _h 98
  · exact point17_0_18
  · exact point17_0_19
  · exact point17_1_0
  · exact _h 99
  · exact point17_1_2
  · exact point17_1_3
  · exact _h 100
  · exact point17_1_5
  · exact point17_1_6
  · exact _h 101
  · exact point17_1_8
  · exact _h 102
  · exact point17_1_10
  · exact point17_1_11
  · exact point17_1_12
  · exact point17_1_13
  · exact point17_1_14
  · exact point17_1_15
  · exact _h 103
  · exact point17_1_17
  · exact point17_1_18
  · exact point17_1_19

set_option maxHeartbeats 1600000 in
private theorem point18_0_0 : stepCheck 0 2580 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_1 : stepCheck 0 2581 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_2 : stepCheck 0 2582 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_4 : stepCheck 0 2584 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_5 : stepCheck 0 2585 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_7 : stepCheck 0 2587 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_9 : stepCheck 0 2589 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_10 : stepCheck 0 2590 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_12 : stepCheck 0 2592 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_13 : stepCheck 0 2593 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_15 : stepCheck 0 2595 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_16 : stepCheck 0 2596 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_18 : stepCheck 0 2598 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_19 : stepCheck 0 2599 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_0 : stepCheck 1 2580 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_2 : stepCheck 1 2582 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_3 : stepCheck 1 2583 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_6 : stepCheck 1 2586 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_7 : stepCheck 1 2587 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_8 : stepCheck 1 2588 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_9 : stepCheck 1 2589 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_10 : stepCheck 1 2590 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_11 : stepCheck 1 2591 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_13 : stepCheck 1 2593 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_15 : stepCheck 1 2595 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_17 : stepCheck 1 2597 := by
  left
  decide +kernel

private theorem checked18 (_h : ∀ k : Fin 271, residualCheck k) : stepBatch 129 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point18_0_0
  · exact point18_0_1
  · exact point18_0_2
  · exact _h 104
  · exact point18_0_4
  · exact point18_0_5
  · exact _h 105
  · exact point18_0_7
  · exact _h 106
  · exact point18_0_9
  · exact point18_0_10
  · exact _h 107
  · exact point18_0_12
  · exact point18_0_13
  · exact _h 108
  · exact point18_0_15
  · exact point18_0_16
  · exact _h 109
  · exact point18_0_18
  · exact point18_0_19
  · exact point18_1_0
  · exact _h 110
  · exact point18_1_2
  · exact point18_1_3
  · exact _h 111
  · exact _h 112
  · exact point18_1_6
  · exact point18_1_7
  · exact point18_1_8
  · exact point18_1_9
  · exact point18_1_10
  · exact point18_1_11
  · exact _h 113
  · exact point18_1_13
  · exact _h 114
  · exact point18_1_15
  · exact _h 115
  · exact point18_1_17
  · exact _h 116
  · exact _h 117

set_option maxHeartbeats 1600000 in
private theorem point19_0_0 : stepCheck 0 2720 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_1 : stepCheck 0 2721 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_2 : stepCheck 0 2722 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_3 : stepCheck 0 2723 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_4 : stepCheck 0 2724 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_5 : stepCheck 0 2725 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_7 : stepCheck 0 2727 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_9 : stepCheck 0 2729 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_10 : stepCheck 0 2730 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_16 : stepCheck 0 2736 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_17 : stepCheck 0 2737 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_18 : stepCheck 0 2738 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_1 : stepCheck 1 2721 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_2 : stepCheck 1 2722 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_3 : stepCheck 1 2723 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_4 : stepCheck 1 2724 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_5 : stepCheck 1 2725 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_7 : stepCheck 1 2727 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_8 : stepCheck 1 2728 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_10 : stepCheck 1 2730 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_11 : stepCheck 1 2731 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_12 : stepCheck 1 2732 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_14 : stepCheck 1 2734 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_15 : stepCheck 1 2735 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_17 : stepCheck 1 2737 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_18 : stepCheck 1 2738 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_19 : stepCheck 1 2739 := by
  left
  decide +kernel

private theorem checked19 (_h : ∀ k : Fin 271, residualCheck k) : stepBatch 136 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point19_0_0
  · exact point19_0_1
  · exact point19_0_2
  · exact point19_0_3
  · exact point19_0_4
  · exact point19_0_5
  · exact _h 118
  · exact point19_0_7
  · exact _h 119
  · exact point19_0_9
  · exact point19_0_10
  · exact _h 120
  · exact _h 121
  · exact _h 122
  · exact _h 123
  · exact _h 124
  · exact point19_0_16
  · exact point19_0_17
  · exact point19_0_18
  · exact _h 125
  · exact _h 126
  · exact point19_1_1
  · exact point19_1_2
  · exact point19_1_3
  · exact point19_1_4
  · exact point19_1_5
  · exact _h 127
  · exact point19_1_7
  · exact point19_1_8
  · exact _h 128
  · exact point19_1_10
  · exact point19_1_11
  · exact point19_1_12
  · exact _h 129
  · exact point19_1_14
  · exact point19_1_15
  · exact _h 130
  · exact point19_1_17
  · exact point19_1_18
  · exact point19_1_19

set_option maxHeartbeats 1600000 in
private theorem point20_0_1 : stepCheck 0 2861 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_4 : stepCheck 0 2864 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_6 : stepCheck 0 2866 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_7 : stepCheck 0 2867 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_8 : stepCheck 0 2868 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_10 : stepCheck 0 2870 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_11 : stepCheck 0 2871 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_12 : stepCheck 0 2872 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_13 : stepCheck 0 2873 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_14 : stepCheck 0 2874 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_16 : stepCheck 0 2876 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_17 : stepCheck 0 2877 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_18 : stepCheck 0 2878 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_19 : stepCheck 0 2879 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_0 : stepCheck 1 2860 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_1 : stepCheck 1 2861 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_3 : stepCheck 1 2863 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_6 : stepCheck 1 2866 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_7 : stepCheck 1 2867 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_9 : stepCheck 1 2869 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_10 : stepCheck 1 2870 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_11 : stepCheck 1 2871 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_12 : stepCheck 1 2872 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_13 : stepCheck 1 2873 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_15 : stepCheck 1 2875 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_16 : stepCheck 1 2876 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_17 : stepCheck 1 2877 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_18 : stepCheck 1 2878 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_19 : stepCheck 1 2879 := by
  left
  decide +kernel

private theorem checked20 (_h : ∀ k : Fin 271, residualCheck k) : stepBatch 143 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact _h 131
  · exact point20_0_1
  · exact _h 132
  · exact _h 133
  · exact point20_0_4
  · exact _h 134
  · exact point20_0_6
  · exact point20_0_7
  · exact point20_0_8
  · exact _h 135
  · exact point20_0_10
  · exact point20_0_11
  · exact point20_0_12
  · exact point20_0_13
  · exact point20_0_14
  · exact _h 136
  · exact point20_0_16
  · exact point20_0_17
  · exact point20_0_18
  · exact point20_0_19
  · exact point20_1_0
  · exact point20_1_1
  · exact _h 137
  · exact point20_1_3
  · exact _h 138
  · exact _h 139
  · exact point20_1_6
  · exact point20_1_7
  · exact _h 140
  · exact point20_1_9
  · exact point20_1_10
  · exact point20_1_11
  · exact point20_1_12
  · exact point20_1_13
  · exact _h 141
  · exact point20_1_15
  · exact point20_1_16
  · exact point20_1_17
  · exact point20_1_18
  · exact point20_1_19

set_option maxHeartbeats 1600000 in
private theorem point21_0_0 : stepCheck 0 3000 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_1 : stepCheck 0 3001 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_4 : stepCheck 0 3004 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_5 : stepCheck 0 3005 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_7 : stepCheck 0 3007 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_8 : stepCheck 0 3008 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_9 : stepCheck 0 3009 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_10 : stepCheck 0 3010 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_11 : stepCheck 0 3011 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_12 : stepCheck 0 3012 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_13 : stepCheck 0 3013 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_15 : stepCheck 0 3015 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_17 : stepCheck 0 3017 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_19 : stepCheck 0 3019 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_2 : stepCheck 1 3002 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_4 : stepCheck 1 3004 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_6 : stepCheck 1 3006 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_8 : stepCheck 1 3008 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_10 : stepCheck 1 3010 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_11 : stepCheck 1 3011 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_12 : stepCheck 1 3012 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_13 : stepCheck 1 3013 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_14 : stepCheck 1 3014 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_16 : stepCheck 1 3016 := by
  left
  decide +kernel

private theorem checked21 (_h : ∀ k : Fin 271, residualCheck k) : stepBatch 150 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point21_0_0
  · exact point21_0_1
  · exact _h 142
  · exact _h 143
  · exact point21_0_4
  · exact point21_0_5
  · exact _h 144
  · exact point21_0_7
  · exact point21_0_8
  · exact point21_0_9
  · exact point21_0_10
  · exact point21_0_11
  · exact point21_0_12
  · exact point21_0_13
  · exact _h 145
  · exact point21_0_15
  · exact _h 146
  · exact point21_0_17
  · exact _h 147
  · exact point21_0_19
  · exact _h 148
  · exact _h 149
  · exact point21_1_2
  · exact _h 150
  · exact point21_1_4
  · exact _h 151
  · exact point21_1_6
  · exact _h 152
  · exact point21_1_8
  · exact _h 153
  · exact point21_1_10
  · exact point21_1_11
  · exact point21_1_12
  · exact point21_1_13
  · exact point21_1_14
  · exact _h 154
  · exact point21_1_16
  · exact _h 155
  · exact _h 156
  · exact _h 157

set_option maxHeartbeats 1600000 in
private theorem point22_0_0 : stepCheck 0 3140 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_1 : stepCheck 0 3141 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_2 : stepCheck 0 3142 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_3 : stepCheck 0 3143 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_4 : stepCheck 0 3144 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_5 : stepCheck 0 3145 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_6 : stepCheck 0 3146 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_7 : stepCheck 0 3147 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_8 : stepCheck 0 3148 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_10 : stepCheck 0 3150 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_11 : stepCheck 0 3151 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_12 : stepCheck 0 3152 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_15 : stepCheck 0 3155 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_18 : stepCheck 0 3158 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_19 : stepCheck 0 3159 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_1 : stepCheck 1 3141 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_6 : stepCheck 1 3146 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_7 : stepCheck 1 3147 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_9 : stepCheck 1 3149 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_12 : stepCheck 1 3152 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_13 : stepCheck 1 3153 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_14 : stepCheck 1 3154 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_15 : stepCheck 1 3155 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_16 : stepCheck 1 3156 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_17 : stepCheck 1 3157 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_18 : stepCheck 1 3158 := by
  left
  decide +kernel

private theorem checked22 (_h : ∀ k : Fin 271, residualCheck k) : stepBatch 157 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point22_0_0
  · exact point22_0_1
  · exact point22_0_2
  · exact point22_0_3
  · exact point22_0_4
  · exact point22_0_5
  · exact point22_0_6
  · exact point22_0_7
  · exact point22_0_8
  · exact _h 158
  · exact point22_0_10
  · exact point22_0_11
  · exact point22_0_12
  · exact _h 159
  · exact _h 160
  · exact point22_0_15
  · exact _h 161
  · exact _h 162
  · exact point22_0_18
  · exact point22_0_19
  · exact _h 163
  · exact point22_1_1
  · exact _h 164
  · exact _h 165
  · exact _h 166
  · exact _h 167
  · exact point22_1_6
  · exact point22_1_7
  · exact _h 168
  · exact point22_1_9
  · exact _h 169
  · exact _h 170
  · exact point22_1_12
  · exact point22_1_13
  · exact point22_1_14
  · exact point22_1_15
  · exact point22_1_16
  · exact point22_1_17
  · exact point22_1_18
  · exact _h 171

set_option maxHeartbeats 1600000 in
private theorem point23_0_1 : stepCheck 0 3281 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_2 : stepCheck 0 3282 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_4 : stepCheck 0 3284 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_6 : stepCheck 0 3286 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_7 : stepCheck 0 3287 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_9 : stepCheck 0 3289 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_11 : stepCheck 0 3291 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_12 : stepCheck 0 3292 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_13 : stepCheck 0 3293 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_15 : stepCheck 0 3295 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_18 : stepCheck 0 3298 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_0 : stepCheck 1 3280 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_2 : stepCheck 1 3282 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_3 : stepCheck 1 3283 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_5 : stepCheck 1 3285 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_6 : stepCheck 1 3286 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_7 : stepCheck 1 3287 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_8 : stepCheck 1 3288 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_10 : stepCheck 1 3290 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_14 : stepCheck 1 3294 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_15 : stepCheck 1 3295 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_16 : stepCheck 1 3296 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_18 : stepCheck 1 3298 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_19 : stepCheck 1 3299 := by
  left
  decide +kernel

private theorem checked23 (_h : ∀ k : Fin 271, residualCheck k) : stepBatch 164 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact _h 172
  · exact point23_0_1
  · exact point23_0_2
  · exact _h 173
  · exact point23_0_4
  · exact _h 174
  · exact point23_0_6
  · exact point23_0_7
  · exact _h 175
  · exact point23_0_9
  · exact _h 176
  · exact point23_0_11
  · exact point23_0_12
  · exact point23_0_13
  · exact _h 177
  · exact point23_0_15
  · exact _h 178
  · exact _h 179
  · exact point23_0_18
  · exact _h 180
  · exact point23_1_0
  · exact _h 181
  · exact point23_1_2
  · exact point23_1_3
  · exact _h 182
  · exact point23_1_5
  · exact point23_1_6
  · exact point23_1_7
  · exact point23_1_8
  · exact _h 183
  · exact point23_1_10
  · exact _h 184
  · exact _h 185
  · exact _h 186
  · exact point23_1_14
  · exact point23_1_15
  · exact point23_1_16
  · exact _h 187
  · exact point23_1_18
  · exact point23_1_19

set_option maxHeartbeats 1600000 in
private theorem point24_0_0 : stepCheck 0 3420 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_1 : stepCheck 0 3421 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_2 : stepCheck 0 3422 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_3 : stepCheck 0 3423 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_5 : stepCheck 0 3425 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_7 : stepCheck 0 3427 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_8 : stepCheck 0 3428 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_11 : stepCheck 0 3431 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_12 : stepCheck 0 3432 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_13 : stepCheck 0 3433 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_14 : stepCheck 0 3434 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_15 : stepCheck 0 3435 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_16 : stepCheck 0 3436 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_17 : stepCheck 0 3437 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_19 : stepCheck 0 3439 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_0 : stepCheck 1 3420 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_1 : stepCheck 1 3421 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_2 : stepCheck 1 3422 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_7 : stepCheck 1 3427 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_8 : stepCheck 1 3428 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_9 : stepCheck 1 3429 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_11 : stepCheck 1 3431 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_15 : stepCheck 1 3435 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_16 : stepCheck 1 3436 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_17 : stepCheck 1 3437 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_19 : stepCheck 1 3439 := by
  left
  decide +kernel

private theorem checked24 (_h : ∀ k : Fin 271, residualCheck k) : stepBatch 171 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point24_0_0
  · exact point24_0_1
  · exact point24_0_2
  · exact point24_0_3
  · exact _h 188
  · exact point24_0_5
  · exact _h 189
  · exact point24_0_7
  · exact point24_0_8
  · exact _h 190
  · exact _h 191
  · exact point24_0_11
  · exact point24_0_12
  · exact point24_0_13
  · exact point24_0_14
  · exact point24_0_15
  · exact point24_0_16
  · exact point24_0_17
  · exact _h 192
  · exact point24_0_19
  · exact point24_1_0
  · exact point24_1_1
  · exact point24_1_2
  · exact _h 193
  · exact _h 194
  · exact _h 195
  · exact _h 196
  · exact point24_1_7
  · exact point24_1_8
  · exact point24_1_9
  · exact _h 197
  · exact point24_1_11
  · exact _h 198
  · exact _h 199
  · exact _h 200
  · exact point24_1_15
  · exact point24_1_16
  · exact point24_1_17
  · exact _h 201
  · exact point24_1_19

set_option maxHeartbeats 1600000 in
private theorem point25_0_0 : stepCheck 0 3560 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_1 : stepCheck 0 3561 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_2 : stepCheck 0 3562 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_3 : stepCheck 0 3563 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_4 : stepCheck 0 3564 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_5 : stepCheck 0 3565 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_6 : stepCheck 0 3566 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_7 : stepCheck 0 3567 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_8 : stepCheck 0 3568 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_9 : stepCheck 0 3569 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_13 : stepCheck 0 3573 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_14 : stepCheck 0 3574 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_16 : stepCheck 0 3576 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_18 : stepCheck 0 3578 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_19 : stepCheck 0 3579 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_1 : stepCheck 1 3561 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_2 : stepCheck 1 3562 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_4 : stepCheck 1 3564 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_5 : stepCheck 1 3565 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_6 : stepCheck 1 3566 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_7 : stepCheck 1 3567 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_8 : stepCheck 1 3568 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_9 : stepCheck 1 3569 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_10 : stepCheck 1 3570 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_12 : stepCheck 1 3572 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_13 : stepCheck 1 3573 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_15 : stepCheck 1 3575 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_17 : stepCheck 1 3577 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_18 : stepCheck 1 3578 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_19 : stepCheck 1 3579 := by
  left
  decide +kernel

private theorem checked25 (_h : ∀ k : Fin 271, residualCheck k) : stepBatch 178 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point25_0_0
  · exact point25_0_1
  · exact point25_0_2
  · exact point25_0_3
  · exact point25_0_4
  · exact point25_0_5
  · exact point25_0_6
  · exact point25_0_7
  · exact point25_0_8
  · exact point25_0_9
  · exact _h 202
  · exact _h 203
  · exact _h 204
  · exact point25_0_13
  · exact point25_0_14
  · exact _h 205
  · exact point25_0_16
  · exact _h 206
  · exact point25_0_18
  · exact point25_0_19
  · exact _h 207
  · exact point25_1_1
  · exact point25_1_2
  · exact _h 208
  · exact point25_1_4
  · exact point25_1_5
  · exact point25_1_6
  · exact point25_1_7
  · exact point25_1_8
  · exact point25_1_9
  · exact point25_1_10
  · exact _h 209
  · exact point25_1_12
  · exact point25_1_13
  · exact _h 210
  · exact point25_1_15
  · exact _h 211
  · exact point25_1_17
  · exact point25_1_18
  · exact point25_1_19

set_option maxHeartbeats 1600000 in
private theorem point26_0_2 : stepCheck 0 3702 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_3 : stepCheck 0 3703 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_4 : stepCheck 0 3704 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_5 : stepCheck 0 3705 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_6 : stepCheck 0 3706 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_7 : stepCheck 0 3707 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_8 : stepCheck 0 3708 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_11 : stepCheck 0 3711 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_12 : stepCheck 0 3712 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_13 : stepCheck 0 3713 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_15 : stepCheck 0 3715 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_16 : stepCheck 0 3716 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_18 : stepCheck 0 3718 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_0 : stepCheck 1 3700 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_1 : stepCheck 1 3701 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_2 : stepCheck 1 3702 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_4 : stepCheck 1 3704 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_6 : stepCheck 1 3706 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_7 : stepCheck 1 3707 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_8 : stepCheck 1 3708 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_9 : stepCheck 1 3709 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_10 : stepCheck 1 3710 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_12 : stepCheck 1 3712 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_13 : stepCheck 1 3713 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_14 : stepCheck 1 3714 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_15 : stepCheck 1 3715 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_16 : stepCheck 1 3716 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_19 : stepCheck 1 3719 := by
  left
  decide +kernel

private theorem checked26 (_h : ∀ k : Fin 271, residualCheck k) : stepBatch 185 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact _h 212
  · exact _h 213
  · exact point26_0_2
  · exact point26_0_3
  · exact point26_0_4
  · exact point26_0_5
  · exact point26_0_6
  · exact point26_0_7
  · exact point26_0_8
  · exact _h 214
  · exact _h 215
  · exact point26_0_11
  · exact point26_0_12
  · exact point26_0_13
  · exact _h 216
  · exact point26_0_15
  · exact point26_0_16
  · exact _h 217
  · exact point26_0_18
  · exact _h 218
  · exact point26_1_0
  · exact point26_1_1
  · exact point26_1_2
  · exact _h 219
  · exact point26_1_4
  · exact _h 220
  · exact point26_1_6
  · exact point26_1_7
  · exact point26_1_8
  · exact point26_1_9
  · exact point26_1_10
  · exact _h 221
  · exact point26_1_12
  · exact point26_1_13
  · exact point26_1_14
  · exact point26_1_15
  · exact point26_1_16
  · exact _h 222
  · exact _h 223
  · exact point26_1_19

set_option maxHeartbeats 1600000 in
private theorem point27_0_3 : stepCheck 0 3843 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_5 : stepCheck 0 3845 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_6 : stepCheck 0 3846 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_7 : stepCheck 0 3847 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_8 : stepCheck 0 3848 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_10 : stepCheck 0 3850 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_14 : stepCheck 0 3854 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_15 : stepCheck 0 3855 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_16 : stepCheck 0 3856 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_19 : stepCheck 0 3859 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_0 : stepCheck 1 3840 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_1 : stepCheck 1 3841 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_2 : stepCheck 1 3842 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_4 : stepCheck 1 3844 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_5 : stepCheck 1 3845 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_10 : stepCheck 1 3850 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_12 : stepCheck 1 3852 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_15 : stepCheck 1 3855 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_16 : stepCheck 1 3856 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_17 : stepCheck 1 3857 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_18 : stepCheck 1 3858 := by
  left
  decide +kernel

private theorem checked27 (_h : ∀ k : Fin 271, residualCheck k) : stepBatch 192 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact _h 224
  · exact _h 225
  · exact _h 226
  · exact point27_0_3
  · exact _h 227
  · exact point27_0_5
  · exact point27_0_6
  · exact point27_0_7
  · exact point27_0_8
  · exact _h 228
  · exact point27_0_10
  · exact _h 229
  · exact _h 230
  · exact _h 231
  · exact point27_0_14
  · exact point27_0_15
  · exact point27_0_16
  · exact _h 232
  · exact _h 233
  · exact point27_0_19
  · exact point27_1_0
  · exact point27_1_1
  · exact point27_1_2
  · exact _h 234
  · exact point27_1_4
  · exact point27_1_5
  · exact _h 235
  · exact _h 236
  · exact _h 237
  · exact _h 238
  · exact point27_1_10
  · exact _h 239
  · exact point27_1_12
  · exact _h 240
  · exact _h 241
  · exact point27_1_15
  · exact point27_1_16
  · exact point27_1_17
  · exact point27_1_18
  · exact _h 242

set_option maxHeartbeats 1600000 in
private theorem point28_0_1 : stepCheck 0 3981 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_7 : stepCheck 0 3987 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_2 : stepCheck 1 3982 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_3 : stepCheck 1 3983 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_4 : stepCheck 1 3984 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_5 : stepCheck 1 3985 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_6 : stepCheck 1 3986 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_8 : stepCheck 1 3988 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_9 : stepCheck 1 3989 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_11 : stepCheck 1 3991 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_13 : stepCheck 1 3993 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_16 : stepCheck 1 3996 := by
  left
  decide +kernel

private theorem checked28 (_h : ∀ k : Fin 271, residualCheck k) : stepBatch 199 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact _h 243
  · exact point28_0_1
  · exact _h 244
  · exact _h 245
  · exact _h 246
  · exact _h 247
  · exact _h 248
  · exact point28_0_7
  · exact _h 249
  · exact _h 250
  · exact _h 251
  · exact _h 252
  · exact _h 253
  · exact _h 254
  · exact _h 255
  · exact _h 256
  · exact _h 257
  · exact _h 258
  · exact _h 259
  · exact _h 260
  · exact _h 261
  · exact _h 262
  · exact point28_1_2
  · exact point28_1_3
  · exact point28_1_4
  · exact point28_1_5
  · exact point28_1_6
  · exact _h 263
  · exact point28_1_8
  · exact point28_1_9
  · exact _h 264
  · exact point28_1_11
  · exact _h 265
  · exact point28_1_13
  · exact _h 266
  · exact _h 267
  · exact point28_1_16
  · exact _h 268
  · exact _h 269
  · exact _h 270

/-- The algebraic transitions leave precisely the explicit residual checks. -/
public theorem part3_of_residual (h : ∀ k : Fin 271, residualCheck k) (b : Fin 29) :
    stepBatch ⟨7 * b.val + 3, by omega⟩ := by
  fin_cases b
  · exact checked0 h
  · exact checked1 h
  · exact checked2 h
  · exact checked3 h
  · exact checked4 h
  · exact checked5 h
  · exact checked6 h
  · exact checked7 h
  · exact checked8 h
  · exact checked9 h
  · exact checked10 h
  · exact checked11 h
  · exact checked12 h
  · exact checked13 h
  · exact checked14 h
  · exact checked15 h
  · exact checked16 h
  · exact checked17 h
  · exact checked18 h
  · exact checked19 h
  · exact checked20 h
  · exact checked21 h
  · exact checked22 h
  · exact checked23 h
  · exact checked24 h
  · exact checked25 h
  · exact checked26 h
  · exact checked27 h
  · exact checked28 h

/-- Four independent residual certificates complete part 3. -/
public theorem part3_of_batches (h : ∀ g : Fin 4, residualBatch g) (b : Fin 29) :
    stepBatch ⟨7 * b.val + 3, by omega⟩ :=
  part3_of_residual (all_of_batches h) b

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual
