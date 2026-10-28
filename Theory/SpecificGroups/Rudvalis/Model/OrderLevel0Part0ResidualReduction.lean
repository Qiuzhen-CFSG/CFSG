module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Reduction
import Mathlib.Tactic.FinCases

/-!
# Residual checks for Rudvalis level-0 transition part 0

Of the 1160 forward transitions in the 29 batches numbered 0 modulo 7,
901 follow by word reduction in the cyclic groups of orders 2 and 4.
This module proves these checks and reduces part 0 to the remaining 259
explicit transitions, grouped into four independent finite certificates.

The source witnesses are those of `OrderLevel0Data`, documented in
`OrderCertificate/GenerateChain.g`. The accompanying generator only selects
proof branches; the word reductions and final coverage are kernel-checked.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual
set_option maxRecDepth 30000
set_option Elab.async false

@[expose] public def target (k : Fin 259) : Fin 2 × Fin 4060 :=
  (if k.val < 129 then (if k.val < 64 then (if k.val < 32 then (if k.val < 16 then (if k.val < 8 then (if k.val < 4 then (if k.val < 2 then (if k.val < 1 then (1, 434) else (1, 438)) else (if k.val < 3 then (0, 562) else (0, 571))) else (if k.val < 6 then (if k.val < 5 then (1, 565) else (1, 570)) else (if k.val < 7 then (1, 578) else (0, 712)))) else (if k.val < 12 then (if k.val < 10 then (if k.val < 9 then (0, 713) else (0, 844)) else (if k.val < 11 then (0, 981) else (0, 987))) else (if k.val < 14 then (if k.val < 13 then (0, 989) else (0, 994)) else (if k.val < 15 then (1, 994) else (1, 999))))) else (if k.val < 24 then (if k.val < 20 then (if k.val < 18 then (if k.val < 17 then (0, 1129) else (0, 1131)) else (if k.val < 19 then (1, 1123) else (1, 1125))) else (if k.val < 22 then (if k.val < 21 then (1, 1129) else (1, 1134)) else (if k.val < 23 then (0, 1261) else (0, 1268)))) else (if k.val < 28 then (if k.val < 26 then (if k.val < 25 then (0, 1269) else (0, 1276)) else (if k.val < 27 then (1, 1262) else (1, 1268))) else (if k.val < 30 then (if k.val < 29 then (1, 1270) else (0, 1404)) else (if k.val < 31 then (0, 1405) else (0, 1408)))))) else (if k.val < 48 then (if k.val < 40 then (if k.val < 36 then (if k.val < 34 then (if k.val < 33 then (0, 1411) else (0, 1416)) else (if k.val < 35 then (0, 1417) else (1, 1405))) else (if k.val < 38 then (if k.val < 37 then (1, 1416) else (0, 1550)) else (if k.val < 39 then (1, 1540) else (1, 1547)))) else (if k.val < 44 then (if k.val < 42 then (if k.val < 41 then (1, 1550) else (1, 1552)) else (if k.val < 43 then (1, 1559) else (0, 1684))) else (if k.val < 46 then (if k.val < 45 then (0, 1688) else (0, 1691)) else (if k.val < 47 then (0, 1694) else (1, 1680))))) else (if k.val < 56 then (if k.val < 52 then (if k.val < 50 then (if k.val < 49 then (1, 1686) else (1, 1688)) else (if k.val < 51 then (1, 1690) else (1, 1692))) else (if k.val < 54 then (if k.val < 53 then (0, 1830) else (0, 1838)) else (if k.val < 55 then (1, 1837) else (1, 1839)))) else (if k.val < 60 then (if k.val < 58 then (if k.val < 57 then (0, 1962) else (0, 1964)) else (if k.val < 59 then (0, 1967) else (0, 1974))) else (if k.val < 62 then (if k.val < 61 then (0, 1977) else (1, 1969)) else (if k.val < 63 then (0, 2100) else (0, 2106))))))) else (if k.val < 96 then (if k.val < 80 then (if k.val < 72 then (if k.val < 68 then (if k.val < 66 then (if k.val < 65 then (0, 2114) else (1, 2103)) else (if k.val < 67 then (1, 2104) else (1, 2107))) else (if k.val < 70 then (if k.val < 69 then (1, 2108) else (1, 2111)) else (if k.val < 71 then (1, 2114) else (1, 2118)))) else (if k.val < 76 then (if k.val < 74 then (if k.val < 73 then (0, 2245) else (0, 2246)) else (if k.val < 75 then (0, 2248) else (0, 2253))) else (if k.val < 78 then (if k.val < 77 then (0, 2255) else (1, 2255)) else (if k.val < 79 then (1, 2257) else (0, 2380))))) else (if k.val < 88 then (if k.val < 84 then (if k.val < 82 then (if k.val < 81 then (0, 2381) else (0, 2385)) else (if k.val < 83 then (0, 2387) else (0, 2392))) else (if k.val < 86 then (if k.val < 85 then (0, 2398) else (0, 2399)) else (if k.val < 87 then (1, 2382) else (1, 2386)))) else (if k.val < 92 then (if k.val < 90 then (if k.val < 89 then (1, 2387) else (1, 2395)) else (if k.val < 91 then (1, 2396) else (1, 2397))) else (if k.val < 94 then (if k.val < 93 then (1, 2398) else (0, 2521)) else (if k.val < 95 then (0, 2522) else (0, 2527)))))) else (if k.val < 112 then (if k.val < 104 then (if k.val < 100 then (if k.val < 98 then (if k.val < 97 then (0, 2528) else (0, 2529)) else (if k.val < 99 then (0, 2535) else (1, 2520))) else (if k.val < 102 then (if k.val < 101 then (1, 2526) else (1, 2529)) else (if k.val < 103 then (1, 2531) else (0, 2662)))) else (if k.val < 108 then (if k.val < 106 then (if k.val < 105 then (0, 2663) else (0, 2667)) else (if k.val < 107 then (0, 2668) else (0, 2670))) else (if k.val < 110 then (if k.val < 109 then (0, 2672) else (0, 2675)) else (if k.val < 111 then (1, 2662) else (1, 2664))))) else (if k.val < 120 then (if k.val < 116 then (if k.val < 114 then (if k.val < 113 then (1, 2665) else (1, 2676)) else (if k.val < 115 then (1, 2678) else (0, 2804))) else (if k.val < 118 then (if k.val < 117 then (0, 2808) else (0, 2809)) else (if k.val < 119 then (0, 2812) else (0, 2816)))) else (if k.val < 124 then (if k.val < 122 then (if k.val < 121 then (0, 2819) else (1, 2802)) else (if k.val < 123 then (1, 2811) else (1, 2818))) else (if k.val < 126 then (if k.val < 125 then (0, 2942) else (0, 2943)) else (if k.val < 127 then (0, 2945) else (if k.val < 128 then (0, 2948) else (0, 2952))))))))) else (if k.val < 194 then (if k.val < 161 then (if k.val < 145 then (if k.val < 137 then (if k.val < 133 then (if k.val < 131 then (if k.val < 130 then (0, 2953) else (0, 2955)) else (if k.val < 132 then (0, 2957) else (1, 2940))) else (if k.val < 135 then (if k.val < 134 then (1, 2947) else (1, 2950)) else (if k.val < 136 then (1, 2951) else (1, 2952)))) else (if k.val < 141 then (if k.val < 139 then (if k.val < 138 then (1, 2954) else (1, 2956)) else (if k.val < 140 then (1, 2957) else (1, 2958))) else (if k.val < 143 then (if k.val < 142 then (0, 3080) else (0, 3082)) else (if k.val < 144 then (0, 3088) else (0, 3090))))) else (if k.val < 153 then (if k.val < 149 then (if k.val < 147 then (if k.val < 146 then (0, 3091) else (0, 3092)) else (if k.val < 148 then (0, 3095) else (0, 3097))) else (if k.val < 151 then (if k.val < 150 then (0, 3098) else (1, 3080)) else (if k.val < 152 then (1, 3083) else (1, 3086)))) else (if k.val < 157 then (if k.val < 155 then (if k.val < 154 then (1, 3093) else (1, 3096)) else (if k.val < 156 then (1, 3098) else (0, 3222))) else (if k.val < 159 then (if k.val < 158 then (0, 3226) else (0, 3229)) else (if k.val < 160 then (0, 3231) else (0, 3232)))))) else (if k.val < 177 then (if k.val < 169 then (if k.val < 165 then (if k.val < 163 then (if k.val < 162 then (0, 3235) else (1, 3221)) else (if k.val < 164 then (1, 3222) else (1, 3226))) else (if k.val < 167 then (if k.val < 166 then (1, 3228) else (1, 3229)) else (if k.val < 168 then (1, 3230) else (1, 3231)))) else (if k.val < 173 then (if k.val < 171 then (if k.val < 170 then (1, 3235) else (1, 3236)) else (if k.val < 172 then (1, 3239) else (0, 3361))) else (if k.val < 175 then (if k.val < 174 then (0, 3364) else (0, 3365)) else (if k.val < 176 then (0, 3368) else (0, 3369))))) else (if k.val < 185 then (if k.val < 181 then (if k.val < 179 then (if k.val < 178 then (0, 3371) else (0, 3373)) else (if k.val < 180 then (0, 3378) else (0, 3379))) else (if k.val < 183 then (if k.val < 182 then (1, 3360) else (1, 3364)) else (if k.val < 184 then (1, 3368) else (1, 3370)))) else (if k.val < 189 then (if k.val < 187 then (if k.val < 186 then (1, 3371) else (1, 3372)) else (if k.val < 188 then (1, 3376) else (1, 3378))) else (if k.val < 191 then (if k.val < 190 then (0, 3505) else (0, 3506)) else (if k.val < 192 then (0, 3507) else (if k.val < 193 then (0, 3508) else (0, 3510)))))))) else (if k.val < 226 then (if k.val < 210 then (if k.val < 202 then (if k.val < 198 then (if k.val < 196 then (if k.val < 195 then (0, 3511) else (0, 3516)) else (if k.val < 197 then (1, 3502) else (1, 3508))) else (if k.val < 200 then (if k.val < 199 then (1, 3513) else (1, 3514)) else (if k.val < 201 then (1, 3515) else (1, 3517)))) else (if k.val < 206 then (if k.val < 204 then (if k.val < 203 then (1, 3519) else (0, 3644)) else (if k.val < 205 then (0, 3645) else (0, 3647))) else (if k.val < 208 then (if k.val < 207 then (0, 3648) else (0, 3650)) else (if k.val < 209 then (0, 3651) else (0, 3652))))) else (if k.val < 218 then (if k.val < 214 then (if k.val < 212 then (if k.val < 211 then (0, 3657) else (0, 3658)) else (if k.val < 213 then (1, 3643) else (1, 3645))) else (if k.val < 216 then (if k.val < 215 then (1, 3646) else (1, 3649)) else (if k.val < 217 then (1, 3657) else (0, 3780)))) else (if k.val < 222 then (if k.val < 220 then (if k.val < 219 then (0, 3781) else (0, 3782)) else (if k.val < 221 then (0, 3783) else (0, 3784))) else (if k.val < 224 then (if k.val < 223 then (0, 3785) else (0, 3788)) else (if k.val < 225 then (0, 3789) else (0, 3792)))))) else (if k.val < 242 then (if k.val < 234 then (if k.val < 230 then (if k.val < 228 then (if k.val < 227 then (0, 3794) else (0, 3795)) else (if k.val < 229 then (0, 3797) else (0, 3799))) else (if k.val < 232 then (if k.val < 231 then (1, 3781) else (1, 3784)) else (if k.val < 233 then (1, 3788) else (1, 3791)))) else (if k.val < 238 then (if k.val < 236 then (if k.val < 235 then (1, 3792) else (1, 3793)) else (if k.val < 237 then (1, 3797) else (1, 3798))) else (if k.val < 240 then (if k.val < 239 then (1, 3799) else (0, 3921)) else (if k.val < 241 then (0, 3922) else (0, 3923))))) else (if k.val < 250 then (if k.val < 246 then (if k.val < 244 then (if k.val < 243 then (0, 3924) else (0, 3930)) else (if k.val < 245 then (0, 3931) else (0, 3933))) else (if k.val < 248 then (if k.val < 247 then (0, 3935) else (0, 3939)) else (if k.val < 249 then (1, 3920) else (1, 3923)))) else (if k.val < 254 then (if k.val < 252 then (if k.val < 251 then (1, 3925) else (1, 3926)) else (if k.val < 253 then (1, 3927) else (1, 3928))) else (if k.val < 256 then (if k.val < 255 then (1, 3931) else (1, 3934)) else (if k.val < 257 then (1, 3936) else (if k.val < 258 then (1, 3937) else (1, 3938))))))))))

@[expose] public def residualCheck (k : Fin 259) : Prop :=
  stepCheck (target k).1 (target k).2

/-- Groups 0, 1, 2 contain 65 transitions; group 3 contains 64. -/
@[expose] public def residualBatch (g : Fin 4) : Prop :=
  ∀ (s : Fin 65) (h : 65 * g.val + s.val < 259),
    residualCheck ⟨65 * g.val + s.val, h⟩

public theorem all_of_batches (h : ∀ g : Fin 4, residualBatch g) :
    ∀ k : Fin 259, residualCheck k := by
  intro k
  let g : Fin 4 := ⟨k.val / 65, by omega⟩
  let s : Fin 65 := ⟨k.val % 65, by omega⟩
  have hlt : 65 * g.val + s.val < 259 := by dsimp [g, s]; omega
  have hk : (⟨65 * g.val + s.val, hlt⟩ : Fin 259) = k := by
    apply Fin.ext
    dsimp [g, s]
    omega
  simpa only [hk] using h g s hlt

set_option maxHeartbeats 1600000 in
private theorem point0_0_0 : stepCheck 0 0 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_1 : stepCheck 0 1 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_2 : stepCheck 0 2 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_3 : stepCheck 0 3 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_4 : stepCheck 0 4 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_5 : stepCheck 0 5 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_6 : stepCheck 0 6 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_7 : stepCheck 0 7 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_8 : stepCheck 0 8 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_9 : stepCheck 0 9 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_10 : stepCheck 0 10 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_11 : stepCheck 0 11 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_12 : stepCheck 0 12 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_13 : stepCheck 0 13 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_14 : stepCheck 0 14 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_15 : stepCheck 0 15 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_16 : stepCheck 0 16 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_17 : stepCheck 0 17 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_18 : stepCheck 0 18 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_19 : stepCheck 0 19 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_0 : stepCheck 1 0 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_1 : stepCheck 1 1 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_2 : stepCheck 1 2 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_3 : stepCheck 1 3 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_4 : stepCheck 1 4 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_5 : stepCheck 1 5 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_6 : stepCheck 1 6 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_7 : stepCheck 1 7 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_8 : stepCheck 1 8 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_9 : stepCheck 1 9 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_10 : stepCheck 1 10 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_11 : stepCheck 1 11 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_12 : stepCheck 1 12 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_13 : stepCheck 1 13 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_14 : stepCheck 1 14 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_15 : stepCheck 1 15 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_16 : stepCheck 1 16 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_17 : stepCheck 1 17 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_18 : stepCheck 1 18 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_19 : stepCheck 1 19 := by
  left
  decide +kernel

private theorem checked0 (_h : ∀ k : Fin 259, residualCheck k) : stepBatch 0 := by
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
private theorem point1_0_0 : stepCheck 0 140 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_1 : stepCheck 0 141 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_2 : stepCheck 0 142 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_3 : stepCheck 0 143 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_4 : stepCheck 0 144 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_5 : stepCheck 0 145 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_6 : stepCheck 0 146 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_7 : stepCheck 0 147 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_8 : stepCheck 0 148 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_9 : stepCheck 0 149 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_10 : stepCheck 0 150 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_11 : stepCheck 0 151 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_12 : stepCheck 0 152 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_13 : stepCheck 0 153 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_14 : stepCheck 0 154 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_15 : stepCheck 0 155 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_16 : stepCheck 0 156 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_17 : stepCheck 0 157 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_18 : stepCheck 0 158 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_19 : stepCheck 0 159 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_0 : stepCheck 1 140 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_1 : stepCheck 1 141 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_2 : stepCheck 1 142 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_3 : stepCheck 1 143 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_4 : stepCheck 1 144 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_5 : stepCheck 1 145 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_6 : stepCheck 1 146 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_7 : stepCheck 1 147 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_8 : stepCheck 1 148 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_9 : stepCheck 1 149 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_10 : stepCheck 1 150 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_11 : stepCheck 1 151 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_12 : stepCheck 1 152 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_13 : stepCheck 1 153 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_14 : stepCheck 1 154 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_15 : stepCheck 1 155 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_16 : stepCheck 1 156 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_17 : stepCheck 1 157 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_18 : stepCheck 1 158 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_19 : stepCheck 1 159 := by
  left
  decide +kernel

private theorem checked1 (_h : ∀ k : Fin 259, residualCheck k) : stepBatch 7 := by
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
private theorem point2_0_0 : stepCheck 0 280 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_1 : stepCheck 0 281 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_2 : stepCheck 0 282 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_3 : stepCheck 0 283 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_4 : stepCheck 0 284 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_5 : stepCheck 0 285 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_6 : stepCheck 0 286 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_7 : stepCheck 0 287 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_8 : stepCheck 0 288 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_9 : stepCheck 0 289 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_10 : stepCheck 0 290 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_11 : stepCheck 0 291 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_12 : stepCheck 0 292 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_13 : stepCheck 0 293 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_14 : stepCheck 0 294 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_15 : stepCheck 0 295 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_16 : stepCheck 0 296 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_17 : stepCheck 0 297 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_18 : stepCheck 0 298 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_19 : stepCheck 0 299 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_0 : stepCheck 1 280 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_1 : stepCheck 1 281 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_2 : stepCheck 1 282 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_3 : stepCheck 1 283 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_4 : stepCheck 1 284 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_5 : stepCheck 1 285 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_6 : stepCheck 1 286 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_7 : stepCheck 1 287 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_8 : stepCheck 1 288 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_9 : stepCheck 1 289 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_10 : stepCheck 1 290 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_11 : stepCheck 1 291 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_12 : stepCheck 1 292 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_13 : stepCheck 1 293 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_14 : stepCheck 1 294 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_15 : stepCheck 1 295 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_16 : stepCheck 1 296 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_17 : stepCheck 1 297 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_18 : stepCheck 1 298 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_19 : stepCheck 1 299 := by
  left
  decide +kernel

private theorem checked2 (_h : ∀ k : Fin 259, residualCheck k) : stepBatch 14 := by
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
  · exact point2_0_13
  · exact point2_0_14
  · exact point2_0_15
  · exact point2_0_16
  · exact point2_0_17
  · exact point2_0_18
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
private theorem point3_0_0 : stepCheck 0 420 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_1 : stepCheck 0 421 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_2 : stepCheck 0 422 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_3 : stepCheck 0 423 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_4 : stepCheck 0 424 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_5 : stepCheck 0 425 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_6 : stepCheck 0 426 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_7 : stepCheck 0 427 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_8 : stepCheck 0 428 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_9 : stepCheck 0 429 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_10 : stepCheck 0 430 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_11 : stepCheck 0 431 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_12 : stepCheck 0 432 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_13 : stepCheck 0 433 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_14 : stepCheck 0 434 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_15 : stepCheck 0 435 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_16 : stepCheck 0 436 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_17 : stepCheck 0 437 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_18 : stepCheck 0 438 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_19 : stepCheck 0 439 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_0 : stepCheck 1 420 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_1 : stepCheck 1 421 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_2 : stepCheck 1 422 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_3 : stepCheck 1 423 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_4 : stepCheck 1 424 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_5 : stepCheck 1 425 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_6 : stepCheck 1 426 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_7 : stepCheck 1 427 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_8 : stepCheck 1 428 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_9 : stepCheck 1 429 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_10 : stepCheck 1 430 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_11 : stepCheck 1 431 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_12 : stepCheck 1 432 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_13 : stepCheck 1 433 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_15 : stepCheck 1 435 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_16 : stepCheck 1 436 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_17 : stepCheck 1 437 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_19 : stepCheck 1 439 := by
  left
  decide +kernel

private theorem checked3 (_h : ∀ k : Fin 259, residualCheck k) : stepBatch 21 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point3_0_0
  · exact point3_0_1
  · exact point3_0_2
  · exact point3_0_3
  · exact point3_0_4
  · exact point3_0_5
  · exact point3_0_6
  · exact point3_0_7
  · exact point3_0_8
  · exact point3_0_9
  · exact point3_0_10
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
  · exact point3_1_4
  · exact point3_1_5
  · exact point3_1_6
  · exact point3_1_7
  · exact point3_1_8
  · exact point3_1_9
  · exact point3_1_10
  · exact point3_1_11
  · exact point3_1_12
  · exact point3_1_13
  · exact _h 0
  · exact point3_1_15
  · exact point3_1_16
  · exact point3_1_17
  · exact _h 1
  · exact point3_1_19

set_option maxHeartbeats 1600000 in
private theorem point4_0_0 : stepCheck 0 560 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_1 : stepCheck 0 561 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_3 : stepCheck 0 563 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_4 : stepCheck 0 564 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_5 : stepCheck 0 565 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_6 : stepCheck 0 566 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_7 : stepCheck 0 567 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_8 : stepCheck 0 568 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_9 : stepCheck 0 569 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_10 : stepCheck 0 570 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_12 : stepCheck 0 572 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_13 : stepCheck 0 573 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_14 : stepCheck 0 574 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_15 : stepCheck 0 575 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_16 : stepCheck 0 576 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_17 : stepCheck 0 577 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_18 : stepCheck 0 578 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_19 : stepCheck 0 579 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_0 : stepCheck 1 560 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_1 : stepCheck 1 561 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_2 : stepCheck 1 562 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_3 : stepCheck 1 563 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_4 : stepCheck 1 564 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_6 : stepCheck 1 566 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_7 : stepCheck 1 567 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_8 : stepCheck 1 568 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_9 : stepCheck 1 569 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_11 : stepCheck 1 571 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_12 : stepCheck 1 572 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_13 : stepCheck 1 573 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_14 : stepCheck 1 574 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_15 : stepCheck 1 575 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_16 : stepCheck 1 576 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_17 : stepCheck 1 577 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_19 : stepCheck 1 579 := by
  left
  decide +kernel

private theorem checked4 (_h : ∀ k : Fin 259, residualCheck k) : stepBatch 28 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point4_0_0
  · exact point4_0_1
  · exact _h 2
  · exact point4_0_3
  · exact point4_0_4
  · exact point4_0_5
  · exact point4_0_6
  · exact point4_0_7
  · exact point4_0_8
  · exact point4_0_9
  · exact point4_0_10
  · exact _h 3
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
  · exact _h 4
  · exact point4_1_6
  · exact point4_1_7
  · exact point4_1_8
  · exact point4_1_9
  · exact _h 5
  · exact point4_1_11
  · exact point4_1_12
  · exact point4_1_13
  · exact point4_1_14
  · exact point4_1_15
  · exact point4_1_16
  · exact point4_1_17
  · exact _h 6
  · exact point4_1_19

set_option maxHeartbeats 1600000 in
private theorem point5_0_0 : stepCheck 0 700 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_1 : stepCheck 0 701 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_2 : stepCheck 0 702 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_3 : stepCheck 0 703 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_4 : stepCheck 0 704 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_5 : stepCheck 0 705 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_6 : stepCheck 0 706 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_7 : stepCheck 0 707 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_8 : stepCheck 0 708 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_9 : stepCheck 0 709 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_10 : stepCheck 0 710 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_11 : stepCheck 0 711 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_14 : stepCheck 0 714 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_15 : stepCheck 0 715 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_16 : stepCheck 0 716 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_17 : stepCheck 0 717 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_18 : stepCheck 0 718 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_19 : stepCheck 0 719 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_0 : stepCheck 1 700 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_1 : stepCheck 1 701 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_2 : stepCheck 1 702 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_3 : stepCheck 1 703 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_4 : stepCheck 1 704 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_5 : stepCheck 1 705 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_6 : stepCheck 1 706 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_7 : stepCheck 1 707 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_8 : stepCheck 1 708 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_9 : stepCheck 1 709 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_10 : stepCheck 1 710 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_11 : stepCheck 1 711 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_12 : stepCheck 1 712 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_13 : stepCheck 1 713 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_14 : stepCheck 1 714 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_15 : stepCheck 1 715 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_16 : stepCheck 1 716 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_17 : stepCheck 1 717 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_18 : stepCheck 1 718 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_19 : stepCheck 1 719 := by
  left
  decide +kernel

private theorem checked5 (_h : ∀ k : Fin 259, residualCheck k) : stepBatch 35 := by
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
  · exact point5_0_7
  · exact point5_0_8
  · exact point5_0_9
  · exact point5_0_10
  · exact point5_0_11
  · exact _h 7
  · exact _h 8
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
  · exact point5_1_17
  · exact point5_1_18
  · exact point5_1_19

set_option maxHeartbeats 1600000 in
private theorem point6_0_0 : stepCheck 0 840 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_1 : stepCheck 0 841 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_2 : stepCheck 0 842 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_3 : stepCheck 0 843 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_5 : stepCheck 0 845 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_6 : stepCheck 0 846 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_7 : stepCheck 0 847 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_8 : stepCheck 0 848 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_9 : stepCheck 0 849 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_10 : stepCheck 0 850 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_11 : stepCheck 0 851 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_12 : stepCheck 0 852 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_13 : stepCheck 0 853 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_14 : stepCheck 0 854 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_15 : stepCheck 0 855 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_16 : stepCheck 0 856 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_17 : stepCheck 0 857 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_18 : stepCheck 0 858 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_19 : stepCheck 0 859 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_0 : stepCheck 1 840 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_1 : stepCheck 1 841 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_2 : stepCheck 1 842 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_3 : stepCheck 1 843 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_4 : stepCheck 1 844 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_5 : stepCheck 1 845 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_6 : stepCheck 1 846 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_7 : stepCheck 1 847 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_8 : stepCheck 1 848 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_9 : stepCheck 1 849 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_10 : stepCheck 1 850 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_11 : stepCheck 1 851 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_12 : stepCheck 1 852 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_13 : stepCheck 1 853 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_14 : stepCheck 1 854 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_15 : stepCheck 1 855 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_16 : stepCheck 1 856 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_17 : stepCheck 1 857 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_18 : stepCheck 1 858 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_19 : stepCheck 1 859 := by
  left
  decide +kernel

private theorem checked6 (_h : ∀ k : Fin 259, residualCheck k) : stepBatch 42 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point6_0_0
  · exact point6_0_1
  · exact point6_0_2
  · exact point6_0_3
  · exact _h 9
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
  · exact point6_1_8
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
  · exact point6_1_19

set_option maxHeartbeats 1600000 in
private theorem point7_0_0 : stepCheck 0 980 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_2 : stepCheck 0 982 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_3 : stepCheck 0 983 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_4 : stepCheck 0 984 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_5 : stepCheck 0 985 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_6 : stepCheck 0 986 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_8 : stepCheck 0 988 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_10 : stepCheck 0 990 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_11 : stepCheck 0 991 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_12 : stepCheck 0 992 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_13 : stepCheck 0 993 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_15 : stepCheck 0 995 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_16 : stepCheck 0 996 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_17 : stepCheck 0 997 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_18 : stepCheck 0 998 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_19 : stepCheck 0 999 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_0 : stepCheck 1 980 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_1 : stepCheck 1 981 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_2 : stepCheck 1 982 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_3 : stepCheck 1 983 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_4 : stepCheck 1 984 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_5 : stepCheck 1 985 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_6 : stepCheck 1 986 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_7 : stepCheck 1 987 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_8 : stepCheck 1 988 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_9 : stepCheck 1 989 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_10 : stepCheck 1 990 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_11 : stepCheck 1 991 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_12 : stepCheck 1 992 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_13 : stepCheck 1 993 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_15 : stepCheck 1 995 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_16 : stepCheck 1 996 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_17 : stepCheck 1 997 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_18 : stepCheck 1 998 := by
  left
  decide +kernel

private theorem checked7 (_h : ∀ k : Fin 259, residualCheck k) : stepBatch 49 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point7_0_0
  · exact _h 10
  · exact point7_0_2
  · exact point7_0_3
  · exact point7_0_4
  · exact point7_0_5
  · exact point7_0_6
  · exact _h 11
  · exact point7_0_8
  · exact _h 12
  · exact point7_0_10
  · exact point7_0_11
  · exact point7_0_12
  · exact point7_0_13
  · exact _h 13
  · exact point7_0_15
  · exact point7_0_16
  · exact point7_0_17
  · exact point7_0_18
  · exact point7_0_19
  · exact point7_1_0
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
  · exact _h 14
  · exact point7_1_15
  · exact point7_1_16
  · exact point7_1_17
  · exact point7_1_18
  · exact _h 15

set_option maxHeartbeats 1600000 in
private theorem point8_0_0 : stepCheck 0 1120 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_1 : stepCheck 0 1121 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_2 : stepCheck 0 1122 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_3 : stepCheck 0 1123 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_4 : stepCheck 0 1124 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_5 : stepCheck 0 1125 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_6 : stepCheck 0 1126 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_7 : stepCheck 0 1127 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_8 : stepCheck 0 1128 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_10 : stepCheck 0 1130 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_12 : stepCheck 0 1132 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_13 : stepCheck 0 1133 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_14 : stepCheck 0 1134 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_15 : stepCheck 0 1135 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_16 : stepCheck 0 1136 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_17 : stepCheck 0 1137 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_18 : stepCheck 0 1138 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_19 : stepCheck 0 1139 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_0 : stepCheck 1 1120 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_1 : stepCheck 1 1121 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_2 : stepCheck 1 1122 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_4 : stepCheck 1 1124 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_6 : stepCheck 1 1126 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_7 : stepCheck 1 1127 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_8 : stepCheck 1 1128 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_10 : stepCheck 1 1130 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_11 : stepCheck 1 1131 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_12 : stepCheck 1 1132 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_13 : stepCheck 1 1133 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_15 : stepCheck 1 1135 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_16 : stepCheck 1 1136 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_17 : stepCheck 1 1137 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_18 : stepCheck 1 1138 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_19 : stepCheck 1 1139 := by
  left
  decide +kernel

private theorem checked8 (_h : ∀ k : Fin 259, residualCheck k) : stepBatch 56 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point8_0_0
  · exact point8_0_1
  · exact point8_0_2
  · exact point8_0_3
  · exact point8_0_4
  · exact point8_0_5
  · exact point8_0_6
  · exact point8_0_7
  · exact point8_0_8
  · exact _h 16
  · exact point8_0_10
  · exact _h 17
  · exact point8_0_12
  · exact point8_0_13
  · exact point8_0_14
  · exact point8_0_15
  · exact point8_0_16
  · exact point8_0_17
  · exact point8_0_18
  · exact point8_0_19
  · exact point8_1_0
  · exact point8_1_1
  · exact point8_1_2
  · exact _h 18
  · exact point8_1_4
  · exact _h 19
  · exact point8_1_6
  · exact point8_1_7
  · exact point8_1_8
  · exact _h 20
  · exact point8_1_10
  · exact point8_1_11
  · exact point8_1_12
  · exact point8_1_13
  · exact _h 21
  · exact point8_1_15
  · exact point8_1_16
  · exact point8_1_17
  · exact point8_1_18
  · exact point8_1_19

set_option maxHeartbeats 1600000 in
private theorem point9_0_0 : stepCheck 0 1260 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_2 : stepCheck 0 1262 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_3 : stepCheck 0 1263 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_4 : stepCheck 0 1264 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_5 : stepCheck 0 1265 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_6 : stepCheck 0 1266 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_7 : stepCheck 0 1267 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_10 : stepCheck 0 1270 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_11 : stepCheck 0 1271 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_12 : stepCheck 0 1272 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_13 : stepCheck 0 1273 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_14 : stepCheck 0 1274 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_15 : stepCheck 0 1275 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_17 : stepCheck 0 1277 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_18 : stepCheck 0 1278 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_19 : stepCheck 0 1279 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_0 : stepCheck 1 1260 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_1 : stepCheck 1 1261 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_3 : stepCheck 1 1263 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_4 : stepCheck 1 1264 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_5 : stepCheck 1 1265 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_6 : stepCheck 1 1266 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_7 : stepCheck 1 1267 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_9 : stepCheck 1 1269 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_11 : stepCheck 1 1271 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_12 : stepCheck 1 1272 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_13 : stepCheck 1 1273 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_14 : stepCheck 1 1274 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_15 : stepCheck 1 1275 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_16 : stepCheck 1 1276 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_17 : stepCheck 1 1277 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_18 : stepCheck 1 1278 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_19 : stepCheck 1 1279 := by
  left
  decide +kernel

private theorem checked9 (_h : ∀ k : Fin 259, residualCheck k) : stepBatch 63 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point9_0_0
  · exact _h 22
  · exact point9_0_2
  · exact point9_0_3
  · exact point9_0_4
  · exact point9_0_5
  · exact point9_0_6
  · exact point9_0_7
  · exact _h 23
  · exact _h 24
  · exact point9_0_10
  · exact point9_0_11
  · exact point9_0_12
  · exact point9_0_13
  · exact point9_0_14
  · exact point9_0_15
  · exact _h 25
  · exact point9_0_17
  · exact point9_0_18
  · exact point9_0_19
  · exact point9_1_0
  · exact point9_1_1
  · exact _h 26
  · exact point9_1_3
  · exact point9_1_4
  · exact point9_1_5
  · exact point9_1_6
  · exact point9_1_7
  · exact _h 27
  · exact point9_1_9
  · exact _h 28
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
private theorem point10_0_0 : stepCheck 0 1400 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_1 : stepCheck 0 1401 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_2 : stepCheck 0 1402 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_3 : stepCheck 0 1403 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_6 : stepCheck 0 1406 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_7 : stepCheck 0 1407 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_9 : stepCheck 0 1409 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_10 : stepCheck 0 1410 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_12 : stepCheck 0 1412 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_13 : stepCheck 0 1413 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_14 : stepCheck 0 1414 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_15 : stepCheck 0 1415 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_18 : stepCheck 0 1418 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_19 : stepCheck 0 1419 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_0 : stepCheck 1 1400 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_1 : stepCheck 1 1401 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_2 : stepCheck 1 1402 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_3 : stepCheck 1 1403 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_4 : stepCheck 1 1404 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_6 : stepCheck 1 1406 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_7 : stepCheck 1 1407 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_8 : stepCheck 1 1408 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_9 : stepCheck 1 1409 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_10 : stepCheck 1 1410 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_11 : stepCheck 1 1411 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_12 : stepCheck 1 1412 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_13 : stepCheck 1 1413 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_14 : stepCheck 1 1414 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_15 : stepCheck 1 1415 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_17 : stepCheck 1 1417 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_18 : stepCheck 1 1418 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_19 : stepCheck 1 1419 := by
  left
  decide +kernel

private theorem checked10 (_h : ∀ k : Fin 259, residualCheck k) : stepBatch 70 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point10_0_0
  · exact point10_0_1
  · exact point10_0_2
  · exact point10_0_3
  · exact _h 29
  · exact _h 30
  · exact point10_0_6
  · exact point10_0_7
  · exact _h 31
  · exact point10_0_9
  · exact point10_0_10
  · exact _h 32
  · exact point10_0_12
  · exact point10_0_13
  · exact point10_0_14
  · exact point10_0_15
  · exact _h 33
  · exact _h 34
  · exact point10_0_18
  · exact point10_0_19
  · exact point10_1_0
  · exact point10_1_1
  · exact point10_1_2
  · exact point10_1_3
  · exact point10_1_4
  · exact _h 35
  · exact point10_1_6
  · exact point10_1_7
  · exact point10_1_8
  · exact point10_1_9
  · exact point10_1_10
  · exact point10_1_11
  · exact point10_1_12
  · exact point10_1_13
  · exact point10_1_14
  · exact point10_1_15
  · exact _h 36
  · exact point10_1_17
  · exact point10_1_18
  · exact point10_1_19

set_option maxHeartbeats 1600000 in
private theorem point11_0_0 : stepCheck 0 1540 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_1 : stepCheck 0 1541 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_2 : stepCheck 0 1542 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_3 : stepCheck 0 1543 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_4 : stepCheck 0 1544 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_5 : stepCheck 0 1545 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_6 : stepCheck 0 1546 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_7 : stepCheck 0 1547 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_8 : stepCheck 0 1548 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_9 : stepCheck 0 1549 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_11 : stepCheck 0 1551 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_12 : stepCheck 0 1552 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_13 : stepCheck 0 1553 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_14 : stepCheck 0 1554 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_15 : stepCheck 0 1555 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_16 : stepCheck 0 1556 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_17 : stepCheck 0 1557 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_18 : stepCheck 0 1558 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_19 : stepCheck 0 1559 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_1 : stepCheck 1 1541 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_2 : stepCheck 1 1542 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_3 : stepCheck 1 1543 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_4 : stepCheck 1 1544 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_5 : stepCheck 1 1545 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_6 : stepCheck 1 1546 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_8 : stepCheck 1 1548 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_9 : stepCheck 1 1549 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_11 : stepCheck 1 1551 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_13 : stepCheck 1 1553 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_14 : stepCheck 1 1554 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_15 : stepCheck 1 1555 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_16 : stepCheck 1 1556 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_17 : stepCheck 1 1557 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_18 : stepCheck 1 1558 := by
  left
  decide +kernel

private theorem checked11 (_h : ∀ k : Fin 259, residualCheck k) : stepBatch 77 := by
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
  · exact point11_0_7
  · exact point11_0_8
  · exact point11_0_9
  · exact _h 37
  · exact point11_0_11
  · exact point11_0_12
  · exact point11_0_13
  · exact point11_0_14
  · exact point11_0_15
  · exact point11_0_16
  · exact point11_0_17
  · exact point11_0_18
  · exact point11_0_19
  · exact _h 38
  · exact point11_1_1
  · exact point11_1_2
  · exact point11_1_3
  · exact point11_1_4
  · exact point11_1_5
  · exact point11_1_6
  · exact _h 39
  · exact point11_1_8
  · exact point11_1_9
  · exact _h 40
  · exact point11_1_11
  · exact _h 41
  · exact point11_1_13
  · exact point11_1_14
  · exact point11_1_15
  · exact point11_1_16
  · exact point11_1_17
  · exact point11_1_18
  · exact _h 42

set_option maxHeartbeats 1600000 in
private theorem point12_0_0 : stepCheck 0 1680 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_1 : stepCheck 0 1681 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_2 : stepCheck 0 1682 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_3 : stepCheck 0 1683 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_5 : stepCheck 0 1685 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_6 : stepCheck 0 1686 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_7 : stepCheck 0 1687 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_9 : stepCheck 0 1689 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_10 : stepCheck 0 1690 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_12 : stepCheck 0 1692 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_13 : stepCheck 0 1693 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_15 : stepCheck 0 1695 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_16 : stepCheck 0 1696 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_17 : stepCheck 0 1697 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_18 : stepCheck 0 1698 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_19 : stepCheck 0 1699 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_1 : stepCheck 1 1681 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_2 : stepCheck 1 1682 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_3 : stepCheck 1 1683 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_4 : stepCheck 1 1684 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_5 : stepCheck 1 1685 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_7 : stepCheck 1 1687 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_9 : stepCheck 1 1689 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_11 : stepCheck 1 1691 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_13 : stepCheck 1 1693 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_14 : stepCheck 1 1694 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_15 : stepCheck 1 1695 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_16 : stepCheck 1 1696 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_17 : stepCheck 1 1697 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_18 : stepCheck 1 1698 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_19 : stepCheck 1 1699 := by
  left
  decide +kernel

private theorem checked12 (_h : ∀ k : Fin 259, residualCheck k) : stepBatch 84 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point12_0_0
  · exact point12_0_1
  · exact point12_0_2
  · exact point12_0_3
  · exact _h 43
  · exact point12_0_5
  · exact point12_0_6
  · exact point12_0_7
  · exact _h 44
  · exact point12_0_9
  · exact point12_0_10
  · exact _h 45
  · exact point12_0_12
  · exact point12_0_13
  · exact _h 46
  · exact point12_0_15
  · exact point12_0_16
  · exact point12_0_17
  · exact point12_0_18
  · exact point12_0_19
  · exact _h 47
  · exact point12_1_1
  · exact point12_1_2
  · exact point12_1_3
  · exact point12_1_4
  · exact point12_1_5
  · exact _h 48
  · exact point12_1_7
  · exact _h 49
  · exact point12_1_9
  · exact _h 50
  · exact point12_1_11
  · exact _h 51
  · exact point12_1_13
  · exact point12_1_14
  · exact point12_1_15
  · exact point12_1_16
  · exact point12_1_17
  · exact point12_1_18
  · exact point12_1_19

set_option maxHeartbeats 1600000 in
private theorem point13_0_0 : stepCheck 0 1820 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_1 : stepCheck 0 1821 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_2 : stepCheck 0 1822 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_3 : stepCheck 0 1823 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_4 : stepCheck 0 1824 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_5 : stepCheck 0 1825 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_6 : stepCheck 0 1826 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_7 : stepCheck 0 1827 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_8 : stepCheck 0 1828 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_9 : stepCheck 0 1829 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_11 : stepCheck 0 1831 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_12 : stepCheck 0 1832 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_13 : stepCheck 0 1833 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_14 : stepCheck 0 1834 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_15 : stepCheck 0 1835 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_16 : stepCheck 0 1836 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_17 : stepCheck 0 1837 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_19 : stepCheck 0 1839 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_0 : stepCheck 1 1820 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_1 : stepCheck 1 1821 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_2 : stepCheck 1 1822 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_3 : stepCheck 1 1823 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_4 : stepCheck 1 1824 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_5 : stepCheck 1 1825 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_6 : stepCheck 1 1826 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_7 : stepCheck 1 1827 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_8 : stepCheck 1 1828 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_9 : stepCheck 1 1829 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_10 : stepCheck 1 1830 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_11 : stepCheck 1 1831 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_12 : stepCheck 1 1832 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_13 : stepCheck 1 1833 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_14 : stepCheck 1 1834 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_15 : stepCheck 1 1835 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_16 : stepCheck 1 1836 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_18 : stepCheck 1 1838 := by
  left
  decide +kernel

private theorem checked13 (_h : ∀ k : Fin 259, residualCheck k) : stepBatch 91 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point13_0_0
  · exact point13_0_1
  · exact point13_0_2
  · exact point13_0_3
  · exact point13_0_4
  · exact point13_0_5
  · exact point13_0_6
  · exact point13_0_7
  · exact point13_0_8
  · exact point13_0_9
  · exact _h 52
  · exact point13_0_11
  · exact point13_0_12
  · exact point13_0_13
  · exact point13_0_14
  · exact point13_0_15
  · exact point13_0_16
  · exact point13_0_17
  · exact _h 53
  · exact point13_0_19
  · exact point13_1_0
  · exact point13_1_1
  · exact point13_1_2
  · exact point13_1_3
  · exact point13_1_4
  · exact point13_1_5
  · exact point13_1_6
  · exact point13_1_7
  · exact point13_1_8
  · exact point13_1_9
  · exact point13_1_10
  · exact point13_1_11
  · exact point13_1_12
  · exact point13_1_13
  · exact point13_1_14
  · exact point13_1_15
  · exact point13_1_16
  · exact _h 54
  · exact point13_1_18
  · exact _h 55

set_option maxHeartbeats 1600000 in
private theorem point14_0_0 : stepCheck 0 1960 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_1 : stepCheck 0 1961 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_3 : stepCheck 0 1963 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_5 : stepCheck 0 1965 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_6 : stepCheck 0 1966 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_8 : stepCheck 0 1968 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_9 : stepCheck 0 1969 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_10 : stepCheck 0 1970 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_11 : stepCheck 0 1971 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_12 : stepCheck 0 1972 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_13 : stepCheck 0 1973 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_15 : stepCheck 0 1975 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_16 : stepCheck 0 1976 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_18 : stepCheck 0 1978 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_19 : stepCheck 0 1979 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_0 : stepCheck 1 1960 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_1 : stepCheck 1 1961 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_2 : stepCheck 1 1962 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_3 : stepCheck 1 1963 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_4 : stepCheck 1 1964 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_5 : stepCheck 1 1965 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_6 : stepCheck 1 1966 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_7 : stepCheck 1 1967 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_8 : stepCheck 1 1968 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_10 : stepCheck 1 1970 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_11 : stepCheck 1 1971 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_12 : stepCheck 1 1972 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_13 : stepCheck 1 1973 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_14 : stepCheck 1 1974 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_15 : stepCheck 1 1975 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_16 : stepCheck 1 1976 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_17 : stepCheck 1 1977 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_18 : stepCheck 1 1978 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_19 : stepCheck 1 1979 := by
  left
  decide +kernel

private theorem checked14 (_h : ∀ k : Fin 259, residualCheck k) : stepBatch 98 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point14_0_0
  · exact point14_0_1
  · exact _h 56
  · exact point14_0_3
  · exact _h 57
  · exact point14_0_5
  · exact point14_0_6
  · exact _h 58
  · exact point14_0_8
  · exact point14_0_9
  · exact point14_0_10
  · exact point14_0_11
  · exact point14_0_12
  · exact point14_0_13
  · exact _h 59
  · exact point14_0_15
  · exact point14_0_16
  · exact _h 60
  · exact point14_0_18
  · exact point14_0_19
  · exact point14_1_0
  · exact point14_1_1
  · exact point14_1_2
  · exact point14_1_3
  · exact point14_1_4
  · exact point14_1_5
  · exact point14_1_6
  · exact point14_1_7
  · exact point14_1_8
  · exact _h 61
  · exact point14_1_10
  · exact point14_1_11
  · exact point14_1_12
  · exact point14_1_13
  · exact point14_1_14
  · exact point14_1_15
  · exact point14_1_16
  · exact point14_1_17
  · exact point14_1_18
  · exact point14_1_19

set_option maxHeartbeats 1600000 in
private theorem point15_0_1 : stepCheck 0 2101 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_2 : stepCheck 0 2102 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_3 : stepCheck 0 2103 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_4 : stepCheck 0 2104 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_5 : stepCheck 0 2105 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_7 : stepCheck 0 2107 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_8 : stepCheck 0 2108 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_9 : stepCheck 0 2109 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_10 : stepCheck 0 2110 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_11 : stepCheck 0 2111 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_12 : stepCheck 0 2112 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_13 : stepCheck 0 2113 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_15 : stepCheck 0 2115 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_16 : stepCheck 0 2116 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_17 : stepCheck 0 2117 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_18 : stepCheck 0 2118 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_19 : stepCheck 0 2119 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_0 : stepCheck 1 2100 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_1 : stepCheck 1 2101 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_2 : stepCheck 1 2102 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_5 : stepCheck 1 2105 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_6 : stepCheck 1 2106 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_9 : stepCheck 1 2109 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_10 : stepCheck 1 2110 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_12 : stepCheck 1 2112 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_13 : stepCheck 1 2113 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_15 : stepCheck 1 2115 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_16 : stepCheck 1 2116 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_17 : stepCheck 1 2117 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_19 : stepCheck 1 2119 := by
  left
  decide +kernel

private theorem checked15 (_h : ∀ k : Fin 259, residualCheck k) : stepBatch 105 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact _h 62
  · exact point15_0_1
  · exact point15_0_2
  · exact point15_0_3
  · exact point15_0_4
  · exact point15_0_5
  · exact _h 63
  · exact point15_0_7
  · exact point15_0_8
  · exact point15_0_9
  · exact point15_0_10
  · exact point15_0_11
  · exact point15_0_12
  · exact point15_0_13
  · exact _h 64
  · exact point15_0_15
  · exact point15_0_16
  · exact point15_0_17
  · exact point15_0_18
  · exact point15_0_19
  · exact point15_1_0
  · exact point15_1_1
  · exact point15_1_2
  · exact _h 65
  · exact _h 66
  · exact point15_1_5
  · exact point15_1_6
  · exact _h 67
  · exact _h 68
  · exact point15_1_9
  · exact point15_1_10
  · exact _h 69
  · exact point15_1_12
  · exact point15_1_13
  · exact _h 70
  · exact point15_1_15
  · exact point15_1_16
  · exact point15_1_17
  · exact _h 71
  · exact point15_1_19

set_option maxHeartbeats 1600000 in
private theorem point16_0_0 : stepCheck 0 2240 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_1 : stepCheck 0 2241 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_2 : stepCheck 0 2242 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_3 : stepCheck 0 2243 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_4 : stepCheck 0 2244 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_7 : stepCheck 0 2247 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_9 : stepCheck 0 2249 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_10 : stepCheck 0 2250 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_11 : stepCheck 0 2251 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_12 : stepCheck 0 2252 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_14 : stepCheck 0 2254 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_16 : stepCheck 0 2256 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_17 : stepCheck 0 2257 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_18 : stepCheck 0 2258 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_19 : stepCheck 0 2259 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_0 : stepCheck 1 2240 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_1 : stepCheck 1 2241 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_2 : stepCheck 1 2242 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_3 : stepCheck 1 2243 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_4 : stepCheck 1 2244 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_5 : stepCheck 1 2245 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_6 : stepCheck 1 2246 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_7 : stepCheck 1 2247 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_8 : stepCheck 1 2248 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_9 : stepCheck 1 2249 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_10 : stepCheck 1 2250 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_11 : stepCheck 1 2251 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_12 : stepCheck 1 2252 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_13 : stepCheck 1 2253 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_14 : stepCheck 1 2254 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_16 : stepCheck 1 2256 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_18 : stepCheck 1 2258 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_19 : stepCheck 1 2259 := by
  left
  decide +kernel

private theorem checked16 (_h : ∀ k : Fin 259, residualCheck k) : stepBatch 112 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point16_0_0
  · exact point16_0_1
  · exact point16_0_2
  · exact point16_0_3
  · exact point16_0_4
  · exact _h 72
  · exact _h 73
  · exact point16_0_7
  · exact _h 74
  · exact point16_0_9
  · exact point16_0_10
  · exact point16_0_11
  · exact point16_0_12
  · exact _h 75
  · exact point16_0_14
  · exact _h 76
  · exact point16_0_16
  · exact point16_0_17
  · exact point16_0_18
  · exact point16_0_19
  · exact point16_1_0
  · exact point16_1_1
  · exact point16_1_2
  · exact point16_1_3
  · exact point16_1_4
  · exact point16_1_5
  · exact point16_1_6
  · exact point16_1_7
  · exact point16_1_8
  · exact point16_1_9
  · exact point16_1_10
  · exact point16_1_11
  · exact point16_1_12
  · exact point16_1_13
  · exact point16_1_14
  · exact _h 77
  · exact point16_1_16
  · exact _h 78
  · exact point16_1_18
  · exact point16_1_19

set_option maxHeartbeats 1600000 in
private theorem point17_0_2 : stepCheck 0 2382 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_3 : stepCheck 0 2383 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_4 : stepCheck 0 2384 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_6 : stepCheck 0 2386 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_8 : stepCheck 0 2388 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_9 : stepCheck 0 2389 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_10 : stepCheck 0 2390 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_11 : stepCheck 0 2391 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_13 : stepCheck 0 2393 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_14 : stepCheck 0 2394 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_15 : stepCheck 0 2395 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_16 : stepCheck 0 2396 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_17 : stepCheck 0 2397 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_0 : stepCheck 1 2380 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_1 : stepCheck 1 2381 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_3 : stepCheck 1 2383 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_4 : stepCheck 1 2384 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_5 : stepCheck 1 2385 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_8 : stepCheck 1 2388 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_9 : stepCheck 1 2389 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_10 : stepCheck 1 2390 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_11 : stepCheck 1 2391 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_12 : stepCheck 1 2392 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_13 : stepCheck 1 2393 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_14 : stepCheck 1 2394 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_19 : stepCheck 1 2399 := by
  left
  decide +kernel

private theorem checked17 (_h : ∀ k : Fin 259, residualCheck k) : stepBatch 119 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact _h 79
  · exact _h 80
  · exact point17_0_2
  · exact point17_0_3
  · exact point17_0_4
  · exact _h 81
  · exact point17_0_6
  · exact _h 82
  · exact point17_0_8
  · exact point17_0_9
  · exact point17_0_10
  · exact point17_0_11
  · exact _h 83
  · exact point17_0_13
  · exact point17_0_14
  · exact point17_0_15
  · exact point17_0_16
  · exact point17_0_17
  · exact _h 84
  · exact _h 85
  · exact point17_1_0
  · exact point17_1_1
  · exact _h 86
  · exact point17_1_3
  · exact point17_1_4
  · exact point17_1_5
  · exact _h 87
  · exact _h 88
  · exact point17_1_8
  · exact point17_1_9
  · exact point17_1_10
  · exact point17_1_11
  · exact point17_1_12
  · exact point17_1_13
  · exact point17_1_14
  · exact _h 89
  · exact _h 90
  · exact _h 91
  · exact _h 92
  · exact point17_1_19

set_option maxHeartbeats 1600000 in
private theorem point18_0_0 : stepCheck 0 2520 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_3 : stepCheck 0 2523 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_4 : stepCheck 0 2524 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_5 : stepCheck 0 2525 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_6 : stepCheck 0 2526 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_10 : stepCheck 0 2530 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_11 : stepCheck 0 2531 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_12 : stepCheck 0 2532 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_13 : stepCheck 0 2533 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_14 : stepCheck 0 2534 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_16 : stepCheck 0 2536 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_17 : stepCheck 0 2537 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_18 : stepCheck 0 2538 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_19 : stepCheck 0 2539 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_1 : stepCheck 1 2521 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_2 : stepCheck 1 2522 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_3 : stepCheck 1 2523 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_4 : stepCheck 1 2524 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_5 : stepCheck 1 2525 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_7 : stepCheck 1 2527 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_8 : stepCheck 1 2528 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_10 : stepCheck 1 2530 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_12 : stepCheck 1 2532 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_13 : stepCheck 1 2533 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_14 : stepCheck 1 2534 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_15 : stepCheck 1 2535 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_16 : stepCheck 1 2536 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_17 : stepCheck 1 2537 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_18 : stepCheck 1 2538 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_19 : stepCheck 1 2539 := by
  left
  decide +kernel

private theorem checked18 (_h : ∀ k : Fin 259, residualCheck k) : stepBatch 126 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point18_0_0
  · exact _h 93
  · exact _h 94
  · exact point18_0_3
  · exact point18_0_4
  · exact point18_0_5
  · exact point18_0_6
  · exact _h 95
  · exact _h 96
  · exact _h 97
  · exact point18_0_10
  · exact point18_0_11
  · exact point18_0_12
  · exact point18_0_13
  · exact point18_0_14
  · exact _h 98
  · exact point18_0_16
  · exact point18_0_17
  · exact point18_0_18
  · exact point18_0_19
  · exact _h 99
  · exact point18_1_1
  · exact point18_1_2
  · exact point18_1_3
  · exact point18_1_4
  · exact point18_1_5
  · exact _h 100
  · exact point18_1_7
  · exact point18_1_8
  · exact _h 101
  · exact point18_1_10
  · exact _h 102
  · exact point18_1_12
  · exact point18_1_13
  · exact point18_1_14
  · exact point18_1_15
  · exact point18_1_16
  · exact point18_1_17
  · exact point18_1_18
  · exact point18_1_19

set_option maxHeartbeats 1600000 in
private theorem point19_0_0 : stepCheck 0 2660 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_1 : stepCheck 0 2661 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_4 : stepCheck 0 2664 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_5 : stepCheck 0 2665 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_6 : stepCheck 0 2666 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_9 : stepCheck 0 2669 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_11 : stepCheck 0 2671 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_13 : stepCheck 0 2673 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_14 : stepCheck 0 2674 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_16 : stepCheck 0 2676 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_17 : stepCheck 0 2677 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_18 : stepCheck 0 2678 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_19 : stepCheck 0 2679 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_0 : stepCheck 1 2660 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_1 : stepCheck 1 2661 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_3 : stepCheck 1 2663 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_6 : stepCheck 1 2666 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_7 : stepCheck 1 2667 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_8 : stepCheck 1 2668 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_9 : stepCheck 1 2669 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_10 : stepCheck 1 2670 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_11 : stepCheck 1 2671 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_12 : stepCheck 1 2672 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_13 : stepCheck 1 2673 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_14 : stepCheck 1 2674 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_15 : stepCheck 1 2675 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_17 : stepCheck 1 2677 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_19 : stepCheck 1 2679 := by
  left
  decide +kernel

private theorem checked19 (_h : ∀ k : Fin 259, residualCheck k) : stepBatch 133 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point19_0_0
  · exact point19_0_1
  · exact _h 103
  · exact _h 104
  · exact point19_0_4
  · exact point19_0_5
  · exact point19_0_6
  · exact _h 105
  · exact _h 106
  · exact point19_0_9
  · exact _h 107
  · exact point19_0_11
  · exact _h 108
  · exact point19_0_13
  · exact point19_0_14
  · exact _h 109
  · exact point19_0_16
  · exact point19_0_17
  · exact point19_0_18
  · exact point19_0_19
  · exact point19_1_0
  · exact point19_1_1
  · exact _h 110
  · exact point19_1_3
  · exact _h 111
  · exact _h 112
  · exact point19_1_6
  · exact point19_1_7
  · exact point19_1_8
  · exact point19_1_9
  · exact point19_1_10
  · exact point19_1_11
  · exact point19_1_12
  · exact point19_1_13
  · exact point19_1_14
  · exact point19_1_15
  · exact _h 113
  · exact point19_1_17
  · exact _h 114
  · exact point19_1_19

set_option maxHeartbeats 1600000 in
private theorem point20_0_0 : stepCheck 0 2800 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_1 : stepCheck 0 2801 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_2 : stepCheck 0 2802 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_3 : stepCheck 0 2803 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_5 : stepCheck 0 2805 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_6 : stepCheck 0 2806 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_7 : stepCheck 0 2807 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_10 : stepCheck 0 2810 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_11 : stepCheck 0 2811 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_13 : stepCheck 0 2813 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_14 : stepCheck 0 2814 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_15 : stepCheck 0 2815 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_17 : stepCheck 0 2817 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_18 : stepCheck 0 2818 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_0 : stepCheck 1 2800 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_1 : stepCheck 1 2801 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_3 : stepCheck 1 2803 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_4 : stepCheck 1 2804 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_5 : stepCheck 1 2805 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_6 : stepCheck 1 2806 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_7 : stepCheck 1 2807 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_8 : stepCheck 1 2808 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_9 : stepCheck 1 2809 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_10 : stepCheck 1 2810 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_12 : stepCheck 1 2812 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_13 : stepCheck 1 2813 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_14 : stepCheck 1 2814 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_15 : stepCheck 1 2815 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_16 : stepCheck 1 2816 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_17 : stepCheck 1 2817 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_19 : stepCheck 1 2819 := by
  left
  decide +kernel

private theorem checked20 (_h : ∀ k : Fin 259, residualCheck k) : stepBatch 140 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point20_0_0
  · exact point20_0_1
  · exact point20_0_2
  · exact point20_0_3
  · exact _h 115
  · exact point20_0_5
  · exact point20_0_6
  · exact point20_0_7
  · exact _h 116
  · exact _h 117
  · exact point20_0_10
  · exact point20_0_11
  · exact _h 118
  · exact point20_0_13
  · exact point20_0_14
  · exact point20_0_15
  · exact _h 119
  · exact point20_0_17
  · exact point20_0_18
  · exact _h 120
  · exact point20_1_0
  · exact point20_1_1
  · exact _h 121
  · exact point20_1_3
  · exact point20_1_4
  · exact point20_1_5
  · exact point20_1_6
  · exact point20_1_7
  · exact point20_1_8
  · exact point20_1_9
  · exact point20_1_10
  · exact _h 122
  · exact point20_1_12
  · exact point20_1_13
  · exact point20_1_14
  · exact point20_1_15
  · exact point20_1_16
  · exact point20_1_17
  · exact _h 123
  · exact point20_1_19

set_option maxHeartbeats 1600000 in
private theorem point21_0_0 : stepCheck 0 2940 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_1 : stepCheck 0 2941 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_4 : stepCheck 0 2944 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_6 : stepCheck 0 2946 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_7 : stepCheck 0 2947 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_9 : stepCheck 0 2949 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_10 : stepCheck 0 2950 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_11 : stepCheck 0 2951 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_14 : stepCheck 0 2954 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_16 : stepCheck 0 2956 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_18 : stepCheck 0 2958 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_19 : stepCheck 0 2959 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_1 : stepCheck 1 2941 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_2 : stepCheck 1 2942 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_3 : stepCheck 1 2943 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_4 : stepCheck 1 2944 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_5 : stepCheck 1 2945 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_6 : stepCheck 1 2946 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_8 : stepCheck 1 2948 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_9 : stepCheck 1 2949 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_13 : stepCheck 1 2953 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_15 : stepCheck 1 2955 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_19 : stepCheck 1 2959 := by
  left
  decide +kernel

private theorem checked21 (_h : ∀ k : Fin 259, residualCheck k) : stepBatch 147 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point21_0_0
  · exact point21_0_1
  · exact _h 124
  · exact _h 125
  · exact point21_0_4
  · exact _h 126
  · exact point21_0_6
  · exact point21_0_7
  · exact _h 127
  · exact point21_0_9
  · exact point21_0_10
  · exact point21_0_11
  · exact _h 128
  · exact _h 129
  · exact point21_0_14
  · exact _h 130
  · exact point21_0_16
  · exact _h 131
  · exact point21_0_18
  · exact point21_0_19
  · exact _h 132
  · exact point21_1_1
  · exact point21_1_2
  · exact point21_1_3
  · exact point21_1_4
  · exact point21_1_5
  · exact point21_1_6
  · exact _h 133
  · exact point21_1_8
  · exact point21_1_9
  · exact _h 134
  · exact _h 135
  · exact _h 136
  · exact point21_1_13
  · exact _h 137
  · exact point21_1_15
  · exact _h 138
  · exact _h 139
  · exact _h 140
  · exact point21_1_19

set_option maxHeartbeats 1600000 in
private theorem point22_0_1 : stepCheck 0 3081 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_3 : stepCheck 0 3083 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_4 : stepCheck 0 3084 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_5 : stepCheck 0 3085 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_6 : stepCheck 0 3086 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_7 : stepCheck 0 3087 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_9 : stepCheck 0 3089 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_13 : stepCheck 0 3093 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_14 : stepCheck 0 3094 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_16 : stepCheck 0 3096 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_19 : stepCheck 0 3099 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_1 : stepCheck 1 3081 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_2 : stepCheck 1 3082 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_4 : stepCheck 1 3084 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_5 : stepCheck 1 3085 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_7 : stepCheck 1 3087 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_8 : stepCheck 1 3088 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_9 : stepCheck 1 3089 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_10 : stepCheck 1 3090 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_11 : stepCheck 1 3091 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_12 : stepCheck 1 3092 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_14 : stepCheck 1 3094 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_15 : stepCheck 1 3095 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_17 : stepCheck 1 3097 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_19 : stepCheck 1 3099 := by
  left
  decide +kernel

private theorem checked22 (_h : ∀ k : Fin 259, residualCheck k) : stepBatch 154 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact _h 141
  · exact point22_0_1
  · exact _h 142
  · exact point22_0_3
  · exact point22_0_4
  · exact point22_0_5
  · exact point22_0_6
  · exact point22_0_7
  · exact _h 143
  · exact point22_0_9
  · exact _h 144
  · exact _h 145
  · exact _h 146
  · exact point22_0_13
  · exact point22_0_14
  · exact _h 147
  · exact point22_0_16
  · exact _h 148
  · exact _h 149
  · exact point22_0_19
  · exact _h 150
  · exact point22_1_1
  · exact point22_1_2
  · exact _h 151
  · exact point22_1_4
  · exact point22_1_5
  · exact _h 152
  · exact point22_1_7
  · exact point22_1_8
  · exact point22_1_9
  · exact point22_1_10
  · exact point22_1_11
  · exact point22_1_12
  · exact _h 153
  · exact point22_1_14
  · exact point22_1_15
  · exact _h 154
  · exact point22_1_17
  · exact _h 155
  · exact point22_1_19

set_option maxHeartbeats 1600000 in
private theorem point23_0_0 : stepCheck 0 3220 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_1 : stepCheck 0 3221 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_3 : stepCheck 0 3223 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_4 : stepCheck 0 3224 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_5 : stepCheck 0 3225 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_7 : stepCheck 0 3227 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_8 : stepCheck 0 3228 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_10 : stepCheck 0 3230 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_13 : stepCheck 0 3233 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_14 : stepCheck 0 3234 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_16 : stepCheck 0 3236 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_17 : stepCheck 0 3237 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_18 : stepCheck 0 3238 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_19 : stepCheck 0 3239 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_0 : stepCheck 1 3220 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_3 : stepCheck 1 3223 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_4 : stepCheck 1 3224 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_5 : stepCheck 1 3225 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_7 : stepCheck 1 3227 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_12 : stepCheck 1 3232 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_13 : stepCheck 1 3233 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_14 : stepCheck 1 3234 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_17 : stepCheck 1 3237 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_18 : stepCheck 1 3238 := by
  left
  decide +kernel

private theorem checked23 (_h : ∀ k : Fin 259, residualCheck k) : stepBatch 161 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point23_0_0
  · exact point23_0_1
  · exact _h 156
  · exact point23_0_3
  · exact point23_0_4
  · exact point23_0_5
  · exact _h 157
  · exact point23_0_7
  · exact point23_0_8
  · exact _h 158
  · exact point23_0_10
  · exact _h 159
  · exact _h 160
  · exact point23_0_13
  · exact point23_0_14
  · exact _h 161
  · exact point23_0_16
  · exact point23_0_17
  · exact point23_0_18
  · exact point23_0_19
  · exact point23_1_0
  · exact _h 162
  · exact _h 163
  · exact point23_1_3
  · exact point23_1_4
  · exact point23_1_5
  · exact _h 164
  · exact point23_1_7
  · exact _h 165
  · exact _h 166
  · exact _h 167
  · exact _h 168
  · exact point23_1_12
  · exact point23_1_13
  · exact point23_1_14
  · exact _h 169
  · exact _h 170
  · exact point23_1_17
  · exact point23_1_18
  · exact _h 171

set_option maxHeartbeats 1600000 in
private theorem point24_0_0 : stepCheck 0 3360 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_2 : stepCheck 0 3362 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_3 : stepCheck 0 3363 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_6 : stepCheck 0 3366 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_7 : stepCheck 0 3367 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_10 : stepCheck 0 3370 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_12 : stepCheck 0 3372 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_14 : stepCheck 0 3374 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_15 : stepCheck 0 3375 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_16 : stepCheck 0 3376 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_17 : stepCheck 0 3377 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_1 : stepCheck 1 3361 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_2 : stepCheck 1 3362 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_3 : stepCheck 1 3363 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_5 : stepCheck 1 3365 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_6 : stepCheck 1 3366 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_7 : stepCheck 1 3367 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_9 : stepCheck 1 3369 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_13 : stepCheck 1 3373 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_14 : stepCheck 1 3374 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_15 : stepCheck 1 3375 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_17 : stepCheck 1 3377 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_19 : stepCheck 1 3379 := by
  left
  decide +kernel

private theorem checked24 (_h : ∀ k : Fin 259, residualCheck k) : stepBatch 168 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point24_0_0
  · exact _h 172
  · exact point24_0_2
  · exact point24_0_3
  · exact _h 173
  · exact _h 174
  · exact point24_0_6
  · exact point24_0_7
  · exact _h 175
  · exact _h 176
  · exact point24_0_10
  · exact _h 177
  · exact point24_0_12
  · exact _h 178
  · exact point24_0_14
  · exact point24_0_15
  · exact point24_0_16
  · exact point24_0_17
  · exact _h 179
  · exact _h 180
  · exact _h 181
  · exact point24_1_1
  · exact point24_1_2
  · exact point24_1_3
  · exact _h 182
  · exact point24_1_5
  · exact point24_1_6
  · exact point24_1_7
  · exact _h 183
  · exact point24_1_9
  · exact _h 184
  · exact _h 185
  · exact _h 186
  · exact point24_1_13
  · exact point24_1_14
  · exact point24_1_15
  · exact _h 187
  · exact point24_1_17
  · exact _h 188
  · exact point24_1_19

set_option maxHeartbeats 1600000 in
private theorem point25_0_0 : stepCheck 0 3500 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_1 : stepCheck 0 3501 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_2 : stepCheck 0 3502 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_3 : stepCheck 0 3503 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_4 : stepCheck 0 3504 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_9 : stepCheck 0 3509 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_12 : stepCheck 0 3512 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_13 : stepCheck 0 3513 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_14 : stepCheck 0 3514 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_15 : stepCheck 0 3515 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_17 : stepCheck 0 3517 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_18 : stepCheck 0 3518 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_19 : stepCheck 0 3519 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_0 : stepCheck 1 3500 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_1 : stepCheck 1 3501 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_3 : stepCheck 1 3503 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_4 : stepCheck 1 3504 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_5 : stepCheck 1 3505 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_6 : stepCheck 1 3506 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_7 : stepCheck 1 3507 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_9 : stepCheck 1 3509 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_10 : stepCheck 1 3510 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_11 : stepCheck 1 3511 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_12 : stepCheck 1 3512 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_16 : stepCheck 1 3516 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_18 : stepCheck 1 3518 := by
  left
  decide +kernel

private theorem checked25 (_h : ∀ k : Fin 259, residualCheck k) : stepBatch 175 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point25_0_0
  · exact point25_0_1
  · exact point25_0_2
  · exact point25_0_3
  · exact point25_0_4
  · exact _h 189
  · exact _h 190
  · exact _h 191
  · exact _h 192
  · exact point25_0_9
  · exact _h 193
  · exact _h 194
  · exact point25_0_12
  · exact point25_0_13
  · exact point25_0_14
  · exact point25_0_15
  · exact _h 195
  · exact point25_0_17
  · exact point25_0_18
  · exact point25_0_19
  · exact point25_1_0
  · exact point25_1_1
  · exact _h 196
  · exact point25_1_3
  · exact point25_1_4
  · exact point25_1_5
  · exact point25_1_6
  · exact point25_1_7
  · exact _h 197
  · exact point25_1_9
  · exact point25_1_10
  · exact point25_1_11
  · exact point25_1_12
  · exact _h 198
  · exact _h 199
  · exact _h 200
  · exact point25_1_16
  · exact _h 201
  · exact point25_1_18
  · exact _h 202

set_option maxHeartbeats 1600000 in
private theorem point26_0_0 : stepCheck 0 3640 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_1 : stepCheck 0 3641 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_2 : stepCheck 0 3642 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_3 : stepCheck 0 3643 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_6 : stepCheck 0 3646 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_9 : stepCheck 0 3649 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_13 : stepCheck 0 3653 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_14 : stepCheck 0 3654 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_15 : stepCheck 0 3655 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_16 : stepCheck 0 3656 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_19 : stepCheck 0 3659 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_0 : stepCheck 1 3640 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_1 : stepCheck 1 3641 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_2 : stepCheck 1 3642 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_4 : stepCheck 1 3644 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_7 : stepCheck 1 3647 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_8 : stepCheck 1 3648 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_10 : stepCheck 1 3650 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_11 : stepCheck 1 3651 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_12 : stepCheck 1 3652 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_13 : stepCheck 1 3653 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_14 : stepCheck 1 3654 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_15 : stepCheck 1 3655 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_16 : stepCheck 1 3656 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_18 : stepCheck 1 3658 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_19 : stepCheck 1 3659 := by
  left
  decide +kernel

private theorem checked26 (_h : ∀ k : Fin 259, residualCheck k) : stepBatch 182 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point26_0_0
  · exact point26_0_1
  · exact point26_0_2
  · exact point26_0_3
  · exact _h 203
  · exact _h 204
  · exact point26_0_6
  · exact _h 205
  · exact _h 206
  · exact point26_0_9
  · exact _h 207
  · exact _h 208
  · exact _h 209
  · exact point26_0_13
  · exact point26_0_14
  · exact point26_0_15
  · exact point26_0_16
  · exact _h 210
  · exact _h 211
  · exact point26_0_19
  · exact point26_1_0
  · exact point26_1_1
  · exact point26_1_2
  · exact _h 212
  · exact point26_1_4
  · exact _h 213
  · exact _h 214
  · exact point26_1_7
  · exact point26_1_8
  · exact _h 215
  · exact point26_1_10
  · exact point26_1_11
  · exact point26_1_12
  · exact point26_1_13
  · exact point26_1_14
  · exact point26_1_15
  · exact point26_1_16
  · exact _h 216
  · exact point26_1_18
  · exact point26_1_19

set_option maxHeartbeats 1600000 in
private theorem point27_0_6 : stepCheck 0 3786 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_7 : stepCheck 0 3787 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_10 : stepCheck 0 3790 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_11 : stepCheck 0 3791 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_13 : stepCheck 0 3793 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_16 : stepCheck 0 3796 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_18 : stepCheck 0 3798 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_0 : stepCheck 1 3780 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_2 : stepCheck 1 3782 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_3 : stepCheck 1 3783 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_5 : stepCheck 1 3785 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_6 : stepCheck 1 3786 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_7 : stepCheck 1 3787 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_9 : stepCheck 1 3789 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_10 : stepCheck 1 3790 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_14 : stepCheck 1 3794 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_15 : stepCheck 1 3795 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_16 : stepCheck 1 3796 := by
  left
  decide +kernel

private theorem checked27 (_h : ∀ k : Fin 259, residualCheck k) : stepBatch 189 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact _h 217
  · exact _h 218
  · exact _h 219
  · exact _h 220
  · exact _h 221
  · exact _h 222
  · exact point27_0_6
  · exact point27_0_7
  · exact _h 223
  · exact _h 224
  · exact point27_0_10
  · exact point27_0_11
  · exact _h 225
  · exact point27_0_13
  · exact _h 226
  · exact _h 227
  · exact point27_0_16
  · exact _h 228
  · exact point27_0_18
  · exact _h 229
  · exact point27_1_0
  · exact _h 230
  · exact point27_1_2
  · exact point27_1_3
  · exact _h 231
  · exact point27_1_5
  · exact point27_1_6
  · exact point27_1_7
  · exact _h 232
  · exact point27_1_9
  · exact point27_1_10
  · exact _h 233
  · exact _h 234
  · exact _h 235
  · exact point27_1_14
  · exact point27_1_15
  · exact point27_1_16
  · exact _h 236
  · exact _h 237
  · exact _h 238

set_option maxHeartbeats 1600000 in
private theorem point28_0_0 : stepCheck 0 3920 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_5 : stepCheck 0 3925 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_6 : stepCheck 0 3926 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_7 : stepCheck 0 3927 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_8 : stepCheck 0 3928 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_9 : stepCheck 0 3929 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_12 : stepCheck 0 3932 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_14 : stepCheck 0 3934 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_16 : stepCheck 0 3936 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_17 : stepCheck 0 3937 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_18 : stepCheck 0 3938 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_1 : stepCheck 1 3921 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_2 : stepCheck 1 3922 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_4 : stepCheck 1 3924 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_9 : stepCheck 1 3929 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_10 : stepCheck 1 3930 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_12 : stepCheck 1 3932 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_13 : stepCheck 1 3933 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_15 : stepCheck 1 3935 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_19 : stepCheck 1 3939 := by
  left
  decide +kernel

private theorem checked28 (_h : ∀ k : Fin 259, residualCheck k) : stepBatch 196 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point28_0_0
  · exact _h 239
  · exact _h 240
  · exact _h 241
  · exact _h 242
  · exact point28_0_5
  · exact point28_0_6
  · exact point28_0_7
  · exact point28_0_8
  · exact point28_0_9
  · exact _h 243
  · exact _h 244
  · exact point28_0_12
  · exact _h 245
  · exact point28_0_14
  · exact _h 246
  · exact point28_0_16
  · exact point28_0_17
  · exact point28_0_18
  · exact _h 247
  · exact _h 248
  · exact point28_1_1
  · exact point28_1_2
  · exact _h 249
  · exact point28_1_4
  · exact _h 250
  · exact _h 251
  · exact _h 252
  · exact _h 253
  · exact point28_1_9
  · exact point28_1_10
  · exact _h 254
  · exact point28_1_12
  · exact point28_1_13
  · exact _h 255
  · exact point28_1_15
  · exact _h 256
  · exact _h 257
  · exact _h 258
  · exact point28_1_19

/-- The algebraic transitions leave precisely the explicit residual checks. -/
public theorem part0_of_residual (h : ∀ k : Fin 259, residualCheck k) (b : Fin 29) :
    stepBatch ⟨7 * b.val + 0, by omega⟩ := by
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

/-- Four independent residual certificates complete part 0. -/
public theorem part0_of_batches (h : ∀ g : Fin 4, residualBatch g) (b : Fin 29) :
    stepBatch ⟨7 * b.val + 0, by omega⟩ :=
  part0_of_residual (all_of_batches h) b

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual
