module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Reduction
import Mathlib.Tactic.FinCases

/-!
# Residual checks for Rudvalis level-0 transition part 2

Of the 1160 forward transitions in the 29 batches numbered 2 modulo 7,
875 follow by word reduction in the cyclic groups of orders 2 and 4.
This module proves these checks and reduces part 2 to the remaining 285
explicit transitions, grouped into four independent finite certificates.

The source witnesses are those of `OrderLevel0Data`, documented in
`OrderCertificate/GenerateChain.g`. The accompanying generator only selects
proof branches; the word reductions and final coverage are kernel-checked.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
set_option maxRecDepth 30000
set_option Elab.async false

@[expose] public def target (k : Fin 285) : Fin 2 × Fin 4060 :=
  (if k.val < 142 then (if k.val < 71 then (if k.val < 35 then (if k.val < 17 then (if k.val < 8 then (if k.val < 4 then (if k.val < 2 then (if k.val < 1 then (1, 188) else (1, 324)) else (if k.val < 3 then (0, 472) else (1, 472))) else (if k.val < 6 then (if k.val < 5 then (1, 476) else (0, 600)) else (if k.val < 7 then (0, 605) else (0, 611)))) else (if k.val < 12 then (if k.val < 10 then (if k.val < 9 then (0, 613) else (0, 616)) else (if k.val < 11 then (0, 618) else (1, 605))) else (if k.val < 14 then (if k.val < 13 then (1, 607) else (1, 617)) else (if k.val < 15 then (0, 750) else (if k.val < 16 then (0, 755) else (0, 758)))))) else (if k.val < 26 then (if k.val < 21 then (if k.val < 19 then (if k.val < 18 then (1, 742) else (1, 752)) else (if k.val < 20 then (1, 758) else (0, 883))) else (if k.val < 23 then (if k.val < 22 then (0, 886) else (1, 885)) else (if k.val < 24 then (1, 891) else (if k.val < 25 then (1, 895) else (0, 1025))))) else (if k.val < 30 then (if k.val < 28 then (if k.val < 27 then (0, 1029) else (0, 1030)) else (if k.val < 29 then (0, 1038) else (0, 1164))) else (if k.val < 32 then (if k.val < 31 then (0, 1167) else (0, 1177)) else (if k.val < 33 then (0, 1178) else (if k.val < 34 then (1, 1160) else (1, 1161))))))) else (if k.val < 53 then (if k.val < 44 then (if k.val < 39 then (if k.val < 37 then (if k.val < 36 then (1, 1165) else (1, 1166)) else (if k.val < 38 then (1, 1176) else (0, 1304))) else (if k.val < 41 then (if k.val < 40 then (0, 1307) else (0, 1314)) else (if k.val < 42 then (0, 1317) else (if k.val < 43 then (1, 1311) else (0, 1444))))) else (if k.val < 48 then (if k.val < 46 then (if k.val < 45 then (0, 1448) else (0, 1454)) else (if k.val < 47 then (0, 1456) else (1, 1446))) else (if k.val < 50 then (if k.val < 49 then (0, 1583) else (0, 1587)) else (if k.val < 51 then (0, 1588) else (if k.val < 52 then (1, 1580) else (1, 1587)))))) else (if k.val < 62 then (if k.val < 57 then (if k.val < 55 then (if k.val < 54 then (1, 1592) else (1, 1599)) else (if k.val < 56 then (0, 1726) else (0, 1730))) else (if k.val < 59 then (if k.val < 58 then (0, 1733) else (0, 1734)) else (if k.val < 60 then (0, 1735) else (if k.val < 61 then (0, 1738) else (1, 1722))))) else (if k.val < 66 then (if k.val < 64 then (if k.val < 63 then (1, 1729) else (1, 1732)) else (if k.val < 65 then (1, 1736) else (1, 1737))) else (if k.val < 68 then (if k.val < 67 then (0, 1861) else (0, 1863)) else (if k.val < 69 then (0, 1868) else (if k.val < 70 then (0, 1870) else (0, 1872)))))))) else (if k.val < 106 then (if k.val < 88 then (if k.val < 79 then (if k.val < 75 then (if k.val < 73 then (if k.val < 72 then (0, 1873) else (0, 1879)) else (if k.val < 74 then (1, 1860) else (1, 1862))) else (if k.val < 77 then (if k.val < 76 then (1, 1867) else (1, 1871)) else (if k.val < 78 then (1, 1872) else (1, 1874)))) else (if k.val < 83 then (if k.val < 81 then (if k.val < 80 then (0, 2011) else (0, 2012)) else (if k.val < 82 then (0, 2017) else (1, 2002))) else (if k.val < 85 then (if k.val < 84 then (1, 2007) else (1, 2009)) else (if k.val < 86 then (1, 2017) else (if k.val < 87 then (1, 2019) else (0, 2146)))))) else (if k.val < 97 then (if k.val < 92 then (if k.val < 90 then (if k.val < 89 then (1, 2141) else (1, 2142)) else (if k.val < 91 then (1, 2146) else (1, 2151))) else (if k.val < 94 then (if k.val < 93 then (1, 2152) else (1, 2153)) else (if k.val < 95 then (1, 2156) else (if k.val < 96 then (1, 2159) else (0, 2283))))) else (if k.val < 101 then (if k.val < 99 then (if k.val < 98 then (0, 2284) else (0, 2288)) else (if k.val < 100 then (0, 2289) else (0, 2290))) else (if k.val < 103 then (if k.val < 102 then (0, 2291) else (0, 2292)) else (if k.val < 104 then (0, 2295) else (if k.val < 105 then (0, 2296) else (1, 2280))))))) else (if k.val < 124 then (if k.val < 115 then (if k.val < 110 then (if k.val < 108 then (if k.val < 107 then (1, 2281) else (1, 2282)) else (if k.val < 109 then (1, 2294) else (1, 2295))) else (if k.val < 112 then (if k.val < 111 then (0, 2428) else (0, 2433)) else (if k.val < 113 then (0, 2437) else (if k.val < 114 then (0, 2438) else (1, 2420))))) else (if k.val < 119 then (if k.val < 117 then (if k.val < 116 then (1, 2423) else (0, 2561)) else (if k.val < 118 then (0, 2571) else (0, 2579))) else (if k.val < 121 then (if k.val < 120 then (1, 2566) else (1, 2568)) else (if k.val < 122 then (1, 2569) else (if k.val < 123 then (1, 2573) else (1, 2574)))))) else (if k.val < 133 then (if k.val < 128 then (if k.val < 126 then (if k.val < 125 then (1, 2576) else (1, 2577)) else (if k.val < 127 then (1, 2578) else (1, 2579))) else (if k.val < 130 then (if k.val < 129 then (0, 2700) else (0, 2704)) else (if k.val < 131 then (0, 2714) else (if k.val < 132 then (0, 2715) else (0, 2717))))) else (if k.val < 137 then (if k.val < 135 then (if k.val < 134 then (1, 2700) else (1, 2701)) else (if k.val < 136 then (1, 2712) else (1, 2719))) else (if k.val < 139 then (if k.val < 138 then (0, 2841) else (0, 2846)) else (if k.val < 140 then (0, 2847) else (if k.val < 141 then (0, 2849) else (0, 2854))))))))) else (if k.val < 213 then (if k.val < 177 then (if k.val < 159 then (if k.val < 150 then (if k.val < 146 then (if k.val < 144 then (if k.val < 143 then (0, 2858) else (1, 2844)) else (if k.val < 145 then (1, 2851) else (1, 2852))) else (if k.val < 148 then (if k.val < 147 then (1, 2858) else (1, 2859)) else (if k.val < 149 then (0, 2982) else (0, 2983)))) else (if k.val < 154 then (if k.val < 152 then (if k.val < 151 then (0, 2989) else (0, 2992)) else (if k.val < 153 then (0, 2993) else (0, 2995))) else (if k.val < 156 then (if k.val < 155 then (1, 2984) else (1, 2986)) else (if k.val < 157 then (1, 2988) else (if k.val < 158 then (1, 2990) else (1, 2996)))))) else (if k.val < 168 then (if k.val < 163 then (if k.val < 161 then (if k.val < 160 then (1, 2999) else (0, 3122)) else (if k.val < 162 then (0, 3125) else (0, 3136))) else (if k.val < 165 then (if k.val < 164 then (0, 3138) else (0, 3139)) else (if k.val < 166 then (1, 3122) else (if k.val < 167 then (1, 3123) else (1, 3126))))) else (if k.val < 172 then (if k.val < 170 then (if k.val < 169 then (1, 3129) else (1, 3135)) else (if k.val < 171 then (1, 3138) else (0, 3264))) else (if k.val < 174 then (if k.val < 173 then (0, 3265) else (0, 3266)) else (if k.val < 175 then (0, 3267) else (if k.val < 176 then (0, 3270) else (0, 3271))))))) else (if k.val < 195 then (if k.val < 186 then (if k.val < 181 then (if k.val < 179 then (if k.val < 178 then (0, 3272) else (0, 3273)) else (if k.val < 180 then (0, 3274) else (0, 3276))) else (if k.val < 183 then (if k.val < 182 then (0, 3277) else (0, 3279)) else (if k.val < 184 then (1, 3260) else (if k.val < 185 then (1, 3263) else (1, 3266))))) else (if k.val < 190 then (if k.val < 188 then (if k.val < 187 then (1, 3269) else (1, 3270)) else (if k.val < 189 then (1, 3272) else (1, 3275))) else (if k.val < 192 then (if k.val < 191 then (0, 3400) else (0, 3403)) else (if k.val < 193 then (0, 3406) else (if k.val < 194 then (0, 3407) else (0, 3410)))))) else (if k.val < 204 then (if k.val < 199 then (if k.val < 197 then (if k.val < 196 then (0, 3413) else (0, 3417)) else (if k.val < 198 then (0, 3419) else (1, 3402))) else (if k.val < 201 then (if k.val < 200 then (1, 3409) else (1, 3410)) else (if k.val < 202 then (1, 3411) else (if k.val < 203 then (1, 3412) else (1, 3415))))) else (if k.val < 208 then (if k.val < 206 then (if k.val < 205 then (1, 3416) else (1, 3418)) else (if k.val < 207 then (1, 3419) else (0, 3540))) else (if k.val < 210 then (if k.val < 209 then (0, 3542) else (0, 3543)) else (if k.val < 211 then (0, 3545) else (if k.val < 212 then (0, 3546) else (0, 3548)))))))) else (if k.val < 249 then (if k.val < 231 then (if k.val < 222 then (if k.val < 217 then (if k.val < 215 then (if k.val < 214 then (0, 3553) else (0, 3555)) else (if k.val < 216 then (0, 3556) else (0, 3557))) else (if k.val < 219 then (if k.val < 218 then (0, 3559) else (1, 3541)) else (if k.val < 220 then (1, 3542) else (if k.val < 221 then (1, 3544) else (1, 3545))))) else (if k.val < 226 then (if k.val < 224 then (if k.val < 223 then (1, 3547) else (1, 3549)) else (if k.val < 225 then (1, 3550) else (0, 3682))) else (if k.val < 228 then (if k.val < 227 then (0, 3685) else (0, 3686)) else (if k.val < 229 then (0, 3688) else (if k.val < 230 then (0, 3689) else (0, 3695)))))) else (if k.val < 240 then (if k.val < 235 then (if k.val < 233 then (if k.val < 232 then (0, 3696) else (0, 3698)) else (if k.val < 234 then (0, 3699) else (1, 3680))) else (if k.val < 237 then (if k.val < 236 then (1, 3681) else (1, 3682)) else (if k.val < 238 then (1, 3683) else (if k.val < 239 then (1, 3684) else (1, 3687))))) else (if k.val < 244 then (if k.val < 242 then (if k.val < 241 then (1, 3688) else (1, 3697)) else (if k.val < 243 then (1, 3698) else (1, 3699))) else (if k.val < 246 then (if k.val < 245 then (0, 3821) else (0, 3822)) else (if k.val < 247 then (0, 3823) else (if k.val < 248 then (0, 3824) else (0, 3826))))))) else (if k.val < 267 then (if k.val < 258 then (if k.val < 253 then (if k.val < 251 then (if k.val < 250 then (0, 3827) else (0, 3828)) else (if k.val < 252 then (0, 3829) else (0, 3830))) else (if k.val < 255 then (if k.val < 254 then (0, 3833) else (0, 3835)) else (if k.val < 256 then (0, 3836) else (if k.val < 257 then (0, 3837) else (0, 3838))))) else (if k.val < 262 then (if k.val < 260 then (if k.val < 259 then (1, 3821) else (1, 3824)) else (if k.val < 261 then (1, 3828) else (1, 3831))) else (if k.val < 264 then (if k.val < 263 then (1, 3832) else (1, 3834)) else (if k.val < 265 then (1, 3836) else (if k.val < 266 then (1, 3837) else (1, 3839)))))) else (if k.val < 276 then (if k.val < 271 then (if k.val < 269 then (if k.val < 268 then (0, 3960) else (0, 3966)) else (if k.val < 270 then (0, 3969) else (0, 3975))) else (if k.val < 273 then (if k.val < 272 then (0, 3976) else (0, 3977)) else (if k.val < 274 then (0, 3978) else (if k.val < 275 then (0, 3979) else (1, 3960))))) else (if k.val < 280 then (if k.val < 278 then (if k.val < 277 then (1, 3964) else (1, 3965)) else (if k.val < 279 then (1, 3967) else (1, 3969))) else (if k.val < 282 then (if k.val < 281 then (1, 3970) else (1, 3971)) else (if k.val < 283 then (1, 3972) else (if k.val < 284 then (1, 3974) else (1, 3978))))))))))

@[expose] public def residualCheck (k : Fin 285) : Prop :=
  stepCheck (target k).1 (target k).2

/-- Groups 0, 1, 2 contain 72 transitions; group 3 contains 69. -/
@[expose] public def residualBatch (g : Fin 4) : Prop :=
  ∀ (s : Fin 72) (h : 72 * g.val + s.val < 285),
    residualCheck ⟨72 * g.val + s.val, h⟩

public theorem all_of_batches (h : ∀ g : Fin 4, residualBatch g) :
    ∀ k : Fin 285, residualCheck k := by
  intro k
  let g : Fin 4 := ⟨k.val / 72, by omega⟩
  let s : Fin 72 := ⟨k.val % 72, by omega⟩
  have hlt : 72 * g.val + s.val < 285 := by dsimp [g, s]; omega
  have hk : (⟨72 * g.val + s.val, hlt⟩ : Fin 285) = k := by
    apply Fin.ext
    dsimp [g, s]
    omega
  simpa only [hk] using h g s hlt

set_option maxHeartbeats 1600000 in
private theorem point0_0_0 : stepCheck 0 40 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_1 : stepCheck 0 41 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_2 : stepCheck 0 42 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_3 : stepCheck 0 43 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_4 : stepCheck 0 44 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_5 : stepCheck 0 45 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_6 : stepCheck 0 46 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_7 : stepCheck 0 47 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_8 : stepCheck 0 48 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_9 : stepCheck 0 49 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_10 : stepCheck 0 50 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_11 : stepCheck 0 51 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_12 : stepCheck 0 52 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_13 : stepCheck 0 53 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_14 : stepCheck 0 54 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_15 : stepCheck 0 55 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_16 : stepCheck 0 56 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_17 : stepCheck 0 57 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_18 : stepCheck 0 58 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_19 : stepCheck 0 59 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_0 : stepCheck 1 40 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_1 : stepCheck 1 41 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_2 : stepCheck 1 42 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_3 : stepCheck 1 43 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_4 : stepCheck 1 44 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_5 : stepCheck 1 45 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_6 : stepCheck 1 46 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_7 : stepCheck 1 47 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_8 : stepCheck 1 48 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_9 : stepCheck 1 49 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_10 : stepCheck 1 50 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_11 : stepCheck 1 51 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_12 : stepCheck 1 52 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_13 : stepCheck 1 53 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_14 : stepCheck 1 54 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_15 : stepCheck 1 55 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_16 : stepCheck 1 56 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_17 : stepCheck 1 57 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_18 : stepCheck 1 58 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_19 : stepCheck 1 59 := by
  left
  decide +kernel

private theorem checked0 (_h : ∀ k : Fin 285, residualCheck k) : stepBatch 2 := by
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
private theorem point1_0_0 : stepCheck 0 180 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_1 : stepCheck 0 181 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_2 : stepCheck 0 182 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_3 : stepCheck 0 183 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_4 : stepCheck 0 184 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_5 : stepCheck 0 185 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_6 : stepCheck 0 186 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_7 : stepCheck 0 187 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_8 : stepCheck 0 188 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_9 : stepCheck 0 189 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_10 : stepCheck 0 190 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_11 : stepCheck 0 191 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_12 : stepCheck 0 192 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_13 : stepCheck 0 193 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_14 : stepCheck 0 194 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_15 : stepCheck 0 195 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_16 : stepCheck 0 196 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_17 : stepCheck 0 197 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_18 : stepCheck 0 198 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_19 : stepCheck 0 199 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_0 : stepCheck 1 180 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_1 : stepCheck 1 181 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_2 : stepCheck 1 182 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_3 : stepCheck 1 183 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_4 : stepCheck 1 184 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_5 : stepCheck 1 185 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_6 : stepCheck 1 186 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_7 : stepCheck 1 187 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_9 : stepCheck 1 189 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_10 : stepCheck 1 190 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_11 : stepCheck 1 191 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_12 : stepCheck 1 192 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_13 : stepCheck 1 193 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_14 : stepCheck 1 194 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_15 : stepCheck 1 195 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_16 : stepCheck 1 196 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_17 : stepCheck 1 197 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_18 : stepCheck 1 198 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_19 : stepCheck 1 199 := by
  left
  decide +kernel

private theorem checked1 (_h : ∀ k : Fin 285, residualCheck k) : stepBatch 9 := by
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
  · exact _h 0
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
private theorem point2_0_0 : stepCheck 0 320 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_1 : stepCheck 0 321 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_2 : stepCheck 0 322 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_3 : stepCheck 0 323 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_4 : stepCheck 0 324 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_5 : stepCheck 0 325 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_6 : stepCheck 0 326 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_7 : stepCheck 0 327 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_8 : stepCheck 0 328 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_9 : stepCheck 0 329 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_10 : stepCheck 0 330 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_11 : stepCheck 0 331 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_12 : stepCheck 0 332 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_13 : stepCheck 0 333 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_14 : stepCheck 0 334 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_15 : stepCheck 0 335 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_16 : stepCheck 0 336 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_17 : stepCheck 0 337 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_18 : stepCheck 0 338 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_19 : stepCheck 0 339 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_0 : stepCheck 1 320 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_1 : stepCheck 1 321 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_2 : stepCheck 1 322 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_3 : stepCheck 1 323 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_5 : stepCheck 1 325 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_6 : stepCheck 1 326 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_7 : stepCheck 1 327 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_8 : stepCheck 1 328 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_9 : stepCheck 1 329 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_10 : stepCheck 1 330 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_11 : stepCheck 1 331 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_12 : stepCheck 1 332 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_13 : stepCheck 1 333 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_14 : stepCheck 1 334 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_15 : stepCheck 1 335 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_16 : stepCheck 1 336 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_17 : stepCheck 1 337 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_18 : stepCheck 1 338 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_19 : stepCheck 1 339 := by
  left
  decide +kernel

private theorem checked2 (_h : ∀ k : Fin 285, residualCheck k) : stepBatch 16 := by
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
  · exact _h 1
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
private theorem point3_0_0 : stepCheck 0 460 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_1 : stepCheck 0 461 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_2 : stepCheck 0 462 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_3 : stepCheck 0 463 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_4 : stepCheck 0 464 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_5 : stepCheck 0 465 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_6 : stepCheck 0 466 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_7 : stepCheck 0 467 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_8 : stepCheck 0 468 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_9 : stepCheck 0 469 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_10 : stepCheck 0 470 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_11 : stepCheck 0 471 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_13 : stepCheck 0 473 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_14 : stepCheck 0 474 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_15 : stepCheck 0 475 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_16 : stepCheck 0 476 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_17 : stepCheck 0 477 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_18 : stepCheck 0 478 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_19 : stepCheck 0 479 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_0 : stepCheck 1 460 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_1 : stepCheck 1 461 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_2 : stepCheck 1 462 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_3 : stepCheck 1 463 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_4 : stepCheck 1 464 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_5 : stepCheck 1 465 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_6 : stepCheck 1 466 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_7 : stepCheck 1 467 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_8 : stepCheck 1 468 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_9 : stepCheck 1 469 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_10 : stepCheck 1 470 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_11 : stepCheck 1 471 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_13 : stepCheck 1 473 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_14 : stepCheck 1 474 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_15 : stepCheck 1 475 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_17 : stepCheck 1 477 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_18 : stepCheck 1 478 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_19 : stepCheck 1 479 := by
  left
  decide +kernel

private theorem checked3 (_h : ∀ k : Fin 285, residualCheck k) : stepBatch 23 := by
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
  · exact _h 2
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
  · exact _h 3
  · exact point3_1_13
  · exact point3_1_14
  · exact point3_1_15
  · exact _h 4
  · exact point3_1_17
  · exact point3_1_18
  · exact point3_1_19

set_option maxHeartbeats 1600000 in
private theorem point4_0_1 : stepCheck 0 601 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_2 : stepCheck 0 602 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_3 : stepCheck 0 603 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_4 : stepCheck 0 604 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_6 : stepCheck 0 606 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_7 : stepCheck 0 607 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_8 : stepCheck 0 608 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_9 : stepCheck 0 609 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_10 : stepCheck 0 610 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_12 : stepCheck 0 612 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_14 : stepCheck 0 614 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_15 : stepCheck 0 615 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_17 : stepCheck 0 617 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_19 : stepCheck 0 619 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_0 : stepCheck 1 600 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_1 : stepCheck 1 601 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_2 : stepCheck 1 602 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_3 : stepCheck 1 603 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_4 : stepCheck 1 604 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_6 : stepCheck 1 606 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_8 : stepCheck 1 608 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_9 : stepCheck 1 609 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_10 : stepCheck 1 610 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_11 : stepCheck 1 611 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_12 : stepCheck 1 612 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_13 : stepCheck 1 613 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_14 : stepCheck 1 614 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_15 : stepCheck 1 615 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_16 : stepCheck 1 616 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_18 : stepCheck 1 618 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_19 : stepCheck 1 619 := by
  left
  decide +kernel

private theorem checked4 (_h : ∀ k : Fin 285, residualCheck k) : stepBatch 30 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact _h 5
  · exact point4_0_1
  · exact point4_0_2
  · exact point4_0_3
  · exact point4_0_4
  · exact _h 6
  · exact point4_0_6
  · exact point4_0_7
  · exact point4_0_8
  · exact point4_0_9
  · exact point4_0_10
  · exact _h 7
  · exact point4_0_12
  · exact _h 8
  · exact point4_0_14
  · exact point4_0_15
  · exact _h 9
  · exact point4_0_17
  · exact _h 10
  · exact point4_0_19
  · exact point4_1_0
  · exact point4_1_1
  · exact point4_1_2
  · exact point4_1_3
  · exact point4_1_4
  · exact _h 11
  · exact point4_1_6
  · exact _h 12
  · exact point4_1_8
  · exact point4_1_9
  · exact point4_1_10
  · exact point4_1_11
  · exact point4_1_12
  · exact point4_1_13
  · exact point4_1_14
  · exact point4_1_15
  · exact point4_1_16
  · exact _h 13
  · exact point4_1_18
  · exact point4_1_19

set_option maxHeartbeats 1600000 in
private theorem point5_0_0 : stepCheck 0 740 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_1 : stepCheck 0 741 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_2 : stepCheck 0 742 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_3 : stepCheck 0 743 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_4 : stepCheck 0 744 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_5 : stepCheck 0 745 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_6 : stepCheck 0 746 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_7 : stepCheck 0 747 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_8 : stepCheck 0 748 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_9 : stepCheck 0 749 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_11 : stepCheck 0 751 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_12 : stepCheck 0 752 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_13 : stepCheck 0 753 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_14 : stepCheck 0 754 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_16 : stepCheck 0 756 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_17 : stepCheck 0 757 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_19 : stepCheck 0 759 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_0 : stepCheck 1 740 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_1 : stepCheck 1 741 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_3 : stepCheck 1 743 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_4 : stepCheck 1 744 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_5 : stepCheck 1 745 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_6 : stepCheck 1 746 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_7 : stepCheck 1 747 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_8 : stepCheck 1 748 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_9 : stepCheck 1 749 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_10 : stepCheck 1 750 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_11 : stepCheck 1 751 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_13 : stepCheck 1 753 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_14 : stepCheck 1 754 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_15 : stepCheck 1 755 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_16 : stepCheck 1 756 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_17 : stepCheck 1 757 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_19 : stepCheck 1 759 := by
  left
  decide +kernel

private theorem checked5 (_h : ∀ k : Fin 285, residualCheck k) : stepBatch 37 := by
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
  · exact _h 14
  · exact point5_0_11
  · exact point5_0_12
  · exact point5_0_13
  · exact point5_0_14
  · exact _h 15
  · exact point5_0_16
  · exact point5_0_17
  · exact _h 16
  · exact point5_0_19
  · exact point5_1_0
  · exact point5_1_1
  · exact _h 17
  · exact point5_1_3
  · exact point5_1_4
  · exact point5_1_5
  · exact point5_1_6
  · exact point5_1_7
  · exact point5_1_8
  · exact point5_1_9
  · exact point5_1_10
  · exact point5_1_11
  · exact _h 18
  · exact point5_1_13
  · exact point5_1_14
  · exact point5_1_15
  · exact point5_1_16
  · exact point5_1_17
  · exact _h 19
  · exact point5_1_19

set_option maxHeartbeats 1600000 in
private theorem point6_0_0 : stepCheck 0 880 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_1 : stepCheck 0 881 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_2 : stepCheck 0 882 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_4 : stepCheck 0 884 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_5 : stepCheck 0 885 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_7 : stepCheck 0 887 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_8 : stepCheck 0 888 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_9 : stepCheck 0 889 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_10 : stepCheck 0 890 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_11 : stepCheck 0 891 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_12 : stepCheck 0 892 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_13 : stepCheck 0 893 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_14 : stepCheck 0 894 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_15 : stepCheck 0 895 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_16 : stepCheck 0 896 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_17 : stepCheck 0 897 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_18 : stepCheck 0 898 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_19 : stepCheck 0 899 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_0 : stepCheck 1 880 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_1 : stepCheck 1 881 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_2 : stepCheck 1 882 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_3 : stepCheck 1 883 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_4 : stepCheck 1 884 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_6 : stepCheck 1 886 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_7 : stepCheck 1 887 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_8 : stepCheck 1 888 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_9 : stepCheck 1 889 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_10 : stepCheck 1 890 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_12 : stepCheck 1 892 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_13 : stepCheck 1 893 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_14 : stepCheck 1 894 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_16 : stepCheck 1 896 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_17 : stepCheck 1 897 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_18 : stepCheck 1 898 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_19 : stepCheck 1 899 := by
  left
  decide +kernel

private theorem checked6 (_h : ∀ k : Fin 285, residualCheck k) : stepBatch 44 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point6_0_0
  · exact point6_0_1
  · exact point6_0_2
  · exact _h 20
  · exact point6_0_4
  · exact point6_0_5
  · exact _h 21
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
  · exact _h 22
  · exact point6_1_6
  · exact point6_1_7
  · exact point6_1_8
  · exact point6_1_9
  · exact point6_1_10
  · exact _h 23
  · exact point6_1_12
  · exact point6_1_13
  · exact point6_1_14
  · exact _h 24
  · exact point6_1_16
  · exact point6_1_17
  · exact point6_1_18
  · exact point6_1_19

set_option maxHeartbeats 1600000 in
private theorem point7_0_0 : stepCheck 0 1020 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_1 : stepCheck 0 1021 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_2 : stepCheck 0 1022 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_3 : stepCheck 0 1023 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_4 : stepCheck 0 1024 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_6 : stepCheck 0 1026 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_7 : stepCheck 0 1027 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_8 : stepCheck 0 1028 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_11 : stepCheck 0 1031 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_12 : stepCheck 0 1032 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_13 : stepCheck 0 1033 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_14 : stepCheck 0 1034 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_15 : stepCheck 0 1035 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_16 : stepCheck 0 1036 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_17 : stepCheck 0 1037 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_19 : stepCheck 0 1039 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_0 : stepCheck 1 1020 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_1 : stepCheck 1 1021 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_2 : stepCheck 1 1022 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_3 : stepCheck 1 1023 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_4 : stepCheck 1 1024 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_5 : stepCheck 1 1025 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_6 : stepCheck 1 1026 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_7 : stepCheck 1 1027 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_8 : stepCheck 1 1028 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_9 : stepCheck 1 1029 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_10 : stepCheck 1 1030 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_11 : stepCheck 1 1031 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_12 : stepCheck 1 1032 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_13 : stepCheck 1 1033 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_14 : stepCheck 1 1034 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_15 : stepCheck 1 1035 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_16 : stepCheck 1 1036 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_17 : stepCheck 1 1037 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_18 : stepCheck 1 1038 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_19 : stepCheck 1 1039 := by
  left
  decide +kernel

private theorem checked7 (_h : ∀ k : Fin 285, residualCheck k) : stepBatch 51 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point7_0_0
  · exact point7_0_1
  · exact point7_0_2
  · exact point7_0_3
  · exact point7_0_4
  · exact _h 25
  · exact point7_0_6
  · exact point7_0_7
  · exact point7_0_8
  · exact _h 26
  · exact _h 27
  · exact point7_0_11
  · exact point7_0_12
  · exact point7_0_13
  · exact point7_0_14
  · exact point7_0_15
  · exact point7_0_16
  · exact point7_0_17
  · exact _h 28
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
  · exact point7_1_14
  · exact point7_1_15
  · exact point7_1_16
  · exact point7_1_17
  · exact point7_1_18
  · exact point7_1_19

set_option maxHeartbeats 1600000 in
private theorem point8_0_0 : stepCheck 0 1160 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_1 : stepCheck 0 1161 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_2 : stepCheck 0 1162 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_3 : stepCheck 0 1163 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_5 : stepCheck 0 1165 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_6 : stepCheck 0 1166 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_8 : stepCheck 0 1168 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_9 : stepCheck 0 1169 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_10 : stepCheck 0 1170 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_11 : stepCheck 0 1171 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_12 : stepCheck 0 1172 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_13 : stepCheck 0 1173 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_14 : stepCheck 0 1174 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_15 : stepCheck 0 1175 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_16 : stepCheck 0 1176 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_19 : stepCheck 0 1179 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_2 : stepCheck 1 1162 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_3 : stepCheck 1 1163 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_4 : stepCheck 1 1164 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_7 : stepCheck 1 1167 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_8 : stepCheck 1 1168 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_9 : stepCheck 1 1169 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_10 : stepCheck 1 1170 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_11 : stepCheck 1 1171 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_12 : stepCheck 1 1172 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_13 : stepCheck 1 1173 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_14 : stepCheck 1 1174 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_15 : stepCheck 1 1175 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_17 : stepCheck 1 1177 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_18 : stepCheck 1 1178 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_19 : stepCheck 1 1179 := by
  left
  decide +kernel

private theorem checked8 (_h : ∀ k : Fin 285, residualCheck k) : stepBatch 58 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point8_0_0
  · exact point8_0_1
  · exact point8_0_2
  · exact point8_0_3
  · exact _h 29
  · exact point8_0_5
  · exact point8_0_6
  · exact _h 30
  · exact point8_0_8
  · exact point8_0_9
  · exact point8_0_10
  · exact point8_0_11
  · exact point8_0_12
  · exact point8_0_13
  · exact point8_0_14
  · exact point8_0_15
  · exact point8_0_16
  · exact _h 31
  · exact _h 32
  · exact point8_0_19
  · exact _h 33
  · exact _h 34
  · exact point8_1_2
  · exact point8_1_3
  · exact point8_1_4
  · exact _h 35
  · exact _h 36
  · exact point8_1_7
  · exact point8_1_8
  · exact point8_1_9
  · exact point8_1_10
  · exact point8_1_11
  · exact point8_1_12
  · exact point8_1_13
  · exact point8_1_14
  · exact point8_1_15
  · exact _h 37
  · exact point8_1_17
  · exact point8_1_18
  · exact point8_1_19

set_option maxHeartbeats 1600000 in
private theorem point9_0_0 : stepCheck 0 1300 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_1 : stepCheck 0 1301 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_2 : stepCheck 0 1302 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_3 : stepCheck 0 1303 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_5 : stepCheck 0 1305 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_6 : stepCheck 0 1306 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_8 : stepCheck 0 1308 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_9 : stepCheck 0 1309 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_10 : stepCheck 0 1310 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_11 : stepCheck 0 1311 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_12 : stepCheck 0 1312 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_13 : stepCheck 0 1313 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_15 : stepCheck 0 1315 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_16 : stepCheck 0 1316 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_18 : stepCheck 0 1318 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_19 : stepCheck 0 1319 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_0 : stepCheck 1 1300 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_1 : stepCheck 1 1301 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_2 : stepCheck 1 1302 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_3 : stepCheck 1 1303 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_4 : stepCheck 1 1304 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_5 : stepCheck 1 1305 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_6 : stepCheck 1 1306 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_7 : stepCheck 1 1307 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_8 : stepCheck 1 1308 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_9 : stepCheck 1 1309 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_10 : stepCheck 1 1310 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_12 : stepCheck 1 1312 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_13 : stepCheck 1 1313 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_14 : stepCheck 1 1314 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_15 : stepCheck 1 1315 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_16 : stepCheck 1 1316 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_17 : stepCheck 1 1317 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_18 : stepCheck 1 1318 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_19 : stepCheck 1 1319 := by
  left
  decide +kernel

private theorem checked9 (_h : ∀ k : Fin 285, residualCheck k) : stepBatch 65 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point9_0_0
  · exact point9_0_1
  · exact point9_0_2
  · exact point9_0_3
  · exact _h 38
  · exact point9_0_5
  · exact point9_0_6
  · exact _h 39
  · exact point9_0_8
  · exact point9_0_9
  · exact point9_0_10
  · exact point9_0_11
  · exact point9_0_12
  · exact point9_0_13
  · exact _h 40
  · exact point9_0_15
  · exact point9_0_16
  · exact _h 41
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
  · exact point9_1_8
  · exact point9_1_9
  · exact point9_1_10
  · exact _h 42
  · exact point9_1_12
  · exact point9_1_13
  · exact point9_1_14
  · exact point9_1_15
  · exact point9_1_16
  · exact point9_1_17
  · exact point9_1_18
  · exact point9_1_19

set_option maxHeartbeats 1600000 in
private theorem point10_0_0 : stepCheck 0 1440 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_1 : stepCheck 0 1441 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_2 : stepCheck 0 1442 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_3 : stepCheck 0 1443 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_5 : stepCheck 0 1445 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_6 : stepCheck 0 1446 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_7 : stepCheck 0 1447 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_9 : stepCheck 0 1449 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_10 : stepCheck 0 1450 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_11 : stepCheck 0 1451 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_12 : stepCheck 0 1452 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_13 : stepCheck 0 1453 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_15 : stepCheck 0 1455 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_17 : stepCheck 0 1457 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_18 : stepCheck 0 1458 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_19 : stepCheck 0 1459 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_0 : stepCheck 1 1440 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_1 : stepCheck 1 1441 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_2 : stepCheck 1 1442 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_3 : stepCheck 1 1443 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_4 : stepCheck 1 1444 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_5 : stepCheck 1 1445 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_7 : stepCheck 1 1447 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_8 : stepCheck 1 1448 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_9 : stepCheck 1 1449 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_10 : stepCheck 1 1450 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_11 : stepCheck 1 1451 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_12 : stepCheck 1 1452 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_13 : stepCheck 1 1453 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_14 : stepCheck 1 1454 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_15 : stepCheck 1 1455 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_16 : stepCheck 1 1456 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_17 : stepCheck 1 1457 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_18 : stepCheck 1 1458 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_19 : stepCheck 1 1459 := by
  left
  decide +kernel

private theorem checked10 (_h : ∀ k : Fin 285, residualCheck k) : stepBatch 72 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point10_0_0
  · exact point10_0_1
  · exact point10_0_2
  · exact point10_0_3
  · exact _h 43
  · exact point10_0_5
  · exact point10_0_6
  · exact point10_0_7
  · exact _h 44
  · exact point10_0_9
  · exact point10_0_10
  · exact point10_0_11
  · exact point10_0_12
  · exact point10_0_13
  · exact _h 45
  · exact point10_0_15
  · exact _h 46
  · exact point10_0_17
  · exact point10_0_18
  · exact point10_0_19
  · exact point10_1_0
  · exact point10_1_1
  · exact point10_1_2
  · exact point10_1_3
  · exact point10_1_4
  · exact point10_1_5
  · exact _h 47
  · exact point10_1_7
  · exact point10_1_8
  · exact point10_1_9
  · exact point10_1_10
  · exact point10_1_11
  · exact point10_1_12
  · exact point10_1_13
  · exact point10_1_14
  · exact point10_1_15
  · exact point10_1_16
  · exact point10_1_17
  · exact point10_1_18
  · exact point10_1_19

set_option maxHeartbeats 1600000 in
private theorem point11_0_0 : stepCheck 0 1580 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_1 : stepCheck 0 1581 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_2 : stepCheck 0 1582 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_4 : stepCheck 0 1584 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_5 : stepCheck 0 1585 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_6 : stepCheck 0 1586 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_9 : stepCheck 0 1589 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_10 : stepCheck 0 1590 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_11 : stepCheck 0 1591 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_12 : stepCheck 0 1592 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_13 : stepCheck 0 1593 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_14 : stepCheck 0 1594 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_15 : stepCheck 0 1595 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_16 : stepCheck 0 1596 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_17 : stepCheck 0 1597 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_18 : stepCheck 0 1598 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_19 : stepCheck 0 1599 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_1 : stepCheck 1 1581 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_2 : stepCheck 1 1582 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_3 : stepCheck 1 1583 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_4 : stepCheck 1 1584 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_5 : stepCheck 1 1585 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_6 : stepCheck 1 1586 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_8 : stepCheck 1 1588 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_9 : stepCheck 1 1589 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_10 : stepCheck 1 1590 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_11 : stepCheck 1 1591 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_13 : stepCheck 1 1593 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_14 : stepCheck 1 1594 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_15 : stepCheck 1 1595 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_16 : stepCheck 1 1596 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_17 : stepCheck 1 1597 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_18 : stepCheck 1 1598 := by
  left
  decide +kernel

private theorem checked11 (_h : ∀ k : Fin 285, residualCheck k) : stepBatch 79 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point11_0_0
  · exact point11_0_1
  · exact point11_0_2
  · exact _h 48
  · exact point11_0_4
  · exact point11_0_5
  · exact point11_0_6
  · exact _h 49
  · exact _h 50
  · exact point11_0_9
  · exact point11_0_10
  · exact point11_0_11
  · exact point11_0_12
  · exact point11_0_13
  · exact point11_0_14
  · exact point11_0_15
  · exact point11_0_16
  · exact point11_0_17
  · exact point11_0_18
  · exact point11_0_19
  · exact _h 51
  · exact point11_1_1
  · exact point11_1_2
  · exact point11_1_3
  · exact point11_1_4
  · exact point11_1_5
  · exact point11_1_6
  · exact _h 52
  · exact point11_1_8
  · exact point11_1_9
  · exact point11_1_10
  · exact point11_1_11
  · exact _h 53
  · exact point11_1_13
  · exact point11_1_14
  · exact point11_1_15
  · exact point11_1_16
  · exact point11_1_17
  · exact point11_1_18
  · exact _h 54

set_option maxHeartbeats 1600000 in
private theorem point12_0_0 : stepCheck 0 1720 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_1 : stepCheck 0 1721 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_2 : stepCheck 0 1722 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_3 : stepCheck 0 1723 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_4 : stepCheck 0 1724 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_5 : stepCheck 0 1725 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_7 : stepCheck 0 1727 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_8 : stepCheck 0 1728 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_9 : stepCheck 0 1729 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_11 : stepCheck 0 1731 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_12 : stepCheck 0 1732 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_16 : stepCheck 0 1736 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_17 : stepCheck 0 1737 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_19 : stepCheck 0 1739 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_0 : stepCheck 1 1720 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_1 : stepCheck 1 1721 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_3 : stepCheck 1 1723 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_4 : stepCheck 1 1724 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_5 : stepCheck 1 1725 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_6 : stepCheck 1 1726 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_7 : stepCheck 1 1727 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_8 : stepCheck 1 1728 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_10 : stepCheck 1 1730 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_11 : stepCheck 1 1731 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_13 : stepCheck 1 1733 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_14 : stepCheck 1 1734 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_15 : stepCheck 1 1735 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_18 : stepCheck 1 1738 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_19 : stepCheck 1 1739 := by
  left
  decide +kernel

private theorem checked12 (_h : ∀ k : Fin 285, residualCheck k) : stepBatch 86 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point12_0_0
  · exact point12_0_1
  · exact point12_0_2
  · exact point12_0_3
  · exact point12_0_4
  · exact point12_0_5
  · exact _h 55
  · exact point12_0_7
  · exact point12_0_8
  · exact point12_0_9
  · exact _h 56
  · exact point12_0_11
  · exact point12_0_12
  · exact _h 57
  · exact _h 58
  · exact _h 59
  · exact point12_0_16
  · exact point12_0_17
  · exact _h 60
  · exact point12_0_19
  · exact point12_1_0
  · exact point12_1_1
  · exact _h 61
  · exact point12_1_3
  · exact point12_1_4
  · exact point12_1_5
  · exact point12_1_6
  · exact point12_1_7
  · exact point12_1_8
  · exact _h 62
  · exact point12_1_10
  · exact point12_1_11
  · exact _h 63
  · exact point12_1_13
  · exact point12_1_14
  · exact point12_1_15
  · exact _h 64
  · exact _h 65
  · exact point12_1_18
  · exact point12_1_19

set_option maxHeartbeats 1600000 in
private theorem point13_0_0 : stepCheck 0 1860 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_2 : stepCheck 0 1862 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_4 : stepCheck 0 1864 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_5 : stepCheck 0 1865 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_6 : stepCheck 0 1866 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_7 : stepCheck 0 1867 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_9 : stepCheck 0 1869 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_11 : stepCheck 0 1871 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_14 : stepCheck 0 1874 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_15 : stepCheck 0 1875 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_16 : stepCheck 0 1876 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_17 : stepCheck 0 1877 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_18 : stepCheck 0 1878 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_1 : stepCheck 1 1861 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_3 : stepCheck 1 1863 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_4 : stepCheck 1 1864 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_5 : stepCheck 1 1865 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_6 : stepCheck 1 1866 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_8 : stepCheck 1 1868 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_9 : stepCheck 1 1869 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_10 : stepCheck 1 1870 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_13 : stepCheck 1 1873 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_15 : stepCheck 1 1875 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_16 : stepCheck 1 1876 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_17 : stepCheck 1 1877 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_18 : stepCheck 1 1878 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_19 : stepCheck 1 1879 := by
  left
  decide +kernel

private theorem checked13 (_h : ∀ k : Fin 285, residualCheck k) : stepBatch 93 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point13_0_0
  · exact _h 66
  · exact point13_0_2
  · exact _h 67
  · exact point13_0_4
  · exact point13_0_5
  · exact point13_0_6
  · exact point13_0_7
  · exact _h 68
  · exact point13_0_9
  · exact _h 69
  · exact point13_0_11
  · exact _h 70
  · exact _h 71
  · exact point13_0_14
  · exact point13_0_15
  · exact point13_0_16
  · exact point13_0_17
  · exact point13_0_18
  · exact _h 72
  · exact _h 73
  · exact point13_1_1
  · exact _h 74
  · exact point13_1_3
  · exact point13_1_4
  · exact point13_1_5
  · exact point13_1_6
  · exact _h 75
  · exact point13_1_8
  · exact point13_1_9
  · exact point13_1_10
  · exact _h 76
  · exact _h 77
  · exact point13_1_13
  · exact _h 78
  · exact point13_1_15
  · exact point13_1_16
  · exact point13_1_17
  · exact point13_1_18
  · exact point13_1_19

set_option maxHeartbeats 1600000 in
private theorem point14_0_0 : stepCheck 0 2000 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_1 : stepCheck 0 2001 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_2 : stepCheck 0 2002 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_3 : stepCheck 0 2003 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_4 : stepCheck 0 2004 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_5 : stepCheck 0 2005 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_6 : stepCheck 0 2006 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_7 : stepCheck 0 2007 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_8 : stepCheck 0 2008 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_9 : stepCheck 0 2009 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_10 : stepCheck 0 2010 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_13 : stepCheck 0 2013 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_14 : stepCheck 0 2014 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_15 : stepCheck 0 2015 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_16 : stepCheck 0 2016 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_18 : stepCheck 0 2018 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_19 : stepCheck 0 2019 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_0 : stepCheck 1 2000 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_1 : stepCheck 1 2001 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_3 : stepCheck 1 2003 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_4 : stepCheck 1 2004 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_5 : stepCheck 1 2005 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_6 : stepCheck 1 2006 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_8 : stepCheck 1 2008 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_10 : stepCheck 1 2010 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_11 : stepCheck 1 2011 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_12 : stepCheck 1 2012 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_13 : stepCheck 1 2013 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_14 : stepCheck 1 2014 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_15 : stepCheck 1 2015 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_16 : stepCheck 1 2016 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_18 : stepCheck 1 2018 := by
  left
  decide +kernel

private theorem checked14 (_h : ∀ k : Fin 285, residualCheck k) : stepBatch 100 := by
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
  · exact point14_0_7
  · exact point14_0_8
  · exact point14_0_9
  · exact point14_0_10
  · exact _h 79
  · exact _h 80
  · exact point14_0_13
  · exact point14_0_14
  · exact point14_0_15
  · exact point14_0_16
  · exact _h 81
  · exact point14_0_18
  · exact point14_0_19
  · exact point14_1_0
  · exact point14_1_1
  · exact _h 82
  · exact point14_1_3
  · exact point14_1_4
  · exact point14_1_5
  · exact point14_1_6
  · exact _h 83
  · exact point14_1_8
  · exact _h 84
  · exact point14_1_10
  · exact point14_1_11
  · exact point14_1_12
  · exact point14_1_13
  · exact point14_1_14
  · exact point14_1_15
  · exact point14_1_16
  · exact _h 85
  · exact point14_1_18
  · exact _h 86

set_option maxHeartbeats 1600000 in
private theorem point15_0_0 : stepCheck 0 2140 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_1 : stepCheck 0 2141 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_2 : stepCheck 0 2142 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_3 : stepCheck 0 2143 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_4 : stepCheck 0 2144 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_5 : stepCheck 0 2145 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_7 : stepCheck 0 2147 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_8 : stepCheck 0 2148 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_9 : stepCheck 0 2149 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_10 : stepCheck 0 2150 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_11 : stepCheck 0 2151 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_12 : stepCheck 0 2152 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_13 : stepCheck 0 2153 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_14 : stepCheck 0 2154 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_15 : stepCheck 0 2155 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_16 : stepCheck 0 2156 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_17 : stepCheck 0 2157 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_18 : stepCheck 0 2158 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_19 : stepCheck 0 2159 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_0 : stepCheck 1 2140 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_3 : stepCheck 1 2143 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_4 : stepCheck 1 2144 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_5 : stepCheck 1 2145 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_7 : stepCheck 1 2147 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_8 : stepCheck 1 2148 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_9 : stepCheck 1 2149 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_10 : stepCheck 1 2150 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_14 : stepCheck 1 2154 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_15 : stepCheck 1 2155 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_17 : stepCheck 1 2157 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_18 : stepCheck 1 2158 := by
  left
  decide +kernel

private theorem checked15 (_h : ∀ k : Fin 285, residualCheck k) : stepBatch 107 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point15_0_0
  · exact point15_0_1
  · exact point15_0_2
  · exact point15_0_3
  · exact point15_0_4
  · exact point15_0_5
  · exact _h 87
  · exact point15_0_7
  · exact point15_0_8
  · exact point15_0_9
  · exact point15_0_10
  · exact point15_0_11
  · exact point15_0_12
  · exact point15_0_13
  · exact point15_0_14
  · exact point15_0_15
  · exact point15_0_16
  · exact point15_0_17
  · exact point15_0_18
  · exact point15_0_19
  · exact point15_1_0
  · exact _h 88
  · exact _h 89
  · exact point15_1_3
  · exact point15_1_4
  · exact point15_1_5
  · exact _h 90
  · exact point15_1_7
  · exact point15_1_8
  · exact point15_1_9
  · exact point15_1_10
  · exact _h 91
  · exact _h 92
  · exact _h 93
  · exact point15_1_14
  · exact point15_1_15
  · exact _h 94
  · exact point15_1_17
  · exact point15_1_18
  · exact _h 95

set_option maxHeartbeats 1600000 in
private theorem point16_0_0 : stepCheck 0 2280 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_1 : stepCheck 0 2281 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_2 : stepCheck 0 2282 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_5 : stepCheck 0 2285 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_6 : stepCheck 0 2286 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_7 : stepCheck 0 2287 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_13 : stepCheck 0 2293 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_14 : stepCheck 0 2294 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_17 : stepCheck 0 2297 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_18 : stepCheck 0 2298 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_19 : stepCheck 0 2299 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_3 : stepCheck 1 2283 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_4 : stepCheck 1 2284 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_5 : stepCheck 1 2285 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_6 : stepCheck 1 2286 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_7 : stepCheck 1 2287 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_8 : stepCheck 1 2288 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_9 : stepCheck 1 2289 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_10 : stepCheck 1 2290 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_11 : stepCheck 1 2291 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_12 : stepCheck 1 2292 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_13 : stepCheck 1 2293 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_16 : stepCheck 1 2296 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_17 : stepCheck 1 2297 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_18 : stepCheck 1 2298 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_19 : stepCheck 1 2299 := by
  left
  decide +kernel

private theorem checked16 (_h : ∀ k : Fin 285, residualCheck k) : stepBatch 114 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point16_0_0
  · exact point16_0_1
  · exact point16_0_2
  · exact _h 96
  · exact _h 97
  · exact point16_0_5
  · exact point16_0_6
  · exact point16_0_7
  · exact _h 98
  · exact _h 99
  · exact _h 100
  · exact _h 101
  · exact _h 102
  · exact point16_0_13
  · exact point16_0_14
  · exact _h 103
  · exact _h 104
  · exact point16_0_17
  · exact point16_0_18
  · exact point16_0_19
  · exact _h 105
  · exact _h 106
  · exact _h 107
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
  · exact _h 108
  · exact _h 109
  · exact point16_1_16
  · exact point16_1_17
  · exact point16_1_18
  · exact point16_1_19

set_option maxHeartbeats 1600000 in
private theorem point17_0_0 : stepCheck 0 2420 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_1 : stepCheck 0 2421 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_2 : stepCheck 0 2422 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_3 : stepCheck 0 2423 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_4 : stepCheck 0 2424 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_5 : stepCheck 0 2425 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_6 : stepCheck 0 2426 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_7 : stepCheck 0 2427 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_9 : stepCheck 0 2429 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_10 : stepCheck 0 2430 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_11 : stepCheck 0 2431 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_12 : stepCheck 0 2432 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_14 : stepCheck 0 2434 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_15 : stepCheck 0 2435 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_16 : stepCheck 0 2436 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_19 : stepCheck 0 2439 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_1 : stepCheck 1 2421 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_2 : stepCheck 1 2422 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_4 : stepCheck 1 2424 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_5 : stepCheck 1 2425 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_6 : stepCheck 1 2426 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_7 : stepCheck 1 2427 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_8 : stepCheck 1 2428 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_9 : stepCheck 1 2429 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_10 : stepCheck 1 2430 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_11 : stepCheck 1 2431 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_12 : stepCheck 1 2432 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_13 : stepCheck 1 2433 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_14 : stepCheck 1 2434 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_15 : stepCheck 1 2435 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_16 : stepCheck 1 2436 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_17 : stepCheck 1 2437 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_18 : stepCheck 1 2438 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_19 : stepCheck 1 2439 := by
  left
  decide +kernel

private theorem checked17 (_h : ∀ k : Fin 285, residualCheck k) : stepBatch 121 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point17_0_0
  · exact point17_0_1
  · exact point17_0_2
  · exact point17_0_3
  · exact point17_0_4
  · exact point17_0_5
  · exact point17_0_6
  · exact point17_0_7
  · exact _h 110
  · exact point17_0_9
  · exact point17_0_10
  · exact point17_0_11
  · exact point17_0_12
  · exact _h 111
  · exact point17_0_14
  · exact point17_0_15
  · exact point17_0_16
  · exact _h 112
  · exact _h 113
  · exact point17_0_19
  · exact _h 114
  · exact point17_1_1
  · exact point17_1_2
  · exact _h 115
  · exact point17_1_4
  · exact point17_1_5
  · exact point17_1_6
  · exact point17_1_7
  · exact point17_1_8
  · exact point17_1_9
  · exact point17_1_10
  · exact point17_1_11
  · exact point17_1_12
  · exact point17_1_13
  · exact point17_1_14
  · exact point17_1_15
  · exact point17_1_16
  · exact point17_1_17
  · exact point17_1_18
  · exact point17_1_19

set_option maxHeartbeats 1600000 in
private theorem point18_0_0 : stepCheck 0 2560 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_2 : stepCheck 0 2562 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_3 : stepCheck 0 2563 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_4 : stepCheck 0 2564 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_5 : stepCheck 0 2565 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_6 : stepCheck 0 2566 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_7 : stepCheck 0 2567 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_8 : stepCheck 0 2568 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_9 : stepCheck 0 2569 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_10 : stepCheck 0 2570 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_12 : stepCheck 0 2572 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_13 : stepCheck 0 2573 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_14 : stepCheck 0 2574 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_15 : stepCheck 0 2575 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_16 : stepCheck 0 2576 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_17 : stepCheck 0 2577 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_18 : stepCheck 0 2578 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_0 : stepCheck 1 2560 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_1 : stepCheck 1 2561 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_2 : stepCheck 1 2562 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_3 : stepCheck 1 2563 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_4 : stepCheck 1 2564 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_5 : stepCheck 1 2565 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_7 : stepCheck 1 2567 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_10 : stepCheck 1 2570 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_11 : stepCheck 1 2571 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_12 : stepCheck 1 2572 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_15 : stepCheck 1 2575 := by
  left
  decide +kernel

private theorem checked18 (_h : ∀ k : Fin 285, residualCheck k) : stepBatch 128 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point18_0_0
  · exact _h 116
  · exact point18_0_2
  · exact point18_0_3
  · exact point18_0_4
  · exact point18_0_5
  · exact point18_0_6
  · exact point18_0_7
  · exact point18_0_8
  · exact point18_0_9
  · exact point18_0_10
  · exact _h 117
  · exact point18_0_12
  · exact point18_0_13
  · exact point18_0_14
  · exact point18_0_15
  · exact point18_0_16
  · exact point18_0_17
  · exact point18_0_18
  · exact _h 118
  · exact point18_1_0
  · exact point18_1_1
  · exact point18_1_2
  · exact point18_1_3
  · exact point18_1_4
  · exact point18_1_5
  · exact _h 119
  · exact point18_1_7
  · exact _h 120
  · exact _h 121
  · exact point18_1_10
  · exact point18_1_11
  · exact point18_1_12
  · exact _h 122
  · exact _h 123
  · exact point18_1_15
  · exact _h 124
  · exact _h 125
  · exact _h 126
  · exact _h 127

set_option maxHeartbeats 1600000 in
private theorem point19_0_1 : stepCheck 0 2701 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_2 : stepCheck 0 2702 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_3 : stepCheck 0 2703 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_5 : stepCheck 0 2705 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_6 : stepCheck 0 2706 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_7 : stepCheck 0 2707 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_8 : stepCheck 0 2708 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_9 : stepCheck 0 2709 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_10 : stepCheck 0 2710 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_11 : stepCheck 0 2711 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_12 : stepCheck 0 2712 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_13 : stepCheck 0 2713 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_16 : stepCheck 0 2716 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_18 : stepCheck 0 2718 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_19 : stepCheck 0 2719 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_2 : stepCheck 1 2702 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_3 : stepCheck 1 2703 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_4 : stepCheck 1 2704 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_5 : stepCheck 1 2705 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_6 : stepCheck 1 2706 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_7 : stepCheck 1 2707 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_8 : stepCheck 1 2708 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_9 : stepCheck 1 2709 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_10 : stepCheck 1 2710 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_11 : stepCheck 1 2711 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_13 : stepCheck 1 2713 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_14 : stepCheck 1 2714 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_15 : stepCheck 1 2715 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_16 : stepCheck 1 2716 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_17 : stepCheck 1 2717 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_18 : stepCheck 1 2718 := by
  left
  decide +kernel

private theorem checked19 (_h : ∀ k : Fin 285, residualCheck k) : stepBatch 135 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact _h 128
  · exact point19_0_1
  · exact point19_0_2
  · exact point19_0_3
  · exact _h 129
  · exact point19_0_5
  · exact point19_0_6
  · exact point19_0_7
  · exact point19_0_8
  · exact point19_0_9
  · exact point19_0_10
  · exact point19_0_11
  · exact point19_0_12
  · exact point19_0_13
  · exact _h 130
  · exact _h 131
  · exact point19_0_16
  · exact _h 132
  · exact point19_0_18
  · exact point19_0_19
  · exact _h 133
  · exact _h 134
  · exact point19_1_2
  · exact point19_1_3
  · exact point19_1_4
  · exact point19_1_5
  · exact point19_1_6
  · exact point19_1_7
  · exact point19_1_8
  · exact point19_1_9
  · exact point19_1_10
  · exact point19_1_11
  · exact _h 135
  · exact point19_1_13
  · exact point19_1_14
  · exact point19_1_15
  · exact point19_1_16
  · exact point19_1_17
  · exact point19_1_18
  · exact _h 136

set_option maxHeartbeats 1600000 in
private theorem point20_0_0 : stepCheck 0 2840 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_2 : stepCheck 0 2842 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_3 : stepCheck 0 2843 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_4 : stepCheck 0 2844 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_5 : stepCheck 0 2845 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_8 : stepCheck 0 2848 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_10 : stepCheck 0 2850 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_11 : stepCheck 0 2851 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_12 : stepCheck 0 2852 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_13 : stepCheck 0 2853 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_15 : stepCheck 0 2855 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_16 : stepCheck 0 2856 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_17 : stepCheck 0 2857 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_19 : stepCheck 0 2859 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_0 : stepCheck 1 2840 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_1 : stepCheck 1 2841 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_2 : stepCheck 1 2842 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_3 : stepCheck 1 2843 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_5 : stepCheck 1 2845 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_6 : stepCheck 1 2846 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_7 : stepCheck 1 2847 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_8 : stepCheck 1 2848 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_9 : stepCheck 1 2849 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_10 : stepCheck 1 2850 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_13 : stepCheck 1 2853 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_14 : stepCheck 1 2854 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_15 : stepCheck 1 2855 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_16 : stepCheck 1 2856 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_17 : stepCheck 1 2857 := by
  left
  decide +kernel

private theorem checked20 (_h : ∀ k : Fin 285, residualCheck k) : stepBatch 142 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point20_0_0
  · exact _h 137
  · exact point20_0_2
  · exact point20_0_3
  · exact point20_0_4
  · exact point20_0_5
  · exact _h 138
  · exact _h 139
  · exact point20_0_8
  · exact _h 140
  · exact point20_0_10
  · exact point20_0_11
  · exact point20_0_12
  · exact point20_0_13
  · exact _h 141
  · exact point20_0_15
  · exact point20_0_16
  · exact point20_0_17
  · exact _h 142
  · exact point20_0_19
  · exact point20_1_0
  · exact point20_1_1
  · exact point20_1_2
  · exact point20_1_3
  · exact _h 143
  · exact point20_1_5
  · exact point20_1_6
  · exact point20_1_7
  · exact point20_1_8
  · exact point20_1_9
  · exact point20_1_10
  · exact _h 144
  · exact _h 145
  · exact point20_1_13
  · exact point20_1_14
  · exact point20_1_15
  · exact point20_1_16
  · exact point20_1_17
  · exact _h 146
  · exact _h 147

set_option maxHeartbeats 1600000 in
private theorem point21_0_0 : stepCheck 0 2980 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_1 : stepCheck 0 2981 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_4 : stepCheck 0 2984 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_5 : stepCheck 0 2985 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_6 : stepCheck 0 2986 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_7 : stepCheck 0 2987 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_8 : stepCheck 0 2988 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_10 : stepCheck 0 2990 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_11 : stepCheck 0 2991 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_14 : stepCheck 0 2994 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_16 : stepCheck 0 2996 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_17 : stepCheck 0 2997 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_18 : stepCheck 0 2998 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_19 : stepCheck 0 2999 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_0 : stepCheck 1 2980 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_1 : stepCheck 1 2981 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_2 : stepCheck 1 2982 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_3 : stepCheck 1 2983 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_5 : stepCheck 1 2985 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_7 : stepCheck 1 2987 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_9 : stepCheck 1 2989 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_11 : stepCheck 1 2991 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_12 : stepCheck 1 2992 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_13 : stepCheck 1 2993 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_14 : stepCheck 1 2994 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_15 : stepCheck 1 2995 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_17 : stepCheck 1 2997 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_18 : stepCheck 1 2998 := by
  left
  decide +kernel

private theorem checked21 (_h : ∀ k : Fin 285, residualCheck k) : stepBatch 149 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point21_0_0
  · exact point21_0_1
  · exact _h 148
  · exact _h 149
  · exact point21_0_4
  · exact point21_0_5
  · exact point21_0_6
  · exact point21_0_7
  · exact point21_0_8
  · exact _h 150
  · exact point21_0_10
  · exact point21_0_11
  · exact _h 151
  · exact _h 152
  · exact point21_0_14
  · exact _h 153
  · exact point21_0_16
  · exact point21_0_17
  · exact point21_0_18
  · exact point21_0_19
  · exact point21_1_0
  · exact point21_1_1
  · exact point21_1_2
  · exact point21_1_3
  · exact _h 154
  · exact point21_1_5
  · exact _h 155
  · exact point21_1_7
  · exact _h 156
  · exact point21_1_9
  · exact _h 157
  · exact point21_1_11
  · exact point21_1_12
  · exact point21_1_13
  · exact point21_1_14
  · exact point21_1_15
  · exact _h 158
  · exact point21_1_17
  · exact point21_1_18
  · exact _h 159

set_option maxHeartbeats 1600000 in
private theorem point22_0_0 : stepCheck 0 3120 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_1 : stepCheck 0 3121 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_3 : stepCheck 0 3123 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_4 : stepCheck 0 3124 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_6 : stepCheck 0 3126 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_7 : stepCheck 0 3127 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_8 : stepCheck 0 3128 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_9 : stepCheck 0 3129 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_10 : stepCheck 0 3130 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_11 : stepCheck 0 3131 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_12 : stepCheck 0 3132 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_13 : stepCheck 0 3133 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_14 : stepCheck 0 3134 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_15 : stepCheck 0 3135 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_17 : stepCheck 0 3137 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_0 : stepCheck 1 3120 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_1 : stepCheck 1 3121 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_4 : stepCheck 1 3124 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_5 : stepCheck 1 3125 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_7 : stepCheck 1 3127 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_8 : stepCheck 1 3128 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_10 : stepCheck 1 3130 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_11 : stepCheck 1 3131 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_12 : stepCheck 1 3132 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_13 : stepCheck 1 3133 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_14 : stepCheck 1 3134 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_16 : stepCheck 1 3136 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_17 : stepCheck 1 3137 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_19 : stepCheck 1 3139 := by
  left
  decide +kernel

private theorem checked22 (_h : ∀ k : Fin 285, residualCheck k) : stepBatch 156 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point22_0_0
  · exact point22_0_1
  · exact _h 160
  · exact point22_0_3
  · exact point22_0_4
  · exact _h 161
  · exact point22_0_6
  · exact point22_0_7
  · exact point22_0_8
  · exact point22_0_9
  · exact point22_0_10
  · exact point22_0_11
  · exact point22_0_12
  · exact point22_0_13
  · exact point22_0_14
  · exact point22_0_15
  · exact _h 162
  · exact point22_0_17
  · exact _h 163
  · exact _h 164
  · exact point22_1_0
  · exact point22_1_1
  · exact _h 165
  · exact _h 166
  · exact point22_1_4
  · exact point22_1_5
  · exact _h 167
  · exact point22_1_7
  · exact point22_1_8
  · exact _h 168
  · exact point22_1_10
  · exact point22_1_11
  · exact point22_1_12
  · exact point22_1_13
  · exact point22_1_14
  · exact _h 169
  · exact point22_1_16
  · exact point22_1_17
  · exact _h 170
  · exact point22_1_19

set_option maxHeartbeats 1600000 in
private theorem point23_0_0 : stepCheck 0 3260 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_1 : stepCheck 0 3261 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_2 : stepCheck 0 3262 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_3 : stepCheck 0 3263 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_8 : stepCheck 0 3268 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_9 : stepCheck 0 3269 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_15 : stepCheck 0 3275 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_18 : stepCheck 0 3278 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_1 : stepCheck 1 3261 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_2 : stepCheck 1 3262 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_4 : stepCheck 1 3264 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_5 : stepCheck 1 3265 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_7 : stepCheck 1 3267 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_8 : stepCheck 1 3268 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_11 : stepCheck 1 3271 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_13 : stepCheck 1 3273 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_14 : stepCheck 1 3274 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_16 : stepCheck 1 3276 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_17 : stepCheck 1 3277 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_18 : stepCheck 1 3278 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_19 : stepCheck 1 3279 := by
  left
  decide +kernel

private theorem checked23 (_h : ∀ k : Fin 285, residualCheck k) : stepBatch 163 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point23_0_0
  · exact point23_0_1
  · exact point23_0_2
  · exact point23_0_3
  · exact _h 171
  · exact _h 172
  · exact _h 173
  · exact _h 174
  · exact point23_0_8
  · exact point23_0_9
  · exact _h 175
  · exact _h 176
  · exact _h 177
  · exact _h 178
  · exact _h 179
  · exact point23_0_15
  · exact _h 180
  · exact _h 181
  · exact point23_0_18
  · exact _h 182
  · exact _h 183
  · exact point23_1_1
  · exact point23_1_2
  · exact _h 184
  · exact point23_1_4
  · exact point23_1_5
  · exact _h 185
  · exact point23_1_7
  · exact point23_1_8
  · exact _h 186
  · exact _h 187
  · exact point23_1_11
  · exact _h 188
  · exact point23_1_13
  · exact point23_1_14
  · exact _h 189
  · exact point23_1_16
  · exact point23_1_17
  · exact point23_1_18
  · exact point23_1_19

set_option maxHeartbeats 1600000 in
private theorem point24_0_1 : stepCheck 0 3401 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_2 : stepCheck 0 3402 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_4 : stepCheck 0 3404 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_5 : stepCheck 0 3405 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_8 : stepCheck 0 3408 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_9 : stepCheck 0 3409 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_11 : stepCheck 0 3411 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_12 : stepCheck 0 3412 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_14 : stepCheck 0 3414 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_15 : stepCheck 0 3415 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_16 : stepCheck 0 3416 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_18 : stepCheck 0 3418 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_0 : stepCheck 1 3400 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_1 : stepCheck 1 3401 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_3 : stepCheck 1 3403 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_4 : stepCheck 1 3404 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_5 : stepCheck 1 3405 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_6 : stepCheck 1 3406 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_7 : stepCheck 1 3407 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_8 : stepCheck 1 3408 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_13 : stepCheck 1 3413 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_14 : stepCheck 1 3414 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_17 : stepCheck 1 3417 := by
  left
  decide +kernel

private theorem checked24 (_h : ∀ k : Fin 285, residualCheck k) : stepBatch 170 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact _h 190
  · exact point24_0_1
  · exact point24_0_2
  · exact _h 191
  · exact point24_0_4
  · exact point24_0_5
  · exact _h 192
  · exact _h 193
  · exact point24_0_8
  · exact point24_0_9
  · exact _h 194
  · exact point24_0_11
  · exact point24_0_12
  · exact _h 195
  · exact point24_0_14
  · exact point24_0_15
  · exact point24_0_16
  · exact _h 196
  · exact point24_0_18
  · exact _h 197
  · exact point24_1_0
  · exact point24_1_1
  · exact _h 198
  · exact point24_1_3
  · exact point24_1_4
  · exact point24_1_5
  · exact point24_1_6
  · exact point24_1_7
  · exact point24_1_8
  · exact _h 199
  · exact _h 200
  · exact _h 201
  · exact _h 202
  · exact point24_1_13
  · exact point24_1_14
  · exact _h 203
  · exact _h 204
  · exact point24_1_17
  · exact _h 205
  · exact _h 206

set_option maxHeartbeats 1600000 in
private theorem point25_0_1 : stepCheck 0 3541 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_4 : stepCheck 0 3544 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_7 : stepCheck 0 3547 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_9 : stepCheck 0 3549 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_10 : stepCheck 0 3550 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_11 : stepCheck 0 3551 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_12 : stepCheck 0 3552 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_14 : stepCheck 0 3554 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_18 : stepCheck 0 3558 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_0 : stepCheck 1 3540 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_3 : stepCheck 1 3543 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_6 : stepCheck 1 3546 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_8 : stepCheck 1 3548 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_11 : stepCheck 1 3551 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_12 : stepCheck 1 3552 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_13 : stepCheck 1 3553 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_14 : stepCheck 1 3554 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_15 : stepCheck 1 3555 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_16 : stepCheck 1 3556 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_17 : stepCheck 1 3557 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_18 : stepCheck 1 3558 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_19 : stepCheck 1 3559 := by
  left
  decide +kernel

private theorem checked25 (_h : ∀ k : Fin 285, residualCheck k) : stepBatch 177 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact _h 207
  · exact point25_0_1
  · exact _h 208
  · exact _h 209
  · exact point25_0_4
  · exact _h 210
  · exact _h 211
  · exact point25_0_7
  · exact _h 212
  · exact point25_0_9
  · exact point25_0_10
  · exact point25_0_11
  · exact point25_0_12
  · exact _h 213
  · exact point25_0_14
  · exact _h 214
  · exact _h 215
  · exact _h 216
  · exact point25_0_18
  · exact _h 217
  · exact point25_1_0
  · exact _h 218
  · exact _h 219
  · exact point25_1_3
  · exact _h 220
  · exact _h 221
  · exact point25_1_6
  · exact _h 222
  · exact point25_1_8
  · exact _h 223
  · exact _h 224
  · exact point25_1_11
  · exact point25_1_12
  · exact point25_1_13
  · exact point25_1_14
  · exact point25_1_15
  · exact point25_1_16
  · exact point25_1_17
  · exact point25_1_18
  · exact point25_1_19

set_option maxHeartbeats 1600000 in
private theorem point26_0_0 : stepCheck 0 3680 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_1 : stepCheck 0 3681 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_3 : stepCheck 0 3683 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_4 : stepCheck 0 3684 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_7 : stepCheck 0 3687 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_10 : stepCheck 0 3690 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_11 : stepCheck 0 3691 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_12 : stepCheck 0 3692 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_13 : stepCheck 0 3693 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_14 : stepCheck 0 3694 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_17 : stepCheck 0 3697 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_5 : stepCheck 1 3685 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_6 : stepCheck 1 3686 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_9 : stepCheck 1 3689 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_10 : stepCheck 1 3690 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_11 : stepCheck 1 3691 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_12 : stepCheck 1 3692 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_13 : stepCheck 1 3693 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_14 : stepCheck 1 3694 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_15 : stepCheck 1 3695 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_16 : stepCheck 1 3696 := by
  left
  decide +kernel

private theorem checked26 (_h : ∀ k : Fin 285, residualCheck k) : stepBatch 184 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point26_0_0
  · exact point26_0_1
  · exact _h 225
  · exact point26_0_3
  · exact point26_0_4
  · exact _h 226
  · exact _h 227
  · exact point26_0_7
  · exact _h 228
  · exact _h 229
  · exact point26_0_10
  · exact point26_0_11
  · exact point26_0_12
  · exact point26_0_13
  · exact point26_0_14
  · exact _h 230
  · exact _h 231
  · exact point26_0_17
  · exact _h 232
  · exact _h 233
  · exact _h 234
  · exact _h 235
  · exact _h 236
  · exact _h 237
  · exact _h 238
  · exact point26_1_5
  · exact point26_1_6
  · exact _h 239
  · exact _h 240
  · exact point26_1_9
  · exact point26_1_10
  · exact point26_1_11
  · exact point26_1_12
  · exact point26_1_13
  · exact point26_1_14
  · exact point26_1_15
  · exact point26_1_16
  · exact _h 241
  · exact _h 242
  · exact _h 243

set_option maxHeartbeats 1600000 in
private theorem point27_0_0 : stepCheck 0 3820 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_5 : stepCheck 0 3825 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_11 : stepCheck 0 3831 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_12 : stepCheck 0 3832 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_14 : stepCheck 0 3834 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_19 : stepCheck 0 3839 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_0 : stepCheck 1 3820 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_2 : stepCheck 1 3822 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_3 : stepCheck 1 3823 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_5 : stepCheck 1 3825 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_6 : stepCheck 1 3826 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_7 : stepCheck 1 3827 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_9 : stepCheck 1 3829 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_10 : stepCheck 1 3830 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_13 : stepCheck 1 3833 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_15 : stepCheck 1 3835 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_18 : stepCheck 1 3838 := by
  left
  decide +kernel

private theorem checked27 (_h : ∀ k : Fin 285, residualCheck k) : stepBatch 191 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point27_0_0
  · exact _h 244
  · exact _h 245
  · exact _h 246
  · exact _h 247
  · exact point27_0_5
  · exact _h 248
  · exact _h 249
  · exact _h 250
  · exact _h 251
  · exact _h 252
  · exact point27_0_11
  · exact point27_0_12
  · exact _h 253
  · exact point27_0_14
  · exact _h 254
  · exact _h 255
  · exact _h 256
  · exact _h 257
  · exact point27_0_19
  · exact point27_1_0
  · exact _h 258
  · exact point27_1_2
  · exact point27_1_3
  · exact _h 259
  · exact point27_1_5
  · exact point27_1_6
  · exact point27_1_7
  · exact _h 260
  · exact point27_1_9
  · exact point27_1_10
  · exact _h 261
  · exact _h 262
  · exact point27_1_13
  · exact _h 263
  · exact point27_1_15
  · exact _h 264
  · exact _h 265
  · exact point27_1_18
  · exact _h 266

set_option maxHeartbeats 1600000 in
private theorem point28_0_1 : stepCheck 0 3961 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_2 : stepCheck 0 3962 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_3 : stepCheck 0 3963 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_4 : stepCheck 0 3964 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_5 : stepCheck 0 3965 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_7 : stepCheck 0 3967 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_8 : stepCheck 0 3968 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_10 : stepCheck 0 3970 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_11 : stepCheck 0 3971 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_12 : stepCheck 0 3972 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_13 : stepCheck 0 3973 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_14 : stepCheck 0 3974 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_1 : stepCheck 1 3961 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_2 : stepCheck 1 3962 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_3 : stepCheck 1 3963 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_6 : stepCheck 1 3966 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_8 : stepCheck 1 3968 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_13 : stepCheck 1 3973 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_15 : stepCheck 1 3975 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_16 : stepCheck 1 3976 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_17 : stepCheck 1 3977 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_19 : stepCheck 1 3979 := by
  left
  decide +kernel

private theorem checked28 (_h : ∀ k : Fin 285, residualCheck k) : stepBatch 198 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact _h 267
  · exact point28_0_1
  · exact point28_0_2
  · exact point28_0_3
  · exact point28_0_4
  · exact point28_0_5
  · exact _h 268
  · exact point28_0_7
  · exact point28_0_8
  · exact _h 269
  · exact point28_0_10
  · exact point28_0_11
  · exact point28_0_12
  · exact point28_0_13
  · exact point28_0_14
  · exact _h 270
  · exact _h 271
  · exact _h 272
  · exact _h 273
  · exact _h 274
  · exact _h 275
  · exact point28_1_1
  · exact point28_1_2
  · exact point28_1_3
  · exact _h 276
  · exact _h 277
  · exact point28_1_6
  · exact _h 278
  · exact point28_1_8
  · exact _h 279
  · exact _h 280
  · exact _h 281
  · exact _h 282
  · exact point28_1_13
  · exact _h 283
  · exact point28_1_15
  · exact point28_1_16
  · exact point28_1_17
  · exact _h 284
  · exact point28_1_19

/-- The algebraic transitions leave precisely the explicit residual checks. -/
public theorem part2_of_residual (h : ∀ k : Fin 285, residualCheck k) (b : Fin 29) :
    stepBatch ⟨7 * b.val + 2, by omega⟩ := by
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

/-- Four independent residual certificates complete part 2. -/
public theorem part2_of_batches (h : ∀ g : Fin 4, residualBatch g) (b : Fin 29) :
    stepBatch ⟨7 * b.val + 2, by omega⟩ :=
  part2_of_residual (all_of_batches h) b

end Rudvalis.OrderCertificate.ForwardReduction.Part2Residual
