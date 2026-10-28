module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Reduction
import Mathlib.Tactic.FinCases

/-!
# Residual checks for Rudvalis level-0 transition part 1

Of the 1160 forward transitions in the 29 batches numbered 1 modulo 7,
877 follow by word reduction in the cyclic groups of orders 2 and 4.
This module proves these checks and reduces part 1 to the remaining 283
explicit transitions, grouped into four independent finite certificates.

The source witnesses are those of `OrderLevel0Data`, documented in
`OrderCertificate/GenerateChain.g`. The accompanying generator only selects
proof branches; the word reductions and final coverage are kernel-checked.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part1Residual
set_option maxRecDepth 30000
set_option Elab.async false

@[expose] public def target (k : Fin 283) : Fin 2 × Fin 4060 :=
  (if k.val < 141 then (if k.val < 70 then (if k.val < 35 then (if k.val < 17 then (if k.val < 8 then (if k.val < 4 then (if k.val < 2 then (if k.val < 1 then (1, 303) else (1, 317)) else (if k.val < 3 then (1, 440) else (0, 584))) else (if k.val < 6 then (if k.val < 5 then (0, 595) else (1, 581)) else (if k.val < 7 then (0, 728) else (1, 736)))) else (if k.val < 12 then (if k.val < 10 then (if k.val < 9 then (0, 860) else (0, 878)) else (if k.val < 11 then (1, 870) else (0, 1001))) else (if k.val < 14 then (if k.val < 13 then (0, 1013) else (1, 1004)) else (if k.val < 15 then (0, 1141) else (if k.val < 16 then (0, 1158) else (1, 1141)))))) else (if k.val < 26 then (if k.val < 21 then (if k.val < 19 then (if k.val < 18 then (1, 1147) else (1, 1151)) else (if k.val < 20 then (0, 1282) else (0, 1288))) else (if k.val < 23 then (if k.val < 22 then (0, 1291) else (0, 1293)) else (if k.val < 24 then (1, 1281) else (if k.val < 25 then (1, 1284) else (1, 1290))))) else (if k.val < 30 then (if k.val < 28 then (if k.val < 27 then (1, 1291) else (1, 1297)) else (if k.val < 29 then (0, 1425) else (0, 1434))) else (if k.val < 32 then (if k.val < 31 then (0, 1437) else (0, 1439)) else (if k.val < 33 then (1, 1426) else (if k.val < 34 then (1, 1432) else (0, 1560))))))) else (if k.val < 52 then (if k.val < 43 then (if k.val < 39 then (if k.val < 37 then (if k.val < 36 then (0, 1565) else (0, 1568)) else (if k.val < 38 then (0, 1571) else (1, 1560))) else (if k.val < 41 then (if k.val < 40 then (1, 1564) else (1, 1568)) else (if k.val < 42 then (1, 1573) else (0, 1700)))) else (if k.val < 47 then (if k.val < 45 then (if k.val < 44 then (0, 1708) else (0, 1709)) else (if k.val < 46 then (0, 1715) else (0, 1716))) else (if k.val < 49 then (if k.val < 48 then (0, 1718) else (1, 1701)) else (if k.val < 50 then (1, 1717) else (if k.val < 51 then (0, 1840) else (0, 1843)))))) else (if k.val < 61 then (if k.val < 56 then (if k.val < 54 then (if k.val < 53 then (0, 1852) else (0, 1853)) else (if k.val < 55 then (0, 1857) else (0, 1858))) else (if k.val < 58 then (if k.val < 57 then (0, 1859) else (1, 1841)) else (if k.val < 59 then (1, 1847) else (if k.val < 60 then (1, 1849) else (1, 1850))))) else (if k.val < 65 then (if k.val < 63 then (if k.val < 62 then (1, 1854) else (1, 1858)) else (if k.val < 64 then (0, 1981) else (0, 1982))) else (if k.val < 67 then (if k.val < 66 then (0, 1988) else (0, 1989)) else (if k.val < 68 then (0, 1996) else (if k.val < 69 then (0, 1997) else (0, 1999)))))))) else (if k.val < 105 then (if k.val < 87 then (if k.val < 78 then (if k.val < 74 then (if k.val < 72 then (if k.val < 71 then (1, 1980) else (1, 1985)) else (if k.val < 73 then (1, 1990) else (1, 1991))) else (if k.val < 76 then (if k.val < 75 then (1, 1993) else (1, 1994)) else (if k.val < 77 then (1, 1995) else (1, 1998)))) else (if k.val < 82 then (if k.val < 80 then (if k.val < 79 then (0, 2128) else (0, 2131)) else (if k.val < 81 then (0, 2134) else (0, 2138))) else (if k.val < 84 then (if k.val < 83 then (1, 2121) else (1, 2130)) else (if k.val < 85 then (1, 2132) else (if k.val < 86 then (1, 2133) else (1, 2135)))))) else (if k.val < 96 then (if k.val < 91 then (if k.val < 89 then (if k.val < 88 then (1, 2136) else (1, 2137)) else (if k.val < 90 then (0, 2266) else (0, 2267))) else (if k.val < 93 then (if k.val < 92 then (0, 2268) else (0, 2269)) else (if k.val < 94 then (0, 2274) else (if k.val < 95 then (0, 2276) else (0, 2277))))) else (if k.val < 100 then (if k.val < 98 then (if k.val < 97 then (1, 2264) else (1, 2267)) else (if k.val < 99 then (1, 2268) else (1, 2271))) else (if k.val < 102 then (if k.val < 101 then (1, 2272) else (0, 2401)) else (if k.val < 103 then (0, 2405) else (if k.val < 104 then (0, 2408) else (0, 2409))))))) else (if k.val < 123 then (if k.val < 114 then (if k.val < 109 then (if k.val < 107 then (if k.val < 106 then (0, 2414) else (1, 2400)) else (if k.val < 108 then (1, 2406) else (1, 2409))) else (if k.val < 111 then (if k.val < 110 then (1, 2411) else (1, 2414)) else (if k.val < 112 then (1, 2418) else (if k.val < 113 then (0, 2542) else (0, 2543))))) else (if k.val < 118 then (if k.val < 116 then (if k.val < 115 then (1, 2540) else (1, 2541)) else (if k.val < 117 then (1, 2543) else (1, 2544))) else (if k.val < 120 then (if k.val < 119 then (1, 2546) else (1, 2549)) else (if k.val < 121 then (1, 2555) else (if k.val < 122 then (1, 2557) else (1, 2558)))))) else (if k.val < 132 then (if k.val < 127 then (if k.val < 125 then (if k.val < 124 then (0, 2684) else (0, 2689)) else (if k.val < 126 then (0, 2692) else (0, 2695))) else (if k.val < 129 then (if k.val < 128 then (0, 2697) else (0, 2698)) else (if k.val < 130 then (1, 2682) else (if k.val < 131 then (1, 2686) else (1, 2688))))) else (if k.val < 136 then (if k.val < 134 then (if k.val < 133 then (1, 2692) else (1, 2694)) else (if k.val < 135 then (1, 2696) else (1, 2697))) else (if k.val < 138 then (if k.val < 137 then (0, 2821) else (0, 2829)) else (if k.val < 139 then (0, 2831) else (if k.val < 140 then (0, 2835) else (0, 2838))))))))) else (if k.val < 212 then (if k.val < 176 then (if k.val < 158 then (if k.val < 149 then (if k.val < 145 then (if k.val < 143 then (if k.val < 142 then (1, 2823) else (1, 2827)) else (if k.val < 144 then (1, 2828) else (1, 2833))) else (if k.val < 147 then (if k.val < 146 then (1, 2834) else (1, 2836)) else (if k.val < 148 then (1, 2837) else (0, 2962)))) else (if k.val < 153 then (if k.val < 151 then (if k.val < 150 then (0, 2966) else (0, 2970)) else (if k.val < 152 then (0, 2971) else (0, 2976))) else (if k.val < 155 then (if k.val < 154 then (0, 2977) else (0, 2978)) else (if k.val < 156 then (1, 2960) else (if k.val < 157 then (1, 2961) else (1, 2965)))))) else (if k.val < 167 then (if k.val < 162 then (if k.val < 160 then (if k.val < 159 then (1, 2971) else (1, 2975)) else (if k.val < 161 then (1, 2979) else (0, 3102))) else (if k.val < 164 then (if k.val < 163 then (0, 3105) else (0, 3106)) else (if k.val < 165 then (0, 3107) else (if k.val < 166 then (0, 3111) else (0, 3116))))) else (if k.val < 171 then (if k.val < 169 then (if k.val < 168 then (0, 3118) else (1, 3103)) else (if k.val < 170 then (1, 3105) else (1, 3108))) else (if k.val < 173 then (if k.val < 172 then (1, 3109) else (1, 3112)) else (if k.val < 174 then (1, 3113) else (if k.val < 175 then (1, 3114) else (0, 3241))))))) else (if k.val < 194 then (if k.val < 185 then (if k.val < 180 then (if k.val < 178 then (if k.val < 177 then (0, 3242) else (0, 3249)) else (if k.val < 179 then (0, 3252) else (0, 3257))) else (if k.val < 182 then (if k.val < 181 then (0, 3258) else (0, 3259)) else (if k.val < 183 then (1, 3240) else (if k.val < 184 then (1, 3241) else (1, 3244))))) else (if k.val < 189 then (if k.val < 187 then (if k.val < 186 then (1, 3247) else (1, 3250)) else (if k.val < 188 then (1, 3251) else (1, 3257))) else (if k.val < 191 then (if k.val < 190 then (1, 3258) else (0, 3382)) else (if k.val < 192 then (0, 3383) else (if k.val < 193 then (0, 3392) else (0, 3393)))))) else (if k.val < 203 then (if k.val < 198 then (if k.val < 196 then (if k.val < 195 then (0, 3395) else (0, 3397)) else (if k.val < 197 then (0, 3398) else (0, 3399))) else (if k.val < 200 then (if k.val < 199 then (1, 3381) else (1, 3384)) else (if k.val < 201 then (1, 3386) else (if k.val < 202 then (1, 3388) else (1, 3389))))) else (if k.val < 207 then (if k.val < 205 then (if k.val < 204 then (1, 3391) else (1, 3398)) else (if k.val < 206 then (0, 3522) else (0, 3523))) else (if k.val < 209 then (if k.val < 208 then (0, 3524) else (0, 3525)) else (if k.val < 210 then (0, 3528) else (if k.val < 211 then (0, 3532) else (0, 3537)))))))) else (if k.val < 247 then (if k.val < 229 then (if k.val < 220 then (if k.val < 216 then (if k.val < 214 then (if k.val < 213 then (0, 3538) else (1, 3523)) else (if k.val < 215 then (1, 3526) else (1, 3530))) else (if k.val < 218 then (if k.val < 217 then (1, 3533) else (1, 3535)) else (if k.val < 219 then (1, 3536) else (0, 3662)))) else (if k.val < 224 then (if k.val < 222 then (if k.val < 221 then (0, 3665) else (0, 3671)) else (if k.val < 223 then (0, 3675) else (0, 3677))) else (if k.val < 226 then (if k.val < 225 then (0, 3678) else (0, 3679)) else (if k.val < 227 then (1, 3660) else (if k.val < 228 then (1, 3663) else (1, 3664)))))) else (if k.val < 238 then (if k.val < 233 then (if k.val < 231 then (if k.val < 230 then (1, 3667) else (1, 3669)) else (if k.val < 232 then (1, 3670) else (1, 3673))) else (if k.val < 235 then (if k.val < 234 then (1, 3674) else (1, 3676)) else (if k.val < 236 then (1, 3677) else (if k.val < 237 then (1, 3679) else (0, 3800))))) else (if k.val < 242 then (if k.val < 240 then (if k.val < 239 then (0, 3801) else (0, 3805)) else (if k.val < 241 then (0, 3806) else (0, 3807))) else (if k.val < 244 then (if k.val < 243 then (0, 3808) else (0, 3812)) else (if k.val < 245 then (0, 3814) else (if k.val < 246 then (0, 3815) else (0, 3816))))))) else (if k.val < 265 then (if k.val < 256 then (if k.val < 251 then (if k.val < 249 then (if k.val < 248 then (0, 3817) else (0, 3818)) else (if k.val < 250 then (1, 3800) else (1, 3802))) else (if k.val < 253 then (if k.val < 252 then (1, 3803) else (1, 3807)) else (if k.val < 254 then (1, 3809) else (if k.val < 255 then (1, 3811) else (1, 3812))))) else (if k.val < 260 then (if k.val < 258 then (if k.val < 257 then (1, 3813) else (1, 3814)) else (if k.val < 259 then (1, 3817) else (0, 3940))) else (if k.val < 262 then (if k.val < 261 then (0, 3941) else (0, 3942)) else (if k.val < 263 then (0, 3946) else (if k.val < 264 then (0, 3947) else (0, 3949)))))) else (if k.val < 274 then (if k.val < 269 then (if k.val < 267 then (if k.val < 266 then (0, 3951) else (0, 3954)) else (if k.val < 268 then (0, 3955) else (0, 3956))) else (if k.val < 271 then (if k.val < 270 then (0, 3957) else (0, 3959)) else (if k.val < 272 then (1, 3940) else (if k.val < 273 then (1, 3943) else (1, 3944))))) else (if k.val < 278 then (if k.val < 276 then (if k.val < 275 then (1, 3945) else (1, 3946)) else (if k.val < 277 then (1, 3950) else (1, 3952))) else (if k.val < 280 then (if k.val < 279 then (1, 3953) else (1, 3956)) else (if k.val < 281 then (1, 3957) else (if k.val < 282 then (1, 3958) else (1, 3959))))))))))

@[expose] public def residualCheck (k : Fin 283) : Prop :=
  stepCheck (target k).1 (target k).2

/-- Groups 0, 1, 2 contain 71 transitions; group 3 contains 70. -/
@[expose] public def residualBatch (g : Fin 4) : Prop :=
  ∀ (s : Fin 71) (h : 71 * g.val + s.val < 283),
    residualCheck ⟨71 * g.val + s.val, h⟩

public theorem all_of_batches (h : ∀ g : Fin 4, residualBatch g) :
    ∀ k : Fin 283, residualCheck k := by
  intro k
  let g : Fin 4 := ⟨k.val / 71, by omega⟩
  let s : Fin 71 := ⟨k.val % 71, by omega⟩
  have hlt : 71 * g.val + s.val < 283 := by dsimp [g, s]; omega
  have hk : (⟨71 * g.val + s.val, hlt⟩ : Fin 283) = k := by
    apply Fin.ext
    dsimp [g, s]
    omega
  simpa only [hk] using h g s hlt

set_option maxHeartbeats 1600000 in
private theorem point0_0_0 : stepCheck 0 20 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_1 : stepCheck 0 21 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_2 : stepCheck 0 22 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_3 : stepCheck 0 23 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_4 : stepCheck 0 24 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_5 : stepCheck 0 25 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_6 : stepCheck 0 26 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_7 : stepCheck 0 27 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_8 : stepCheck 0 28 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_9 : stepCheck 0 29 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_10 : stepCheck 0 30 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_11 : stepCheck 0 31 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_12 : stepCheck 0 32 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_13 : stepCheck 0 33 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_14 : stepCheck 0 34 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_15 : stepCheck 0 35 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_16 : stepCheck 0 36 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_17 : stepCheck 0 37 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_18 : stepCheck 0 38 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_0_19 : stepCheck 0 39 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_0 : stepCheck 1 20 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_1 : stepCheck 1 21 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_2 : stepCheck 1 22 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_3 : stepCheck 1 23 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_4 : stepCheck 1 24 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_5 : stepCheck 1 25 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_6 : stepCheck 1 26 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_7 : stepCheck 1 27 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_8 : stepCheck 1 28 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_9 : stepCheck 1 29 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_10 : stepCheck 1 30 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_11 : stepCheck 1 31 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_12 : stepCheck 1 32 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_13 : stepCheck 1 33 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_14 : stepCheck 1 34 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_15 : stepCheck 1 35 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_16 : stepCheck 1 36 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_17 : stepCheck 1 37 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_18 : stepCheck 1 38 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point0_1_19 : stepCheck 1 39 := by
  left
  decide +kernel

private theorem checked0 (_h : ∀ k : Fin 283, residualCheck k) : stepBatch 1 := by
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
private theorem point1_0_0 : stepCheck 0 160 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_1 : stepCheck 0 161 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_2 : stepCheck 0 162 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_3 : stepCheck 0 163 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_4 : stepCheck 0 164 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_5 : stepCheck 0 165 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_6 : stepCheck 0 166 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_7 : stepCheck 0 167 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_8 : stepCheck 0 168 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_9 : stepCheck 0 169 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_10 : stepCheck 0 170 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_11 : stepCheck 0 171 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_12 : stepCheck 0 172 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_13 : stepCheck 0 173 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_14 : stepCheck 0 174 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_15 : stepCheck 0 175 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_16 : stepCheck 0 176 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_17 : stepCheck 0 177 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_18 : stepCheck 0 178 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_0_19 : stepCheck 0 179 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_0 : stepCheck 1 160 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_1 : stepCheck 1 161 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_2 : stepCheck 1 162 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_3 : stepCheck 1 163 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_4 : stepCheck 1 164 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_5 : stepCheck 1 165 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_6 : stepCheck 1 166 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_7 : stepCheck 1 167 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_8 : stepCheck 1 168 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_9 : stepCheck 1 169 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_10 : stepCheck 1 170 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_11 : stepCheck 1 171 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_12 : stepCheck 1 172 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_13 : stepCheck 1 173 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_14 : stepCheck 1 174 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_15 : stepCheck 1 175 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_16 : stepCheck 1 176 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_17 : stepCheck 1 177 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_18 : stepCheck 1 178 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point1_1_19 : stepCheck 1 179 := by
  left
  decide +kernel

private theorem checked1 (_h : ∀ k : Fin 283, residualCheck k) : stepBatch 8 := by
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
private theorem point2_0_0 : stepCheck 0 300 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_1 : stepCheck 0 301 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_2 : stepCheck 0 302 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_3 : stepCheck 0 303 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_4 : stepCheck 0 304 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_5 : stepCheck 0 305 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_6 : stepCheck 0 306 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_7 : stepCheck 0 307 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_8 : stepCheck 0 308 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_9 : stepCheck 0 309 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_10 : stepCheck 0 310 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_11 : stepCheck 0 311 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_12 : stepCheck 0 312 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_13 : stepCheck 0 313 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_14 : stepCheck 0 314 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_15 : stepCheck 0 315 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_16 : stepCheck 0 316 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_17 : stepCheck 0 317 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_18 : stepCheck 0 318 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_0_19 : stepCheck 0 319 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_0 : stepCheck 1 300 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_1 : stepCheck 1 301 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_2 : stepCheck 1 302 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_4 : stepCheck 1 304 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_5 : stepCheck 1 305 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_6 : stepCheck 1 306 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_7 : stepCheck 1 307 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_8 : stepCheck 1 308 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_9 : stepCheck 1 309 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_10 : stepCheck 1 310 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_11 : stepCheck 1 311 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_12 : stepCheck 1 312 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_13 : stepCheck 1 313 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_14 : stepCheck 1 314 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_15 : stepCheck 1 315 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_16 : stepCheck 1 316 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_18 : stepCheck 1 318 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point2_1_19 : stepCheck 1 319 := by
  left
  decide +kernel

private theorem checked2 (_h : ∀ k : Fin 283, residualCheck k) : stepBatch 15 := by
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
  · exact _h 0
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
  · exact _h 1
  · exact point2_1_18
  · exact point2_1_19

set_option maxHeartbeats 1600000 in
private theorem point3_0_0 : stepCheck 0 440 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_1 : stepCheck 0 441 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_2 : stepCheck 0 442 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_3 : stepCheck 0 443 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_4 : stepCheck 0 444 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_5 : stepCheck 0 445 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_6 : stepCheck 0 446 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_7 : stepCheck 0 447 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_8 : stepCheck 0 448 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_9 : stepCheck 0 449 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_10 : stepCheck 0 450 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_11 : stepCheck 0 451 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_12 : stepCheck 0 452 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_13 : stepCheck 0 453 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_14 : stepCheck 0 454 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_15 : stepCheck 0 455 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_16 : stepCheck 0 456 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_17 : stepCheck 0 457 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_18 : stepCheck 0 458 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_0_19 : stepCheck 0 459 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_1 : stepCheck 1 441 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_2 : stepCheck 1 442 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_3 : stepCheck 1 443 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_4 : stepCheck 1 444 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_5 : stepCheck 1 445 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_6 : stepCheck 1 446 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_7 : stepCheck 1 447 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_8 : stepCheck 1 448 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_9 : stepCheck 1 449 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_10 : stepCheck 1 450 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_11 : stepCheck 1 451 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_12 : stepCheck 1 452 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_13 : stepCheck 1 453 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_14 : stepCheck 1 454 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_15 : stepCheck 1 455 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_16 : stepCheck 1 456 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_17 : stepCheck 1 457 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_18 : stepCheck 1 458 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point3_1_19 : stepCheck 1 459 := by
  left
  decide +kernel

private theorem checked3 (_h : ∀ k : Fin 283, residualCheck k) : stepBatch 22 := by
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
  · exact _h 2
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
  · exact point3_1_14
  · exact point3_1_15
  · exact point3_1_16
  · exact point3_1_17
  · exact point3_1_18
  · exact point3_1_19

set_option maxHeartbeats 1600000 in
private theorem point4_0_0 : stepCheck 0 580 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_1 : stepCheck 0 581 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_2 : stepCheck 0 582 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_3 : stepCheck 0 583 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_5 : stepCheck 0 585 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_6 : stepCheck 0 586 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_7 : stepCheck 0 587 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_8 : stepCheck 0 588 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_9 : stepCheck 0 589 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_10 : stepCheck 0 590 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_11 : stepCheck 0 591 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_12 : stepCheck 0 592 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_13 : stepCheck 0 593 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_14 : stepCheck 0 594 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_16 : stepCheck 0 596 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_17 : stepCheck 0 597 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_18 : stepCheck 0 598 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_0_19 : stepCheck 0 599 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_0 : stepCheck 1 580 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_2 : stepCheck 1 582 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_3 : stepCheck 1 583 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_4 : stepCheck 1 584 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_5 : stepCheck 1 585 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_6 : stepCheck 1 586 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_7 : stepCheck 1 587 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_8 : stepCheck 1 588 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_9 : stepCheck 1 589 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_10 : stepCheck 1 590 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_11 : stepCheck 1 591 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_12 : stepCheck 1 592 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_13 : stepCheck 1 593 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_14 : stepCheck 1 594 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_15 : stepCheck 1 595 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_16 : stepCheck 1 596 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_17 : stepCheck 1 597 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_18 : stepCheck 1 598 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point4_1_19 : stepCheck 1 599 := by
  left
  decide +kernel

private theorem checked4 (_h : ∀ k : Fin 283, residualCheck k) : stepBatch 29 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point4_0_0
  · exact point4_0_1
  · exact point4_0_2
  · exact point4_0_3
  · exact _h 3
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
  · exact _h 4
  · exact point4_0_16
  · exact point4_0_17
  · exact point4_0_18
  · exact point4_0_19
  · exact point4_1_0
  · exact _h 5
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
private theorem point5_0_0 : stepCheck 0 720 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_1 : stepCheck 0 721 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_2 : stepCheck 0 722 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_3 : stepCheck 0 723 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_4 : stepCheck 0 724 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_5 : stepCheck 0 725 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_6 : stepCheck 0 726 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_7 : stepCheck 0 727 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_9 : stepCheck 0 729 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_10 : stepCheck 0 730 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_11 : stepCheck 0 731 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_12 : stepCheck 0 732 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_13 : stepCheck 0 733 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_14 : stepCheck 0 734 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_15 : stepCheck 0 735 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_16 : stepCheck 0 736 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_17 : stepCheck 0 737 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_18 : stepCheck 0 738 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_0_19 : stepCheck 0 739 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_0 : stepCheck 1 720 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_1 : stepCheck 1 721 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_2 : stepCheck 1 722 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_3 : stepCheck 1 723 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_4 : stepCheck 1 724 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_5 : stepCheck 1 725 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_6 : stepCheck 1 726 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_7 : stepCheck 1 727 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_8 : stepCheck 1 728 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_9 : stepCheck 1 729 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_10 : stepCheck 1 730 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_11 : stepCheck 1 731 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_12 : stepCheck 1 732 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_13 : stepCheck 1 733 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_14 : stepCheck 1 734 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_15 : stepCheck 1 735 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_17 : stepCheck 1 737 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_18 : stepCheck 1 738 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point5_1_19 : stepCheck 1 739 := by
  left
  decide +kernel

private theorem checked5 (_h : ∀ k : Fin 283, residualCheck k) : stepBatch 36 := by
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
  · exact _h 6
  · exact point5_0_9
  · exact point5_0_10
  · exact point5_0_11
  · exact point5_0_12
  · exact point5_0_13
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
  · exact _h 7
  · exact point5_1_17
  · exact point5_1_18
  · exact point5_1_19

set_option maxHeartbeats 1600000 in
private theorem point6_0_1 : stepCheck 0 861 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_2 : stepCheck 0 862 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_3 : stepCheck 0 863 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_4 : stepCheck 0 864 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_5 : stepCheck 0 865 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_6 : stepCheck 0 866 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_7 : stepCheck 0 867 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_8 : stepCheck 0 868 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_9 : stepCheck 0 869 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_10 : stepCheck 0 870 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_11 : stepCheck 0 871 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_12 : stepCheck 0 872 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_13 : stepCheck 0 873 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_14 : stepCheck 0 874 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_15 : stepCheck 0 875 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_16 : stepCheck 0 876 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_17 : stepCheck 0 877 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_19 : stepCheck 0 879 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_0 : stepCheck 1 860 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_1 : stepCheck 1 861 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_2 : stepCheck 1 862 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_3 : stepCheck 1 863 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_4 : stepCheck 1 864 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_5 : stepCheck 1 865 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_6 : stepCheck 1 866 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_7 : stepCheck 1 867 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_8 : stepCheck 1 868 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_9 : stepCheck 1 869 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_11 : stepCheck 1 871 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_12 : stepCheck 1 872 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_13 : stepCheck 1 873 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_14 : stepCheck 1 874 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_15 : stepCheck 1 875 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_16 : stepCheck 1 876 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_17 : stepCheck 1 877 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_18 : stepCheck 1 878 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_19 : stepCheck 1 879 := by
  left
  decide +kernel

private theorem checked6 (_h : ∀ k : Fin 283, residualCheck k) : stepBatch 43 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact _h 8
  · exact point6_0_1
  · exact point6_0_2
  · exact point6_0_3
  · exact point6_0_4
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
  · exact _h 9
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
  · exact _h 10
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
private theorem point7_0_0 : stepCheck 0 1000 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_2 : stepCheck 0 1002 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_3 : stepCheck 0 1003 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_4 : stepCheck 0 1004 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_5 : stepCheck 0 1005 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_6 : stepCheck 0 1006 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_7 : stepCheck 0 1007 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_8 : stepCheck 0 1008 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_9 : stepCheck 0 1009 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_10 : stepCheck 0 1010 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_11 : stepCheck 0 1011 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_12 : stepCheck 0 1012 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_14 : stepCheck 0 1014 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_15 : stepCheck 0 1015 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_16 : stepCheck 0 1016 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_17 : stepCheck 0 1017 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_18 : stepCheck 0 1018 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_19 : stepCheck 0 1019 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_0 : stepCheck 1 1000 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_1 : stepCheck 1 1001 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_2 : stepCheck 1 1002 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_3 : stepCheck 1 1003 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_5 : stepCheck 1 1005 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_6 : stepCheck 1 1006 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_7 : stepCheck 1 1007 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_8 : stepCheck 1 1008 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_9 : stepCheck 1 1009 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_10 : stepCheck 1 1010 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_11 : stepCheck 1 1011 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_12 : stepCheck 1 1012 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_13 : stepCheck 1 1013 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_14 : stepCheck 1 1014 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_15 : stepCheck 1 1015 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_16 : stepCheck 1 1016 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_17 : stepCheck 1 1017 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_18 : stepCheck 1 1018 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_19 : stepCheck 1 1019 := by
  left
  decide +kernel

private theorem checked7 (_h : ∀ k : Fin 283, residualCheck k) : stepBatch 50 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point7_0_0
  · exact _h 11
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
  · exact _h 12
  · exact point7_0_14
  · exact point7_0_15
  · exact point7_0_16
  · exact point7_0_17
  · exact point7_0_18
  · exact point7_0_19
  · exact point7_1_0
  · exact point7_1_1
  · exact point7_1_2
  · exact point7_1_3
  · exact _h 13
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
private theorem point8_0_0 : stepCheck 0 1140 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_2 : stepCheck 0 1142 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_3 : stepCheck 0 1143 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_4 : stepCheck 0 1144 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_5 : stepCheck 0 1145 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_6 : stepCheck 0 1146 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_7 : stepCheck 0 1147 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_8 : stepCheck 0 1148 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_9 : stepCheck 0 1149 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_10 : stepCheck 0 1150 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_11 : stepCheck 0 1151 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_12 : stepCheck 0 1152 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_13 : stepCheck 0 1153 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_14 : stepCheck 0 1154 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_15 : stepCheck 0 1155 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_16 : stepCheck 0 1156 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_17 : stepCheck 0 1157 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_19 : stepCheck 0 1159 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_0 : stepCheck 1 1140 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_2 : stepCheck 1 1142 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_3 : stepCheck 1 1143 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_4 : stepCheck 1 1144 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_5 : stepCheck 1 1145 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_6 : stepCheck 1 1146 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_8 : stepCheck 1 1148 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_9 : stepCheck 1 1149 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_10 : stepCheck 1 1150 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_12 : stepCheck 1 1152 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_13 : stepCheck 1 1153 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_14 : stepCheck 1 1154 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_15 : stepCheck 1 1155 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_16 : stepCheck 1 1156 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_17 : stepCheck 1 1157 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_18 : stepCheck 1 1158 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_19 : stepCheck 1 1159 := by
  left
  decide +kernel

private theorem checked8 (_h : ∀ k : Fin 283, residualCheck k) : stepBatch 57 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point8_0_0
  · exact _h 14
  · exact point8_0_2
  · exact point8_0_3
  · exact point8_0_4
  · exact point8_0_5
  · exact point8_0_6
  · exact point8_0_7
  · exact point8_0_8
  · exact point8_0_9
  · exact point8_0_10
  · exact point8_0_11
  · exact point8_0_12
  · exact point8_0_13
  · exact point8_0_14
  · exact point8_0_15
  · exact point8_0_16
  · exact point8_0_17
  · exact _h 15
  · exact point8_0_19
  · exact point8_1_0
  · exact _h 16
  · exact point8_1_2
  · exact point8_1_3
  · exact point8_1_4
  · exact point8_1_5
  · exact point8_1_6
  · exact _h 17
  · exact point8_1_8
  · exact point8_1_9
  · exact point8_1_10
  · exact _h 18
  · exact point8_1_12
  · exact point8_1_13
  · exact point8_1_14
  · exact point8_1_15
  · exact point8_1_16
  · exact point8_1_17
  · exact point8_1_18
  · exact point8_1_19

set_option maxHeartbeats 1600000 in
private theorem point9_0_0 : stepCheck 0 1280 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_1 : stepCheck 0 1281 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_3 : stepCheck 0 1283 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_4 : stepCheck 0 1284 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_5 : stepCheck 0 1285 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_6 : stepCheck 0 1286 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_7 : stepCheck 0 1287 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_9 : stepCheck 0 1289 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_10 : stepCheck 0 1290 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_12 : stepCheck 0 1292 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_14 : stepCheck 0 1294 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_15 : stepCheck 0 1295 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_16 : stepCheck 0 1296 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_17 : stepCheck 0 1297 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_18 : stepCheck 0 1298 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_19 : stepCheck 0 1299 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_0 : stepCheck 1 1280 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_2 : stepCheck 1 1282 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_3 : stepCheck 1 1283 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_5 : stepCheck 1 1285 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_6 : stepCheck 1 1286 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_7 : stepCheck 1 1287 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_8 : stepCheck 1 1288 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_9 : stepCheck 1 1289 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_12 : stepCheck 1 1292 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_13 : stepCheck 1 1293 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_14 : stepCheck 1 1294 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_15 : stepCheck 1 1295 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_16 : stepCheck 1 1296 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_18 : stepCheck 1 1298 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_19 : stepCheck 1 1299 := by
  left
  decide +kernel

private theorem checked9 (_h : ∀ k : Fin 283, residualCheck k) : stepBatch 64 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point9_0_0
  · exact point9_0_1
  · exact _h 19
  · exact point9_0_3
  · exact point9_0_4
  · exact point9_0_5
  · exact point9_0_6
  · exact point9_0_7
  · exact _h 20
  · exact point9_0_9
  · exact point9_0_10
  · exact _h 21
  · exact point9_0_12
  · exact _h 22
  · exact point9_0_14
  · exact point9_0_15
  · exact point9_0_16
  · exact point9_0_17
  · exact point9_0_18
  · exact point9_0_19
  · exact point9_1_0
  · exact _h 23
  · exact point9_1_2
  · exact point9_1_3
  · exact _h 24
  · exact point9_1_5
  · exact point9_1_6
  · exact point9_1_7
  · exact point9_1_8
  · exact point9_1_9
  · exact _h 25
  · exact _h 26
  · exact point9_1_12
  · exact point9_1_13
  · exact point9_1_14
  · exact point9_1_15
  · exact point9_1_16
  · exact _h 27
  · exact point9_1_18
  · exact point9_1_19

set_option maxHeartbeats 1600000 in
private theorem point10_0_0 : stepCheck 0 1420 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_1 : stepCheck 0 1421 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_2 : stepCheck 0 1422 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_3 : stepCheck 0 1423 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_4 : stepCheck 0 1424 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_6 : stepCheck 0 1426 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_7 : stepCheck 0 1427 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_8 : stepCheck 0 1428 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_9 : stepCheck 0 1429 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_10 : stepCheck 0 1430 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_11 : stepCheck 0 1431 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_12 : stepCheck 0 1432 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_13 : stepCheck 0 1433 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_15 : stepCheck 0 1435 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_16 : stepCheck 0 1436 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_18 : stepCheck 0 1438 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_0 : stepCheck 1 1420 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_1 : stepCheck 1 1421 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_2 : stepCheck 1 1422 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_3 : stepCheck 1 1423 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_4 : stepCheck 1 1424 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_5 : stepCheck 1 1425 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_7 : stepCheck 1 1427 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_8 : stepCheck 1 1428 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_9 : stepCheck 1 1429 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_10 : stepCheck 1 1430 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_11 : stepCheck 1 1431 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_13 : stepCheck 1 1433 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_14 : stepCheck 1 1434 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_15 : stepCheck 1 1435 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_16 : stepCheck 1 1436 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_17 : stepCheck 1 1437 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_18 : stepCheck 1 1438 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_19 : stepCheck 1 1439 := by
  left
  decide +kernel

private theorem checked10 (_h : ∀ k : Fin 283, residualCheck k) : stepBatch 71 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point10_0_0
  · exact point10_0_1
  · exact point10_0_2
  · exact point10_0_3
  · exact point10_0_4
  · exact _h 28
  · exact point10_0_6
  · exact point10_0_7
  · exact point10_0_8
  · exact point10_0_9
  · exact point10_0_10
  · exact point10_0_11
  · exact point10_0_12
  · exact point10_0_13
  · exact _h 29
  · exact point10_0_15
  · exact point10_0_16
  · exact _h 30
  · exact point10_0_18
  · exact _h 31
  · exact point10_1_0
  · exact point10_1_1
  · exact point10_1_2
  · exact point10_1_3
  · exact point10_1_4
  · exact point10_1_5
  · exact _h 32
  · exact point10_1_7
  · exact point10_1_8
  · exact point10_1_9
  · exact point10_1_10
  · exact point10_1_11
  · exact _h 33
  · exact point10_1_13
  · exact point10_1_14
  · exact point10_1_15
  · exact point10_1_16
  · exact point10_1_17
  · exact point10_1_18
  · exact point10_1_19

set_option maxHeartbeats 1600000 in
private theorem point11_0_1 : stepCheck 0 1561 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_2 : stepCheck 0 1562 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_3 : stepCheck 0 1563 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_4 : stepCheck 0 1564 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_6 : stepCheck 0 1566 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_7 : stepCheck 0 1567 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_9 : stepCheck 0 1569 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_10 : stepCheck 0 1570 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_12 : stepCheck 0 1572 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_13 : stepCheck 0 1573 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_14 : stepCheck 0 1574 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_15 : stepCheck 0 1575 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_16 : stepCheck 0 1576 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_17 : stepCheck 0 1577 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_18 : stepCheck 0 1578 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_19 : stepCheck 0 1579 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_1 : stepCheck 1 1561 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_2 : stepCheck 1 1562 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_3 : stepCheck 1 1563 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_5 : stepCheck 1 1565 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_6 : stepCheck 1 1566 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_7 : stepCheck 1 1567 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_9 : stepCheck 1 1569 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_10 : stepCheck 1 1570 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_11 : stepCheck 1 1571 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_12 : stepCheck 1 1572 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_14 : stepCheck 1 1574 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_15 : stepCheck 1 1575 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_16 : stepCheck 1 1576 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_17 : stepCheck 1 1577 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_18 : stepCheck 1 1578 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_19 : stepCheck 1 1579 := by
  left
  decide +kernel

private theorem checked11 (_h : ∀ k : Fin 283, residualCheck k) : stepBatch 78 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact _h 34
  · exact point11_0_1
  · exact point11_0_2
  · exact point11_0_3
  · exact point11_0_4
  · exact _h 35
  · exact point11_0_6
  · exact point11_0_7
  · exact _h 36
  · exact point11_0_9
  · exact point11_0_10
  · exact _h 37
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
  · exact _h 39
  · exact point11_1_5
  · exact point11_1_6
  · exact point11_1_7
  · exact _h 40
  · exact point11_1_9
  · exact point11_1_10
  · exact point11_1_11
  · exact point11_1_12
  · exact _h 41
  · exact point11_1_14
  · exact point11_1_15
  · exact point11_1_16
  · exact point11_1_17
  · exact point11_1_18
  · exact point11_1_19

set_option maxHeartbeats 1600000 in
private theorem point12_0_1 : stepCheck 0 1701 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_2 : stepCheck 0 1702 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_3 : stepCheck 0 1703 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_4 : stepCheck 0 1704 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_5 : stepCheck 0 1705 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_6 : stepCheck 0 1706 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_7 : stepCheck 0 1707 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_10 : stepCheck 0 1710 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_11 : stepCheck 0 1711 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_12 : stepCheck 0 1712 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_13 : stepCheck 0 1713 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_14 : stepCheck 0 1714 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_17 : stepCheck 0 1717 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_19 : stepCheck 0 1719 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_0 : stepCheck 1 1700 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_2 : stepCheck 1 1702 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_3 : stepCheck 1 1703 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_4 : stepCheck 1 1704 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_5 : stepCheck 1 1705 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_6 : stepCheck 1 1706 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_7 : stepCheck 1 1707 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_8 : stepCheck 1 1708 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_9 : stepCheck 1 1709 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_10 : stepCheck 1 1710 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_11 : stepCheck 1 1711 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_12 : stepCheck 1 1712 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_13 : stepCheck 1 1713 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_14 : stepCheck 1 1714 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_15 : stepCheck 1 1715 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_16 : stepCheck 1 1716 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_18 : stepCheck 1 1718 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_19 : stepCheck 1 1719 := by
  left
  decide +kernel

private theorem checked12 (_h : ∀ k : Fin 283, residualCheck k) : stepBatch 85 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact _h 42
  · exact point12_0_1
  · exact point12_0_2
  · exact point12_0_3
  · exact point12_0_4
  · exact point12_0_5
  · exact point12_0_6
  · exact point12_0_7
  · exact _h 43
  · exact _h 44
  · exact point12_0_10
  · exact point12_0_11
  · exact point12_0_12
  · exact point12_0_13
  · exact point12_0_14
  · exact _h 45
  · exact _h 46
  · exact point12_0_17
  · exact _h 47
  · exact point12_0_19
  · exact point12_1_0
  · exact _h 48
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
  · exact point12_1_16
  · exact _h 49
  · exact point12_1_18
  · exact point12_1_19

set_option maxHeartbeats 1600000 in
private theorem point13_0_1 : stepCheck 0 1841 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_2 : stepCheck 0 1842 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_4 : stepCheck 0 1844 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_5 : stepCheck 0 1845 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_6 : stepCheck 0 1846 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_7 : stepCheck 0 1847 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_8 : stepCheck 0 1848 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_9 : stepCheck 0 1849 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_10 : stepCheck 0 1850 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_11 : stepCheck 0 1851 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_14 : stepCheck 0 1854 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_15 : stepCheck 0 1855 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_16 : stepCheck 0 1856 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_0 : stepCheck 1 1840 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_2 : stepCheck 1 1842 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_3 : stepCheck 1 1843 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_4 : stepCheck 1 1844 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_5 : stepCheck 1 1845 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_6 : stepCheck 1 1846 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_8 : stepCheck 1 1848 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_11 : stepCheck 1 1851 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_12 : stepCheck 1 1852 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_13 : stepCheck 1 1853 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_15 : stepCheck 1 1855 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_16 : stepCheck 1 1856 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_17 : stepCheck 1 1857 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_19 : stepCheck 1 1859 := by
  left
  decide +kernel

private theorem checked13 (_h : ∀ k : Fin 283, residualCheck k) : stepBatch 92 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact _h 50
  · exact point13_0_1
  · exact point13_0_2
  · exact _h 51
  · exact point13_0_4
  · exact point13_0_5
  · exact point13_0_6
  · exact point13_0_7
  · exact point13_0_8
  · exact point13_0_9
  · exact point13_0_10
  · exact point13_0_11
  · exact _h 52
  · exact _h 53
  · exact point13_0_14
  · exact point13_0_15
  · exact point13_0_16
  · exact _h 54
  · exact _h 55
  · exact _h 56
  · exact point13_1_0
  · exact _h 57
  · exact point13_1_2
  · exact point13_1_3
  · exact point13_1_4
  · exact point13_1_5
  · exact point13_1_6
  · exact _h 58
  · exact point13_1_8
  · exact _h 59
  · exact _h 60
  · exact point13_1_11
  · exact point13_1_12
  · exact point13_1_13
  · exact _h 61
  · exact point13_1_15
  · exact point13_1_16
  · exact point13_1_17
  · exact _h 62
  · exact point13_1_19

set_option maxHeartbeats 1600000 in
private theorem point14_0_0 : stepCheck 0 1980 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_3 : stepCheck 0 1983 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_4 : stepCheck 0 1984 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_5 : stepCheck 0 1985 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_6 : stepCheck 0 1986 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_7 : stepCheck 0 1987 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_10 : stepCheck 0 1990 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_11 : stepCheck 0 1991 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_12 : stepCheck 0 1992 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_13 : stepCheck 0 1993 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_14 : stepCheck 0 1994 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_15 : stepCheck 0 1995 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_18 : stepCheck 0 1998 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_1 : stepCheck 1 1981 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_2 : stepCheck 1 1982 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_3 : stepCheck 1 1983 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_4 : stepCheck 1 1984 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_6 : stepCheck 1 1986 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_7 : stepCheck 1 1987 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_8 : stepCheck 1 1988 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_9 : stepCheck 1 1989 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_12 : stepCheck 1 1992 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_16 : stepCheck 1 1996 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_17 : stepCheck 1 1997 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_19 : stepCheck 1 1999 := by
  left
  decide +kernel

private theorem checked14 (_h : ∀ k : Fin 283, residualCheck k) : stepBatch 99 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point14_0_0
  · exact _h 63
  · exact _h 64
  · exact point14_0_3
  · exact point14_0_4
  · exact point14_0_5
  · exact point14_0_6
  · exact point14_0_7
  · exact _h 65
  · exact _h 66
  · exact point14_0_10
  · exact point14_0_11
  · exact point14_0_12
  · exact point14_0_13
  · exact point14_0_14
  · exact point14_0_15
  · exact _h 67
  · exact _h 68
  · exact point14_0_18
  · exact _h 69
  · exact _h 70
  · exact point14_1_1
  · exact point14_1_2
  · exact point14_1_3
  · exact point14_1_4
  · exact _h 71
  · exact point14_1_6
  · exact point14_1_7
  · exact point14_1_8
  · exact point14_1_9
  · exact _h 72
  · exact _h 73
  · exact point14_1_12
  · exact _h 74
  · exact _h 75
  · exact _h 76
  · exact point14_1_16
  · exact point14_1_17
  · exact _h 77
  · exact point14_1_19

set_option maxHeartbeats 1600000 in
private theorem point15_0_0 : stepCheck 0 2120 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_1 : stepCheck 0 2121 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_2 : stepCheck 0 2122 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_3 : stepCheck 0 2123 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_4 : stepCheck 0 2124 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_5 : stepCheck 0 2125 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_6 : stepCheck 0 2126 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_7 : stepCheck 0 2127 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_9 : stepCheck 0 2129 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_10 : stepCheck 0 2130 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_12 : stepCheck 0 2132 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_13 : stepCheck 0 2133 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_15 : stepCheck 0 2135 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_16 : stepCheck 0 2136 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_17 : stepCheck 0 2137 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_19 : stepCheck 0 2139 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_0 : stepCheck 1 2120 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_2 : stepCheck 1 2122 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_3 : stepCheck 1 2123 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_4 : stepCheck 1 2124 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_5 : stepCheck 1 2125 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_6 : stepCheck 1 2126 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_7 : stepCheck 1 2127 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_8 : stepCheck 1 2128 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_9 : stepCheck 1 2129 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_11 : stepCheck 1 2131 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_14 : stepCheck 1 2134 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_18 : stepCheck 1 2138 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_19 : stepCheck 1 2139 := by
  left
  decide +kernel

private theorem checked15 (_h : ∀ k : Fin 283, residualCheck k) : stepBatch 106 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point15_0_0
  · exact point15_0_1
  · exact point15_0_2
  · exact point15_0_3
  · exact point15_0_4
  · exact point15_0_5
  · exact point15_0_6
  · exact point15_0_7
  · exact _h 78
  · exact point15_0_9
  · exact point15_0_10
  · exact _h 79
  · exact point15_0_12
  · exact point15_0_13
  · exact _h 80
  · exact point15_0_15
  · exact point15_0_16
  · exact point15_0_17
  · exact _h 81
  · exact point15_0_19
  · exact point15_1_0
  · exact _h 82
  · exact point15_1_2
  · exact point15_1_3
  · exact point15_1_4
  · exact point15_1_5
  · exact point15_1_6
  · exact point15_1_7
  · exact point15_1_8
  · exact point15_1_9
  · exact _h 83
  · exact point15_1_11
  · exact _h 84
  · exact _h 85
  · exact point15_1_14
  · exact _h 86
  · exact _h 87
  · exact _h 88
  · exact point15_1_18
  · exact point15_1_19

set_option maxHeartbeats 1600000 in
private theorem point16_0_0 : stepCheck 0 2260 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_1 : stepCheck 0 2261 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_2 : stepCheck 0 2262 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_3 : stepCheck 0 2263 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_4 : stepCheck 0 2264 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_5 : stepCheck 0 2265 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_10 : stepCheck 0 2270 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_11 : stepCheck 0 2271 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_12 : stepCheck 0 2272 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_13 : stepCheck 0 2273 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_15 : stepCheck 0 2275 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_18 : stepCheck 0 2278 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_19 : stepCheck 0 2279 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_0 : stepCheck 1 2260 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_1 : stepCheck 1 2261 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_2 : stepCheck 1 2262 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_3 : stepCheck 1 2263 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_5 : stepCheck 1 2265 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_6 : stepCheck 1 2266 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_9 : stepCheck 1 2269 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_10 : stepCheck 1 2270 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_13 : stepCheck 1 2273 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_14 : stepCheck 1 2274 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_15 : stepCheck 1 2275 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_16 : stepCheck 1 2276 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_17 : stepCheck 1 2277 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_18 : stepCheck 1 2278 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_19 : stepCheck 1 2279 := by
  left
  decide +kernel

private theorem checked16 (_h : ∀ k : Fin 283, residualCheck k) : stepBatch 113 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point16_0_0
  · exact point16_0_1
  · exact point16_0_2
  · exact point16_0_3
  · exact point16_0_4
  · exact point16_0_5
  · exact _h 89
  · exact _h 90
  · exact _h 91
  · exact _h 92
  · exact point16_0_10
  · exact point16_0_11
  · exact point16_0_12
  · exact point16_0_13
  · exact _h 93
  · exact point16_0_15
  · exact _h 94
  · exact _h 95
  · exact point16_0_18
  · exact point16_0_19
  · exact point16_1_0
  · exact point16_1_1
  · exact point16_1_2
  · exact point16_1_3
  · exact _h 96
  · exact point16_1_5
  · exact point16_1_6
  · exact _h 97
  · exact _h 98
  · exact point16_1_9
  · exact point16_1_10
  · exact _h 99
  · exact _h 100
  · exact point16_1_13
  · exact point16_1_14
  · exact point16_1_15
  · exact point16_1_16
  · exact point16_1_17
  · exact point16_1_18
  · exact point16_1_19

set_option maxHeartbeats 1600000 in
private theorem point17_0_0 : stepCheck 0 2400 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_2 : stepCheck 0 2402 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_3 : stepCheck 0 2403 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_4 : stepCheck 0 2404 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_6 : stepCheck 0 2406 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_7 : stepCheck 0 2407 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_10 : stepCheck 0 2410 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_11 : stepCheck 0 2411 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_12 : stepCheck 0 2412 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_13 : stepCheck 0 2413 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_15 : stepCheck 0 2415 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_16 : stepCheck 0 2416 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_17 : stepCheck 0 2417 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_18 : stepCheck 0 2418 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_19 : stepCheck 0 2419 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_1 : stepCheck 1 2401 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_2 : stepCheck 1 2402 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_3 : stepCheck 1 2403 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_4 : stepCheck 1 2404 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_5 : stepCheck 1 2405 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_7 : stepCheck 1 2407 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_8 : stepCheck 1 2408 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_10 : stepCheck 1 2410 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_12 : stepCheck 1 2412 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_13 : stepCheck 1 2413 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_15 : stepCheck 1 2415 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_16 : stepCheck 1 2416 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_17 : stepCheck 1 2417 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_19 : stepCheck 1 2419 := by
  left
  decide +kernel

private theorem checked17 (_h : ∀ k : Fin 283, residualCheck k) : stepBatch 120 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point17_0_0
  · exact _h 101
  · exact point17_0_2
  · exact point17_0_3
  · exact point17_0_4
  · exact _h 102
  · exact point17_0_6
  · exact point17_0_7
  · exact _h 103
  · exact _h 104
  · exact point17_0_10
  · exact point17_0_11
  · exact point17_0_12
  · exact point17_0_13
  · exact _h 105
  · exact point17_0_15
  · exact point17_0_16
  · exact point17_0_17
  · exact point17_0_18
  · exact point17_0_19
  · exact _h 106
  · exact point17_1_1
  · exact point17_1_2
  · exact point17_1_3
  · exact point17_1_4
  · exact point17_1_5
  · exact _h 107
  · exact point17_1_7
  · exact point17_1_8
  · exact _h 108
  · exact point17_1_10
  · exact _h 109
  · exact point17_1_12
  · exact point17_1_13
  · exact _h 110
  · exact point17_1_15
  · exact point17_1_16
  · exact point17_1_17
  · exact _h 111
  · exact point17_1_19

set_option maxHeartbeats 1600000 in
private theorem point18_0_0 : stepCheck 0 2540 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_1 : stepCheck 0 2541 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_4 : stepCheck 0 2544 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_5 : stepCheck 0 2545 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_6 : stepCheck 0 2546 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_7 : stepCheck 0 2547 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_8 : stepCheck 0 2548 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_9 : stepCheck 0 2549 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_10 : stepCheck 0 2550 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_11 : stepCheck 0 2551 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_12 : stepCheck 0 2552 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_13 : stepCheck 0 2553 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_14 : stepCheck 0 2554 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_15 : stepCheck 0 2555 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_16 : stepCheck 0 2556 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_17 : stepCheck 0 2557 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_18 : stepCheck 0 2558 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_19 : stepCheck 0 2559 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_2 : stepCheck 1 2542 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_5 : stepCheck 1 2545 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_7 : stepCheck 1 2547 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_8 : stepCheck 1 2548 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_10 : stepCheck 1 2550 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_11 : stepCheck 1 2551 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_12 : stepCheck 1 2552 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_13 : stepCheck 1 2553 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_14 : stepCheck 1 2554 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_16 : stepCheck 1 2556 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_19 : stepCheck 1 2559 := by
  left
  decide +kernel

private theorem checked18 (_h : ∀ k : Fin 283, residualCheck k) : stepBatch 127 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point18_0_0
  · exact point18_0_1
  · exact _h 112
  · exact _h 113
  · exact point18_0_4
  · exact point18_0_5
  · exact point18_0_6
  · exact point18_0_7
  · exact point18_0_8
  · exact point18_0_9
  · exact point18_0_10
  · exact point18_0_11
  · exact point18_0_12
  · exact point18_0_13
  · exact point18_0_14
  · exact point18_0_15
  · exact point18_0_16
  · exact point18_0_17
  · exact point18_0_18
  · exact point18_0_19
  · exact _h 114
  · exact _h 115
  · exact point18_1_2
  · exact _h 116
  · exact _h 117
  · exact point18_1_5
  · exact _h 118
  · exact point18_1_7
  · exact point18_1_8
  · exact _h 119
  · exact point18_1_10
  · exact point18_1_11
  · exact point18_1_12
  · exact point18_1_13
  · exact point18_1_14
  · exact _h 120
  · exact point18_1_16
  · exact _h 121
  · exact _h 122
  · exact point18_1_19

set_option maxHeartbeats 1600000 in
private theorem point19_0_0 : stepCheck 0 2680 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_1 : stepCheck 0 2681 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_2 : stepCheck 0 2682 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_3 : stepCheck 0 2683 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_5 : stepCheck 0 2685 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_6 : stepCheck 0 2686 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_7 : stepCheck 0 2687 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_8 : stepCheck 0 2688 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_10 : stepCheck 0 2690 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_11 : stepCheck 0 2691 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_13 : stepCheck 0 2693 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_14 : stepCheck 0 2694 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_16 : stepCheck 0 2696 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_19 : stepCheck 0 2699 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_0 : stepCheck 1 2680 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_1 : stepCheck 1 2681 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_3 : stepCheck 1 2683 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_4 : stepCheck 1 2684 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_5 : stepCheck 1 2685 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_7 : stepCheck 1 2687 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_9 : stepCheck 1 2689 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_10 : stepCheck 1 2690 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_11 : stepCheck 1 2691 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_13 : stepCheck 1 2693 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_15 : stepCheck 1 2695 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_18 : stepCheck 1 2698 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_19 : stepCheck 1 2699 := by
  left
  decide +kernel

private theorem checked19 (_h : ∀ k : Fin 283, residualCheck k) : stepBatch 134 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point19_0_0
  · exact point19_0_1
  · exact point19_0_2
  · exact point19_0_3
  · exact _h 123
  · exact point19_0_5
  · exact point19_0_6
  · exact point19_0_7
  · exact point19_0_8
  · exact _h 124
  · exact point19_0_10
  · exact point19_0_11
  · exact _h 125
  · exact point19_0_13
  · exact point19_0_14
  · exact _h 126
  · exact point19_0_16
  · exact _h 127
  · exact _h 128
  · exact point19_0_19
  · exact point19_1_0
  · exact point19_1_1
  · exact _h 129
  · exact point19_1_3
  · exact point19_1_4
  · exact point19_1_5
  · exact _h 130
  · exact point19_1_7
  · exact _h 131
  · exact point19_1_9
  · exact point19_1_10
  · exact point19_1_11
  · exact _h 132
  · exact point19_1_13
  · exact _h 133
  · exact point19_1_15
  · exact _h 134
  · exact _h 135
  · exact point19_1_18
  · exact point19_1_19

set_option maxHeartbeats 1600000 in
private theorem point20_0_0 : stepCheck 0 2820 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_2 : stepCheck 0 2822 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_3 : stepCheck 0 2823 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_4 : stepCheck 0 2824 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_5 : stepCheck 0 2825 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_6 : stepCheck 0 2826 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_7 : stepCheck 0 2827 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_8 : stepCheck 0 2828 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_10 : stepCheck 0 2830 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_12 : stepCheck 0 2832 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_13 : stepCheck 0 2833 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_14 : stepCheck 0 2834 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_16 : stepCheck 0 2836 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_17 : stepCheck 0 2837 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_19 : stepCheck 0 2839 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_0 : stepCheck 1 2820 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_1 : stepCheck 1 2821 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_2 : stepCheck 1 2822 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_4 : stepCheck 1 2824 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_5 : stepCheck 1 2825 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_6 : stepCheck 1 2826 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_9 : stepCheck 1 2829 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_10 : stepCheck 1 2830 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_11 : stepCheck 1 2831 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_12 : stepCheck 1 2832 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_15 : stepCheck 1 2835 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_18 : stepCheck 1 2838 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_19 : stepCheck 1 2839 := by
  left
  decide +kernel

private theorem checked20 (_h : ∀ k : Fin 283, residualCheck k) : stepBatch 141 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point20_0_0
  · exact _h 136
  · exact point20_0_2
  · exact point20_0_3
  · exact point20_0_4
  · exact point20_0_5
  · exact point20_0_6
  · exact point20_0_7
  · exact point20_0_8
  · exact _h 137
  · exact point20_0_10
  · exact _h 138
  · exact point20_0_12
  · exact point20_0_13
  · exact point20_0_14
  · exact _h 139
  · exact point20_0_16
  · exact point20_0_17
  · exact _h 140
  · exact point20_0_19
  · exact point20_1_0
  · exact point20_1_1
  · exact point20_1_2
  · exact _h 141
  · exact point20_1_4
  · exact point20_1_5
  · exact point20_1_6
  · exact _h 142
  · exact _h 143
  · exact point20_1_9
  · exact point20_1_10
  · exact point20_1_11
  · exact point20_1_12
  · exact _h 144
  · exact _h 145
  · exact point20_1_15
  · exact _h 146
  · exact _h 147
  · exact point20_1_18
  · exact point20_1_19

set_option maxHeartbeats 1600000 in
private theorem point21_0_0 : stepCheck 0 2960 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_1 : stepCheck 0 2961 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_3 : stepCheck 0 2963 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_4 : stepCheck 0 2964 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_5 : stepCheck 0 2965 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_7 : stepCheck 0 2967 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_8 : stepCheck 0 2968 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_9 : stepCheck 0 2969 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_12 : stepCheck 0 2972 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_13 : stepCheck 0 2973 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_14 : stepCheck 0 2974 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_15 : stepCheck 0 2975 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_19 : stepCheck 0 2979 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_2 : stepCheck 1 2962 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_3 : stepCheck 1 2963 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_4 : stepCheck 1 2964 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_6 : stepCheck 1 2966 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_7 : stepCheck 1 2967 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_8 : stepCheck 1 2968 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_9 : stepCheck 1 2969 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_10 : stepCheck 1 2970 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_12 : stepCheck 1 2972 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_13 : stepCheck 1 2973 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_14 : stepCheck 1 2974 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_16 : stepCheck 1 2976 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_17 : stepCheck 1 2977 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_18 : stepCheck 1 2978 := by
  left
  decide +kernel

private theorem checked21 (_h : ∀ k : Fin 283, residualCheck k) : stepBatch 148 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point21_0_0
  · exact point21_0_1
  · exact _h 148
  · exact point21_0_3
  · exact point21_0_4
  · exact point21_0_5
  · exact _h 149
  · exact point21_0_7
  · exact point21_0_8
  · exact point21_0_9
  · exact _h 150
  · exact _h 151
  · exact point21_0_12
  · exact point21_0_13
  · exact point21_0_14
  · exact point21_0_15
  · exact _h 152
  · exact _h 153
  · exact _h 154
  · exact point21_0_19
  · exact _h 155
  · exact _h 156
  · exact point21_1_2
  · exact point21_1_3
  · exact point21_1_4
  · exact _h 157
  · exact point21_1_6
  · exact point21_1_7
  · exact point21_1_8
  · exact point21_1_9
  · exact point21_1_10
  · exact _h 158
  · exact point21_1_12
  · exact point21_1_13
  · exact point21_1_14
  · exact _h 159
  · exact point21_1_16
  · exact point21_1_17
  · exact point21_1_18
  · exact _h 160

set_option maxHeartbeats 1600000 in
private theorem point22_0_0 : stepCheck 0 3100 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_1 : stepCheck 0 3101 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_3 : stepCheck 0 3103 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_4 : stepCheck 0 3104 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_8 : stepCheck 0 3108 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_9 : stepCheck 0 3109 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_10 : stepCheck 0 3110 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_12 : stepCheck 0 3112 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_13 : stepCheck 0 3113 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_14 : stepCheck 0 3114 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_15 : stepCheck 0 3115 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_17 : stepCheck 0 3117 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_19 : stepCheck 0 3119 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_0 : stepCheck 1 3100 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_1 : stepCheck 1 3101 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_2 : stepCheck 1 3102 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_4 : stepCheck 1 3104 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_6 : stepCheck 1 3106 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_7 : stepCheck 1 3107 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_10 : stepCheck 1 3110 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_11 : stepCheck 1 3111 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_15 : stepCheck 1 3115 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_16 : stepCheck 1 3116 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_17 : stepCheck 1 3117 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_18 : stepCheck 1 3118 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_19 : stepCheck 1 3119 := by
  left
  decide +kernel

private theorem checked22 (_h : ∀ k : Fin 283, residualCheck k) : stepBatch 155 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point22_0_0
  · exact point22_0_1
  · exact _h 161
  · exact point22_0_3
  · exact point22_0_4
  · exact _h 162
  · exact _h 163
  · exact _h 164
  · exact point22_0_8
  · exact point22_0_9
  · exact point22_0_10
  · exact _h 165
  · exact point22_0_12
  · exact point22_0_13
  · exact point22_0_14
  · exact point22_0_15
  · exact _h 166
  · exact point22_0_17
  · exact _h 167
  · exact point22_0_19
  · exact point22_1_0
  · exact point22_1_1
  · exact point22_1_2
  · exact _h 168
  · exact point22_1_4
  · exact _h 169
  · exact point22_1_6
  · exact point22_1_7
  · exact _h 170
  · exact _h 171
  · exact point22_1_10
  · exact point22_1_11
  · exact _h 172
  · exact _h 173
  · exact _h 174
  · exact point22_1_15
  · exact point22_1_16
  · exact point22_1_17
  · exact point22_1_18
  · exact point22_1_19

set_option maxHeartbeats 1600000 in
private theorem point23_0_0 : stepCheck 0 3240 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_3 : stepCheck 0 3243 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_4 : stepCheck 0 3244 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_5 : stepCheck 0 3245 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_6 : stepCheck 0 3246 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_7 : stepCheck 0 3247 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_8 : stepCheck 0 3248 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_10 : stepCheck 0 3250 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_11 : stepCheck 0 3251 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_13 : stepCheck 0 3253 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_14 : stepCheck 0 3254 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_15 : stepCheck 0 3255 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_16 : stepCheck 0 3256 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_2 : stepCheck 1 3242 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_3 : stepCheck 1 3243 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_5 : stepCheck 1 3245 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_6 : stepCheck 1 3246 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_8 : stepCheck 1 3248 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_9 : stepCheck 1 3249 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_12 : stepCheck 1 3252 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_13 : stepCheck 1 3253 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_14 : stepCheck 1 3254 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_15 : stepCheck 1 3255 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_16 : stepCheck 1 3256 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_19 : stepCheck 1 3259 := by
  left
  decide +kernel

private theorem checked23 (_h : ∀ k : Fin 283, residualCheck k) : stepBatch 162 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point23_0_0
  · exact _h 175
  · exact _h 176
  · exact point23_0_3
  · exact point23_0_4
  · exact point23_0_5
  · exact point23_0_6
  · exact point23_0_7
  · exact point23_0_8
  · exact _h 177
  · exact point23_0_10
  · exact point23_0_11
  · exact _h 178
  · exact point23_0_13
  · exact point23_0_14
  · exact point23_0_15
  · exact point23_0_16
  · exact _h 179
  · exact _h 180
  · exact _h 181
  · exact _h 182
  · exact _h 183
  · exact point23_1_2
  · exact point23_1_3
  · exact _h 184
  · exact point23_1_5
  · exact point23_1_6
  · exact _h 185
  · exact point23_1_8
  · exact point23_1_9
  · exact _h 186
  · exact _h 187
  · exact point23_1_12
  · exact point23_1_13
  · exact point23_1_14
  · exact point23_1_15
  · exact point23_1_16
  · exact _h 188
  · exact _h 189
  · exact point23_1_19

set_option maxHeartbeats 1600000 in
private theorem point24_0_0 : stepCheck 0 3380 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_1 : stepCheck 0 3381 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_4 : stepCheck 0 3384 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_5 : stepCheck 0 3385 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_6 : stepCheck 0 3386 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_7 : stepCheck 0 3387 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_8 : stepCheck 0 3388 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_9 : stepCheck 0 3389 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_10 : stepCheck 0 3390 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_11 : stepCheck 0 3391 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_14 : stepCheck 0 3394 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_16 : stepCheck 0 3396 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_0 : stepCheck 1 3380 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_2 : stepCheck 1 3382 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_3 : stepCheck 1 3383 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_5 : stepCheck 1 3385 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_7 : stepCheck 1 3387 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_10 : stepCheck 1 3390 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_12 : stepCheck 1 3392 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_13 : stepCheck 1 3393 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_14 : stepCheck 1 3394 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_15 : stepCheck 1 3395 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_16 : stepCheck 1 3396 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_17 : stepCheck 1 3397 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_19 : stepCheck 1 3399 := by
  left
  decide +kernel

private theorem checked24 (_h : ∀ k : Fin 283, residualCheck k) : stepBatch 169 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point24_0_0
  · exact point24_0_1
  · exact _h 190
  · exact _h 191
  · exact point24_0_4
  · exact point24_0_5
  · exact point24_0_6
  · exact point24_0_7
  · exact point24_0_8
  · exact point24_0_9
  · exact point24_0_10
  · exact point24_0_11
  · exact _h 192
  · exact _h 193
  · exact point24_0_14
  · exact _h 194
  · exact point24_0_16
  · exact _h 195
  · exact _h 196
  · exact _h 197
  · exact point24_1_0
  · exact _h 198
  · exact point24_1_2
  · exact point24_1_3
  · exact _h 199
  · exact point24_1_5
  · exact _h 200
  · exact point24_1_7
  · exact _h 201
  · exact _h 202
  · exact point24_1_10
  · exact _h 203
  · exact point24_1_12
  · exact point24_1_13
  · exact point24_1_14
  · exact point24_1_15
  · exact point24_1_16
  · exact point24_1_17
  · exact _h 204
  · exact point24_1_19

set_option maxHeartbeats 1600000 in
private theorem point25_0_0 : stepCheck 0 3520 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_1 : stepCheck 0 3521 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_6 : stepCheck 0 3526 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_7 : stepCheck 0 3527 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_9 : stepCheck 0 3529 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_10 : stepCheck 0 3530 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_11 : stepCheck 0 3531 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_13 : stepCheck 0 3533 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_14 : stepCheck 0 3534 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_15 : stepCheck 0 3535 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_16 : stepCheck 0 3536 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_19 : stepCheck 0 3539 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_0 : stepCheck 1 3520 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_1 : stepCheck 1 3521 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_2 : stepCheck 1 3522 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_4 : stepCheck 1 3524 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_5 : stepCheck 1 3525 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_7 : stepCheck 1 3527 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_8 : stepCheck 1 3528 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_9 : stepCheck 1 3529 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_11 : stepCheck 1 3531 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_12 : stepCheck 1 3532 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_14 : stepCheck 1 3534 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_17 : stepCheck 1 3537 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_18 : stepCheck 1 3538 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_19 : stepCheck 1 3539 := by
  left
  decide +kernel

private theorem checked25 (_h : ∀ k : Fin 283, residualCheck k) : stepBatch 176 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point25_0_0
  · exact point25_0_1
  · exact _h 205
  · exact _h 206
  · exact _h 207
  · exact _h 208
  · exact point25_0_6
  · exact point25_0_7
  · exact _h 209
  · exact point25_0_9
  · exact point25_0_10
  · exact point25_0_11
  · exact _h 210
  · exact point25_0_13
  · exact point25_0_14
  · exact point25_0_15
  · exact point25_0_16
  · exact _h 211
  · exact _h 212
  · exact point25_0_19
  · exact point25_1_0
  · exact point25_1_1
  · exact point25_1_2
  · exact _h 213
  · exact point25_1_4
  · exact point25_1_5
  · exact _h 214
  · exact point25_1_7
  · exact point25_1_8
  · exact point25_1_9
  · exact _h 215
  · exact point25_1_11
  · exact point25_1_12
  · exact _h 216
  · exact point25_1_14
  · exact _h 217
  · exact _h 218
  · exact point25_1_17
  · exact point25_1_18
  · exact point25_1_19

set_option maxHeartbeats 1600000 in
private theorem point26_0_0 : stepCheck 0 3660 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_1 : stepCheck 0 3661 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_3 : stepCheck 0 3663 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_4 : stepCheck 0 3664 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_6 : stepCheck 0 3666 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_7 : stepCheck 0 3667 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_8 : stepCheck 0 3668 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_9 : stepCheck 0 3669 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_10 : stepCheck 0 3670 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_12 : stepCheck 0 3672 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_13 : stepCheck 0 3673 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_14 : stepCheck 0 3674 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_16 : stepCheck 0 3676 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_1 : stepCheck 1 3661 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_2 : stepCheck 1 3662 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_5 : stepCheck 1 3665 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_6 : stepCheck 1 3666 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_8 : stepCheck 1 3668 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_11 : stepCheck 1 3671 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_12 : stepCheck 1 3672 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_15 : stepCheck 1 3675 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_18 : stepCheck 1 3678 := by
  left
  decide +kernel

private theorem checked26 (_h : ∀ k : Fin 283, residualCheck k) : stepBatch 183 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point26_0_0
  · exact point26_0_1
  · exact _h 219
  · exact point26_0_3
  · exact point26_0_4
  · exact _h 220
  · exact point26_0_6
  · exact point26_0_7
  · exact point26_0_8
  · exact point26_0_9
  · exact point26_0_10
  · exact _h 221
  · exact point26_0_12
  · exact point26_0_13
  · exact point26_0_14
  · exact _h 222
  · exact point26_0_16
  · exact _h 223
  · exact _h 224
  · exact _h 225
  · exact _h 226
  · exact point26_1_1
  · exact point26_1_2
  · exact _h 227
  · exact _h 228
  · exact point26_1_5
  · exact point26_1_6
  · exact _h 229
  · exact point26_1_8
  · exact _h 230
  · exact _h 231
  · exact point26_1_11
  · exact point26_1_12
  · exact _h 232
  · exact _h 233
  · exact point26_1_15
  · exact _h 234
  · exact _h 235
  · exact point26_1_18
  · exact _h 236

set_option maxHeartbeats 1600000 in
private theorem point27_0_2 : stepCheck 0 3802 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_3 : stepCheck 0 3803 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_4 : stepCheck 0 3804 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_9 : stepCheck 0 3809 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_10 : stepCheck 0 3810 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_11 : stepCheck 0 3811 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_13 : stepCheck 0 3813 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_19 : stepCheck 0 3819 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_1 : stepCheck 1 3801 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_4 : stepCheck 1 3804 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_5 : stepCheck 1 3805 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_6 : stepCheck 1 3806 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_8 : stepCheck 1 3808 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_10 : stepCheck 1 3810 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_15 : stepCheck 1 3815 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_16 : stepCheck 1 3816 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_18 : stepCheck 1 3818 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_19 : stepCheck 1 3819 := by
  left
  decide +kernel

private theorem checked27 (_h : ∀ k : Fin 283, residualCheck k) : stepBatch 190 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact _h 237
  · exact _h 238
  · exact point27_0_2
  · exact point27_0_3
  · exact point27_0_4
  · exact _h 239
  · exact _h 240
  · exact _h 241
  · exact _h 242
  · exact point27_0_9
  · exact point27_0_10
  · exact point27_0_11
  · exact _h 243
  · exact point27_0_13
  · exact _h 244
  · exact _h 245
  · exact _h 246
  · exact _h 247
  · exact _h 248
  · exact point27_0_19
  · exact _h 249
  · exact point27_1_1
  · exact _h 250
  · exact _h 251
  · exact point27_1_4
  · exact point27_1_5
  · exact point27_1_6
  · exact _h 252
  · exact point27_1_8
  · exact _h 253
  · exact point27_1_10
  · exact _h 254
  · exact _h 255
  · exact _h 256
  · exact _h 257
  · exact point27_1_15
  · exact point27_1_16
  · exact _h 258
  · exact point27_1_18
  · exact point27_1_19

set_option maxHeartbeats 1600000 in
private theorem point28_0_3 : stepCheck 0 3943 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_4 : stepCheck 0 3944 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_5 : stepCheck 0 3945 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_8 : stepCheck 0 3948 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_10 : stepCheck 0 3950 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_12 : stepCheck 0 3952 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_13 : stepCheck 0 3953 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_18 : stepCheck 0 3958 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_1 : stepCheck 1 3941 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_2 : stepCheck 1 3942 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_7 : stepCheck 1 3947 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_8 : stepCheck 1 3948 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_9 : stepCheck 1 3949 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_11 : stepCheck 1 3951 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_14 : stepCheck 1 3954 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_15 : stepCheck 1 3955 := by
  left
  decide +kernel

private theorem checked28 (_h : ∀ k : Fin 283, residualCheck k) : stepBatch 197 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact _h 259
  · exact _h 260
  · exact _h 261
  · exact point28_0_3
  · exact point28_0_4
  · exact point28_0_5
  · exact _h 262
  · exact _h 263
  · exact point28_0_8
  · exact _h 264
  · exact point28_0_10
  · exact _h 265
  · exact point28_0_12
  · exact point28_0_13
  · exact _h 266
  · exact _h 267
  · exact _h 268
  · exact _h 269
  · exact point28_0_18
  · exact _h 270
  · exact _h 271
  · exact point28_1_1
  · exact point28_1_2
  · exact _h 272
  · exact _h 273
  · exact _h 274
  · exact _h 275
  · exact point28_1_7
  · exact point28_1_8
  · exact point28_1_9
  · exact _h 276
  · exact point28_1_11
  · exact _h 277
  · exact _h 278
  · exact point28_1_14
  · exact point28_1_15
  · exact _h 279
  · exact _h 280
  · exact _h 281
  · exact _h 282

/-- The algebraic transitions leave precisely the explicit residual checks. -/
public theorem part1_of_residual (h : ∀ k : Fin 283, residualCheck k) (b : Fin 29) :
    stepBatch ⟨7 * b.val + 1, by omega⟩ := by
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

/-- Four independent residual certificates complete part 1. -/
public theorem part1_of_batches (h : ∀ g : Fin 4, residualBatch g) (b : Fin 29) :
    stepBatch ⟨7 * b.val + 1, by omega⟩ :=
  part1_of_residual (all_of_batches h) b

end Rudvalis.OrderCertificate.ForwardReduction.Part1Residual
