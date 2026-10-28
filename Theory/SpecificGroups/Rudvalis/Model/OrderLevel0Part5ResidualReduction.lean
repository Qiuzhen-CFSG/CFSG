module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Batch0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Batch1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Batch2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Batch3
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Batch4
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part5Batch5
import Mathlib.Tactic.FinCases

/-!
# Residual checks for Rudvalis level-0 transition part 5

The first six batches are certified by the imported batch modules.
Of the remaining 920 transitions, 645 follow by word reduction in the cyclic
groups of orders 2 and 4. This module proves these checks and reduces part 5
to 275 explicit transitions, grouped into four independent certificates.

The source witnesses are those of `OrderLevel0Data`, documented in
`OrderCertificate/GenerateChain.g`. The accompanying generator only selects
proof branches; the word reductions and final coverage are kernel-checked.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual
set_option maxRecDepth 30000
set_option Elab.async false

@[expose] public def target (k : Fin 275) : Fin 2 × Fin 4060 :=
  (if k.val < 137 then (if k.val < 68 then (if k.val < 34 then (if k.val < 17 then (if k.val < 8 then (if k.val < 4 then (if k.val < 2 then (if k.val < 1 then (0, 942) else (0, 947)) else (if k.val < 3 then (0, 948) else (0, 951))) else (if k.val < 6 then (if k.val < 5 then (1, 942) else (0, 1082)) else (if k.val < 7 then (0, 1087) else (0, 1088)))) else (if k.val < 12 then (if k.val < 10 then (if k.val < 9 then (1, 1092) else (1, 1099)) else (if k.val < 11 then (0, 1232) else (0, 1234))) else (if k.val < 14 then (if k.val < 13 then (0, 1237) else (1, 1222)) else (if k.val < 15 then (1, 1233) else (if k.val < 16 then (1, 1235) else (0, 1362)))))) else (if k.val < 25 then (if k.val < 21 then (if k.val < 19 then (if k.val < 18 then (0, 1373) else (0, 1375)) else (if k.val < 20 then (0, 1376) else (1, 1367))) else (if k.val < 23 then (if k.val < 22 then (1, 1374) else (0, 1507)) else (if k.val < 24 then (0, 1509) else (1, 1507)))) else (if k.val < 29 then (if k.val < 27 then (if k.val < 26 then (1, 1510) else (1, 1512)) else (if k.val < 28 then (1, 1518) else (0, 1646))) else (if k.val < 31 then (if k.val < 30 then (0, 1647) else (0, 1652)) else (if k.val < 32 then (1, 1643) else (if k.val < 33 then (1, 1648) else (1, 1652))))))) else (if k.val < 51 then (if k.val < 42 then (if k.val < 38 then (if k.val < 36 then (if k.val < 35 then (1, 1657) else (1, 1658)) else (if k.val < 37 then (0, 1791) else (0, 1797))) else (if k.val < 40 then (if k.val < 39 then (0, 1798) else (1, 1784)) else (if k.val < 41 then (1, 1792) else (1, 1795)))) else (if k.val < 46 then (if k.val < 44 then (if k.val < 43 then (0, 1920) else (0, 1927)) else (if k.val < 45 then (0, 1929) else (0, 1939))) else (if k.val < 48 then (if k.val < 47 then (1, 1920) else (1, 1929)) else (if k.val < 49 then (1, 1931) else (if k.val < 50 then (1, 1933) else (1, 1939)))))) else (if k.val < 59 then (if k.val < 55 then (if k.val < 53 then (if k.val < 52 then (0, 2062) else (0, 2064)) else (if k.val < 54 then (0, 2069) else (0, 2074))) else (if k.val < 57 then (if k.val < 56 then (0, 2075) else (1, 2062)) else (if k.val < 58 then (1, 2065) else (1, 2067)))) else (if k.val < 63 then (if k.val < 61 then (if k.val < 60 then (1, 2073) else (0, 2203)) else (if k.val < 62 then (0, 2211) else (0, 2214))) else (if k.val < 65 then (if k.val < 64 then (0, 2217) else (0, 2219)) else (if k.val < 66 then (1, 2200) else (if k.val < 67 then (1, 2203) else (1, 2206)))))))) else (if k.val < 102 then (if k.val < 85 then (if k.val < 76 then (if k.val < 72 then (if k.val < 70 then (if k.val < 69 then (1, 2210) else (1, 2216)) else (if k.val < 71 then (0, 2340) else (0, 2349))) else (if k.val < 74 then (if k.val < 73 then (0, 2351) else (0, 2352)) else (if k.val < 75 then (0, 2354) else (0, 2355)))) else (if k.val < 80 then (if k.val < 78 then (if k.val < 77 then (0, 2356) else (0, 2358)) else (if k.val < 79 then (1, 2347) else (1, 2355))) else (if k.val < 82 then (if k.val < 81 then (0, 2481) else (0, 2482)) else (if k.val < 83 then (0, 2485) else (if k.val < 84 then (0, 2487) else (0, 2488)))))) else (if k.val < 93 then (if k.val < 89 then (if k.val < 87 then (if k.val < 86 then (0, 2491) else (0, 2498)) else (if k.val < 88 then (1, 2482) else (1, 2486))) else (if k.val < 91 then (if k.val < 90 then (1, 2491) else (1, 2493)) else (if k.val < 92 then (1, 2497) else (1, 2499)))) else (if k.val < 97 then (if k.val < 95 then (if k.val < 94 then (0, 2620) else (0, 2622)) else (if k.val < 96 then (0, 2636) else (1, 2628))) else (if k.val < 99 then (if k.val < 98 then (1, 2630) else (1, 2634)) else (if k.val < 100 then (1, 2638) else (if k.val < 101 then (0, 2763) else (0, 2767))))))) else (if k.val < 119 then (if k.val < 110 then (if k.val < 106 then (if k.val < 104 then (if k.val < 103 then (0, 2769) else (0, 2772)) else (if k.val < 105 then (0, 2775) else (0, 2777))) else (if k.val < 108 then (if k.val < 107 then (0, 2778) else (0, 2779)) else (if k.val < 109 then (1, 2761) else (1, 2762)))) else (if k.val < 114 then (if k.val < 112 then (if k.val < 111 then (1, 2764) else (1, 2766)) else (if k.val < 113 then (1, 2770) else (1, 2771))) else (if k.val < 116 then (if k.val < 115 then (1, 2773) else (1, 2774)) else (if k.val < 117 then (1, 2776) else (if k.val < 118 then (1, 2779) else (0, 2903)))))) else (if k.val < 128 then (if k.val < 123 then (if k.val < 121 then (if k.val < 120 then (0, 2907) else (0, 2909)) else (if k.val < 122 then (0, 2911) else (0, 2912))) else (if k.val < 125 then (if k.val < 124 then (0, 2914) else (0, 2917)) else (if k.val < 126 then (0, 2918) else (if k.val < 127 then (1, 2904) else (1, 2909))))) else (if k.val < 132 then (if k.val < 130 then (if k.val < 129 then (1, 2910) else (1, 2915)) else (if k.val < 131 then (1, 2917) else (0, 3041))) else (if k.val < 134 then (if k.val < 133 then (0, 3045) else (0, 3046)) else (if k.val < 135 then (0, 3053) else (if k.val < 136 then (0, 3056) else (0, 3059))))))))) else (if k.val < 206 then (if k.val < 171 then (if k.val < 154 then (if k.val < 145 then (if k.val < 141 then (if k.val < 139 then (if k.val < 138 then (1, 3044) else (1, 3054)) else (if k.val < 140 then (1, 3055) else (1, 3057))) else (if k.val < 143 then (if k.val < 142 then (1, 3058) else (1, 3059)) else (if k.val < 144 then (0, 3182) else (0, 3185)))) else (if k.val < 149 then (if k.val < 147 then (if k.val < 146 then (0, 3187) else (0, 3188)) else (if k.val < 148 then (0, 3189) else (0, 3190))) else (if k.val < 151 then (if k.val < 150 then (0, 3191) else (0, 3192)) else (if k.val < 152 then (0, 3194) else (if k.val < 153 then (0, 3195) else (1, 3183)))))) else (if k.val < 162 then (if k.val < 158 then (if k.val < 156 then (if k.val < 155 then (1, 3186) else (1, 3189)) else (if k.val < 157 then (1, 3191) else (1, 3196))) else (if k.val < 160 then (if k.val < 159 then (1, 3197) else (1, 3198)) else (if k.val < 161 then (1, 3199) else (0, 3323)))) else (if k.val < 166 then (if k.val < 164 then (if k.val < 163 then (0, 3326) else (0, 3327)) else (if k.val < 165 then (0, 3329) else (0, 3333))) else (if k.val < 168 then (if k.val < 167 then (1, 3320) else (1, 3321)) else (if k.val < 169 then (1, 3322) else (if k.val < 170 then (1, 3324) else (1, 3325))))))) else (if k.val < 188 then (if k.val < 179 then (if k.val < 175 then (if k.val < 173 then (if k.val < 172 then (1, 3326) else (1, 3330)) else (if k.val < 174 then (1, 3332) else (1, 3333))) else (if k.val < 177 then (if k.val < 176 then (1, 3337) else (0, 3463)) else (if k.val < 178 then (0, 3467) else (0, 3468)))) else (if k.val < 183 then (if k.val < 181 then (if k.val < 180 then (0, 3469) else (0, 3473)) else (if k.val < 182 then (0, 3476) else (0, 3478))) else (if k.val < 185 then (if k.val < 184 then (1, 3461) else (1, 3462)) else (if k.val < 186 then (1, 3465) else (if k.val < 187 then (1, 3466) else (1, 3467)))))) else (if k.val < 197 then (if k.val < 192 then (if k.val < 190 then (if k.val < 189 then (1, 3470) else (1, 3472)) else (if k.val < 191 then (1, 3475) else (0, 3601))) else (if k.val < 194 then (if k.val < 193 then (0, 3603) else (0, 3604)) else (if k.val < 195 then (0, 3605) else (if k.val < 196 then (0, 3607) else (0, 3609))))) else (if k.val < 201 then (if k.val < 199 then (if k.val < 198 then (0, 3613) else (0, 3617)) else (if k.val < 200 then (0, 3618) else (1, 3602))) else (if k.val < 203 then (if k.val < 202 then (1, 3603) else (1, 3606)) else (if k.val < 204 then (1, 3609) else (if k.val < 205 then (1, 3610) else (1, 3614)))))))) else (if k.val < 240 then (if k.val < 223 then (if k.val < 214 then (if k.val < 210 then (if k.val < 208 then (if k.val < 207 then (1, 3615) else (1, 3616)) else (if k.val < 209 then (1, 3619) else (0, 3742))) else (if k.val < 212 then (if k.val < 211 then (0, 3744) else (0, 3747)) else (if k.val < 213 then (0, 3749) else (0, 3750)))) else (if k.val < 218 then (if k.val < 216 then (if k.val < 215 then (0, 3751) else (0, 3753)) else (if k.val < 217 then (0, 3757) else (0, 3758))) else (if k.val < 220 then (if k.val < 219 then (0, 3759) else (1, 3740)) else (if k.val < 221 then (1, 3743) else (if k.val < 222 then (1, 3745) else (1, 3746)))))) else (if k.val < 231 then (if k.val < 227 then (if k.val < 225 then (if k.val < 224 then (1, 3748) else (1, 3754)) else (if k.val < 226 then (1, 3755) else (1, 3757))) else (if k.val < 229 then (if k.val < 228 then (1, 3758) else (1, 3759)) else (if k.val < 230 then (0, 3880) else (0, 3881)))) else (if k.val < 235 then (if k.val < 233 then (if k.val < 232 then (0, 3884) else (0, 3887)) else (if k.val < 234 then (0, 3890) else (0, 3893))) else (if k.val < 237 then (if k.val < 236 then (0, 3894) else (0, 3896)) else (if k.val < 238 then (0, 3897) else (if k.val < 239 then (0, 3899) else (1, 3880))))))) else (if k.val < 257 then (if k.val < 248 then (if k.val < 244 then (if k.val < 242 then (if k.val < 241 then (1, 3883) else (1, 3885)) else (if k.val < 243 then (1, 3886) else (1, 3888))) else (if k.val < 246 then (if k.val < 245 then (1, 3889) else (1, 3891)) else (if k.val < 247 then (1, 3892) else (1, 3893)))) else (if k.val < 252 then (if k.val < 250 then (if k.val < 249 then (1, 3894) else (1, 3896)) else (if k.val < 251 then (1, 3897) else (1, 3898))) else (if k.val < 254 then (if k.val < 253 then (1, 3899) else (0, 4020)) else (if k.val < 255 then (0, 4021) else (if k.val < 256 then (0, 4023) else (0, 4024)))))) else (if k.val < 266 then (if k.val < 261 then (if k.val < 259 then (if k.val < 258 then (0, 4025) else (0, 4026)) else (if k.val < 260 then (0, 4034) else (0, 4037))) else (if k.val < 263 then (if k.val < 262 then (0, 4038) else (1, 4021)) else (if k.val < 264 then (1, 4022) else (if k.val < 265 then (1, 4023) else (1, 4025))))) else (if k.val < 270 then (if k.val < 268 then (if k.val < 267 then (1, 4027) else (1, 4028)) else (if k.val < 269 then (1, 4029) else (1, 4030))) else (if k.val < 272 then (if k.val < 271 then (1, 4031) else (1, 4032)) else (if k.val < 273 then (1, 4035) else (if k.val < 274 then (1, 4036) else (1, 4039))))))))))

@[expose] public def residualCheck (k : Fin 275) : Prop :=
  stepCheck (target k).1 (target k).2

/-- Groups 0, 1, 2 contain 69 transitions; group 3 contains 68. -/
@[expose] public def residualBatch (g : Fin 4) : Prop :=
  ∀ (s : Fin 69) (h : 69 * g.val + s.val < 275),
    residualCheck ⟨69 * g.val + s.val, h⟩

public theorem all_of_batches (h : ∀ g : Fin 4, residualBatch g) :
    ∀ k : Fin 275, residualCheck k := by
  intro k
  let g : Fin 4 := ⟨k.val / 69, by omega⟩
  let s : Fin 69 := ⟨k.val % 69, by omega⟩
  have hlt : 69 * g.val + s.val < 275 := by dsimp [g, s]; omega
  have hk : (⟨69 * g.val + s.val, hlt⟩ : Fin 275) = k := by
    apply Fin.ext
    dsimp [g, s]
    omega
  simpa only [hk] using h g s hlt

set_option maxHeartbeats 1600000 in
private theorem point6_0_0 : stepCheck 0 940 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_1 : stepCheck 0 941 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_3 : stepCheck 0 943 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_4 : stepCheck 0 944 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_5 : stepCheck 0 945 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_6 : stepCheck 0 946 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_9 : stepCheck 0 949 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_10 : stepCheck 0 950 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_12 : stepCheck 0 952 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_13 : stepCheck 0 953 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_14 : stepCheck 0 954 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_15 : stepCheck 0 955 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_16 : stepCheck 0 956 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_17 : stepCheck 0 957 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_18 : stepCheck 0 958 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_0_19 : stepCheck 0 959 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_0 : stepCheck 1 940 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_1 : stepCheck 1 941 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_3 : stepCheck 1 943 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_4 : stepCheck 1 944 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_5 : stepCheck 1 945 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_6 : stepCheck 1 946 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_7 : stepCheck 1 947 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_8 : stepCheck 1 948 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_9 : stepCheck 1 949 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_10 : stepCheck 1 950 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_11 : stepCheck 1 951 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_12 : stepCheck 1 952 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_13 : stepCheck 1 953 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_14 : stepCheck 1 954 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_15 : stepCheck 1 955 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_16 : stepCheck 1 956 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_17 : stepCheck 1 957 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_18 : stepCheck 1 958 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point6_1_19 : stepCheck 1 959 := by
  left
  decide +kernel

private theorem checked6 (_h : ∀ k : Fin 275, residualCheck k) : stepBatch 47 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point6_0_0
  · exact point6_0_1
  · exact _h 0
  · exact point6_0_3
  · exact point6_0_4
  · exact point6_0_5
  · exact point6_0_6
  · exact _h 1
  · exact _h 2
  · exact point6_0_9
  · exact point6_0_10
  · exact _h 3
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
  · exact _h 4
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
private theorem point7_0_0 : stepCheck 0 1080 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_1 : stepCheck 0 1081 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_3 : stepCheck 0 1083 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_4 : stepCheck 0 1084 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_5 : stepCheck 0 1085 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_6 : stepCheck 0 1086 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_9 : stepCheck 0 1089 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_10 : stepCheck 0 1090 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_11 : stepCheck 0 1091 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_12 : stepCheck 0 1092 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_13 : stepCheck 0 1093 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_14 : stepCheck 0 1094 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_15 : stepCheck 0 1095 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_16 : stepCheck 0 1096 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_17 : stepCheck 0 1097 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_18 : stepCheck 0 1098 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_0_19 : stepCheck 0 1099 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_0 : stepCheck 1 1080 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_1 : stepCheck 1 1081 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_2 : stepCheck 1 1082 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_3 : stepCheck 1 1083 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_4 : stepCheck 1 1084 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_5 : stepCheck 1 1085 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_6 : stepCheck 1 1086 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_7 : stepCheck 1 1087 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_8 : stepCheck 1 1088 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_9 : stepCheck 1 1089 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_10 : stepCheck 1 1090 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_11 : stepCheck 1 1091 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_13 : stepCheck 1 1093 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_14 : stepCheck 1 1094 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_15 : stepCheck 1 1095 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_16 : stepCheck 1 1096 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_17 : stepCheck 1 1097 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point7_1_18 : stepCheck 1 1098 := by
  left
  decide +kernel

private theorem checked7 (_h : ∀ k : Fin 275, residualCheck k) : stepBatch 54 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point7_0_0
  · exact point7_0_1
  · exact _h 5
  · exact point7_0_3
  · exact point7_0_4
  · exact point7_0_5
  · exact point7_0_6
  · exact _h 6
  · exact _h 7
  · exact point7_0_9
  · exact point7_0_10
  · exact point7_0_11
  · exact point7_0_12
  · exact point7_0_13
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
  · exact point7_1_4
  · exact point7_1_5
  · exact point7_1_6
  · exact point7_1_7
  · exact point7_1_8
  · exact point7_1_9
  · exact point7_1_10
  · exact point7_1_11
  · exact _h 8
  · exact point7_1_13
  · exact point7_1_14
  · exact point7_1_15
  · exact point7_1_16
  · exact point7_1_17
  · exact point7_1_18
  · exact _h 9

set_option maxHeartbeats 1600000 in
private theorem point8_0_0 : stepCheck 0 1220 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_1 : stepCheck 0 1221 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_2 : stepCheck 0 1222 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_3 : stepCheck 0 1223 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_4 : stepCheck 0 1224 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_5 : stepCheck 0 1225 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_6 : stepCheck 0 1226 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_7 : stepCheck 0 1227 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_8 : stepCheck 0 1228 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_9 : stepCheck 0 1229 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_10 : stepCheck 0 1230 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_11 : stepCheck 0 1231 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_13 : stepCheck 0 1233 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_15 : stepCheck 0 1235 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_16 : stepCheck 0 1236 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_18 : stepCheck 0 1238 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_0_19 : stepCheck 0 1239 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_0 : stepCheck 1 1220 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_1 : stepCheck 1 1221 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_3 : stepCheck 1 1223 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_4 : stepCheck 1 1224 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_5 : stepCheck 1 1225 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_6 : stepCheck 1 1226 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_7 : stepCheck 1 1227 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_8 : stepCheck 1 1228 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_9 : stepCheck 1 1229 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_10 : stepCheck 1 1230 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_11 : stepCheck 1 1231 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_12 : stepCheck 1 1232 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_14 : stepCheck 1 1234 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_16 : stepCheck 1 1236 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_17 : stepCheck 1 1237 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_18 : stepCheck 1 1238 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point8_1_19 : stepCheck 1 1239 := by
  left
  decide +kernel

private theorem checked8 (_h : ∀ k : Fin 275, residualCheck k) : stepBatch 61 := by
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
  · exact point8_0_9
  · exact point8_0_10
  · exact point8_0_11
  · exact _h 10
  · exact point8_0_13
  · exact _h 11
  · exact point8_0_15
  · exact point8_0_16
  · exact _h 12
  · exact point8_0_18
  · exact point8_0_19
  · exact point8_1_0
  · exact point8_1_1
  · exact _h 13
  · exact point8_1_3
  · exact point8_1_4
  · exact point8_1_5
  · exact point8_1_6
  · exact point8_1_7
  · exact point8_1_8
  · exact point8_1_9
  · exact point8_1_10
  · exact point8_1_11
  · exact point8_1_12
  · exact _h 14
  · exact point8_1_14
  · exact _h 15
  · exact point8_1_16
  · exact point8_1_17
  · exact point8_1_18
  · exact point8_1_19

set_option maxHeartbeats 1600000 in
private theorem point9_0_0 : stepCheck 0 1360 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_1 : stepCheck 0 1361 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_3 : stepCheck 0 1363 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_4 : stepCheck 0 1364 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_5 : stepCheck 0 1365 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_6 : stepCheck 0 1366 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_7 : stepCheck 0 1367 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_8 : stepCheck 0 1368 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_9 : stepCheck 0 1369 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_10 : stepCheck 0 1370 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_11 : stepCheck 0 1371 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_12 : stepCheck 0 1372 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_14 : stepCheck 0 1374 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_17 : stepCheck 0 1377 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_18 : stepCheck 0 1378 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_0_19 : stepCheck 0 1379 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_0 : stepCheck 1 1360 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_1 : stepCheck 1 1361 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_2 : stepCheck 1 1362 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_3 : stepCheck 1 1363 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_4 : stepCheck 1 1364 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_5 : stepCheck 1 1365 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_6 : stepCheck 1 1366 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_8 : stepCheck 1 1368 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_9 : stepCheck 1 1369 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_10 : stepCheck 1 1370 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_11 : stepCheck 1 1371 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_12 : stepCheck 1 1372 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_13 : stepCheck 1 1373 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_15 : stepCheck 1 1375 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_16 : stepCheck 1 1376 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_17 : stepCheck 1 1377 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_18 : stepCheck 1 1378 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point9_1_19 : stepCheck 1 1379 := by
  left
  decide +kernel

private theorem checked9 (_h : ∀ k : Fin 275, residualCheck k) : stepBatch 68 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point9_0_0
  · exact point9_0_1
  · exact _h 16
  · exact point9_0_3
  · exact point9_0_4
  · exact point9_0_5
  · exact point9_0_6
  · exact point9_0_7
  · exact point9_0_8
  · exact point9_0_9
  · exact point9_0_10
  · exact point9_0_11
  · exact point9_0_12
  · exact _h 17
  · exact point9_0_14
  · exact _h 18
  · exact _h 19
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
  · exact _h 20
  · exact point9_1_8
  · exact point9_1_9
  · exact point9_1_10
  · exact point9_1_11
  · exact point9_1_12
  · exact point9_1_13
  · exact _h 21
  · exact point9_1_15
  · exact point9_1_16
  · exact point9_1_17
  · exact point9_1_18
  · exact point9_1_19

set_option maxHeartbeats 1600000 in
private theorem point10_0_0 : stepCheck 0 1500 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_1 : stepCheck 0 1501 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_2 : stepCheck 0 1502 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_3 : stepCheck 0 1503 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_4 : stepCheck 0 1504 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_5 : stepCheck 0 1505 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_6 : stepCheck 0 1506 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_8 : stepCheck 0 1508 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_10 : stepCheck 0 1510 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_11 : stepCheck 0 1511 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_12 : stepCheck 0 1512 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_13 : stepCheck 0 1513 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_14 : stepCheck 0 1514 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_15 : stepCheck 0 1515 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_16 : stepCheck 0 1516 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_17 : stepCheck 0 1517 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_18 : stepCheck 0 1518 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_0_19 : stepCheck 0 1519 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_0 : stepCheck 1 1500 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_1 : stepCheck 1 1501 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_2 : stepCheck 1 1502 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_3 : stepCheck 1 1503 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_4 : stepCheck 1 1504 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_5 : stepCheck 1 1505 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_6 : stepCheck 1 1506 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_8 : stepCheck 1 1508 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_9 : stepCheck 1 1509 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_11 : stepCheck 1 1511 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_13 : stepCheck 1 1513 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_14 : stepCheck 1 1514 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_15 : stepCheck 1 1515 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_16 : stepCheck 1 1516 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_17 : stepCheck 1 1517 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point10_1_19 : stepCheck 1 1519 := by
  left
  decide +kernel

private theorem checked10 (_h : ∀ k : Fin 275, residualCheck k) : stepBatch 75 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point10_0_0
  · exact point10_0_1
  · exact point10_0_2
  · exact point10_0_3
  · exact point10_0_4
  · exact point10_0_5
  · exact point10_0_6
  · exact _h 22
  · exact point10_0_8
  · exact _h 23
  · exact point10_0_10
  · exact point10_0_11
  · exact point10_0_12
  · exact point10_0_13
  · exact point10_0_14
  · exact point10_0_15
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
  · exact _h 24
  · exact point10_1_8
  · exact point10_1_9
  · exact _h 25
  · exact point10_1_11
  · exact _h 26
  · exact point10_1_13
  · exact point10_1_14
  · exact point10_1_15
  · exact point10_1_16
  · exact point10_1_17
  · exact _h 27
  · exact point10_1_19

set_option maxHeartbeats 1600000 in
private theorem point11_0_0 : stepCheck 0 1640 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_1 : stepCheck 0 1641 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_2 : stepCheck 0 1642 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_3 : stepCheck 0 1643 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_4 : stepCheck 0 1644 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_5 : stepCheck 0 1645 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_8 : stepCheck 0 1648 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_9 : stepCheck 0 1649 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_10 : stepCheck 0 1650 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_11 : stepCheck 0 1651 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_13 : stepCheck 0 1653 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_14 : stepCheck 0 1654 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_15 : stepCheck 0 1655 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_16 : stepCheck 0 1656 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_17 : stepCheck 0 1657 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_18 : stepCheck 0 1658 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_0_19 : stepCheck 0 1659 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_0 : stepCheck 1 1640 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_1 : stepCheck 1 1641 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_2 : stepCheck 1 1642 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_4 : stepCheck 1 1644 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_5 : stepCheck 1 1645 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_6 : stepCheck 1 1646 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_7 : stepCheck 1 1647 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_9 : stepCheck 1 1649 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_10 : stepCheck 1 1650 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_11 : stepCheck 1 1651 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_13 : stepCheck 1 1653 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_14 : stepCheck 1 1654 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_15 : stepCheck 1 1655 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_16 : stepCheck 1 1656 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point11_1_19 : stepCheck 1 1659 := by
  left
  decide +kernel

private theorem checked11 (_h : ∀ k : Fin 275, residualCheck k) : stepBatch 82 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point11_0_0
  · exact point11_0_1
  · exact point11_0_2
  · exact point11_0_3
  · exact point11_0_4
  · exact point11_0_5
  · exact _h 28
  · exact _h 29
  · exact point11_0_8
  · exact point11_0_9
  · exact point11_0_10
  · exact point11_0_11
  · exact _h 30
  · exact point11_0_13
  · exact point11_0_14
  · exact point11_0_15
  · exact point11_0_16
  · exact point11_0_17
  · exact point11_0_18
  · exact point11_0_19
  · exact point11_1_0
  · exact point11_1_1
  · exact point11_1_2
  · exact _h 31
  · exact point11_1_4
  · exact point11_1_5
  · exact point11_1_6
  · exact point11_1_7
  · exact _h 32
  · exact point11_1_9
  · exact point11_1_10
  · exact point11_1_11
  · exact _h 33
  · exact point11_1_13
  · exact point11_1_14
  · exact point11_1_15
  · exact point11_1_16
  · exact _h 34
  · exact _h 35
  · exact point11_1_19

set_option maxHeartbeats 1600000 in
private theorem point12_0_0 : stepCheck 0 1780 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_1 : stepCheck 0 1781 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_2 : stepCheck 0 1782 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_3 : stepCheck 0 1783 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_4 : stepCheck 0 1784 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_5 : stepCheck 0 1785 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_6 : stepCheck 0 1786 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_7 : stepCheck 0 1787 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_8 : stepCheck 0 1788 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_9 : stepCheck 0 1789 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_10 : stepCheck 0 1790 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_12 : stepCheck 0 1792 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_13 : stepCheck 0 1793 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_14 : stepCheck 0 1794 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_15 : stepCheck 0 1795 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_16 : stepCheck 0 1796 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_0_19 : stepCheck 0 1799 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_0 : stepCheck 1 1780 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_1 : stepCheck 1 1781 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_2 : stepCheck 1 1782 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_3 : stepCheck 1 1783 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_5 : stepCheck 1 1785 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_6 : stepCheck 1 1786 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_7 : stepCheck 1 1787 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_8 : stepCheck 1 1788 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_9 : stepCheck 1 1789 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_10 : stepCheck 1 1790 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_11 : stepCheck 1 1791 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_13 : stepCheck 1 1793 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_14 : stepCheck 1 1794 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_16 : stepCheck 1 1796 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_17 : stepCheck 1 1797 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_18 : stepCheck 1 1798 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point12_1_19 : stepCheck 1 1799 := by
  left
  decide +kernel

private theorem checked12 (_h : ∀ k : Fin 275, residualCheck k) : stepBatch 89 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point12_0_0
  · exact point12_0_1
  · exact point12_0_2
  · exact point12_0_3
  · exact point12_0_4
  · exact point12_0_5
  · exact point12_0_6
  · exact point12_0_7
  · exact point12_0_8
  · exact point12_0_9
  · exact point12_0_10
  · exact _h 36
  · exact point12_0_12
  · exact point12_0_13
  · exact point12_0_14
  · exact point12_0_15
  · exact point12_0_16
  · exact _h 37
  · exact _h 38
  · exact point12_0_19
  · exact point12_1_0
  · exact point12_1_1
  · exact point12_1_2
  · exact point12_1_3
  · exact _h 39
  · exact point12_1_5
  · exact point12_1_6
  · exact point12_1_7
  · exact point12_1_8
  · exact point12_1_9
  · exact point12_1_10
  · exact point12_1_11
  · exact _h 40
  · exact point12_1_13
  · exact point12_1_14
  · exact _h 41
  · exact point12_1_16
  · exact point12_1_17
  · exact point12_1_18
  · exact point12_1_19

set_option maxHeartbeats 1600000 in
private theorem point13_0_1 : stepCheck 0 1921 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_2 : stepCheck 0 1922 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_3 : stepCheck 0 1923 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_4 : stepCheck 0 1924 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_5 : stepCheck 0 1925 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_6 : stepCheck 0 1926 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_8 : stepCheck 0 1928 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_10 : stepCheck 0 1930 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_11 : stepCheck 0 1931 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_12 : stepCheck 0 1932 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_13 : stepCheck 0 1933 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_14 : stepCheck 0 1934 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_15 : stepCheck 0 1935 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_16 : stepCheck 0 1936 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_17 : stepCheck 0 1937 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_0_18 : stepCheck 0 1938 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_1 : stepCheck 1 1921 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_2 : stepCheck 1 1922 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_3 : stepCheck 1 1923 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_4 : stepCheck 1 1924 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_5 : stepCheck 1 1925 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_6 : stepCheck 1 1926 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_7 : stepCheck 1 1927 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_8 : stepCheck 1 1928 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_10 : stepCheck 1 1930 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_12 : stepCheck 1 1932 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_14 : stepCheck 1 1934 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_15 : stepCheck 1 1935 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_16 : stepCheck 1 1936 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_17 : stepCheck 1 1937 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point13_1_18 : stepCheck 1 1938 := by
  left
  decide +kernel

private theorem checked13 (_h : ∀ k : Fin 275, residualCheck k) : stepBatch 96 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact _h 42
  · exact point13_0_1
  · exact point13_0_2
  · exact point13_0_3
  · exact point13_0_4
  · exact point13_0_5
  · exact point13_0_6
  · exact _h 43
  · exact point13_0_8
  · exact _h 44
  · exact point13_0_10
  · exact point13_0_11
  · exact point13_0_12
  · exact point13_0_13
  · exact point13_0_14
  · exact point13_0_15
  · exact point13_0_16
  · exact point13_0_17
  · exact point13_0_18
  · exact _h 45
  · exact _h 46
  · exact point13_1_1
  · exact point13_1_2
  · exact point13_1_3
  · exact point13_1_4
  · exact point13_1_5
  · exact point13_1_6
  · exact point13_1_7
  · exact point13_1_8
  · exact _h 47
  · exact point13_1_10
  · exact _h 48
  · exact point13_1_12
  · exact _h 49
  · exact point13_1_14
  · exact point13_1_15
  · exact point13_1_16
  · exact point13_1_17
  · exact point13_1_18
  · exact _h 50

set_option maxHeartbeats 1600000 in
private theorem point14_0_0 : stepCheck 0 2060 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_1 : stepCheck 0 2061 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_3 : stepCheck 0 2063 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_5 : stepCheck 0 2065 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_6 : stepCheck 0 2066 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_7 : stepCheck 0 2067 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_8 : stepCheck 0 2068 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_10 : stepCheck 0 2070 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_11 : stepCheck 0 2071 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_12 : stepCheck 0 2072 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_13 : stepCheck 0 2073 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_16 : stepCheck 0 2076 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_17 : stepCheck 0 2077 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_18 : stepCheck 0 2078 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_0_19 : stepCheck 0 2079 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_0 : stepCheck 1 2060 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_1 : stepCheck 1 2061 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_3 : stepCheck 1 2063 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_4 : stepCheck 1 2064 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_6 : stepCheck 1 2066 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_8 : stepCheck 1 2068 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_9 : stepCheck 1 2069 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_10 : stepCheck 1 2070 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_11 : stepCheck 1 2071 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_12 : stepCheck 1 2072 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_14 : stepCheck 1 2074 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_15 : stepCheck 1 2075 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_16 : stepCheck 1 2076 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_17 : stepCheck 1 2077 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_18 : stepCheck 1 2078 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point14_1_19 : stepCheck 1 2079 := by
  left
  decide +kernel

private theorem checked14 (_h : ∀ k : Fin 275, residualCheck k) : stepBatch 103 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point14_0_0
  · exact point14_0_1
  · exact _h 51
  · exact point14_0_3
  · exact _h 52
  · exact point14_0_5
  · exact point14_0_6
  · exact point14_0_7
  · exact point14_0_8
  · exact _h 53
  · exact point14_0_10
  · exact point14_0_11
  · exact point14_0_12
  · exact point14_0_13
  · exact _h 54
  · exact _h 55
  · exact point14_0_16
  · exact point14_0_17
  · exact point14_0_18
  · exact point14_0_19
  · exact point14_1_0
  · exact point14_1_1
  · exact _h 56
  · exact point14_1_3
  · exact point14_1_4
  · exact _h 57
  · exact point14_1_6
  · exact _h 58
  · exact point14_1_8
  · exact point14_1_9
  · exact point14_1_10
  · exact point14_1_11
  · exact point14_1_12
  · exact _h 59
  · exact point14_1_14
  · exact point14_1_15
  · exact point14_1_16
  · exact point14_1_17
  · exact point14_1_18
  · exact point14_1_19

set_option maxHeartbeats 1600000 in
private theorem point15_0_0 : stepCheck 0 2200 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_1 : stepCheck 0 2201 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_2 : stepCheck 0 2202 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_4 : stepCheck 0 2204 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_5 : stepCheck 0 2205 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_6 : stepCheck 0 2206 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_7 : stepCheck 0 2207 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_8 : stepCheck 0 2208 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_9 : stepCheck 0 2209 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_10 : stepCheck 0 2210 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_12 : stepCheck 0 2212 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_13 : stepCheck 0 2213 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_15 : stepCheck 0 2215 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_16 : stepCheck 0 2216 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_0_18 : stepCheck 0 2218 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_1 : stepCheck 1 2201 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_2 : stepCheck 1 2202 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_4 : stepCheck 1 2204 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_5 : stepCheck 1 2205 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_7 : stepCheck 1 2207 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_8 : stepCheck 1 2208 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_9 : stepCheck 1 2209 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_11 : stepCheck 1 2211 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_12 : stepCheck 1 2212 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_13 : stepCheck 1 2213 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_14 : stepCheck 1 2214 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_15 : stepCheck 1 2215 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_17 : stepCheck 1 2217 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_18 : stepCheck 1 2218 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point15_1_19 : stepCheck 1 2219 := by
  left
  decide +kernel

private theorem checked15 (_h : ∀ k : Fin 275, residualCheck k) : stepBatch 110 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point15_0_0
  · exact point15_0_1
  · exact point15_0_2
  · exact _h 60
  · exact point15_0_4
  · exact point15_0_5
  · exact point15_0_6
  · exact point15_0_7
  · exact point15_0_8
  · exact point15_0_9
  · exact point15_0_10
  · exact _h 61
  · exact point15_0_12
  · exact point15_0_13
  · exact _h 62
  · exact point15_0_15
  · exact point15_0_16
  · exact _h 63
  · exact point15_0_18
  · exact _h 64
  · exact _h 65
  · exact point15_1_1
  · exact point15_1_2
  · exact _h 66
  · exact point15_1_4
  · exact point15_1_5
  · exact _h 67
  · exact point15_1_7
  · exact point15_1_8
  · exact point15_1_9
  · exact _h 68
  · exact point15_1_11
  · exact point15_1_12
  · exact point15_1_13
  · exact point15_1_14
  · exact point15_1_15
  · exact _h 69
  · exact point15_1_17
  · exact point15_1_18
  · exact point15_1_19

set_option maxHeartbeats 1600000 in
private theorem point16_0_1 : stepCheck 0 2341 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_2 : stepCheck 0 2342 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_3 : stepCheck 0 2343 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_4 : stepCheck 0 2344 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_5 : stepCheck 0 2345 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_6 : stepCheck 0 2346 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_7 : stepCheck 0 2347 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_8 : stepCheck 0 2348 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_10 : stepCheck 0 2350 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_13 : stepCheck 0 2353 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_17 : stepCheck 0 2357 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_0_19 : stepCheck 0 2359 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_0 : stepCheck 1 2340 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_1 : stepCheck 1 2341 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_2 : stepCheck 1 2342 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_3 : stepCheck 1 2343 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_4 : stepCheck 1 2344 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_5 : stepCheck 1 2345 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_6 : stepCheck 1 2346 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_8 : stepCheck 1 2348 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_9 : stepCheck 1 2349 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_10 : stepCheck 1 2350 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_11 : stepCheck 1 2351 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_12 : stepCheck 1 2352 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_13 : stepCheck 1 2353 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_14 : stepCheck 1 2354 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_16 : stepCheck 1 2356 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_17 : stepCheck 1 2357 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_18 : stepCheck 1 2358 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point16_1_19 : stepCheck 1 2359 := by
  left
  decide +kernel

private theorem checked16 (_h : ∀ k : Fin 275, residualCheck k) : stepBatch 117 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact _h 70
  · exact point16_0_1
  · exact point16_0_2
  · exact point16_0_3
  · exact point16_0_4
  · exact point16_0_5
  · exact point16_0_6
  · exact point16_0_7
  · exact point16_0_8
  · exact _h 71
  · exact point16_0_10
  · exact _h 72
  · exact _h 73
  · exact point16_0_13
  · exact _h 74
  · exact _h 75
  · exact _h 76
  · exact point16_0_17
  · exact _h 77
  · exact point16_0_19
  · exact point16_1_0
  · exact point16_1_1
  · exact point16_1_2
  · exact point16_1_3
  · exact point16_1_4
  · exact point16_1_5
  · exact point16_1_6
  · exact _h 78
  · exact point16_1_8
  · exact point16_1_9
  · exact point16_1_10
  · exact point16_1_11
  · exact point16_1_12
  · exact point16_1_13
  · exact point16_1_14
  · exact _h 79
  · exact point16_1_16
  · exact point16_1_17
  · exact point16_1_18
  · exact point16_1_19

set_option maxHeartbeats 1600000 in
private theorem point17_0_0 : stepCheck 0 2480 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_3 : stepCheck 0 2483 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_4 : stepCheck 0 2484 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_6 : stepCheck 0 2486 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_9 : stepCheck 0 2489 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_10 : stepCheck 0 2490 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_12 : stepCheck 0 2492 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_13 : stepCheck 0 2493 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_14 : stepCheck 0 2494 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_15 : stepCheck 0 2495 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_16 : stepCheck 0 2496 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_17 : stepCheck 0 2497 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_0_19 : stepCheck 0 2499 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_0 : stepCheck 1 2480 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_1 : stepCheck 1 2481 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_3 : stepCheck 1 2483 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_4 : stepCheck 1 2484 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_5 : stepCheck 1 2485 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_7 : stepCheck 1 2487 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_8 : stepCheck 1 2488 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_9 : stepCheck 1 2489 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_10 : stepCheck 1 2490 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_12 : stepCheck 1 2492 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_14 : stepCheck 1 2494 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_15 : stepCheck 1 2495 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_16 : stepCheck 1 2496 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point17_1_18 : stepCheck 1 2498 := by
  left
  decide +kernel

private theorem checked17 (_h : ∀ k : Fin 275, residualCheck k) : stepBatch 124 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point17_0_0
  · exact _h 80
  · exact _h 81
  · exact point17_0_3
  · exact point17_0_4
  · exact _h 82
  · exact point17_0_6
  · exact _h 83
  · exact _h 84
  · exact point17_0_9
  · exact point17_0_10
  · exact _h 85
  · exact point17_0_12
  · exact point17_0_13
  · exact point17_0_14
  · exact point17_0_15
  · exact point17_0_16
  · exact point17_0_17
  · exact _h 86
  · exact point17_0_19
  · exact point17_1_0
  · exact point17_1_1
  · exact _h 87
  · exact point17_1_3
  · exact point17_1_4
  · exact point17_1_5
  · exact _h 88
  · exact point17_1_7
  · exact point17_1_8
  · exact point17_1_9
  · exact point17_1_10
  · exact _h 89
  · exact point17_1_12
  · exact _h 90
  · exact point17_1_14
  · exact point17_1_15
  · exact point17_1_16
  · exact _h 91
  · exact point17_1_18
  · exact _h 92

set_option maxHeartbeats 1600000 in
private theorem point18_0_1 : stepCheck 0 2621 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_3 : stepCheck 0 2623 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_4 : stepCheck 0 2624 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_5 : stepCheck 0 2625 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_6 : stepCheck 0 2626 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_7 : stepCheck 0 2627 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_8 : stepCheck 0 2628 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_9 : stepCheck 0 2629 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_10 : stepCheck 0 2630 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_11 : stepCheck 0 2631 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_12 : stepCheck 0 2632 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_13 : stepCheck 0 2633 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_14 : stepCheck 0 2634 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_15 : stepCheck 0 2635 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_17 : stepCheck 0 2637 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_18 : stepCheck 0 2638 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_0_19 : stepCheck 0 2639 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_0 : stepCheck 1 2620 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_1 : stepCheck 1 2621 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_2 : stepCheck 1 2622 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_3 : stepCheck 1 2623 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_4 : stepCheck 1 2624 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_5 : stepCheck 1 2625 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_6 : stepCheck 1 2626 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_7 : stepCheck 1 2627 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_9 : stepCheck 1 2629 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_11 : stepCheck 1 2631 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_12 : stepCheck 1 2632 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_13 : stepCheck 1 2633 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_15 : stepCheck 1 2635 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_16 : stepCheck 1 2636 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_17 : stepCheck 1 2637 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point18_1_19 : stepCheck 1 2639 := by
  left
  decide +kernel

private theorem checked18 (_h : ∀ k : Fin 275, residualCheck k) : stepBatch 131 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact _h 93
  · exact point18_0_1
  · exact _h 94
  · exact point18_0_3
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
  · exact _h 95
  · exact point18_0_17
  · exact point18_0_18
  · exact point18_0_19
  · exact point18_1_0
  · exact point18_1_1
  · exact point18_1_2
  · exact point18_1_3
  · exact point18_1_4
  · exact point18_1_5
  · exact point18_1_6
  · exact point18_1_7
  · exact _h 96
  · exact point18_1_9
  · exact _h 97
  · exact point18_1_11
  · exact point18_1_12
  · exact point18_1_13
  · exact _h 98
  · exact point18_1_15
  · exact point18_1_16
  · exact point18_1_17
  · exact _h 99
  · exact point18_1_19

set_option maxHeartbeats 1600000 in
private theorem point19_0_0 : stepCheck 0 2760 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_1 : stepCheck 0 2761 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_2 : stepCheck 0 2762 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_4 : stepCheck 0 2764 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_5 : stepCheck 0 2765 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_6 : stepCheck 0 2766 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_8 : stepCheck 0 2768 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_10 : stepCheck 0 2770 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_11 : stepCheck 0 2771 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_13 : stepCheck 0 2773 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_14 : stepCheck 0 2774 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_0_16 : stepCheck 0 2776 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_0 : stepCheck 1 2760 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_3 : stepCheck 1 2763 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_5 : stepCheck 1 2765 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_7 : stepCheck 1 2767 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_8 : stepCheck 1 2768 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_9 : stepCheck 1 2769 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_12 : stepCheck 1 2772 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_15 : stepCheck 1 2775 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_17 : stepCheck 1 2777 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point19_1_18 : stepCheck 1 2778 := by
  left
  decide +kernel

private theorem checked19 (_h : ∀ k : Fin 275, residualCheck k) : stepBatch 138 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point19_0_0
  · exact point19_0_1
  · exact point19_0_2
  · exact _h 100
  · exact point19_0_4
  · exact point19_0_5
  · exact point19_0_6
  · exact _h 101
  · exact point19_0_8
  · exact _h 102
  · exact point19_0_10
  · exact point19_0_11
  · exact _h 103
  · exact point19_0_13
  · exact point19_0_14
  · exact _h 104
  · exact point19_0_16
  · exact _h 105
  · exact _h 106
  · exact _h 107
  · exact point19_1_0
  · exact _h 108
  · exact _h 109
  · exact point19_1_3
  · exact _h 110
  · exact point19_1_5
  · exact _h 111
  · exact point19_1_7
  · exact point19_1_8
  · exact point19_1_9
  · exact _h 112
  · exact _h 113
  · exact point19_1_12
  · exact _h 114
  · exact _h 115
  · exact point19_1_15
  · exact _h 116
  · exact point19_1_17
  · exact point19_1_18
  · exact _h 117

set_option maxHeartbeats 1600000 in
private theorem point20_0_0 : stepCheck 0 2900 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_1 : stepCheck 0 2901 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_2 : stepCheck 0 2902 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_4 : stepCheck 0 2904 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_5 : stepCheck 0 2905 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_6 : stepCheck 0 2906 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_8 : stepCheck 0 2908 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_10 : stepCheck 0 2910 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_13 : stepCheck 0 2913 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_15 : stepCheck 0 2915 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_16 : stepCheck 0 2916 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_0_19 : stepCheck 0 2919 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_0 : stepCheck 1 2900 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_1 : stepCheck 1 2901 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_2 : stepCheck 1 2902 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_3 : stepCheck 1 2903 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_5 : stepCheck 1 2905 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_6 : stepCheck 1 2906 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_7 : stepCheck 1 2907 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_8 : stepCheck 1 2908 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_11 : stepCheck 1 2911 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_12 : stepCheck 1 2912 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_13 : stepCheck 1 2913 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_14 : stepCheck 1 2914 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_16 : stepCheck 1 2916 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_18 : stepCheck 1 2918 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point20_1_19 : stepCheck 1 2919 := by
  left
  decide +kernel

private theorem checked20 (_h : ∀ k : Fin 275, residualCheck k) : stepBatch 145 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point20_0_0
  · exact point20_0_1
  · exact point20_0_2
  · exact _h 118
  · exact point20_0_4
  · exact point20_0_5
  · exact point20_0_6
  · exact _h 119
  · exact point20_0_8
  · exact _h 120
  · exact point20_0_10
  · exact _h 121
  · exact _h 122
  · exact point20_0_13
  · exact _h 123
  · exact point20_0_15
  · exact point20_0_16
  · exact _h 124
  · exact _h 125
  · exact point20_0_19
  · exact point20_1_0
  · exact point20_1_1
  · exact point20_1_2
  · exact point20_1_3
  · exact _h 126
  · exact point20_1_5
  · exact point20_1_6
  · exact point20_1_7
  · exact point20_1_8
  · exact _h 127
  · exact _h 128
  · exact point20_1_11
  · exact point20_1_12
  · exact point20_1_13
  · exact point20_1_14
  · exact _h 129
  · exact point20_1_16
  · exact _h 130
  · exact point20_1_18
  · exact point20_1_19

set_option maxHeartbeats 1600000 in
private theorem point21_0_0 : stepCheck 0 3040 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_2 : stepCheck 0 3042 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_3 : stepCheck 0 3043 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_4 : stepCheck 0 3044 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_7 : stepCheck 0 3047 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_8 : stepCheck 0 3048 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_9 : stepCheck 0 3049 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_10 : stepCheck 0 3050 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_11 : stepCheck 0 3051 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_12 : stepCheck 0 3052 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_14 : stepCheck 0 3054 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_15 : stepCheck 0 3055 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_17 : stepCheck 0 3057 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_0_18 : stepCheck 0 3058 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_0 : stepCheck 1 3040 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_1 : stepCheck 1 3041 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_2 : stepCheck 1 3042 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_3 : stepCheck 1 3043 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_5 : stepCheck 1 3045 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_6 : stepCheck 1 3046 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_7 : stepCheck 1 3047 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_8 : stepCheck 1 3048 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_9 : stepCheck 1 3049 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_10 : stepCheck 1 3050 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_11 : stepCheck 1 3051 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_12 : stepCheck 1 3052 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_13 : stepCheck 1 3053 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point21_1_16 : stepCheck 1 3056 := by
  left
  decide +kernel

private theorem checked21 (_h : ∀ k : Fin 275, residualCheck k) : stepBatch 152 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point21_0_0
  · exact _h 131
  · exact point21_0_2
  · exact point21_0_3
  · exact point21_0_4
  · exact _h 132
  · exact _h 133
  · exact point21_0_7
  · exact point21_0_8
  · exact point21_0_9
  · exact point21_0_10
  · exact point21_0_11
  · exact point21_0_12
  · exact _h 134
  · exact point21_0_14
  · exact point21_0_15
  · exact _h 135
  · exact point21_0_17
  · exact point21_0_18
  · exact _h 136
  · exact point21_1_0
  · exact point21_1_1
  · exact point21_1_2
  · exact point21_1_3
  · exact _h 137
  · exact point21_1_5
  · exact point21_1_6
  · exact point21_1_7
  · exact point21_1_8
  · exact point21_1_9
  · exact point21_1_10
  · exact point21_1_11
  · exact point21_1_12
  · exact point21_1_13
  · exact _h 138
  · exact _h 139
  · exact point21_1_16
  · exact _h 140
  · exact _h 141
  · exact _h 142

set_option maxHeartbeats 1600000 in
private theorem point22_0_0 : stepCheck 0 3180 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_1 : stepCheck 0 3181 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_3 : stepCheck 0 3183 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_4 : stepCheck 0 3184 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_6 : stepCheck 0 3186 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_13 : stepCheck 0 3193 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_16 : stepCheck 0 3196 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_17 : stepCheck 0 3197 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_18 : stepCheck 0 3198 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_0_19 : stepCheck 0 3199 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_0 : stepCheck 1 3180 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_1 : stepCheck 1 3181 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_2 : stepCheck 1 3182 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_4 : stepCheck 1 3184 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_5 : stepCheck 1 3185 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_7 : stepCheck 1 3187 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_8 : stepCheck 1 3188 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_10 : stepCheck 1 3190 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_12 : stepCheck 1 3192 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_13 : stepCheck 1 3193 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_14 : stepCheck 1 3194 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point22_1_15 : stepCheck 1 3195 := by
  left
  decide +kernel

private theorem checked22 (_h : ∀ k : Fin 275, residualCheck k) : stepBatch 159 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point22_0_0
  · exact point22_0_1
  · exact _h 143
  · exact point22_0_3
  · exact point22_0_4
  · exact _h 144
  · exact point22_0_6
  · exact _h 145
  · exact _h 146
  · exact _h 147
  · exact _h 148
  · exact _h 149
  · exact _h 150
  · exact point22_0_13
  · exact _h 151
  · exact _h 152
  · exact point22_0_16
  · exact point22_0_17
  · exact point22_0_18
  · exact point22_0_19
  · exact point22_1_0
  · exact point22_1_1
  · exact point22_1_2
  · exact _h 153
  · exact point22_1_4
  · exact point22_1_5
  · exact _h 154
  · exact point22_1_7
  · exact point22_1_8
  · exact _h 155
  · exact point22_1_10
  · exact _h 156
  · exact point22_1_12
  · exact point22_1_13
  · exact point22_1_14
  · exact point22_1_15
  · exact _h 157
  · exact _h 158
  · exact _h 159
  · exact _h 160

set_option maxHeartbeats 1600000 in
private theorem point23_0_0 : stepCheck 0 3320 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_1 : stepCheck 0 3321 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_2 : stepCheck 0 3322 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_4 : stepCheck 0 3324 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_5 : stepCheck 0 3325 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_8 : stepCheck 0 3328 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_10 : stepCheck 0 3330 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_11 : stepCheck 0 3331 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_12 : stepCheck 0 3332 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_14 : stepCheck 0 3334 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_15 : stepCheck 0 3335 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_16 : stepCheck 0 3336 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_17 : stepCheck 0 3337 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_18 : stepCheck 0 3338 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_0_19 : stepCheck 0 3339 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_3 : stepCheck 1 3323 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_7 : stepCheck 1 3327 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_8 : stepCheck 1 3328 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_9 : stepCheck 1 3329 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_11 : stepCheck 1 3331 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_14 : stepCheck 1 3334 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_15 : stepCheck 1 3335 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_16 : stepCheck 1 3336 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_18 : stepCheck 1 3338 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point23_1_19 : stepCheck 1 3339 := by
  left
  decide +kernel

private theorem checked23 (_h : ∀ k : Fin 275, residualCheck k) : stepBatch 166 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point23_0_0
  · exact point23_0_1
  · exact point23_0_2
  · exact _h 161
  · exact point23_0_4
  · exact point23_0_5
  · exact _h 162
  · exact _h 163
  · exact point23_0_8
  · exact _h 164
  · exact point23_0_10
  · exact point23_0_11
  · exact point23_0_12
  · exact _h 165
  · exact point23_0_14
  · exact point23_0_15
  · exact point23_0_16
  · exact point23_0_17
  · exact point23_0_18
  · exact point23_0_19
  · exact _h 166
  · exact _h 167
  · exact _h 168
  · exact point23_1_3
  · exact _h 169
  · exact _h 170
  · exact _h 171
  · exact point23_1_7
  · exact point23_1_8
  · exact point23_1_9
  · exact _h 172
  · exact point23_1_11
  · exact _h 173
  · exact _h 174
  · exact point23_1_14
  · exact point23_1_15
  · exact point23_1_16
  · exact _h 175
  · exact point23_1_18
  · exact point23_1_19

set_option maxHeartbeats 1600000 in
private theorem point24_0_0 : stepCheck 0 3460 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_1 : stepCheck 0 3461 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_2 : stepCheck 0 3462 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_4 : stepCheck 0 3464 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_5 : stepCheck 0 3465 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_6 : stepCheck 0 3466 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_10 : stepCheck 0 3470 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_11 : stepCheck 0 3471 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_12 : stepCheck 0 3472 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_14 : stepCheck 0 3474 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_15 : stepCheck 0 3475 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_17 : stepCheck 0 3477 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_0_19 : stepCheck 0 3479 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_0 : stepCheck 1 3460 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_3 : stepCheck 1 3463 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_4 : stepCheck 1 3464 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_8 : stepCheck 1 3468 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_9 : stepCheck 1 3469 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_11 : stepCheck 1 3471 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_13 : stepCheck 1 3473 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_14 : stepCheck 1 3474 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_16 : stepCheck 1 3476 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_17 : stepCheck 1 3477 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_18 : stepCheck 1 3478 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point24_1_19 : stepCheck 1 3479 := by
  left
  decide +kernel

private theorem checked24 (_h : ∀ k : Fin 275, residualCheck k) : stepBatch 173 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point24_0_0
  · exact point24_0_1
  · exact point24_0_2
  · exact _h 176
  · exact point24_0_4
  · exact point24_0_5
  · exact point24_0_6
  · exact _h 177
  · exact _h 178
  · exact _h 179
  · exact point24_0_10
  · exact point24_0_11
  · exact point24_0_12
  · exact _h 180
  · exact point24_0_14
  · exact point24_0_15
  · exact _h 181
  · exact point24_0_17
  · exact _h 182
  · exact point24_0_19
  · exact point24_1_0
  · exact _h 183
  · exact _h 184
  · exact point24_1_3
  · exact point24_1_4
  · exact _h 185
  · exact _h 186
  · exact _h 187
  · exact point24_1_8
  · exact point24_1_9
  · exact _h 188
  · exact point24_1_11
  · exact _h 189
  · exact point24_1_13
  · exact point24_1_14
  · exact _h 190
  · exact point24_1_16
  · exact point24_1_17
  · exact point24_1_18
  · exact point24_1_19

set_option maxHeartbeats 1600000 in
private theorem point25_0_0 : stepCheck 0 3600 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_2 : stepCheck 0 3602 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_6 : stepCheck 0 3606 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_8 : stepCheck 0 3608 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_10 : stepCheck 0 3610 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_11 : stepCheck 0 3611 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_12 : stepCheck 0 3612 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_14 : stepCheck 0 3614 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_15 : stepCheck 0 3615 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_16 : stepCheck 0 3616 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_0_19 : stepCheck 0 3619 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_0 : stepCheck 1 3600 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_1 : stepCheck 1 3601 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_4 : stepCheck 1 3604 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_5 : stepCheck 1 3605 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_7 : stepCheck 1 3607 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_8 : stepCheck 1 3608 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_11 : stepCheck 1 3611 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_12 : stepCheck 1 3612 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_13 : stepCheck 1 3613 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_17 : stepCheck 1 3617 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point25_1_18 : stepCheck 1 3618 := by
  left
  decide +kernel

private theorem checked25 (_h : ∀ k : Fin 275, residualCheck k) : stepBatch 180 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point25_0_0
  · exact _h 191
  · exact point25_0_2
  · exact _h 192
  · exact _h 193
  · exact _h 194
  · exact point25_0_6
  · exact _h 195
  · exact point25_0_8
  · exact _h 196
  · exact point25_0_10
  · exact point25_0_11
  · exact point25_0_12
  · exact _h 197
  · exact point25_0_14
  · exact point25_0_15
  · exact point25_0_16
  · exact _h 198
  · exact _h 199
  · exact point25_0_19
  · exact point25_1_0
  · exact point25_1_1
  · exact _h 200
  · exact _h 201
  · exact point25_1_4
  · exact point25_1_5
  · exact _h 202
  · exact point25_1_7
  · exact point25_1_8
  · exact _h 203
  · exact _h 204
  · exact point25_1_11
  · exact point25_1_12
  · exact point25_1_13
  · exact _h 205
  · exact _h 206
  · exact _h 207
  · exact point25_1_17
  · exact point25_1_18
  · exact _h 208

set_option maxHeartbeats 1600000 in
private theorem point26_0_0 : stepCheck 0 3740 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_1 : stepCheck 0 3741 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_3 : stepCheck 0 3743 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_5 : stepCheck 0 3745 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_6 : stepCheck 0 3746 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_8 : stepCheck 0 3748 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_12 : stepCheck 0 3752 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_14 : stepCheck 0 3754 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_15 : stepCheck 0 3755 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_0_16 : stepCheck 0 3756 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_1 : stepCheck 1 3741 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_2 : stepCheck 1 3742 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_4 : stepCheck 1 3744 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_7 : stepCheck 1 3747 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_9 : stepCheck 1 3749 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_10 : stepCheck 1 3750 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_11 : stepCheck 1 3751 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_12 : stepCheck 1 3752 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_13 : stepCheck 1 3753 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point26_1_16 : stepCheck 1 3756 := by
  left
  decide +kernel

private theorem checked26 (_h : ∀ k : Fin 275, residualCheck k) : stepBatch 187 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact point26_0_0
  · exact point26_0_1
  · exact _h 209
  · exact point26_0_3
  · exact _h 210
  · exact point26_0_5
  · exact point26_0_6
  · exact _h 211
  · exact point26_0_8
  · exact _h 212
  · exact _h 213
  · exact _h 214
  · exact point26_0_12
  · exact _h 215
  · exact point26_0_14
  · exact point26_0_15
  · exact point26_0_16
  · exact _h 216
  · exact _h 217
  · exact _h 218
  · exact _h 219
  · exact point26_1_1
  · exact point26_1_2
  · exact _h 220
  · exact point26_1_4
  · exact _h 221
  · exact _h 222
  · exact point26_1_7
  · exact _h 223
  · exact point26_1_9
  · exact point26_1_10
  · exact point26_1_11
  · exact point26_1_12
  · exact point26_1_13
  · exact _h 224
  · exact _h 225
  · exact point26_1_16
  · exact _h 226
  · exact _h 227
  · exact _h 228

set_option maxHeartbeats 1600000 in
private theorem point27_0_2 : stepCheck 0 3882 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_3 : stepCheck 0 3883 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_5 : stepCheck 0 3885 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_6 : stepCheck 0 3886 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_8 : stepCheck 0 3888 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_9 : stepCheck 0 3889 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_11 : stepCheck 0 3891 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_12 : stepCheck 0 3892 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_15 : stepCheck 0 3895 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_0_18 : stepCheck 0 3898 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_1 : stepCheck 1 3881 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_2 : stepCheck 1 3882 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_4 : stepCheck 1 3884 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_7 : stepCheck 1 3887 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_10 : stepCheck 1 3890 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point27_1_15 : stepCheck 1 3895 := by
  left
  decide +kernel

private theorem checked27 (_h : ∀ k : Fin 275, residualCheck k) : stepBatch 194 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact _h 229
  · exact _h 230
  · exact point27_0_2
  · exact point27_0_3
  · exact _h 231
  · exact point27_0_5
  · exact point27_0_6
  · exact _h 232
  · exact point27_0_8
  · exact point27_0_9
  · exact _h 233
  · exact point27_0_11
  · exact point27_0_12
  · exact _h 234
  · exact _h 235
  · exact point27_0_15
  · exact _h 236
  · exact _h 237
  · exact point27_0_18
  · exact _h 238
  · exact _h 239
  · exact point27_1_1
  · exact point27_1_2
  · exact _h 240
  · exact point27_1_4
  · exact _h 241
  · exact _h 242
  · exact point27_1_7
  · exact _h 243
  · exact _h 244
  · exact point27_1_10
  · exact _h 245
  · exact _h 246
  · exact _h 247
  · exact _h 248
  · exact point27_1_15
  · exact _h 249
  · exact _h 250
  · exact _h 251
  · exact _h 252

set_option maxHeartbeats 1600000 in
private theorem point28_0_2 : stepCheck 0 4022 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_7 : stepCheck 0 4027 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_8 : stepCheck 0 4028 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_9 : stepCheck 0 4029 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_10 : stepCheck 0 4030 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_11 : stepCheck 0 4031 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_12 : stepCheck 0 4032 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_13 : stepCheck 0 4033 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_15 : stepCheck 0 4035 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_16 : stepCheck 0 4036 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_0_19 : stepCheck 0 4039 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_0 : stepCheck 1 4020 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_4 : stepCheck 1 4024 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_6 : stepCheck 1 4026 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_13 : stepCheck 1 4033 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_14 : stepCheck 1 4034 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_17 : stepCheck 1 4037 := by
  left
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem point28_1_18 : stepCheck 1 4038 := by
  left
  decide +kernel

private theorem checked28 (_h : ∀ k : Fin 275, residualCheck k) : stepBatch 201 := by
  apply ofStepBatchCheck
  intro i r
  fin_cases i <;> fin_cases r
  · exact _h 253
  · exact _h 254
  · exact point28_0_2
  · exact _h 255
  · exact _h 256
  · exact _h 257
  · exact _h 258
  · exact point28_0_7
  · exact point28_0_8
  · exact point28_0_9
  · exact point28_0_10
  · exact point28_0_11
  · exact point28_0_12
  · exact point28_0_13
  · exact _h 259
  · exact point28_0_15
  · exact point28_0_16
  · exact _h 260
  · exact _h 261
  · exact point28_0_19
  · exact point28_1_0
  · exact _h 262
  · exact _h 263
  · exact _h 264
  · exact point28_1_4
  · exact _h 265
  · exact point28_1_6
  · exact _h 266
  · exact _h 267
  · exact _h 268
  · exact _h 269
  · exact _h 270
  · exact _h 271
  · exact point28_1_13
  · exact point28_1_14
  · exact _h 272
  · exact _h 273
  · exact point28_1_17
  · exact point28_1_18
  · exact _h 274

/-- The algebraic transitions leave precisely the explicit residual checks. -/
public theorem part5_of_residual (h : ∀ k : Fin 275, residualCheck k) (b : Fin 29) :
    stepBatch ⟨7 * b.val + 5, by omega⟩ := by
  fin_cases b
  · exact part5_checked0
  · exact part5_checked1
  · exact part5_checked2
  · exact part5_checked3
  · exact part5_checked4
  · exact part5_checked5
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

/-- Four independent residual certificates complete part 5. -/
public theorem part5_of_batches (h : ∀ g : Fin 4, residualBatch g) (b : Fin 29) :
    stepBatch ⟨7 * b.val + 5, by omega⟩ :=
  part5_of_residual (all_of_batches h) b

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual
