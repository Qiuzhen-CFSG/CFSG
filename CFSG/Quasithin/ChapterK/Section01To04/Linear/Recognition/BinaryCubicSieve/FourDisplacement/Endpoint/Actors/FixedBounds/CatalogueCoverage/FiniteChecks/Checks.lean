module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Actors.FixedBounds.CatalogueCoverage.FiniteChecks.Data

/-!
# Kernel-checked finite extensions and conjugates

The square-zero condition is checked once. For each elementary row we then
check its supplied extension indices and its supplied conjugator. Bounded
decision procedures examine only members of each finite set. The checks use
the exact published code operations; the generating data are not trusted.

Source: Guralnick–Malle, Classification of 2F-modules II, Lemma 4.5 and Proposition 4.8 step 3A; Aschbacher–Smith K.3.2, printed pp.454–455.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.FixedBounds
namespace FiniteChecks

theorem mem_involutions_iff : ∀ c : Code, c ∈ involutions ↔ CoverageCode.mul c c = 0 := by
  decide +kernel

def ExtensionCheck (i : Fin 241) : Prop :=
  ∀ c ∈ involutions, (∀ a ∈ elementaryRows i, CoverageCode.mul c a = CoverageCode.mul a c) →
    elementaryRows (nextRow i c) = elementaryRows i ∪ (elementaryRows i).image (CoverageCode.mul c)

local instance boundedCommute (s : Finset Code) (c : Code) :
    Decidable (∀ a ∈ s, CoverageCode.mul c a = CoverageCode.mul a c) :=
  Finset.decidableDforallFinset

instance extensionDecidable (i : Fin 241) : Decidable (ExtensionCheck i) :=
  Finset.decidableDforallFinset

def ConjugacyCheck (i : Fin 241) : Prop :=
  elementaryRows i ≠ {0} →
    (elementaryRows i).image (CoverageCode.conj (conjugateWitness i).2) =
      CoverageCode.products 0 CoverageCode.mul (catalogueGenerators (conjugateWitness i).1)

instance conjugacyDecidable (i : Fin 241) : Decidable (ConjugacyCheck i) :=
  inferInstanceAs (Decidable (_ → _))

def RowCheck (i : Fin 241) : Prop := ExtensionCheck i ∧ ConjugacyCheck i

instance rowDecidable (i : Fin 241) : Decidable (RowCheck i) :=
  inferInstanceAs (Decidable (_ ∧ _))

-- Keep the measured kernel checks sequential, so their reduction caches do
-- not accumulate across concurrent declarations. Lean thread settings are unchanged.
set_option Elab.async false

theorem checked000 : RowCheck 0 := by decide +kernel
theorem checked001 : RowCheck 1 := by decide +kernel
theorem checked002 : RowCheck 2 := by decide +kernel
theorem checked003 : RowCheck 3 := by decide +kernel
theorem checked004 : RowCheck 4 := by decide +kernel
theorem checked005 : RowCheck 5 := by decide +kernel
theorem checked006 : RowCheck 6 := by decide +kernel
theorem checked007 : RowCheck 7 := by decide +kernel
theorem checked008 : RowCheck 8 := by decide +kernel
theorem checked009 : RowCheck 9 := by decide +kernel
theorem checked010 : RowCheck 10 := by decide +kernel
theorem checked011 : RowCheck 11 := by decide +kernel
theorem checked012 : RowCheck 12 := by decide +kernel
theorem checked013 : RowCheck 13 := by decide +kernel
theorem checked014 : RowCheck 14 := by decide +kernel
theorem checked015 : RowCheck 15 := by decide +kernel
theorem checked016 : RowCheck 16 := by decide +kernel
theorem checked017 : RowCheck 17 := by decide +kernel
theorem checked018 : RowCheck 18 := by decide +kernel
theorem checked019 : RowCheck 19 := by decide +kernel
theorem checked020 : RowCheck 20 := by decide +kernel
theorem checked021 : RowCheck 21 := by decide +kernel
theorem checked022 : RowCheck 22 := by decide +kernel
theorem checked023 : RowCheck 23 := by decide +kernel
theorem checked024 : RowCheck 24 := by decide +kernel
theorem checked025 : RowCheck 25 := by decide +kernel
theorem checked026 : RowCheck 26 := by decide +kernel
theorem checked027 : RowCheck 27 := by decide +kernel
theorem checked028 : RowCheck 28 := by decide +kernel
theorem checked029 : RowCheck 29 := by decide +kernel
theorem checked030 : RowCheck 30 := by decide +kernel
theorem checked031 : RowCheck 31 := by decide +kernel
theorem checked032 : RowCheck 32 := by decide +kernel
theorem checked033 : RowCheck 33 := by decide +kernel
theorem checked034 : RowCheck 34 := by decide +kernel
theorem checked035 : RowCheck 35 := by decide +kernel
theorem checked036 : RowCheck 36 := by decide +kernel
theorem checked037 : RowCheck 37 := by decide +kernel
theorem checked038 : RowCheck 38 := by decide +kernel
theorem checked039 : RowCheck 39 := by decide +kernel
theorem checked040 : RowCheck 40 := by decide +kernel
theorem checked041 : RowCheck 41 := by decide +kernel
theorem checked042 : RowCheck 42 := by decide +kernel
theorem checked043 : RowCheck 43 := by decide +kernel
theorem checked044 : RowCheck 44 := by decide +kernel
theorem checked045 : RowCheck 45 := by decide +kernel
theorem checked046 : RowCheck 46 := by decide +kernel
theorem checked047 : RowCheck 47 := by decide +kernel
theorem checked048 : RowCheck 48 := by decide +kernel
theorem checked049 : RowCheck 49 := by decide +kernel
theorem checked050 : RowCheck 50 := by decide +kernel
theorem checked051 : RowCheck 51 := by decide +kernel
theorem checked052 : RowCheck 52 := by decide +kernel
theorem checked053 : RowCheck 53 := by decide +kernel
theorem checked054 : RowCheck 54 := by decide +kernel
theorem checked055 : RowCheck 55 := by decide +kernel
theorem checked056 : RowCheck 56 := by decide +kernel
theorem checked057 : RowCheck 57 := by decide +kernel
theorem checked058 : RowCheck 58 := by decide +kernel
theorem checked059 : RowCheck 59 := by decide +kernel
theorem checked060 : RowCheck 60 := by decide +kernel
theorem checked061 : RowCheck 61 := by decide +kernel
theorem checked062 : RowCheck 62 := by decide +kernel
theorem checked063 : RowCheck 63 := by decide +kernel
theorem checked064 : RowCheck 64 := by decide +kernel
theorem checked065 : RowCheck 65 := by decide +kernel
theorem checked066 : RowCheck 66 := by decide +kernel
theorem checked067 : RowCheck 67 := by decide +kernel
theorem checked068 : RowCheck 68 := by decide +kernel
theorem checked069 : RowCheck 69 := by decide +kernel
theorem checked070 : RowCheck 70 := by decide +kernel
theorem checked071 : RowCheck 71 := by decide +kernel
theorem checked072 : RowCheck 72 := by decide +kernel
theorem checked073 : RowCheck 73 := by decide +kernel
theorem checked074 : RowCheck 74 := by decide +kernel
theorem checked075 : RowCheck 75 := by decide +kernel
theorem checked076 : RowCheck 76 := by decide +kernel
theorem checked077 : RowCheck 77 := by decide +kernel
theorem checked078 : RowCheck 78 := by decide +kernel
theorem checked079 : RowCheck 79 := by decide +kernel
theorem checked080 : RowCheck 80 := by decide +kernel
theorem checked081 : RowCheck 81 := by decide +kernel
theorem checked082 : RowCheck 82 := by decide +kernel
theorem checked083 : RowCheck 83 := by decide +kernel
theorem checked084 : RowCheck 84 := by decide +kernel
theorem checked085 : RowCheck 85 := by decide +kernel
theorem checked086 : RowCheck 86 := by decide +kernel
theorem checked087 : RowCheck 87 := by decide +kernel
theorem checked088 : RowCheck 88 := by decide +kernel
theorem checked089 : RowCheck 89 := by decide +kernel
theorem checked090 : RowCheck 90 := by decide +kernel
theorem checked091 : RowCheck 91 := by decide +kernel
theorem checked092 : RowCheck 92 := by decide +kernel
theorem checked093 : RowCheck 93 := by decide +kernel
theorem checked094 : RowCheck 94 := by decide +kernel
theorem checked095 : RowCheck 95 := by decide +kernel
theorem checked096 : RowCheck 96 := by decide +kernel
theorem checked097 : RowCheck 97 := by decide +kernel
theorem checked098 : RowCheck 98 := by decide +kernel
theorem checked099 : RowCheck 99 := by decide +kernel
theorem checked100 : RowCheck 100 := by decide +kernel
theorem checked101 : RowCheck 101 := by decide +kernel
theorem checked102 : RowCheck 102 := by decide +kernel
theorem checked103 : RowCheck 103 := by decide +kernel
theorem checked104 : RowCheck 104 := by decide +kernel
theorem checked105 : RowCheck 105 := by decide +kernel
theorem checked106 : RowCheck 106 := by decide +kernel
theorem checked107 : RowCheck 107 := by decide +kernel
theorem checked108 : RowCheck 108 := by decide +kernel
theorem checked109 : RowCheck 109 := by decide +kernel
theorem checked110 : RowCheck 110 := by decide +kernel
theorem checked111 : RowCheck 111 := by decide +kernel
theorem checked112 : RowCheck 112 := by decide +kernel
theorem checked113 : RowCheck 113 := by decide +kernel
theorem checked114 : RowCheck 114 := by decide +kernel
theorem checked115 : RowCheck 115 := by decide +kernel
theorem checked116 : RowCheck 116 := by decide +kernel
theorem checked117 : RowCheck 117 := by decide +kernel
theorem checked118 : RowCheck 118 := by decide +kernel
theorem checked119 : RowCheck 119 := by decide +kernel
theorem checked120 : RowCheck 120 := by decide +kernel
theorem checked121 : RowCheck 121 := by decide +kernel
theorem checked122 : RowCheck 122 := by decide +kernel
theorem checked123 : RowCheck 123 := by decide +kernel
theorem checked124 : RowCheck 124 := by decide +kernel
theorem checked125 : RowCheck 125 := by decide +kernel
theorem checked126 : RowCheck 126 := by decide +kernel
theorem checked127 : RowCheck 127 := by decide +kernel
theorem checked128 : RowCheck 128 := by decide +kernel
theorem checked129 : RowCheck 129 := by decide +kernel
theorem checked130 : RowCheck 130 := by decide +kernel
theorem checked131 : RowCheck 131 := by decide +kernel
theorem checked132 : RowCheck 132 := by decide +kernel
theorem checked133 : RowCheck 133 := by decide +kernel
theorem checked134 : RowCheck 134 := by decide +kernel
theorem checked135 : RowCheck 135 := by decide +kernel
theorem checked136 : RowCheck 136 := by decide +kernel
theorem checked137 : RowCheck 137 := by decide +kernel
theorem checked138 : RowCheck 138 := by decide +kernel
theorem checked139 : RowCheck 139 := by decide +kernel
theorem checked140 : RowCheck 140 := by decide +kernel
theorem checked141 : RowCheck 141 := by decide +kernel
theorem checked142 : RowCheck 142 := by decide +kernel
theorem checked143 : RowCheck 143 := by decide +kernel
theorem checked144 : RowCheck 144 := by decide +kernel
theorem checked145 : RowCheck 145 := by decide +kernel
theorem checked146 : RowCheck 146 := by decide +kernel
theorem checked147 : RowCheck 147 := by decide +kernel
theorem checked148 : RowCheck 148 := by decide +kernel
theorem checked149 : RowCheck 149 := by decide +kernel
theorem checked150 : RowCheck 150 := by decide +kernel
theorem checked151 : RowCheck 151 := by decide +kernel
theorem checked152 : RowCheck 152 := by decide +kernel
theorem checked153 : RowCheck 153 := by decide +kernel
theorem checked154 : RowCheck 154 := by decide +kernel
theorem checked155 : RowCheck 155 := by decide +kernel
theorem checked156 : RowCheck 156 := by decide +kernel
theorem checked157 : RowCheck 157 := by decide +kernel
theorem checked158 : RowCheck 158 := by decide +kernel
theorem checked159 : RowCheck 159 := by decide +kernel
theorem checked160 : RowCheck 160 := by decide +kernel
theorem checked161 : RowCheck 161 := by decide +kernel
theorem checked162 : RowCheck 162 := by decide +kernel
theorem checked163 : RowCheck 163 := by decide +kernel
theorem checked164 : RowCheck 164 := by decide +kernel
theorem checked165 : RowCheck 165 := by decide +kernel
theorem checked166 : RowCheck 166 := by decide +kernel
theorem checked167 : RowCheck 167 := by decide +kernel
theorem checked168 : RowCheck 168 := by decide +kernel
theorem checked169 : RowCheck 169 := by decide +kernel
theorem checked170 : RowCheck 170 := by decide +kernel
theorem checked171 : RowCheck 171 := by decide +kernel
theorem checked172 : RowCheck 172 := by decide +kernel
theorem checked173 : RowCheck 173 := by decide +kernel
theorem checked174 : RowCheck 174 := by decide +kernel
theorem checked175 : RowCheck 175 := by decide +kernel
theorem checked176 : RowCheck 176 := by decide +kernel
theorem checked177 : RowCheck 177 := by decide +kernel
theorem checked178 : RowCheck 178 := by decide +kernel
theorem checked179 : RowCheck 179 := by decide +kernel
theorem checked180 : RowCheck 180 := by decide +kernel
theorem checked181 : RowCheck 181 := by decide +kernel
theorem checked182 : RowCheck 182 := by decide +kernel
theorem checked183 : RowCheck 183 := by decide +kernel
theorem checked184 : RowCheck 184 := by decide +kernel
theorem checked185 : RowCheck 185 := by decide +kernel
theorem checked186 : RowCheck 186 := by decide +kernel
theorem checked187 : RowCheck 187 := by decide +kernel
theorem checked188 : RowCheck 188 := by decide +kernel
theorem checked189 : RowCheck 189 := by decide +kernel
theorem checked190 : RowCheck 190 := by decide +kernel
theorem checked191 : RowCheck 191 := by decide +kernel
theorem checked192 : RowCheck 192 := by decide +kernel
theorem checked193 : RowCheck 193 := by decide +kernel
theorem checked194 : RowCheck 194 := by decide +kernel
theorem checked195 : RowCheck 195 := by decide +kernel
theorem checked196 : RowCheck 196 := by decide +kernel
theorem checked197 : RowCheck 197 := by decide +kernel
theorem checked198 : RowCheck 198 := by decide +kernel
theorem checked199 : RowCheck 199 := by decide +kernel
theorem checked200 : RowCheck 200 := by decide +kernel
theorem checked201 : RowCheck 201 := by decide +kernel
theorem checked202 : RowCheck 202 := by decide +kernel
theorem checked203 : RowCheck 203 := by decide +kernel
theorem checked204 : RowCheck 204 := by decide +kernel
theorem checked205 : RowCheck 205 := by decide +kernel
theorem checked206 : RowCheck 206 := by decide +kernel
theorem checked207 : RowCheck 207 := by decide +kernel
theorem checked208 : RowCheck 208 := by decide +kernel
theorem checked209 : RowCheck 209 := by decide +kernel
theorem checked210 : RowCheck 210 := by decide +kernel
theorem checked211 : RowCheck 211 := by decide +kernel
theorem checked212 : RowCheck 212 := by decide +kernel
theorem checked213 : RowCheck 213 := by decide +kernel
theorem checked214 : RowCheck 214 := by decide +kernel
theorem checked215 : RowCheck 215 := by decide +kernel
theorem checked216 : RowCheck 216 := by decide +kernel
theorem checked217 : RowCheck 217 := by decide +kernel
theorem checked218 : RowCheck 218 := by decide +kernel
theorem checked219 : RowCheck 219 := by decide +kernel
theorem checked220 : RowCheck 220 := by decide +kernel
theorem checked221 : RowCheck 221 := by decide +kernel
theorem checked222 : RowCheck 222 := by decide +kernel
theorem checked223 : RowCheck 223 := by decide +kernel
theorem checked224 : RowCheck 224 := by decide +kernel
theorem checked225 : RowCheck 225 := by decide +kernel
theorem checked226 : RowCheck 226 := by decide +kernel
theorem checked227 : RowCheck 227 := by decide +kernel
theorem checked228 : RowCheck 228 := by decide +kernel
theorem checked229 : RowCheck 229 := by decide +kernel
theorem checked230 : RowCheck 230 := by decide +kernel
theorem checked231 : RowCheck 231 := by decide +kernel
theorem checked232 : RowCheck 232 := by decide +kernel
theorem checked233 : RowCheck 233 := by decide +kernel
theorem checked234 : RowCheck 234 := by decide +kernel
theorem checked235 : RowCheck 235 := by decide +kernel
theorem checked236 : RowCheck 236 := by decide +kernel
theorem checked237 : RowCheck 237 := by decide +kernel
theorem checked238 : RowCheck 238 := by decide +kernel
theorem checked239 : RowCheck 239 := by decide +kernel
theorem checked240 : RowCheck 240 := by decide +kernel

theorem range000 (k : Fin 16) : RowCheck (Fin.ofNat 241 (0 + k.val)) := by
  fin_cases k
  · exact checked000
  · exact checked001
  · exact checked002
  · exact checked003
  · exact checked004
  · exact checked005
  · exact checked006
  · exact checked007
  · exact checked008
  · exact checked009
  · exact checked010
  · exact checked011
  · exact checked012
  · exact checked013
  · exact checked014
  · exact checked015

theorem range016 (k : Fin 16) : RowCheck (Fin.ofNat 241 (16 + k.val)) := by
  fin_cases k
  · exact checked016
  · exact checked017
  · exact checked018
  · exact checked019
  · exact checked020
  · exact checked021
  · exact checked022
  · exact checked023
  · exact checked024
  · exact checked025
  · exact checked026
  · exact checked027
  · exact checked028
  · exact checked029
  · exact checked030
  · exact checked031

theorem range032 (k : Fin 16) : RowCheck (Fin.ofNat 241 (32 + k.val)) := by
  fin_cases k
  · exact checked032
  · exact checked033
  · exact checked034
  · exact checked035
  · exact checked036
  · exact checked037
  · exact checked038
  · exact checked039
  · exact checked040
  · exact checked041
  · exact checked042
  · exact checked043
  · exact checked044
  · exact checked045
  · exact checked046
  · exact checked047

theorem range048 (k : Fin 16) : RowCheck (Fin.ofNat 241 (48 + k.val)) := by
  fin_cases k
  · exact checked048
  · exact checked049
  · exact checked050
  · exact checked051
  · exact checked052
  · exact checked053
  · exact checked054
  · exact checked055
  · exact checked056
  · exact checked057
  · exact checked058
  · exact checked059
  · exact checked060
  · exact checked061
  · exact checked062
  · exact checked063

theorem range064 (k : Fin 16) : RowCheck (Fin.ofNat 241 (64 + k.val)) := by
  fin_cases k
  · exact checked064
  · exact checked065
  · exact checked066
  · exact checked067
  · exact checked068
  · exact checked069
  · exact checked070
  · exact checked071
  · exact checked072
  · exact checked073
  · exact checked074
  · exact checked075
  · exact checked076
  · exact checked077
  · exact checked078
  · exact checked079

theorem range080 (k : Fin 16) : RowCheck (Fin.ofNat 241 (80 + k.val)) := by
  fin_cases k
  · exact checked080
  · exact checked081
  · exact checked082
  · exact checked083
  · exact checked084
  · exact checked085
  · exact checked086
  · exact checked087
  · exact checked088
  · exact checked089
  · exact checked090
  · exact checked091
  · exact checked092
  · exact checked093
  · exact checked094
  · exact checked095

theorem range096 (k : Fin 16) : RowCheck (Fin.ofNat 241 (96 + k.val)) := by
  fin_cases k
  · exact checked096
  · exact checked097
  · exact checked098
  · exact checked099
  · exact checked100
  · exact checked101
  · exact checked102
  · exact checked103
  · exact checked104
  · exact checked105
  · exact checked106
  · exact checked107
  · exact checked108
  · exact checked109
  · exact checked110
  · exact checked111

theorem range112 (k : Fin 16) : RowCheck (Fin.ofNat 241 (112 + k.val)) := by
  fin_cases k
  · exact checked112
  · exact checked113
  · exact checked114
  · exact checked115
  · exact checked116
  · exact checked117
  · exact checked118
  · exact checked119
  · exact checked120
  · exact checked121
  · exact checked122
  · exact checked123
  · exact checked124
  · exact checked125
  · exact checked126
  · exact checked127

theorem range128 (k : Fin 16) : RowCheck (Fin.ofNat 241 (128 + k.val)) := by
  fin_cases k
  · exact checked128
  · exact checked129
  · exact checked130
  · exact checked131
  · exact checked132
  · exact checked133
  · exact checked134
  · exact checked135
  · exact checked136
  · exact checked137
  · exact checked138
  · exact checked139
  · exact checked140
  · exact checked141
  · exact checked142
  · exact checked143

theorem range144 (k : Fin 16) : RowCheck (Fin.ofNat 241 (144 + k.val)) := by
  fin_cases k
  · exact checked144
  · exact checked145
  · exact checked146
  · exact checked147
  · exact checked148
  · exact checked149
  · exact checked150
  · exact checked151
  · exact checked152
  · exact checked153
  · exact checked154
  · exact checked155
  · exact checked156
  · exact checked157
  · exact checked158
  · exact checked159

theorem range160 (k : Fin 16) : RowCheck (Fin.ofNat 241 (160 + k.val)) := by
  fin_cases k
  · exact checked160
  · exact checked161
  · exact checked162
  · exact checked163
  · exact checked164
  · exact checked165
  · exact checked166
  · exact checked167
  · exact checked168
  · exact checked169
  · exact checked170
  · exact checked171
  · exact checked172
  · exact checked173
  · exact checked174
  · exact checked175

theorem range176 (k : Fin 16) : RowCheck (Fin.ofNat 241 (176 + k.val)) := by
  fin_cases k
  · exact checked176
  · exact checked177
  · exact checked178
  · exact checked179
  · exact checked180
  · exact checked181
  · exact checked182
  · exact checked183
  · exact checked184
  · exact checked185
  · exact checked186
  · exact checked187
  · exact checked188
  · exact checked189
  · exact checked190
  · exact checked191

theorem range192 (k : Fin 16) : RowCheck (Fin.ofNat 241 (192 + k.val)) := by
  fin_cases k
  · exact checked192
  · exact checked193
  · exact checked194
  · exact checked195
  · exact checked196
  · exact checked197
  · exact checked198
  · exact checked199
  · exact checked200
  · exact checked201
  · exact checked202
  · exact checked203
  · exact checked204
  · exact checked205
  · exact checked206
  · exact checked207

theorem range208 (k : Fin 16) : RowCheck (Fin.ofNat 241 (208 + k.val)) := by
  fin_cases k
  · exact checked208
  · exact checked209
  · exact checked210
  · exact checked211
  · exact checked212
  · exact checked213
  · exact checked214
  · exact checked215
  · exact checked216
  · exact checked217
  · exact checked218
  · exact checked219
  · exact checked220
  · exact checked221
  · exact checked222
  · exact checked223

theorem range224 (k : Fin 16) : RowCheck (Fin.ofNat 241 (224 + k.val)) := by
  fin_cases k
  · exact checked224
  · exact checked225
  · exact checked226
  · exact checked227
  · exact checked228
  · exact checked229
  · exact checked230
  · exact checked231
  · exact checked232
  · exact checked233
  · exact checked234
  · exact checked235
  · exact checked236
  · exact checked237
  · exact checked238
  · exact checked239

theorem range240 (k : Fin 1) : RowCheck (Fin.ofNat 241 (240 + k.val)) := by
  fin_cases k
  · exact checked240

private theorem of_range {P : Fin 241 → Prop} (start count : Nat)
    (h : ∀ k : Fin count, P (Fin.ofNat 241 (start + k.val)))
    (i : Fin 241) (hlo : start ≤ i.val) (hhi : i.val < start + count) : P i := by
  let k : Fin count := ⟨i.val - start, by omega⟩
  have hk : Fin.ofNat 241 (start + k.val) = i := by
    apply Fin.ext
    change (start + (i.val - start)) % 241 = i.val
    rw [Nat.add_sub_of_le hlo, Nat.mod_eq_of_lt i.isLt]
  exact hk ▸ h k

theorem all_checked (i : Fin 241) : RowCheck i := by
  by_cases h16 : i.val < 16
  · exact of_range 0 16 range000 i (by omega) (by omega)
  by_cases h32 : i.val < 32
  · exact of_range 16 16 range016 i (by omega) (by omega)
  by_cases h48 : i.val < 48
  · exact of_range 32 16 range032 i (by omega) (by omega)
  by_cases h64 : i.val < 64
  · exact of_range 48 16 range048 i (by omega) (by omega)
  by_cases h80 : i.val < 80
  · exact of_range 64 16 range064 i (by omega) (by omega)
  by_cases h96 : i.val < 96
  · exact of_range 80 16 range080 i (by omega) (by omega)
  by_cases h112 : i.val < 112
  · exact of_range 96 16 range096 i (by omega) (by omega)
  by_cases h128 : i.val < 128
  · exact of_range 112 16 range112 i (by omega) (by omega)
  by_cases h144 : i.val < 144
  · exact of_range 128 16 range128 i (by omega) (by omega)
  by_cases h160 : i.val < 160
  · exact of_range 144 16 range144 i (by omega) (by omega)
  by_cases h176 : i.val < 176
  · exact of_range 160 16 range160 i (by omega) (by omega)
  by_cases h192 : i.val < 192
  · exact of_range 176 16 range176 i (by omega) (by omega)
  by_cases h208 : i.val < 208
  · exact of_range 192 16 range192 i (by omega) (by omega)
  by_cases h224 : i.val < 224
  · exact of_range 208 16 range208 i (by omega) (by omega)
  by_cases h240 : i.val < 240
  · exact of_range 224 16 range224 i (by omega) (by omega)
  exact of_range 240 1 range240 i (by omega) (by omega)
end FiniteChecks

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.FixedBounds
