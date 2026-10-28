module

public import Theory.SpecificGroups.Lyons.Atlas111LocalPresentationSetup
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationData0
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationData1
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationData2
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationData3
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationData4
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationData5
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationData6

/-!
# Arithmetic contracts for the 22 local presentation relations

The matrices and multiplication lists are candidates. The contracts below
state exactly the numerical identities required by the conditional assembly.
Their definitions make no group identification or order assumption.

Source and reproducible candidate generation: `Atlas111LocalRelationSource/`.
-/

namespace Lyons.RelationCertificate
open OrderCertificate

@[expose] public def matrixRows (i : Fin 261) : Rows :=
  if i.val < 130 then
    if i.val < 65 then
      if i.val < 32 then
        if i.val < 16 then
          if i.val < 8 then
            if i.val < 4 then
              if i.val < 2 then
                if i.val < 1 then
                  m0
                else
                  m1
              else
                if i.val < 3 then
                  m2
                else
                  m3
            else
              if i.val < 6 then
                if i.val < 5 then
                  m4
                else
                  m5
              else
                if i.val < 7 then
                  m6
                else
                  m7
          else
            if i.val < 12 then
              if i.val < 10 then
                if i.val < 9 then
                  m8
                else
                  m9
              else
                if i.val < 11 then
                  m10
                else
                  m11
            else
              if i.val < 14 then
                if i.val < 13 then
                  m12
                else
                  m13
              else
                if i.val < 15 then
                  m14
                else
                  m15
        else
          if i.val < 24 then
            if i.val < 20 then
              if i.val < 18 then
                if i.val < 17 then
                  m16
                else
                  m17
              else
                if i.val < 19 then
                  m18
                else
                  m19
            else
              if i.val < 22 then
                if i.val < 21 then
                  m20
                else
                  m21
              else
                if i.val < 23 then
                  m22
                else
                  m23
          else
            if i.val < 28 then
              if i.val < 26 then
                if i.val < 25 then
                  m24
                else
                  m25
              else
                if i.val < 27 then
                  m26
                else
                  m27
            else
              if i.val < 30 then
                if i.val < 29 then
                  m28
                else
                  m29
              else
                if i.val < 31 then
                  m30
                else
                  m31
      else
        if i.val < 48 then
          if i.val < 40 then
            if i.val < 36 then
              if i.val < 34 then
                if i.val < 33 then
                  m32
                else
                  m33
              else
                if i.val < 35 then
                  m34
                else
                  m35
            else
              if i.val < 38 then
                if i.val < 37 then
                  m36
                else
                  m37
              else
                if i.val < 39 then
                  m38
                else
                  m39
          else
            if i.val < 44 then
              if i.val < 42 then
                if i.val < 41 then
                  m40
                else
                  m41
              else
                if i.val < 43 then
                  m42
                else
                  m43
            else
              if i.val < 46 then
                if i.val < 45 then
                  m44
                else
                  m45
              else
                if i.val < 47 then
                  m46
                else
                  m47
        else
          if i.val < 56 then
            if i.val < 52 then
              if i.val < 50 then
                if i.val < 49 then
                  m48
                else
                  m49
              else
                if i.val < 51 then
                  m50
                else
                  m51
            else
              if i.val < 54 then
                if i.val < 53 then
                  m52
                else
                  m53
              else
                if i.val < 55 then
                  m54
                else
                  m55
          else
            if i.val < 60 then
              if i.val < 58 then
                if i.val < 57 then
                  m56
                else
                  m57
              else
                if i.val < 59 then
                  m58
                else
                  m59
            else
              if i.val < 62 then
                if i.val < 61 then
                  m60
                else
                  m61
              else
                if i.val < 63 then
                  m62
                else
                  if i.val < 64 then
                    m63
                  else
                    m64
    else
      if i.val < 97 then
        if i.val < 81 then
          if i.val < 73 then
            if i.val < 69 then
              if i.val < 67 then
                if i.val < 66 then
                  m65
                else
                  m66
              else
                if i.val < 68 then
                  m67
                else
                  m68
            else
              if i.val < 71 then
                if i.val < 70 then
                  m69
                else
                  m70
              else
                if i.val < 72 then
                  m71
                else
                  m72
          else
            if i.val < 77 then
              if i.val < 75 then
                if i.val < 74 then
                  m73
                else
                  m74
              else
                if i.val < 76 then
                  m75
                else
                  m76
            else
              if i.val < 79 then
                if i.val < 78 then
                  m77
                else
                  m78
              else
                if i.val < 80 then
                  m79
                else
                  m80
        else
          if i.val < 89 then
            if i.val < 85 then
              if i.val < 83 then
                if i.val < 82 then
                  m81
                else
                  m82
              else
                if i.val < 84 then
                  m83
                else
                  m84
            else
              if i.val < 87 then
                if i.val < 86 then
                  m85
                else
                  m86
              else
                if i.val < 88 then
                  m87
                else
                  m88
          else
            if i.val < 93 then
              if i.val < 91 then
                if i.val < 90 then
                  m89
                else
                  m90
              else
                if i.val < 92 then
                  m91
                else
                  m92
            else
              if i.val < 95 then
                if i.val < 94 then
                  m93
                else
                  m94
              else
                if i.val < 96 then
                  m95
                else
                  m96
      else
        if i.val < 113 then
          if i.val < 105 then
            if i.val < 101 then
              if i.val < 99 then
                if i.val < 98 then
                  m97
                else
                  m98
              else
                if i.val < 100 then
                  m99
                else
                  m100
            else
              if i.val < 103 then
                if i.val < 102 then
                  m101
                else
                  m102
              else
                if i.val < 104 then
                  m103
                else
                  m104
          else
            if i.val < 109 then
              if i.val < 107 then
                if i.val < 106 then
                  m105
                else
                  m106
              else
                if i.val < 108 then
                  m107
                else
                  m108
            else
              if i.val < 111 then
                if i.val < 110 then
                  m109
                else
                  m110
              else
                if i.val < 112 then
                  m111
                else
                  m112
        else
          if i.val < 121 then
            if i.val < 117 then
              if i.val < 115 then
                if i.val < 114 then
                  m113
                else
                  m114
              else
                if i.val < 116 then
                  m115
                else
                  m116
            else
              if i.val < 119 then
                if i.val < 118 then
                  m117
                else
                  m118
              else
                if i.val < 120 then
                  m119
                else
                  m120
          else
            if i.val < 125 then
              if i.val < 123 then
                if i.val < 122 then
                  m121
                else
                  m122
              else
                if i.val < 124 then
                  m123
                else
                  m124
            else
              if i.val < 127 then
                if i.val < 126 then
                  m125
                else
                  m126
              else
                if i.val < 128 then
                  m127
                else
                  if i.val < 129 then
                    m128
                  else
                    m129
  else
    if i.val < 195 then
      if i.val < 162 then
        if i.val < 146 then
          if i.val < 138 then
            if i.val < 134 then
              if i.val < 132 then
                if i.val < 131 then
                  m130
                else
                  m131
              else
                if i.val < 133 then
                  m132
                else
                  m133
            else
              if i.val < 136 then
                if i.val < 135 then
                  m134
                else
                  m135
              else
                if i.val < 137 then
                  m136
                else
                  m137
          else
            if i.val < 142 then
              if i.val < 140 then
                if i.val < 139 then
                  m138
                else
                  m139
              else
                if i.val < 141 then
                  m140
                else
                  m141
            else
              if i.val < 144 then
                if i.val < 143 then
                  m142
                else
                  m143
              else
                if i.val < 145 then
                  m144
                else
                  m145
        else
          if i.val < 154 then
            if i.val < 150 then
              if i.val < 148 then
                if i.val < 147 then
                  m146
                else
                  m147
              else
                if i.val < 149 then
                  m148
                else
                  m149
            else
              if i.val < 152 then
                if i.val < 151 then
                  m150
                else
                  m151
              else
                if i.val < 153 then
                  m152
                else
                  m153
          else
            if i.val < 158 then
              if i.val < 156 then
                if i.val < 155 then
                  m154
                else
                  m155
              else
                if i.val < 157 then
                  m156
                else
                  m157
            else
              if i.val < 160 then
                if i.val < 159 then
                  m158
                else
                  m159
              else
                if i.val < 161 then
                  m160
                else
                  m161
      else
        if i.val < 178 then
          if i.val < 170 then
            if i.val < 166 then
              if i.val < 164 then
                if i.val < 163 then
                  m162
                else
                  m163
              else
                if i.val < 165 then
                  m164
                else
                  m165
            else
              if i.val < 168 then
                if i.val < 167 then
                  m166
                else
                  m167
              else
                if i.val < 169 then
                  m168
                else
                  m169
          else
            if i.val < 174 then
              if i.val < 172 then
                if i.val < 171 then
                  m170
                else
                  m171
              else
                if i.val < 173 then
                  m172
                else
                  m173
            else
              if i.val < 176 then
                if i.val < 175 then
                  m174
                else
                  m175
              else
                if i.val < 177 then
                  m176
                else
                  m177
        else
          if i.val < 186 then
            if i.val < 182 then
              if i.val < 180 then
                if i.val < 179 then
                  m178
                else
                  m179
              else
                if i.val < 181 then
                  m180
                else
                  m181
            else
              if i.val < 184 then
                if i.val < 183 then
                  m182
                else
                  m183
              else
                if i.val < 185 then
                  m184
                else
                  m185
          else
            if i.val < 190 then
              if i.val < 188 then
                if i.val < 187 then
                  m186
                else
                  m187
              else
                if i.val < 189 then
                  m188
                else
                  m189
            else
              if i.val < 192 then
                if i.val < 191 then
                  m190
                else
                  m191
              else
                if i.val < 193 then
                  m192
                else
                  if i.val < 194 then
                    m193
                  else
                    m194
    else
      if i.val < 228 then
        if i.val < 211 then
          if i.val < 203 then
            if i.val < 199 then
              if i.val < 197 then
                if i.val < 196 then
                  m195
                else
                  m196
              else
                if i.val < 198 then
                  m197
                else
                  m198
            else
              if i.val < 201 then
                if i.val < 200 then
                  m199
                else
                  m200
              else
                if i.val < 202 then
                  m201
                else
                  m202
          else
            if i.val < 207 then
              if i.val < 205 then
                if i.val < 204 then
                  m203
                else
                  m204
              else
                if i.val < 206 then
                  m205
                else
                  m206
            else
              if i.val < 209 then
                if i.val < 208 then
                  m207
                else
                  m208
              else
                if i.val < 210 then
                  m209
                else
                  m210
        else
          if i.val < 219 then
            if i.val < 215 then
              if i.val < 213 then
                if i.val < 212 then
                  m211
                else
                  m212
              else
                if i.val < 214 then
                  m213
                else
                  m214
            else
              if i.val < 217 then
                if i.val < 216 then
                  m215
                else
                  m216
              else
                if i.val < 218 then
                  m217
                else
                  m218
          else
            if i.val < 223 then
              if i.val < 221 then
                if i.val < 220 then
                  m219
                else
                  m220
              else
                if i.val < 222 then
                  m221
                else
                  m222
            else
              if i.val < 225 then
                if i.val < 224 then
                  m223
                else
                  m224
              else
                if i.val < 226 then
                  m225
                else
                  if i.val < 227 then
                    m226
                  else
                    m227
      else
        if i.val < 244 then
          if i.val < 236 then
            if i.val < 232 then
              if i.val < 230 then
                if i.val < 229 then
                  m228
                else
                  m229
              else
                if i.val < 231 then
                  m230
                else
                  m231
            else
              if i.val < 234 then
                if i.val < 233 then
                  m232
                else
                  m233
              else
                if i.val < 235 then
                  m234
                else
                  m235
          else
            if i.val < 240 then
              if i.val < 238 then
                if i.val < 237 then
                  m236
                else
                  m237
              else
                if i.val < 239 then
                  m238
                else
                  m239
            else
              if i.val < 242 then
                if i.val < 241 then
                  m240
                else
                  m241
              else
                if i.val < 243 then
                  m242
                else
                  m243
        else
          if i.val < 252 then
            if i.val < 248 then
              if i.val < 246 then
                if i.val < 245 then
                  m244
                else
                  m245
              else
                if i.val < 247 then
                  m246
                else
                  m247
            else
              if i.val < 250 then
                if i.val < 249 then
                  m248
                else
                  m249
              else
                if i.val < 251 then
                  m250
                else
                  m251
          else
            if i.val < 256 then
              if i.val < 254 then
                if i.val < 253 then
                  m252
                else
                  m253
              else
                if i.val < 255 then
                  m254
                else
                  m255
            else
              if i.val < 258 then
                if i.val < 257 then
                  m256
                else
                  m257
              else
                if i.val < 259 then
                  m258
                else
                  if i.val < 260 then
                    m259
                  else
                    m260

/-- The identity and the three exact letter values. -/
@[expose] public def SeedIdentities : Prop :=
  decode (matrixRows 0) = 1 ∧
  decode (matrixRows 1) = ↑(localMatrixAssignment false) ∧
  decode (matrixRows 2) = ↑(localMatrixAssignment true) ∧
  decode (matrixRows 3) = ↑((localMatrixAssignment true)⁻¹)

@[expose] public def sharedSpec (i : Fin 113) :
    Fin 261 × Fin 261 × Fin 261 :=
  if i.val < 56 then
    if i.val < 28 then
      if i.val < 14 then
        if i.val < 7 then
          if i.val < 3 then
            if i.val < 1 then
              (1, 2, 4)
            else
              if i.val < 2 then
                (1, 3, 5)
              else
                (4, 5, 6)
          else
            if i.val < 5 then
              if i.val < 4 then
                (6, 6, 7)
              else
                (6, 5, 8)
            else
              if i.val < 6 then
                (4, 7, 9)
              else
                (4, 8, 10)
        else
          if i.val < 10 then
            if i.val < 8 then
              (10, 7, 11)
            else
              if i.val < 9 then
                (6, 11, 12)
              else
                (5, 7, 13)
          else
            if i.val < 12 then
              if i.val < 11 then
                (11, 7, 14)
              else
                (9, 14, 15)
            else
              if i.val < 13 then
                (15, 12, 16)
              else
                (9, 7, 17)
      else
        if i.val < 21 then
          if i.val < 17 then
            if i.val < 15 then
              (4, 6, 18)
            else
              if i.val < 16 then
                (8, 7, 19)
              else
                (16, 13, 20)
          else
            if i.val < 19 then
              if i.val < 18 then
                (20, 17, 21)
              else
                (9, 5, 22)
            else
              if i.val < 20 then
                (16, 5, 23)
              else
                (13, 5, 24)
        else
          if i.val < 24 then
            if i.val < 22 then
              (21, 8, 25)
            else
              if i.val < 23 then
                (8, 6, 26)
              else
                (18, 18, 27)
          else
            if i.val < 26 then
              if i.val < 25 then
                (9, 6, 28)
              else
                (4, 12, 29)
            else
              if i.val < 27 then
                (19, 23, 30)
              else
                (18, 22, 31)
    else
      if i.val < 42 then
        if i.val < 35 then
          if i.val < 31 then
            if i.val < 29 then
              (10, 8, 32)
            else
              if i.val < 30 then
                (19, 5, 33)
              else
                (8, 8, 34)
          else
            if i.val < 33 then
              if i.val < 32 then
                (9, 24, 35)
              else
                (4, 4, 36)
            else
              if i.val < 34 then
                (18, 10, 37)
              else
                (17, 5, 38)
        else
          if i.val < 38 then
            if i.val < 36 then
              (10, 6, 39)
            else
              if i.val < 37 then
                (9, 8, 40)
              else
                (17, 30, 41)
          else
            if i.val < 40 then
              if i.val < 39 then
                (7, 7, 42)
              else
                (13, 23, 43)
            else
              if i.val < 41 then
                (25, 35, 44)
              else
                (12, 7, 45)
      else
        if i.val < 49 then
          if i.val < 45 then
            if i.val < 43 then
              (19, 24, 46)
            else
              if i.val < 44 then
                (37, 31, 47)
              else
                (17, 7, 48)
          else
            if i.val < 47 then
              if i.val < 46 then
                (9, 9, 49)
              else
                (16, 26, 50)
            else
              if i.val < 48 then
                (6, 10, 51)
              else
                (22, 41, 52)
        else
          if i.val < 52 then
            if i.val < 50 then
              (2, 13, 53)
            else
              if i.val < 51 then
                (26, 47, 54)
              else
                (8, 10, 55)
          else
            if i.val < 54 then
              if i.val < 53 then
                (25, 8, 56)
              else
                (9, 18, 57)
            else
              if i.val < 55 then
                (5, 9, 58)
              else
                (12, 13, 59)
  else
    if i.val < 84 then
      if i.val < 70 then
        if i.val < 63 then
          if i.val < 59 then
            if i.val < 57 then
              (18, 9, 60)
            else
              if i.val < 58 then
                (5, 6, 61)
              else
                (13, 50, 62)
          else
            if i.val < 61 then
              if i.val < 60 then
                (9, 23, 63)
              else
                (7, 24, 64)
            else
              if i.val < 62 then
                (45, 30, 65)
              else
                (9, 11, 66)
        else
          if i.val < 66 then
            if i.val < 64 then
              (66, 34, 67)
            else
              if i.val < 65 then
                (67, 20, 68)
              else
                (10, 39, 69)
          else
            if i.val < 68 then
              if i.val < 67 then
                (25, 52, 70)
              else
                (40, 32, 71)
            else
              if i.val < 69 then
                (71, 33, 72)
              else
                (72, 34, 73)
      else
        if i.val < 77 then
          if i.val < 73 then
            if i.val < 71 then
              (2, 2, 3)
            else
              if i.val < 72 then
                (36, 36, 74)
              else
                (42, 42, 75)
          else
            if i.val < 75 then
              if i.val < 74 then
                (28, 9, 76)
              else
                (76, 28, 77)
            else
              if i.val < 76 then
                (31, 54, 78)
              else
                (55, 26, 79)
        else
          if i.val < 80 then
            if i.val < 78 then
              (6, 18, 80)
            else
              if i.val < 79 then
                (25, 27, 81)
              else
                (48, 43, 82)
          else
            if i.val < 82 then
              if i.val < 81 then
                (29, 58, 83)
              else
                (33, 56, 84)
            else
              if i.val < 83 then
                (5, 8, 85)
              else
                (17, 43, 86)
    else
      if i.val < 98 then
        if i.val < 91 then
          if i.val < 87 then
            if i.val < 85 then
              (57, 1, 87)
            else
              if i.val < 86 then
                (32, 21, 88)
              else
                (22, 6, 89)
          else
            if i.val < 89 then
              if i.val < 88 then
                (23, 8, 90)
              else
                (90, 14, 91)
            else
              if i.val < 90 then
                (91, 61, 92)
              else
                (28, 27, 93)
        else
          if i.val < 94 then
            if i.val < 92 then
              (93, 49, 94)
            else
              if i.val < 93 then
                (27, 60, 95)
              else
                (95, 27, 96)
          else
            if i.val < 96 then
              if i.val < 95 then
                (96, 10, 97)
              else
                (9, 39, 98)
            else
              if i.val < 97 then
                (98, 22, 99)
              else
                (99, 26, 100)
      else
        if i.val < 105 then
          if i.val < 101 then
            if i.val < 99 then
              (100, 17, 101)
            else
              if i.val < 100 then
                (101, 62, 102)
              else
                (63, 29, 103)
          else
            if i.val < 103 then
              if i.val < 102 then
                (64, 21, 104)
              else
                (37, 4, 105)
            else
              if i.val < 104 then
                (9, 45, 106)
              else
                (106, 59, 107)
        else
          if i.val < 109 then
            if i.val < 107 then
              if i.val < 106 then
                (9, 69, 108)
              else
                (108, 9, 109)
            else
              if i.val < 108 then
                (109, 29, 110)
              else
                (110, 6, 111)
          else
            if i.val < 111 then
              if i.val < 110 then
                (111, 68, 112)
              else
                (112, 10, 113)
            else
              if i.val < 112 then
                (9, 35, 114)
              else
                (73, 19, 115)

@[expose] public def SharedIdentities : Prop :=
  ∀ i, let e := sharedSpec i
    decode (matrixRows e.1) * decode (matrixRows e.2.1) = decode (matrixRows e.2.2)

@[expose] public def firstSpec (i : Fin 55) :
    Fin 261 × Fin 261 × Fin 261 :=
  if i.val < 27 then
    if i.val < 13 then
      if i.val < 6 then
        if i.val < 3 then
          if i.val < 1 then
            (1, 1, 0)
          else
            if i.val < 2 then
              (3, 2, 0)
            else
              (74, 36, 116)
        else
          if i.val < 4 then
            (116, 4, 0)
          else
            if i.val < 5 then
              (53, 75, 117)
            else
              (117, 42, 1)
      else
        if i.val < 9 then
          if i.val < 7 then
            (1, 1, 0)
          else
            if i.val < 8 then
              (53, 6, 118)
            else
              (118, 77, 119)
        else
          if i.val < 11 then
            if i.val < 10 then
              (119, 29, 120)
            else
              (120, 19, 121)
          else
            if i.val < 12 then
              (121, 46, 122)
            else
              (122, 18, 123)
    else
      if i.val < 20 then
        if i.val < 16 then
          if i.val < 14 then
            (123, 4, 1)
          else
            if i.val < 15 then
              (1, 1, 0)
            else
              (78, 79, 124)
        else
          if i.val < 18 then
            if i.val < 17 then
              (124, 78, 125)
            else
              (125, 54, 126)
          else
            if i.val < 19 then
              (126, 79, 0)
            else
              (80, 38, 127)
      else
        if i.val < 23 then
          if i.val < 21 then
            (127, 20, 128)
          else
            if i.val < 22 then
              (128, 28, 129)
            else
              (129, 39, 130)
        else
          if i.val < 25 then
            if i.val < 24 then
              (130, 56, 131)
            else
              (131, 57, 0)
          else
            if i.val < 26 then
              (32, 81, 132)
            else
              (132, 28, 133)
  else
    if i.val < 41 then
      if i.val < 34 then
        if i.val < 30 then
          if i.val < 28 then
            (133, 82, 134)
          else
            if i.val < 29 then
              (134, 83, 0)
            else
              (53, 84, 135)
        else
          if i.val < 32 then
            if i.val < 31 then
              (135, 47, 136)
            else
              (136, 8, 137)
          else
            if i.val < 33 then
              (137, 11, 138)
            else
              (138, 85, 139)
      else
        if i.val < 37 then
          if i.val < 35 then
            (139, 86, 140)
          else
            if i.val < 36 then
              (140, 87, 0)
            else
              (77, 88, 141)
        else
          if i.val < 39 then
            if i.val < 38 then
              (141, 46, 142)
            else
              (142, 9, 143)
          else
            if i.val < 40 then
              (143, 59, 144)
            else
              (144, 24, 145)
    else
      if i.val < 48 then
        if i.val < 44 then
          if i.val < 42 then
            (145, 8, 146)
          else
            if i.val < 43 then
              (146, 84, 147)
            else
              (147, 60, 0)
        else
          if i.val < 46 then
            if i.val < 45 then
              (7, 8, 148)
            else
              (148, 89, 149)
          else
            if i.val < 47 then
              (149, 32, 150)
            else
              (150, 92, 151)
      else
        if i.val < 51 then
          if i.val < 49 then
            (151, 94, 152)
          else
            if i.val < 50 then
              (152, 17, 153)
            else
              (153, 82, 154)
        else
          if i.val < 53 then
            if i.val < 52 then
              (154, 10, 155)
            else
              (155, 10, 156)
          else
            if i.val < 54 then
              (156, 97, 116)
            else
              (116, 4, 0)

@[expose] public def FirstIdentities : Prop :=
  ∀ i, let e := firstSpec i
    decode (matrixRows e.1) * decode (matrixRows e.2.1) = decode (matrixRows e.2.2)

@[expose] public def lastSpec (i : Fin 121) :
    Fin 261 × Fin 261 × Fin 261 :=
  if i.val < 60 then
    if i.val < 30 then
      if i.val < 15 then
        if i.val < 7 then
          if i.val < 3 then
            if i.val < 1 then
              (94, 9, 157)
            else
              if i.val < 2 then
                (157, 38, 158)
              else
                (158, 21, 159)
          else
            if i.val < 5 then
              if i.val < 4 then
                (159, 5, 160)
              else
                (160, 18, 161)
            else
              if i.val < 6 then
                (161, 17, 162)
              else
                (162, 32, 163)
        else
          if i.val < 11 then
            if i.val < 9 then
              if i.val < 8 then
                (163, 44, 164)
              else
                (164, 92, 0)
            else
              if i.val < 10 then
                (7, 23, 165)
              else
                (165, 102, 166)
          else
            if i.val < 13 then
              if i.val < 12 then
                (166, 63, 167)
              else
                (167, 102, 116)
            else
              if i.val < 14 then
                (116, 4, 0)
              else
                (48, 62, 168)
      else
        if i.val < 22 then
          if i.val < 18 then
            if i.val < 16 then
              (168, 103, 169)
            else
              if i.val < 17 then
                (169, 46, 170)
              else
                (170, 34, 171)
          else
            if i.val < 20 then
              if i.val < 19 then
                (171, 17, 172)
              else
                (172, 19, 173)
            else
              if i.val < 21 then
                (173, 50, 174)
              else
                (174, 103, 175)
        else
          if i.val < 26 then
            if i.val < 24 then
              if i.val < 23 then
                (175, 7, 176)
              else
                (176, 85, 177)
            else
              if i.val < 25 then
                (177, 28, 0)
              else
                (13, 104, 178)
          else
            if i.val < 28 then
              if i.val < 27 then
                (178, 51, 179)
              else
                (179, 65, 180)
            else
              if i.val < 29 then
                (180, 10, 181)
              else
                (181, 14, 182)
    else
      if i.val < 45 then
        if i.val < 37 then
          if i.val < 33 then
            if i.val < 31 then
              (182, 58, 183)
            else
              if i.val < 32 then
                (183, 12, 184)
              else
                (184, 97, 185)
          else
            if i.val < 35 then
              if i.val < 34 then
                (185, 40, 186)
              else
                (186, 89, 187)
            else
              if i.val < 36 then
                (187, 88, 188)
              else
                (188, 61, 0)
        else
          if i.val < 41 then
            if i.val < 39 then
              if i.val < 38 then
                (13, 68, 189)
              else
                (189, 22, 190)
            else
              if i.val < 40 then
                (190, 51, 191)
              else
                (191, 44, 192)
          else
            if i.val < 43 then
              if i.val < 42 then
                (192, 44, 193)
              else
                (193, 81, 194)
            else
              if i.val < 44 then
                (194, 105, 0)
              else
                (64, 25, 195)
      else
        if i.val < 52 then
          if i.val < 48 then
            if i.val < 46 then
              (195, 10, 196)
            else
              if i.val < 47 then
                (196, 12, 197)
              else
                (197, 107, 198)
          else
            if i.val < 50 then
              if i.val < 49 then
                (198, 17, 199)
              else
                (199, 51, 200)
            else
              if i.val < 51 then
                (200, 69, 201)
              else
                (201, 10, 202)
        else
          if i.val < 56 then
            if i.val < 54 then
              if i.val < 53 then
                (202, 70, 203)
              else
                (203, 17, 204)
            else
              if i.val < 55 then
                (204, 24, 116)
              else
                (116, 4, 0)
          else
            if i.val < 58 then
              if i.val < 57 then
                (5, 22, 205)
              else
                (205, 9, 206)
            else
              if i.val < 59 then
                (206, 26, 207)
              else
                (207, 29, 208)
  else
    if i.val < 90 then
      if i.val < 75 then
        if i.val < 67 then
          if i.val < 63 then
            if i.val < 61 then
              (208, 107, 209)
            else
              if i.val < 62 then
                (209, 38, 210)
              else
                (210, 6, 211)
          else
            if i.val < 65 then
              if i.val < 64 then
                (211, 31, 212)
              else
                (212, 8, 213)
            else
              if i.val < 66 then
                (213, 40, 214)
              else
                (214, 73, 215)
        else
          if i.val < 71 then
            if i.val < 69 then
              if i.val < 68 then
                (215, 55, 216)
              else
                (216, 10, 217)
            else
              if i.val < 70 then
                (217, 21, 218)
              else
                (218, 46, 219)
          else
            if i.val < 73 then
              if i.val < 72 then
                (219, 8, 220)
              else
                (220, 86, 134)
            else
              if i.val < 74 then
                (134, 83, 0)
              else
                (3, 40, 221)
      else
        if i.val < 82 then
          if i.val < 78 then
            if i.val < 76 then
              (221, 113, 222)
            else
              if i.val < 77 then
                (222, 31, 223)
              else
                (223, 65, 224)
          else
            if i.val < 80 then
              if i.val < 79 then
                (224, 49, 225)
              else
                (225, 22, 226)
            else
              if i.val < 81 then
                (226, 65, 227)
              else
                (227, 9, 228)
        else
          if i.val < 86 then
            if i.val < 84 then
              if i.val < 83 then
                (228, 52, 140)
              else
                (140, 87, 0)
            else
              if i.val < 85 then
                (3, 10, 229)
              else
                (229, 113, 230)
          else
            if i.val < 88 then
              if i.val < 87 then
                (230, 48, 231)
              else
                (231, 33, 232)
            else
              if i.val < 89 then
                (232, 70, 233)
              else
                (233, 38, 234)
    else
      if i.val < 105 then
        if i.val < 97 then
          if i.val < 93 then
            if i.val < 91 then
              (234, 8, 235)
            else
              if i.val < 92 then
                (235, 18, 236)
              else
                (236, 41, 237)
          else
            if i.val < 95 then
              if i.val < 94 then
                (237, 38, 238)
              else
                (238, 80, 1)
            else
              if i.val < 96 then
                (1, 1, 0)
              else
                (8, 29, 239)
        else
          if i.val < 101 then
            if i.val < 99 then
              if i.val < 98 then
                (239, 14, 240)
              else
                (240, 43, 241)
            else
              if i.val < 100 then
                (241, 114, 242)
              else
                (242, 21, 243)
          else
            if i.val < 103 then
              if i.val < 102 then
                (243, 51, 244)
              else
                (244, 12, 245)
            else
              if i.val < 104 then
                (245, 38, 246)
              else
                (246, 44, 247)
      else
        if i.val < 113 then
          if i.val < 109 then
            if i.val < 107 then
              if i.val < 106 then
                (247, 70, 194)
              else
                (194, 105, 0)
            else
              if i.val < 108 then
                (8, 41, 248)
              else
                (248, 114, 249)
          else
            if i.val < 111 then
              if i.val < 110 then
                (249, 44, 250)
              else
                (250, 21, 251)
            else
              if i.val < 112 then
                (251, 33, 252)
              else
                (252, 33, 253)
        else
          if i.val < 117 then
            if i.val < 115 then
              if i.val < 114 then
                (253, 22, 254)
              else
                (254, 115, 255)
            else
              if i.val < 116 then
                (255, 104, 256)
              else
                (256, 19, 257)
          else
            if i.val < 119 then
              if i.val < 118 then
                (257, 7, 258)
              else
                (258, 5, 259)
            else
              if i.val < 120 then
                (259, 115, 260)
              else
                (260, 6, 0)

@[expose] public def LastIdentities : Prop :=
  ∀ i, let e := lastSpec i
    decode (matrixRows e.1) * decode (matrixRows e.2.1) = decode (matrixRows e.2.2)

end Lyons.RelationCertificate
