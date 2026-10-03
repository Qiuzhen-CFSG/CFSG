module

public import Mathlib.GroupTheory.Perm.Finite

/-!
# The degree-1600 Atlas permutation group

The two permutations below are the inverse point maps of the disjoint cycles
in `refs/original/n-group-global/atlas-tits-p1600-{a,b}.g`, with labels shifted
from 1–1600 to 0–1599. Taking inverse point maps converts GAP right-action
word evaluation to Lean left-action word evaluation without reversing words.
The finite group is the subgroup they generate; its order and its relation
to Parrott's presentation require separate proofs.

The tables are represented by balanced comparisons. The kernel checks the
involution and order-three identities pointwise, giving explicit inverse
maps without any external computation assumption.
-/

namespace Tits

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

@[expose] public def atlas1600AMap (x : Fin 1600) : Fin 1600 :=
  if x.val < 800 then
    if x.val < 400 then
      if x.val < 200 then
        if x.val < 100 then
          if x.val < 50 then
            if x.val < 25 then
              if x.val < 12 then
                if x.val < 6 then
                  if x.val < 3 then
                    if x.val < 1 then
                      1
                    else
                      if x.val < 2 then
                        0
                      else
                        3
                  else
                    if x.val < 4 then
                      2
                    else
                      if x.val < 5 then
                        5
                      else
                        4
                else
                  if x.val < 9 then
                    if x.val < 7 then
                      8
                    else
                      if x.val < 8 then
                        9
                      else
                        6
                  else
                    if x.val < 10 then
                      7
                    else
                      if x.val < 11 then
                        13
                      else
                        14
              else
                if x.val < 18 then
                  if x.val < 15 then
                    if x.val < 13 then
                      16
                    else
                      if x.val < 14 then
                        10
                      else
                        11
                  else
                    if x.val < 16 then
                      20
                    else
                      if x.val < 17 then
                        12
                      else
                        22
                else
                  if x.val < 21 then
                    if x.val < 19 then
                      23
                    else
                      if x.val < 20 then
                        25
                      else
                        15
                  else
                    if x.val < 23 then
                      if x.val < 22 then
                        28
                      else
                        17
                    else
                      if x.val < 24 then
                        18
                      else
                        32
            else
              if x.val < 37 then
                if x.val < 31 then
                  if x.val < 28 then
                    if x.val < 26 then
                      19
                    else
                      if x.val < 27 then
                        34
                      else
                        35
                  else
                    if x.val < 29 then
                      21
                    else
                      if x.val < 30 then
                        38
                      else
                        39
                else
                  if x.val < 34 then
                    if x.val < 32 then
                      41
                    else
                      if x.val < 33 then
                        24
                      else
                        43
                  else
                    if x.val < 35 then
                      26
                    else
                      if x.val < 36 then
                        27
                      else
                        46
              else
                if x.val < 43 then
                  if x.val < 40 then
                    if x.val < 38 then
                      47
                    else
                      if x.val < 39 then
                        29
                      else
                        30
                  else
                    if x.val < 41 then
                      51
                    else
                      if x.val < 42 then
                        31
                      else
                        53
                else
                  if x.val < 46 then
                    if x.val < 44 then
                      33
                    else
                      if x.val < 45 then
                        56
                      else
                        57
                  else
                    if x.val < 48 then
                      if x.val < 47 then
                        36
                      else
                        37
                    else
                      if x.val < 49 then
                        61
                      else
                        62
          else
            if x.val < 75 then
              if x.val < 62 then
                if x.val < 56 then
                  if x.val < 53 then
                    if x.val < 51 then
                      64
                    else
                      if x.val < 52 then
                        40
                      else
                        67
                  else
                    if x.val < 54 then
                      42
                    else
                      if x.val < 55 then
                        70
                      else
                        71
                else
                  if x.val < 59 then
                    if x.val < 57 then
                      44
                    else
                      if x.val < 58 then
                        45
                      else
                        75
                  else
                    if x.val < 60 then
                      76
                    else
                      if x.val < 61 then
                        78
                      else
                        48
              else
                if x.val < 68 then
                  if x.val < 65 then
                    if x.val < 63 then
                      49
                    else
                      if x.val < 64 then
                        82
                      else
                        50
                  else
                    if x.val < 66 then
                      84
                    else
                      if x.val < 67 then
                        85
                      else
                        52
                else
                  if x.val < 71 then
                    if x.val < 69 then
                      88
                    else
                      if x.val < 70 then
                        89
                      else
                        54
                  else
                    if x.val < 73 then
                      if x.val < 72 then
                        55
                      else
                        93
                    else
                      if x.val < 74 then
                        94
                      else
                        96
            else
              if x.val < 87 then
                if x.val < 81 then
                  if x.val < 78 then
                    if x.val < 76 then
                      58
                    else
                      if x.val < 77 then
                        59
                      else
                        100
                  else
                    if x.val < 79 then
                      60
                    else
                      if x.val < 80 then
                        101
                      else
                        102
                else
                  if x.val < 84 then
                    if x.val < 82 then
                      104
                    else
                      if x.val < 83 then
                        63
                      else
                        107
                  else
                    if x.val < 85 then
                      65
                    else
                      if x.val < 86 then
                        66
                      else
                        111
              else
                if x.val < 93 then
                  if x.val < 90 then
                    if x.val < 88 then
                      112
                    else
                      if x.val < 89 then
                        68
                      else
                        69
                  else
                    if x.val < 91 then
                      116
                    else
                      if x.val < 92 then
                        117
                      else
                        119
                else
                  if x.val < 96 then
                    if x.val < 94 then
                      72
                    else
                      if x.val < 95 then
                        73
                      else
                        123
                  else
                    if x.val < 98 then
                      if x.val < 97 then
                        74
                      else
                        125
                    else
                      if x.val < 99 then
                        109
                      else
                        127
        else
          if x.val < 150 then
            if x.val < 125 then
              if x.val < 112 then
                if x.val < 106 then
                  if x.val < 103 then
                    if x.val < 101 then
                      77
                    else
                      if x.val < 102 then
                        79
                      else
                        80
                  else
                    if x.val < 104 then
                      132
                    else
                      if x.val < 105 then
                        81
                      else
                        134
                else
                  if x.val < 109 then
                    if x.val < 107 then
                      135
                    else
                      if x.val < 108 then
                        83
                      else
                        138
                  else
                    if x.val < 110 then
                      98
                    else
                      if x.val < 111 then
                        140
                      else
                        86
              else
                if x.val < 118 then
                  if x.val < 115 then
                    if x.val < 113 then
                      87
                    else
                      if x.val < 114 then
                        144
                      else
                        145
                  else
                    if x.val < 116 then
                      147
                    else
                      if x.val < 117 then
                        90
                      else
                        91
                else
                  if x.val < 121 then
                    if x.val < 119 then
                      151
                    else
                      if x.val < 120 then
                        92
                      else
                        153
                  else
                    if x.val < 123 then
                      if x.val < 122 then
                        154
                      else
                        156
                    else
                      if x.val < 124 then
                        95
                      else
                        159
            else
              if x.val < 137 then
                if x.val < 131 then
                  if x.val < 128 then
                    if x.val < 126 then
                      97
                    else
                      if x.val < 127 then
                        162
                      else
                        99
                  else
                    if x.val < 129 then
                      164
                    else
                      if x.val < 130 then
                        165
                      else
                        166
                else
                  if x.val < 134 then
                    if x.val < 132 then
                      168
                    else
                      if x.val < 133 then
                        103
                      else
                        171
                  else
                    if x.val < 135 then
                      105
                    else
                      if x.val < 136 then
                        106
                      else
                        175
              else
                if x.val < 143 then
                  if x.val < 140 then
                    if x.val < 138 then
                      176
                    else
                      if x.val < 139 then
                        108
                      else
                        179
                  else
                    if x.val < 141 then
                      110
                    else
                      if x.val < 142 then
                        181
                      else
                        182
                else
                  if x.val < 146 then
                    if x.val < 144 then
                      184
                    else
                      if x.val < 145 then
                        113
                      else
                        114
                  else
                    if x.val < 148 then
                      if x.val < 147 then
                        188
                      else
                        115
                    else
                      if x.val < 149 then
                        158
                      else
                        173
          else
            if x.val < 175 then
              if x.val < 162 then
                if x.val < 156 then
                  if x.val < 153 then
                    if x.val < 151 then
                      191
                    else
                      if x.val < 152 then
                        118
                      else
                        194
                  else
                    if x.val < 154 then
                      120
                    else
                      if x.val < 155 then
                        121
                      else
                        198
                else
                  if x.val < 159 then
                    if x.val < 157 then
                      122
                    else
                      if x.val < 158 then
                        200
                      else
                        148
                  else
                    if x.val < 160 then
                      124
                    else
                      if x.val < 161 then
                        203
                      else
                        204
              else
                if x.val < 168 then
                  if x.val < 165 then
                    if x.val < 163 then
                      126
                    else
                      if x.val < 164 then
                        207
                      else
                        128
                  else
                    if x.val < 166 then
                      129
                    else
                      if x.val < 167 then
                        130
                      else
                        212
                else
                  if x.val < 171 then
                    if x.val < 169 then
                      131
                    else
                      if x.val < 170 then
                        214
                      else
                        215
                  else
                    if x.val < 173 then
                      if x.val < 172 then
                        133
                      else
                        218
                    else
                      if x.val < 174 then
                        149
                      else
                        220
            else
              if x.val < 187 then
                if x.val < 181 then
                  if x.val < 178 then
                    if x.val < 176 then
                      136
                    else
                      if x.val < 177 then
                        137
                      else
                        224
                  else
                    if x.val < 179 then
                      225
                    else
                      if x.val < 180 then
                        139
                      else
                        228
                else
                  if x.val < 184 then
                    if x.val < 182 then
                      141
                    else
                      if x.val < 183 then
                        142
                      else
                        232
                  else
                    if x.val < 185 then
                      143
                    else
                      if x.val < 186 then
                        234
                      else
                        235
              else
                if x.val < 193 then
                  if x.val < 190 then
                    if x.val < 188 then
                      237
                    else
                      if x.val < 189 then
                        146
                      else
                        239
                  else
                    if x.val < 191 then
                      241
                    else
                      if x.val < 192 then
                        150
                      else
                        243
                else
                  if x.val < 196 then
                    if x.val < 194 then
                      244
                    else
                      if x.val < 195 then
                        152
                      else
                        247
                  else
                    if x.val < 198 then
                      if x.val < 197 then
                        248
                      else
                        250
                    else
                      if x.val < 199 then
                        155
                      else
                        252
      else
        if x.val < 300 then
          if x.val < 250 then
            if x.val < 225 then
              if x.val < 212 then
                if x.val < 206 then
                  if x.val < 203 then
                    if x.val < 201 then
                      157
                    else
                      if x.val < 202 then
                        255
                      else
                        256
                  else
                    if x.val < 204 then
                      160
                    else
                      if x.val < 205 then
                        161
                      else
                        260
                else
                  if x.val < 209 then
                    if x.val < 207 then
                      261
                    else
                      if x.val < 208 then
                        163
                      else
                        264
                  else
                    if x.val < 210 then
                      254
                    else
                      if x.val < 211 then
                        266
                      else
                        268
              else
                if x.val < 218 then
                  if x.val < 215 then
                    if x.val < 213 then
                      167
                    else
                      if x.val < 214 then
                        271
                      else
                        169
                  else
                    if x.val < 216 then
                      170
                    else
                      if x.val < 217 then
                        275
                      else
                        276
                else
                  if x.val < 221 then
                    if x.val < 219 then
                      172
                    else
                      if x.val < 220 then
                        279
                      else
                        174
                  else
                    if x.val < 223 then
                      if x.val < 222 then
                        281
                      else
                        282
                    else
                      if x.val < 224 then
                        284
                      else
                        177
            else
              if x.val < 237 then
                if x.val < 231 then
                  if x.val < 228 then
                    if x.val < 226 then
                      178
                    else
                      if x.val < 227 then
                        288
                      else
                        289
                  else
                    if x.val < 229 then
                      180
                    else
                      if x.val < 230 then
                        292
                      else
                        273
                else
                  if x.val < 234 then
                    if x.val < 232 then
                      294
                    else
                      if x.val < 233 then
                        183
                      else
                        297
                  else
                    if x.val < 235 then
                      185
                    else
                      if x.val < 236 then
                        186
                      else
                        300
              else
                if x.val < 243 then
                  if x.val < 240 then
                    if x.val < 238 then
                      187
                    else
                      if x.val < 239 then
                        301
                      else
                        189
                  else
                    if x.val < 241 then
                      304
                    else
                      if x.val < 242 then
                        190
                      else
                        306
                else
                  if x.val < 246 then
                    if x.val < 244 then
                      192
                    else
                      if x.val < 245 then
                        193
                      else
                        246
                  else
                    if x.val < 248 then
                      if x.val < 247 then
                        245
                      else
                        195
                    else
                      if x.val < 249 then
                        196
                      else
                        312
          else
            if x.val < 275 then
              if x.val < 262 then
                if x.val < 256 then
                  if x.val < 253 then
                    if x.val < 251 then
                      197
                    else
                      if x.val < 252 then
                        314
                      else
                        199
                  else
                    if x.val < 254 then
                      317
                    else
                      if x.val < 255 then
                        209
                      else
                        201
                else
                  if x.val < 259 then
                    if x.val < 257 then
                      202
                    else
                      if x.val < 258 then
                        321
                      else
                        322
                  else
                    if x.val < 260 then
                      324
                    else
                      if x.val < 261 then
                        205
                      else
                        206
              else
                if x.val < 268 then
                  if x.val < 265 then
                    if x.val < 263 then
                      327
                    else
                      if x.val < 264 then
                        328
                      else
                        208
                  else
                    if x.val < 266 then
                      331
                    else
                      if x.val < 267 then
                        210
                      else
                        333
                else
                  if x.val < 271 then
                    if x.val < 269 then
                      211
                    else
                      if x.val < 270 then
                        335
                      else
                        336
                  else
                    if x.val < 273 then
                      if x.val < 272 then
                        213
                      else
                        339
                    else
                      if x.val < 274 then
                        230
                      else
                        341
            else
              if x.val < 287 then
                if x.val < 281 then
                  if x.val < 278 then
                    if x.val < 276 then
                      216
                    else
                      if x.val < 277 then
                        217
                      else
                        345
                  else
                    if x.val < 279 then
                      346
                    else
                      if x.val < 280 then
                        219
                      else
                        349
                else
                  if x.val < 284 then
                    if x.val < 282 then
                      221
                    else
                      if x.val < 283 then
                        222
                      else
                        353
                  else
                    if x.val < 285 then
                      223
                    else
                      if x.val < 286 then
                        355
                      else
                        356
              else
                if x.val < 293 then
                  if x.val < 290 then
                    if x.val < 288 then
                      357
                    else
                      if x.val < 289 then
                        226
                      else
                        227
                  else
                    if x.val < 291 then
                      361
                    else
                      if x.val < 292 then
                        362
                      else
                        229
                else
                  if x.val < 296 then
                    if x.val < 294 then
                      365
                    else
                      if x.val < 295 then
                        231
                      else
                        367
                  else
                    if x.val < 298 then
                      if x.val < 297 then
                        368
                      else
                        233
                    else
                      if x.val < 299 then
                        371
                      else
                        372
        else
          if x.val < 350 then
            if x.val < 325 then
              if x.val < 312 then
                if x.val < 306 then
                  if x.val < 303 then
                    if x.val < 301 then
                      236
                    else
                      if x.val < 302 then
                        238
                      else
                        376
                  else
                    if x.val < 304 then
                      377
                    else
                      if x.val < 305 then
                        240
                      else
                        380
                else
                  if x.val < 309 then
                    if x.val < 307 then
                      242
                    else
                      if x.val < 308 then
                        383
                      else
                        384
                  else
                    if x.val < 310 then
                      386
                    else
                      if x.val < 311 then
                        387
                      else
                        389
              else
                if x.val < 318 then
                  if x.val < 315 then
                    if x.val < 313 then
                      249
                    else
                      if x.val < 314 then
                        392
                      else
                        251
                  else
                    if x.val < 316 then
                      395
                    else
                      if x.val < 317 then
                        396
                      else
                        253
                else
                  if x.val < 321 then
                    if x.val < 319 then
                      399
                    else
                      if x.val < 320 then
                        400
                      else
                        402
                  else
                    if x.val < 323 then
                      if x.val < 322 then
                        257
                      else
                        258
                    else
                      if x.val < 324 then
                        406
                      else
                        259
            else
              if x.val < 337 then
                if x.val < 331 then
                  if x.val < 328 then
                    if x.val < 326 then
                      408
                    else
                      if x.val < 327 then
                        409
                      else
                        262
                  else
                    if x.val < 329 then
                      263
                    else
                      if x.val < 330 then
                        412
                      else
                        413
                else
                  if x.val < 334 then
                    if x.val < 332 then
                      265
                    else
                      if x.val < 333 then
                        416
                      else
                        267
                  else
                    if x.val < 335 then
                      419
                    else
                      if x.val < 336 then
                        269
                      else
                        270
              else
                if x.val < 343 then
                  if x.val < 340 then
                    if x.val < 338 then
                      423
                    else
                      if x.val < 339 then
                        424
                      else
                        272
                  else
                    if x.val < 341 then
                      343
                    else
                      if x.val < 342 then
                        274
                      else
                        428
                else
                  if x.val < 346 then
                    if x.val < 344 then
                      340
                    else
                      if x.val < 345 then
                        430
                      else
                        277
                  else
                    if x.val < 348 then
                      if x.val < 347 then
                        278
                      else
                        434
                    else
                      if x.val < 349 then
                        435
                      else
                        280
          else
            if x.val < 375 then
              if x.val < 362 then
                if x.val < 356 then
                  if x.val < 353 then
                    if x.val < 351 then
                      438
                    else
                      if x.val < 352 then
                        421
                      else
                        440
                  else
                    if x.val < 354 then
                      283
                    else
                      if x.val < 355 then
                        443
                      else
                        285
                else
                  if x.val < 359 then
                    if x.val < 357 then
                      286
                    else
                      if x.val < 358 then
                        287
                      else
                        448
                  else
                    if x.val < 360 then
                      449
                    else
                      if x.val < 361 then
                        450
                      else
                        290
              else
                if x.val < 368 then
                  if x.val < 365 then
                    if x.val < 363 then
                      291
                    else
                      if x.val < 364 then
                        454
                      else
                        455
                  else
                    if x.val < 366 then
                      293
                    else
                      if x.val < 367 then
                        457
                      else
                        295
                else
                  if x.val < 371 then
                    if x.val < 369 then
                      296
                    else
                      if x.val < 370 then
                        370
                      else
                        369
                  else
                    if x.val < 373 then
                      if x.val < 372 then
                        298
                      else
                        299
                    else
                      if x.val < 374 then
                        463
                      else
                        464
            else
              if x.val < 387 then
                if x.val < 381 then
                  if x.val < 378 then
                    if x.val < 376 then
                      465
                    else
                      if x.val < 377 then
                        302
                      else
                        303
                  else
                    if x.val < 379 then
                      390
                    else
                      if x.val < 380 then
                        469
                      else
                        305
                else
                  if x.val < 384 then
                    if x.val < 382 then
                      472
                    else
                      if x.val < 383 then
                        473
                      else
                        307
                  else
                    if x.val < 385 then
                      308
                    else
                      if x.val < 386 then
                        477
                      else
                        309
              else
                if x.val < 393 then
                  if x.val < 390 then
                    if x.val < 388 then
                      310
                    else
                      if x.val < 389 then
                        479
                      else
                        311
                  else
                    if x.val < 391 then
                      378
                    else
                      if x.val < 392 then
                        481
                      else
                        313
                else
                  if x.val < 396 then
                    if x.val < 394 then
                      484
                    else
                      if x.val < 395 then
                        485
                      else
                        315
                  else
                    if x.val < 398 then
                      if x.val < 397 then
                        316
                      else
                        489
                    else
                      if x.val < 399 then
                        490
                      else
                        318
    else
      if x.val < 600 then
        if x.val < 500 then
          if x.val < 450 then
            if x.val < 425 then
              if x.val < 412 then
                if x.val < 406 then
                  if x.val < 403 then
                    if x.val < 401 then
                      319
                    else
                      if x.val < 402 then
                        468
                      else
                        320
                  else
                    if x.val < 404 then
                      494
                    else
                      if x.val < 405 then
                        495
                      else
                        497
                else
                  if x.val < 409 then
                    if x.val < 407 then
                      323
                    else
                      if x.val < 408 then
                        499
                      else
                        325
                  else
                    if x.val < 410 then
                      326
                    else
                      if x.val < 411 then
                        503
                      else
                        504
              else
                if x.val < 418 then
                  if x.val < 415 then
                    if x.val < 413 then
                      329
                    else
                      if x.val < 414 then
                        330
                      else
                        508
                  else
                    if x.val < 416 then
                      509
                    else
                      if x.val < 417 then
                        332
                      else
                        512
                else
                  if x.val < 421 then
                    if x.val < 419 then
                      501
                    else
                      if x.val < 420 then
                        334
                      else
                        515
                  else
                    if x.val < 423 then
                      if x.val < 422 then
                        351
                      else
                        517
                    else
                      if x.val < 424 then
                        337
                      else
                        338
            else
              if x.val < 437 then
                if x.val < 431 then
                  if x.val < 428 then
                    if x.val < 426 then
                      521
                    else
                      if x.val < 427 then
                        522
                      else
                        524
                  else
                    if x.val < 429 then
                      342
                    else
                      if x.val < 430 then
                        526
                      else
                        344
                else
                  if x.val < 434 then
                    if x.val < 432 then
                      528
                    else
                      if x.val < 433 then
                        529
                      else
                        531
                  else
                    if x.val < 435 then
                      347
                    else
                      if x.val < 436 then
                        348
                      else
                        482
              else
                if x.val < 443 then
                  if x.val < 440 then
                    if x.val < 438 then
                      535
                    else
                      if x.val < 439 then
                        350
                      else
                        507
                  else
                    if x.val < 441 then
                      352
                    else
                      if x.val < 442 then
                        539
                      else
                        540
                else
                  if x.val < 446 then
                    if x.val < 444 then
                      354
                    else
                      if x.val < 445 then
                        543
                      else
                        544
                  else
                    if x.val < 448 then
                      if x.val < 447 then
                        546
                      else
                        548
                    else
                      if x.val < 449 then
                        358
                      else
                        359
          else
            if x.val < 475 then
              if x.val < 462 then
                if x.val < 456 then
                  if x.val < 453 then
                    if x.val < 451 then
                      360
                    else
                      if x.val < 452 then
                        553
                      else
                        554
                  else
                    if x.val < 454 then
                      556
                    else
                      if x.val < 455 then
                        363
                      else
                        364
                else
                  if x.val < 459 then
                    if x.val < 457 then
                      500
                    else
                      if x.val < 458 then
                        366
                      else
                        550
                  else
                    if x.val < 460 then
                      562
                    else
                      if x.val < 461 then
                        564
                      else
                        565
              else
                if x.val < 468 then
                  if x.val < 465 then
                    if x.val < 463 then
                      567
                    else
                      if x.val < 464 then
                        373
                      else
                        374
                  else
                    if x.val < 466 then
                      375
                    else
                      if x.val < 467 then
                        571
                      else
                        572
                else
                  if x.val < 471 then
                    if x.val < 469 then
                      401
                    else
                      if x.val < 470 then
                        379
                      else
                        575
                  else
                    if x.val < 473 then
                      if x.val < 472 then
                        576
                      else
                        381
                    else
                      if x.val < 474 then
                        382
                      else
                        580
            else
              if x.val < 487 then
                if x.val < 481 then
                  if x.val < 478 then
                    if x.val < 476 then
                      581
                    else
                      if x.val < 477 then
                        492
                      else
                        385
                  else
                    if x.val < 479 then
                      584
                    else
                      if x.val < 480 then
                        388
                      else
                        587
                else
                  if x.val < 484 then
                    if x.val < 482 then
                      391
                    else
                      if x.val < 483 then
                        436
                      else
                        589
                  else
                    if x.val < 485 then
                      393
                    else
                      if x.val < 486 then
                        394
                      else
                        592
              else
                if x.val < 493 then
                  if x.val < 490 then
                    if x.val < 488 then
                      593
                    else
                      if x.val < 489 then
                        595
                      else
                        397
                  else
                    if x.val < 491 then
                      398
                    else
                      if x.val < 492 then
                        599
                      else
                        476
                else
                  if x.val < 496 then
                    if x.val < 494 then
                      601
                    else
                      if x.val < 495 then
                        403
                      else
                        404
                  else
                    if x.val < 498 then
                      if x.val < 497 then
                        604
                      else
                        405
                    else
                      if x.val < 499 then
                        606
                      else
                        407
        else
          if x.val < 550 then
            if x.val < 525 then
              if x.val < 512 then
                if x.val < 506 then
                  if x.val < 503 then
                    if x.val < 501 then
                      456
                    else
                      if x.val < 502 then
                        418
                      else
                        585
                  else
                    if x.val < 504 then
                      410
                    else
                      if x.val < 505 then
                        411
                      else
                        612
                else
                  if x.val < 509 then
                    if x.val < 507 then
                      613
                    else
                      if x.val < 508 then
                        439
                      else
                        414
                  else
                    if x.val < 510 then
                      415
                    else
                      if x.val < 511 then
                        618
                      else
                        619
              else
                if x.val < 518 then
                  if x.val < 515 then
                    if x.val < 513 then
                      417
                    else
                      if x.val < 514 then
                        622
                      else
                        623
                  else
                    if x.val < 516 then
                      420
                    else
                      if x.val < 517 then
                        626
                      else
                        422
                else
                  if x.val < 521 then
                    if x.val < 519 then
                      615
                    else
                      if x.val < 520 then
                        628
                      else
                        630
                  else
                    if x.val < 523 then
                      if x.val < 522 then
                        425
                      else
                        426
                    else
                      if x.val < 524 then
                        634
                      else
                        427
            else
              if x.val < 537 then
                if x.val < 531 then
                  if x.val < 528 then
                    if x.val < 526 then
                      621
                    else
                      if x.val < 527 then
                        429
                      else
                        638
                  else
                    if x.val < 529 then
                      431
                    else
                      if x.val < 530 then
                        432
                      else
                        642
                else
                  if x.val < 534 then
                    if x.val < 532 then
                      433
                    else
                      if x.val < 533 then
                        643
                      else
                        617
                  else
                    if x.val < 535 then
                      645
                    else
                      if x.val < 536 then
                        437
                      else
                        648
              else
                if x.val < 543 then
                  if x.val < 540 then
                    if x.val < 538 then
                      649
                    else
                      if x.val < 539 then
                        650
                      else
                        441
                  else
                    if x.val < 541 then
                      442
                    else
                      if x.val < 542 then
                        542
                      else
                        541
                else
                  if x.val < 546 then
                    if x.val < 544 then
                      444
                    else
                      if x.val < 545 then
                        445
                      else
                        627
                  else
                    if x.val < 548 then
                      if x.val < 547 then
                        446
                      else
                        657
                    else
                      if x.val < 549 then
                        447
                      else
                        659
          else
            if x.val < 575 then
              if x.val < 562 then
                if x.val < 556 then
                  if x.val < 553 then
                    if x.val < 551 then
                      458
                    else
                      if x.val < 552 then
                        661
                      else
                        663
                  else
                    if x.val < 554 then
                      451
                    else
                      if x.val < 555 then
                        452
                      else
                        667
                else
                  if x.val < 559 then
                    if x.val < 557 then
                      453
                    else
                      if x.val < 558 then
                        669
                      else
                        670
                  else
                    if x.val < 560 then
                      672
                    else
                      if x.val < 561 then
                        674
                      else
                        658
              else
                if x.val < 568 then
                  if x.val < 565 then
                    if x.val < 563 then
                      459
                    else
                      if x.val < 564 then
                        677
                      else
                        460
                  else
                    if x.val < 566 then
                      461
                    else
                      if x.val < 567 then
                        680
                      else
                        462
                else
                  if x.val < 571 then
                    if x.val < 569 then
                      682
                    else
                      if x.val < 570 then
                        683
                      else
                        685
                  else
                    if x.val < 573 then
                      if x.val < 572 then
                        466
                      else
                        467
                    else
                      if x.val < 574 then
                        583
                      else
                        689
            else
              if x.val < 587 then
                if x.val < 581 then
                  if x.val < 578 then
                    if x.val < 576 then
                      470
                    else
                      if x.val < 577 then
                        471
                      else
                        693
                  else
                    if x.val < 579 then
                      694
                    else
                      if x.val < 580 then
                        696
                      else
                        474
                else
                  if x.val < 584 then
                    if x.val < 582 then
                      475
                    else
                      if x.val < 583 then
                        700
                      else
                        573
                  else
                    if x.val < 585 then
                      478
                    else
                      if x.val < 586 then
                        502
                      else
                        703
              else
                if x.val < 593 then
                  if x.val < 590 then
                    if x.val < 588 then
                      480
                    else
                      if x.val < 589 then
                        706
                      else
                        483
                  else
                    if x.val < 591 then
                      708
                    else
                      if x.val < 592 then
                        709
                      else
                        486
                else
                  if x.val < 596 then
                    if x.val < 594 then
                      487
                    else
                      if x.val < 595 then
                        712
                      else
                        488
                  else
                    if x.val < 598 then
                      if x.val < 597 then
                        714
                      else
                        715
                    else
                      if x.val < 599 then
                        717
                      else
                        491
      else
        if x.val < 700 then
          if x.val < 650 then
            if x.val < 625 then
              if x.val < 612 then
                if x.val < 606 then
                  if x.val < 603 then
                    if x.val < 601 then
                      720
                    else
                      if x.val < 602 then
                        493
                      else
                        722
                  else
                    if x.val < 604 then
                      723
                    else
                      if x.val < 605 then
                        496
                      else
                        725
                else
                  if x.val < 609 then
                    if x.val < 607 then
                      498
                    else
                      if x.val < 608 then
                        728
                      else
                        620
                  else
                    if x.val < 610 then
                      730
                    else
                      if x.val < 611 then
                        727
                      else
                        732
              else
                if x.val < 618 then
                  if x.val < 615 then
                    if x.val < 613 then
                      505
                    else
                      if x.val < 614 then
                        506
                      else
                        736
                  else
                    if x.val < 616 then
                      518
                    else
                      if x.val < 617 then
                        686
                      else
                        533
                else
                  if x.val < 621 then
                    if x.val < 619 then
                      510
                    else
                      if x.val < 620 then
                        511
                      else
                        608
                  else
                    if x.val < 623 then
                      if x.val < 622 then
                        525
                      else
                        513
                    else
                      if x.val < 624 then
                        514
                      else
                        743
            else
              if x.val < 637 then
                if x.val < 631 then
                  if x.val < 628 then
                    if x.val < 626 then
                      744
                    else
                      if x.val < 627 then
                        516
                      else
                        545
                  else
                    if x.val < 629 then
                      519
                    else
                      if x.val < 630 then
                        749
                      else
                        520
                else
                  if x.val < 634 then
                    if x.val < 632 then
                      751
                    else
                      if x.val < 633 then
                        752
                      else
                        754
                  else
                    if x.val < 635 then
                      523
                    else
                      if x.val < 636 then
                        756
                      else
                        758
              else
                if x.val < 643 then
                  if x.val < 640 then
                    if x.val < 638 then
                      759
                    else
                      if x.val < 639 then
                        527
                      else
                        762
                  else
                    if x.val < 641 then
                      763
                    else
                      if x.val < 642 then
                        765
                      else
                        530
                else
                  if x.val < 646 then
                    if x.val < 644 then
                      532
                    else
                      if x.val < 645 then
                        768
                      else
                        534
                  else
                    if x.val < 648 then
                      if x.val < 647 then
                        770
                      else
                        771
                    else
                      if x.val < 649 then
                        536
                      else
                        537
          else
            if x.val < 675 then
              if x.val < 662 then
                if x.val < 656 then
                  if x.val < 653 then
                    if x.val < 651 then
                      538
                    else
                      if x.val < 652 then
                        776
                      else
                        767
                  else
                    if x.val < 654 then
                      778
                    else
                      if x.val < 655 then
                        780
                      else
                        773
                else
                  if x.val < 659 then
                    if x.val < 657 then
                      782
                    else
                      if x.val < 658 then
                        547
                      else
                        561
                  else
                    if x.val < 660 then
                      549
                    else
                      if x.val < 661 then
                        786
                      else
                        551
              else
                if x.val < 668 then
                  if x.val < 665 then
                    if x.val < 663 then
                      788
                    else
                      if x.val < 664 then
                        552
                      else
                        790
                  else
                    if x.val < 666 then
                      784
                    else
                      if x.val < 667 then
                        792
                      else
                        555
                else
                  if x.val < 671 then
                    if x.val < 669 then
                      794
                    else
                      if x.val < 670 then
                        557
                      else
                        558
                  else
                    if x.val < 673 then
                      if x.val < 672 then
                        797
                      else
                        559
                    else
                      if x.val < 674 then
                        799
                      else
                        560
            else
              if x.val < 687 then
                if x.val < 681 then
                  if x.val < 678 then
                    if x.val < 676 then
                      800
                    else
                      if x.val < 677 then
                        801
                      else
                        563
                  else
                    if x.val < 679 then
                      804
                    else
                      if x.val < 680 then
                        805
                      else
                        566
                else
                  if x.val < 684 then
                    if x.val < 682 then
                      781
                    else
                      if x.val < 683 then
                        568
                      else
                        569
                  else
                    if x.val < 685 then
                      811
                    else
                      if x.val < 686 then
                        570
                      else
                        616
              else
                if x.val < 693 then
                  if x.val < 690 then
                    if x.val < 688 then
                      809
                    else
                      if x.val < 689 then
                        814
                      else
                        574
                  else
                    if x.val < 691 then
                      817
                    else
                      if x.val < 692 then
                        818
                      else
                        820
                else
                  if x.val < 696 then
                    if x.val < 694 then
                      577
                    else
                      if x.val < 695 then
                        578
                      else
                        824
                  else
                    if x.val < 698 then
                      if x.val < 697 then
                        579
                      else
                        826
                    else
                      if x.val < 699 then
                        827
                      else
                        829
        else
          if x.val < 750 then
            if x.val < 725 then
              if x.val < 712 then
                if x.val < 706 then
                  if x.val < 703 then
                    if x.val < 701 then
                      582
                    else
                      if x.val < 702 then
                        832
                      else
                        833
                  else
                    if x.val < 704 then
                      586
                    else
                      if x.val < 705 then
                        836
                      else
                        837
                else
                  if x.val < 709 then
                    if x.val < 707 then
                      588
                    else
                      if x.val < 708 then
                        839
                      else
                        590
                  else
                    if x.val < 710 then
                      591
                    else
                      if x.val < 711 then
                        843
                      else
                        844
              else
                if x.val < 718 then
                  if x.val < 715 then
                    if x.val < 713 then
                      594
                    else
                      if x.val < 714 then
                        847
                      else
                        596
                  else
                    if x.val < 716 then
                      597
                    else
                      if x.val < 717 then
                        851
                      else
                        598
                else
                  if x.val < 721 then
                    if x.val < 719 then
                      853
                    else
                      if x.val < 720 then
                        854
                      else
                        600
                  else
                    if x.val < 723 then
                      if x.val < 722 then
                        857
                      else
                        602
                    else
                      if x.val < 724 then
                        603
                      else
                        861
            else
              if x.val < 737 then
                if x.val < 731 then
                  if x.val < 728 then
                    if x.val < 726 then
                      605
                    else
                      if x.val < 727 then
                        863
                      else
                        610
                  else
                    if x.val < 729 then
                      607
                    else
                      if x.val < 730 then
                        866
                      else
                        609
                else
                  if x.val < 734 then
                    if x.val < 732 then
                      868
                    else
                      if x.val < 733 then
                        611
                      else
                        795
                  else
                    if x.val < 735 then
                      869
                    else
                      if x.val < 736 then
                        871
                      else
                        614
              else
                if x.val < 743 then
                  if x.val < 740 then
                    if x.val < 738 then
                      874
                    else
                      if x.val < 739 then
                        875
                      else
                        877
                  else
                    if x.val < 741 then
                      879
                    else
                      if x.val < 742 then
                        880
                      else
                        882
                else
                  if x.val < 746 then
                    if x.val < 744 then
                      624
                    else
                      if x.val < 745 then
                        625
                      else
                        885
                  else
                    if x.val < 748 then
                      if x.val < 747 then
                        886
                      else
                        887
                    else
                      if x.val < 749 then
                        888
                      else
                        629
          else
            if x.val < 775 then
              if x.val < 762 then
                if x.val < 756 then
                  if x.val < 753 then
                    if x.val < 751 then
                      891
                    else
                      if x.val < 752 then
                        631
                      else
                        632
                  else
                    if x.val < 754 then
                      895
                    else
                      if x.val < 755 then
                        633
                      else
                        897
                else
                  if x.val < 759 then
                    if x.val < 757 then
                      635
                    else
                      if x.val < 758 then
                        900
                      else
                        636
                  else
                    if x.val < 760 then
                      637
                    else
                      if x.val < 761 then
                        761
                      else
                        760
              else
                if x.val < 768 then
                  if x.val < 765 then
                    if x.val < 763 then
                      639
                    else
                      if x.val < 764 then
                        640
                      else
                        906
                  else
                    if x.val < 766 then
                      641
                    else
                      if x.val < 767 then
                        908
                      else
                        652
                else
                  if x.val < 771 then
                    if x.val < 769 then
                      644
                    else
                      if x.val < 770 then
                        911
                      else
                        646
                  else
                    if x.val < 773 then
                      if x.val < 772 then
                        647
                      else
                        914
                    else
                      if x.val < 774 then
                        655
                      else
                        916
            else
              if x.val < 787 then
                if x.val < 781 then
                  if x.val < 778 then
                    if x.val < 776 then
                      918
                    else
                      if x.val < 777 then
                        651
                      else
                        921
                  else
                    if x.val < 779 then
                      653
                    else
                      if x.val < 780 then
                        923
                      else
                        654
                else
                  if x.val < 784 then
                    if x.val < 782 then
                      681
                    else
                      if x.val < 783 then
                        656
                      else
                        925
                  else
                    if x.val < 785 then
                      665
                    else
                      if x.val < 786 then
                        926
                      else
                        660
              else
                if x.val < 793 then
                  if x.val < 790 then
                    if x.val < 788 then
                      929
                    else
                      if x.val < 789 then
                        662
                      else
                        924
                  else
                    if x.val < 791 then
                      664
                    else
                      if x.val < 792 then
                        933
                      else
                        666
                else
                  if x.val < 796 then
                    if x.val < 794 then
                      935
                    else
                      if x.val < 795 then
                        668
                      else
                        733
                  else
                    if x.val < 798 then
                      if x.val < 797 then
                        894
                      else
                        671
                    else
                      if x.val < 799 then
                        920
                      else
                        673
  else
    if x.val < 1200 then
      if x.val < 1000 then
        if x.val < 900 then
          if x.val < 850 then
            if x.val < 825 then
              if x.val < 812 then
                if x.val < 806 then
                  if x.val < 803 then
                    if x.val < 801 then
                      675
                    else
                      if x.val < 802 then
                        676
                      else
                        944
                  else
                    if x.val < 804 then
                      941
                    else
                      if x.val < 805 then
                        678
                      else
                        679
                else
                  if x.val < 809 then
                    if x.val < 807 then
                      948
                    else
                      if x.val < 808 then
                        949
                      else
                        930
                  else
                    if x.val < 810 then
                      687
                    else
                      if x.val < 811 then
                        952
                      else
                        684
              else
                if x.val < 818 then
                  if x.val < 815 then
                    if x.val < 813 then
                      955
                    else
                      if x.val < 814 then
                        957
                      else
                        688
                  else
                    if x.val < 816 then
                      959
                    else
                      if x.val < 817 then
                        960
                      else
                        690
                else
                  if x.val < 821 then
                    if x.val < 819 then
                      691
                    else
                      if x.val < 820 then
                        964
                      else
                        692
                  else
                    if x.val < 823 then
                      if x.val < 822 then
                        966
                      else
                        962
                    else
                      if x.val < 824 then
                        968
                      else
                        695
            else
              if x.val < 837 then
                if x.val < 831 then
                  if x.val < 828 then
                    if x.val < 826 then
                      970
                    else
                      if x.val < 827 then
                        697
                      else
                        698
                  else
                    if x.val < 829 then
                      974
                    else
                      if x.val < 830 then
                        699
                      else
                        975
                else
                  if x.val < 834 then
                    if x.val < 832 then
                      976
                    else
                      if x.val < 833 then
                        701
                      else
                        702
                  else
                    if x.val < 835 then
                      978
                    else
                      if x.val < 836 then
                        901
                      else
                        704
              else
                if x.val < 843 then
                  if x.val < 840 then
                    if x.val < 838 then
                      705
                    else
                      if x.val < 839 then
                        982
                      else
                        707
                  else
                    if x.val < 841 then
                      984
                    else
                      if x.val < 842 then
                        985
                      else
                        987
                else
                  if x.val < 846 then
                    if x.val < 844 then
                      710
                    else
                      if x.val < 845 then
                        711
                      else
                        973
                  else
                    if x.val < 848 then
                      if x.val < 847 then
                        991
                      else
                        713
                    else
                      if x.val < 849 then
                        994
                      else
                        995
          else
            if x.val < 875 then
              if x.val < 862 then
                if x.val < 856 then
                  if x.val < 853 then
                    if x.val < 851 then
                      997
                    else
                      if x.val < 852 then
                        716
                      else
                        999
                  else
                    if x.val < 854 then
                      718
                    else
                      if x.val < 855 then
                        719
                      else
                        1002
                else
                  if x.val < 859 then
                    if x.val < 857 then
                      1003
                    else
                      if x.val < 858 then
                        721
                      else
                        963
                  else
                    if x.val < 860 then
                      1001
                    else
                      if x.val < 861 then
                        1006
                      else
                        724
              else
                if x.val < 868 then
                  if x.val < 865 then
                    if x.val < 863 then
                      1009
                    else
                      if x.val < 864 then
                        726
                      else
                        1011
                  else
                    if x.val < 866 then
                      1012
                    else
                      if x.val < 867 then
                        729
                      else
                        1014
                else
                  if x.val < 871 then
                    if x.val < 869 then
                      731
                    else
                      if x.val < 870 then
                        734
                      else
                        1016
                  else
                    if x.val < 873 then
                      if x.val < 872 then
                        735
                      else
                        1018
                    else
                      if x.val < 874 then
                        939
                      else
                        737
            else
              if x.val < 887 then
                if x.val < 881 then
                  if x.val < 878 then
                    if x.val < 876 then
                      738
                    else
                      if x.val < 877 then
                        1021
                      else
                        739
                  else
                    if x.val < 879 then
                      902
                    else
                      if x.val < 880 then
                        740
                      else
                        741
                else
                  if x.val < 884 then
                    if x.val < 882 then
                      1024
                    else
                      if x.val < 883 then
                        742
                      else
                        1026
                  else
                    if x.val < 885 then
                      943
                    else
                      if x.val < 886 then
                        745
                      else
                        746
              else
                if x.val < 893 then
                  if x.val < 890 then
                    if x.val < 888 then
                      747
                    else
                      if x.val < 889 then
                        748
                      else
                        1031
                  else
                    if x.val < 891 then
                      1032
                    else
                      if x.val < 892 then
                        750
                      else
                        1035
                else
                  if x.val < 896 then
                    if x.val < 894 then
                      1036
                    else
                      if x.val < 895 then
                        796
                      else
                        753
                  else
                    if x.val < 898 then
                      if x.val < 897 then
                        1040
                      else
                        755
                    else
                      if x.val < 899 then
                        1023
                      else
                        1043
        else
          if x.val < 950 then
            if x.val < 925 then
              if x.val < 912 then
                if x.val < 906 then
                  if x.val < 903 then
                    if x.val < 901 then
                      757
                    else
                      if x.val < 902 then
                        835
                      else
                        878
                  else
                    if x.val < 904 then
                      1046
                    else
                      if x.val < 905 then
                        1047
                      else
                        1049
                else
                  if x.val < 909 then
                    if x.val < 907 then
                      764
                    else
                      if x.val < 908 then
                        1051
                      else
                        766
                  else
                    if x.val < 910 then
                      1054
                    else
                      if x.val < 911 then
                        1055
                      else
                        769
              else
                if x.val < 918 then
                  if x.val < 915 then
                    if x.val < 913 then
                      1045
                    else
                      if x.val < 914 then
                        1053
                      else
                        772
                  else
                    if x.val < 916 then
                      1058
                    else
                      if x.val < 917 then
                        774
                      else
                        1060
                else
                  if x.val < 921 then
                    if x.val < 919 then
                      775
                    else
                      if x.val < 920 then
                        1061
                      else
                        798
                  else
                    if x.val < 923 then
                      if x.val < 922 then
                        777
                      else
                        1064
                    else
                      if x.val < 924 then
                        779
                      else
                        789
            else
              if x.val < 937 then
                if x.val < 931 then
                  if x.val < 928 then
                    if x.val < 926 then
                      783
                    else
                      if x.val < 927 then
                        785
                      else
                        1069
                  else
                    if x.val < 929 then
                      1070
                    else
                      if x.val < 930 then
                        787
                      else
                        808
                else
                  if x.val < 934 then
                    if x.val < 932 then
                      1074
                    else
                      if x.val < 933 then
                        1075
                      else
                        791
                  else
                    if x.val < 935 then
                      1078
                    else
                      if x.val < 936 then
                        793
                      else
                        937
              else
                if x.val < 943 then
                  if x.val < 940 then
                    if x.val < 938 then
                      936
                    else
                      if x.val < 939 then
                        1013
                      else
                        873
                  else
                    if x.val < 941 then
                      1083
                    else
                      if x.val < 942 then
                        803
                      else
                        1085
                else
                  if x.val < 946 then
                    if x.val < 944 then
                      884
                    else
                      if x.val < 945 then
                        802
                      else
                        1088
                  else
                    if x.val < 948 then
                      if x.val < 947 then
                        1089
                      else
                        1090
                    else
                      if x.val < 949 then
                        806
                      else
                        807
          else
            if x.val < 975 then
              if x.val < 962 then
                if x.val < 956 then
                  if x.val < 953 then
                    if x.val < 951 then
                      1093
                    else
                      if x.val < 952 then
                        1094
                      else
                        810
                  else
                    if x.val < 954 then
                      1096
                    else
                      if x.val < 955 then
                        1092
                      else
                        812
                else
                  if x.val < 959 then
                    if x.val < 957 then
                      1098
                    else
                      if x.val < 958 then
                        813
                      else
                        1100
                  else
                    if x.val < 960 then
                      815
                    else
                      if x.val < 961 then
                        816
                      else
                        1102
              else
                if x.val < 968 then
                  if x.val < 965 then
                    if x.val < 963 then
                      822
                    else
                      if x.val < 964 then
                        858
                      else
                        819
                  else
                    if x.val < 966 then
                      1105
                    else
                      if x.val < 967 then
                        821
                      else
                        1108
                else
                  if x.val < 971 then
                    if x.val < 969 then
                      823
                    else
                      if x.val < 970 then
                        1109
                      else
                        825
                  else
                    if x.val < 973 then
                      if x.val < 972 then
                        1112
                      else
                        1113
                    else
                      if x.val < 974 then
                        845
                      else
                        828
            else
              if x.val < 987 then
                if x.val < 981 then
                  if x.val < 978 then
                    if x.val < 976 then
                      830
                    else
                      if x.val < 977 then
                        831
                      else
                        1118
                  else
                    if x.val < 979 then
                      834
                    else
                      if x.val < 980 then
                        1120
                      else
                        1121
                else
                  if x.val < 984 then
                    if x.val < 982 then
                      1123
                    else
                      if x.val < 983 then
                        838
                      else
                        1057
                  else
                    if x.val < 985 then
                      840
                    else
                      if x.val < 986 then
                        841
                      else
                        1129
              else
                if x.val < 993 then
                  if x.val < 990 then
                    if x.val < 988 then
                      842
                    else
                      if x.val < 989 then
                        1130
                      else
                        1131
                  else
                    if x.val < 991 then
                      1133
                    else
                      if x.val < 992 then
                        846
                      else
                        993
                else
                  if x.val < 996 then
                    if x.val < 994 then
                      992
                    else
                      if x.val < 995 then
                        848
                      else
                        849
                  else
                    if x.val < 998 then
                      if x.val < 997 then
                        1135
                      else
                        850
                    else
                      if x.val < 999 then
                        1137
                      else
                        852
      else
        if x.val < 1100 then
          if x.val < 1050 then
            if x.val < 1025 then
              if x.val < 1012 then
                if x.val < 1006 then
                  if x.val < 1003 then
                    if x.val < 1001 then
                      1138
                    else
                      if x.val < 1002 then
                        859
                      else
                        855
                  else
                    if x.val < 1004 then
                      856
                    else
                      if x.val < 1005 then
                        1142
                      else
                        1143
                else
                  if x.val < 1009 then
                    if x.val < 1007 then
                      860
                    else
                      if x.val < 1008 then
                        1145
                      else
                        1029
                  else
                    if x.val < 1010 then
                      862
                    else
                      if x.val < 1011 then
                        1147
                      else
                        864
              else
                if x.val < 1018 then
                  if x.val < 1015 then
                    if x.val < 1013 then
                      865
                    else
                      if x.val < 1014 then
                        938
                      else
                        867
                  else
                    if x.val < 1016 then
                      1150
                    else
                      if x.val < 1017 then
                        870
                      else
                        1152
                else
                  if x.val < 1021 then
                    if x.val < 1019 then
                      872
                    else
                      if x.val < 1020 then
                        1154
                      else
                        1156
                  else
                    if x.val < 1023 then
                      if x.val < 1022 then
                        876
                      else
                        1158
                    else
                      if x.val < 1024 then
                        898
                      else
                        881
            else
              if x.val < 1037 then
                if x.val < 1031 then
                  if x.val < 1028 then
                    if x.val < 1026 then
                      1161
                    else
                      if x.val < 1027 then
                        883
                      else
                        1041
                  else
                    if x.val < 1029 then
                      1080
                    else
                      if x.val < 1030 then
                        1008
                      else
                        1167
                else
                  if x.val < 1034 then
                    if x.val < 1032 then
                      889
                    else
                      if x.val < 1033 then
                        890
                      else
                        1034
                  else
                    if x.val < 1035 then
                      1033
                    else
                      if x.val < 1036 then
                        892
                      else
                        893
              else
                if x.val < 1043 then
                  if x.val < 1040 then
                    if x.val < 1038 then
                      1171
                    else
                      if x.val < 1039 then
                        1172
                      else
                        1173
                  else
                    if x.val < 1041 then
                      896
                    else
                      if x.val < 1042 then
                        1027
                      else
                        1176
                else
                  if x.val < 1046 then
                    if x.val < 1044 then
                      899
                    else
                      if x.val < 1045 then
                        1178
                      else
                        912
                  else
                    if x.val < 1048 then
                      if x.val < 1047 then
                        903
                      else
                        904
                    else
                      if x.val < 1049 then
                        1181
                      else
                        905
          else
            if x.val < 1075 then
              if x.val < 1062 then
                if x.val < 1056 then
                  if x.val < 1053 then
                    if x.val < 1051 then
                      1124
                    else
                      if x.val < 1052 then
                        907
                      else
                        1184
                  else
                    if x.val < 1054 then
                      913
                    else
                      if x.val < 1055 then
                        909
                      else
                        910
                else
                  if x.val < 1059 then
                    if x.val < 1057 then
                      1188
                    else
                      if x.val < 1058 then
                        983
                      else
                        915
                  else
                    if x.val < 1060 then
                      1190
                    else
                      if x.val < 1061 then
                        917
                      else
                        919
              else
                if x.val < 1068 then
                  if x.val < 1065 then
                    if x.val < 1063 then
                      1193
                    else
                      if x.val < 1064 then
                        1194
                      else
                        922
                  else
                    if x.val < 1066 then
                      1196
                    else
                      if x.val < 1067 then
                        1191
                      else
                        1084
                else
                  if x.val < 1071 then
                    if x.val < 1069 then
                      1197
                    else
                      if x.val < 1070 then
                        927
                      else
                        928
                  else
                    if x.val < 1073 then
                      if x.val < 1072 then
                        1200
                      else
                        1201
                    else
                      if x.val < 1074 then
                        1149
                      else
                        931
            else
              if x.val < 1087 then
                if x.val < 1081 then
                  if x.val < 1078 then
                    if x.val < 1076 then
                      932
                    else
                      if x.val < 1077 then
                        1166
                      else
                        1204
                  else
                    if x.val < 1079 then
                      934
                    else
                      if x.val < 1080 then
                        1207
                      else
                        1028
                else
                  if x.val < 1084 then
                    if x.val < 1082 then
                      1209
                    else
                      if x.val < 1083 then
                        1210
                      else
                        940
                  else
                    if x.val < 1085 then
                      1067
                    else
                      if x.val < 1086 then
                        942
                      else
                        1211
              else
                if x.val < 1093 then
                  if x.val < 1090 then
                    if x.val < 1088 then
                      1212
                    else
                      if x.val < 1089 then
                        945
                      else
                        946
                  else
                    if x.val < 1091 then
                      947
                    else
                      if x.val < 1092 then
                        1217
                      else
                        954
                else
                  if x.val < 1096 then
                    if x.val < 1094 then
                      950
                    else
                      if x.val < 1095 then
                        951
                      else
                        1221
                  else
                    if x.val < 1098 then
                      if x.val < 1097 then
                        953
                      else
                        1223
                    else
                      if x.val < 1099 then
                        956
                      else
                        1224
        else
          if x.val < 1150 then
            if x.val < 1125 then
              if x.val < 1112 then
                if x.val < 1106 then
                  if x.val < 1103 then
                    if x.val < 1101 then
                      958
                    else
                      if x.val < 1102 then
                        1225
                      else
                        961
                  else
                    if x.val < 1104 then
                      1125
                    else
                      if x.val < 1105 then
                        1228
                      else
                        965
                else
                  if x.val < 1109 then
                    if x.val < 1107 then
                      1231
                    else
                      if x.val < 1108 then
                        1232
                      else
                        967
                  else
                    if x.val < 1110 then
                      969
                    else
                      if x.val < 1111 then
                        1111
                      else
                        1110
              else
                if x.val < 1118 then
                  if x.val < 1115 then
                    if x.val < 1113 then
                      971
                    else
                      if x.val < 1114 then
                        972
                      else
                        1237
                  else
                    if x.val < 1116 then
                      1238
                    else
                      if x.val < 1117 then
                        1239
                      else
                        1241
                else
                  if x.val < 1121 then
                    if x.val < 1119 then
                      977
                    else
                      if x.val < 1120 then
                        1243
                      else
                        979
                  else
                    if x.val < 1123 then
                      if x.val < 1122 then
                        980
                      else
                        1245
                    else
                      if x.val < 1124 then
                        981
                      else
                        1050
            else
              if x.val < 1137 then
                if x.val < 1131 then
                  if x.val < 1128 then
                    if x.val < 1126 then
                      1103
                    else
                      if x.val < 1127 then
                        1248
                      else
                        1249
                  else
                    if x.val < 1129 then
                      1250
                    else
                      if x.val < 1130 then
                        986
                      else
                        988
                else
                  if x.val < 1134 then
                    if x.val < 1132 then
                      989
                    else
                      if x.val < 1133 then
                        1252
                      else
                        990
                  else
                    if x.val < 1135 then
                      1253
                    else
                      if x.val < 1136 then
                        996
                      else
                        1247
              else
                if x.val < 1143 then
                  if x.val < 1140 then
                    if x.val < 1138 then
                      998
                    else
                      if x.val < 1139 then
                        1000
                      else
                        1235
                  else
                    if x.val < 1141 then
                      1257
                    else
                      if x.val < 1142 then
                        1259
                      else
                        1004
                else
                  if x.val < 1146 then
                    if x.val < 1144 then
                      1005
                    else
                      if x.val < 1145 then
                        1263
                      else
                        1007
                  else
                    if x.val < 1148 then
                      if x.val < 1147 then
                        1265
                      else
                        1010
                    else
                      if x.val < 1149 then
                        1267
                      else
                        1073
          else
            if x.val < 1175 then
              if x.val < 1162 then
                if x.val < 1156 then
                  if x.val < 1153 then
                    if x.val < 1151 then
                      1015
                    else
                      if x.val < 1152 then
                        1270
                      else
                        1017
                  else
                    if x.val < 1154 then
                      1272
                    else
                      if x.val < 1155 then
                        1019
                      else
                        1274
                else
                  if x.val < 1159 then
                    if x.val < 1157 then
                      1020
                    else
                      if x.val < 1158 then
                        1275
                      else
                        1022
                  else
                    if x.val < 1160 then
                      1276
                    else
                      if x.val < 1161 then
                        1277
                      else
                        1025
              else
                if x.val < 1168 then
                  if x.val < 1165 then
                    if x.val < 1163 then
                      1280
                    else
                      if x.val < 1164 then
                        1281
                      else
                        1283
                  else
                    if x.val < 1166 then
                      1213
                    else
                      if x.val < 1167 then
                        1076
                      else
                        1030
                else
                  if x.val < 1171 then
                    if x.val < 1169 then
                      1284
                    else
                      if x.val < 1170 then
                        1285
                      else
                        1287
                  else
                    if x.val < 1173 then
                      if x.val < 1172 then
                        1037
                      else
                        1038
                    else
                      if x.val < 1174 then
                        1039
                      else
                        1290
            else
              if x.val < 1187 then
                if x.val < 1181 then
                  if x.val < 1178 then
                    if x.val < 1176 then
                      1291
                    else
                      if x.val < 1177 then
                        1042
                      else
                        1293
                  else
                    if x.val < 1179 then
                      1044
                    else
                      if x.val < 1180 then
                        1295
                      else
                        1296
                else
                  if x.val < 1184 then
                    if x.val < 1182 then
                      1048
                    else
                      if x.val < 1183 then
                        1298
                      else
                        1299
                  else
                    if x.val < 1185 then
                      1052
                    else
                      if x.val < 1186 then
                        1264
                      else
                        1269
              else
                if x.val < 1193 then
                  if x.val < 1190 then
                    if x.val < 1188 then
                      1301
                    else
                      if x.val < 1189 then
                        1056
                      else
                        1304
                  else
                    if x.val < 1191 then
                      1059
                    else
                      if x.val < 1192 then
                        1066
                      else
                        1307
                else
                  if x.val < 1196 then
                    if x.val < 1194 then
                      1062
                    else
                      if x.val < 1195 then
                        1063
                      else
                        1311
                  else
                    if x.val < 1198 then
                      if x.val < 1197 then
                        1065
                      else
                        1068
                    else
                      if x.val < 1199 then
                        1313
                      else
                        1314
    else
      if x.val < 1400 then
        if x.val < 1300 then
          if x.val < 1250 then
            if x.val < 1225 then
              if x.val < 1212 then
                if x.val < 1206 then
                  if x.val < 1203 then
                    if x.val < 1201 then
                      1071
                    else
                      if x.val < 1202 then
                        1072
                      else
                        1318
                  else
                    if x.val < 1204 then
                      1320
                    else
                      if x.val < 1205 then
                        1077
                      else
                        1322
                else
                  if x.val < 1209 then
                    if x.val < 1207 then
                      1323
                    else
                      if x.val < 1208 then
                        1079
                      else
                        1326
                  else
                    if x.val < 1210 then
                      1081
                    else
                      if x.val < 1211 then
                        1082
                      else
                        1086
              else
                if x.val < 1218 then
                  if x.val < 1215 then
                    if x.val < 1213 then
                      1087
                    else
                      if x.val < 1214 then
                        1165
                      else
                        1331
                  else
                    if x.val < 1216 then
                      1333
                    else
                      if x.val < 1217 then
                        1334
                      else
                        1091
                else
                  if x.val < 1221 then
                    if x.val < 1219 then
                      1336
                    else
                      if x.val < 1220 then
                        1337
                      else
                        1321
                  else
                    if x.val < 1223 then
                      if x.val < 1222 then
                        1095
                      else
                        1340
                    else
                      if x.val < 1224 then
                        1097
                      else
                        1099
            else
              if x.val < 1237 then
                if x.val < 1231 then
                  if x.val < 1228 then
                    if x.val < 1226 then
                      1101
                    else
                      if x.val < 1227 then
                        1342
                      else
                        1343
                  else
                    if x.val < 1229 then
                      1104
                    else
                      if x.val < 1230 then
                        1346
                      else
                        1347
                else
                  if x.val < 1234 then
                    if x.val < 1232 then
                      1106
                    else
                      if x.val < 1233 then
                        1107
                      else
                        1341
                  else
                    if x.val < 1235 then
                      1350
                    else
                      if x.val < 1236 then
                        1139
                      else
                        1351
              else
                if x.val < 1243 then
                  if x.val < 1240 then
                    if x.val < 1238 then
                      1114
                    else
                      if x.val < 1239 then
                        1115
                      else
                        1116
                  else
                    if x.val < 1241 then
                      1354
                    else
                      if x.val < 1242 then
                        1117
                      else
                        1355
                else
                  if x.val < 1246 then
                    if x.val < 1244 then
                      1119
                    else
                      if x.val < 1245 then
                        1289
                      else
                        1122
                  else
                    if x.val < 1248 then
                      if x.val < 1247 then
                        1358
                      else
                        1136
                    else
                      if x.val < 1249 then
                        1126
                      else
                        1127
          else
            if x.val < 1275 then
              if x.val < 1262 then
                if x.val < 1256 then
                  if x.val < 1253 then
                    if x.val < 1251 then
                      1128
                    else
                      if x.val < 1252 then
                        1362
                      else
                        1132
                  else
                    if x.val < 1254 then
                      1134
                    else
                      if x.val < 1255 then
                        1365
                      else
                        1366
                else
                  if x.val < 1259 then
                    if x.val < 1257 then
                      1367
                    else
                      if x.val < 1258 then
                        1140
                      else
                        1369
                  else
                    if x.val < 1260 then
                      1141
                    else
                      if x.val < 1261 then
                        1371
                      else
                        1372
              else
                if x.val < 1268 then
                  if x.val < 1265 then
                    if x.val < 1263 then
                      1344
                    else
                      if x.val < 1264 then
                        1144
                      else
                        1185
                  else
                    if x.val < 1266 then
                      1146
                    else
                      if x.val < 1267 then
                        1375
                      else
                        1148
                else
                  if x.val < 1271 then
                    if x.val < 1269 then
                      1377
                    else
                      if x.val < 1270 then
                        1186
                      else
                        1151
                  else
                    if x.val < 1273 then
                      if x.val < 1272 then
                        1379
                      else
                        1153
                    else
                      if x.val < 1274 then
                        1381
                      else
                        1155
            else
              if x.val < 1287 then
                if x.val < 1281 then
                  if x.val < 1278 then
                    if x.val < 1276 then
                      1157
                    else
                      if x.val < 1277 then
                        1159
                      else
                        1160
                  else
                    if x.val < 1279 then
                      1279
                    else
                      if x.val < 1280 then
                        1278
                      else
                        1162
                else
                  if x.val < 1284 then
                    if x.val < 1282 then
                      1163
                    else
                      if x.val < 1283 then
                        1386
                      else
                        1164
                  else
                    if x.val < 1285 then
                      1168
                    else
                      if x.val < 1286 then
                        1169
                      else
                        1390
              else
                if x.val < 1293 then
                  if x.val < 1290 then
                    if x.val < 1288 then
                      1170
                    else
                      if x.val < 1289 then
                        1328
                      else
                        1244
                  else
                    if x.val < 1291 then
                      1174
                    else
                      if x.val < 1292 then
                        1175
                      else
                        1395
                else
                  if x.val < 1296 then
                    if x.val < 1294 then
                      1177
                    else
                      if x.val < 1295 then
                        1398
                      else
                        1179
                  else
                    if x.val < 1298 then
                      if x.val < 1297 then
                        1180
                      else
                        1399
                    else
                      if x.val < 1299 then
                        1182
                      else
                        1183
        else
          if x.val < 1350 then
            if x.val < 1325 then
              if x.val < 1312 then
                if x.val < 1306 then
                  if x.val < 1303 then
                    if x.val < 1301 then
                      1402
                    else
                      if x.val < 1302 then
                        1187
                      else
                        1403
                  else
                    if x.val < 1304 then
                      1404
                    else
                      if x.val < 1305 then
                        1189
                      else
                        1406
                else
                  if x.val < 1309 then
                    if x.val < 1307 then
                      1407
                    else
                      if x.val < 1308 then
                        1192
                      else
                        1410
                  else
                    if x.val < 1310 then
                      1396
                    else
                      if x.val < 1311 then
                        1412
                      else
                        1195
              else
                if x.val < 1318 then
                  if x.val < 1315 then
                    if x.val < 1313 then
                      1414
                    else
                      if x.val < 1314 then
                        1198
                      else
                        1199
                  else
                    if x.val < 1316 then
                      1416
                    else
                      if x.val < 1317 then
                        1417
                      else
                        1419
                else
                  if x.val < 1321 then
                    if x.val < 1319 then
                      1202
                    else
                      if x.val < 1320 then
                        1421
                      else
                        1203
                  else
                    if x.val < 1323 then
                      if x.val < 1322 then
                        1220
                      else
                        1205
                    else
                      if x.val < 1324 then
                        1206
                      else
                        1425
            else
              if x.val < 1337 then
                if x.val < 1331 then
                  if x.val < 1328 then
                    if x.val < 1326 then
                      1426
                    else
                      if x.val < 1327 then
                        1208
                      else
                        1428
                  else
                    if x.val < 1329 then
                      1288
                    else
                      if x.val < 1330 then
                        1370
                      else
                        1430
                else
                  if x.val < 1334 then
                    if x.val < 1332 then
                      1214
                    else
                      if x.val < 1333 then
                        1431
                      else
                        1215
                  else
                    if x.val < 1335 then
                      1216
                    else
                      if x.val < 1336 then
                        1434
                      else
                        1218
              else
                if x.val < 1343 then
                  if x.val < 1340 then
                    if x.val < 1338 then
                      1219
                    else
                      if x.val < 1339 then
                        1427
                      else
                        1437
                  else
                    if x.val < 1341 then
                      1222
                    else
                      if x.val < 1342 then
                        1233
                      else
                        1226
                else
                  if x.val < 1346 then
                    if x.val < 1344 then
                      1227
                    else
                      if x.val < 1345 then
                        1262
                      else
                        1439
                  else
                    if x.val < 1348 then
                      if x.val < 1347 then
                        1229
                      else
                        1230
                    else
                      if x.val < 1349 then
                        1441
                      else
                        1442
          else
            if x.val < 1375 then
              if x.val < 1362 then
                if x.val < 1356 then
                  if x.val < 1353 then
                    if x.val < 1351 then
                      1234
                    else
                      if x.val < 1352 then
                        1236
                      else
                        1420
                  else
                    if x.val < 1354 then
                      1444
                    else
                      if x.val < 1355 then
                        1240
                      else
                        1242
                else
                  if x.val < 1359 then
                    if x.val < 1357 then
                      1432
                    else
                      if x.val < 1358 then
                        1448
                      else
                        1246
                  else
                    if x.val < 1360 then
                      1449
                    else
                      if x.val < 1361 then
                        1445
                      else
                        1451
              else
                if x.val < 1368 then
                  if x.val < 1365 then
                    if x.val < 1363 then
                      1251
                    else
                      if x.val < 1364 then
                        1454
                      else
                        1455
                  else
                    if x.val < 1366 then
                      1254
                    else
                      if x.val < 1367 then
                        1255
                      else
                        1256
                else
                  if x.val < 1371 then
                    if x.val < 1369 then
                      1458
                    else
                      if x.val < 1370 then
                        1258
                      else
                        1329
                  else
                    if x.val < 1373 then
                      if x.val < 1372 then
                        1260
                      else
                        1261
                    else
                      if x.val < 1374 then
                        1440
                      else
                        1464
            else
              if x.val < 1387 then
                if x.val < 1381 then
                  if x.val < 1378 then
                    if x.val < 1376 then
                      1266
                    else
                      if x.val < 1377 then
                        1465
                      else
                        1268
                  else
                    if x.val < 1379 then
                      1468
                    else
                      if x.val < 1380 then
                        1271
                      else
                        1470
                else
                  if x.val < 1384 then
                    if x.val < 1382 then
                      1273
                    else
                      if x.val < 1383 then
                        1462
                      else
                        1472
                  else
                    if x.val < 1385 then
                      1392
                    else
                      if x.val < 1386 then
                        1474
                      else
                        1282
              else
                if x.val < 1393 then
                  if x.val < 1390 then
                    if x.val < 1388 then
                      1475
                    else
                      if x.val < 1389 then
                        1476
                      else
                        1477
                  else
                    if x.val < 1391 then
                      1286
                    else
                      if x.val < 1392 then
                        1393
                      else
                        1384
                else
                  if x.val < 1396 then
                    if x.val < 1394 then
                      1391
                    else
                      if x.val < 1395 then
                        1473
                      else
                        1292
                  else
                    if x.val < 1398 then
                      if x.val < 1397 then
                        1309
                      else
                        1429
                    else
                      if x.val < 1399 then
                        1294
                      else
                        1297
      else
        if x.val < 1500 then
          if x.val < 1450 then
            if x.val < 1425 then
              if x.val < 1412 then
                if x.val < 1406 then
                  if x.val < 1403 then
                    if x.val < 1401 then
                      1481
                    else
                      if x.val < 1402 then
                        1482
                      else
                        1300
                  else
                    if x.val < 1404 then
                      1302
                    else
                      if x.val < 1405 then
                        1303
                      else
                        1485
                else
                  if x.val < 1409 then
                    if x.val < 1407 then
                      1305
                    else
                      if x.val < 1408 then
                        1306
                      else
                        1489
                  else
                    if x.val < 1410 then
                      1490
                    else
                      if x.val < 1411 then
                        1308
                      else
                        1478
              else
                if x.val < 1418 then
                  if x.val < 1415 then
                    if x.val < 1413 then
                      1310
                    else
                      if x.val < 1414 then
                        1493
                      else
                        1312
                  else
                    if x.val < 1416 then
                      1496
                    else
                      if x.val < 1417 then
                        1315
                      else
                        1316
                else
                  if x.val < 1421 then
                    if x.val < 1419 then
                      1498
                    else
                      if x.val < 1420 then
                        1317
                      else
                        1352
                  else
                    if x.val < 1423 then
                      if x.val < 1422 then
                        1319
                      else
                        1487
                    else
                      if x.val < 1424 then
                        1500
                      else
                        1502
            else
              if x.val < 1437 then
                if x.val < 1431 then
                  if x.val < 1428 then
                    if x.val < 1426 then
                      1324
                    else
                      if x.val < 1427 then
                        1325
                      else
                        1338
                  else
                    if x.val < 1429 then
                      1327
                    else
                      if x.val < 1430 then
                        1397
                      else
                        1330
                else
                  if x.val < 1434 then
                    if x.val < 1432 then
                      1332
                    else
                      if x.val < 1433 then
                        1356
                      else
                        1452
                  else
                    if x.val < 1435 then
                      1335
                    else
                      if x.val < 1436 then
                        1508
                      else
                        1510
              else
                if x.val < 1443 then
                  if x.val < 1440 then
                    if x.val < 1438 then
                      1339
                    else
                      if x.val < 1439 then
                        1513
                      else
                        1345
                  else
                    if x.val < 1441 then
                      1373
                    else
                      if x.val < 1442 then
                        1348
                      else
                        1349
                else
                  if x.val < 1446 then
                    if x.val < 1444 then
                      1469
                    else
                      if x.val < 1445 then
                        1353
                      else
                        1360
                  else
                    if x.val < 1448 then
                      if x.val < 1447 then
                        1518
                      else
                        1519
                    else
                      if x.val < 1449 then
                        1357
                      else
                        1359
          else
            if x.val < 1475 then
              if x.val < 1462 then
                if x.val < 1456 then
                  if x.val < 1453 then
                    if x.val < 1451 then
                      1521
                    else
                      if x.val < 1452 then
                        1361
                      else
                        1433
                  else
                    if x.val < 1454 then
                      1522
                    else
                      if x.val < 1455 then
                        1363
                      else
                        1364
                else
                  if x.val < 1459 then
                    if x.val < 1457 then
                      1512
                    else
                      if x.val < 1458 then
                        1523
                      else
                        1368
                  else
                    if x.val < 1460 then
                      1517
                    else
                      if x.val < 1461 then
                        1525
                      else
                        1526
              else
                if x.val < 1468 then
                  if x.val < 1465 then
                    if x.val < 1463 then
                      1382
                    else
                      if x.val < 1464 then
                        1514
                      else
                        1374
                  else
                    if x.val < 1466 then
                      1376
                    else
                      if x.val < 1467 then
                        1527
                      else
                        1528
                else
                  if x.val < 1471 then
                    if x.val < 1469 then
                      1378
                    else
                      if x.val < 1470 then
                        1443
                      else
                        1380
                  else
                    if x.val < 1473 then
                      if x.val < 1472 then
                        1532
                      else
                        1383
                    else
                      if x.val < 1474 then
                        1394
                      else
                        1385
            else
              if x.val < 1487 then
                if x.val < 1481 then
                  if x.val < 1478 then
                    if x.val < 1476 then
                      1387
                    else
                      if x.val < 1477 then
                        1388
                      else
                        1389
                  else
                    if x.val < 1479 then
                      1411
                    else
                      if x.val < 1480 then
                        1480
                      else
                        1479
                else
                  if x.val < 1484 then
                    if x.val < 1482 then
                      1400
                    else
                      if x.val < 1483 then
                        1401
                      else
                        1536
                  else
                    if x.val < 1485 then
                      1537
                    else
                      if x.val < 1486 then
                        1405
                      else
                        1538
              else
                if x.val < 1493 then
                  if x.val < 1490 then
                    if x.val < 1488 then
                      1422
                    else
                      if x.val < 1489 then
                        1540
                      else
                        1408
                  else
                    if x.val < 1491 then
                      1409
                    else
                      if x.val < 1492 then
                        1501
                      else
                        1505
                else
                  if x.val < 1496 then
                    if x.val < 1494 then
                      1413
                    else
                      if x.val < 1495 then
                        1524
                      else
                        1544
                  else
                    if x.val < 1498 then
                      if x.val < 1497 then
                        1415
                      else
                        1546
                    else
                      if x.val < 1499 then
                        1418
                      else
                        1548
        else
          if x.val < 1550 then
            if x.val < 1525 then
              if x.val < 1512 then
                if x.val < 1506 then
                  if x.val < 1503 then
                    if x.val < 1501 then
                      1423
                    else
                      if x.val < 1502 then
                        1491
                      else
                        1424
                  else
                    if x.val < 1504 then
                      1550
                    else
                      if x.val < 1505 then
                        1551
                      else
                        1492
                else
                  if x.val < 1509 then
                    if x.val < 1507 then
                      1511
                    else
                      if x.val < 1508 then
                        1552
                      else
                        1435
                  else
                    if x.val < 1510 then
                      1554
                    else
                      if x.val < 1511 then
                        1436
                      else
                        1506
              else
                if x.val < 1518 then
                  if x.val < 1515 then
                    if x.val < 1513 then
                      1456
                    else
                      if x.val < 1514 then
                        1438
                      else
                        1463
                  else
                    if x.val < 1516 then
                      1555
                    else
                      if x.val < 1517 then
                        1556
                      else
                        1459
                else
                  if x.val < 1521 then
                    if x.val < 1519 then
                      1446
                    else
                      if x.val < 1520 then
                        1447
                      else
                        1557
                  else
                    if x.val < 1523 then
                      if x.val < 1522 then
                        1450
                      else
                        1453
                    else
                      if x.val < 1524 then
                        1457
                      else
                        1494
            else
              if x.val < 1537 then
                if x.val < 1531 then
                  if x.val < 1528 then
                    if x.val < 1526 then
                      1460
                    else
                      if x.val < 1527 then
                        1461
                      else
                        1466
                  else
                    if x.val < 1529 then
                      1467
                    else
                      if x.val < 1530 then
                        1545
                      else
                        1539
                else
                  if x.val < 1534 then
                    if x.val < 1532 then
                      1562
                    else
                      if x.val < 1533 then
                        1471
                      else
                        1564
                  else
                    if x.val < 1535 then
                      1565
                    else
                      if x.val < 1536 then
                        1566
                      else
                        1483
              else
                if x.val < 1543 then
                  if x.val < 1540 then
                    if x.val < 1538 then
                      1484
                    else
                      if x.val < 1539 then
                        1486
                      else
                        1530
                  else
                    if x.val < 1541 then
                      1488
                    else
                      if x.val < 1542 then
                        1559
                      else
                        1567
                else
                  if x.val < 1546 then
                    if x.val < 1544 then
                      1568
                    else
                      if x.val < 1545 then
                        1495
                      else
                        1529
                  else
                    if x.val < 1548 then
                      if x.val < 1547 then
                        1497
                      else
                        1572
                    else
                      if x.val < 1549 then
                        1499
                      else
                        1574
          else
            if x.val < 1575 then
              if x.val < 1562 then
                if x.val < 1556 then
                  if x.val < 1553 then
                    if x.val < 1551 then
                      1503
                    else
                      if x.val < 1552 then
                        1504
                      else
                        1507
                  else
                    if x.val < 1554 then
                      1578
                    else
                      if x.val < 1555 then
                        1509
                      else
                        1515
                else
                  if x.val < 1559 then
                    if x.val < 1557 then
                      1516
                    else
                      if x.val < 1558 then
                        1520
                      else
                        1561
                  else
                    if x.val < 1560 then
                      1541
                    else
                      if x.val < 1561 then
                        1563
                      else
                        1558
              else
                if x.val < 1568 then
                  if x.val < 1565 then
                    if x.val < 1563 then
                      1531
                    else
                      if x.val < 1564 then
                        1560
                      else
                        1533
                  else
                    if x.val < 1566 then
                      1534
                    else
                      if x.val < 1567 then
                        1535
                      else
                        1542
                else
                  if x.val < 1571 then
                    if x.val < 1569 then
                      1543
                    else
                      if x.val < 1570 then
                        1586
                      else
                        1587
                  else
                    if x.val < 1573 then
                      if x.val < 1572 then
                        1588
                      else
                        1547
                    else
                      if x.val < 1574 then
                        1589
                      else
                        1549
            else
              if x.val < 1587 then
                if x.val < 1581 then
                  if x.val < 1578 then
                    if x.val < 1576 then
                      1591
                    else
                      if x.val < 1577 then
                        1592
                      else
                        1590
                  else
                    if x.val < 1579 then
                      1553
                    else
                      if x.val < 1580 then
                        1580
                      else
                        1579
                else
                  if x.val < 1584 then
                    if x.val < 1582 then
                      1595
                    else
                      if x.val < 1583 then
                        1593
                      else
                        1585
                  else
                    if x.val < 1585 then
                      1596
                    else
                      if x.val < 1586 then
                        1583
                      else
                        1569
              else
                if x.val < 1593 then
                  if x.val < 1590 then
                    if x.val < 1588 then
                      1570
                    else
                      if x.val < 1589 then
                        1571
                      else
                        1573
                  else
                    if x.val < 1591 then
                      1577
                    else
                      if x.val < 1592 then
                        1575
                      else
                        1576
                else
                  if x.val < 1596 then
                    if x.val < 1594 then
                      1582
                    else
                      if x.val < 1595 then
                        1598
                      else
                        1581
                  else
                    if x.val < 1598 then
                      if x.val < 1597 then
                        1584
                      else
                        1599
                    else
                      if x.val < 1599 then
                        1594
                      else
                        1597

@[expose] public def atlas1600BMap (x : Fin 1600) : Fin 1600 :=
  if x.val < 800 then
    if x.val < 400 then
      if x.val < 200 then
        if x.val < 100 then
          if x.val < 50 then
            if x.val < 25 then
              if x.val < 12 then
                if x.val < 6 then
                  if x.val < 3 then
                    if x.val < 1 then
                      1
                    else
                      if x.val < 2 then
                        2
                      else
                        0
                  else
                    if x.val < 4 then
                      6
                    else
                      if x.val < 5 then
                        3
                      else
                        10
                else
                  if x.val < 9 then
                    if x.val < 7 then
                      4
                    else
                      if x.val < 8 then
                        5
                      else
                        15
                  else
                    if x.val < 10 then
                      17
                    else
                      if x.val < 11 then
                        7
                      else
                        8
              else
                if x.val < 18 then
                  if x.val < 15 then
                    if x.val < 13 then
                      9
                    else
                      if x.val < 14 then
                        24
                      else
                        26
                  else
                    if x.val < 16 then
                      11
                    else
                      if x.val < 17 then
                        29
                      else
                        12
                else
                  if x.val < 21 then
                    if x.val < 19 then
                      13
                    else
                      if x.val < 20 then
                        14
                      else
                        36
                  else
                    if x.val < 23 then
                      if x.val < 22 then
                        16
                      else
                        40
                    else
                      if x.val < 24 then
                        34
                      else
                        18
            else
              if x.val < 37 then
                if x.val < 31 then
                  if x.val < 28 then
                    if x.val < 26 then
                      44
                    else
                      if x.val < 27 then
                        19
                      else
                        20
                  else
                    if x.val < 29 then
                      48
                    else
                      if x.val < 30 then
                        21
                      else
                        22
                else
                  if x.val < 34 then
                    if x.val < 32 then
                      23
                    else
                      if x.val < 33 then
                        54
                      else
                        25
                  else
                    if x.val < 35 then
                      31
                    else
                      if x.val < 36 then
                        58
                      else
                        27
              else
                if x.val < 43 then
                  if x.val < 40 then
                    if x.val < 38 then
                      28
                    else
                      if x.val < 39 then
                        63
                      else
                        65
                  else
                    if x.val < 41 then
                      30
                    else
                      if x.val < 42 then
                        68
                      else
                        32
                else
                  if x.val < 46 then
                    if x.val < 44 then
                      72
                    else
                      if x.val < 45 then
                        33
                      else
                        35
                  else
                    if x.val < 48 then
                      if x.val < 47 then
                        77
                      else
                        79
                    else
                      if x.val < 49 then
                        37
                      else
                        38
          else
            if x.val < 75 then
              if x.val < 62 then
                if x.val < 56 then
                  if x.val < 53 then
                    if x.val < 51 then
                      39
                    else
                      if x.val < 52 then
                        86
                      else
                        41
                  else
                    if x.val < 54 then
                      90
                    else
                      if x.val < 55 then
                        42
                      else
                        43
                else
                  if x.val < 59 then
                    if x.val < 57 then
                      95
                    else
                      if x.val < 58 then
                        97
                      else
                        45
                  else
                    if x.val < 60 then
                      46
                    else
                      if x.val < 61 then
                        47
                      else
                        103
              else
                if x.val < 68 then
                  if x.val < 65 then
                    if x.val < 63 then
                      105
                    else
                      if x.val < 64 then
                        49
                      else
                        108
                  else
                    if x.val < 66 then
                      50
                    else
                      if x.val < 67 then
                        51
                      else
                        113
                else
                  if x.val < 71 then
                    if x.val < 69 then
                      52
                    else
                      if x.val < 70 then
                        53
                      else
                        118
                  else
                    if x.val < 73 then
                      if x.val < 72 then
                        120
                      else
                        55
                    else
                      if x.val < 74 then
                        56
                      else
                        57
            else
              if x.val < 87 then
                if x.val < 81 then
                  if x.val < 78 then
                    if x.val < 76 then
                      126
                    else
                      if x.val < 77 then
                        128
                      else
                        59
                  else
                    if x.val < 79 then
                      129
                    else
                      if x.val < 80 then
                        60
                      else
                        61
                else
                  if x.val < 84 then
                    if x.val < 82 then
                      62
                    else
                      if x.val < 83 then
                        136
                      else
                        64
                  else
                    if x.val < 85 then
                      139
                    else
                      if x.val < 86 then
                        141
                      else
                        66
              else
                if x.val < 93 then
                  if x.val < 90 then
                    if x.val < 88 then
                      67
                    else
                      if x.val < 89 then
                        146
                      else
                        148
                  else
                    if x.val < 91 then
                      69
                    else
                      if x.val < 92 then
                        70
                      else
                        71
                else
                  if x.val < 96 then
                    if x.val < 94 then
                      155
                    else
                      if x.val < 95 then
                        157
                      else
                        73
                  else
                    if x.val < 98 then
                      if x.val < 97 then
                        160
                      else
                        74
                    else
                      if x.val < 99 then
                        75
                      else
                        76
        else
          if x.val < 150 then
            if x.val < 125 then
              if x.val < 112 then
                if x.val < 106 then
                  if x.val < 103 then
                    if x.val < 101 then
                      78
                    else
                      if x.val < 102 then
                        167
                      else
                        169
                  else
                    if x.val < 104 then
                      80
                    else
                      if x.val < 105 then
                        172
                      else
                        81
                else
                  if x.val < 109 then
                    if x.val < 107 then
                      82
                    else
                      if x.val < 108 then
                        177
                      else
                        83
                  else
                    if x.val < 110 then
                      84
                    else
                      if x.val < 111 then
                        85
                      else
                        183
              else
                if x.val < 118 then
                  if x.val < 115 then
                    if x.val < 113 then
                      185
                    else
                      if x.val < 114 then
                        87
                      else
                        88
                  else
                    if x.val < 116 then
                      89
                    else
                      if x.val < 117 then
                        190
                      else
                        192
                else
                  if x.val < 121 then
                    if x.val < 119 then
                      91
                    else
                      if x.val < 120 then
                        195
                      else
                        92
                  else
                    if x.val < 123 then
                      if x.val < 122 then
                        93
                      else
                        94
                    else
                      if x.val < 124 then
                        201
                      else
                        96
            else
              if x.val < 137 then
                if x.val < 131 then
                  if x.val < 128 then
                    if x.val < 126 then
                      205
                    else
                      if x.val < 127 then
                        98
                      else
                        208
                  else
                    if x.val < 129 then
                      99
                    else
                      if x.val < 130 then
                        100
                      else
                        101
                else
                  if x.val < 134 then
                    if x.val < 132 then
                      102
                    else
                      if x.val < 133 then
                        216
                      else
                        104
                  else
                    if x.val < 135 then
                      219
                    else
                      if x.val < 136 then
                        221
                      else
                        106
              else
                if x.val < 143 then
                  if x.val < 140 then
                    if x.val < 138 then
                      107
                    else
                      if x.val < 139 then
                        226
                      else
                        109
                  else
                    if x.val < 141 then
                      229
                    else
                      if x.val < 142 then
                        110
                      else
                        111
                else
                  if x.val < 146 then
                    if x.val < 144 then
                      112
                    else
                      if x.val < 145 then
                        236
                      else
                        235
                  else
                    if x.val < 148 then
                      if x.val < 147 then
                        114
                      else
                        240
                    else
                      if x.val < 149 then
                        115
                      else
                        116
          else
            if x.val < 175 then
              if x.val < 162 then
                if x.val < 156 then
                  if x.val < 153 then
                    if x.val < 151 then
                      117
                    else
                      if x.val < 152 then
                        245
                      else
                        119
                  else
                    if x.val < 154 then
                      249
                    else
                      if x.val < 155 then
                        237
                      else
                        121
                else
                  if x.val < 159 then
                    if x.val < 157 then
                      253
                    else
                      if x.val < 158 then
                        122
                      else
                        123
                  else
                    if x.val < 160 then
                      257
                    else
                      if x.val < 161 then
                        124
                      else
                        125
              else
                if x.val < 168 then
                  if x.val < 165 then
                    if x.val < 163 then
                      262
                    else
                      if x.val < 164 then
                        127
                      else
                        265
                  else
                    if x.val < 166 then
                      267
                    else
                      if x.val < 167 then
                        269
                      else
                        130
                else
                  if x.val < 171 then
                    if x.val < 169 then
                      272
                    else
                      if x.val < 170 then
                        131
                      else
                        132
                  else
                    if x.val < 173 then
                      if x.val < 172 then
                        277
                      else
                        133
                    else
                      if x.val < 174 then
                        134
                      else
                        135
            else
              if x.val < 187 then
                if x.val < 181 then
                  if x.val < 178 then
                    if x.val < 176 then
                      283
                    else
                      if x.val < 177 then
                        285
                      else
                        137
                  else
                    if x.val < 179 then
                      138
                    else
                      if x.val < 180 then
                        290
                      else
                        140
                else
                  if x.val < 184 then
                    if x.val < 182 then
                      293
                    else
                      if x.val < 183 then
                        295
                      else
                        142
                  else
                    if x.val < 185 then
                      298
                    else
                      if x.val < 186 then
                        143
                      else
                        144
              else
                if x.val < 193 then
                  if x.val < 190 then
                    if x.val < 188 then
                      145
                    else
                      if x.val < 189 then
                        302
                      else
                        147
                  else
                    if x.val < 191 then
                      149
                    else
                      if x.val < 192 then
                        307
                      else
                        150
                else
                  if x.val < 196 then
                    if x.val < 194 then
                      151
                    else
                      if x.val < 195 then
                        309
                      else
                        152
                  else
                    if x.val < 198 then
                      if x.val < 197 then
                        153
                      else
                        154
                    else
                      if x.val < 199 then
                        315
                      else
                        156
      else
        if x.val < 300 then
          if x.val < 250 then
            if x.val < 225 then
              if x.val < 212 then
                if x.val < 206 then
                  if x.val < 203 then
                    if x.val < 201 then
                      318
                    else
                      if x.val < 202 then
                        158
                      else
                        159
                  else
                    if x.val < 204 then
                      323
                    else
                      if x.val < 205 then
                        325
                      else
                        161
                else
                  if x.val < 209 then
                    if x.val < 207 then
                      162
                    else
                      if x.val < 208 then
                        329
                      else
                        163
                  else
                    if x.val < 210 then
                      164
                    else
                      if x.val < 211 then
                        165
                      else
                        166
              else
                if x.val < 218 then
                  if x.val < 215 then
                    if x.val < 213 then
                      337
                    else
                      if x.val < 214 then
                        168
                      else
                        340
                  else
                    if x.val < 216 then
                      342
                    else
                      if x.val < 217 then
                        170
                      else
                        171
                else
                  if x.val < 221 then
                    if x.val < 219 then
                      347
                    else
                      if x.val < 220 then
                        173
                      else
                        350
                  else
                    if x.val < 223 then
                      if x.val < 222 then
                        174
                      else
                        175
                    else
                      if x.val < 224 then
                        176
                      else
                        327
            else
              if x.val < 237 then
                if x.val < 231 then
                  if x.val < 228 then
                    if x.val < 226 then
                      358
                    else
                      if x.val < 227 then
                        178
                      else
                        179
                  else
                    if x.val < 229 then
                      363
                    else
                      if x.val < 230 then
                        180
                      else
                        181
                else
                  if x.val < 234 then
                    if x.val < 232 then
                      182
                    else
                      if x.val < 233 then
                        369
                      else
                        184
                  else
                    if x.val < 235 then
                      373
                    else
                      if x.val < 236 then
                        187
                      else
                        186
              else
                if x.val < 243 then
                  if x.val < 240 then
                    if x.val < 238 then
                      197
                    else
                      if x.val < 239 then
                        188
                      else
                        378
                  else
                    if x.val < 241 then
                      189
                    else
                      if x.val < 242 then
                        381
                      else
                        191
                else
                  if x.val < 246 then
                    if x.val < 244 then
                      374
                    else
                      if x.val < 245 then
                        385
                      else
                        193
                  else
                    if x.val < 248 then
                      if x.val < 247 then
                        194
                      else
                        388
                    else
                      if x.val < 249 then
                        390
                      else
                        196
          else
            if x.val < 275 then
              if x.val < 262 then
                if x.val < 256 then
                  if x.val < 253 then
                    if x.val < 251 then
                      393
                    else
                      if x.val < 252 then
                        198
                      else
                        397
                  else
                    if x.val < 254 then
                      199
                    else
                      if x.val < 255 then
                        200
                      else
                        401
                else
                  if x.val < 259 then
                    if x.val < 257 then
                      403
                    else
                      if x.val < 258 then
                        202
                      else
                        203
                  else
                    if x.val < 260 then
                      204
                    else
                      if x.val < 261 then
                        364
                      else
                        410
              else
                if x.val < 268 then
                  if x.val < 265 then
                    if x.val < 263 then
                      206
                    else
                      if x.val < 264 then
                        207
                      else
                        414
                  else
                    if x.val < 266 then
                      209
                    else
                      if x.val < 267 then
                        417
                      else
                        210
                else
                  if x.val < 271 then
                    if x.val < 269 then
                      420
                    else
                      if x.val < 270 then
                        211
                      else
                        212
                  else
                    if x.val < 273 then
                      if x.val < 272 then
                        425
                      else
                        213
                    else
                      if x.val < 274 then
                        214
                      else
                        215
            else
              if x.val < 287 then
                if x.val < 281 then
                  if x.val < 278 then
                    if x.val < 276 then
                      429
                    else
                      if x.val < 277 then
                        431
                      else
                        217
                  else
                    if x.val < 279 then
                      218
                    else
                      if x.val < 280 then
                        436
                      else
                        220
                else
                  if x.val < 284 then
                    if x.val < 282 then
                      439
                    else
                      if x.val < 283 then
                        441
                      else
                        222
                  else
                    if x.val < 285 then
                      444
                    else
                      if x.val < 286 then
                        223
                      else
                        224
              else
                if x.val < 293 then
                  if x.val < 290 then
                    if x.val < 288 then
                      225
                    else
                      if x.val < 289 then
                        387
                      else
                        451
                  else
                    if x.val < 291 then
                      227
                    else
                      if x.val < 292 then
                        228
                      else
                        260
                else
                  if x.val < 296 then
                    if x.val < 294 then
                      230
                    else
                      if x.val < 295 then
                        406
                      else
                        231
                  else
                    if x.val < 298 then
                      if x.val < 297 then
                        232
                      else
                        460
                    else
                      if x.val < 299 then
                        233
                      else
                        234
        else
          if x.val < 350 then
            if x.val < 325 then
              if x.val < 312 then
                if x.val < 306 then
                  if x.val < 303 then
                    if x.val < 301 then
                      243
                    else
                      if x.val < 302 then
                        466
                      else
                        238
                  else
                    if x.val < 304 then
                      239
                    else
                      if x.val < 305 then
                        470
                      else
                        241
                else
                  if x.val < 309 then
                    if x.val < 307 then
                      474
                    else
                      if x.val < 308 then
                        242
                      else
                        244
                  else
                    if x.val < 310 then
                      246
                    else
                      if x.val < 311 then
                        247
                      else
                        248
              else
                if x.val < 318 then
                  if x.val < 315 then
                    if x.val < 313 then
                      482
                    else
                      if x.val < 314 then
                        250
                      else
                        486
                  else
                    if x.val < 316 then
                      251
                    else
                      if x.val < 317 then
                        252
                      else
                        491
                else
                  if x.val < 321 then
                    if x.val < 319 then
                      254
                    else
                      if x.val < 320 then
                        255
                      else
                        256
                  else
                    if x.val < 323 then
                      if x.val < 322 then
                        496
                      else
                        498
                    else
                      if x.val < 324 then
                        258
                      else
                        500
            else
              if x.val < 337 then
                if x.val < 331 then
                  if x.val < 328 then
                    if x.val < 326 then
                      259
                    else
                      if x.val < 327 then
                        261
                      else
                        286
                  else
                    if x.val < 329 then
                      505
                    else
                      if x.val < 330 then
                        263
                      else
                        264
                else
                  if x.val < 334 then
                    if x.val < 332 then
                      510
                    else
                      if x.val < 333 then
                        266
                      else
                        513
                  else
                    if x.val < 335 then
                      268
                    else
                      if x.val < 336 then
                        516
                      else
                        518
              else
                if x.val < 343 then
                  if x.val < 340 then
                    if x.val < 338 then
                      270
                    else
                      if x.val < 339 then
                        271
                      else
                        523
                  else
                    if x.val < 341 then
                      273
                    else
                      if x.val < 342 then
                        481
                      else
                        274
                else
                  if x.val < 346 then
                    if x.val < 344 then
                      275
                    else
                      if x.val < 345 then
                        276
                      else
                        530
                  else
                    if x.val < 348 then
                      if x.val < 347 then
                        532
                      else
                        278
                    else
                      if x.val < 349 then
                        279
                      else
                        536
          else
            if x.val < 375 then
              if x.val < 362 then
                if x.val < 356 then
                  if x.val < 353 then
                    if x.val < 351 then
                      280
                    else
                      if x.val < 352 then
                        281
                      else
                        282
                  else
                    if x.val < 354 then
                      541
                    else
                      if x.val < 355 then
                        284
                      else
                        545
                else
                  if x.val < 359 then
                    if x.val < 357 then
                      547
                    else
                      if x.val < 358 then
                        549
                      else
                        287
                  else
                    if x.val < 360 then
                      288
                    else
                      if x.val < 361 then
                        289
                      else
                        555
              else
                if x.val < 368 then
                  if x.val < 365 then
                    if x.val < 363 then
                      557
                    else
                      if x.val < 364 then
                        291
                      else
                        292
                  else
                    if x.val < 366 then
                      560
                    else
                      if x.val < 367 then
                        294
                      else
                        531
                else
                  if x.val < 371 then
                    if x.val < 369 then
                      563
                    else
                      if x.val < 370 then
                        296
                      else
                        297
                  else
                    if x.val < 373 then
                      if x.val < 372 then
                        566
                      else
                        568
                    else
                      if x.val < 374 then
                        299
                      else
                        300
            else
              if x.val < 387 then
                if x.val < 381 then
                  if x.val < 378 then
                    if x.val < 376 then
                      301
                    else
                      if x.val < 377 then
                        402
                      else
                        573
                  else
                    if x.val < 379 then
                      303
                    else
                      if x.val < 380 then
                        304
                      else
                        577
                else
                  if x.val < 384 then
                    if x.val < 382 then
                      305
                    else
                      if x.val < 383 then
                        306
                      else
                        485
                  else
                    if x.val < 385 then
                      582
                    else
                      if x.val < 386 then
                        308
                      else
                        585
              else
                if x.val < 393 then
                  if x.val < 390 then
                    if x.val < 388 then
                      359
                    else
                      if x.val < 389 then
                        310
                      else
                        588
                  else
                    if x.val < 391 then
                      311
                    else
                      if x.val < 392 then
                        312
                      else
                        590
                else
                  if x.val < 396 then
                    if x.val < 394 then
                      313
                    else
                      if x.val < 395 then
                        314
                      else
                        594
                  else
                    if x.val < 398 then
                      if x.val < 397 then
                        596
                      else
                        316
                    else
                      if x.val < 399 then
                        317
                      else
                        600
    else
      if x.val < 600 then
        if x.val < 500 then
          if x.val < 450 then
            if x.val < 425 then
              if x.val < 412 then
                if x.val < 406 then
                  if x.val < 403 then
                    if x.val < 401 then
                      602
                    else
                      if x.val < 402 then
                        319
                      else
                        467
                  else
                    if x.val < 404 then
                      320
                    else
                      if x.val < 405 then
                        321
                      else
                        322
                else
                  if x.val < 409 then
                    if x.val < 407 then
                      366
                    else
                      if x.val < 408 then
                        324
                      else
                        608
                  else
                    if x.val < 410 then
                      609
                    else
                      if x.val < 411 then
                        326
                      else
                        328
              else
                if x.val < 418 then
                  if x.val < 415 then
                    if x.val < 413 then
                      614
                    else
                      if x.val < 414 then
                        615
                      else
                        330
                  else
                    if x.val < 416 then
                      331
                    else
                      if x.val < 417 then
                        620
                      else
                        332
                else
                  if x.val < 421 then
                    if x.val < 419 then
                      333
                    else
                      if x.val < 420 then
                        624
                      else
                        334
                  else
                    if x.val < 423 then
                      if x.val < 422 then
                        335
                      else
                        336
                    else
                      if x.val < 424 then
                        629
                      else
                        631
            else
              if x.val < 437 then
                if x.val < 431 then
                  if x.val < 428 then
                    if x.val < 426 then
                      338
                    else
                      if x.val < 427 then
                        339
                      else
                        341
                  else
                    if x.val < 429 then
                      636
                    else
                      if x.val < 430 then
                        343
                      else
                        639
                else
                  if x.val < 434 then
                    if x.val < 432 then
                      344
                    else
                      if x.val < 433 then
                        345
                      else
                        346
                  else
                    if x.val < 435 then
                      644
                    else
                      if x.val < 436 then
                        646
                      else
                        348
              else
                if x.val < 443 then
                  if x.val < 440 then
                    if x.val < 438 then
                      349
                    else
                      if x.val < 439 then
                        463
                      else
                        351
                  else
                    if x.val < 441 then
                      651
                    else
                      if x.val < 442 then
                        352
                      else
                        353
                else
                  if x.val < 446 then
                    if x.val < 444 then
                      654
                    else
                      if x.val < 445 then
                        354
                      else
                        355
                  else
                    if x.val < 448 then
                      if x.val < 447 then
                        356
                      else
                        357
                    else
                      if x.val < 449 then
                        660
                      else
                        662
          else
            if x.val < 475 then
              if x.val < 462 then
                if x.val < 456 then
                  if x.val < 453 then
                    if x.val < 451 then
                      664
                    else
                      if x.val < 452 then
                        360
                      else
                        361
                  else
                    if x.val < 454 then
                      362
                    else
                      if x.val < 455 then
                        671
                      else
                        673
                else
                  if x.val < 459 then
                    if x.val < 457 then
                      365
                    else
                      if x.val < 458 then
                        675
                      else
                        367
                  else
                    if x.val < 460 then
                      368
                    else
                      if x.val < 461 then
                        370
                      else
                        371
              else
                if x.val < 468 then
                  if x.val < 465 then
                    if x.val < 463 then
                      372
                    else
                      if x.val < 464 then
                        537
                      else
                        684
                  else
                    if x.val < 466 then
                      686
                    else
                      if x.val < 467 then
                        375
                      else
                        376
                else
                  if x.val < 471 then
                    if x.val < 469 then
                      377
                    else
                      if x.val < 470 then
                        690
                      else
                        379
                  else
                    if x.val < 473 then
                      if x.val < 472 then
                        380
                      else
                        695
                    else
                      if x.val < 474 then
                        697
                      else
                        382
            else
              if x.val < 487 then
                if x.val < 481 then
                  if x.val < 478 then
                    if x.val < 476 then
                      383
                    else
                      if x.val < 477 then
                        384
                      else
                        701
                  else
                    if x.val < 479 then
                      386
                    else
                      if x.val < 480 then
                        704
                      else
                        389
                else
                  if x.val < 484 then
                    if x.val < 482 then
                      427
                    else
                      if x.val < 483 then
                        391
                      else
                        392
                  else
                    if x.val < 485 then
                      710
                    else
                      if x.val < 486 then
                        475
                      else
                        394
              else
                if x.val < 493 then
                  if x.val < 490 then
                    if x.val < 488 then
                      395
                    else
                      if x.val < 489 then
                        396
                      else
                        716
                  else
                    if x.val < 491 then
                      718
                    else
                      if x.val < 492 then
                        398
                      else
                        399
                else
                  if x.val < 496 then
                    if x.val < 494 then
                      400
                    else
                      if x.val < 495 then
                        678
                      else
                        669
                  else
                    if x.val < 498 then
                      if x.val < 497 then
                        404
                      else
                        726
                    else
                      if x.val < 499 then
                        405
                      else
                        729
        else
          if x.val < 550 then
            if x.val < 525 then
              if x.val < 512 then
                if x.val < 506 then
                  if x.val < 503 then
                    if x.val < 501 then
                      407
                    else
                      if x.val < 502 then
                        408
                      else
                        409
                  else
                    if x.val < 504 then
                      731
                    else
                      if x.val < 505 then
                        733
                      else
                        411
                else
                  if x.val < 509 then
                    if x.val < 507 then
                      412
                    else
                      if x.val < 508 then
                        413
                      else
                        737
                  else
                    if x.val < 510 then
                      725
                    else
                      if x.val < 511 then
                        415
                      else
                        416
              else
                if x.val < 518 then
                  if x.val < 515 then
                    if x.val < 513 then
                      740
                    else
                      if x.val < 514 then
                        418
                      else
                        419
                  else
                    if x.val < 516 then
                      745
                    else
                      if x.val < 517 then
                        421
                      else
                        747
                else
                  if x.val < 521 then
                    if x.val < 519 then
                      422
                    else
                      if x.val < 520 then
                        423
                      else
                        424
                  else
                    if x.val < 523 then
                      if x.val < 522 then
                        753
                      else
                        674
                    else
                      if x.val < 524 then
                        426
                      else
                        757
            else
              if x.val < 537 then
                if x.val < 531 then
                  if x.val < 528 then
                    if x.val < 526 then
                      428
                    else
                      if x.val < 527 then
                        760
                      else
                        430
                  else
                    if x.val < 529 then
                      764
                    else
                      if x.val < 530 then
                        766
                      else
                        432
                else
                  if x.val < 534 then
                    if x.val < 532 then
                      458
                    else
                      if x.val < 533 then
                        433
                      else
                        434
                  else
                    if x.val < 535 then
                      435
                    else
                      if x.val < 536 then
                        772
                      else
                        437
              else
                if x.val < 543 then
                  if x.val < 540 then
                    if x.val < 538 then
                      438
                    else
                      if x.val < 539 then
                        440
                      else
                        777
                  else
                    if x.val < 541 then
                      779
                    else
                      if x.val < 542 then
                        442
                      else
                        443
                else
                  if x.val < 546 then
                    if x.val < 544 then
                      666
                    else
                      if x.val < 545 then
                        781
                      else
                        445
                  else
                    if x.val < 548 then
                      if x.val < 547 then
                        783
                      else
                        446
                    else
                      if x.val < 549 then
                        744
                      else
                        447
          else
            if x.val < 575 then
              if x.val < 562 then
                if x.val < 556 then
                  if x.val < 553 then
                    if x.val < 551 then
                      448
                    else
                      if x.val < 552 then
                        449
                      else
                        450
                  else
                    if x.val < 554 then
                      791
                    else
                      if x.val < 555 then
                        543
                      else
                        452
                else
                  if x.val < 559 then
                    if x.val < 557 then
                      795
                    else
                      if x.val < 558 then
                        453
                      else
                        454
                  else
                    if x.val < 560 then
                      455
                    else
                      if x.val < 561 then
                        456
                      else
                        457
              else
                if x.val < 568 then
                  if x.val < 565 then
                    if x.val < 563 then
                      802
                    else
                      if x.val < 564 then
                        459
                      else
                        494
                  else
                    if x.val < 566 then
                      806
                    else
                      if x.val < 567 then
                        461
                      else
                        808
                else
                  if x.val < 571 then
                    if x.val < 569 then
                      462
                    else
                      if x.val < 570 then
                        464
                      else
                        465
                  else
                    if x.val < 573 then
                      if x.val < 572 then
                        813
                      else
                        815
                    else
                      if x.val < 574 then
                        468
                      else
                        469
            else
              if x.val < 587 then
                if x.val < 581 then
                  if x.val < 578 then
                    if x.val < 576 then
                      819
                    else
                      if x.val < 577 then
                        821
                      else
                        471
                  else
                    if x.val < 579 then
                      472
                    else
                      if x.val < 580 then
                        473
                      else
                        828
                else
                  if x.val < 584 then
                    if x.val < 582 then
                      830
                    else
                      if x.val < 583 then
                        476
                      else
                        477
                  else
                    if x.val < 585 then
                      834
                    else
                      if x.val < 586 then
                        478
                      else
                        479
              else
                if x.val < 593 then
                  if x.val < 590 then
                    if x.val < 588 then
                      838
                    else
                      if x.val < 589 then
                        480
                      else
                        840
                  else
                    if x.val < 591 then
                      483
                    else
                      if x.val < 592 then
                        484
                      else
                        787
                else
                  if x.val < 596 then
                    if x.val < 594 then
                      845
                    else
                      if x.val < 595 then
                        487
                      else
                        848
                  else
                    if x.val < 598 then
                      if x.val < 597 then
                        488
                      else
                        489
                    else
                      if x.val < 599 then
                        490
                      else
                        855
      else
        if x.val < 700 then
          if x.val < 650 then
            if x.val < 625 then
              if x.val < 612 then
                if x.val < 606 then
                  if x.val < 603 then
                    if x.val < 601 then
                      492
                    else
                      if x.val < 602 then
                        858
                      else
                        493
                  else
                    if x.val < 604 then
                      495
                    else
                      if x.val < 605 then
                        862
                      else
                        497
                else
                  if x.val < 609 then
                    if x.val < 607 then
                      864
                    else
                      if x.val < 608 then
                        499
                      else
                        501
                  else
                    if x.val < 610 then
                      502
                    else
                      if x.val < 611 then
                        503
                      else
                        504
              else
                if x.val < 618 then
                  if x.val < 615 then
                    if x.val < 613 then
                      870
                    else
                      if x.val < 614 then
                        872
                      else
                        506
                  else
                    if x.val < 616 then
                      507
                    else
                      if x.val < 617 then
                        508
                      else
                        509
                else
                  if x.val < 621 then
                    if x.val < 619 then
                      876
                    else
                      if x.val < 620 then
                        878
                      else
                        511
                  else
                    if x.val < 623 then
                      if x.val < 622 then
                        512
                      else
                        881
                    else
                      if x.val < 624 then
                        883
                      else
                        514
            else
              if x.val < 637 then
                if x.val < 631 then
                  if x.val < 628 then
                    if x.val < 626 then
                      515
                    else
                      if x.val < 627 then
                        782
                      else
                        517
                  else
                    if x.val < 629 then
                      889
                    else
                      if x.val < 630 then
                        519
                      else
                        892
                else
                  if x.val < 634 then
                    if x.val < 632 then
                      520
                    else
                      if x.val < 633 then
                        521
                      else
                        522
                  else
                    if x.val < 635 then
                      898
                    else
                      if x.val < 636 then
                        524
                      else
                        525
              else
                if x.val < 643 then
                  if x.val < 640 then
                    if x.val < 638 then
                      526
                    else
                      if x.val < 639 then
                        903
                      else
                        527
                  else
                    if x.val < 641 then
                      528
                    else
                      if x.val < 642 then
                        529
                      else
                        884
                else
                  if x.val < 646 then
                    if x.val < 644 then
                      909
                    else
                      if x.val < 645 then
                        533
                      else
                        912
                  else
                    if x.val < 648 then
                      if x.val < 647 then
                        534
                      else
                        535
                    else
                      if x.val < 649 then
                        915
                      else
                        917
          else
            if x.val < 675 then
              if x.val < 662 then
                if x.val < 656 then
                  if x.val < 653 then
                    if x.val < 651 then
                      919
                    else
                      if x.val < 652 then
                        538
                      else
                        539
                  else
                    if x.val < 654 then
                      540
                    else
                      if x.val < 655 then
                        542
                      else
                        544
                else
                  if x.val < 659 then
                    if x.val < 657 then
                      546
                    else
                      if x.val < 658 then
                        732
                      else
                        548
                  else
                    if x.val < 660 then
                      927
                    else
                      if x.val < 661 then
                        550
                      else
                        592
              else
                if x.val < 668 then
                  if x.val < 665 then
                    if x.val < 663 then
                      551
                    else
                      if x.val < 664 then
                        931
                      else
                        552
                  else
                    if x.val < 666 then
                      553
                    else
                      if x.val < 667 then
                        554
                      else
                        936
                else
                  if x.val < 671 then
                    if x.val < 669 then
                      556
                    else
                      if x.val < 670 then
                        603
                      else
                        938
                  else
                    if x.val < 673 then
                      if x.val < 672 then
                        558
                      else
                        940
                    else
                      if x.val < 674 then
                        559
                      else
                        633
            else
              if x.val < 687 then
                if x.val < 681 then
                  if x.val < 678 then
                    if x.val < 676 then
                      561
                    else
                      if x.val < 677 then
                        562
                      else
                        945
                  else
                    if x.val < 679 then
                      564
                    else
                      if x.val < 680 then
                        565
                      else
                        950
                else
                  if x.val < 684 then
                    if x.val < 682 then
                      567
                    else
                      if x.val < 683 then
                        951
                      else
                        953
                  else
                    if x.val < 685 then
                      569
                    else
                      if x.val < 686 then
                        956
                      else
                        570
              else
                if x.val < 693 then
                  if x.val < 690 then
                    if x.val < 688 then
                      571
                    else
                      if x.val < 689 then
                        572
                      else
                        961
                  else
                    if x.val < 691 then
                      574
                    else
                      if x.val < 692 then
                        575
                      else
                        576
                else
                  if x.val < 696 then
                    if x.val < 694 then
                      967
                    else
                      if x.val < 695 then
                        706
                      else
                        578
                  else
                    if x.val < 698 then
                      if x.val < 697 then
                        971
                      else
                        579
                    else
                      if x.val < 699 then
                        580
                      else
                        581
        else
          if x.val < 750 then
            if x.val < 725 then
              if x.val < 712 then
                if x.val < 706 then
                  if x.val < 703 then
                    if x.val < 701 then
                      879
                    else
                      if x.val < 702 then
                        583
                      else
                        584
                  else
                    if x.val < 704 then
                      979
                    else
                      if x.val < 705 then
                        586
                      else
                        587
                else
                  if x.val < 709 then
                    if x.val < 707 then
                      823
                    else
                      if x.val < 708 then
                        589
                      else
                        986
                  else
                    if x.val < 710 then
                      988
                    else
                      if x.val < 711 then
                        591
                      else
                        593
              else
                if x.val < 718 then
                  if x.val < 715 then
                    if x.val < 713 then
                      992
                    else
                      if x.val < 714 then
                        595
                      else
                        996
                  else
                    if x.val < 716 then
                      832
                    else
                      if x.val < 717 then
                        597
                      else
                        1000
                else
                  if x.val < 721 then
                    if x.val < 719 then
                      598
                    else
                      if x.val < 720 then
                        599
                      else
                        911
                  else
                    if x.val < 723 then
                      if x.val < 722 then
                        601
                      else
                        1005
                    else
                      if x.val < 724 then
                        1007
                      else
                        604
            else
              if x.val < 737 then
                if x.val < 731 then
                  if x.val < 728 then
                    if x.val < 726 then
                      617
                    else
                      if x.val < 727 then
                        605
                      else
                        606
                  else
                    if x.val < 729 then
                      1013
                    else
                      if x.val < 730 then
                        607
                      else
                        975
                else
                  if x.val < 734 then
                    if x.val < 732 then
                      610
                    else
                      if x.val < 733 then
                        784
                      else
                        611
                  else
                    if x.val < 735 then
                      612
                    else
                      if x.val < 736 then
                        613
                      else
                        918
              else
                if x.val < 743 then
                  if x.val < 740 then
                    if x.val < 738 then
                      616
                    else
                      if x.val < 739 then
                        618
                      else
                        619
                  else
                    if x.val < 741 then
                      621
                    else
                      if x.val < 742 then
                        622
                      else
                        623
                else
                  if x.val < 746 then
                    if x.val < 744 then
                      642
                    else
                      if x.val < 745 then
                        658
                      else
                        625
                  else
                    if x.val < 748 then
                      if x.val < 747 then
                        626
                      else
                        627
                    else
                      if x.val < 749 then
                        628
                      else
                        1033
          else
            if x.val < 775 then
              if x.val < 762 then
                if x.val < 756 then
                  if x.val < 753 then
                    if x.val < 751 then
                      630
                    else
                      if x.val < 752 then
                        1037
                      else
                        1038
                  else
                    if x.val < 754 then
                      632
                    else
                      if x.val < 755 then
                        1041
                      else
                        634
                else
                  if x.val < 759 then
                    if x.val < 757 then
                      978
                    else
                      if x.val < 758 then
                        635
                      else
                        1043
                  else
                    if x.val < 760 then
                      1045
                    else
                      if x.val < 761 then
                        637
                      else
                        638
              else
                if x.val < 768 then
                  if x.val < 765 then
                    if x.val < 763 then
                      1048
                    else
                      if x.val < 764 then
                        1021
                      else
                        640
                  else
                    if x.val < 766 then
                      1052
                    else
                      if x.val < 767 then
                        641
                      else
                        643
                else
                  if x.val < 771 then
                    if x.val < 769 then
                      1056
                    else
                      if x.val < 770 then
                        645
                      else
                        1057
                  else
                    if x.val < 773 then
                      if x.val < 772 then
                        1044
                      else
                        647
                    else
                      if x.val < 774 then
                        648
                      else
                        649
            else
              if x.val < 787 then
                if x.val < 781 then
                  if x.val < 778 then
                    if x.val < 776 then
                      650
                    else
                      if x.val < 777 then
                        1062
                      else
                        652
                  else
                    if x.val < 779 then
                      1065
                    else
                      if x.val < 780 then
                        653
                      else
                        1067
                else
                  if x.val < 784 then
                    if x.val < 782 then
                      655
                    else
                      if x.val < 783 then
                        746
                      else
                        656
                  else
                    if x.val < 785 then
                      657
                    else
                      if x.val < 786 then
                        659
                      else
                        1071
              else
                if x.val < 793 then
                  if x.val < 790 then
                    if x.val < 788 then
                      661
                    else
                      if x.val < 789 then
                        1073
                      else
                        663
                  else
                    if x.val < 791 then
                      1076
                    else
                      if x.val < 792 then
                        665
                      else
                        1079
                else
                  if x.val < 796 then
                    if x.val < 794 then
                      667
                    else
                      if x.val < 795 then
                        1081
                      else
                        668
                  else
                    if x.val < 798 then
                      if x.val < 797 then
                        670
                      else
                        1082
                    else
                      if x.val < 799 then
                        672
                      else
                        1084
  else
    if x.val < 1200 then
      if x.val < 1000 then
        if x.val < 900 then
          if x.val < 850 then
            if x.val < 825 then
              if x.val < 812 then
                if x.val < 806 then
                  if x.val < 803 then
                    if x.val < 801 then
                      1031
                    else
                      if x.val < 802 then
                        1086
                      else
                        676
                  else
                    if x.val < 804 then
                      677
                    else
                      if x.val < 805 then
                        914
                      else
                        1091
                else
                  if x.val < 809 then
                    if x.val < 807 then
                      679
                    else
                      if x.val < 808 then
                        680
                      else
                        681
                  else
                    if x.val < 810 then
                      682
                    else
                      if x.val < 811 then
                        683
                      else
                        1097
              else
                if x.val < 818 then
                  if x.val < 815 then
                    if x.val < 813 then
                      685
                    else
                      if x.val < 814 then
                        687
                      else
                        949
                  else
                    if x.val < 816 then
                      688
                    else
                      if x.val < 817 then
                        689
                      else
                        994
                else
                  if x.val < 821 then
                    if x.val < 819 then
                      1103
                    else
                      if x.val < 820 then
                        691
                      else
                        1106
                  else
                    if x.val < 823 then
                      if x.val < 822 then
                        692
                      else
                        693
                    else
                      if x.val < 824 then
                        694
                      else
                        1110
            else
              if x.val < 837 then
                if x.val < 831 then
                  if x.val < 828 then
                    if x.val < 826 then
                      696
                    else
                      if x.val < 827 then
                        1114
                      else
                        1115
                  else
                    if x.val < 829 then
                      698
                    else
                      if x.val < 830 then
                        1059
                      else
                        699
                else
                  if x.val < 834 then
                    if x.val < 832 then
                      700
                    else
                      if x.val < 833 then
                        850
                      else
                        1119
                  else
                    if x.val < 835 then
                      702
                    else
                      if x.val < 836 then
                        703
                      else
                        1122
              else
                if x.val < 843 then
                  if x.val < 840 then
                    if x.val < 838 then
                      1124
                    else
                      if x.val < 839 then
                        705
                      else
                        1126
                  else
                    if x.val < 841 then
                      707
                    else
                      if x.val < 842 then
                        708
                      else
                        709
                else
                  if x.val < 846 then
                    if x.val < 844 then
                      1132
                    else
                      if x.val < 845 then
                        995
                      else
                        711
                  else
                    if x.val < 848 then
                      if x.val < 847 then
                        712
                      else
                        1112
                    else
                      if x.val < 849 then
                        713
                      else
                        714
          else
            if x.val < 875 then
              if x.val < 862 then
                if x.val < 856 then
                  if x.val < 853 then
                    if x.val < 851 then
                      715
                    else
                      if x.val < 852 then
                        968
                      else
                        717
                  else
                    if x.val < 854 then
                      1139
                    else
                      if x.val < 855 then
                        1064
                      else
                        719
                else
                  if x.val < 859 then
                    if x.val < 857 then
                      720
                    else
                      if x.val < 858 then
                        1051
                      else
                        721
                  else
                    if x.val < 860 then
                      722
                    else
                      if x.val < 861 then
                        723
                      else
                        1146
              else
                if x.val < 868 then
                  if x.val < 865 then
                    if x.val < 863 then
                      724
                    else
                      if x.val < 864 then
                        1018
                      else
                        727
                  else
                    if x.val < 866 then
                      728
                    else
                      if x.val < 867 then
                        1023
                      else
                        730
                else
                  if x.val < 871 then
                    if x.val < 869 then
                      1085
                    else
                      if x.val < 870 then
                        1066
                      else
                        734
                  else
                    if x.val < 873 then
                      if x.val < 872 then
                        1153
                      else
                        735
                    else
                      if x.val < 874 then
                        736
                      else
                        1155
            else
              if x.val < 887 then
                if x.val < 881 then
                  if x.val < 878 then
                    if x.val < 876 then
                      1157
                    else
                      if x.val < 877 then
                        738
                      else
                        1159
                  else
                    if x.val < 879 then
                      739
                    else
                      if x.val < 880 then
                        831
                      else
                        866
                else
                  if x.val < 884 then
                    if x.val < 882 then
                      741
                    else
                      if x.val < 883 then
                        1162
                      else
                        742
                  else
                    if x.val < 885 then
                      743
                    else
                      if x.val < 886 then
                        1164
                      else
                        1165
              else
                if x.val < 893 then
                  if x.val < 890 then
                    if x.val < 888 then
                      1166
                    else
                      if x.val < 889 then
                        1012
                      else
                        748
                  else
                    if x.val < 891 then
                      749
                    else
                      if x.val < 892 then
                        1168
                      else
                        750
                else
                  if x.val < 896 then
                    if x.val < 894 then
                      751
                    else
                      if x.val < 895 then
                        752
                      else
                        1174
                  else
                    if x.val < 898 then
                      if x.val < 897 then
                        754
                      else
                        1177
                    else
                      if x.val < 899 then
                        755
                      else
                        756
        else
          if x.val < 950 then
            if x.val < 925 then
              if x.val < 912 then
                if x.val < 906 then
                  if x.val < 903 then
                    if x.val < 901 then
                      771
                    else
                      if x.val < 902 then
                        758
                      else
                        759
                  else
                    if x.val < 904 then
                      761
                    else
                      if x.val < 905 then
                        762
                      else
                        763
                else
                  if x.val < 909 then
                    if x.val < 907 then
                      1183
                    else
                      if x.val < 908 then
                        765
                      else
                        1185
                  else
                    if x.val < 910 then
                      767
                    else
                      if x.val < 911 then
                        768
                      else
                        856
              else
                if x.val < 918 then
                  if x.val < 915 then
                    if x.val < 913 then
                      769
                    else
                      if x.val < 914 then
                        770
                      else
                        946
                  else
                    if x.val < 916 then
                      773
                    else
                      if x.val < 917 then
                        829
                      else
                        774
                else
                  if x.val < 921 then
                    if x.val < 919 then
                      873
                    else
                      if x.val < 920 then
                        775
                      else
                        776
                  else
                    if x.val < 923 then
                      if x.val < 922 then
                        1195
                      else
                        778
                    else
                      if x.val < 924 then
                        869
                      else
                        780
            else
              if x.val < 937 then
                if x.val < 931 then
                  if x.val < 928 then
                    if x.val < 926 then
                      1198
                    else
                      if x.val < 927 then
                        1144
                      else
                        785
                  else
                    if x.val < 929 then
                      786
                    else
                      if x.val < 930 then
                        1098
                      else
                        788
                else
                  if x.val < 934 then
                    if x.val < 932 then
                      789
                    else
                      if x.val < 933 then
                        790
                      else
                        1205
                  else
                    if x.val < 935 then
                      792
                    else
                      if x.val < 936 then
                        1208
                      else
                        793
              else
                if x.val < 943 then
                  if x.val < 940 then
                    if x.val < 938 then
                      794
                    else
                      if x.val < 939 then
                        796
                      else
                        797
                  else
                    if x.val < 941 then
                      798
                    else
                      if x.val < 942 then
                        799
                      else
                        800
                else
                  if x.val < 946 then
                    if x.val < 944 then
                      801
                    else
                      if x.val < 945 then
                        1213
                      else
                        803
                  else
                    if x.val < 948 then
                      if x.val < 947 then
                        804
                      else
                        805
                    else
                      if x.val < 949 then
                        1218
                      else
                        958
          else
            if x.val < 975 then
              if x.val < 962 then
                if x.val < 956 then
                  if x.val < 953 then
                    if x.val < 951 then
                      807
                    else
                      if x.val < 952 then
                        809
                      else
                        1184
                  else
                    if x.val < 954 then
                      810
                    else
                      if x.val < 955 then
                        811
                      else
                        1191
                else
                  if x.val < 959 then
                    if x.val < 957 then
                      812
                    else
                      if x.val < 958 then
                        1197
                      else
                        814
                  else
                    if x.val < 960 then
                      1128
                    else
                      if x.val < 961 then
                        1226
                      else
                        816
              else
                if x.val < 968 then
                  if x.val < 965 then
                    if x.val < 963 then
                      817
                    else
                      if x.val < 964 then
                        818
                      else
                        1229
                  else
                    if x.val < 966 then
                      820
                    else
                      if x.val < 967 then
                        1233
                      else
                        822
                else
                  if x.val < 971 then
                    if x.val < 969 then
                      998
                    else
                      if x.val < 970 then
                        824
                      else
                        1235
                  else
                    if x.val < 973 then
                      if x.val < 972 then
                        825
                      else
                        826
                    else
                      if x.val < 974 then
                        827
                      else
                        1240
            else
              if x.val < 987 then
                if x.val < 981 then
                  if x.val < 978 then
                    if x.val < 976 then
                      867
                    else
                      if x.val < 977 then
                        1120
                      else
                        833
                  else
                    if x.val < 979 then
                      899
                    else
                      if x.val < 980 then
                        835
                      else
                        836
                else
                  if x.val < 984 then
                    if x.val < 982 then
                      837
                    else
                      if x.val < 983 then
                        1247
                      else
                        839
                  else
                    if x.val < 985 then
                      1009
                    else
                      if x.val < 986 then
                        959
                      else
                        841
              else
                if x.val < 993 then
                  if x.val < 990 then
                    if x.val < 988 then
                      854
                    else
                      if x.val < 989 then
                        842
                      else
                        843
                  else
                    if x.val < 991 then
                      844
                    else
                      if x.val < 992 then
                        1254
                      else
                        846
                else
                  if x.val < 996 then
                    if x.val < 994 then
                      847
                    else
                      if x.val < 995 then
                        962
                      else
                        990
                  else
                    if x.val < 998 then
                      if x.val < 997 then
                        849
                      else
                        1255
                    else
                      if x.val < 999 then
                        851
                      else
                        1234
      else
        if x.val < 1100 then
          if x.val < 1050 then
            if x.val < 1025 then
              if x.val < 1012 then
                if x.val < 1006 then
                  if x.val < 1003 then
                    if x.val < 1001 then
                      852
                    else
                      if x.val < 1002 then
                        853
                      else
                        1258
                  else
                    if x.val < 1004 then
                      1260
                    else
                      if x.val < 1005 then
                        857
                      else
                        859
                else
                  if x.val < 1009 then
                    if x.val < 1007 then
                      926
                    else
                      if x.val < 1008 then
                        860
                      else
                        861
                  else
                    if x.val < 1010 then
                      1127
                    else
                      if x.val < 1011 then
                        863
                      else
                        1268
              else
                if x.val < 1018 then
                  if x.val < 1015 then
                    if x.val < 1013 then
                      1030
                    else
                      if x.val < 1014 then
                        865
                      else
                        1224
                  else
                    if x.val < 1016 then
                      868
                    else
                      if x.val < 1017 then
                        1232
                      else
                        871
                else
                  if x.val < 1021 then
                    if x.val < 1019 then
                      1010
                    else
                      if x.val < 1020 then
                        874
                      else
                        875
                  else
                    if x.val < 1023 then
                      if x.val < 1022 then
                        905
                      else
                        877
                    else
                      if x.val < 1024 then
                        880
                      else
                        1278
            else
              if x.val < 1037 then
                if x.val < 1031 then
                  if x.val < 1028 then
                    if x.val < 1026 then
                      882
                    else
                      if x.val < 1027 then
                        1282
                      else
                        885
                  else
                    if x.val < 1029 then
                      886
                    else
                      if x.val < 1030 then
                        887
                      else
                        888
                else
                  if x.val < 1034 then
                    if x.val < 1032 then
                      942
                    else
                      if x.val < 1033 then
                        1249
                      else
                        890
                  else
                    if x.val < 1035 then
                      891
                    else
                      if x.val < 1036 then
                        1286
                      else
                        1288
              else
                if x.val < 1043 then
                  if x.val < 1040 then
                    if x.val < 1038 then
                      893
                    else
                      if x.val < 1039 then
                        894
                      else
                        895
                  else
                    if x.val < 1041 then
                      1083
                    else
                      if x.val < 1042 then
                        896
                      else
                        897
                else
                  if x.val < 1046 then
                    if x.val < 1044 then
                      901
                    else
                      if x.val < 1045 then
                        900
                      else
                        902
                  else
                    if x.val < 1048 then
                      if x.val < 1047 then
                        1172
                      else
                        1280
                    else
                      if x.val < 1049 then
                        904
                      else
                        1158
          else
            if x.val < 1075 then
              if x.val < 1062 then
                if x.val < 1056 then
                  if x.val < 1053 then
                    if x.val < 1051 then
                      906
                    else
                      if x.val < 1052 then
                        1004
                      else
                        907
                  else
                    if x.val < 1054 then
                      908
                    else
                      if x.val < 1055 then
                        1300
                      else
                        1302
                else
                  if x.val < 1059 then
                    if x.val < 1057 then
                      910
                    else
                      if x.val < 1058 then
                        913
                      else
                        1305
                  else
                    if x.val < 1060 then
                      916
                    else
                      if x.val < 1061 then
                        955
                      else
                        1308
              else
                if x.val < 1068 then
                  if x.val < 1065 then
                    if x.val < 1063 then
                      920
                    else
                      if x.val < 1064 then
                        921
                      else
                        987
                  else
                    if x.val < 1066 then
                      922
                    else
                      if x.val < 1067 then
                        923
                      else
                        924
                else
                  if x.val < 1071 then
                    if x.val < 1069 then
                      925
                    else
                      if x.val < 1070 then
                        1266
                      else
                        1315
                  else
                    if x.val < 1073 then
                      if x.val < 1072 then
                        928
                      else
                        929
                    else
                      if x.val < 1074 then
                        930
                      else
                        1319
            else
              if x.val < 1087 then
                if x.val < 1081 then
                  if x.val < 1078 then
                    if x.val < 1076 then
                      1321
                    else
                      if x.val < 1077 then
                        932
                      else
                        933
                  else
                    if x.val < 1079 then
                      1324
                    else
                      if x.val < 1080 then
                        934
                      else
                        935
                else
                  if x.val < 1084 then
                    if x.val < 1082 then
                      937
                    else
                      if x.val < 1083 then
                        939
                      else
                        1175
                  else
                    if x.val < 1085 then
                      941
                    else
                      if x.val < 1086 then
                        1015
                      else
                        943
              else
                if x.val < 1093 then
                  if x.val < 1090 then
                    if x.val < 1088 then
                      944
                    else
                      if x.val < 1089 then
                        1332
                      else
                        1274
                  else
                    if x.val < 1091 then
                      1335
                    else
                      if x.val < 1092 then
                        947
                      else
                        948
                else
                  if x.val < 1096 then
                    if x.val < 1094 then
                      1265
                    else
                      if x.val < 1095 then
                        1338
                      else
                        952
                  else
                    if x.val < 1098 then
                      if x.val < 1097 then
                        1341
                      else
                        954
                    else
                      if x.val < 1099 then
                        1072
                      else
                        957
        else
          if x.val < 1150 then
            if x.val < 1125 then
              if x.val < 1112 then
                if x.val < 1106 then
                  if x.val < 1103 then
                    if x.val < 1101 then
                      1330
                    else
                      if x.val < 1102 then
                        960
                      else
                        1344
                  else
                    if x.val < 1104 then
                      963
                    else
                      if x.val < 1105 then
                        964
                      else
                        1348
                else
                  if x.val < 1109 then
                    if x.val < 1107 then
                      965
                    else
                      if x.val < 1108 then
                        966
                      else
                        999
                  else
                    if x.val < 1110 then
                      1239
                    else
                      if x.val < 1111 then
                        969
                      else
                        970
              else
                if x.val < 1118 then
                  if x.val < 1115 then
                    if x.val < 1113 then
                      993
                    else
                      if x.val < 1114 then
                        1352
                      else
                        972
                  else
                    if x.val < 1116 then
                      973
                    else
                      if x.val < 1117 then
                        974
                      else
                        976
                else
                  if x.val < 1121 then
                    if x.val < 1119 then
                      1356
                    else
                      if x.val < 1120 then
                        977
                      else
                        1117
                  else
                    if x.val < 1123 then
                      if x.val < 1122 then
                        1263
                      else
                        980
                    else
                      if x.val < 1124 then
                        1359
                      else
                        981
            else
              if x.val < 1137 then
                if x.val < 1131 then
                  if x.val < 1128 then
                    if x.val < 1126 then
                      982
                    else
                      if x.val < 1127 then
                        983
                      else
                        984
                  else
                    if x.val < 1129 then
                      985
                    else
                      if x.val < 1130 then
                        1363
                      else
                        1340
                else
                  if x.val < 1134 then
                    if x.val < 1132 then
                      1345
                    else
                      if x.val < 1133 then
                        989
                      else
                        1312
                  else
                    if x.val < 1135 then
                      991
                    else
                      if x.val < 1136 then
                        1109
                      else
                        997
              else
                if x.val < 1143 then
                  if x.val < 1140 then
                    if x.val < 1138 then
                      1342
                    else
                      if x.val < 1139 then
                        1353
                      else
                        1001
                  else
                    if x.val < 1141 then
                      1002
                    else
                      if x.val < 1142 then
                        1003
                      else
                        1373
                else
                  if x.val < 1146 then
                    if x.val < 1144 then
                      1374
                    else
                      if x.val < 1145 then
                        1006
                      else
                        1296
                  else
                    if x.val < 1148 then
                      if x.val < 1147 then
                        1008
                      else
                        1069
                    else
                      if x.val < 1149 then
                        1011
                      else
                        1014
          else
            if x.val < 1175 then
              if x.val < 1162 then
                if x.val < 1156 then
                  if x.val < 1153 then
                    if x.val < 1151 then
                      1378
                    else
                      if x.val < 1152 then
                        1016
                      else
                        1380
                  else
                    if x.val < 1154 then
                      1017
                    else
                      if x.val < 1155 then
                        1313
                      else
                        1019
                else
                  if x.val < 1159 then
                    if x.val < 1157 then
                      1032
                    else
                      if x.val < 1158 then
                        1020
                      else
                        1182
                  else
                    if x.val < 1160 then
                      1022
                    else
                      if x.val < 1161 then
                        1024
                      else
                        1385
              else
                if x.val < 1168 then
                  if x.val < 1165 then
                    if x.val < 1163 then
                      1025
                    else
                      if x.val < 1164 then
                        1026
                      else
                        1027
                  else
                    if x.val < 1166 then
                      1028
                    else
                      if x.val < 1167 then
                        1029
                      else
                        1387
                else
                  if x.val < 1171 then
                    if x.val < 1169 then
                      1034
                    else
                      if x.val < 1170 then
                        1035
                      else
                        1036
                  else
                    if x.val < 1173 then
                      if x.val < 1172 then
                        1392
                      else
                        1179
                    else
                      if x.val < 1174 then
                        1357
                      else
                        1039
            else
              if x.val < 1187 then
                if x.val < 1181 then
                  if x.val < 1178 then
                    if x.val < 1176 then
                      1040
                    else
                      if x.val < 1177 then
                        1396
                      else
                        1042
                  else
                    if x.val < 1179 then
                      1245
                    else
                      if x.val < 1180 then
                        1046
                      else
                        1047
                else
                  if x.val < 1184 then
                    if x.val < 1182 then
                      1400
                    else
                      if x.val < 1183 then
                        1049
                      else
                        1050
                  else
                    if x.val < 1185 then
                      1095
                    else
                      if x.val < 1186 then
                        1053
                      else
                        1054
              else
                if x.val < 1193 then
                  if x.val < 1190 then
                    if x.val < 1188 then
                      1055
                    else
                      if x.val < 1189 then
                        1347
                      else
                        1058
                  else
                    if x.val < 1191 then
                      1408
                    else
                      if x.val < 1192 then
                        1060
                      else
                        1061
                else
                  if x.val < 1196 then
                    if x.val < 1194 then
                      1411
                    else
                      if x.val < 1195 then
                        1204
                      else
                        1063
                  else
                    if x.val < 1198 then
                      if x.val < 1197 then
                        1133
                      else
                        1099
                    else
                      if x.val < 1199 then
                        1068
                      else
                        1070
    else
      if x.val < 1400 then
        if x.val < 1300 then
          if x.val < 1250 then
            if x.val < 1225 then
              if x.val < 1212 then
                if x.val < 1206 then
                  if x.val < 1203 then
                    if x.val < 1201 then
                      1418
                    else
                      if x.val < 1202 then
                        1420
                      else
                        1074
                  else
                    if x.val < 1204 then
                      1075
                    else
                      if x.val < 1205 then
                        1310
                      else
                        1077
                else
                  if x.val < 1209 then
                    if x.val < 1207 then
                      1078
                    else
                      if x.val < 1208 then
                        1272
                      else
                        1080
                  else
                    if x.val < 1210 then
                      1318
                    else
                      if x.val < 1211 then
                        1429
                      else
                        1223
              else
                if x.val < 1218 then
                  if x.val < 1215 then
                    if x.val < 1213 then
                      1100
                    else
                      if x.val < 1214 then
                        1087
                      else
                        1088
                  else
                    if x.val < 1216 then
                      1089
                    else
                      if x.val < 1217 then
                        1090
                      else
                        1217
                else
                  if x.val < 1221 then
                    if x.val < 1219 then
                      1092
                    else
                      if x.val < 1220 then
                        1093
                      else
                        1094
                  else
                    if x.val < 1223 then
                      if x.val < 1222 then
                        1438
                      else
                        1096
                    else
                      if x.val < 1224 then
                        1329
                      else
                        1149
            else
              if x.val < 1237 then
                if x.val < 1231 then
                  if x.val < 1228 then
                    if x.val < 1226 then
                      1225
                    else
                      if x.val < 1227 then
                        1101
                      else
                        1102
                  else
                    if x.val < 1229 then
                      1131
                    else
                      if x.val < 1230 then
                        1104
                      else
                        1105
                else
                  if x.val < 1234 then
                    if x.val < 1232 then
                      1443
                    else
                      if x.val < 1233 then
                        1151
                      else
                        1107
                  else
                    if x.val < 1235 then
                      1108
                    else
                      if x.val < 1236 then
                        1111
                      else
                        1113
              else
                if x.val < 1243 then
                  if x.val < 1240 then
                    if x.val < 1238 then
                      1138
                    else
                      if x.val < 1239 then
                        1130
                      else
                        1135
                  else
                    if x.val < 1241 then
                      1116
                    else
                      if x.val < 1242 then
                        1432
                      else
                        1118
                else
                  if x.val < 1246 then
                    if x.val < 1244 then
                      1173
                    else
                      if x.val < 1245 then
                        1121
                      else
                        1294
                  else
                    if x.val < 1248 then
                      if x.val < 1247 then
                        1123
                      else
                        1125
                    else
                      if x.val < 1249 then
                        1450
                      else
                        1156
          else
            if x.val < 1275 then
              if x.val < 1262 then
                if x.val < 1256 then
                  if x.val < 1253 then
                    if x.val < 1251 then
                      1452
                    else
                      if x.val < 1252 then
                        1129
                      else
                        1456
                  else
                    if x.val < 1254 then
                      1444
                    else
                      if x.val < 1255 then
                        1134
                      else
                        1136
                else
                  if x.val < 1259 then
                    if x.val < 1257 then
                      1137
                    else
                      if x.val < 1258 then
                        1459
                      else
                        1140
                  else
                    if x.val < 1260 then
                      1461
                    else
                      if x.val < 1261 then
                        1141
                      else
                        1142
              else
                if x.val < 1268 then
                  if x.val < 1265 then
                    if x.val < 1263 then
                      1143
                    else
                      if x.val < 1264 then
                        1244
                      else
                        1145
                  else
                    if x.val < 1266 then
                      1219
                    else
                      if x.val < 1267 then
                        1147
                      else
                        1466
                else
                  if x.val < 1271 then
                    if x.val < 1269 then
                      1148
                    else
                      if x.val < 1270 then
                        1150
                      else
                        1446
                  else
                    if x.val < 1273 then
                      if x.val < 1272 then
                        1152
                      else
                        1325
                    else
                      if x.val < 1274 then
                        1154
                      else
                        1215
            else
              if x.val < 1287 then
                if x.val < 1281 then
                  if x.val < 1278 then
                    if x.val < 1276 then
                      1439
                    else
                      if x.val < 1277 then
                        1281
                      else
                        1473
                  else
                    if x.val < 1279 then
                      1160
                    else
                      if x.val < 1280 then
                        1161
                      else
                        1180
                else
                  if x.val < 1284 then
                    if x.val < 1282 then
                      1383
                    else
                      if x.val < 1283 then
                        1163
                      else
                        1167
                  else
                    if x.val < 1285 then
                      1295
                    else
                      if x.val < 1286 then
                        1331
                      else
                        1169
              else
                if x.val < 1293 then
                  if x.val < 1290 then
                    if x.val < 1288 then
                      1478
                    else
                      if x.val < 1289 then
                        1170
                      else
                        1171
                  else
                    if x.val < 1291 then
                      1474
                    else
                      if x.val < 1292 then
                        1472
                      else
                        1176
                else
                  if x.val < 1296 then
                    if x.val < 1294 then
                      1480
                    else
                      if x.val < 1295 then
                        1178
                      else
                        1388
                  else
                    if x.val < 1298 then
                      if x.val < 1297 then
                        1264
                      else
                        1181
                    else
                      if x.val < 1299 then
                        1390
                      else
                        1366
        else
          if x.val < 1350 then
            if x.val < 1325 then
              if x.val < 1312 then
                if x.val < 1306 then
                  if x.val < 1303 then
                    if x.val < 1301 then
                      1186
                    else
                      if x.val < 1302 then
                        1460
                      else
                        1187
                  else
                    if x.val < 1304 then
                      1188
                    else
                      if x.val < 1305 then
                        1486
                      else
                        1189
                else
                  if x.val < 1309 then
                    if x.val < 1307 then
                      1190
                    else
                      if x.val < 1308 then
                        1491
                      else
                        1192
                  else
                    if x.val < 1310 then
                      1193
                    else
                      if x.val < 1311 then
                        1194
                      else
                        1494
              else
                if x.val < 1318 then
                  if x.val < 1315 then
                    if x.val < 1313 then
                      1196
                    else
                      if x.val < 1314 then
                        1273
                      else
                        1490
                  else
                    if x.val < 1316 then
                      1199
                    else
                      if x.val < 1317 then
                        1200
                      else
                        1201
                else
                  if x.val < 1321 then
                    if x.val < 1319 then
                      1327
                    else
                      if x.val < 1320 then
                        1202
                      else
                        1499
                  else
                    if x.val < 1323 then
                      if x.val < 1322 then
                        1203
                      else
                        1501
                    else
                      if x.val < 1324 then
                        1410
                      else
                        1206
            else
              if x.val < 1337 then
                if x.val < 1331 then
                  if x.val < 1328 then
                    if x.val < 1326 then
                      1207
                    else
                      if x.val < 1327 then
                        1504
                      else
                        1209
                  else
                    if x.val < 1329 then
                      1210
                    else
                      if x.val < 1330 then
                        1211
                      else
                        1212
                else
                  if x.val < 1334 then
                    if x.val < 1332 then
                      1389
                    else
                      if x.val < 1333 then
                        1214
                      else
                        1241
                  else
                    if x.val < 1335 then
                      1506
                    else
                      if x.val < 1336 then
                        1216
                      else
                        1509
              else
                if x.val < 1343 then
                  if x.val < 1340 then
                    if x.val < 1338 then
                      1511
                    else
                      if x.val < 1339 then
                        1220
                      else
                        1221
                  else
                    if x.val < 1341 then
                      1238
                    else
                      if x.val < 1342 then
                        1222
                      else
                        1256
                else
                  if x.val < 1346 then
                    if x.val < 1344 then
                      1512
                    else
                      if x.val < 1345 then
                        1227
                      else
                        1228
                  else
                    if x.val < 1348 then
                      if x.val < 1347 then
                        1514
                      else
                        1303
                    else
                      if x.val < 1349 then
                        1230
                      else
                        1231
          else
            if x.val < 1375 then
              if x.val < 1362 then
                if x.val < 1356 then
                  if x.val < 1353 then
                    if x.val < 1351 then
                      1253
                    else
                      if x.val < 1352 then
                        1517
                      else
                        1236
                  else
                    if x.val < 1354 then
                      1237
                    else
                      if x.val < 1355 then
                        1270
                      else
                        1386
                else
                  if x.val < 1359 then
                    if x.val < 1357 then
                      1242
                    else
                      if x.val < 1358 then
                        1243
                      else
                        1476
                  else
                    if x.val < 1360 then
                      1246
                    else
                      if x.val < 1361 then
                        1248
                      else
                        1250
              else
                if x.val < 1368 then
                  if x.val < 1365 then
                    if x.val < 1363 then
                      1419
                    else
                      if x.val < 1364 then
                        1251
                      else
                        1252
                  else
                    if x.val < 1366 then
                      1488
                    else
                      if x.val < 1367 then
                        1401
                      else
                        1464
                else
                  if x.val < 1371 then
                    if x.val < 1369 then
                      1257
                    else
                      if x.val < 1370 then
                        1301
                      else
                        1259
                  else
                    if x.val < 1373 then
                      if x.val < 1372 then
                        1477
                      else
                        1481
                    else
                      if x.val < 1374 then
                        1261
                      else
                        1262
            else
              if x.val < 1387 then
                if x.val < 1381 then
                  if x.val < 1378 then
                    if x.val < 1376 then
                      1505
                    else
                      if x.val < 1377 then
                        1267
                      else
                        1529
                  else
                    if x.val < 1379 then
                      1269
                    else
                      if x.val < 1380 then
                        1530
                      else
                        1271
                else
                  if x.val < 1384 then
                    if x.val < 1382 then
                      1533
                    else
                      if x.val < 1383 then
                        1275
                      else
                        1276
                  else
                    if x.val < 1385 then
                      1277
                    else
                      if x.val < 1386 then
                        1279
                      else
                        1447
              else
                if x.val < 1393 then
                  if x.val < 1390 then
                    if x.val < 1388 then
                      1283
                    else
                      if x.val < 1389 then
                        1284
                      else
                        1285
                  else
                    if x.val < 1391 then
                      1399
                    else
                      if x.val < 1392 then
                        1287
                      else
                        1289
                else
                  if x.val < 1396 then
                    if x.val < 1394 then
                      1290
                    else
                      if x.val < 1395 then
                        1291
                      else
                        1534
                  else
                    if x.val < 1398 then
                      if x.val < 1397 then
                        1292
                      else
                        1293
                    else
                      if x.val < 1399 then
                        1358
                      else
                        1298
      else
        if x.val < 1500 then
          if x.val < 1450 then
            if x.val < 1425 then
              if x.val < 1412 then
                if x.val < 1406 then
                  if x.val < 1403 then
                    if x.val < 1401 then
                      1297
                    else
                      if x.val < 1402 then
                        1299
                      else
                        1421
                  else
                    if x.val < 1404 then
                      1497
                    else
                      if x.val < 1405 then
                        1527
                      else
                        1304
                else
                  if x.val < 1409 then
                    if x.val < 1407 then
                      1539
                    else
                      if x.val < 1408 then
                        1365
                      else
                        1306
                  else
                    if x.val < 1410 then
                      1307
                    else
                      if x.val < 1411 then
                        1424
                      else
                        1309
              else
                if x.val < 1418 then
                  if x.val < 1415 then
                    if x.val < 1413 then
                      1542
                    else
                      if x.val < 1414 then
                        1311
                      else
                        1425
                  else
                    if x.val < 1416 then
                      1314
                    else
                      if x.val < 1417 then
                        1528
                      else
                        1403
                else
                  if x.val < 1421 then
                    if x.val < 1419 then
                      1316
                    else
                      if x.val < 1420 then
                        1453
                      else
                        1317
                  else
                    if x.val < 1423 then
                      if x.val < 1422 then
                        1483
                      else
                        1320
                    else
                      if x.val < 1424 then
                        1322
                      else
                        1323
            else
              if x.val < 1437 then
                if x.val < 1431 then
                  if x.val < 1428 then
                    if x.val < 1426 then
                      1495
                    else
                      if x.val < 1427 then
                        1536
                      else
                        1326
                  else
                    if x.val < 1429 then
                      1375
                    else
                      if x.val < 1430 then
                        1328
                      else
                        1507
                else
                  if x.val < 1434 then
                    if x.val < 1432 then
                      1448
                    else
                      if x.val < 1433 then
                        1333
                      else
                        1334
                  else
                    if x.val < 1435 then
                      1430
                    else
                      if x.val < 1436 then
                        1336
                      else
                        1337
              else
                if x.val < 1443 then
                  if x.val < 1440 then
                    if x.val < 1438 then
                      1343
                    else
                      if x.val < 1439 then
                        1339
                      else
                        1382
                  else
                    if x.val < 1441 then
                      1346
                    else
                      if x.val < 1442 then
                        1455
                      else
                        1540
                else
                  if x.val < 1446 then
                    if x.val < 1444 then
                      1349
                    else
                      if x.val < 1445 then
                        1350
                      else
                        1351
                  else
                    if x.val < 1448 then
                      if x.val < 1447 then
                        1354
                      else
                        1355
                    else
                      if x.val < 1449 then
                        1468
                      else
                        1538
          else
            if x.val < 1475 then
              if x.val < 1462 then
                if x.val < 1456 then
                  if x.val < 1453 then
                    if x.val < 1451 then
                      1360
                    else
                      if x.val < 1452 then
                        1451
                      else
                        1361
                  else
                    if x.val < 1454 then
                      1362
                    else
                      if x.val < 1455 then
                        1547
                      else
                        1515
                else
                  if x.val < 1459 then
                    if x.val < 1457 then
                      1364
                    else
                      if x.val < 1458 then
                        1367
                      else
                        1560
                  else
                    if x.val < 1460 then
                      1368
                    else
                      if x.val < 1461 then
                        1369
                      else
                        1370
              else
                if x.val < 1468 then
                  if x.val < 1465 then
                    if x.val < 1463 then
                      1371
                    else
                      if x.val < 1464 then
                        1372
                      else
                        1457
                  else
                    if x.val < 1466 then
                      1553
                    else
                      if x.val < 1467 then
                        1376
                      else
                        1377
                else
                  if x.val < 1471 then
                    if x.val < 1469 then
                      1431
                    else
                      if x.val < 1470 then
                        1379
                      else
                        1485
                  else
                    if x.val < 1473 then
                      if x.val < 1472 then
                        1381
                      else
                        1394
                    else
                      if x.val < 1474 then
                        1384
                      else
                        1393
            else
              if x.val < 1487 then
                if x.val < 1481 then
                  if x.val < 1478 then
                    if x.val < 1476 then
                      1416
                    else
                      if x.val < 1477 then
                        1398
                      else
                        1462
                  else
                    if x.val < 1479 then
                      1391
                    else
                      if x.val < 1480 then
                        1395
                      else
                        1397
                else
                  if x.val < 1484 then
                    if x.val < 1482 then
                      1463
                    else
                      if x.val < 1483 then
                        1519
                      else
                        1402
                  else
                    if x.val < 1485 then
                      1404
                    else
                      if x.val < 1486 then
                        1531
                      else
                        1405
              else
                if x.val < 1493 then
                  if x.val < 1490 then
                    if x.val < 1488 then
                      1406
                    else
                      if x.val < 1489 then
                        1407
                      else
                        1554
                  else
                    if x.val < 1491 then
                      1415
                    else
                      if x.val < 1492 then
                        1409
                      else
                        1412
                else
                  if x.val < 1496 then
                    if x.val < 1494 then
                      1569
                    else
                      if x.val < 1495 then
                        1413
                      else
                        1414
                  else
                    if x.val < 1498 then
                      if x.val < 1497 then
                        1502
                      else
                        1417
                    else
                      if x.val < 1499 then
                        1454
                      else
                        1422
        else
          if x.val < 1550 then
            if x.val < 1525 then
              if x.val < 1512 then
                if x.val < 1506 then
                  if x.val < 1503 then
                    if x.val < 1501 then
                      1518
                    else
                      if x.val < 1502 then
                        1423
                      else
                        1545
                  else
                    if x.val < 1504 then
                      1426
                    else
                      if x.val < 1505 then
                        1427
                      else
                        1428
                else
                  if x.val < 1509 then
                    if x.val < 1507 then
                      1433
                    else
                      if x.val < 1508 then
                        1434
                      else
                        1465
                  else
                    if x.val < 1510 then
                      1435
                    else
                      if x.val < 1511 then
                        1571
                      else
                        1436
              else
                if x.val < 1518 then
                  if x.val < 1515 then
                    if x.val < 1513 then
                      1437
                    else
                      if x.val < 1514 then
                        1525
                      else
                        1440
                  else
                    if x.val < 1516 then
                      1441
                    else
                      if x.val < 1517 then
                        1442
                      else
                        1445
                else
                  if x.val < 1521 then
                    if x.val < 1519 then
                      1549
                    else
                      if x.val < 1520 then
                        1535
                      else
                        1449
                  else
                    if x.val < 1523 then
                      if x.val < 1522 then
                        1580
                      else
                        1581
                    else
                      if x.val < 1524 then
                        1523
                      else
                        1458
            else
              if x.val < 1537 then
                if x.val < 1531 then
                  if x.val < 1528 then
                    if x.val < 1526 then
                      1555
                    else
                      if x.val < 1527 then
                        1556
                      else
                        1484
                  else
                    if x.val < 1529 then
                      1475
                    else
                      if x.val < 1530 then
                        1467
                      else
                        1469
                else
                  if x.val < 1534 then
                    if x.val < 1532 then
                      1470
                    else
                      if x.val < 1533 then
                        1582
                      else
                        1471
                  else
                    if x.val < 1535 then
                      1479
                    else
                      if x.val < 1536 then
                        1482
                      else
                        1503
              else
                if x.val < 1543 then
                  if x.val < 1540 then
                    if x.val < 1538 then
                      1577
                    else
                      if x.val < 1539 then
                        1520
                      else
                        1487
                  else
                    if x.val < 1541 then
                      1516
                    else
                      if x.val < 1542 then
                        1489
                      else
                        1492
                else
                  if x.val < 1546 then
                    if x.val < 1544 then
                      1493
                    else
                      if x.val < 1545 then
                        1574
                      else
                        1496
                  else
                    if x.val < 1548 then
                      if x.val < 1547 then
                        1510
                      else
                        1498
                    else
                      if x.val < 1549 then
                        1590
                      else
                        1500
          else
            if x.val < 1575 then
              if x.val < 1562 then
                if x.val < 1556 then
                  if x.val < 1553 then
                    if x.val < 1551 then
                      1562
                    else
                      if x.val < 1552 then
                        1593
                      else
                        1537
                  else
                    if x.val < 1554 then
                      1508
                    else
                      if x.val < 1555 then
                        1541
                      else
                        1513
                else
                  if x.val < 1559 then
                    if x.val < 1557 then
                      1561
                    else
                      if x.val < 1558 then
                        1594
                      else
                        1521
                  else
                    if x.val < 1560 then
                      1522
                    else
                      if x.val < 1561 then
                        1524
                      else
                        1526
              else
                if x.val < 1568 then
                  if x.val < 1565 then
                    if x.val < 1563 then
                      1575
                    else
                      if x.val < 1564 then
                        1532
                      else
                        1568
                  else
                    if x.val < 1566 then
                      1597
                    else
                      if x.val < 1567 then
                        1598
                      else
                        1591
                else
                  if x.val < 1571 then
                    if x.val < 1569 then
                      1583
                    else
                      if x.val < 1570 then
                        1543
                      else
                        1544
                  else
                    if x.val < 1573 then
                      if x.val < 1572 then
                        1546
                      else
                        1587
                    else
                      if x.val < 1574 then
                        1548
                      else
                        1570
            else
              if x.val < 1587 then
                if x.val < 1581 then
                  if x.val < 1578 then
                    if x.val < 1576 then
                      1550
                    else
                      if x.val < 1577 then
                        1551
                      else
                        1552
                  else
                    if x.val < 1579 then
                      1572
                    else
                      if x.val < 1580 then
                        1557
                      else
                        1558
                else
                  if x.val < 1584 then
                    if x.val < 1582 then
                      1559
                    else
                      if x.val < 1583 then
                        1563
                      else
                        1564
                  else
                    if x.val < 1585 then
                      1565
                    else
                      if x.val < 1586 then
                        1566
                      else
                        1567
              else
                if x.val < 1593 then
                  if x.val < 1590 then
                    if x.val < 1588 then
                      1578
                    else
                      if x.val < 1589 then
                        1592
                      else
                        1588
                  else
                    if x.val < 1591 then
                      1573
                    else
                      if x.val < 1592 then
                        1586
                      else
                        1589
                else
                  if x.val < 1596 then
                    if x.val < 1594 then
                      1576
                    else
                      if x.val < 1595 then
                        1579
                      else
                        1595
                  else
                    if x.val < 1598 then
                      if x.val < 1597 then
                        1596
                      else
                        1584
                    else
                      if x.val < 1599 then
                        1585
                      else
                        1599

public theorem atlas1600AMap_involutive :
    ∀ x, atlas1600AMap (atlas1600AMap x) = x := by decide +kernel

public theorem atlas1600BMap_cube :
    ∀ x, atlas1600BMap (atlas1600BMap (atlas1600BMap x)) = x := by decide +kernel

/-- The first Atlas generator, as a left permutation. -/
@[expose] public def atlas1600A : Equiv.Perm (Fin 1600) where
  toFun := atlas1600AMap
  invFun := atlas1600AMap
  left_inv := atlas1600AMap_involutive
  right_inv := atlas1600AMap_involutive

/-- The second Atlas generator, as a left permutation. -/
@[expose] public def atlas1600B : Equiv.Perm (Fin 1600) where
  toFun := atlas1600BMap
  invFun x := atlas1600BMap (atlas1600BMap x)
  left_inv := atlas1600BMap_cube
  right_inv := atlas1600BMap_cube

/-- The concrete subgroup generated by the two Atlas permutations. -/
@[expose] public def atlas1600Subgroup : Subgroup (Equiv.Perm (Fin 1600)) :=
  Subgroup.closure {atlas1600A, atlas1600B}

/-- A finite permutation model; identification with Parrott's model is separate. -/
@[expose] public def Atlas1600Group : Type := atlas1600Subgroup
  deriving Group, Finite

public theorem atlas1600A_mem : atlas1600A ∈ atlas1600Subgroup :=
  Subgroup.subset_closure (Set.mem_insert _ _)

public theorem atlas1600B_mem : atlas1600B ∈ atlas1600Subgroup :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

end Tits
