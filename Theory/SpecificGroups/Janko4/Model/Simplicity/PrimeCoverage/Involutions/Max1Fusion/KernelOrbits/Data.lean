module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarData
import Mathlib.Tactic.FinCases

/-!
# Certificate for the two nonzero binary conjugation orbits

Each non-root mask is the image of its recorded parent under one of the two
certified right-conjugation maps. The depth strictly decreases toward roots
1 and 3. The generating Python search is untrusted; Lean checks every edge
and depth comparison. The input maps are the ATLAS local-kernel tables from
`KernelCount.Tables`.
-/

@[expose] public section
namespace Janko4.Simplicity.Max1Fusion.KernelOrbits
open Cardinality.KernelCount Cardinality.QuotientCount.Image

/-- Depth times 2048 plus the parent mask. -/
def tree (m : ℕ) : ℕ :=
  if m < 1024 then
    if m < 512 then
      if m < 256 then
        if m < 128 then
          if m < 64 then
            if m < 32 then
              if m < 16 then
                if m < 8 then
                  if m < 4 then
                    if m < 2 then
                      if m < 1 then
                        0
                      else
                        1
                    else
                      if m < 3 then
                        2049
                      else
                        3
                  else
                    if m < 6 then
                      if m < 5 then
                        2049
                      else
                        2051
                    else
                      if m < 7 then
                        4101
                      else
                        55307
                else
                  if m < 12 then
                    if m < 10 then
                      if m < 9 then
                        4100
                      else
                        6150
                    else
                      if m < 11 then
                        4101
                      else
                        53286
                  else
                    if m < 14 then
                      if m < 13 then
                        12321
                      else
                        34851
                    else
                      if m < 15 then
                        36877
                      else
                        47143
              else
                if m < 24 then
                  if m < 20 then
                    if m < 18 then
                      if m < 17 then
                        6152
                      else
                        6154
                    else
                      if m < 19 then
                        8209
                      else
                        38926
                  else
                    if m < 22 then
                      if m < 21 then
                        8201
                      else
                        55307
                    else
                      if m < 23 then
                        36877
                      else
                        45083
                else
                  if m < 28 then
                    if m < 26 then
                      if m < 25 then
                        10260
                      else
                        38934
                    else
                      if m < 27 then
                        55340
                      else
                        43054
                  else
                    if m < 30 then
                      if m < 29 then
                        49193
                      else
                        38942
                    else
                      if m < 31 then
                        36909
                      else
                        38959
            else
              if m < 48 then
                if m < 40 then
                  if m < 36 then
                    if m < 34 then
                      if m < 33 then
                        8208
                      else
                        10258
                    else
                      if m < 35 then
                        10260
                      else
                        32835
                  else
                    if m < 38 then
                      if m < 37 then
                        8209
                      else
                        40979
                    else
                      if m < 39 then
                        51273
                      else
                        45131
                else
                  if m < 44 then
                    if m < 42 then
                      if m < 41 then
                        14384
                      else
                        47174
                    else
                      if m < 43 then
                        43060
                      else
                        43062
                  else
                    if m < 46 then
                      if m < 45 then
                        53324
                      else
                        34867
                    else
                      if m < 47 then
                        41037
                      else
                        36943
              else
                if m < 56 then
                  if m < 52 then
                    if m < 50 then
                      if m < 49 then
                        12312
                      else
                        57370
                    else
                      if m < 51 then
                        47185
                      else
                        32851
                  else
                    if m < 54 then
                      if m < 53 then
                        40985
                      else
                        45083
                    else
                      if m < 55 then
                        40989
                      else
                        40991
                else
                  if m < 60 then
                    if m < 58 then
                      if m < 57 then
                        49236
                      else
                        53334
                    else
                      if m < 59 then
                        57404
                      else
                        59454
                  else
                    if m < 62 then
                      if m < 61 then
                        55353
                      else
                        57438
                    else
                      if m < 63 then
                        57437
                      else
                        41055
          else
            if m < 96 then
              if m < 80 then
                if m < 72 then
                  if m < 68 then
                    if m < 66 then
                      if m < 65 then
                        10272
                      else
                        12322
                    else
                      if m < 67 then
                        12321
                      else
                        30982
                  else
                    if m < 70 then
                      if m < 69 then
                        16424
                      else
                        45098
                    else
                      if m < 71 then
                        45317
                      else
                        43271
                else
                  if m < 76 then
                    if m < 74 then
                      if m < 73 then
                        10276
                      else
                        49442
                    else
                      if m < 75 then
                        43045
                      else
                        43302
                  else
                    if m < 78 then
                      if m < 77 then
                        51489
                      else
                        39203
                    else
                      if m < 79 then
                        36909
                      else
                        35111
              else
                if m < 88 then
                  if m < 84 then
                    if m < 82 then
                      if m < 81 then
                        14384
                      else
                        45322
                    else
                      if m < 83 then
                        55564
                      else
                        30990
                  else
                    if m < 86 then
                      if m < 85 then
                        47369
                      else
                        57611
                    else
                      if m < 87 then
                        51469
                      else
                        59663
                else
                  if m < 92 then
                    if m < 90 then
                      if m < 89 then
                        43060
                      else
                        43306
                    else
                      if m < 91 then
                        47157
                      else
                        43063
                  else
                    if m < 94 then
                      if m < 93 then
                        55593
                      else
                        55595
                    else
                      if m < 95 then
                        55597
                      else
                        39215
            else
              if m < 112 then
                if m < 104 then
                  if m < 100 then
                    if m < 98 then
                      if m < 97 then
                        59664
                      else
                        37138
                    else
                      if m < 99 then
                        39009
                      else
                        41238
                  else
                    if m < 102 then
                      if m < 101 then
                        39016
                      else
                        53354
                    else
                      if m < 103 then
                        49429
                      else
                        45335
                else
                  if m < 108 then
                    if m < 106 then
                      if m < 105 then
                        37168
                      else
                        51302
                    else
                      if m < 107 then
                        51508
                      else
                        47207
                  else
                    if m < 110 then
                      if m < 109 then
                        51505
                      else
                        39022
                    else
                      if m < 111 then
                        37173
                      else
                        45367
              else
                if m < 120 then
                  if m < 116 then
                    if m < 114 then
                      if m < 113 then
                        53528
                      else
                        59674
                    else
                      if m < 115 then
                        59676
                      else
                        37150
                  else
                    if m < 118 then
                      if m < 117 then
                        36984
                      else
                        45339
                    else
                      if m < 119 then
                        51321
                      else
                        43295
                else
                  if m < 124 then
                    if m < 122 then
                      if m < 121 then
                        35128
                      else
                        49466
                    else
                      if m < 123 then
                        47221
                      else
                        45175
                  else
                    if m < 126 then
                      if m < 125 then
                        41273
                      else
                        41275
                    else
                      if m < 127 then
                        43133
                      else
                        47423
        else
          if m < 192 then
            if m < 160 then
              if m < 144 then
                if m < 136 then
                  if m < 132 then
                    if m < 130 then
                      if m < 129 then
                        12352
                      else
                        14402
                    else
                      if m < 131 then
                        18500
                      else
                        45283
                  else
                    if m < 134 then
                      if m < 133 then
                        14401
                      else
                        32835
                    else
                      if m < 135 then
                        43241
                      else
                        39147
                else
                  if m < 140 then
                    if m < 138 then
                      if m < 137 then
                        61536
                      else
                        41058
                    else
                      if m < 139 then
                        41060
                      else
                        45287
                  else
                    if m < 142 then
                      if m < 141 then
                        39009
                      else
                        43107
                    else
                      if m < 143 then
                        55397
                      else
                        41199
              else
                if m < 152 then
                  if m < 148 then
                    if m < 146 then
                      if m < 145 then
                        12360
                      else
                        45130
                    else
                      if m < 147 then
                        47345
                      else
                        38990
                  else
                    if m < 150 then
                      if m < 149 then
                        51448
                      else
                        39162
                    else
                      if m < 151 then
                        41037
                      else
                        36943
                else
                  if m < 156 then
                    if m < 154 then
                      if m < 153 then
                        35060
                      else
                        49398
                    else
                      if m < 155 then
                        47349
                      else
                        33015
                  else
                    if m < 158 then
                      if m < 157 then
                        49404
                      else
                        49259
                    else
                      if m < 159 then
                        41069
                      else
                        41215
            else
              if m < 176 then
                if m < 168 then
                  if m < 164 then
                    if m < 162 then
                      if m < 161 then
                        16464
                      else
                        51362
                    else
                      if m < 163 then
                        49236
                      else
                        53334
                  else
                    if m < 166 then
                      if m < 165 then
                        47185
                      else
                        32851
                    else
                      if m < 167 then
                        59477
                      else
                        55467
                else
                  if m < 172 then
                    if m < 170 then
                      if m < 169 then
                        49316
                      else
                        61554
                    else
                      if m < 171 then
                        34981
                      else
                        53366
                  else
                    if m < 174 then
                      if m < 173 then
                        61553
                      else
                        39027
                    else
                      if m < 175 then
                        41133
                      else
                        45175
              else
                if m < 184 then
                  if m < 180 then
                    if m < 178 then
                      if m < 177 then
                        45144
                      else
                        49242
                    else
                      if m < 179 then
                        51377
                      else
                        57438
                  else
                    if m < 182 then
                      if m < 181 then
                        39096
                      else
                        45242
                    else
                      if m < 183 then
                        51385
                      else
                        41055
                else
                  if m < 188 then
                    if m < 186 then
                      if m < 185 then
                        36984
                      else
                        49274
                    else
                      if m < 187 then
                        43132
                      else
                        43191
                  else
                    if m < 190 then
                      if m < 189 then
                        51321
                      else
                        45246
                    else
                      if m < 191 then
                        43133
                      else
                        49279
          else
            if m < 224 then
              if m < 208 then
                if m < 200 then
                  if m < 196 then
                    if m < 194 then
                      if m < 193 then
                        45376
                      else
                        45250
                    else
                      if m < 195 then
                        43332
                      else
                        51526
                  else
                    if m < 198 then
                      if m < 197 then
                        49473
                      else
                        45379
                    else
                      if m < 199 then
                        51525
                      else
                        41163
                else
                  if m < 204 then
                    if m < 202 then
                      if m < 201 then
                        51396
                      else
                        53446
                    else
                      if m < 203 then
                        47301
                      else
                        39270
                  else
                    if m < 206 then
                      if m < 205 then
                        41313
                      else
                        45262
                    else
                      if m < 207 then
                        43365
                      else
                        37223
              else
                if m < 216 then
                  if m < 212 then
                    if m < 210 then
                      if m < 209 then
                        49480
                      else
                        49482
                    else
                      if m < 211 then
                        51532
                      else
                        33102
                  else
                    if m < 214 then
                      if m < 213 then
                        55625
                      else
                        55627
                    else
                      if m < 215 then
                        53581
                      else
                        49371
                else
                  if m < 220 then
                    if m < 218 then
                      if m < 217 then
                        57704
                      else
                        55510
                    else
                      if m < 219 then
                        57557
                      else
                        47470
                  else
                    if m < 222 then
                      if m < 221 then
                        47465
                      else
                        41323
                    else
                      if m < 223 then
                        43373
                      else
                        39279
            else
              if m < 240 then
                if m < 232 then
                  if m < 228 then
                    if m < 226 then
                      if m < 225 then
                        14464
                      else
                        20610
                    else
                      if m < 227 then
                        16513
                      else
                        43350
                  else
                    if m < 230 then
                      if m < 229 then
                        63624
                      else
                        43146
                    else
                      if m < 231 then
                        43145
                      else
                        43351
                else
                  if m < 236 then
                    if m < 234 then
                      if m < 233 then
                        16516
                      else
                        41330
                    else
                      if m < 235 then
                        34949
                      else
                        37238
                  else
                    if m < 238 then
                      if m < 237 then
                        41100
                      else
                        55667
                    else
                      if m < 239 then
                        45197
                      else
                        39287
              else
                if m < 248 then
                  if m < 244 then
                    if m < 242 then
                      if m < 241 then
                        14480
                      else
                        45402
                    else
                      if m < 243 then
                        47249
                      else
                        41107
                  else
                    if m < 246 then
                      if m < 245 then
                        33113
                      else
                        45403
                    else
                      if m < 247 then
                        47453
                      else
                        31071
                else
                  if m < 252 then
                    if m < 250 then
                      if m < 249 then
                        49528
                      else
                        43158
                    else
                      if m < 251 then
                        37244
                      else
                        39063
                  else
                    if m < 254 then
                      if m < 253 then
                        47481
                      else
                        43166
                    else
                      if m < 255 then
                        51357
                      else
                        39295
      else
        if m < 384 then
          if m < 320 then
            if m < 288 then
              if m < 272 then
                if m < 264 then
                  if m < 260 then
                    if m < 258 then
                      if m < 257 then
                        14464
                      else
                        20610
                    else
                      if m < 259 then
                        16516
                      else
                        45190
                  else
                    if m < 262 then
                      if m < 261 then
                        16513
                      else
                        43530
                    else
                      if m < 263 then
                        29193
                      else
                        41095
                else
                  if m < 268 then
                    if m < 266 then
                      if m < 265 then
                        18592
                      else
                        45574
                    else
                      if m < 267 then
                        43525
                      else
                        55815
                  else
                    if m < 270 then
                      if m < 269 then
                        53409
                      else
                        49678
                    else
                      if m < 271 then
                        29197
                      else
                        57511
              else
                if m < 280 then
                  if m < 276 then
                    if m < 274 then
                      if m < 273 then
                        57872
                      else
                        43146
                    else
                      if m < 275 then
                        35345
                      else
                        57486
                  else
                    if m < 278 then
                      if m < 277 then
                        43145
                      else
                        47243
                    else
                      if m < 279 then
                        39449
                      else
                        43151
                else
                  if m < 284 then
                    if m < 282 then
                      if m < 281 then
                        51368
                      else
                        37034
                    else
                      if m < 283 then
                        57877
                      else
                        43182
                  else
                    if m < 286 then
                      if m < 285 then
                        57884
                      else
                        53790
                    else
                      if m < 287 then
                        35357
                      else
                        41503
            else
              if m < 304 then
                if m < 296 then
                  if m < 292 then
                    if m < 290 then
                      if m < 289 then
                        14480
                      else
                        49298
                    else
                      if m < 291 then
                        47681
                      else
                        37443
                  else
                    if m < 294 then
                      if m < 293 then
                        47249
                      else
                        41107
                    else
                      if m < 295 then
                        41109
                      else
                        33355
                else
                  if m < 300 then
                    if m < 298 then
                      if m < 297 then
                        47280
                      else
                        53426
                    else
                      if m < 299 then
                        41140
                      else
                        53831
                  else
                    if m < 302 then
                      if m < 301 then
                        51377
                      else
                        53838
                    else
                      if m < 303 then
                        47285
                      else
                        37455
              else
                if m < 312 then
                  if m < 308 then
                    if m < 306 then
                      if m < 305 then
                        35408
                      else
                        49306
                    else
                      if m < 307 then
                        51356
                      else
                        43166
                  else
                    if m < 310 then
                      if m < 309 then
                        49752
                      else
                        34971
                    else
                      if m < 311 then
                        49753
                      else
                        43167
                else
                  if m < 316 then
                    if m < 314 then
                      if m < 313 then
                        33364
                      else
                        39510
                    else
                      if m < 315 then
                        47701
                      else
                        39511
                  else
                    if m < 318 then
                      if m < 317 then
                        51385
                      else
                        45243
                    else
                      if m < 319 then
                        47293
                      else
                        45663
          else
            if m < 352 then
              if m < 336 then
                if m < 328 then
                  if m < 324 then
                    if m < 322 then
                      if m < 321 then
                        43392
                      else
                        47650
                    else
                      if m < 323 then
                        49540
                      else
                        43555
                  else
                    if m < 326 then
                      if m < 325 then
                        41345
                      else
                        49706
                    else
                      if m < 327 then
                        49541
                      else
                        45447
                else
                  if m < 332 then
                    if m < 330 then
                      if m < 329 then
                        47520
                      else
                        53666
                    else
                      if m < 331 then
                        47653
                      else
                        53799
                  else
                    if m < 334 then
                      if m < 333 then
                        49569
                      else
                        51758
                    else
                      if m < 335 then
                        31277
                      else
                        53671
              else
                if m < 344 then
                  if m < 340 then
                    if m < 338 then
                      if m < 337 then
                        18824
                      else
                        63882
                    else
                      if m < 339 then
                        24972
                      else
                        47502
                  else
                    if m < 342 then
                      if m < 341 then
                        20873
                      else
                        47499
                    else
                      if m < 343 then
                        41357
                      else
                        41531
                else
                  if m < 348 then
                    if m < 346 then
                      if m < 345 then
                        18856
                      else
                        31286
                    else
                      if m < 347 then
                        43573
                      else
                        43575
                  else
                    if m < 350 then
                      if m < 349 then
                        47676
                      else
                        45483
                    else
                      if m < 351 then
                        41389
                      else
                        29103
            else
              if m < 368 then
                if m < 360 then
                  if m < 356 then
                    if m < 354 then
                      if m < 353 then
                        53856
                      else
                        39522
                    else
                      if m < 355 then
                        57748
                      else
                        45667
                  else
                    if m < 358 then
                      if m < 357 then
                        51601
                      else
                        41578
                    else
                      if m < 359 then
                        37481
                      else
                        35435
                else
                  if m < 364 then
                    if m < 362 then
                      if m < 361 then
                        55728
                      else
                        45490
                    else
                      if m < 363 then
                        59828
                      else
                        39350
                  else
                    if m < 366 then
                      if m < 365 then
                        55729
                      else
                        41582
                    else
                      if m < 367 then
                        45677
                      else
                        37303
              else
                if m < 376 then
                  if m < 372 then
                    if m < 370 then
                      if m < 369 then
                        20888
                      else
                        45466
                    else
                      if m < 371 then
                        39324
                      else
                        53662
                  else
                    if m < 374 then
                      if m < 373 then
                        39321
                      else
                        49563
                    else
                      if m < 375 then
                        35229
                      else
                        37279
                else
                  if m < 380 then
                    if m < 378 then
                      if m < 377 then
                        47732
                      else
                        45498
                    else
                      if m < 379 then
                        47548
                      else
                        47550
                  else
                    if m < 382 then
                      if m < 381 then
                        35257
                      else
                        55739
                    else
                      if m < 383 then
                        43453
                      else
                        37311
        else
          if m < 448 then
            if m < 416 then
              if m < 400 then
                if m < 392 then
                  if m < 388 then
                    if m < 386 then
                      if m < 385 then
                        41696
                      else
                        39650
                    else
                      if m < 387 then
                        51396
                      else
                        49891
                  else
                    if m < 390 then
                      if m < 389 then
                        47297
                      else
                        47850
                    else
                      if m < 391 then
                        47301
                      else
                        43755
                else
                  if m < 396 then
                    if m < 394 then
                      if m < 393 then
                        16608
                      else
                        18658
                    else
                      if m < 395 then
                        62181
                      else
                        45286
                  else
                    if m < 398 then
                      if m < 397 then
                        22753
                      else
                        39662
                    else
                      if m < 399 then
                        45285
                      else
                        45807
              else
                if m < 408 then
                  if m < 404 then
                    if m < 402 then
                      if m < 401 then
                        51952
                      else
                        49354
                    else
                      if m < 403 then
                        43212
                      else
                        45262
                  else
                    if m < 406 then
                      if m < 405 then
                        55497
                      else
                        41163
                    else
                      if m < 407 then
                        47309
                      else
                        39119
                else
                  if m < 412 then
                    if m < 410 then
                      if m < 409 then
                        18664
                      else
                        37098
                    else
                      if m < 411 then
                        43244
                      else
                        47342
                  else
                    if m < 414 then
                      if m < 413 then
                        37628
                      else
                        33534
                    else
                      if m < 415 then
                        51965
                      else
                        35583
            else
              if m < 432 then
                if m < 424 then
                  if m < 420 then
                    if m < 418 then
                      if m < 417 then
                        45728
                      else
                        47778
                    else
                      if m < 419 then
                        51873
                      else
                        53923
                  else
                    if m < 422 then
                      if m < 421 then
                        47784
                      else
                        35027
                    else
                      if m < 423 then
                        57557
                      else
                        51415
                else
                  if m < 428 then
                    if m < 426 then
                      if m < 425 then
                        16624
                      else
                        49830
                    else
                      if m < 427 then
                        35060
                      else
                        43687
                  else
                    if m < 430 then
                      if m < 429 then
                        45740
                      else
                        39598
                    else
                      if m < 431 then
                        47349
                      else
                        27311
              else
                if m < 440 then
                  if m < 436 then
                    if m < 434 then
                      if m < 433 then
                        53936
                      else
                        53938
                    else
                      if m < 435 then
                        43697
                      else
                        45278
                  else
                    if m < 438 then
                      if m < 437 then
                        57561
                      else
                        49371
                    else
                      if m < 439 then
                        37561
                      else
                        35515
                else
                  if m < 444 then
                    if m < 442 then
                      if m < 441 then
                        51448
                      else
                        33462
                    else
                      if m < 443 then
                        43701
                      else
                        53502
                  else
                    if m < 446 then
                      if m < 445 then
                        45305
                      else
                        41211
                    else
                      if m < 447 then
                        45309
                      else
                        35519
          else
            if m < 480 then
              if m < 464 then
                if m < 456 then
                  if m < 452 then
                    if m < 450 then
                      if m < 449 then
                        51904
                      else
                        53698
                    else
                      if m < 451 then
                        51905
                      else
                        51654
                  else
                    if m < 454 then
                      if m < 453 then
                        55745
                      else
                        47818
                    else
                      if m < 455 then
                        49605
                      else
                        58059
                else
                  if m < 460 then
                    if m < 458 then
                      if m < 457 then
                        45764
                      else
                        55778
                    else
                      if m < 459 then
                        43717
                      else
                        49638
                  else
                    if m < 462 then
                      if m < 461 then
                        45537
                      else
                        33251
                    else
                      if m < 463 then
                        33253
                      else
                        31207
              else
                if m < 472 then
                  if m < 468 then
                    if m < 466 then
                      if m < 465 then
                        47560
                      else
                        45514
                    else
                      if m < 467 then
                        41681
                      else
                        29395
                  else
                    if m < 470 then
                      if m < 469 then
                        57801
                      else
                        45786
                    else
                      if m < 471 then
                        35277
                      else
                        33231
                else
                  if m < 476 then
                    if m < 474 then
                      if m < 473 then
                        43732
                      else
                        53738
                    else
                      if m < 475 then
                        35308
                      else
                        41687
                  else
                    if m < 478 then
                      if m < 477 then
                        43740
                      else
                        39646
                    else
                      if m < 479 then
                        33261
                      else
                        27119
            else
              if m < 496 then
                if m < 488 then
                  if m < 484 then
                    if m < 482 then
                      if m < 481 then
                        45696
                      else
                        43474
                    else
                      if m < 483 then
                        53889
                      else
                        31363
                  else
                    if m < 486 then
                      if m < 485 then
                        47569
                      else
                        31187
                    else
                      if m < 487 then
                        47573
                      else
                        29323
                else
                  if m < 492 then
                    if m < 490 then
                      if m < 489 then
                        47600
                      else
                        47602
                    else
                      if m < 491 then
                        51700
                      else
                        43510
                  else
                    if m < 494 then
                      if m < 493 then
                        33265
                      else
                        31374
                    else
                      if m < 495 then
                        45557
                      else
                        25231
              else
                if m < 504 then
                  if m < 500 then
                    if m < 498 then
                      if m < 497 then
                        45528
                      else
                        31378
                    else
                      if m < 499 then
                        45532
                      else
                        35294
                  else
                    if m < 502 then
                      if m < 501 then
                        49816
                      else
                        43483
                    else
                      if m < 503 then
                        41437
                      else
                        29151
                else
                  if m < 508 then
                    if m < 506 then
                      if m < 505 then
                        55956
                      else
                        53754
                    else
                      if m < 507 then
                        51708
                      else
                        59902
                  else
                    if m < 510 then
                      if m < 509 then
                        49820
                      else
                        55966
                    else
                      if m < 511 then
                        57853
                      else
                        27295
    else
      if m < 768 then
        if m < 640 then
          if m < 576 then
            if m < 544 then
              if m < 528 then
                if m < 520 then
                  if m < 516 then
                    if m < 514 then
                      if m < 513 then
                        16640
                      else
                        18690
                    else
                      if m < 515 then
                        22785
                      else
                        47363
                  else
                    if m < 518 then
                      if m < 517 then
                        20744
                      else
                        42948
                    else
                      if m < 519 then
                        44994
                      else
                        55232
                else
                  if m < 524 then
                    if m < 522 then
                      if m < 521 then
                        18692
                      else
                        28645
                    else
                      if m < 523 then
                        42979
                      else
                        43271
                  else
                    if m < 526 then
                      if m < 525 then
                        55564
                      else
                        28644
                    else
                      if m < 527 then
                        49122
                      else
                        59663
              else
                if m < 536 then
                  if m < 532 then
                    if m < 530 then
                      if m < 529 then
                        57295
                      else
                        34765
                    else
                      if m < 531 then
                        42955
                      else
                        57289
                  else
                    if m < 534 then
                      if m < 533 then
                        53528
                      else
                        57292
                    else
                      if m < 535 then
                        39193
                      else
                        45339
                else
                  if m < 540 then
                    if m < 538 then
                      if m < 537 then
                        45332
                      else
                        38893
                    else
                      if m < 539 then
                        49429
                      else
                        45335
                  else
                    if m < 542 then
                      if m < 541 then
                        57326
                      else
                        34796
                    else
                      if m < 543 then
                        53226
                      else
                        40936
            else
              if m < 560 then
                if m < 552 then
                  if m < 548 then
                    if m < 546 then
                      if m < 545 then
                        45376
                      else
                        51522
                    else
                      if m < 547 then
                        47059
                      else
                        42961
                  else
                    if m < 550 then
                      if m < 549 then
                        49480
                      else
                        47060
                    else
                      if m < 551 then
                        55625
                      else
                        53200
                else
                  if m < 556 then
                    if m < 554 then
                      if m < 553 then
                        43332
                      else
                        53237
                    else
                      if m < 555 then
                        49139
                      else
                        47431
                  else
                    if m < 558 then
                      if m < 557 then
                        51532
                      else
                        30708
                    else
                      if m < 559 then
                        51186
                      else
                        53232
              else
                if m < 568 then
                  if m < 564 then
                    if m < 562 then
                      if m < 561 then
                        20816
                      else
                        26962
                    else
                      if m < 563 then
                        65873
                      else
                        49491
                  else
                    if m < 566 then
                      if m < 565 then
                        20824
                      else
                        42972
                    else
                      if m < 567 then
                        30682
                      else
                        42968
                else
                  if m < 572 then
                    if m < 570 then
                      if m < 569 then
                        22868
                      else
                        43350
                    else
                      if m < 571 then
                        47099
                      else
                        40953
                  else
                    if m < 574 then
                      if m < 573 then
                        47102
                      else
                        43358
                    else
                      if m < 575 then
                        47453
                      else
                        31071
          else
            if m < 608 then
              if m < 592 then
                if m < 584 then
                  if m < 580 then
                    if m < 578 then
                      if m < 577 then
                        16672
                      else
                        46789
                    else
                      if m < 579 then
                        50883
                      else
                        36545
                  else
                    if m < 582 then
                      if m < 581 then
                        49448
                      else
                        42692
                    else
                      if m < 583 then
                        55593
                      else
                        52928
                else
                  if m < 588 then
                    if m < 586 then
                      if m < 585 then
                        49444
                      else
                        43302
                    else
                      if m < 587 then
                        44771
                      else
                        32481
                  else
                    if m < 590 then
                      if m < 589 then
                        50918
                      else
                        49454
                    else
                      if m < 591 then
                        52962
                      else
                        36576
              else
                if m < 600 then
                  if m < 596 then
                    if m < 594 then
                      if m < 593 then
                        34511
                      else
                        53554
                    else
                      if m < 595 then
                        51505
                      else
                        45363
                  else
                    if m < 598 then
                      if m < 597 then
                        32462
                      else
                        46796
                    else
                      if m < 599 then
                        38602
                      else
                        38600
                else
                  if m < 604 then
                    if m < 602 then
                      if m < 601 then
                        48879
                      else
                        48877
                    else
                      if m < 603 then
                        37173
                      else
                        45367
                  else
                    if m < 606 then
                      if m < 605 then
                        53564
                      else
                        48876
                    else
                      if m < 607 then
                        47421
                      else
                        44776
            else
              if m < 624 then
                if m < 616 then
                  if m < 612 then
                    if m < 610 then
                      if m < 609 then
                        52951
                      else
                        59746
                    else
                      if m < 611 then
                        38611
                      else
                        44753
                  else
                    if m < 614 then
                      if m < 613 then
                        57704
                      else
                        61140
                    else
                      if m < 615 then
                        47465
                      else
                        41323
                else
                  if m < 620 then
                    if m < 618 then
                      if m < 617 then
                        53604
                      else
                        36597
                    else
                      if m < 619 then
                        40691
                      else
                        34545
                  else
                    if m < 622 then
                      if m < 621 then
                        59126
                      else
                        44788
                    else
                      if m < 623 then
                        40690
                      else
                        39279
              else
                if m < 632 then
                  if m < 628 then
                    if m < 626 then
                      if m < 625 then
                        22896
                      else
                        41330
                    else
                      if m < 627 then
                        48859
                      else
                        52953
                  else
                    if m < 630 then
                      if m < 629 then
                        46814
                      else
                        49530
                    else
                      if m < 631 then
                        44762
                      else
                        49531
                else
                  if m < 636 then
                    if m < 634 then
                      if m < 633 then
                        41332
                      else
                        37238
                    else
                      if m < 635 then
                        51573
                      else
                        39287
                  else
                    if m < 638 then
                      if m < 637 then
                        37244
                      else
                        44796
                    else
                      if m < 639 then
                        57725
                      else
                        39295
        else
          if m < 704 then
            if m < 672 then
              if m < 656 then
                if m < 648 then
                  if m < 644 then
                    if m < 642 then
                      if m < 641 then
                        44935
                      else
                        53125
                    else
                      if m < 643 then
                        45537
                      else
                        30593
                  else
                    if m < 646 then
                      if m < 645 then
                        49640
                      else
                        53124
                    else
                      if m < 647 then
                        49641
                      else
                        45547
                else
                  if m < 652 then
                    if m < 650 then
                      if m < 649 then
                        49636
                      else
                        49638
                    else
                      if m < 651 then
                        33253
                      else
                        28577
                  else
                    if m < 654 then
                      if m < 653 then
                        35308
                      else
                        47598
                    else
                      if m < 655 then
                        30626
                      else
                        24480
              else
                if m < 664 then
                  if m < 660 then
                    if m < 658 then
                      if m < 657 then
                        47600
                      else
                        47602
                    else
                      if m < 659 then
                        30603
                      else
                        37363
                  else
                    if m < 662 then
                      if m < 661 then
                        55182
                      else
                        53754
                    else
                      if m < 663 then
                        55801
                      else
                        61947
                else
                  if m < 668 then
                    if m < 666 then
                      if m < 665 then
                        49071
                      else
                        43510
                    else
                      if m < 667 then
                        45557
                      else
                        31223
                  else
                    if m < 670 then
                      if m < 669 then
                        49070
                      else
                        59308
                    else
                      if m < 671 then
                        55210
                      else
                        26536
            else
              if m < 688 then
                if m < 680 then
                  if m < 676 then
                    if m < 674 then
                      if m < 673 then
                        44951
                      else
                        51093
                    else
                      if m < 675 then
                        46995
                      else
                        53137
                  else
                    if m < 678 then
                      if m < 677 then
                        18856
                      else
                        37290
                    else
                      if m < 679 then
                        49042
                      else
                        42896
                else
                  if m < 684 then
                    if m < 682 then
                      if m < 681 then
                        47031
                      else
                        57269
                    else
                      if m < 683 then
                        37285
                      else
                        53671
                  else
                    if m < 686 then
                      if m < 685 then
                        44982
                      else
                        49582
                    else
                      if m < 687 then
                        38834
                      else
                        26544
              else
                if m < 696 then
                  if m < 692 then
                    if m < 690 then
                      if m < 689 then
                        53151
                      else
                        42909
                    else
                      if m < 691 then
                        53147
                      else
                        47539
                  else
                    if m < 694 then
                      if m < 693 then
                        53688
                      else
                        42908
                    else
                      if m < 695 then
                        32666
                      else
                        55739
                else
                  if m < 700 then
                    if m < 698 then
                      if m < 697 then
                        59327
                      else
                        36797
                    else
                      if m < 699 then
                        51637
                      else
                        34745
                  else
                    if m < 702 then
                      if m < 701 then
                        47548
                      else
                        47550
                    else
                      if m < 703 then
                        43453
                      else
                        34744
          else
            if m < 736 then
              if m < 720 then
                if m < 712 then
                  if m < 708 then
                    if m < 706 then
                      if m < 705 then
                        50823
                      else
                        50821
                    else
                      if m < 707 then
                        55745
                      else
                        53699
                  else
                    if m < 710 then
                      if m < 709 then
                        44678
                      else
                        42628
                    else
                      if m < 711 then
                        56962
                      else
                        52864
                else
                  if m < 716 then
                    if m < 714 then
                      if m < 713 then
                        54951
                      else
                        51654
                    else
                      if m < 715 then
                        46755
                      else
                        56993
                  else
                    if m < 718 then
                      if m < 717 then
                        46758
                      else
                        35278
                    else
                      if m < 719 then
                        35277
                      else
                        33231
              else
                if m < 728 then
                  if m < 724 then
                    if m < 722 then
                      if m < 721 then
                        49616
                      else
                        40589
                    else
                      if m < 723 then
                        47569
                      else
                        28297
                  else
                    if m < 726 then
                      if m < 725 then
                        42638
                      else
                        37338
                    else
                      if m < 727 then
                        55769
                      else
                        40584
                else
                  if m < 732 then
                    if m < 730 then
                      if m < 729 then
                        59055
                      else
                        37334
                    else
                      if m < 731 then
                        44715
                      else
                        35287
                  else
                    if m < 734 then
                      if m < 733 then
                        42670
                      else
                        35294
                    else
                      if m < 735 then
                        38570
                      else
                        29151
            else
              if m < 752 then
                if m < 744 then
                  if m < 740 then
                    if m < 738 then
                      if m < 737 then
                        40599
                      else
                        52885
                    else
                      if m < 739 then
                        38547
                      else
                        48785
                  else
                    if m < 742 then
                      if m < 741 then
                        18824
                      else
                        61076
                    else
                      if m < 743 then
                        20873
                      else
                        47499
                else
                  if m < 748 then
                    if m < 746 then
                      if m < 745 then
                        48823
                      else
                        49542
                    else
                      if m < 747 then
                        46771
                      else
                        42673
                  else
                    if m < 750 then
                      if m < 749 then
                        24972
                      else
                        47502
                    else
                      if m < 751 then
                        38578
                      else
                        44720
              else
                if m < 760 then
                  if m < 756 then
                    if m < 754 then
                      if m < 753 then
                        50847
                      else
                        42653
                    else
                      if m < 755 then
                        51601
                      else
                        46745
                  else
                    if m < 758 then
                      if m < 757 then
                        20888
                      else
                        45466
                    else
                      if m < 759 then
                        39321
                      else
                        48792
                else
                  if m < 764 then
                    if m < 762 then
                      if m < 761 then
                        59071
                      else
                        48829
                    else
                      if m < 763 then
                        43413
                      else
                        41367
                  else
                    if m < 766 then
                      if m < 765 then
                        36542
                      else
                        50876
                    else
                      if m < 767 then
                        32442
                      else
                        34488
      else
        if m < 896 then
          if m < 832 then
            if m < 800 then
              if m < 784 then
                if m < 776 then
                  if m < 772 then
                    if m < 770 then
                      if m < 769 then
                        53063
                      else
                        62210
                    else
                      if m < 771 then
                        61251
                      else
                        57153
                  else
                    if m < 774 then
                      if m < 773 then
                        34630
                      else
                        48964
                    else
                      if m < 775 then
                        55106
                      else
                        24384
                else
                  if m < 780 then
                    if m < 778 then
                      if m < 777 then
                        35588
                      else
                        55141
                    else
                      if m < 779 then
                        49925
                      else
                        25351
                  else
                    if m < 782 then
                      if m < 781 then
                        46950
                      else
                        51982
                    else
                      if m < 783 then
                        51042
                      else
                        55136
              else
                if m < 792 then
                  if m < 788 then
                    if m < 786 then
                      if m < 785 then
                        48975
                      else
                        49938
                    else
                      if m < 787 then
                        48971
                      else
                        48969
                  else
                    if m < 790 then
                      if m < 789 then
                        51022
                      else
                        61260
                    else
                      if m < 791 then
                        34634
                      else
                        35611
                else
                  if m < 796 then
                    if m < 794 then
                      if m < 793 then
                        51988
                      else
                        35606
                    else
                      if m < 795 then
                        61291
                      else
                        34665
                  else
                    if m < 798 then
                      if m < 797 then
                        36718
                      else
                        49004
                    else
                      if m < 799 then
                        51050
                      else
                        67432
            else
              if m < 816 then
                if m < 808 then
                  if m < 804 then
                    if m < 802 then
                      if m < 801 then
                        46935
                      else
                        56130
                    else
                      if m < 803 then
                        59219
                      else
                        57169
                  else
                    if m < 806 then
                      if m < 805 then
                        46934
                      else
                        49994
                    else
                      if m < 807 then
                        37705
                      else
                        57168
                else
                  if m < 812 then
                    if m < 810 then
                      if m < 809 then
                        31556
                      else
                        46965
                    else
                      if m < 811 then
                        30579
                      else
                        55153
                  else
                    if m < 814 then
                      if m < 813 then
                        46966
                      else
                        35662
                    else
                      if m < 815 then
                        37709
                      else
                        55152
              else
                if m < 824 then
                  if m < 820 then
                    if m < 818 then
                      if m < 817 then
                        46943
                      else
                        51037
                    else
                      if m < 819 then
                        32603
                      else
                        47955
                  else
                    if m < 822 then
                      if m < 821 then
                        30558
                      else
                        27482
                    else
                      if m < 823 then
                        28506
                      else
                        51032
                else
                  if m < 828 then
                    if m < 826 then
                      if m < 825 then
                        39764
                      else
                        46973
                    else
                      if m < 827 then
                        47957
                      else
                        32633
                  else
                    if m < 830 then
                      if m < 829 then
                        58204
                      else
                        38780
                    else
                      if m < 831 then
                        50013
                      else
                        32632
          else
            if m < 864 then
              if m < 848 then
                if m < 840 then
                  if m < 836 then
                    if m < 834 then
                      if m < 833 then
                        47904
                      else
                        60997
                    else
                      if m < 835 then
                        54851
                      else
                        54849
                  else
                    if m < 838 then
                      if m < 837 then
                        30278
                      else
                        31530
                    else
                      if m < 839 then
                        47913
                      else
                        54848
                else
                  if m < 844 then
                    if m < 842 then
                      if m < 841 then
                        47908
                      else
                        36453
                    else
                      if m < 843 then
                        48739
                      else
                        58151
                  else
                    if m < 846 then
                      if m < 845 then
                        47916
                      else
                        36452
                    else
                      if m < 847 then
                        34402
                      else
                        54880
              else
                if m < 856 then
                  if m < 852 then
                    if m < 850 then
                      if m < 849 then
                        47920
                      else
                        33586
                    else
                      if m < 851 then
                        48715
                      else
                        46665
                  else
                    if m < 854 then
                      if m < 853 then
                        38478
                      else
                        46668
                    else
                      if m < 855 then
                        47929
                      else
                        33595
                else
                  if m < 860 then
                    if m < 858 then
                      if m < 857 then
                        31540
                      else
                        29494
                    else
                      if m < 859 then
                        26219
                      else
                        50793
                  else
                    if m < 862 then
                      if m < 861 then
                        56942
                      else
                        48748
                    else
                      if m < 863 then
                        39741
                      else
                        33599
            else
              if m < 880 then
                if m < 872 then
                  if m < 868 then
                    if m < 866 then
                      if m < 865 then
                        58967
                      else
                        41826
                    else
                      if m < 867 then
                        40531
                      else
                        30289
                  else
                    if m < 870 then
                      if m < 869 then
                        48726
                      else
                        41834
                    else
                      if m < 871 then
                        43881
                      else
                        56912
                else
                  if m < 876 then
                    if m < 874 then
                      if m < 873 then
                        46711
                      else
                        42613
                    else
                      if m < 875 then
                        40563
                      else
                        56945
                  else
                    if m < 878 then
                      if m < 877 then
                        50806
                      else
                        43886
                    else
                      if m < 879 then
                        42610
                      else
                        50800
              else
                if m < 888 then
                  if m < 884 then
                    if m < 882 then
                      if m < 881 then
                        48735
                      else
                        30301
                    else
                      if m < 883 then
                        31601
                      else
                        28249
                  else
                    if m < 886 then
                      if m < 885 then
                        33656
                      else
                        54876
                    else
                      if m < 887 then
                        45945
                      else
                        58968
                else
                  if m < 892 then
                    if m < 890 then
                      if m < 889 then
                        32383
                      else
                        44669
                    else
                      if m < 891 then
                        54907
                      else
                        56953
                  else
                    if m < 894 then
                      if m < 893 then
                        50814
                      else
                        59004
                    else
                      if m < 895 then
                        60285
                      else
                        59000
        else
          if m < 960 then
            if m < 928 then
              if m < 912 then
                if m < 904 then
                  if m < 900 then
                    if m < 898 then
                      if m < 897 then
                        50951
                      else
                        48901
                    else
                      if m < 899 then
                        35809
                      else
                        28417
                  else
                    if m < 902 then
                      if m < 901 then
                        55046
                      else
                        30468
                    else
                      if m < 903 then
                        59138
                      else
                        30464
                else
                  if m < 908 then
                    if m < 906 then
                      if m < 905 then
                        46052
                      else
                        40741
                    else
                      if m < 907 then
                        37861
                      else
                        34593
                  else
                    if m < 910 then
                      if m < 909 then
                        38694
                      else
                        37870
                    else
                      if m < 911 then
                        44834
                      else
                        46880
              else
                if m < 920 then
                  if m < 916 then
                    if m < 914 then
                      if m < 913 then
                        55055
                      else
                        52210
                    else
                      if m < 915 then
                        39921
                      else
                        35827
                  else
                    if m < 918 then
                      if m < 917 then
                        50958
                      else
                        48908
                    else
                      if m < 919 then
                        46073
                      else
                        50952
                else
                  if m < 924 then
                    if m < 922 then
                      if m < 921 then
                        48116
                      else
                        58358
                    else
                      if m < 923 then
                        40747
                      else
                        48937
                  else
                    if m < 926 then
                      if m < 925 then
                        34606
                      else
                        36652
                    else
                      if m < 927 then
                        42794
                      else
                        40744
            else
              if m < 944 then
                if m < 936 then
                  if m < 932 then
                    if m < 930 then
                      if m < 929 then
                        59159
                      else
                        44821
                    else
                      if m < 931 then
                        45985
                      else
                        61201
                  else
                    if m < 934 then
                      if m < 933 then
                        59158
                      else
                        45994
                    else
                      if m < 935 then
                        44818
                      else
                        55056
                else
                  if m < 940 then
                    if m < 938 then
                      if m < 937 then
                        60324
                      else
                        45990
                    else
                      if m < 939 then
                        44851
                      else
                        57137
                  else
                    if m < 942 then
                      if m < 941 then
                        61238
                      else
                        33710
                    else
                      if m < 943 then
                        32562
                      else
                        38704
              else
                if m < 952 then
                  if m < 948 then
                    if m < 946 then
                      if m < 945 then
                        46879
                      else
                        42781
                    else
                      if m < 947 then
                        43953
                      else
                        44825
                  else
                    if m < 950 then
                      if m < 949 then
                        46878
                      else
                        38684
                    else
                      if m < 951 then
                        50970
                      else
                        44824
                else
                  if m < 956 then
                    if m < 954 then
                      if m < 953 then
                        48052
                      else
                        52150
                    else
                      if m < 955 then
                        39861
                      else
                        46007
                  else
                    if m < 958 then
                      if m < 957 then
                        53054
                      else
                        40764
                    else
                      if m < 959 then
                        41917
                      else
                        36664
          else
            if m < 992 then
              if m < 976 then
                if m < 968 then
                  if m < 964 then
                    if m < 962 then
                      if m < 961 then
                        46599
                      else
                        40453
                    else
                      if m < 963 then
                        41921
                      else
                        44545
                  else
                    if m < 966 then
                      if m < 965 then
                        44550
                      else
                        38404
                    else
                      if m < 967 then
                        54786
                      else
                        42496
                else
                  if m < 972 then
                    if m < 970 then
                      if m < 969 then
                        46631
                      else
                        56262
                    else
                      if m < 971 then
                        39877
                      else
                        43975
                  else
                    if m < 974 then
                      if m < 973 then
                        48678
                      else
                        35790
                    else
                      if m < 975 then
                        34338
                      else
                        38432
              else
                if m < 984 then
                  if m < 980 then
                    if m < 978 then
                      if m < 977 then
                        56847
                      else
                        44557
                    else
                      if m < 979 then
                        46033
                      else
                        48649
                  else
                    if m < 982 then
                      if m < 981 then
                        38414
                      else
                        44556
                    else
                      if m < 983 then
                        60938
                      else
                        40456
                else
                  if m < 988 then
                    if m < 986 then
                      if m < 985 then
                        39892
                      else
                        63021
                    else
                      if m < 987 then
                        46037
                      else
                        41943
                  else
                    if m < 990 then
                      if m < 989 then
                        50734
                      else
                        50732
                    else
                      if m < 991 then
                        52189
                      else
                        52776
            else
              if m < 1008 then
                if m < 1000 then
                  if m < 996 then
                    if m < 994 then
                      if m < 993 then
                        52096
                      else
                        34325
                    else
                      if m < 995 then
                        48659
                      else
                        29571
                  else
                    if m < 998 then
                      if m < 997 then
                        44566
                      else
                        36372
                    else
                      if m < 999 then
                        41865
                      else
                        35723
                else
                  if m < 1004 then
                    if m < 1002 then
                      if m < 1001 then
                        56196
                      else
                        60981
                    else
                      if m < 1003 then
                        31621
                      else
                        31623
                  else
                    if m < 1006 then
                      if m < 1005 then
                        39820
                      else
                        45966
                    else
                      if m < 1007 then
                        36402
                      else
                        44592
              else
                if m < 1016 then
                  if m < 1012 then
                    if m < 1010 then
                      if m < 1009 then
                        56863
                      else
                        38429
                    else
                      if m < 1011 then
                        50715
                      else
                        34329
                  else
                    if m < 1014 then
                      if m < 1013 then
                        46622
                      else
                        41882
                    else
                      if m < 1015 then
                        56858
                      else
                        50075
                else
                  if m < 1020 then
                    if m < 1018 then
                      if m < 1017 then
                        50751
                      else
                        44605
                    else
                      if m < 1019 then
                        50069
                      else
                        52119
                  else
                    if m < 1022 then
                      if m < 1021 then
                        35740
                      else
                        42556
                    else
                      if m < 1023 then
                        34362
                      else
                        42552
  else
    if m < 1536 then
      if m < 1280 then
        if m < 1152 then
          if m < 1088 then
            if m < 1056 then
              if m < 1040 then
                if m < 1032 then
                  if m < 1028 then
                    if m < 1026 then
                      if m < 1025 then
                        18944
                      else
                        25090
                    else
                      if m < 1027 then
                        23044
                      else
                        40867
                  else
                    if m < 1030 then
                      if m < 1029 then
                        20993
                      else
                        49667
                    else
                      if m < 1031 then
                        38825
                      else
                        53163
                else
                  if m < 1036 then
                    if m < 1034 then
                      if m < 1033 then
                        47648
                      else
                        42918
                    else
                      if m < 1035 then
                        51748
                      else
                        57255
                  else
                    if m < 1038 then
                      if m < 1037 then
                        53793
                      else
                        43555
                    else
                      if m < 1039 then
                        47653
                      else
                        49071
              else
                if m < 1048 then
                  if m < 1044 then
                    if m < 1042 then
                      if m < 1041 then
                        21000
                      else
                        38834
                    else
                      if m < 1043 then
                        57868
                      else
                        44979
                  else
                    if m < 1046 then
                      if m < 1045 then
                        29193
                      else
                        45579
                    else
                      if m < 1047 then
                        29197
                      else
                        59323
                else
                  if m < 1052 then
                    if m < 1050 then
                      if m < 1049 then
                        45608
                      else
                        44982
                    else
                      if m < 1051 then
                        53804
                      else
                        47031
                  else
                    if m < 1054 then
                      if m < 1053 then
                        55228
                      else
                        51134
                    else
                      if m < 1055 then
                        31277
                      else
                        53807
            else
              if m < 1072 then
                if m < 1064 then
                  if m < 1060 then
                    if m < 1058 then
                      if m < 1057 then
                        57872
                      else
                        43538
                    else
                      if m < 1059 then
                        51169
                      else
                        41494
                  else
                    if m < 1062 then
                      if m < 1061 then
                        35345
                      else
                        53226
                    else
                      if m < 1063 then
                        53225
                      else
                        47639
                else
                  if m < 1068 then
                    if m < 1066 then
                      if m < 1065 then
                        23088
                      else
                        63462
                    else
                      if m < 1067 then
                        23092
                      else
                        26599
                  else
                    if m < 1070 then
                      if m < 1069 then
                        29233
                      else
                        51763
                    else
                      if m < 1071 then
                        38893
                      else
                        43575
              else
                if m < 1080 then
                  if m < 1076 then
                    if m < 1074 then
                      if m < 1073 then
                        47640
                      else
                        51186
                    else
                      if m < 1075 then
                        55281
                      else
                        49139
                  else
                    if m < 1078 then
                      if m < 1077 then
                        34808
                      else
                        47643
                    else
                      if m < 1079 then
                        35357
                      else
                        41503
                else
                  if m < 1084 then
                    if m < 1082 then
                      if m < 1081 then
                        25144
                      else
                        47674
                    else
                      if m < 1083 then
                        47676
                      else
                        49726
                  else
                    if m < 1086 then
                      if m < 1085 then
                        45625
                      else
                        41531
                    else
                      if m < 1087 then
                        45629
                      else
                        30719
          else
            if m < 1120 then
              if m < 1104 then
                if m < 1096 then
                  if m < 1092 then
                    if m < 1090 then
                      if m < 1089 then
                        49024
                      else
                        57218
                    else
                      if m < 1091 then
                        30593
                      else
                        51075
                  else
                    if m < 1094 then
                      if m < 1093 then
                        65416
                      else
                        58115
                    else
                      if m < 1095 then
                        44937
                      else
                        25351
                else
                  if m < 1100 then
                    if m < 1098 then
                      if m < 1097 then
                        47904
                      else
                        57222
                    else
                      if m < 1099 then
                        47908
                      else
                        39718
                  else
                    if m < 1102 then
                      if m < 1101 then
                        58145
                      else
                        55182
                    else
                      if m < 1103 then
                        52005
                      else
                        55183
              else
                if m < 1112 then
                  if m < 1108 then
                    if m < 1106 then
                      if m < 1105 then
                        37640
                      else
                        49042
                    else
                      if m < 1107 then
                        47884
                      else
                        46995
                  else
                    if m < 1110 then
                      if m < 1109 then
                        56073
                      else
                        27403
                    else
                      if m < 1111 then
                        51097
                      else
                        53147
                else
                  if m < 1116 then
                    if m < 1114 then
                      if m < 1113 then
                        33576
                      else
                        26518
                    else
                      if m < 1115 then
                        47916
                      else
                        39726
                  else
                    if m < 1118 then
                      if m < 1117 then
                        42908
                      else
                        57246
                    else
                      if m < 1119 then
                        37677
                      else
                        53151
            else
              if m < 1136 then
                if m < 1128 then
                  if m < 1124 then
                    if m < 1122 then
                      if m < 1121 then
                        49936
                      else
                        44994
                    else
                      if m < 1123 then
                        51988
                      else
                        30659
                  else
                    if m < 1126 then
                      if m < 1125 then
                        51985
                      else
                        47050
                    else
                      if m < 1127 then
                        57289
                      else
                        37655
                else
                  if m < 1132 then
                    if m < 1130 then
                      if m < 1129 then
                        42948
                      else
                        28614
                    else
                      if m < 1131 then
                        26565
                      else
                        24519
                  else
                    if m < 1134 then
                      if m < 1133 then
                        52017
                      else
                        49971
                    else
                      if m < 1135 then
                        29493
                      else
                        52023
              else
                if m < 1144 then
                  if m < 1140 then
                    if m < 1138 then
                      if m < 1137 then
                        53200
                      else
                        61394
                    else
                      if m < 1139 then
                        37660
                      else
                        47059
                  else
                    if m < 1142 then
                      if m < 1141 then
                        37657
                      else
                        30682
                    else
                      if m < 1143 then
                        49949
                      else
                        67547
                else
                  if m < 1148 then
                    if m < 1146 then
                      if m < 1145 then
                        41784
                      else
                        49978
                    else
                      if m < 1147 then
                        59349
                      else
                        52030
                  else
                    if m < 1150 then
                      if m < 1149 then
                        42972
                      else
                        28638
                    else
                      if m < 1151 then
                        34781
                      else
                        28639
        else
          if m < 1216 then
            if m < 1184 then
              if m < 1168 then
                if m < 1160 then
                  if m < 1156 then
                    if m < 1154 then
                      if m < 1153 then
                        19008
                      else
                        51778
                    else
                      if m < 1155 then
                        51780
                      else
                        57926
                  else
                    if m < 1158 then
                      if m < 1157 then
                        42824
                      else
                        34634
                    else
                      if m < 1159 then
                        43589
                      else
                        48971
                else
                  if m < 1164 then
                    if m < 1162 then
                      if m < 1161 then
                        48964
                      else
                        34630
                    else
                      if m < 1163 then
                        60004
                      else
                        49766
                  else
                    if m < 1166 then
                      if m < 1165 then
                        61260
                      else
                        45667
                    else
                      if m < 1167 then
                        57165
                      else
                        43623
              else
                if m < 1176 then
                  if m < 1172 then
                    if m < 1170 then
                      if m < 1169 then
                        51784
                      else
                        44882
                    else
                      if m < 1171 then
                        51788
                      else
                        53838
                  else
                    if m < 1174 then
                      if m < 1173 then
                        45641
                      else
                        28506
                    else
                      if m < 1175 then
                        51789
                      else
                        32603
                else
                  if m < 1180 then
                    if m < 1178 then
                      if m < 1177 then
                        55912
                      else
                        41578
                    else
                      if m < 1179 then
                        60012
                      else
                        41582
                  else
                    if m < 1182 then
                      if m < 1181 then
                        34652
                      else
                        30558
                    else
                      if m < 1183 then
                        45677
                      else
                        41583
            else
              if m < 1200 then
                if m < 1192 then
                  if m < 1188 then
                    if m < 1186 then
                      if m < 1185 then
                        30464
                      else
                        53842
                    else
                      if m < 1187 then
                        28417
                      else
                        39510
                  else
                    if m < 1190 then
                      if m < 1189 then
                        50952
                      else
                        47699
                    else
                      if m < 1191 then
                        42761
                      else
                        39511
                else
                  if m < 1196 then
                    if m < 1194 then
                      if m < 1193 then
                        25200
                      else
                        49778
                    else
                      if m < 1195 then
                        47732
                      else
                        45686
                  else
                    if m < 1198 then
                      if m < 1197 then
                        43633
                      else
                        50958
                    else
                      if m < 1199 then
                        51829
                      else
                        51831
              else
                if m < 1208 then
                  if m < 1204 then
                    if m < 1202 then
                      if m < 1201 then
                        49752
                      else
                        39514
                    else
                      if m < 1203 then
                        55900
                      else
                        50963
                  else
                    if m < 1206 then
                      if m < 1205 then
                        44824
                      else
                        47707
                    else
                      if m < 1207 then
                        44825
                      else
                        46875
                else
                  if m < 1212 then
                    if m < 1210 then
                      if m < 1209 then
                        43640
                      else
                        53882
                    else
                      if m < 1211 then
                        39548
                      else
                        59159
                  else
                    if m < 1214 then
                      if m < 1213 then
                        38684
                      else
                        41595
                    else
                      if m < 1215 then
                        42781
                      else
                        41599
          else
            if m < 1248 then
              if m < 1232 then
                if m < 1224 then
                  if m < 1220 then
                    if m < 1218 then
                      if m < 1217 then
                        49984
                      else
                        51042
                    else
                      if m < 1219 then
                        31556
                      else
                        49990
                  else
                    if m < 1222 then
                      if m < 1221 then
                        62273
                      else
                        51050
                    else
                      if m < 1223 then
                        34665
                      else
                        56135
                else
                  if m < 1228 then
                    if m < 1226 then
                      if m < 1225 then
                        55140
                      else
                        41826
                    else
                      if m < 1227 then
                        50020
                      else
                        42855
                  else
                    if m < 1230 then
                      if m < 1229 then
                        43873
                      else
                        31587
                    else
                      if m < 1231 then
                        42861
                      else
                        57199
              else
                if m < 1240 then
                  if m < 1236 then
                    if m < 1234 then
                      if m < 1233 then
                        49992
                      else
                        44914
                    else
                      if m < 1235 then
                        49996
                      else
                        30579
                  else
                    if m < 1238 then
                      if m < 1237 then
                        32632
                      else
                        57210
                    else
                      if m < 1239 then
                        32633
                      else
                        55163
                else
                  if m < 1244 then
                    if m < 1242 then
                      if m < 1241 then
                        42868
                      else
                        41834
                    else
                      if m < 1243 then
                        46965
                      else
                        38775
                  else
                    if m < 1246 then
                      if m < 1245 then
                        38780
                      else
                        58219
                    else
                      if m < 1247 then
                        46973
                      else
                        46975
            else
              if m < 1264 then
                if m < 1256 then
                  if m < 1252 then
                    if m < 1250 then
                      if m < 1249 then
                        46880
                      else
                        44834
                    else
                      if m < 1251 then
                        34593
                      else
                        44835
                  else
                    if m < 1254 then
                      if m < 1253 then
                        35665
                      else
                        42794
                    else
                      if m < 1255 then
                        47957
                      else
                        35671
                else
                  if m < 1260 then
                    if m < 1258 then
                      if m < 1257 then
                        44836
                      else
                        33650
                    else
                      if m < 1259 then
                        35700
                      else
                        47990
                  else
                    if m < 1262 then
                      if m < 1261 then
                        31601
                      else
                        29555
                    else
                      if m < 1263 then
                        56181
                      else
                        55087
              else
                if m < 1272 then
                  if m < 1268 then
                    if m < 1266 then
                      if m < 1265 then
                        33624
                      else
                        27482
                    else
                      if m < 1267 then
                        57137
                      else
                        41822
                  else
                    if m < 1270 then
                      if m < 1269 then
                        31577
                      else
                        46906
                    else
                      if m < 1271 then
                        50013
                      else
                        35679
                else
                  if m < 1276 then
                    if m < 1274 then
                      if m < 1273 then
                        33656
                      else
                        56186
                    else
                      if m < 1275 then
                        53045
                      else
                        61239
                  else
                    if m < 1278 then
                      if m < 1277 then
                        40764
                      else
                        53054
                    else
                      if m < 1279 then
                        59197
                      else
                        55103
      else
        if m < 1408 then
          if m < 1344 then
            if m < 1312 then
              if m < 1296 then
                if m < 1288 then
                  if m < 1284 then
                    if m < 1282 then
                      if m < 1281 then
                        45696
                      else
                        46498
                    else
                      if m < 1283 then
                        52641
                      else
                        51846
                  else
                    if m < 1286 then
                      if m < 1285 then
                        53889
                      else
                        26026
                    else
                      if m < 1287 then
                        53893
                      else
                        44459
                else
                  if m < 1292 then
                    if m < 1290 then
                      if m < 1289 then
                        44452
                      else
                        42406
                    else
                      if m < 1291 then
                        21156
                      else
                        44455
                  else
                    if m < 1294 then
                      if m < 1293 then
                        46508
                      else
                        50606
                    else
                      if m < 1295 then
                        39589
                      else
                        43687
              else
                if m < 1304 then
                  if m < 1300 then
                    if m < 1298 then
                      if m < 1297 then
                        51848
                      else
                        35466
                    else
                      if m < 1299 then
                        37516
                      else
                        31374
                  else
                    if m < 1302 then
                      if m < 1301 then
                        51849
                      else
                        29323
                    else
                      if m < 1303 then
                        48569
                      else
                        25231
                else
                  if m < 1308 then
                    if m < 1306 then
                      if m < 1305 then
                        42420
                      else
                        39594
                    else
                      if m < 1307 then
                        40373
                      else
                        34231
                  else
                    if m < 1310 then
                      if m < 1309 then
                        52668
                      else
                        54718
                    else
                      if m < 1311 then
                        46525
                      else
                        27311
            else
              if m < 1328 then
                if m < 1320 then
                  if m < 1316 then
                    if m < 1314 then
                      if m < 1313 then
                        49808
                      else
                        31378
                    else
                      if m < 1315 then
                        50657
                      else
                        58006
                  else
                    if m < 1318 then
                      if m < 1317 then
                        49809
                      else
                        39571
                    else
                      if m < 1319 then
                        54761
                      else
                        60907
                else
                  if m < 1324 then
                    if m < 1322 then
                      if m < 1321 then
                        48612
                      else
                        48614
                    else
                      if m < 1323 then
                        52709
                      else
                        33462
                  else
                    if m < 1326 then
                      if m < 1325 then
                        42476
                      else
                        46574
                    else
                      if m < 1327 then
                        38381
                      else
                        54767
              else
                if m < 1336 then
                  if m < 1332 then
                    if m < 1330 then
                      if m < 1329 then
                        44528
                      else
                        47770
                    else
                      if m < 1331 then
                        49820
                      else
                        56819
                  else
                    if m < 1334 then
                      if m < 1333 then
                        45721
                      else
                        33435
                    else
                      if m < 1335 then
                        54777
                      else
                        27295
                else
                  if m < 1340 then
                    if m < 1338 then
                      if m < 1337 then
                        60088
                      else
                        54774
                    else
                      if m < 1339 then
                        46581
                      else
                        45758
                  else
                    if m < 1342 then
                      if m < 1341 then
                        37561
                      else
                        35515
                    else
                      if m < 1343 then
                        49853
                      else
                        35519
          else
            if m < 1376 then
              if m < 1360 then
                if m < 1352 then
                  if m < 1348 then
                    if m < 1346 then
                      if m < 1345 then
                        52096
                      else
                        37762
                    else
                      if m < 1347 then
                        56196
                      else
                        60803
                  else
                    if m < 1350 then
                      if m < 1349 then
                        44424
                      else
                        23946
                    else
                      if m < 1351 then
                        31621
                      else
                        25995
                else
                  if m < 1356 then
                    if m < 1354 then
                      if m < 1353 then
                        54660
                      else
                        46470
                    else
                      if m < 1355 then
                        58757
                      else
                        45990
                  else
                    if m < 1358 then
                      if m < 1357 then
                        45985
                      else
                        62371
                    else
                      if m < 1359 then
                        48037
                      else
                        52623
              else
                if m < 1368 then
                  if m < 1364 then
                    if m < 1362 then
                      if m < 1361 then
                        48008
                      else
                        39818
                    else
                      if m < 1363 then
                        39820
                      else
                        40339
                  else
                    if m < 1366 then
                      if m < 1365 then
                        41865
                      else
                        30106
                    else
                      if m < 1367 then
                        39821
                      else
                        42395
                else
                  if m < 1372 then
                    if m < 1370 then
                      if m < 1369 then
                        56724
                      else
                        40342
                    else
                      if m < 1371 then
                        60821
                      else
                        33710
                  else
                    if m < 1374 then
                      if m < 1373 then
                        48041
                      else
                        52638
                    else
                      if m < 1375 then
                        35757
                      else
                        39855
            else
              if m < 1392 then
                if m < 1384 then
                  if m < 1380 then
                    if m < 1378 then
                      if m < 1377 then
                        50624
                      else
                        41874
                    else
                      if m < 1379 then
                        46529
                      else
                        48022
                  else
                    if m < 1382 then
                      if m < 1381 then
                        54161
                      else
                        37779
                    else
                      if m < 1383 then
                        50069
                      else
                        46539
                else
                  if m < 1388 then
                    if m < 1386 then
                      if m < 1385 then
                        44484
                      else
                        42438
                    else
                      if m < 1387 then
                        48052
                      else
                        46535
                  else
                    if m < 1390 then
                      if m < 1389 then
                        38348
                      else
                        40398
                    else
                      if m < 1391 then
                        34253
                      else
                        40399
              else
                if m < 1400 then
                  if m < 1396 then
                    if m < 1394 then
                      if m < 1393 then
                        50640
                      else
                        41882
                    else
                      if m < 1395 then
                        35740
                      else
                        38355
                  else
                    if m < 1398 then
                      if m < 1397 then
                        60313
                      else
                        44506
                    else
                      if m < 1399 then
                        36313
                      else
                        40411
                else
                  if m < 1404 then
                    if m < 1402 then
                      if m < 1401 then
                        50104
                      else
                        40406
                    else
                      if m < 1403 then
                        48597
                      else
                        42455
                  else
                    if m < 1406 then
                      if m < 1405 then
                        54201
                      else
                        48059
                    else
                      if m < 1407 then
                        36317
                      else
                        37823
        else
          if m < 1472 then
            if m < 1440 then
              if m < 1424 then
                if m < 1416 then
                  if m < 1412 then
                    if m < 1410 then
                      if m < 1409 then
                        51904
                      else
                        58050
                    else
                      if m < 1411 then
                        40257
                      else
                        58054
                  else
                    if m < 1414 then
                      if m < 1413 then
                        51905
                      else
                        56003
                    else
                      if m < 1415 then
                        43717
                      else
                        48459
                else
                  if m < 1420 then
                    if m < 1418 then
                      if m < 1417 then
                        41696
                      else
                        34118
                    else
                      if m < 1419 then
                        21220
                      else
                        23270
                  else
                    if m < 1422 then
                      if m < 1421 then
                        48460
                      else
                        50510
                    else
                      if m < 1423 then
                        62181
                      else
                        49895
              else
                if m < 1432 then
                  if m < 1428 then
                    if m < 1426 then
                      if m < 1425 then
                        50512
                      else
                        42322
                    else
                      if m < 1427 then
                        42321
                      else
                        37582
                  else
                    if m < 1430 then
                      if m < 1429 then
                        53961
                      else
                        58059
                    else
                      if m < 1431 then
                        37581
                      else
                        36187
                else
                  if m < 1436 then
                    if m < 1434 then
                      if m < 1433 then
                        44372
                      else
                        42326
                    else
                      if m < 1435 then
                        27372
                      else
                        39662
                  else
                    if m < 1438 then
                      if m < 1437 then
                        50524
                      else
                        38238
                    else
                      if m < 1439 then
                        49901
                      else
                        42335
            else
              if m < 1456 then
                if m < 1448 then
                  if m < 1444 then
                    if m < 1442 then
                      if m < 1441 then
                        48384
                      else
                        49874
                    else
                      if m < 1443 then
                        43732
                      else
                        54531
                  else
                    if m < 1446 then
                      if m < 1445 then
                        41681
                      else
                        23818
                    else
                      if m < 1447 then
                        39637
                      else
                        41687
                else
                  if m < 1452 then
                    if m < 1450 then
                      if m < 1449 then
                        51952
                      else
                        54002
                    else
                      if m < 1451 then
                        23284
                      else
                        41718
                  else
                    if m < 1454 then
                      if m < 1453 then
                        43761
                      else
                        42254
                    else
                      if m < 1455 then
                        47861
                      else
                        46351
              else
                if m < 1464 then
                  if m < 1460 then
                    if m < 1458 then
                      if m < 1457 then
                        54544
                      else
                        40210
                    else
                      if m < 1459 then
                        38161
                      else
                        34067
                  else
                    if m < 1462 then
                      if m < 1461 then
                        39641
                      else
                        37595
                    else
                      if m < 1463 then
                        37597
                      else
                        31455
                else
                  if m < 1468 then
                    if m < 1466 then
                      if m < 1465 then
                        54548
                      else
                        45818
                    else
                      if m < 1467 then
                        32021
                      else
                        27927
                  else
                    if m < 1470 then
                      if m < 1469 then
                        49913
                      else
                        43771
                    else
                      if m < 1471 then
                        51965
                      else
                        29983
          else
            if m < 1504 then
              if m < 1488 then
                if m < 1480 then
                  if m < 1476 then
                    if m < 1474 then
                      if m < 1473 then
                        48064
                      else
                        43970
                    else
                      if m < 1475 then
                        44385
                      else
                        50531
                  else
                    if m < 1478 then
                      if m < 1477 then
                        41921
                      else
                        46019
                    else
                      if m < 1479 then
                        39877
                      else
                        43975
                else
                  if m < 1484 then
                    if m < 1482 then
                      if m < 1481 then
                        54240
                      else
                        50146
                    else
                      if m < 1483 then
                        40293
                      else
                        44006
                  else
                    if m < 1486 then
                      if m < 1485 then
                        35809
                      else
                        31715
                    else
                      if m < 1487 then
                        37861
                      else
                        37863
              else
                if m < 1496 then
                  if m < 1492 then
                    if m < 1490 then
                      if m < 1489 then
                        48072
                      else
                        38258
                    else
                      if m < 1491 then
                        44401
                      else
                        35790
                  else
                    if m < 1494 then
                      if m < 1493 then
                        52600
                      else
                        46027
                    else
                      if m < 1495 then
                        37837
                      else
                        39887
                else
                  if m < 1500 then
                    if m < 1498 then
                      if m < 1497 then
                        58344
                      else
                        33770
                    else
                      if m < 1499 then
                        41964
                      else
                        37870
                  else
                    if m < 1502 then
                      if m < 1501 then
                        56700
                      else
                        33771
                    else
                      if m < 1503 then
                        48109
                      else
                        40319
            else
              if m < 1520 then
                if m < 1512 then
                  if m < 1508 then
                    if m < 1506 then
                      if m < 1505 then
                        52512
                      else
                        48082
                    else
                      if m < 1507 then
                        34081
                      else
                        60707
                  else
                    if m < 1510 then
                      if m < 1509 then
                        46033
                      else
                        50131
                    else
                      if m < 1511 then
                        46037
                      else
                        36139
                else
                  if m < 1516 then
                    if m < 1514 then
                      if m < 1513 then
                        52516
                      else
                        52210
                    else
                      if m < 1515 then
                        42277
                      else
                        58358
                  else
                    if m < 1518 then
                      if m < 1517 then
                        39921
                      else
                        35827
                    else
                      if m < 1519 then
                        44021
                      else
                        52215
              else
                if m < 1528 then
                  if m < 1524 then
                    if m < 1522 then
                      if m < 1521 then
                        41944
                      else
                        48090
                    else
                      if m < 1523 then
                        50481
                      else
                        54238
                  else
                    if m < 1526 then
                      if m < 1525 then
                        62776
                      else
                        43995
                    else
                      if m < 1527 then
                        52189
                      else
                        48443
                else
                  if m < 1532 then
                    if m < 1530 then
                      if m < 1529 then
                        48436
                      else
                        52218
                    else
                      if m < 1531 then
                        36149
                      else
                        30007
                  else
                    if m < 1534 then
                      if m < 1533 then
                        40252
                      else
                        52542
                    else
                      if m < 1535 then
                        38205
                      else
                        38207
    else
      if m < 1792 then
        if m < 1664 then
          if m < 1600 then
            if m < 1568 then
              if m < 1552 then
                if m < 1544 then
                  if m < 1540 then
                    if m < 1538 then
                      if m < 1537 then
                        40608
                      else
                        42658
                    else
                      if m < 1539 then
                        52675
                      else
                        46529
                  else
                    if m < 1542 then
                      if m < 1541 then
                        36520
                      else
                        38570
                    else
                      if m < 1543 then
                        42665
                      else
                        44715
                else
                  if m < 1548 then
                    if m < 1546 then
                      if m < 1545 then
                        38375
                      else
                        46758
                    else
                      if m < 1547 then
                        59045
                      else
                        50657
                  else
                    if m < 1550 then
                      if m < 1549 then
                        42668
                      else
                        42670
                    else
                      if m < 1551 then
                        36322
                      else
                        54752
              else
                if m < 1560 then
                  if m < 1556 then
                    if m < 1554 then
                      if m < 1553 then
                        40399
                      else
                        34253
                    else
                      if m < 1555 then
                        42673
                      else
                        46771
                  else
                    if m < 1558 then
                      if m < 1557 then
                        34488
                      else
                        32442
                    else
                      if m < 1559 then
                        42442
                      else
                        50875
                else
                  if m < 1564 then
                    if m < 1562 then
                      if m < 1561 then
                        54964
                      else
                        32438
                    else
                      if m < 1563 then
                        54965
                      else
                        48823
                  else
                    if m < 1566 then
                      if m < 1565 then
                        46574
                      else
                        36542
                    else
                      if m < 1567 then
                        44522
                      else
                        54760
            else
              if m < 1584 then
                if m < 1576 then
                  if m < 1572 then
                    if m < 1570 then
                      if m < 1569 then
                        36576
                      else
                        48597
                    else
                      if m < 1571 then
                        32481
                      else
                        40401
                  else
                    if m < 1574 then
                      if m < 1573 then
                        40406
                      else
                        54740
                    else
                      if m < 1575 then
                        46546
                      else
                        44779
                else
                  if m < 1580 then
                    if m < 1578 then
                      if m < 1577 then
                        50679
                      else
                        46581
                    else
                      if m < 1579 then
                        50917
                      else
                        50673
                  else
                    if m < 1582 then
                      if m < 1581 then
                        48876
                      else
                        61166
                    else
                      if m < 1583 then
                        48877
                      else
                        44528
              else
                if m < 1592 then
                  if m < 1588 then
                    if m < 1586 then
                      if m < 1585 then
                        42463
                      else
                        36317
                    else
                      if m < 1587 then
                        34545
                      else
                        36313
                  else
                    if m < 1590 then
                      if m < 1589 then
                        46840
                      else
                        58844
                    else
                      if m < 1591 then
                        44506
                      else
                        59131
                else
                  if m < 1596 then
                    if m < 1594 then
                      if m < 1593 then
                        40447
                      else
                        54781
                    else
                      if m < 1595 then
                        32251
                      else
                        54777
                  else
                    if m < 1598 then
                      if m < 1597 then
                        40446
                      else
                        42492
                    else
                      if m < 1599 then
                        38394
                      else
                        48895
          else
            if m < 1632 then
              if m < 1616 then
                if m < 1608 then
                  if m < 1604 then
                    if m < 1602 then
                      if m < 1601 then
                        52864
                      else
                        52421
                    else
                      if m < 1603 then
                        52419
                      else
                        52417
                  else
                    if m < 1606 then
                      if m < 1605 then
                        36038
                      else
                        59018
                    else
                      if m < 1607 then
                        28297
                      else
                        52416
                else
                  if m < 1612 then
                    if m < 1610 then
                      if m < 1609 then
                        38119
                      else
                        44678
                    else
                      if m < 1611 then
                        46307
                      else
                        46305
                  else
                    if m < 1614 then
                      if m < 1613 then
                        44684
                      else
                        38116
                    else
                      if m < 1615 then
                        36066
                      else
                        48352
              else
                if m < 1624 then
                  if m < 1620 then
                    if m < 1618 then
                      if m < 1617 then
                        54928
                      else
                        28306
                    else
                      if m < 1619 then
                        44235
                      else
                        38547
                  else
                    if m < 1622 then
                      if m < 1621 then
                        44238
                      else
                        46746
                    else
                      if m < 1623 then
                        46745
                      else
                        56520
                else
                  if m < 1628 then
                    if m < 1626 then
                      if m < 1625 then
                        56559
                      else
                        26262
                    else
                      if m < 1627 then
                        50411
                      else
                        36073
                  else
                    if m < 1630 then
                      if m < 1629 then
                        52892
                      else
                        28318
                    else
                      if m < 1631 then
                        38122
                      else
                        46312
            else
              if m < 1648 then
                if m < 1640 then
                  if m < 1636 then
                    if m < 1634 then
                      if m < 1633 then
                        52928
                      else
                        58581
                    else
                      if m < 1635 then
                        31955
                      else
                        46289
                  else
                    if m < 1638 then
                      if m < 1637 then
                        34006
                      else
                        34004
                    else
                      if m < 1639 then
                        52937
                      else
                        52432
                else
                  if m < 1644 then
                    if m < 1642 then
                      if m < 1641 then
                        38135
                      else
                        48373
                    else
                      if m < 1643 then
                        44275
                      else
                        24263
                  else
                    if m < 1646 then
                      if m < 1645 then
                        46796
                      else
                        32462
                    else
                      if m < 1647 then
                        54989
                      else
                        34511
              else
                if m < 1656 then
                  if m < 1652 then
                    if m < 1650 then
                      if m < 1649 then
                        48848
                      else
                        54994
                    else
                      if m < 1651 then
                        40155
                      else
                        38611
                  else
                    if m < 1654 then
                      if m < 1653 then
                        48350
                      else
                        40156
                    else
                      if m < 1655 then
                        48346
                      else
                        44248
                else
                  if m < 1660 then
                    if m < 1658 then
                      if m < 1657 then
                        56575
                      else
                        54525
                    else
                      if m < 1659 then
                        62715
                      else
                        52951
                  else
                    if m < 1662 then
                      if m < 1661 then
                        57052
                      else
                        42236
                    else
                      if m < 1663 then
                        48861
                      else
                        30431
        else
          if m < 1728 then
            if m < 1696 then
              if m < 1680 then
                if m < 1672 then
                  if m < 1668 then
                    if m < 1666 then
                      if m < 1665 then
                        50567
                      else
                        54850
                    else
                      if m < 1667 then
                        54849
                      else
                        54851
                  else
                    if m < 1670 then
                      if m < 1669 then
                        40520
                      else
                        48714
                    else
                      if m < 1671 then
                        42370
                      else
                        48715
                else
                  if m < 1676 then
                    if m < 1674 then
                      if m < 1673 then
                        38468
                      else
                        26021
                    else
                      if m < 1675 then
                        56739
                      else
                        52641
                  else
                    if m < 1678 then
                      if m < 1677 then
                        42406
                      else
                        38478
                    else
                      if m < 1679 then
                        40525
                      else
                        50767
              else
                if m < 1688 then
                  if m < 1684 then
                    if m < 1682 then
                      if m < 1681 then
                        52623
                      else
                        46674
                    else
                      if m < 1683 then
                        25995
                      else
                        36233
                  else
                    if m < 1686 then
                      if m < 1685 then
                        58968
                      else
                        50572
                    else
                      if m < 1687 then
                        23946
                      else
                        38491
                else
                  if m < 1692 then
                    if m < 1690 then
                      if m < 1689 then
                        46676
                      else
                        44461
                    else
                      if m < 1691 then
                        44459
                      else
                        56745
                  else
                    if m < 1694 then
                      if m < 1693 then
                        50606
                      else
                        40542
                    else
                      if m < 1695 then
                        26026
                      else
                        48735
            else
              if m < 1712 then
                if m < 1704 then
                  if m < 1700 then
                    if m < 1698 then
                      if m < 1697 then
                        38295
                      else
                        54786
                    else
                      if m < 1699 then
                        40339
                      else
                        44433
                  else
                    if m < 1702 then
                      if m < 1701 then
                        40342
                      else
                        56724
                    else
                      if m < 1703 then
                        44434
                      else
                        52747
                else
                  if m < 1708 then
                    if m < 1706 then
                      if m < 1705 then
                        34231
                      else
                        40373
                    else
                      if m < 1707 then
                        36275
                      else
                        42417
                  else
                    if m < 1710 then
                      if m < 1709 then
                        40374
                      else
                        38414
                    else
                      if m < 1711 then
                        40370
                      else
                        56752
              else
                if m < 1720 then
                  if m < 1716 then
                    if m < 1714 then
                      if m < 1713 then
                        42512
                      else
                        40349
                    else
                      if m < 1715 then
                        36369
                      else
                        44441
                  else
                    if m < 1718 then
                      if m < 1717 then
                        52638
                      else
                        52636
                    else
                      if m < 1719 then
                        30106
                      else
                        46488
                else
                  if m < 1724 then
                    if m < 1722 then
                      if m < 1721 then
                        32191
                      else
                        44566
                    else
                      if m < 1723 then
                        30139
                      else
                        48569
                  else
                    if m < 1726 then
                      if m < 1725 then
                        48668
                      else
                        46622
                    else
                      if m < 1727 then
                        34234
                      else
                        56863
          else
            if m < 1760 then
              if m < 1744 then
                if m < 1736 then
                  if m < 1732 then
                    if m < 1730 then
                      if m < 1729 then
                        50311
                      else
                        34402
                    else
                      if m < 1731 then
                        60547
                      else
                        48739
                  else
                    if m < 1734 then
                      if m < 1733 then
                        40552
                      else
                        44164
                    else
                      if m < 1735 then
                        50793
                      else
                        21632
                else
                  if m < 1740 then
                    if m < 1738 then
                      if m < 1737 then
                        36452
                      else
                        50341
                    else
                      if m < 1739 then
                        36453
                      else
                        54887
                  else
                    if m < 1742 then
                      if m < 1741 then
                        44198
                      else
                        52388
                    else
                      if m < 1743 then
                        29858
                      else
                        31904
              else
                if m < 1752 then
                  if m < 1748 then
                    if m < 1746 then
                      if m < 1745 then
                        46223
                      else
                        42610
                    else
                      if m < 1747 then
                        52363
                      else
                        35977
                  else
                    if m < 1750 then
                      if m < 1749 then
                        59000
                      else
                        62604
                    else
                      if m < 1751 then
                        56953
                      else
                        50312
                else
                  if m < 1756 then
                    if m < 1754 then
                      if m < 1753 then
                        50804
                      else
                        50806
                    else
                      if m < 1755 then
                        42613
                      else
                        46711
                  else
                    if m < 1758 then
                      if m < 1757 then
                        54446
                      else
                        46252
                    else
                      if m < 1759 then
                        44669
                      else
                        27816
            else
              if m < 1776 then
                if m < 1768 then
                  if m < 1764 then
                    if m < 1762 then
                      if m < 1761 then
                        33943
                      else
                        29845
                    else
                      if m < 1763 then
                        50721
                      else
                        42531
                  else
                    if m < 1766 then
                      if m < 1765 then
                        52776
                      else
                        48276
                    else
                      if m < 1767 then
                        48681
                      else
                        52779
                else
                  if m < 1772 then
                    if m < 1770 then
                      if m < 1769 then
                        42532
                      else
                        48678
                    else
                      if m < 1771 then
                        52403
                      else
                        42161
                  else
                    if m < 1774 then
                      if m < 1773 then
                        46262
                      else
                        46260
                    else
                      if m < 1775 then
                        58546
                      else
                        46639
              else
                if m < 1784 then
                  if m < 1780 then
                    if m < 1778 then
                      if m < 1777 then
                        44191
                      else
                        31901
                    else
                      if m < 1779 then
                        38449
                      else
                        38451
                  else
                    if m < 1782 then
                      if m < 1781 then
                        42552
                      else
                        34362
                    else
                      if m < 1783 then
                        56889
                      else
                        56891
                else
                  if m < 1788 then
                    if m < 1786 then
                      if m < 1785 then
                        44223
                      else
                        44221
                    else
                      if m < 1787 then
                        60603
                      else
                        56505
                  else
                    if m < 1790 then
                      if m < 1789 then
                        42556
                      else
                        40124
                    else
                      if m < 1791 then
                        42170
                      else
                        46264
      else
        if m < 1920 then
          if m < 1856 then
            if m < 1824 then
              if m < 1808 then
                if m < 1800 then
                  if m < 1796 then
                    if m < 1794 then
                      if m < 1793 then
                        27975
                      else
                        25925
                    else
                      if m < 1795 then
                        56481
                      else
                        40257
                  else
                    if m < 1798 then
                      if m < 1797 then
                        27816
                      else
                        46404
                    else
                      if m < 1799 then
                        52393
                      else
                        48299
                else
                  if m < 1804 then
                    if m < 1802 then
                      if m < 1801 then
                        48487
                      else
                        40293
                    else
                      if m < 1803 then
                        50531
                      else
                        42151
                  else
                    if m < 1806 then
                      if m < 1805 then
                        46252
                      else
                        54446
                    else
                      if m < 1807 then
                        48482
                      else
                        52576
              else
                if m < 1816 then
                  if m < 1812 then
                    if m < 1810 then
                      if m < 1809 then
                        52400
                      else
                        58546
                    else
                      if m < 1811 then
                        42161
                      else
                        48457
                  else
                    if m < 1814 then
                      if m < 1813 then
                        46264
                      else
                        42170
                    else
                      if m < 1815 then
                        56505
                      else
                        56648
                else
                  if m < 1820 then
                    if m < 1818 then
                      if m < 1817 then
                        42351
                      else
                        42349
                    else
                      if m < 1819 then
                        48491
                      else
                        44393
                  else
                    if m < 1822 then
                      if m < 1821 then
                        36206
                      else
                        40300
                    else
                      if m < 1823 then
                        44221
                      else
                        44223
            else
              if m < 1840 then
                if m < 1832 then
                  if m < 1828 then
                    if m < 1826 then
                      if m < 1825 then
                        44375
                      else
                        32085
                    else
                      if m < 1827 then
                        42323
                      else
                        42321
                  else
                    if m < 1830 then
                      if m < 1829 then
                        42326
                      else
                        38122
                    else
                      if m < 1831 then
                        36073
                      else
                        50411
                else
                  if m < 1836 then
                    if m < 1834 then
                      if m < 1833 then
                        38116
                      else
                        46453
                    else
                      if m < 1835 then
                        40307
                      else
                        38119
                  else
                    if m < 1838 then
                      if m < 1837 then
                        34028
                      else
                        58606
                    else
                      if m < 1839 then
                        31981
                      else
                        52592
              else
                if m < 1848 then
                  if m < 1844 then
                    if m < 1842 then
                      if m < 1841 then
                        36080
                      else
                        54621
                    else
                      if m < 1843 then
                        29937
                      else
                        42329
                  else
                    if m < 1846 then
                      if m < 1845 then
                        36088
                      else
                        50524
                    else
                      if m < 1847 then
                        58617
                      else
                        58712
                else
                  if m < 1852 then
                    if m < 1850 then
                      if m < 1849 then
                        34036
                      else
                        50557
                    else
                      if m < 1851 then
                        44411
                      else
                        38135
                  else
                    if m < 1854 then
                      if m < 1853 then
                        38270
                      else
                        56700
                    else
                      if m < 1855 then
                        50554
                      else
                        52600
          else
            if m < 1888 then
              if m < 1872 then
                if m < 1864 then
                  if m < 1860 then
                    if m < 1858 then
                      if m < 1857 then
                        21632
                      else
                        54402
                    else
                      if m < 1859 then
                        52291
                      else
                        58433
                  else
                    if m < 1862 then
                      if m < 1861 then
                        46150
                      else
                        62602
                    else
                      if m < 1863 then
                        31810
                      else
                        50240
                else
                  if m < 1868 then
                    if m < 1866 then
                      if m < 1865 then
                        40039
                      else
                        46214
                    else
                      if m < 1867 then
                        31843
                      else
                        46177
                  else
                    if m < 1870 then
                      if m < 1869 then
                        58470
                      else
                        54372
                    else
                      if m < 1871 then
                        48269
                      else
                        46223
              else
                if m < 1880 then
                  if m < 1876 then
                    if m < 1874 then
                      if m < 1873 then
                        54416
                      else
                        54418
                    else
                      if m < 1875 then
                        42059
                      else
                        56467
                  else
                    if m < 1878 then
                      if m < 1877 then
                        54350
                      else
                        60492
                    else
                      if m < 1879 then
                        44185
                      else
                        44187
                else
                  if m < 1884 then
                    if m < 1882 then
                      if m < 1881 then
                        48276
                      else
                        52333
                    else
                      if m < 1883 then
                        25707
                      else
                        29801
                  else
                    if m < 1886 then
                      if m < 1885 then
                        31854
                      else
                        48286
                    else
                      if m < 1887 then
                        27754
                      else
                        44191
            else
              if m < 1904 then
                if m < 1896 then
                  if m < 1892 then
                    if m < 1890 then
                      if m < 1889 then
                        52416
                      else
                        29781
                    else
                      if m < 1891 then
                        48211
                      else
                        50257
                  else
                    if m < 1894 then
                      if m < 1893 then
                        52310
                      else
                        52426
                    else
                      if m < 1895 then
                        44233
                      else
                        40016
                else
                  if m < 1900 then
                    if m < 1898 then
                      if m < 1897 then
                        64708
                      else
                        31861
                    else
                      if m < 1899 then
                        48243
                      else
                        58567
                  else
                    if m < 1902 then
                      if m < 1901 then
                        46284
                      else
                        40052
                    else
                      if m < 1903 then
                        33997
                      else
                        54384
              else
                if m < 1912 then
                  if m < 1908 then
                    if m < 1906 then
                      if m < 1905 then
                        52432
                      else
                        52434
                    else
                      if m < 1907 then
                        42075
                      else
                        27737
                  else
                    if m < 1910 then
                      if m < 1909 then
                        40030
                      else
                        44124
                    else
                      if m < 1911 then
                        44249
                      else
                        35928
                else
                  if m < 1916 then
                    if m < 1914 then
                      if m < 1913 then
                        29823
                      else
                        29821
                    else
                      if m < 1915 then
                        54395
                      else
                        52345
                  else
                    if m < 1918 then
                      if m < 1917 then
                        35966
                      else
                        44156
                    else
                      if m < 1919 then
                        60637
                      else
                        44152
        else
          if m < 1984 then
            if m < 1952 then
              if m < 1936 then
                if m < 1928 then
                  if m < 1924 then
                    if m < 1922 then
                      if m < 1921 then
                        46343
                      else
                        27909
                    else
                      if m < 1923 then
                        54531
                      else
                        48385
                  else
                    if m < 1926 then
                      if m < 1925 then
                        50248
                      else
                        50250
                    else
                      if m < 1927 then
                        54530
                      else
                        42059
                else
                  if m < 1932 then
                    if m < 1930 then
                      if m < 1929 then
                        62759
                      else
                        42277
                    else
                      if m < 1931 then
                        60707
                      else
                        27719
                  else
                    if m < 1934 then
                      if m < 1933 then
                        56614
                      else
                        52516
                    else
                      if m < 1935 then
                        52514
                      else
                        52512
              else
                if m < 1944 then
                  if m < 1940 then
                    if m < 1938 then
                      if m < 1937 then
                        40016
                      else
                        50258
                    else
                      if m < 1939 then
                        46347
                      else
                        44297
                  else
                    if m < 1942 then
                      if m < 1941 then
                        35928
                      else
                        48396
                    else
                      if m < 1943 then
                        23818
                      else
                        42075
                else
                  if m < 1948 then
                    if m < 1946 then
                      if m < 1945 then
                        56623
                      else
                        48429
                    else
                      if m < 1947 then
                        29781
                      else
                        50473
                  else
                    if m < 1950 then
                      if m < 1949 then
                        40238
                      else
                        40030
                    else
                      if m < 1951 then
                        54570
                      else
                        50472
            else
              if m < 1968 then
                if m < 1960 then
                  if m < 1956 then
                    if m < 1954 then
                      if m < 1953 then
                        21504
                      else
                        25602
                    else
                      if m < 1955 then
                        27649
                      else
                        38161
                  else
                    if m < 1958 then
                      if m < 1957 then
                        50184
                      else
                        54282
                    else
                      if m < 1959 then
                        40210
                      else
                        54544
                else
                  if m < 1964 then
                    if m < 1962 then
                      if m < 1961 then
                        23556
                      else
                        36149
                    else
                      if m < 1963 then
                        52229
                      else
                        50481
                  else
                    if m < 1966 then
                      if m < 1965 then
                        56630
                      else
                        48436
                    else
                      if m < 1967 then
                        46093
                      else
                        46384
              else
                if m < 1976 then
                  if m < 1972 then
                    if m < 1970 then
                      if m < 1969 then
                        23568
                      else
                        56605
                    else
                      if m < 1971 then
                        36123
                      else
                        42265
                  else
                    if m < 1974 then
                      if m < 1973 then
                        48152
                      else
                        54556
                    else
                      if m < 1975 then
                        42266
                      else
                        44312
                else
                  if m < 1980 then
                    if m < 1978 then
                      if m < 1977 then
                        31764
                      else
                        31766
                    else
                      if m < 1979 then
                        48149
                      else
                        56633
                  else
                    if m < 1982 then
                      if m < 1981 then
                        52542
                      else
                        33822
                    else
                      if m < 1983 then
                        48442
                      else
                        56351
          else
            if m < 2016 then
              if m < 2000 then
                if m < 1992 then
                  if m < 1988 then
                    if m < 1986 then
                      if m < 1985 then
                        52320
                      else
                        52229
                    else
                      if m < 1987 then
                        41987
                      else
                        27649
                  else
                    if m < 1990 then
                      if m < 1989 then
                        39942
                      else
                        23556
                    else
                      if m < 1991 then
                        25602
                      else
                        21504
                else
                  if m < 1996 then
                    if m < 1994 then
                      if m < 1993 then
                        50215
                      else
                        54309
                    else
                      if m < 1995 then
                        44067
                      else
                        40039
                  else
                    if m < 1998 then
                      if m < 1997 then
                        54310
                      else
                        31854
                    else
                      if m < 1999 then
                        52333
                      else
                        54383
              else
                if m < 2008 then
                  if m < 2004 then
                    if m < 2002 then
                      if m < 2001 then
                        50191
                      else
                        40050
                    else
                      if m < 2003 then
                        58379
                      else
                        44041
                  else
                    if m < 2006 then
                      if m < 2005 then
                        44152
                      else
                        56332
                    else
                      if m < 2007 then
                        52345
                      else
                        50184
                else
                  if m < 2012 then
                    if m < 2010 then
                      if m < 2009 then
                        40052
                      else
                        52342
                    else
                      if m < 2011 then
                        27691
                      else
                        64553
                  else
                    if m < 2014 then
                      if m < 2013 then
                        39982
                      else
                        31788
                    else
                      if m < 2015 then
                        25642
                      else
                        25640
            else
              if m < 2032 then
                if m < 2024 then
                  if m < 2020 then
                    if m < 2018 then
                      if m < 2017 then
                        60439
                      else
                        48149
                    else
                      if m < 2019 then
                        46099
                      else
                        39953
                  else
                    if m < 2022 then
                      if m < 2021 then
                        25640
                      else
                        25642
                    else
                      if m < 2023 then
                        60434
                      else
                        23568
                else
                  if m < 2028 then
                    if m < 2026 then
                      if m < 2025 then
                        37924
                      else
                        50229
                    else
                      if m < 2027 then
                        50227
                      else
                        50215
                  else
                    if m < 2030 then
                      if m < 2029 then
                        31788
                      else
                        35892
                    else
                      if m < 2031 then
                        54317
                      else
                        46127
              else
                if m < 2040 then
                  if m < 2036 then
                    if m < 2034 then
                      if m < 2033 then
                        50224
                      else
                        52253
                    else
                      if m < 2035 then
                        48155
                      else
                        46105
                  else
                    if m < 2038 then
                      if m < 2037 then
                        27704
                      else
                        50234
                    else
                      if m < 2039 then
                        50233
                      else
                        48152
                else
                  if m < 2044 then
                    if m < 2042 then
                      if m < 2041 then
                        31807
                      else
                        37942
                    else
                      if m < 2043 then
                        50229
                      else
                        44087
                  else
                    if m < 2046 then
                      if m < 2045 then
                        48188
                      else
                        48188
                    else
                      if m < 2047 then
                        44093
                      else
                        27704

def parent (m : Fin 2048) : Fin 2048 := ⟨(tree m.val) % 2048, Nat.mod_lt _ (by decide)⟩
def depth (m : Fin 2048) : ℕ := (tree m.val) / 2048

def Valid (m : Fin 2048) : Prop :=
    m = 0 ∨ m = 1 ∨ m = 3 ∨
      (depth (parent m) < depth m ∧
        (maskImage xMasks (parent m).val = m.val ∨
         maskImage yMasks (parent m).val = m.val))

instance (m : Fin 2048) : Decidable (Valid m) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

set_option maxRecDepth 10000 in
private theorem block0 : ∀ i : Fin 64, Valid ⟨0 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block1 : ∀ i : Fin 64, Valid ⟨64 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block2 : ∀ i : Fin 64, Valid ⟨128 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block3 : ∀ i : Fin 64, Valid ⟨192 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block4 : ∀ i : Fin 64, Valid ⟨256 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block5 : ∀ i : Fin 64, Valid ⟨320 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block6 : ∀ i : Fin 64, Valid ⟨384 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block7 : ∀ i : Fin 64, Valid ⟨448 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block8 : ∀ i : Fin 64, Valid ⟨512 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block9 : ∀ i : Fin 64, Valid ⟨576 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block10 : ∀ i : Fin 64, Valid ⟨640 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block11 : ∀ i : Fin 64, Valid ⟨704 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block12 : ∀ i : Fin 64, Valid ⟨768 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block13 : ∀ i : Fin 64, Valid ⟨832 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block14 : ∀ i : Fin 64, Valid ⟨896 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block15 : ∀ i : Fin 64, Valid ⟨960 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block16 : ∀ i : Fin 64, Valid ⟨1024 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block17 : ∀ i : Fin 64, Valid ⟨1088 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block18 : ∀ i : Fin 64, Valid ⟨1152 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block19 : ∀ i : Fin 64, Valid ⟨1216 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block20 : ∀ i : Fin 64, Valid ⟨1280 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block21 : ∀ i : Fin 64, Valid ⟨1344 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block22 : ∀ i : Fin 64, Valid ⟨1408 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block23 : ∀ i : Fin 64, Valid ⟨1472 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block24 : ∀ i : Fin 64, Valid ⟨1536 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block25 : ∀ i : Fin 64, Valid ⟨1600 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block26 : ∀ i : Fin 64, Valid ⟨1664 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block27 : ∀ i : Fin 64, Valid ⟨1728 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block28 : ∀ i : Fin 64, Valid ⟨1792 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block29 : ∀ i : Fin 64, Valid ⟨1856 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block30 : ∀ i : Fin 64, Valid ⟨1920 + i.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem block31 : ∀ i : Fin 64, Valid ⟨1984 + i.val, by omega⟩ := by
  decide +kernel

theorem tree_certificate (m : Fin 2048) : Valid m := by
  have hb : m.val / 64 < 32 := by omega
  have hi : m.val % 64 < 64 := Nat.mod_lt _ (by decide)
  have h : ∀ b : Fin 32, ∀ i : Fin 64, Valid ⟨64 * b.val + i.val, by omega⟩ := by
    intro b
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
  convert h ⟨m.val / 64, hb⟩ ⟨m.val % 64, hi⟩ using 1
  apply Fin.ext
  exact (Nat.div_add_mod m.val 64).symm

end Janko4.Simplicity.Max1Fusion.KernelOrbits
