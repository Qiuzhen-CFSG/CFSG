module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.Word

/-!
# Finite witnesses for the third Fi23 prefix step

There are 693 candidate representatives, stored as words of length at most six
in the exact six second-stage generators. The positive transition tables have
explicit inverse tables. Each Schreier factor is a signed word in seven packed
candidate generators. The table contents alone assert no group identities:
`Representatives` certifies the base images and inverse tables; the remaining
permutation identities are the separate `Step` obligations in `Reduction`.

Source: ATLAS F23G1-p31671B0; GLS3 Table 5.3u. Reproduce with `source/Generate.g`
and `source/Encode.py`. The scripts are witness search, never trusted proofs.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.KernelUpperThird

def representativeCode (b : Nat) : Nat × Nat :=
  if b < 346 then
    if b < 173 then
      if b < 86 then
        if b < 43 then
          if b < 21 then
            if b < 10 then
              if b < 5 then
                if b < 2 then
                  if b < 1 then
                    (0, 0)
                  else
                    (1, 0)
                else
                  if b < 3 then
                    (1, 1)
                  else
                    if b < 4 then
                      (1, 3)
                    else
                      (1, 5)
              else
                if b < 7 then
                  if b < 6 then
                    (2, 0)
                  else
                    (2, 1)
                else
                  if b < 8 then
                    (2, 3)
                  else
                    if b < 9 then
                      (2, 4)
                    else
                      (2, 5)
            else
              if b < 15 then
                if b < 12 then
                  if b < 11 then
                    (2, 16)
                  else
                    (2, 17)
                else
                  if b < 13 then
                    (2, 19)
                  else
                    if b < 14 then
                      (2, 21)
                    else
                      (2, 48)
              else
                if b < 18 then
                  if b < 16 then
                    (2, 49)
                  else
                    if b < 17 then
                      (2, 51)
                    else
                      (2, 52)
                else
                  if b < 19 then
                    (2, 53)
                  else
                    if b < 20 then
                      (2, 80)
                    else
                      (2, 81)
          else
            if b < 32 then
              if b < 26 then
                if b < 23 then
                  if b < 22 then
                    (2, 83)
                  else
                    (2, 84)
                else
                  if b < 24 then
                    (2, 85)
                  else
                    if b < 25 then
                      (3, 0)
                    else
                      (3, 3)
              else
                if b < 29 then
                  if b < 27 then
                    (3, 4)
                  else
                    if b < 28 then
                      (3, 5)
                    else
                      (3, 16)
                else
                  if b < 30 then
                    (3, 20)
                  else
                    if b < 31 then
                      (3, 21)
                    else
                      (3, 48)
            else
              if b < 37 then
                if b < 34 then
                  if b < 33 then
                    (3, 52)
                  else
                    (3, 53)
                else
                  if b < 35 then
                    (3, 64)
                  else
                    if b < 36 then
                      (3, 65)
                    else
                      (3, 67)
              else
                if b < 40 then
                  if b < 38 then
                    (3, 68)
                  else
                    if b < 39 then
                      (3, 80)
                    else
                      (3, 81)
                else
                  if b < 41 then
                    (3, 82)
                  else
                    if b < 42 then
                      (3, 83)
                    else
                      (3, 84)
        else
          if b < 64 then
            if b < 53 then
              if b < 48 then
                if b < 45 then
                  if b < 44 then
                    (3, 261)
                  else
                    (3, 273)
                else
                  if b < 46 then
                    (3, 276)
                  else
                    if b < 47 then
                      (3, 277)
                    else
                      (3, 304)
              else
                if b < 50 then
                  if b < 49 then
                    (3, 305)
                  else
                    (3, 308)
                else
                  if b < 51 then
                    (3, 309)
                  else
                    if b < 52 then
                      (3, 336)
                    else
                      (3, 337)
            else
              if b < 58 then
                if b < 55 then
                  if b < 54 then
                    (3, 338)
                  else
                    (3, 339)
                else
                  if b < 56 then
                    (3, 340)
                  else
                    if b < 57 then
                      (3, 341)
                    else
                      (3, 773)
              else
                if b < 61 then
                  if b < 59 then
                    (3, 788)
                  else
                    if b < 60 then
                      (3, 789)
                    else
                      (3, 821)
                else
                  if b < 62 then
                    (3, 832)
                  else
                    if b < 63 then
                      (3, 833)
                    else
                      (3, 835)
          else
            if b < 75 then
              if b < 69 then
                if b < 66 then
                  if b < 65 then
                    (3, 836)
                  else
                    (3, 837)
                else
                  if b < 67 then
                    (3, 849)
                  else
                    if b < 68 then
                      (3, 851)
                    else
                      (3, 852)
              else
                if b < 72 then
                  if b < 70 then
                    (3, 853)
                  else
                    if b < 71 then
                      (3, 1280)
                    else
                      (3, 1281)
                else
                  if b < 73 then
                    (3, 1282)
                  else
                    if b < 74 then
                      (3, 1283)
                    else
                      (3, 1296)
            else
              if b < 80 then
                if b < 77 then
                  if b < 76 then
                    (3, 1297)
                  else
                    (3, 1298)
                else
                  if b < 78 then
                    (3, 1299)
                  else
                    if b < 79 then
                      (3, 1300)
                    else
                      (3, 1301)
              else
                if b < 83 then
                  if b < 81 then
                    (3, 1328)
                  else
                    if b < 82 then
                      (3, 1329)
                    else
                      (3, 1330)
                else
                  if b < 84 then
                    (3, 1331)
                  else
                    if b < 85 then
                      (3, 1332)
                    else
                      (3, 1333)
      else
        if b < 129 then
          if b < 107 then
            if b < 96 then
              if b < 91 then
                if b < 88 then
                  if b < 87 then
                    (3, 1344)
                  else
                    (3, 1345)
                else
                  if b < 89 then
                    (3, 1348)
                  else
                    if b < 90 then
                      (3, 1349)
                    else
                      (3, 1360)
              else
                if b < 93 then
                  if b < 92 then
                    (3, 1361)
                  else
                    (3, 1362)
                else
                  if b < 94 then
                    (3, 1363)
                  else
                    if b < 95 then
                      (3, 1364)
                    else
                      (3, 1365)
            else
              if b < 101 then
                if b < 98 then
                  if b < 97 then
                    (4, 3)
                  else
                    (4, 4)
                else
                  if b < 99 then
                    (4, 5)
                  else
                    if b < 100 then
                      (4, 52)
                    else
                      (4, 53)
              else
                if b < 104 then
                  if b < 102 then
                    (4, 64)
                  else
                    if b < 103 then
                      (4, 65)
                    else
                      (4, 67)
                else
                  if b < 105 then
                    (4, 68)
                  else
                    if b < 106 then
                      (4, 69)
                    else
                      (4, 80)
          else
            if b < 118 then
              if b < 112 then
                if b < 109 then
                  if b < 108 then
                    (4, 81)
                  else
                    (4, 83)
                else
                  if b < 110 then
                    (4, 84)
                  else
                    if b < 111 then
                      (4, 85)
                    else
                      (4, 260)
              else
                if b < 115 then
                  if b < 113 then
                    (4, 261)
                  else
                    if b < 114 then
                      (4, 320)
                    else
                      (4, 321)
                else
                  if b < 116 then
                    (4, 323)
                  else
                    if b < 117 then
                      (4, 324)
                    else
                      (4, 325)
            else
              if b < 123 then
                if b < 120 then
                  if b < 119 then
                    (4, 336)
                  else
                    (4, 337)
                else
                  if b < 121 then
                    (4, 338)
                  else
                    if b < 122 then
                      (4, 339)
                    else
                      (4, 340)
              else
                if b < 126 then
                  if b < 124 then
                    (4, 773)
                  else
                    if b < 125 then
                      (4, 835)
                    else
                      (4, 836)
                else
                  if b < 127 then
                    (4, 837)
                  else
                    if b < 128 then
                      (4, 849)
                    else
                      (4, 850)
        else
          if b < 151 then
            if b < 140 then
              if b < 134 then
                if b < 131 then
                  if b < 130 then
                    (4, 851)
                  else
                    (4, 852)
                else
                  if b < 132 then
                    (4, 853)
                  else
                    if b < 133 then
                      (4, 1029)
                    else
                      (4, 1040)
              else
                if b < 137 then
                  if b < 135 then
                    (4, 1043)
                  else
                    if b < 136 then
                      (4, 1045)
                    else
                      (4, 1072)
                else
                  if b < 138 then
                    (4, 1073)
                  else
                    if b < 139 then
                      (4, 1074)
                    else
                      (4, 1075)
            else
              if b < 145 then
                if b < 142 then
                  if b < 141 then
                    (4, 1077)
                  else
                    (4, 1088)
                else
                  if b < 143 then
                    (4, 1091)
                  else
                    if b < 144 then
                      (4, 1093)
                    else
                      (4, 1281)
              else
                if b < 148 then
                  if b < 146 then
                    (4, 1282)
                  else
                    if b < 147 then
                      (4, 1283)
                    else
                      (4, 1284)
                else
                  if b < 149 then
                    (4, 1285)
                  else
                    if b < 150 then
                      (4, 1299)
                    else
                      (4, 1300)
          else
            if b < 162 then
              if b < 156 then
                if b < 153 then
                  if b < 152 then
                    (4, 1301)
                  else
                    (4, 1312)
                else
                  if b < 154 then
                    (4, 1313)
                  else
                    if b < 155 then
                      (4, 1315)
                    else
                      (4, 1316)
              else
                if b < 159 then
                  if b < 157 then
                    (4, 1317)
                  else
                    if b < 158 then
                      (4, 1328)
                    else
                      (4, 1329)
                else
                  if b < 160 then
                    (4, 1330)
                  else
                    if b < 161 then
                      (4, 1331)
                    else
                      (4, 1332)
            else
              if b < 167 then
                if b < 164 then
                  if b < 163 then
                    (4, 1333)
                  else
                    (4, 1347)
                else
                  if b < 165 then
                    (4, 1348)
                  else
                    if b < 166 then
                      (4, 4176)
                    else
                      (4, 4177)
              else
                if b < 170 then
                  if b < 168 then
                    (4, 4178)
                  else
                    if b < 169 then
                      (4, 4179)
                    else
                      (4, 4180)
                else
                  if b < 171 then
                    (4, 4181)
                  else
                    if b < 172 then
                      (4, 4372)
                    else
                      (4, 4373)
    else
      if b < 259 then
        if b < 216 then
          if b < 194 then
            if b < 183 then
              if b < 178 then
                if b < 175 then
                  if b < 174 then
                    (4, 4416)
                  else
                    (4, 4417)
                else
                  if b < 176 then
                    (4, 4419)
                  else
                    if b < 177 then
                      (4, 4421)
                    else
                      (4, 4432)
              else
                if b < 180 then
                  if b < 179 then
                    (4, 4433)
                  else
                    (4, 4434)
                else
                  if b < 181 then
                    (4, 4435)
                  else
                    if b < 182 then
                      (4, 4436)
                    else
                      (4, 4437)
            else
              if b < 188 then
                if b < 185 then
                  if b < 184 then
                    (4, 4869)
                  else
                    (4, 4885)
                else
                  if b < 186 then
                    (4, 4929)
                  else
                    if b < 187 then
                      (4, 4931)
                    else
                      (4, 4933)
              else
                if b < 191 then
                  if b < 189 then
                    (4, 4944)
                  else
                    if b < 190 then
                      (4, 4945)
                    else
                      (4, 4946)
                else
                  if b < 192 then
                    (4, 4948)
                  else
                    if b < 193 then
                      (4, 4949)
                    else
                      (4, 5377)
          else
            if b < 205 then
              if b < 199 then
                if b < 196 then
                  if b < 195 then
                    (4, 5379)
                  else
                    (4, 5380)
                else
                  if b < 197 then
                    (4, 5381)
                  else
                    if b < 198 then
                      (4, 5393)
                    else
                      (4, 5395)
              else
                if b < 202 then
                  if b < 200 then
                    (4, 5396)
                  else
                    if b < 201 then
                      (4, 5397)
                    else
                      (4, 5409)
                else
                  if b < 203 then
                    (4, 5411)
                  else
                    if b < 204 then
                      (4, 5412)
                    else
                      (4, 5413)
            else
              if b < 210 then
                if b < 207 then
                  if b < 206 then
                    (4, 5425)
                  else
                    (4, 5426)
                else
                  if b < 208 then
                    (4, 5427)
                  else
                    if b < 209 then
                      (4, 5428)
                    else
                      (4, 5429)
              else
                if b < 213 then
                  if b < 211 then
                    (4, 5440)
                  else
                    if b < 212 then
                      (4, 5441)
                    else
                      (4, 5444)
                else
                  if b < 214 then
                    (4, 5445)
                  else
                    if b < 215 then
                      (4, 5456)
                    else
                      (4, 5457)
        else
          if b < 237 then
            if b < 226 then
              if b < 221 then
                if b < 218 then
                  if b < 217 then
                    (4, 5458)
                  else
                    (4, 5459)
                else
                  if b < 219 then
                    (4, 5460)
                  else
                    if b < 220 then
                      (4, 5461)
                    else
                      (4, 12368)
              else
                if b < 223 then
                  if b < 222 then
                    (4, 12369)
                  else
                    (4, 12370)
                else
                  if b < 224 then
                    (4, 12371)
                  else
                    if b < 225 then
                      (4, 12372)
                    else
                      (4, 12608)
            else
              if b < 231 then
                if b < 228 then
                  if b < 227 then
                    (4, 12609)
                  else
                    (4, 12611)
                else
                  if b < 229 then
                    (4, 12612)
                  else
                    if b < 230 then
                      (4, 12613)
                    else
                      (4, 12624)
              else
                if b < 234 then
                  if b < 232 then
                    (4, 12625)
                  else
                    if b < 233 then
                      (4, 12627)
                    else
                      (4, 12628)
                else
                  if b < 235 then
                    (4, 12629)
                  else
                    if b < 236 then
                      (4, 13136)
                    else
                      (4, 13137)
          else
            if b < 248 then
              if b < 242 then
                if b < 239 then
                  if b < 238 then
                    (4, 13138)
                  else
                    (4, 13140)
                else
                  if b < 240 then
                    (4, 13141)
                  else
                    if b < 241 then
                      (4, 13312)
                    else
                      (4, 13315)
              else
                if b < 245 then
                  if b < 243 then
                    (4, 13316)
                  else
                    if b < 244 then
                      (4, 13317)
                    else
                      (4, 13328)
                else
                  if b < 246 then
                    (4, 13333)
                  else
                    if b < 247 then
                      (4, 13360)
                    else
                      (4, 13361)
            else
              if b < 253 then
                if b < 250 then
                  if b < 249 then
                    (4, 13365)
                  else
                    (4, 13377)
                else
                  if b < 251 then
                    (4, 13378)
                  else
                    if b < 252 then
                      (4, 13379)
                    else
                      (4, 13380)
              else
                if b < 256 then
                  if b < 254 then
                    (4, 13381)
                  else
                    if b < 255 then
                      (4, 13392)
                    else
                      (4, 13393)
                else
                  if b < 257 then
                    (4, 13394)
                  else
                    if b < 258 then
                      (4, 13395)
                    else
                      (4, 13585)
      else
        if b < 302 then
          if b < 280 then
            if b < 269 then
              if b < 264 then
                if b < 261 then
                  if b < 260 then
                    (4, 13586)
                  else
                    (4, 13620)
                else
                  if b < 262 then
                    (4, 13621)
                  else
                    if b < 263 then
                      (4, 13632)
                    else
                      (4, 13633)
              else
                if b < 266 then
                  if b < 265 then
                    (4, 13636)
                  else
                    (4, 13637)
                else
                  if b < 267 then
                    (4, 13648)
                  else
                    if b < 268 then
                      (4, 13649)
                    else
                      (4, 13650)
            else
              if b < 274 then
                if b < 271 then
                  if b < 270 then
                    (4, 13652)
                  else
                    (4, 13653)
                else
                  if b < 272 then
                    (4, 20480)
                  else
                    if b < 273 then
                      (4, 20482)
                    else
                      (4, 20483)
              else
                if b < 277 then
                  if b < 275 then
                    (4, 20484)
                  else
                    if b < 276 then
                      (4, 20485)
                    else
                      (4, 20496)
                else
                  if b < 278 then
                    (4, 20497)
                  else
                    if b < 279 then
                      (4, 20498)
                    else
                      (4, 20500)
          else
            if b < 291 then
              if b < 285 then
                if b < 282 then
                  if b < 281 then
                    (4, 20501)
                  else
                    (4, 20513)
                else
                  if b < 283 then
                    (4, 20515)
                  else
                    if b < 284 then
                      (4, 20517)
                    else
                      (4, 20528)
              else
                if b < 288 then
                  if b < 286 then
                    (4, 20529)
                  else
                    if b < 287 then
                      (4, 20530)
                    else
                      (4, 20738)
                else
                  if b < 289 then
                    (4, 20741)
                  else
                    if b < 290 then
                      (4, 20752)
                    else
                      (4, 20753)
            else
              if b < 296 then
                if b < 293 then
                  if b < 292 then
                    (4, 20757)
                  else
                    (4, 20768)
                else
                  if b < 294 then
                    (4, 20771)
                  else
                    if b < 295 then
                      (4, 20773)
                    else
                      (4, 20784)
              else
                if b < 299 then
                  if b < 297 then
                    (4, 20785)
                  else
                    if b < 298 then
                      (4, 20786)
                    else
                      (4, 20787)
                else
                  if b < 300 then
                    (4, 20788)
                  else
                    if b < 301 then
                      (4, 20789)
                    else
                      (4, 20800)
        else
          if b < 324 then
            if b < 313 then
              if b < 307 then
                if b < 304 then
                  if b < 303 then
                    (4, 20802)
                  else
                    (4, 20803)
                else
                  if b < 305 then
                    (4, 20804)
                  else
                    if b < 306 then
                      (4, 20819)
                    else
                      (4, 21249)
              else
                if b < 310 then
                  if b < 308 then
                    (4, 21250)
                  else
                    if b < 309 then
                      (4, 21251)
                    else
                      (4, 21252)
                else
                  if b < 311 then
                    (4, 21253)
                  else
                    if b < 312 then
                      (4, 21264)
                    else
                      (4, 21267)
            else
              if b < 318 then
                if b < 315 then
                  if b < 314 then
                    (4, 21269)
                  else
                    (4, 21283)
                else
                  if b < 316 then
                    (4, 21284)
                  else
                    if b < 317 then
                      (4, 21297)
                    else
                      (4, 21299)
              else
                if b < 321 then
                  if b < 319 then
                    (4, 21300)
                  else
                    if b < 320 then
                      (4, 21301)
                    else
                      (4, 21313)
                else
                  if b < 322 then
                    (4, 21316)
                  else
                    if b < 323 then
                      (4, 21317)
                    else
                      (4, 21328)
          else
            if b < 335 then
              if b < 329 then
                if b < 326 then
                  if b < 325 then
                    (4, 21331)
                  else
                    (4, 21332)
                else
                  if b < 327 then
                    (4, 21504)
                  else
                    if b < 328 then
                      (4, 21505)
                    else
                      (4, 21506)
              else
                if b < 332 then
                  if b < 330 then
                    (4, 21520)
                  else
                    if b < 331 then
                      (4, 21521)
                    else
                      (4, 21522)
                else
                  if b < 333 then
                    (4, 21523)
                  else
                    if b < 334 then
                      (4, 21524)
                    else
                      (4, 21571)
            else
              if b < 340 then
                if b < 337 then
                  if b < 336 then
                    (4, 21572)
                  else
                    (4, 21584)
                else
                  if b < 338 then
                    (4, 21585)
                  else
                    if b < 339 then
                      (4, 21586)
                    else
                      (4, 21587)
              else
                if b < 343 then
                  if b < 341 then
                    (4, 21588)
                  else
                    if b < 342 then
                      (4, 21762)
                    else
                      (4, 21763)
                else
                  if b < 344 then
                    (4, 21765)
                  else
                    if b < 345 then
                      (4, 21777)
                    else
                      (4, 21778)
  else
    if b < 519 then
      if b < 432 then
        if b < 389 then
          if b < 367 then
            if b < 356 then
              if b < 351 then
                if b < 348 then
                  if b < 347 then
                    (4, 21779)
                  else
                    (4, 21780)
                else
                  if b < 349 then
                    (4, 21781)
                  else
                    if b < 350 then
                      (4, 21796)
                    else
                      (4, 21808)
              else
                if b < 353 then
                  if b < 352 then
                    (4, 21810)
                  else
                    (4, 21812)
                else
                  if b < 354 then
                    (4, 21824)
                  else
                    if b < 355 then
                      (4, 21825)
                    else
                      (4, 21827)
            else
              if b < 361 then
                if b < 358 then
                  if b < 357 then
                    (4, 21828)
                  else
                    (4, 21829)
                else
                  if b < 359 then
                    (4, 21841)
                  else
                    if b < 360 then
                      (4, 21842)
                    else
                      (4, 21843)
              else
                if b < 364 then
                  if b < 362 then
                    (5, 53)
                  else
                    if b < 363 then
                      (5, 64)
                    else
                      (5, 69)
                else
                  if b < 365 then
                    (5, 80)
                  else
                    if b < 366 then
                      (5, 84)
                    else
                      (5, 832)
          else
            if b < 378 then
              if b < 372 then
                if b < 369 then
                  if b < 368 then
                    (5, 833)
                  else
                    (5, 835)
                else
                  if b < 370 then
                    (5, 837)
                  else
                    if b < 371 then
                      (5, 849)
                    else
                      (5, 850)
              else
                if b < 375 then
                  if b < 373 then
                    (5, 851)
                  else
                    if b < 374 then
                      (5, 852)
                    else
                      (5, 853)
                else
                  if b < 376 then
                    (5, 1024)
                  else
                    if b < 377 then
                      (5, 1028)
                    else
                      (5, 1043)
            else
              if b < 383 then
                if b < 380 then
                  if b < 379 then
                    (5, 1073)
                  else
                    (5, 1092)
                else
                  if b < 381 then
                    (5, 1093)
                  else
                    if b < 382 then
                      (5, 1104)
                    else
                      (5, 1106)
              else
                if b < 386 then
                  if b < 384 then
                    (5, 1280)
                  else
                    if b < 385 then
                      (5, 1283)
                    else
                      (5, 1284)
                else
                  if b < 387 then
                    (5, 1297)
                  else
                    if b < 388 then
                      (5, 1298)
                    else
                      (5, 1300)
        else
          if b < 410 then
            if b < 399 then
              if b < 394 then
                if b < 391 then
                  if b < 390 then
                    (5, 1328)
                  else
                    (5, 1332)
                else
                  if b < 392 then
                    (5, 1333)
                  else
                    if b < 393 then
                      (5, 1345)
                    else
                      (5, 1346)
              else
                if b < 396 then
                  if b < 395 then
                    (5, 1347)
                  else
                    (5, 1348)
                else
                  if b < 397 then
                    (5, 1349)
                  else
                    if b < 398 then
                      (5, 1361)
                    else
                      (5, 1363)
            else
              if b < 404 then
                if b < 401 then
                  if b < 400 then
                    (5, 4163)
                  else
                    (5, 4178)
                else
                  if b < 402 then
                    (5, 4179)
                  else
                    if b < 403 then
                      (5, 4180)
                    else
                      (5, 5121)
              else
                if b < 407 then
                  if b < 405 then
                    (5, 5125)
                  else
                    if b < 406 then
                      (5, 5141)
                    else
                      (5, 5173)
                else
                  if b < 408 then
                    (5, 5189)
                  else
                    if b < 409 then
                      (5, 5203)
                    else
                      (5, 5204)
          else
            if b < 421 then
              if b < 415 then
                if b < 412 then
                  if b < 411 then
                    (5, 5205)
                  else
                    (5, 5381)
                else
                  if b < 413 then
                    (5, 5393)
                  else
                    if b < 414 then
                      (5, 5394)
                    else
                      (5, 5396)
              else
                if b < 418 then
                  if b < 416 then
                    (5, 5408)
                  else
                    if b < 417 then
                      (5, 5428)
                    else
                      (5, 5429)
                else
                  if b < 419 then
                    (5, 5440)
                  else
                    if b < 420 then
                      (5, 5441)
                    else
                      (5, 5442)
            else
              if b < 426 then
                if b < 423 then
                  if b < 422 then
                    (5, 5445)
                  else
                    (5, 12369)
                else
                  if b < 424 then
                    (5, 12373)
                  else
                    if b < 425 then
                      (5, 13360)
                    else
                      (5, 13363)
              else
                if b < 429 then
                  if b < 427 then
                    (5, 13364)
                  else
                    if b < 428 then
                      (5, 13365)
                    else
                      (5, 13377)
                else
                  if b < 430 then
                    (5, 13393)
                  else
                    if b < 431 then
                      (5, 13397)
                    else
                      (5, 13587)
      else
        if b < 475 then
          if b < 453 then
            if b < 442 then
              if b < 437 then
                if b < 434 then
                  if b < 433 then
                    (5, 13589)
                  else
                    (5, 13601)
                else
                  if b < 435 then
                    (5, 13603)
                  else
                    if b < 436 then
                      (5, 13604)
                    else
                      (5, 13616)
              else
                if b < 439 then
                  if b < 438 then
                    (5, 13617)
                  else
                    (5, 13618)
                else
                  if b < 440 then
                    (5, 13632)
                  else
                    if b < 441 then
                      (5, 13633)
                    else
                      (5, 13634)
            else
              if b < 447 then
                if b < 444 then
                  if b < 443 then
                    (5, 13636)
                  else
                    (5, 13637)
                else
                  if b < 445 then
                    (5, 13648)
                  else
                    if b < 446 then
                      (5, 13649)
                    else
                      (5, 13650)
              else
                if b < 450 then
                  if b < 448 then
                    (5, 13651)
                  else
                    if b < 449 then
                      (5, 13652)
                    else
                      (5, 16693)
                else
                  if b < 451 then
                    (5, 16722)
                  else
                    if b < 452 then
                      (5, 16724)
                    else
                      (5, 16725)
          else
            if b < 464 then
              if b < 458 then
                if b < 455 then
                  if b < 454 then
                    (5, 17157)
                  else
                    (5, 17173)
                else
                  if b < 456 then
                    (5, 17189)
                  else
                    if b < 457 then
                      (5, 17200)
                    else
                      (5, 17233)
              else
                if b < 461 then
                  if b < 459 then
                    (5, 17234)
                  else
                    if b < 460 then
                      (5, 17235)
                    else
                      (5, 17411)
                else
                  if b < 462 then
                    (5, 17491)
                  else
                    if b < 463 then
                      (5, 17492)
                    else
                      (5, 20498)
            else
              if b < 469 then
                if b < 466 then
                  if b < 465 then
                    (5, 20501)
                  else
                    (5, 20515)
                else
                  if b < 467 then
                    (5, 20528)
                  else
                    if b < 468 then
                      (5, 20531)
                    else
                      (5, 20533)
              else
                if b < 472 then
                  if b < 470 then
                    (5, 20544)
                  else
                    if b < 471 then
                      (5, 20546)
                    else
                      (5, 20547)
                else
                  if b < 473 then
                    (5, 20548)
                  else
                    if b < 474 then
                      (5, 20549)
                    else
                      (5, 20560)
        else
          if b < 497 then
            if b < 486 then
              if b < 480 then
                if b < 477 then
                  if b < 476 then
                    (5, 20561)
                  else
                    (5, 20565)
                else
                  if b < 478 then
                    (5, 20784)
                  else
                    if b < 479 then
                      (5, 20785)
                    else
                      (5, 20800)
              else
                if b < 483 then
                  if b < 481 then
                    (5, 20801)
                  else
                    if b < 482 then
                      (5, 20802)
                    else
                      (5, 20803)
                else
                  if b < 484 then
                    (5, 20821)
                  else
                    if b < 485 then
                      (5, 20992)
                    else
                      (5, 20995)
            else
              if b < 491 then
                if b < 488 then
                  if b < 487 then
                    (5, 20996)
                  else
                    (5, 21009)
                else
                  if b < 489 then
                    (5, 21013)
                  else
                    if b < 490 then
                      (5, 21041)
                    else
                      (5, 21042)
              else
                if b < 494 then
                  if b < 492 then
                    (5, 21056)
                  else
                    if b < 493 then
                      (5, 21057)
                    else
                      (5, 21058)
                else
                  if b < 495 then
                    (5, 21060)
                  else
                    if b < 496 then
                      (5, 21061)
                    else
                      (5, 21075)
          else
            if b < 508 then
              if b < 502 then
                if b < 499 then
                  if b < 498 then
                    (5, 21248)
                  else
                    (5, 21251)
                else
                  if b < 500 then
                    (5, 21264)
                  else
                    if b < 501 then
                      (5, 21267)
                    else
                      (5, 21268)
              else
                if b < 505 then
                  if b < 503 then
                    (5, 21283)
                  else
                    if b < 504 then
                      (5, 21284)
                    else
                      (5, 21296)
                else
                  if b < 506 then
                    (5, 21298)
                  else
                    if b < 507 then
                      (5, 21299)
                    else
                      (5, 21330)
            else
              if b < 513 then
                if b < 510 then
                  if b < 509 then
                    (5, 21331)
                  else
                    (5, 21552)
                else
                  if b < 511 then
                    (5, 21553)
                  else
                    if b < 512 then
                      (5, 21554)
                    else
                      (5, 21568)
              else
                if b < 516 then
                  if b < 514 then
                    (5, 66819)
                  else
                    if b < 515 then
                      (5, 66832)
                    else
                      (5, 66848)
                else
                  if b < 517 then
                    (5, 66851)
                  else
                    if b < 518 then
                      (5, 66852)
                    else
                      (5, 66869)
    else
      if b < 606 then
        if b < 562 then
          if b < 540 then
            if b < 529 then
              if b < 524 then
                if b < 521 then
                  if b < 520 then
                    (5, 66883)
                  else
                    (5, 66884)
                else
                  if b < 522 then
                    (5, 66899)
                  else
                    if b < 523 then
                      (5, 66900)
                    else
                      (5, 69955)
              else
                if b < 526 then
                  if b < 525 then
                    (5, 70675)
                  else
                    (5, 70736)
                else
                  if b < 527 then
                    (5, 70915)
                  else
                    if b < 528 then
                      (5, 70929)
                    else
                      (5, 70930)
            else
              if b < 534 then
                if b < 531 then
                  if b < 530 then
                    (5, 70932)
                  else
                    (5, 70933)
                else
                  if b < 532 then
                    (5, 70944)
                  else
                    if b < 533 then
                      (5, 70961)
                    else
                      (5, 70962)
              else
                if b < 537 then
                  if b < 535 then
                    (5, 70965)
                  else
                    if b < 536 then
                      (5, 70981)
                    else
                      (5, 70992)
                else
                  if b < 538 then
                    (5, 70993)
                  else
                    if b < 539 then
                      (5, 70996)
                    else
                      (5, 77905)
          else
            if b < 551 then
              if b < 545 then
                if b < 542 then
                  if b < 541 then
                    (5, 77909)
                  else
                    (5, 78160)
                else
                  if b < 543 then
                    (5, 78164)
                  else
                    if b < 544 then
                      (5, 78928)
                    else
                      (5, 79105)
              else
                if b < 548 then
                  if b < 546 then
                    (5, 79107)
                  else
                    if b < 547 then
                      (5, 79108)
                    else
                      (5, 79136)
                else
                  if b < 549 then
                    (5, 79169)
                  else
                    if b < 550 then
                      (5, 79171)
                    else
                      (5, 79172)
            else
              if b < 556 then
                if b < 553 then
                  if b < 552 then
                    (5, 79185)
                  else
                    (5, 79187)
                else
                  if b < 554 then
                    (5, 79189)
                  else
                    if b < 555 then
                      (5, 86036)
                    else
                      (5, 86066)
              else
                if b < 559 then
                  if b < 557 then
                    (5, 86069)
                  else
                    if b < 558 then
                      (5, 86096)
                    else
                      (5, 86101)
                else
                  if b < 560 then
                    (5, 86289)
                  else
                    if b < 561 then
                      (5, 86290)
                    else
                      (5, 86321)
        else
          if b < 584 then
            if b < 573 then
              if b < 567 then
                if b < 564 then
                  if b < 563 then
                    (5, 86323)
                  else
                    (5, 86336)
                else
                  if b < 565 then
                    (5, 86338)
                  else
                    if b < 566 then
                      (5, 86341)
                    else
                      (5, 86547)
              else
                if b < 570 then
                  if b < 568 then
                    (5, 86548)
                  else
                    if b < 569 then
                      (5, 86595)
                    else
                      (5, 86597)
                else
                  if b < 571 then
                    (5, 86609)
                  else
                    if b < 572 then
                      (5, 86610)
                    else
                      (5, 86801)
            else
              if b < 578 then
                if b < 575 then
                  if b < 574 then
                    (5, 86819)
                  else
                    (5, 86820)
                else
                  if b < 576 then
                    (5, 86821)
                  else
                    if b < 577 then
                      (5, 86833)
                    else
                      (5, 86835)
              else
                if b < 581 then
                  if b < 579 then
                    (5, 86836)
                  else
                    if b < 580 then
                      (5, 86837)
                    else
                      (5, 86851)
                else
                  if b < 582 then
                    (5, 86865)
                  else
                    if b < 583 then
                      (5, 86866)
                    else
                      (5, 87040)
          else
            if b < 595 then
              if b < 589 then
                if b < 586 then
                  if b < 585 then
                    (5, 87045)
                  else
                    (5, 87056)
                else
                  if b < 587 then
                    (5, 87104)
                  else
                    if b < 588 then
                      (5, 87120)
                    else
                      (5, 87123)
              else
                if b < 592 then
                  if b < 590 then
                    (5, 87124)
                  else
                    if b < 591 then
                      (5, 87296)
                    else
                      (5, 87299)
                else
                  if b < 593 then
                    (5, 87317)
                  else
                    if b < 594 then
                      (5, 87333)
                    else
                      (5, 197888)
            else
              if b < 600 then
                if b < 597 then
                  if b < 596 then
                    (5, 197891)
                  else
                    (5, 197892)
                else
                  if b < 598 then
                    (5, 197920)
                  else
                    if b < 599 then
                      (5, 197923)
                    else
                      (5, 197925)
              else
                if b < 603 then
                  if b < 601 then
                    (5, 197937)
                  else
                    if b < 602 then
                      (5, 197954)
                    else
                      (5, 201812)
                else
                  if b < 604 then
                    (5, 201986)
                  else
                    if b < 605 then
                      (5, 201989)
                    else
                      (5, 202002)
      else
        if b < 649 then
          if b < 627 then
            if b < 616 then
              if b < 611 then
                if b < 608 then
                  if b < 607 then
                    (5, 202004)
                  else
                    (5, 202032)
                else
                  if b < 609 then
                    (5, 202036)
                  else
                    if b < 610 then
                      (5, 202049)
                    else
                      (5, 202050)
              else
                if b < 613 then
                  if b < 612 then
                    (5, 202051)
                  else
                    (5, 202052)
                else
                  if b < 614 then
                    (5, 202067)
                  else
                    if b < 615 then
                      (5, 210208)
                    else
                      (5, 210213)
            else
              if b < 621 then
                if b < 618 then
                  if b < 617 then
                    (5, 210244)
                  else
                    (5, 212995)
                else
                  if b < 619 then
                    (5, 213074)
                  else
                    if b < 620 then
                      (5, 213077)
                    else
                      (5, 213332)
              else
                if b < 624 then
                  if b < 622 then
                    (5, 213763)
                  else
                    if b < 623 then
                      (5, 213781)
                    else
                      (5, 214098)
                else
                  if b < 625 then
                    (5, 214099)
                  else
                    if b < 626 then
                      (5, 214100)
                    else
                      (5, 214275)
          else
            if b < 638 then
              if b < 632 then
                if b < 629 then
                  if b < 628 then
                    (5, 214277)
                  else
                    (5, 214308)
                else
                  if b < 630 then
                    (5, 217920)
                  else
                    if b < 631 then
                      (5, 217936)
                    else
                      (5, 218181)
              else
                if b < 635 then
                  if b < 633 then
                    (5, 218371)
                  else
                    if b < 634 then
                      (5, 218404)
                    else
                      (5, 218437)
                else
                  if b < 636 then
                    (5, 327717)
                  else
                    if b < 637 then
                      (5, 327728)
                    else
                      (5, 327760)
            else
              if b < 643 then
                if b < 640 then
                  if b < 639 then
                    (5, 327765)
                  else
                    (5, 327939)
                else
                  if b < 641 then
                    (5, 328001)
                  else
                    if b < 642 then
                      (5, 328468)
                    else
                      (5, 328469)
              else
                if b < 646 then
                  if b < 644 then
                    (5, 331857)
                  else
                    if b < 645 then
                      (5, 332117)
                    else
                      (5, 332608)
                else
                  if b < 647 then
                    (5, 332624)
                  else
                    if b < 648 then
                      (5, 332627)
                    else
                      (5, 332836)
        else
          if b < 671 then
            if b < 660 then
              if b < 654 then
                if b < 651 then
                  if b < 650 then
                    (5, 332865)
                  else
                    (5, 333109)
                else
                  if b < 652 then
                    (5, 339988)
                  else
                    if b < 653 then
                      (5, 340001)
                    else
                      (5, 340033)
              else
                if b < 657 then
                  if b < 655 then
                    (5, 340048)
                  else
                    if b < 656 then
                      (5, 340228)
                    else
                      (5, 340756)
                else
                  if b < 658 then
                    (5, 340802)
                  else
                    if b < 659 then
                      (5, 340803)
                    else
                      (5, 341060)
            else
              if b < 665 then
                if b < 662 then
                  if b < 661 then
                    (5, 344101)
                  else
                    (5, 344372)
                else
                  if b < 663 then
                    (5, 344385)
                  else
                    if b < 664 then
                      (5, 345156)
                    else
                      (5, 345345)
              else
                if b < 668 then
                  if b < 666 then
                    (5, 345409)
                  else
                    if b < 667 then
                      (5, 348466)
                    else
                      (5, 349459)
                else
                  if b < 669 then
                    (5, 349489)
                  else
                    if b < 670 then
                      (6, 1109)
                    else
                      (6, 1344)
          else
            if b < 682 then
              if b < 676 then
                if b < 673 then
                  if b < 672 then
                    (6, 13589)
                  else
                    (6, 17699)
                else
                  if b < 674 then
                    (6, 20772)
                  else
                    if b < 675 then
                      (6, 20800)
                    else
                      (6, 21524)
              else
                if b < 679 then
                  if b < 677 then
                    (6, 21539)
                  else
                    if b < 678 then
                      (6, 21569)
                    else
                      (6, 21572)
                else
                  if b < 680 then
                    (6, 83264)
                  else
                    if b < 681 then
                      (6, 86338)
                    else
                      (6, 86853)
            else
              if b < 687 then
                if b < 684 then
                  if b < 683 then
                    (6, 197970)
                  else
                    (6, 217621)
                else
                  if b < 685 then
                    (6, 217893)
                  else
                    if b < 686 then
                      (6, 218132)
                    else
                      (6, 218133)
              else
                if b < 690 then
                  if b < 688 then
                    (6, 218400)
                  else
                    if b < 689 then
                      (6, 275744)
                    else
                      (6, 332804)
                else
                  if b < 691 then
                    (6, 344851)
                  else
                    if b < 692 then
                      (6, 1070149)
                    else
                      (6, 1389861)

def pointBlocks (b : Nat) : Nat :=
  if b < 1 then
    144798615236968509915088428006028053687400050564450539318687531014119752278511149000712715254555395391190293787118547075948930017661014334457644889170824491078506835180050673072454297942828315749727447832808054609109172900121592962155135262856730737485534576737124993431377945280443383006424271810880444298419995034783241303012008305722182185621056530187160958397030689426613836944756659210459159265311114095230904731169288140254427420719457850039704045833609207598471548119210528114739100080917933571843402002000987974739132332393964445278439896177021208362810928426844337909754376229770952222189604423694108488586129702314933576790408938807195151390891160069714779776113742595972900949308426041445288783994553148361565950721180880691586258445696617203372403878072473021135403980354765948767638110696946009830026393396968427875326064739395501159720336283366207586388360420203272445572267211428106013980826128635881171485265388023587858674188614234362231532251009848064720284123698807113954807138217621999366916724804700983737662020692519523645635239085144089925563576439622920029970892242912211325843050625365889864461729428671017294129062869983372378139
  else
    if b < 2 then
      1046828247660601888085013054307657000627261957222306930581861851099153390879043448808136501023980807228893256093520433623530505318174808853197721943693454725032846859527671400404980029390240647009460971603519250048950376758806951718272402736666485136047445381841230321265855520751979830533102681912322649880871455568020234683027010048985338259950788078488181687858271441346987499324450175638460487838356889443662988992187487816593301303459948726301729038035513023192034950283117529628037310303011815466353014927732432845798092199813280366062958232834848869619959885886735850232753391633407530627317054383859746715057012425616779645169924592102680333594103739734313590875620203429899629019478162971323211567339541604841467444029042003443933764261949237436960132269899818357805366526268934831444964373108601912318524085703476181063302248103241691483434970346590545235585468720975639182064057567997964449968394007939059105296196402674650363759837357793044176986529651177030733957028294990735808772110143964700566257883421801916546383908657086289748235397022565117055379316364197696343502573841231262400083431080147479535783581031148536766908608025019709589811
    else
      12440464347302441239981650423296696447098176345989419710813957007188828254501612425371845829228594846692907918188306837291013914559140233868889203466050954680730874606468929720323081018891315306774399337500666863822519605211988167962215823471046914836570328463389899784795365402726398299278837415748549609108026338243335849408973946394183501249693410062545737385880658998652967377261611800090219531345059256845377906538147628187150580376846182576416934159653734984698703104995977533435347640058784506029503576609646833975225463329928753791762727334176410345608403189157822758282480358647713918508221270705647844844244856931177268191484675510218804792198820441057197644997885597403905257554519804967049217081823555107781148956572461698615738993896257401883125128051268069648663328089435823258745793226903122775160981888

def point (r : Fin 693) : Fin 31671 :=
  Fin.ofNat 31671 ((pointBlocks (r.val / 256) >>> (15 * (r.val % 256))) % 32768)

def forward0Blocks (b : Nat) : Nat :=
  if b < 1 then
    54738400203631998955529560197126927927124413961553044487739108120776974067690665241250720601141558628201687036003333704724611556039400822019538106683431029455436980642770462563272746855679117216674383197634090562375652513135129357884833684910883365876636364954337214136413268286274157325259137817869557776418929498700361782661430519395185628938550332559615375312684305658380555985796312615950737150522859221770778508059031725988965049492775569698694786753855508985748432361838254892290729076859329852479728554989415312645588001833613653410318339150266309784146072423510066179638369892678322959685954891934297088193889295723840894193017417714177796251335620929799815886494038335131092489851767841716915097929214568522213125338013206233279612080179913343762792755251647489
  else
    if b < 2 then
      288715900468738985509146509343463884229508697197966887249638494673191197961905294628516210956603610363278906686839116585195111489792293888263163067321215427227323856497507041470453380806393112163287355114979071227285131501067597894041309404142527792800196142751772177122270107753390967254499894652868523803281449287436677609475515796089546087398635471485034310982434231162378986166274153791643261760084829105411359091976838606031591545864766793471252361591773105288211310866958039808543339683959834416704299371164540533664254618026021361051898115934355513344925098381143468850251500059179776185345263013971681882603474446038055189172232687573327092299646004523287816717358734498354809461741457715595951750829334687613156738350370800726107315349738880817786711155537032737
    else
      27910663529082703634270664577871241761301732737823474928649090780443384969724938116470701170455361483576219084625639512772040001306242665923324043145466150296127672568332194950343660419633289022054663911304472328266522893464054120183877397953987604070019990944259324975727582454743678818526728393796696549556959041092368734899016330145916206103363389983665633329857840243124460380676872097968927674047219444773892338570395739397185772151768420298807777674773176329390832726728542737593574337460226294743877805151047864518298142907779158672359027

def backward0Blocks (b : Nat) : Nat :=
  if b < 1 then
    234449292072115733490313528990636734910179693398204422776805840543025138415584475739286402142203696819307719204064087684871519999072246645972959528449034960729343999724483406479746935251265824851175544379767077679975550402892486948186682129075069542965885447549089563235431850176154853885861528328861495172007833625375630483874711921734522427751323124714965771850161545662295816739601657618346872336654085210708179740820488936086696084813144729928901001294556295121204814504820076497143090989186316855065401689050651209047074081685800077945448702479849789536822307542603466997587851140463862840364598259393743027044077139195421763752911868794131012583745818665161655466518979576621767593430793016574066686603181468813812255770769196259607668915772743373302080404399849496
  else
    if b < 2 then
      119453742364046967254036633361114034252025383599922580136857285972309929005625911426040434523273831708975040902862919384997913201663207178692698940809868597064835961641199869280168539038698916193121620010460393734805396943717380156217238729685830979878740485284793951667248301122084856260461378363509171301585677242568224868540284325484148055145035468892852923804850317117582985812533104422819138207916866714027445678728196365373163309800826577598446814099167258939216951101963746249121162525516290379137588629830145416641493166186869072639506018574313922789792989719155698166766509664543817240496929708967935657874339932506996008991274123049571953075427900844445100840043649348202332662526311873499512877958417306497448425515076930808344984959395819331451211830544219702
    else
      45772063247615858693020201163673119158807173436381697061934364818749710731111325680215497202134941779287147173449354304873012841462816276211230512593647090749946631215663886941458594676017459698110160761117532279899196100734636383434940876063793140919802676745508751932018995097250633725535599559697827111815465688431744183082541008824891724853323727154654069603045386866437899038144817630686586184367637765794941993222186640188234510304504096036220414226698732398117800378913782117477071902578629777017171417125719831323766519637909151412318372

def factorCode0 (b : Nat) : Nat × Nat :=
  if b < 346 then
    if b < 173 then
      if b < 86 then
        if b < 43 then
          if b < 21 then
            if b < 10 then
              (0, 0)
            else
              if b < 15 then
                if b < 12 then
                  if b < 11 then
                    (4, 30891)
                  else
                    (2, 11)
                else
                  if b < 13 then
                    (0, 0)
                  else
                    if b < 14 then
                      (0, 0)
                    else
                      (3, 1079)
              else
                if b < 18 then
                  if b < 16 then
                    (2, 71)
                  else
                    if b < 17 then
                      (3, 2212)
                    else
                      (0, 0)
                else
                  if b < 19 then
                    (17, 134172607308923671893)
                  else
                    (0, 0)
          else
            if b < 32 then
              if b < 26 then
                if b < 23 then
                  (0, 0)
                else
                  if b < 24 then
                    (0, 0)
                  else
                    if b < 25 then
                      (0, 0)
                    else
                      (4, 34724)
              else
                if b < 29 then
                  if b < 27 then
                    (0, 0)
                  else
                    if b < 28 then
                      (0, 0)
                    else
                      (1, 10)
                else
                  if b < 30 then
                    (0, 0)
                  else
                    if b < 31 then
                      (0, 0)
                    else
                      (2, 183)
            else
              if b < 37 then
                if b < 34 then
                  if b < 33 then
                    (14, 57066562356323920)
                  else
                    (58, 5949459045461173213183172689912516585909548480485599058682576619494281)
                else
                  if b < 35 then
                    (19, 36777927671982412605009)
                  else
                    (0, 0)
              else
                if b < 40 then
                  if b < 38 then
                    (0, 0)
                  else
                    if b < 39 then
                      (19, 60126415954805628151384)
                    else
                      (14, 34918020866693913)
                else
                  if b < 41 then
                    (0, 0)
                  else
                    if b < 42 then
                      (0, 0)
                    else
                      (13, 3609031227760641)
        else
          if b < 64 then
            if b < 53 then
              if b < 48 then
                if b < 45 then
                  if b < 44 then
                    (0, 0)
                  else
                    (2, 161)
                else
                  if b < 46 then
                    (0, 0)
                  else
                    if b < 47 then
                      (0, 0)
                    else
                      (3, 2052)
              else
                if b < 50 then
                  if b < 49 then
                    (2, 1)
                  else
                    (8, 2358265089)
                else
                  if b < 51 then
                    (0, 0)
                  else
                    if b < 52 then
                      (32, 231023404883838372425319038260896652169)
                    else
                      (11, 1618356886475)
            else
              if b < 58 then
                if b < 55 then
                  if b < 54 then
                    (39, 79157612246238232573922670774223581861185455323)
                  else
                    (27, 42408736766127895062345859617104)
                else
                  (0, 0)
              else
                (0, 0)
          else
            if b < 75 then
              if b < 69 then
                if b < 66 then
                  if b < 65 then
                    (16, 6110497824202313137)
                  else
                    (0, 0)
                else
                  if b < 67 then
                    (15, 164020589690115669)
                  else
                    if b < 68 then
                      (66, 4217134758504226451226936208044644433412317279657072036621567491344539626898534)
                    else
                      (0, 0)
              else
                if b < 72 then
                  (0, 0)
                else
                  if b < 73 then
                    (51, 21675354570909498372925583525410847728932175936471218941986011)
                  else
                    if b < 74 then
                      (0, 0)
                    else
                      (27, 167862148852871047857651990221923)
            else
              if b < 80 then
                if b < 77 then
                  (0, 0)
                else
                  if b < 78 then
                    (0, 0)
                  else
                    if b < 79 then
                      (0, 0)
                    else
                      (53, 5283272438474655277305810532840797618959314726526841751335131929)
              else
                if b < 83 then
                  if b < 81 then
                    (25, 1003907545706730540193905247451)
                  else
                    if b < 82 then
                      (0, 0)
                    else
                      (51, 19037305249266123360056898575918339345376830627156038626182363)
                else
                  if b < 84 then
                    (51, 3657781333467532330928677533660041091949081361814907376394308)
                  else
                    if b < 85 then
                      (27, 279582519649114197498947197488569)
                    else
                      (0, 0)
      else
        if b < 129 then
          if b < 107 then
            if b < 96 then
              if b < 91 then
                if b < 88 then
                  (0, 0)
                else
                  if b < 89 then
                    (24, 62781391660362258935567109561)
                  else
                    if b < 90 then
                      (0, 0)
                    else
                      (68, 986400176323408950101090316357661547658147674781036668803080466548311229320286819)
              else
                if b < 93 then
                  if b < 92 then
                    (68, 6565263035967072786148642097203827920698053379468092556760768998128800542331260344)
                  else
                    (66, 4217134758504226451226936208044644433412317279657072036621567491344539641529936)
                else
                  if b < 94 then
                    (0, 0)
                  else
                    if b < 95 then
                      (0, 0)
                    else
                      (12, 135022981506441)
            else
              if b < 101 then
                if b < 98 then
                  if b < 97 then
                    (2, 71)
                  else
                    (0, 0)
                else
                  if b < 99 then
                    (0, 0)
                  else
                    if b < 100 then
                      (0, 0)
                    else
                      (16, 15819119327729313025)
              else
                if b < 104 then
                  if b < 102 then
                    (0, 0)
                  else
                    if b < 103 then
                      (9, 10863971348)
                    else
                      (3, 3257)
                else
                  if b < 105 then
                    (35, 720962443135717970083154556032775072604193)
                  else
                    (0, 0)
          else
            if b < 118 then
              if b < 112 then
                if b < 109 then
                  if b < 108 then
                    (14, 38225167461545473)
                  else
                    (0, 0)
                else
                  if b < 110 then
                    (33, 1504009730102249806885210000782105338208)
                  else
                    if b < 111 then
                      (23, 4290160405307372389823172025)
                    else
                      (29, 14554398920038984491063127981118996)
              else
                if b < 115 then
                  if b < 113 then
                    (40, 403729468370831254874022623860326791316245079142)
                  else
                    if b < 114 then
                      (18, 3754549476537046773785)
                    else
                      (5, 544848)
                else
                  if b < 116 then
                    (8, 2356954225)
                  else
                    if b < 117 then
                      (8, 558171460)
                    else
                      (27, 171479548195789381206996550878309)
            else
              if b < 123 then
                if b < 120 then
                  if b < 119 then
                    (8, 363877395)
                  else
                    (42, 48633283500290627555595622103497664075018595075168)
                else
                  if b < 121 then
                    (0, 0)
                  else
                    if b < 122 then
                      (52, 58524501335480517294858840538560982302096726789130212647986213)
                    else
                      (0, 0)
              else
                if b < 126 then
                  if b < 124 then
                    (15, 611602677572632596)
                  else
                    if b < 125 then
                      (0, 0)
                    else
                      (42, 58863794961606947983021415932511701836169360791060)
                else
                  if b < 127 then
                    (40, 1252962149175943917624556192175192212816183821531)
                  else
                    if b < 128 then
                      (79, 62995053528184563475203494973307165863969508521627979965327569662523727245457049543473799122360)
                    else
                      (46, 15020151646879614300625534172744759050106791954191764921)
        else
          if b < 151 then
            if b < 140 then
              if b < 134 then
                if b < 131 then
                  (0, 0)
                else
                  if b < 132 then
                    (0, 0)
                  else
                    if b < 133 then
                      (17, 46679131017640697920)
                    else
                      (8, 3166224641)
              else
                if b < 137 then
                  if b < 135 then
                    (48, 5341476267386335555883774312546550949521104500668030274993)
                  else
                    if b < 136 then
                      (66, 15333175325286581211889750768878683587326235807558566184409495555883014194431604)
                    else
                      (6, 12241984)
                else
                  if b < 138 then
                    (19, 13237148705265085075523)
                  else
                    if b < 139 then
                      (17, 199186448406830458449)
                    else
                      (0, 0)
            else
              if b < 145 then
                if b < 142 then
                  if b < 141 then
                    (21, 15474268289514552530920729)
                  else
                    (19, 54533495303679824258441)
                else
                  if b < 143 then
                    (27, 258267865032314042524465432419209)
                  else
                    if b < 144 then
                      (9, 37117891845)
                    else
                      (52, 218315876297493970169938302273621945950307327870843534012599737)
              else
                if b < 148 then
                  if b < 146 then
                    (8, 2357551124)
                  else
                    (0, 0)
                else
                  (0, 0)
          else
            if b < 162 then
              if b < 156 then
                if b < 153 then
                  if b < 152 then
                    (33, 774565325824692168105717815759807599205)
                  else
                    (0, 0)
                else
                  if b < 154 then
                    (48, 3354428023297090818199590025646032585140751239796542688689)
                  else
                    if b < 155 then
                      (50, 831213099938842124011278130481689813063391461688587206419813)
                    else
                      (0, 0)
              else
                if b < 159 then
                  if b < 157 then
                    (72, 137382019092958621051599884195733316639984723386730220894431215128154421929632871112709)
                  else
                    (0, 0)
                else
                  if b < 160 then
                    (53, 4007332270158343586109126271403090197581224286595463196438824155)
                  else
                    if b < 161 then
                      (0, 0)
                    else
                      (58, 5082985299336406417335857672478550988821164494208237641766966426655625)
            else
              if b < 167 then
                if b < 164 then
                  if b < 163 then
                    (51, 14145774109755896092043540739855300201122846985312227912189147)
                  else
                    (0, 0)
                else
                  if b < 165 then
                    (0, 0)
                  else
                    if b < 166 then
                      (15, 848028675445490907)
                    else
                      (0, 0)
              else
                if b < 170 then
                  if b < 168 then
                    (0, 0)
                  else
                    if b < 169 then
                      (40, 116576944106358385817356716036037965376799507766)
                    else
                      (79, 71368636543203246154120979239489050924638739864916206816285052878396517650394596108217081977625)
                else
                  if b < 171 then
                    (20, 211665221796105575338086)
                  else
                    if b < 172 then
                      (17, 161139865137839473883)
                    else
                      (38, 3163198330433167574204205140273483397542053083)
    else
      if b < 259 then
        if b < 216 then
          if b < 194 then
            if b < 183 then
              if b < 178 then
                if b < 175 then
                  if b < 174 then
                    (14, 8120329115290967)
                  else
                    (8, 2882289921)
                else
                  if b < 176 then
                    (19, 12042942190894475556161)
                  else
                    if b < 177 then
                      (0, 0)
                    else
                      (20, 588743351126287086098001)
              else
                if b < 180 then
                  if b < 179 then
                    (47, 212799076755466997958442266130701569699185178130109488009)
                  else
                    (0, 0)
                else
                  if b < 181 then
                    (52, 277384287109316423740624593613482489086895425846880725859585464)
                  else
                    if b < 182 then
                      (14, 19905399619285606)
                    else
                      (0, 0)
            else
              if b < 188 then
                if b < 185 then
                  if b < 184 then
                    (25, 655711520645485756423051961955)
                  else
                    (0, 0)
                else
                  if b < 186 then
                    (67, 131017703144987698604202160068257633819565509211282940763884749537119145361171778)
                  else
                    if b < 187 then
                      (7, 121374036)
                    else
                      (0, 0)
              else
                if b < 191 then
                  if b < 189 then
                    (15, 853251278707208217)
                  else
                    if b < 190 then
                      (40, 116576944106358385817356716036039119408153584481)
                    else
                      (0, 0)
                else
                  if b < 192 then
                    (50, 443905244949551779844753348977755487461052052928504495736080)
                  else
                    if b < 193 then
                      (13, 1244087496098917)
                    else
                      (41, 12095742567018054600503501285590607048119876208180)
          else
            if b < 205 then
              if b < 199 then
                if b < 196 then
                  if b < 195 then
                    (15, 524111745420518145)
                  else
                    (26, 3191012721059646403240075355414)
                else
                  if b < 197 then
                    (0, 0)
                  else
                    if b < 198 then
                      (46, 13570051183821442643800824525161849130387692808321387961)
                    else
                      (51, 2050843289208542055386715441318898791360907461012948335859014)
              else
                if b < 202 then
                  if b < 200 then
                    (0, 0)
                  else
                    if b < 201 then
                      (41, 3678987185100434248938838495781977762130437740114)
                    else
                      (49, 86717587941784520896455796385736456357389386342597661164763)
                else
                  if b < 203 then
                    (17, 38608680451300418629)
                  else
                    if b < 204 then
                      (61, 4447622598099259928986912673314028525841264006874950824535595093251610179)
                    else
                      (14, 11484563504849220)
            else
              if b < 210 then
                if b < 207 then
                  if b < 206 then
                    (15, 183753016323875941)
                  else
                    (31, 10259245721066179254884935912939218201)
                else
                  if b < 208 then
                    (25, 692486408128707262756119662008)
                  else
                    if b < 209 then
                      (14, 61850022506030337)
                    else
                      (28, 820516655512602905582764290106720)
              else
                if b < 213 then
                  (0, 0)
                else
                  if b < 214 then
                    (0, 0)
                  else
                    if b < 215 then
                      (0, 0)
                    else
                      (10, 173824295523)
        else
          if b < 237 then
            if b < 226 then
              if b < 221 then
                if b < 218 then
                  if b < 217 then
                    (26, 1863229707735646919998361130038)
                  else
                    (16, 2397806004866671908)
                else
                  if b < 219 then
                    (40, 229936699068777140558677405986373614111758049334)
                  else
                    if b < 220 then
                      (25, 180342545836600891967437899334)
                    else
                      (0, 0)
              else
                if b < 223 then
                  if b < 222 then
                    (24, 68334196034812354686233890233)
                  else
                    (0, 0)
                else
                  if b < 224 then
                    (74, 20030311475484424307266889810068566920658230755280638918512990290913908437267305024472390)
                  else
                    if b < 225 then
                      (24, 43862085080883404382406171393)
                    else
                      (19, 54238347398500806633049)
            else
              if b < 231 then
                if b < 228 then
                  if b < 227 then
                    (6, 13229008)
                  else
                    (21, 2179784270988827594937428)
                else
                  if b < 229 then
                    (6, 2443088)
                  else
                    if b < 230 then
                      (15, 849911329092685961)
                    else
                      (19, 11940088814483137631557)
              else
                if b < 234 then
                  if b < 232 then
                    (55, 465468386128221207102492087657722696379811236445488739209136399680)
                  else
                    if b < 233 then
                      (0, 0)
                    else
                      (24, 63693153406613038333727070984)
                else
                  if b < 235 then
                    (51, 15346652178166322265459804463466584340199234288962615740747193)
                  else
                    if b < 236 then
                      (14, 19905399936517670)
                    else
                      (15, 990189129754851209)
          else
            if b < 248 then
              if b < 242 then
                if b < 239 then
                  if b < 238 then
                    (0, 0)
                  else
                    (27, 51056203537631112950663329760852)
                else
                  if b < 240 then
                    (39, 68625620432162828942058202455104069227033677241)
                  else
                    if b < 241 then
                      (81, 29175761072685462177104115221741456578762372102012991195645582251838611569763943907347937628652763)
                    else
                      (27, 167862148721582251661760823123990)
              else
                if b < 245 then
                  if b < 243 then
                    (32, 94000591982815241178968600896271504196)
                  else
                    if b < 244 then
                      (77, 383940370570263601992703808485081195956341119255329461603030724238537930265364461496568175385)
                    else
                      (52, 347888278017827969845553114673241389466115776045901063645056433)
                else
                  if b < 246 then
                    (52, 278975313247768056008939524527453147388827355906825473442729393)
                  else
                    if b < 247 then
                      (67, 399307591774520740222853193220213599363914330253394119685903726708280270748929457)
                    else
                      (24, 58722201271549985679260798392)
            else
              if b < 253 then
                if b < 250 then
                  if b < 249 then
                    (41, 17308523399857266090531130977585495242340214787512)
                  else
                    (4, 22727)
                else
                  if b < 251 then
                    (9, 49304768649)
                  else
                    if b < 252 then
                      (8, 3167274104)
                    else
                      (51, 17323815184287101217459504751765481435733157390294177787432369)
              else
                if b < 256 then
                  if b < 254 then
                    (56, 16611689572650068994840465312815155861748824404358283558009088378075)
                  else
                    if b < 255 then
                      (4, 49240)
                    else
                      (31, 3306710127925001881166363415602550374)
                else
                  if b < 257 then
                    (41, 12860813953601412332210842257033446911338205957553)
                  else
                    if b < 258 then
                      (45, 1135839324183747758843763307829068356791412927089364409)
                    else
                      (41, 3678987185100434248938838495781980076819156242454)
      else
        if b < 302 then
          if b < 280 then
            if b < 269 then
              if b < 264 then
                if b < 261 then
                  if b < 260 then
                    (81, 9440820465003277780766058097568989723301551886169802545863007004031578603161797817454921190359350)
                  else
                    (0, 0)
                else
                  if b < 262 then
                    (0, 0)
                  else
                    if b < 263 then
                      (18, 3723345301356391805065)
                    else
                      (31, 3389786877661559107145072915448750165)
              else
                if b < 266 then
                  if b < 265 then
                    (19, 9976402326603905520740)
                  else
                    (20, 891782281056090822878809)
                else
                  if b < 267 then
                    (14, 11203569587201077)
                  else
                    if b < 268 then
                      (14, 32756984206231059)
                    else
                      (21, 15535705853265735425615241)
            else
              if b < 274 then
                if b < 271 then
                  if b < 270 then
                    (13, 2384041938238406)
                  else
                    (15, 922547723552938753)
                else
                  if b < 272 then
                    (0, 0)
                  else
                    if b < 273 then
                      (42, 198533986281927167219498257558883078468219890060721)
                    else
                      (0, 0)
              else
                if b < 277 then
                  if b < 275 then
                    (29, 71348232480580584571339666606597720)
                  else
                    if b < 276 then
                      (0, 0)
                    else
                      (68, 5479375977670783165689610183291656825801212063042088142278429631640727693431950776)
                else
                  if b < 278 then
                    (17, 33229335466355286112)
                  else
                    if b < 279 then
                      (27, 167862148852871047857651990221923)
                    else
                      (21, 13939763307759413734040857)
          else
            if b < 291 then
              if b < 285 then
                if b < 282 then
                  if b < 281 then
                    (26, 1843917560890589550706898003536)
                  else
                    (68, 605302100661034835059148914663843304386559366401746691069503013631166380636509716)
                else
                  if b < 283 then
                    (23, 759660195081245999987336629)
                  else
                    if b < 284 then
                      (14, 51929766085944585)
                    else
                      (77, 418975830270784548958390182076183380584707841230483756977219523696876451025318581009437969841)
              else
                if b < 288 then
                  if b < 286 then
                    (17, 216302498597601915017)
                  else
                    if b < 287 then
                      (42, 58863794961606947983021415932511663677109930704902)
                    else
                      (14, 11484563512116806)
                else
                  if b < 289 then
                    (51, 7102483919192828477516053583643454190475140060223718324200772)
                  else
                    if b < 290 then
                      (43, 4765657385018164842736139848504436624979373460573625)
                    else
                      (27, 235583969021285939533884894272281)
            else
              if b < 296 then
                if b < 293 then
                  if b < 292 then
                    (52, 322766922057633792255207773506681352904856764958021423701446073)
                  else
                    (29, 42972710319502224911530299138146403)
                else
                  if b < 294 then
                    (57, 309393443927696187789621189372291366108354521158088010061089134140185)
                  else
                    if b < 295 then
                      (17, 46658536227037582850)
                    else
                      (25, 350179493363258396010688631861)
              else
                if b < 299 then
                  if b < 297 then
                    (40, 403729468370831254874022623860323407849702326372)
                  else
                    if b < 298 then
                      (52, 201755805334974378931175097328274276589370273179071656893631928)
                    else
                      (27, 279585447591555006874995142799385)
                else
                  if b < 300 then
                    (0, 0)
                  else
                    if b < 301 then
                      (0, 0)
                    else
                      (19, 13229076256703481139555)
        else
          if b < 324 then
            if b < 313 then
              if b < 307 then
                if b < 304 then
                  if b < 303 then
                    (15, 129802089913521250)
                  else
                    (48, 3476828247043208380466583418236442287802732102469164223921)
                else
                  if b < 305 then
                    (18, 4054617086996072684425)
                  else
                    if b < 306 then
                      (50, 1166679348176567375539889630360928637437191688445809404169656)
                    else
                      (29, 61425024168518389490377842892266265)
              else
                if b < 310 then
                  if b < 308 then
                    (16, 1471407902502048353)
                  else
                    if b < 309 then
                      (78, 1084558463507884789738976973490803247674493350687487092092419601373752054461853134478632895493)
                    else
                      (23, 624260503560779696084236388)
                else
                  if b < 311 then
                    (0, 0)
                  else
                    if b < 312 then
                      (40, 189973763673010263889045398841787971478924633188)
                    else
                      (25, 1092178478265391235163301459737)
            else
              if b < 318 then
                if b < 315 then
                  if b < 314 then
                    (14, 39816340040601009)
                  else
                    (40, 755983910438628412531468830349411934285257266769)
                else
                  if b < 316 then
                    (57, 34407440845202179108306888489542149294870155472532356005469700317206)
                  else
                    if b < 317 then
                      (23, 3525590571808754573638949769)
                    else
                      (26, 17493270007269630621730692455305)
              else
                if b < 321 then
                  if b < 319 then
                    (23, 1367888780567056218639648083)
                  else
                    if b < 320 then
                      (16, 2829954754936194656)
                    else
                      (41, 15845609783585973827028123431786742496260412951993)
                else
                  if b < 322 then
                    (12, 152647832016473)
                  else
                    if b < 323 then
                      (57, 223127067515256657670975994098679607777851146122095194125645084057665)
                    else
                      (25, 677633961268484869508250786585)
          else
            if b < 335 then
              if b < 329 then
                if b < 326 then
                  if b < 325 then
                    (28, 4066424065609699671553890477462117)
                  else
                    (23, 4170604552126880197705223601)
                else
                  if b < 327 then
                    (51, 18830321041662660818177097227068808401740594012672808196263353)
                  else
                    if b < 328 then
                      (41, 17160331046608621183704069708438736219426905185049)
                    else
                      (67, 399235214648339012586705260021270273251919672545001233285006285819299389658647992)
              else
                if b < 332 then
                  if b < 330 then
                    (15, 998544415937023416)
                  else
                    if b < 331 then
                      (16, 8385787956775904324)
                    else
                      (16, 2902209161553384550)
                else
                  if b < 333 then
                    (54, 16568685315919145677189948682911800316874956486158578877913634118)
                  else
                    if b < 334 then
                      (35, 1093562958593026167734710120708930292174257)
                    else
                      (49, 47011197437978124820852014875904478985268834679018045328825)
            else
              if b < 340 then
                if b < 337 then
                  if b < 336 then
                    (50, 877171694402734448820967825719640402067175597760582892520667)
                  else
                    (53, 3483625459850663456048968553042784924252996974919091749340073401)
                else
                  if b < 338 then
                    (55, 814878714125286554144070750148173283971478499490209128691513296091)
                  else
                    if b < 339 then
                      (50, 758289981096575290657623626330893827581741818368410643353016)
                    else
                      (14, 10251286835566180)
              else
                if b < 343 then
                  if b < 341 then
                    (69, 105222224153274192847515092384790610461459854643187724392354921822336960972711808433)
                  else
                    if b < 342 then
                      (13, 1244087616684642)
                    else
                      (39, 48812781601116182579306157613231863047163086043)
                else
                  if b < 344 then
                    (47, 192307558707442396390465305688297326790939587012389260729)
                  else
                    if b < 345 then
                      (53, 1035542832244946604824371792681987519804682951121545485755769188)
                    else
                      (20, 592874051284151604104633)
  else
    if b < 519 then
      if b < 432 then
        if b < 389 then
          if b < 367 then
            if b < 356 then
              if b < 351 then
                if b < 348 then
                  if b < 347 then
                    (47, 108375303942761665001160485590262667701341874162061630224)
                  else
                    (65, 1481411185121313354216123310175870875622009845651566817762221039369464939152603)
                else
                  if b < 349 then
                    (69, 19102393603786873156802072343891684456499319796829832952988615313391241361938081382)
                  else
                    if b < 350 then
                      (16, 2413042528202555462)
                    else
                      (67, 411045957061857564415801762972291316383722312612013136968126701168341012258508217)
              else
                if b < 353 then
                  if b < 352 then
                    (67, 245330805204585299390236012302058937397219772920937058950551928897667199624696419)
                  else
                    (39, 44416974604955474206744258348826202446684507577)
                else
                  if b < 354 then
                    (51, 15829912478914747255906075094040025125292402298935261723119025)
                  else
                    if b < 355 then
                      (29, 42972710319502223906669146547774737)
                    else
                      (58, 3689075122412617758970699221967886848107685106451460798627904718428953)
            else
              if b < 361 then
                if b < 358 then
                  if b < 357 then
                    (58, 1085845360864077131100320476883307745566718787951508402110944705385749)
                  else
                    (57, 319502885634595565491374223034484988305825246533010767732056147381681)
                else
                  if b < 359 then
                    (68, 1079586498177081971514095669259428974953553223592210441375121277729943503371572803)
                  else
                    if b < 360 then
                      (13, 3903082526988645)
                    else
                      (12, 77755474908689)
              else
                if b < 364 then
                  if b < 362 then
                    (45, 1111977386950940336851634181761664689456881395449220536)
                  else
                    if b < 363 then
                      (5, 166979)
                    else
                      (28, 2856761260373500598638321851590209)
                else
                  if b < 365 then
                    (5, 545873)
                  else
                    if b < 366 then
                      (0, 0)
                    else
                      (6, 8082740)
          else
            if b < 378 then
              if b < 372 then
                if b < 369 then
                  if b < 368 then
                    (5, 543861)
                  else
                    (7, 17450325)
                else
                  if b < 370 then
                    (39, 7286059006647399113584794752252594021832462420)
                  else
                    if b < 371 then
                      (15, 633790691819589657)
                    else
                      (53, 855565771287939693963672038339777308322197986705303764427216482)
              else
                if b < 375 then
                  if b < 373 then
                    (65, 1358993070034887643134084316056484938065151823358661796388446243370277454349531)
                  else
                    if b < 374 then
                      (56, 21253884511186197552514423294824104422770578893863855707571991104952)
                    else
                      (25, 101114383045635393268245423360)
                else
                  if b < 376 then
                    (66, 25673215534432205219743215435799856558329079922460471700834757474502734661045689)
                  else
                    if b < 377 then
                      (8, 3162094600)
                    else
                      (20, 943445775188348336154200)
            else
              if b < 383 then
                if b < 380 then
                  if b < 379 then
                    (7, 129808556)
                  else
                    (17, 214174427966740419173)
                else
                  if b < 381 then
                    (25, 180342545559899730861788386644)
                  else
                    if b < 382 then
                      (7, 196875585)
                    else
                      (17, 26832531998535652963)
              else
                if b < 386 then
                  if b < 384 then
                    (58, 897125734194022652537651371274170330851255056833034294513482251785796)
                  else
                    if b < 385 then
                      (51, 21780705972986046464590235401202829154698778263951983062830521)
                    else
                      (26, 2651753057189936735493303980646)
                else
                  if b < 387 then
                    (79, 65624489474070991487379154551979799340935152116933346878549226925382787190627814351040252235185)
                  else
                    if b < 388 then
                      (49, 27744077809346986240297084311108511802299188169227643479585)
                    else
                      (0, 0)
        else
          if b < 410 then
            if b < 399 then
              if b < 394 then
                if b < 391 then
                  if b < 390 then
                    (39, 7286059006647399113584794752252594021826843397)
                  else
                    (23, 3974767718989820129769293019)
                else
                  if b < 392 then
                    (62, 215312166321119103294119205417315432015200074312695102394774126965326928665)
                  else
                    if b < 393 then
                      (81, 17677947566429985520458052280454478774527983171738834818692770800074721496872359200852528270302055)
                    else
                      (16, 13676824895455126785)
              else
                if b < 396 then
                  if b < 395 then
                    (46, 3857697666603872943015291514553086891535205610001491508)
                  else
                    (55, 219024837449712561654700041814982990930482135894772821773678564657)
                else
                  if b < 397 then
                    (15, 922635199151856400)
                  else
                    if b < 398 then
                      (39, 73052437096338713354562789781066090368930434489)
                    else
                      (16, 2624329403206025573)
            else
              if b < 404 then
                if b < 401 then
                  if b < 400 then
                    (9, 53613445384)
                  else
                    (15, 976641589065961609)
                else
                  if b < 402 then
                    (38, 3506909852576476885833802668565906017564511673)
                  else
                    if b < 403 then
                      (15, 854766768145977481)
                    else
                      (13, 1244087598712417)
              else
                if b < 407 then
                  if b < 405 then
                    (83, 7511963876564822697732869457256922669164742374949273904940503373298259380372312894821668310340732123)
                  else
                    if b < 406 then
                      (24, 62745010831281919576645098377)
                    else
                      (29, 40115896806844367477593579531167001)
                else
                  if b < 408 then
                    (52, 64721427015309162801523237042624219987792796130422187717058901)
                  else
                    if b < 409 then
                      (40, 1161709277619601427460195194054391375678673014193)
                    else
                      (0, 0)
          else
            if b < 421 then
              if b < 415 then
                if b < 412 then
                  if b < 411 then
                    (41, 3326732743032637091281392289292892830628101621030)
                  else
                    (26, 17102719270749206151734169022721)
                else
                  if b < 413 then
                    (20, 664907375423687640501689)
                  else
                    if b < 414 then
                      (73, 634705255502745263206982132342554156740440874184077938334895192021313918748291770826854)
                    else
                      (54, 13689052340607035103418752613436436933155168721299814117022176340)
              else
                if b < 418 then
                  if b < 416 then
                    (14, 33739121126876752)
                  else
                    if b < 417 then
                      (65, 1599980376483554717080533856891311274598464918083031426915190449075298295107001)
                    else
                      (27, 178569472761925747468687661062921)
                else
                  if b < 419 then
                    (45, 1224429765753946541478313172001778992244664906090415323)
                  else
                    if b < 420 then
                      (25, 606547423114202081088308792761)
                    else
                      (16, 13463683747151237145)
            else
              if b < 426 then
                if b < 423 then
                  if b < 422 then
                    (69, 62804686132373836643900419149327087973688261867759887091341293796934665234666312709)
                  else
                    (12, 171033455775161)
                else
                  if b < 424 then
                    (69, 15782402821174543201617445061722584762530362796496586700849287464716356108901484133)
                  else
                    if b < 425 then
                      (14, 3495887301846616)
                    else
                      (52, 32813492627336672886187447061102055830828193803064784848168259)
              else
                if b < 429 then
                  if b < 427 then
                    (7, 42742864)
                  else
                    if b < 428 then
                      (15, 782914802910061840)
                    else
                      (17, 234068624228686890203)
                else
                  if b < 430 then
                    (25, 913751227601874967397596364208)
                  else
                    if b < 431 then
                      (78, 7023415728649128708392421108961295778413230279244879136118697934792120083559599567170053735643)
                    else
                      (16, 2435645100838512209)
      else
        if b < 475 then
          if b < 453 then
            if b < 442 then
              if b < 437 then
                if b < 434 then
                  if b < 433 then
                    (54, 16568685315919145677189948682911800316874929462827212539744821590)
                  else
                    (68, 6565395275924793979179397260651105115569922699586126216014694514399900517076585912)
                else
                  if b < 435 then
                    (18, 734237143956706798661)
                  else
                    if b < 436 then
                      (50, 208878362130844651846599618735297273719026262116088227915078)
                    else
                      (14, 39580045752534235)
              else
                if b < 439 then
                  if b < 438 then
                    (31, 18431515248979762394519120596561978633)
                  else
                    (36, 3508555588818010567606771941930749659591782)
                else
                  if b < 440 then
                    (17, 46435346584171847702)
                  else
                    if b < 441 then
                      (25, 180342543451566238429946929200)
                    else
                      (29, 13070388098715592022783424501933606)
            else
              if b < 447 then
                if b < 444 then
                  if b < 443 then
                    (67, 74618725014792473268758095093326892408200467956366534972611778567943774630950244)
                  else
                    (21, 1798509491470946961589781)
                else
                  if b < 445 then
                    (14, 38225167328371972)
                  else
                    if b < 446 then
                      (27, 42182649340460725717876787798352)
                    else
                      (0, 0)
              else
                if b < 450 then
                  if b < 448 then
                    (26, 2636415581583632812595864167779)
                  else
                    if b < 449 then
                      (65, 1363616322296459779169483473335885975388599840782841746338234817095420554005937)
                    else
                      (13, 2193377594461624)
                else
                  if b < 451 then
                    (45, 1219279323325548748278966059118016151383517728702746040)
                  else
                    if b < 452 then
                      (56, 3835461719522051181435868973535111248031473733392284224954402422886)
                    else
                      (41, 19683791823706350089116041401867241364524038937481)
          else
            if b < 464 then
              if b < 458 then
                if b < 455 then
                  if b < 454 then
                    (26, 10491384299616312185674707322212)
                  else
                    (12, 49282149798342)
                else
                  if b < 456 then
                    (76, 15864482637164872756329550052320329978794832033249810142783446204322143768232299365809838873)
                  else
                    if b < 457 then
                      (4, 46468)
                    else
                      (42, 48633283500290627555595622103497682539520070150229)
              else
                if b < 461 then
                  if b < 459 then
                    (0, 0)
                  else
                    if b < 460 then
                      (14, 44047249778429368)
                    else
                      (24, 57904967401526936889294960409)
                else
                  if b < 462 then
                    (42, 321150552719676467459197503444596199558697613020601)
                  else
                    if b < 463 then
                      (14, 61569444832740571)
                    else
                      (24, 39698729000826462887521772629)
            else
              if b < 469 then
                if b < 466 then
                  if b < 465 then
                    (34, 75489326772926809120894996286381924306361)
                  else
                    (53, 4007284605068770180743068066588827545853584600620177106883894153)
                else
                  if b < 467 then
                    (15, 899243110734027545)
                  else
                    if b < 468 then
                      (55, 465468386128221207102492087657660149296814936350842047232288904790)
                    else
                      (58, 5064767917340699301626557034323154965871767379204068694734149544893321)
              else
                if b < 472 then
                  if b < 470 then
                    (70, 932194549309023361498370412230771333130878831529590143839046042981742222148032810424)
                  else
                    if b < 471 then
                      (20, 565939498788157633226121)
                    else
                      (25, 655711518726019511604663948625)
                else
                  if b < 473 then
                    (66, 2364461330707167324449800447905637907759997525006823011990246147217929518994997)
                  else
                    if b < 474 then
                      (28, 820516655512642834773308596438101)
                    else
                      (57, 67865335054004820693770029805206734097919711079739257701642265846276)
        else
          if b < 497 then
            if b < 486 then
              if b < 480 then
                if b < 477 then
                  if b < 476 then
                    (56, 14301587679115962824482478436100724431443465334405798458160849112504)
                  else
                    (16, 2410657587477755237)
                else
                  if b < 478 then
                    (13, 2477364353177120)
                  else
                    if b < 479 then
                      (19, 8514782222395440972368)
                    else
                      (39, 44172841055530291824965601218762600987924385208)
              else
                if b < 483 then
                  if b < 481 then
                    (27, 235514782192995469088586320424985)
                  else
                    if b < 482 then
                      (67, 37831381291314677191196807166490206524159960400109168191843938353101930100043846)
                    else
                      (43, 851643582216355095368036426058994454853700681029200)
                else
                  if b < 484 then
                    (66, 16310339165511078476220670103115023891457112592857598606326220366987915669330713)
                  else
                    if b < 485 then
                      (28, 2844988456071566503112911550959032)
                    else
                      (42, 48633283500290627555595622103497682539520068052324)
            else
              if b < 491 then
                if b < 488 then
                  if b < 487 then
                    (37, 168428027659742126544815484415880104851670235)
                  else
                    (16, 4707505698107106897)
                else
                  if b < 489 then
                    (21, 10624463700190812669532953)
                  else
                    if b < 490 then
                      (14, 52303048672961800)
                    else
                      (48, 2128396030556154089274030878070649569654831997970144054705)
              else
                if b < 494 then
                  if b < 492 then
                    (80, 1808264262766443999302577196844033841178027461877940955801430472972441625531144523415916776541624)
                  else
                    if b < 493 then
                      (12, 40044089205058)
                    else
                      (39, 73092857877575783950883750197184480387696446897)
                else
                  if b < 495 then
                    (28, 414164512986724775376744069053265)
                  else
                    if b < 496 then
                      (26, 11149984247941427912976323424281)
                    else
                      (11, 11878215607560)
          else
            if b < 508 then
              if b < 502 then
                if b < 499 then
                  if b < 498 then
                    (13, 2772680583808219)
                  else
                    (13, 359230452687893)
                else
                  if b < 500 then
                    (68, 5146360989954607411868358796719064088214134354321243733911669750032101423624543113)
                  else
                    if b < 501 then
                      (31, 3389786874225447898054163361977230933)
                    else
                      (25, 999491339687678299817620527993)
              else
                if b < 505 then
                  if b < 503 then
                    (41, 12095742567018054600503501285590590948563822036549)
                  else
                    if b < 504 then
                      (26, 13755012062949748889768469781264)
                    else
                      (24, 38390406746584852628559121841)
                else
                  if b < 506 then
                    (26, 13694631656970326586403428227848)
                  else
                    if b < 507 then
                      (30, 149793637935826683019821647450367040)
                    else
                      (43, 2801429247536358775349149761406246984905405382318985)
            else
              if b < 513 then
                if b < 510 then
                  if b < 509 then
                    (24, 40981970036694363862815098180)
                  else
                    (13, 594639918088534)
                else
                  if b < 511 then
                    (30, 687563363480502237896723223139148902)
                  else
                    if b < 512 then
                      (41, 12838645675847695061977020380093529428476496465329)
                    else
                      (29, 11818928935783210371403017321796913)
              else
                if b < 516 then
                  if b < 514 then
                    (60, 488078978452785680458702743307715780361126612180402890422521034734391301)
                  else
                    if b < 515 then
                      (23, 2703978892707196797680343929)
                    else
                      (26, 2650546047867190332083935776868)
                else
                  if b < 517 then
                    (41, 18804161903138753494680701641967636701258948336409)
                  else
                    if b < 518 then
                      (79, 71368636543203246154120979239489050924638739864916206816285052878396517650394596108217081977625)
                    else
                      (58, 550519053523234865732910215832675088998203184849376289118798624392448)
    else
      if b < 606 then
        if b < 562 then
          if b < 540 then
            if b < 529 then
              if b < 524 then
                if b < 521 then
                  if b < 520 then
                    (58, 5809498957370039252229085474490209345229500919518277783173252727721401)
                  else
                    (28, 4467506732471143537602449069067705)
                else
                  if b < 522 then
                    (25, 159810688911559602197532788242)
                  else
                    if b < 523 then
                      (16, 1715192303792292929)
                    else
                      (17, 163101313071704431369)
              else
                if b < 526 then
                  if b < 525 then
                    (16, 10149913135088458633)
                  else
                    (16, 14753186304720427801)
                else
                  if b < 527 then
                    (49, 27744077809346986240297084311108511802305767906503469127236)
                  else
                    if b < 528 then
                      (41, 12095742567018054600503501285590588583620338103829)
                    else
                      (50, 443905244949551779844753348977736188836876208725614085563718)
            else
              if b < 534 then
                if b < 531 then
                  if b < 530 then
                    (74, 10155284088043924211311714117480866507847053986945247013358323072341022699691193339561477)
                  else
                    (45, 241106104162742058938455719659567698790851594903642467)
                else
                  if b < 532 then
                    (15, 562270833249096800)
                  else
                    if b < 533 then
                      (29, 22949363808901891650817463421370432)
                    else
                      (15, 562270833249096800)
              else
                if b < 537 then
                  if b < 535 then
                    (43, 778132536004650040889529953655962663039394075009381)
                  else
                    if b < 536 then
                      (40, 755983910438628412531468830349415325448526980421)
                    else
                      (42, 300566072844151020321911967360748867252231616875961)
                else
                  if b < 538 then
                    (42, 291647987842649296932836452278211122492388510325641)
                  else
                    if b < 539 then
                      (15, 318486429940732006)
                    else
                      (44, 70256960858463419483816945197159577513180609411829176)
          else
            if b < 551 then
              if b < 545 then
                if b < 542 then
                  if b < 541 then
                    (40, 755983910438628412531468830349415325448515503173)
                  else
                    (25, 1096770431875469952242040929712)
                else
                  if b < 543 then
                    (54, 58326615040532844164597882975317807538133193917229263146130398089)
                  else
                    if b < 544 then
                      (56, 3504397399195400986475200669039731935047276350496968578745428100451)
                    else
                      (29, 56077999444863161251292397858475441)
              else
                if b < 548 then
                  if b < 546 then
                    (26, 10491384299632389964116151047761)
                  else
                    if b < 547 then
                      (27, 173417958092562098119589983269001)
                    else
                      (16, 13531854222498221497)
                else
                  if b < 549 then
                    (34, 6948527600837265222299203719690394624836)
                  else
                    if b < 550 then
                      (73, 4409338949171406727093185966231429395933775342744757719716920073114303828929197545751771)
                    else
                      (12, 173502482244872)
            else
              if b < 556 then
                if b < 553 then
                  if b < 552 then
                    (57, 317588058160163270276827951774679008295568928862265733172019687906185)
                  else
                    (56, 2150465052825136194269180530596384330929384717032267389189261383169)
                else
                  if b < 554 then
                    (9, 53918846233)
                  else
                    if b < 555 then
                      (41, 6459671493933300077984361981765228661059784615460)
                    else
                      (40, 403729468370831254874022623860324426372764492097)
              else
                if b < 559 then
                  if b < 557 then
                    (41, 3326732743032637091281392289292890465684624257110)
                  else
                    if b < 558 then
                      (20, 157142614234276769652996)
                    else
                      (13, 3297975327199369)
                else
                  if b < 560 then
                    (68, 3925292883273364790243776196832942998355516366734992943208830862308416577480250470)
                  else
                    if b < 561 then
                      (77, 414639203330899486225431935543592674230480059883051306456848361677267803391171028766786192603)
                    else
                      (25, 931197915898386888162604331145)
        else
          if b < 584 then
            if b < 573 then
              if b < 567 then
                if b < 564 then
                  if b < 563 then
                    (53, 4751388501494204823827415434167924966824964731618451201510923033)
                  else
                    (71, 17095989568350606425476045220014263089468208381958161022359069297857222069786767580041)
                else
                  if b < 565 then
                    (35, 181173099205980552567525290338313818211589)
                  else
                    if b < 566 then
                      (16, 13666381376785330441)
                    else
                      (77, 74188619245979690949827912039751679792965027429182711776893938493978929781733702620685231204)
              else
                if b < 570 then
                  if b < 568 then
                    (31, 16661346475014598611633543296366039065)
                  else
                    if b < 569 then
                      (38, 4298144252025175458206302633603000869459086776)
                    else
                      (14, 39560186923161176)
                else
                  if b < 571 then
                    (19, 9821413401759452647777)
                  else
                    if b < 572 then
                      (35, 720962439001682674914807157849704471347238)
                    else
                      (8, 2882370832)
            else
              if b < 578 then
                if b < 575 then
                  if b < 574 then
                    (15, 566463749991452081)
                  else
                    (65, 263570922406514153201683513002790277088269829978567002288847968204002699203680)
                else
                  if b < 576 then
                    (56, 3504397399195400986475200669039728025854595002243688818223595498342)
                  else
                    if b < 577 then
                      (31, 11365161767849257308070994043507592633)
                    else
                      (13, 3881807981127248)
              else
                if b < 581 then
                  if b < 579 then
                    (27, 51282290967343523915303927178533)
                  else
                    if b < 580 then
                      (17, 235951973297857889499)
                    else
                      (16, 2381509634402177632)
                else
                  if b < 582 then
                    (28, 4495650083386475666055046318895241)
                  else
                    if b < 583 then
                      (43, 4805038003355307687774300074973487094782446205423033)
                    else
                      (13, 3751827535147265)
          else
            if b < 595 then
              if b < 589 then
                if b < 586 then
                  if b < 585 then
                    (28, 2830462273008151956385978044493849)
                  else
                    (23, 4284041692316560154975143131)
                else
                  if b < 587 then
                    (14, 39931638169226673)
                  else
                    if b < 588 then
                      (11, 3080134870645)
                    else
                      (64, 77589079212125582627130648396703625541755882006033806123203093387692052860345)
              else
                if b < 592 then
                  if b < 590 then
                    (11, 14074018096521)
                  else
                    if b < 591 then
                      (13, 2383568463255909)
                    else
                      (18, 2561583738501328954632)
                else
                  if b < 593 then
                    (66, 21369880580248923058234103527020543868031697146209479121438901463703137863206107)
                  else
                    if b < 594 then
                      (68, 986400176323408950101090316357661547658147674781036668803080466548311229477310560)
                    else
                      (51, 3657781333467532330928677533660061393881282196291199649080854)
            else
              if b < 600 then
                if b < 597 then
                  if b < 596 then
                    (47, 202932885727256377932440949824631032040859017807521005910)
                  else
                    (31, 15352564262278861703255856713652260273)
                else
                  if b < 598 then
                    (13, 3609033185771601)
                  else
                    if b < 599 then
                      (21, 15100878563792532835553417)
                    else
                      (39, 44195571577358243593386491179164435672681434553)
              else
                if b < 603 then
                  if b < 601 then
                    (18, 3976197633043108573321)
                  else
                    if b < 602 then
                      (41, 3326732743032637091281392289292947089243969578593)
                    else
                      (25, 695680272086735580365926190521)
                else
                  if b < 604 then
                    (55, 465468386128221207102492087657660149296814936349837186079694284357)
                  else
                    if b < 605 then
                      (13, 2047311506072608)
                    else
                      (34, 12393045213195074689691485052156787037714)
      else
        if b < 649 then
          if b < 627 then
            if b < 616 then
              if b < 611 then
                if b < 608 then
                  if b < 607 then
                    (13, 2183374489347465)
                  else
                    (66, 8188606446561731162762635004266102113722844325705183797742796849461110059918432)
                else
                  if b < 609 then
                    (39, 71128860422937205586138588540635741217731136945)
                  else
                    if b < 610 then
                      (24, 21886220807067355627749859684)
                    else
                      (20, 896323639509651324479057)
              else
                if b < 613 then
                  if b < 612 then
                    (24, 68658286733869405208899714487)
                  else
                    (40, 229936699068777140558677405986373835297636107094)
                else
                  if b < 614 then
                    (25, 1008569697485889562826271378865)
                  else
                    if b < 615 then
                      (18, 2209847513984012800137)
                    else
                      (16, 13658251944897039800)
            else
              if b < 621 then
                if b < 618 then
                  if b < 617 then
                    (54, 90704969369261909281056431567595991193469641722323458901080857481)
                  else
                    (85, 1649079686460532672084511295244492765522521633640790016290599457262137573588850452236818043364926872457)
                else
                  if b < 619 then
                    (51, 20066724653418913758646003104557505217007330423789479180389816)
                  else
                    if b < 620 then
                      (13, 2107597987927334)
                    else
                      (14, 39637828253349393)
              else
                if b < 624 then
                  if b < 622 then
                    (42, 48633283500290627555595622103497700091514830869270)
                  else
                    if b < 623 then
                      (68, 4194129476786050928783630872226415158423873370134995653309773179143842432503044889)
                    else
                      (16, 2917445688411702534)
                else
                  if b < 625 then
                    (16, 1715192309788005905)
                  else
                    if b < 626 then
                      (40, 403729468370831254874022623860323259271934402854)
                    else
                      (52, 202051966324448207558771078175933074834349818457580486036609929)
          else
            if b < 638 then
              if b < 632 then
                if b < 629 then
                  if b < 628 then
                    (42, 29843697691227746769243319305225719136458722653780)
                  else
                    (15, 610315504976643152)
                else
                  if b < 630 then
                    (18, 746255550873308893509)
                  else
                    if b < 631 then
                      (20, 665012402462741739488080)
                    else
                      (47, 309359763500184640559422669104644457021789563094965738377)
              else
                if b < 635 then
                  if b < 633 then
                    (40, 116576944106358385817356716036037965376793233252)
                  else
                    if b < 634 then
                      (15, 106060155684536417)
                    else
                      (15, 899837261597003913)
                else
                  if b < 636 then
                    (56, 7447494178051539313639873402522562388753990741754536498374669374550)
                  else
                    if b < 637 then
                      (16, 1677033251907810854)
                    else
                      (67, 347896016300532317917174878565572311093974926249215517967532405619184941890817457)
            else
              if b < 643 then
                if b < 640 then
                  if b < 639 then
                    (27, 172220917222680100363735973723568)
                  else
                    (41, 11217040369354049170913479042942202325755610137819)
                else
                  if b < 641 then
                    (13, 3301577814795545)
                  else
                    if b < 642 then
                      (10, 101036610308)
                    else
                      (8, 3433945976)
              else
                if b < 646 then
                  if b < 644 then
                    (43, 5062423827265995418437477911085141650960231505910665)
                  else
                    if b < 645 then
                      (26, 3111568161118818952203500610613)
                    else
                      (29, 56285735997876992394104603641138609)
                else
                  if b < 647 then
                    (26, 15829401072101896744139275390392)
                  else
                    if b < 648 then
                      (51, 4045089188456822675095202315164015018107884003637383496009284)
                    else
                      (35, 679120299767577151003427453799071995678136)
        else
          if b < 671 then
            if b < 660 then
              if b < 654 then
                if b < 651 then
                  if b < 650 then
                    (53, 5257482377516531406885999301342310938758347172577823893122731448)
                  else
                    (69, 87056160092162761816053207264042054375754484491258383791158444080945829730278759193)
                else
                  if b < 652 then
                    (75, 289799293929608167772765281405279999191269638395244967878491947242105194484403100660858949)
                  else
                    if b < 653 then
                      (40, 716652938823555103152003310620978868272345963401)
                    else
                      (46, 3488332112758190470627477201137581912945710185696342357)
              else
                if b < 657 then
                  if b < 655 then
                    (26, 3191012721059646403239980828259)
                  else
                    if b < 656 then
                      (22, 85493049938362518272197634)
                    else
                      (25, 195679173950784377524811333953)
                else
                  if b < 658 then
                    (41, 19705422844215422141390356781626626689339874102705)
                  else
                    if b < 659 then
                      (56, 7447494178051539313639873402522518621231379516630090901650436871492)
                    else
                      (76, 23527207381192510271479224342146259454065069301703917788937983963022571721606590493219937161)
            else
              if b < 665 then
                if b < 662 then
                  if b < 661 then
                    (26, 16211380683254839131972529311161)
                  else
                    (15, 105779161811277410)
                else
                  if b < 663 then
                    (19, 41778235531582301854601)
                  else
                    if b < 664 then
                      (17, 162262373524096004121)
                    else
                      (15, 524111745419075682)
              else
                if b < 668 then
                  if b < 666 then
                    (40, 1146321786555537748427737062486840639295638752689)
                  else
                    if b < 667 then
                      (30, 1067470156210531468792109821859419701)
                    else
                      (47, 187041051538625993745019855837977972729330997769762000312)
                else
                  if b < 669 then
                    (16, 10149254854481919115)
                  else
                    if b < 670 then
                      (20, 887133631864564555290193)
                    else
                      (25, 622853938469540109540392979889)
          else
            if b < 682 then
              if b < 676 then
                if b < 673 then
                  if b < 672 then
                    (9, 59237718809)
                  else
                    (22, 247440435057056111401501915)
                else
                  if b < 674 then
                    (30, 206669382995312616568036560881215014)
                  else
                    if b < 675 then
                      (14, 53228284767785217)
                    else
                      (18, 2523589698279975571593)
              else
                if b < 679 then
                  if b < 677 then
                    (13, 2477364249060950)
                  else
                    if b < 678 then
                      (42, 207108190790579296505517436201247827811770040714459)
                    else
                      (40, 403729468370831254874022623860342890874595005461)
                else
                  if b < 680 then
                    (49, 15801129642409463574590634043609428394665956850014663044101)
                  else
                    if b < 681 then
                      (22, 40484135748693953134200342)
                    else
                      (52, 221442362683809106887662607823245147980110231067539408506867128)
            else
              if b < 687 then
                if b < 684 then
                  if b < 683 then
                    (68, 3925292883273364790243776196832942998355516366734992943208830862308416577140712756)
                  else
                    (18, 4092568713309727856216)
                else
                  if b < 685 then
                    (16, 14544337002459189273)
                  else
                    if b < 686 then
                      (15, 925715704315370249)
                    else
                      (29, 22949367219577555851923690263434849)
              else
                if b < 690 then
                  if b < 688 then
                    (54, 84222119317761206997878891865733866534260243908108923657508936473)
                  else
                    if b < 689 then
                      (84, 110720471642507140848853038031110558290936513128384289210749541737532452610391170106773245831250202041)
                    else
                      (16, 1694597547372602950)
                else
                  if b < 691 then
                    (27, 276015160894313741187369848737929)
                  else
                    if b < 692 then
                      (30, 172780131550362866855848403527885120)
                    else
                      (69, 19102393603786873156802072343891684456499319796829832952988615313409705863674090576)

def forward1Blocks (b : Nat) : Nat :=
  if b < 1 then
    185364397679550396860304084232071293931543531229783369346362607006827173429788002767307622903110538119717798405609812777585043098750848600203121069082863338470121617618338042852823628999106404694883015292488335318028920097053523532798910706610018101190809193464657209724977109717498882362025999985755370588737885689626011252864191122045731494899559463634971286744433253178191628088641189930384980380244202083781425541798390513675841450607620482309282486342860440265629674778470864393228291005545981946702465639553363673381531589406166708896902429818692169297412280456955709314147076969161213790795402362179147683867066442861883325816234332131008016989235170270231275334099720736097290869922010196984710141300903499204935617763581834319892859050072727862058786091634268162
  else
    if b < 2 then
      235818720213182809195532627154513233695410053609458825032909767753576557915208706054512076329876446910359224179261906593175574798061872791155170194015072432353947923661115873451095743146568584963515518187085536996197745580822044819441187667497501705561691264481030445410498542402775431056843026649514073684278079775997653186595778409062572628620537701233980647335110720254839495086881217328870946797845135287730601546658485933308720399142723165362556563167186689409444814267470666063515524556086758342009511309658055520097666304544405500612651319723267513635606005157519846251558876601106912421018148993806960537443170591726806282585492360789544619845389138627643126110479600585530267839829105978314877590551283708970001582905057683863724633657934978116219796622572659955
    else
      33769627576925674511160575226698283160275647101304207524327691004797326505210814146472554581732982798213245424615817119689022911469684358058048025999203823444338119634741447137174302917909148216375216944372338977067415575814256908256621927339920536431047272964258354414093884364727310219906159836363360867291061598208052734936554477399107461347218395191467630544042040407445464619115633032789209808156398696487375312312154173328582829370110748762760967609124986275242377950008398877716126088365452677653491937270377428560010542179113581140823441

def backward1Blocks (b : Nat) : Nat :=
  if b < 1 then
    27584632654211837005169938952832280810387739977686086628940990615644221378644095141104522787769333115704837115858302298218427059659781254424299084074816376916358610626431022008668159673056526454310121668556586124718309684953750128345687505347383991556509312942863321339869575615482857829217959120016733071964751623931585074891357030986941204844305829377992841172400605161582386104016726931411059278736176096641112160404532475859533777863407472380483064506277485554155678914478866396329739264007421282760841098203689004666490351336529116518763912927802153818725654345716934931382150733718598194675141503594661209944435004676132071731105906169801122545068686005187388667472491782853557745970117007368025028337588010246380386097374408098782253668309707010995115874957934620
  else
    if b < 2 then
      140551497968087648062323641940761739574184062151720154629034758595616160760726829377258964097638102507089388807804366127089900041864403726531866890064396481979189545520563943495703603908924684668674174555992666880225609447828181303010335760338782080903422094003748215510825464617894132215266087542106069581502789955086825064041173965321943205258592505948712523442879738878289657727928083701136396818749852114126505980178019323846121719312221596758164623536380625164919790521014552315124370018572656067039830977843266941279275950618286999586541784681909274270380339535776300308906554297725758009223797838075690476072260916782020837200630004997512585482534031466096166434770058953254422175721926165235993279110675557136124818313080629020142747313014785576944616799859728821
    else
      47703391142291453598859287803356227010253515670334326782096299691157238567793179676529034232542462712544800862710443798416783999053732085330318912859406164935802665454427470772666198689552840497118431851747133236935715196786693285117093304581655302499649550004937846970615401905266075409672706648865948620795075740911452343518478263833539947677456756443017473172617816563565527043052712930614916880020816629739908517510173938648213830545125568418572298386200319410346290528638514210512806162835373835988033372873082470537645517695627941202506918

def factorCode1 (b : Nat) : Nat × Nat :=
  if b < 346 then
    if b < 173 then
      if b < 86 then
        if b < 43 then
          if b < 21 then
            if b < 10 then
              if b < 5 then
                (0, 0)
              else
                if b < 7 then
                  if b < 6 then
                    (4, 6913)
                  else
                    (2, 177)
                else
                  if b < 8 then
                    (3, 2164)
                  else
                    (0, 0)
            else
              if b < 15 then
                if b < 12 then
                  (0, 0)
                else
                  if b < 13 then
                    (0, 0)
                  else
                    if b < 14 then
                      (0, 0)
                    else
                      (2, 67)
              else
                if b < 18 then
                  if b < 16 then
                    (4, 34724)
                  else
                    if b < 17 then
                      (4, 43784)
                    else
                      (0, 0)
                else
                  (0, 0)
          else
            if b < 32 then
              if b < 26 then
                if b < 23 then
                  (0, 0)
                else
                  if b < 24 then
                    (0, 0)
                  else
                    if b < 25 then
                      (2, 171)
                    else
                      (3, 1032)
              else
                if b < 29 then
                  (0, 0)
                else
                  if b < 30 then
                    (0, 0)
                  else
                    if b < 31 then
                      (0, 0)
                    else
                      (3, 432)
            else
              if b < 37 then
                if b < 34 then
                  if b < 33 then
                    (8, 676529492)
                  else
                    (0, 0)
                else
                  if b < 35 then
                    (9, 54958698521)
                  else
                    if b < 36 then
                      (6, 282649)
                    else
                      (0, 0)
              else
                if b < 40 then
                  if b < 38 then
                    (9, 10615071829)
                  else
                    if b < 39 then
                      (0, 0)
                    else
                      (7, 141981204)
                else
                  if b < 41 then
                    (0, 0)
                  else
                    if b < 42 then
                      (0, 0)
                    else
                      (38, 1577068235823559589351650874454613476296110166)
        else
          if b < 64 then
            if b < 53 then
              if b < 48 then
                if b < 45 then
                  (0, 0)
                else
                  if b < 46 then
                    (0, 0)
                  else
                    if b < 47 then
                      (0, 0)
                    else
                      (3, 1864)
              else
                if b < 50 then
                  if b < 49 then
                    (2, 116)
                  else
                    (0, 0)
                else
                  (0, 0)
            else
              if b < 58 then
                (0, 0)
              else
                if b < 61 then
                  (0, 0)
                else
                  if b < 62 then
                    (20, 961510903969760873041329)
                  else
                    if b < 63 then
                      (24, 6319649038084449077638284134)
                    else
                      (0, 0)
          else
            if b < 75 then
              if b < 69 then
                if b < 66 then
                  (0, 0)
                else
                  if b < 67 then
                    (0, 0)
                  else
                    if b < 68 then
                      (58, 3569151131212172614007291449525283031576103117911046912792216511841499)
                    else
                      (0, 0)
              else
                if b < 72 then
                  if b < 70 then
                    (0, 0)
                  else
                    if b < 71 then
                      (13, 3111379340905913)
                    else
                      (0, 0)
                else
                  (0, 0)
            else
              if b < 80 then
                if b < 77 then
                  if b < 76 then
                    (0, 0)
                  else
                    (16, 12383168143278005017)
                else
                  if b < 78 then
                    (0, 0)
                  else
                    if b < 79 then
                      (61, 22277052531783974651537450763464728979986610499568277724158004777506364185)
                    else
                      (14, 62431609409130760)
              else
                if b < 83 then
                  if b < 81 then
                    (0, 0)
                  else
                    if b < 82 then
                      (27, 49785090573878353802160448300609)
                    else
                      (31, 16988461652709420761190134145232460681)
                else
                  if b < 84 then
                    (0, 0)
                  else
                    if b < 85 then
                      (0, 0)
                    else
                      (41, 18615541864313572032959745515078020234144054041481)
      else
        if b < 129 then
          if b < 107 then
            if b < 96 then
              if b < 91 then
                if b < 88 then
                  (0, 0)
                else
                  if b < 89 then
                    (54, 8400254112598188258863986447642209449414286924937360630169617985)
                  else
                    if b < 90 then
                      (0, 0)
                    else
                      (78, 7095902330388276544762726109555585120016125148522010570147582904669367497561133371577168354185)
              else
                if b < 93 then
                  if b < 92 then
                    (0, 0)
                  else
                    (14, 57867671806697494)
                else
                  if b < 94 then
                    (58, 1085845360864077131100320476883307745566718787951598604990069078385238)
                  else
                    (0, 0)
            else
              if b < 101 then
                if b < 98 then
                  if b < 97 then
                    (2, 139)
                  else
                    (17, 41989270498928251973)
                else
                  if b < 99 then
                    (15, 91962994023882822)
                  else
                    (0, 0)
              else
                if b < 104 then
                  if b < 102 then
                    (10, 169729197668)
                  else
                    if b < 103 then
                      (7, 213061769)
                    else
                      (0, 0)
                else
                  if b < 105 then
                    (46, 6773456496422604062572530349391416731332953642577083238)
                  else
                    if b < 106 then
                      (23, 2561373124860627154446345539)
                    else
                      (50, 1373060528535942234443316782158459504954396232216845188728027)
          else
            if b < 118 then
              if b < 112 then
                if b < 109 then
                  if b < 108 then
                    (0, 0)
                  else
                    (14, 11263810735597122)
                else
                  if b < 110 then
                    (0, 0)
                  else
                    if b < 111 then
                      (0, 0)
                    else
                      (8, 2360545305)
              else
                if b < 115 then
                  if b < 113 then
                    (15, 201982859882529621)
                  else
                    if b < 114 then
                      (0, 0)
                    else
                      (13, 1244087598712417)
                else
                  if b < 116 then
                    (29, 45286618961217099463644107420075227)
                  else
                    if b < 117 then
                      (7, 41966341)
                    else
                      (19, 35357568090172327068891)
            else
              if b < 123 then
                if b < 120 then
                  if b < 119 then
                    (27, 276015381957775905439584310658267)
                  else
                    (0, 0)
                else
                  if b < 121 then
                    (77, 74188619245979690949827912039751679792965027429182711776893938493978929773600448266399807025)
                  else
                    if b < 122 then
                      (56, 13109936965324033166980239283053405552916461405785611944491843866041)
                    else
                      (0, 0)
              else
                if b < 126 then
                  if b < 124 then
                    (0, 0)
                  else
                    if b < 125 then
                      (7, 125486217)
                    else
                      (0, 0)
                else
                  if b < 127 then
                    (0, 0)
                  else
                    if b < 128 then
                      (62, 324190675300738514972633470499402391695088014467264443884550288705247530424)
                    else
                      (0, 0)
        else
          if b < 151 then
            if b < 140 then
              if b < 134 then
                if b < 131 then
                  (0, 0)
                else
                  if b < 132 then
                    (0, 0)
                  else
                    if b < 133 then
                      (40, 1264445010466451367632120269071452447635232804280)
                    else
                      (19, 36777927671982412605009)
              else
                if b < 137 then
                  if b < 135 then
                    (5, 742537)
                  else
                    if b < 136 then
                      (19, 40684025190534310844773)
                    else
                      (8, 3083584264)
                else
                  if b < 138 then
                    (25, 180342545836600891967436771670)
                  else
                    if b < 139 then
                      (21, 2751808861811278482851329)
                    else
                      (28, 4390947841044051345381620613176201)
            else
              if b < 145 then
                if b < 142 then
                  if b < 141 then
                    (0, 0)
                  else
                    (20, 584605912370766516902793)
                else
                  if b < 143 then
                    (19, 40062024577855016216153)
                  else
                    if b < 144 then
                      (27, 89645952378523014261005716510288)
                    else
                      (25, 115244847419892097305347318864)
              else
                if b < 148 then
                  if b < 146 then
                    (56, 23225237602470317329106738866102457998621700292168590422337965579033)
                  else
                    if b < 147 then
                      (11, 11756748219984)
                    else
                      (15, 180220971769286736)
                else
                  (0, 0)
          else
            if b < 162 then
              if b < 156 then
                if b < 153 then
                  if b < 152 then
                    (41, 3326732743032637091281392289292892830628119316050)
                  else
                    (26, 14858641048138853670676631902984)
                else
                  (0, 0)
              else
                if b < 159 then
                  if b < 157 then
                    (25, 200321449098104553555681883669)
                  else
                    if b < 158 then
                      (14, 11203569584055396)
                    else
                      (19, 41760856140621325290936)
                else
                  if b < 160 then
                    (15, 182269175267742004)
                  else
                    if b < 161 then
                      (27, 179832053127266513114849008647600)
                    else
                      (27, 279555791437363825465783589591945)
            else
              if b < 167 then
                if b < 164 then
                  if b < 163 then
                    (26, 1843917560639230514960361940566)
                  else
                    (0, 0)
                else
                  if b < 165 then
                    (60, 913928468542491269820317671828191494186296213123712908292382690667606086)
                  else
                    if b < 166 then
                      (53, 1818235883313364090244109717412724272761565277164483912302669894)
                    else
                      (42, 48633283500290627555595622103497720698571954980432)
              else
                if b < 170 then
                  if b < 168 then
                    (15, 150815158056584517)
                  else
                    if b < 169 then
                      (29, 66482826364836326812255992471692881)
                    else
                      (39, 47248994402414275783216801896838308781730848804)
                else
                  if b < 171 then
                    (10, 530373639607)
                  else
                    if b < 172 then
                      (52, 351502698437048307396004617459055117277961893349712359891946937)
                    else
                      (33, 4292813480107384356164752416925405957560)
    else
      if b < 259 then
        if b < 216 then
          if b < 194 then
            if b < 183 then
              if b < 178 then
                if b < 175 then
                  if b < 174 then
                    (7, 143377433)
                  else
                    (16, 10149254785762415360)
                else
                  if b < 176 then
                    (7, 45428740)
                  else
                    if b < 177 then
                      (43, 4789779596930725033421062644093318399411197495496113)
                    else
                      (35, 755720265253576573980196873327905100585753)
              else
                if b < 180 then
                  if b < 179 then
                    (0, 0)
                  else
                    (64, 31986743931881762354541542985414461381729860647285874209932800193207471530340)
                else
                  if b < 181 then
                    (0, 0)
                  else
                    if b < 182 then
                      (17, 155959740516387735109)
                    else
                      (0, 0)
            else
              if b < 188 then
                if b < 185 then
                  if b < 184 then
                    (0, 0)
                  else
                    (52, 353103937034171485294517505102204132964399561382906567541971849)
                else
                  if b < 186 then
                    (24, 12464893441804470935220540464)
                  else
                    if b < 187 then
                      (8, 3430530049)
                    else
                      (18, 3464121184779120748120)
              else
                if b < 191 then
                  if b < 189 then
                    (0, 0)
                  else
                    if b < 190 then
                      (30, 984205019579819355389270775250969857)
                    else
                      (81, 20271469280459634673520632300475985832209372893614099597971053609225072486232442960596625220718009)
                else
                  if b < 192 then
                    (0, 0)
                  else
                    if b < 193 then
                      (0, 0)
                    else
                      (47, 31293385150276825796306082783796403475560236122953377123)
          else
            if b < 205 then
              if b < 199 then
                if b < 196 then
                  if b < 195 then
                    (30, 1131228319464361316432612968846347704)
                  else
                    (26, 2636415581711755159959230309204)
                else
                  if b < 197 then
                    (25, 919740246112245840341825859721)
                  else
                    (0, 0)
              else
                if b < 202 then
                  if b < 200 then
                    (21, 3043186873829828689540357)
                  else
                    if b < 201 then
                      (15, 541676042765829222)
                    else
                      (13, 3601502218243505)
                else
                  if b < 203 then
                    (23, 3574367986201555232165481913)
                  else
                    if b < 204 then
                      (24, 42354554583823961815049416969)
                    else
                      (0, 0)
            else
              if b < 210 then
                if b < 207 then
                  if b < 206 then
                    (0, 0)
                  else
                    (19, 10749253459192234520929)
                else
                  if b < 208 then
                    (0, 0)
                  else
                    if b < 209 then
                      (25, 576266960646282370768578150979)
                    else
                      (0, 0)
              else
                if b < 213 then
                  if b < 211 then
                    (26, 3205143185596105099932673466434)
                  else
                    if b < 212 then
                      (59, 8808304856371757851726563453322790219485750515039350882136248600278340)
                    else
                      (27, 51282290967725500872822889001297)
                else
                  if b < 214 then
                    (19, 11940088814483069427808)
                  else
                    if b < 215 then
                      (77, 384083582215761215581964604946550618473148901787535781267552654189857215051201746267784891832)
                    else
                      (22, 241391968680781102274596273)
        else
          if b < 237 then
            if b < 226 then
              if b < 221 then
                if b < 218 then
                  if b < 217 then
                    (25, 929644446538293655876401421193)
                  else
                    (41, 1865231105701734173077707456576625910528348677638)
                else
                  if b < 219 then
                    (69, 62804686132373836643900419149327087973688261867759887091341293797473286890871678470)
                  else
                    if b < 220 then
                      (50, 443905244949551779844753348977736188836876208725613983786561)
                    else
                      (32, 27142684931484606540146450520502481089)
              else
                if b < 223 then
                  if b < 222 then
                    (15, 913625735401702619)
                  else
                    (67, 37831381291314677191196807166490206524159960400109168191843938355486871494284865)
                else
                  if b < 224 then
                    (0, 0)
                  else
                    if b < 225 then
                      (51, 22264015317184147383105393637206879278444091660122724807757233)
                    else
                      (8, 559641877)
            else
              if b < 231 then
                if b < 228 then
                  if b < 227 then
                    (14, 3495887301846616)
                  else
                    (6, 7849017)
                else
                  if b < 229 then
                    (18, 3759268443044325434969)
                  else
                    if b < 230 then
                      (15, 91962994008023094)
                    else
                      (69, 15782402821174543201617445061722584762530362796496586700849287464715189007977571589)
              else
                if b < 234 then
                  if b < 232 then
                    (16, 12508703751775080585)
                  else
                    if b < 233 then
                      (5, 136888)
                    else
                      (0, 0)
                else
                  if b < 235 then
                    (41, 11129594270859705389143438753792178334405656333753)
                  else
                    if b < 236 then
                      (46, 13298887093033755885137510821500901308650924839545396105)
                    else
                      (23, 1367888880942927978036466790)
          else
            if b < 248 then
              if b < 242 then
                if b < 239 then
                  if b < 238 then
                    (65, 1021204970614261686118299646395019224790854143088020147747194366174160551806171)
                  else
                    (16, 1677033251904249942)
                else
                  if b < 240 then
                    (17, 255794822196233755401)
                  else
                    if b < 241 then
                      (6, 2148165)
                    else
                      (9, 34549678661)
              else
                if b < 245 then
                  if b < 243 then
                    (11, 12901030301833)
                  else
                    if b < 244 then
                      (53, 855565771287939693963672038339777942147496034784668257196790837)
                    else
                      (81, 29175761072685462177104115221741456578762372102012991195645582251838611569763943907347937628652763)
                else
                  if b < 246 then
                    (53, 3404648857349497339950195222452996277013073972230739219909707270)
                  else
                    if b < 247 then
                      (10, 143751721040)
                    else
                      (8, 3368045577)
            else
              if b < 253 then
                if b < 250 then
                  if b < 249 then
                    (69, 80090122915076507909494634875347493639799423224011750802582186461200903858781739801)
                  else
                    (8, 3167177841)
                else
                  if b < 251 then
                    (7, 209373953)
                  else
                    if b < 252 then
                      (14, 11203569686753620)
                    else
                      (7, 196695048)
              else
                if b < 256 then
                  if b < 254 then
                    (46, 19591554849755942021366011654789844012383819013659053497)
                  else
                    if b < 255 then
                      (31, 17070598523490341243074661221281356569)
                    else
                      (40, 1247276893932434899504282252544832694230140115737)
                else
                  if b < 257 then
                    (56, 22930833728220430791210886078238121218849477755598439504179391122865)
                  else
                    if b < 258 then
                      (52, 327287025288367090137711434098575582390552532811257555940858761)
                    else
                      (13, 2495323658650843)
      else
        if b < 302 then
          if b < 280 then
            if b < 269 then
              if b < 264 then
                if b < 261 then
                  if b < 260 then
                    (68, 3612335079420481791632265300269511285882755988810855831221144492383842931023302065)
                  else
                    (23, 2357225249793921650751405488)
                else
                  if b < 262 then
                    (25, 1014410504615186812062719299000)
                  else
                    if b < 263 then
                      (25, 1084982879290180409153940205593)
                    else
                      (19, 9976906854638998804068)
              else
                if b < 266 then
                  if b < 265 then
                    (68, 4144066699160388835064189570135348031268092244407837622650510802047249626230555867)
                  else
                    (14, 9514238738837605)
                else
                  if b < 267 then
                    (66, 23372272629571294569467472476959224159458437815096296515479279153673450574709979)
                  else
                    if b < 268 then
                      (16, 1715192309788071190)
                    else
                      (68, 5918749484402288927446436349923098625055026018317325344134607646835042680312224649)
            else
              if b < 274 then
                if b < 271 then
                  if b < 270 then
                    (8, 2379922704)
                  else
                    (25, 993985778450661378071494908793)
                else
                  if b < 272 then
                    (15, 561468737259660681)
                  else
                    if b < 273 then
                      (80, 1842290983329681297894139714567643184489882911245624064350763484786150382660617627536710409968521)
                    else
                      (34, 69583163067401222117649530444960233817307)
              else
                if b < 277 then
                  if b < 275 then
                    (18, 746255550875076809314)
                  else
                    if b < 276 then
                      (41, 12095742567018054600503501285590588583620208058385)
                    else
                      (0, 0)
                else
                  if b < 278 then
                    (79, 64528686491544153277609318060554568349443212725686362064480980693182301331451076784769149717945)
                  else
                    if b < 279 then
                      (14, 60971810410358032)
                    else
                      (0, 0)
          else
            if b < 291 then
              if b < 285 then
                if b < 282 then
                  if b < 281 then
                    (44, 74586678289017582199788519428129336387163131287195064)
                  else
                    (20, 943492470235012721878608)
                else
                  if b < 283 then
                    (20, 896312686755357559432785)
                  else
                    if b < 284 then
                      (31, 18404371121168967874944297933410034953)
                    else
                      (40, 1077678897762787864062206438272007682210272398777)
              else
                if b < 288 then
                  if b < 286 then
                    (67, 260961572542319765778784214888831719203791312964293701486849475791162883694789851)
                  else
                    if b < 287 then
                      (19, 51316220151407380845157)
                    else
                      (19, 36243806691044636809573)
                else
                  if b < 289 then
                    (0, 0)
                  else
                    if b < 290 then
                      (25, 1092745468991649510450037840665)
                    else
                      (0, 0)
            else
              if b < 296 then
                if b < 293 then
                  if b < 292 then
                    (20, 890701383489367136292281)
                  else
                    (80, 1842290983329681297894139714567643184489882911245624064350763484786150382660617627536710409968521)
                else
                  if b < 294 then
                    (28, 674922389776847322734107636032866)
                  else
                    if b < 295 then
                      (21, 2751808861811278504945220)
                    else
                      (27, 220238459530861459225901705219505)
              else
                if b < 299 then
                  if b < 297 then
                    (51, 14142944452232749314718044287006892439576348187203060356894137)
                  else
                    if b < 298 then
                      (26, 2636415583459796040085139449425)
                    else
                      (13, 3568724796581456)
                else
                  if b < 300 then
                    (69, 19102393603786873156802072343891684456499319796829832952988615313393606305304109077)
                  else
                    if b < 301 then
                      (25, 925056577478723912243462647833)
                    else
                      (5, 890505)
        else
          if b < 324 then
            if b < 313 then
              if b < 307 then
                if b < 304 then
                  if b < 303 then
                    (14, 56088704942660489)
                  else
                    (26, 9867848831964481120313400118713)
                else
                  if b < 305 then
                    (0, 0)
                  else
                    if b < 306 then
                      (52, 346268795533744313630190249426376585128248202486238221361499577)
                    else
                      (27, 167862148852871047857651990221923)
              else
                if b < 310 then
                  if b < 308 then
                    (0, 0)
                  else
                    if b < 309 then
                      (16, 15820455301382606985)
                    else
                      (0, 0)
                else
                  if b < 311 then
                    (53, 5136934416223247450742819689064744230617244466696253498015632825)
                  else
                    if b < 312 then
                      (25, 1003907545706730540193905247451)
                    else
                      (42, 29843697691227746769243319305225756975554973939285)
            else
              if b < 318 then
                if b < 315 then
                  if b < 314 then
                    (23, 643656147801211109333421237)
                  else
                    (15, 129802094755730966)
                else
                  if b < 316 then
                    (25, 164775973848914246965204268293)
                  else
                    if b < 317 then
                      (54, 90799801074868845866492004175241294432227938983899830218901478281)
                    else
                      (43, 4766942298795768612378457786302940927965630472444697)
              else
                if b < 321 then
                  if b < 319 then
                    (26, 16228229529922935141334735761433)
                  else
                    if b < 320 then
                      (15, 91962995619792469)
                    else
                      (15, 106060636798402641)
                else
                  if b < 322 then
                    (35, 1102424220991244487603157581059275576331705)
                  else
                    if b < 323 then
                      (30, 206669382995312616568036560879355200)
                    else
                      (9, 10811147537)
          else
            if b < 335 then
              if b < 329 then
                if b < 326 then
                  if b < 325 then
                    (40, 229936699068777140558677405986373835297529407030)
                  else
                    (18, 3784343396517314069825)
                else
                  if b < 327 then
                    (23, 3631395221154074086397500185)
                  else
                    if b < 328 then
                      (19, 39083452144943452479508)
                    else
                      (36, 6160422796185779645904886228338019640651975)
              else
                if b < 332 then
                  if b < 330 then
                    (51, 18830321041662660818177097227068808401740594012672808196263353)
                  else
                    if b < 331 then
                      (41, 17160331046608621183704069708438736219426905185049)
                    else
                      (54, 16568685315919145677189948682911800316874921347480084093412328033)
                else
                  if b < 333 then
                    (20, 192687075140466271208003)
                  else
                    if b < 334 then
                      (0, 0)
                    else
                      (63, 6268495899725581406331875105829084235905057835487811167159438288545369836977)
            else
              if b < 340 then
                if b < 337 then
                  if b < 336 then
                    (61, 17430626395393487419809280736342016374487589607935336483362370659480296217)
                  else
                    (0, 0)
                else
                  if b < 338 then
                    (16, 9785642841945736278)
                  else
                    if b < 339 then
                      (40, 1060752845861405374491735563131111561957193603865)
                    else
                      (41, 11462399703166836885988208935866105363874264927672)
              else
                if b < 343 then
                  if b < 341 then
                    (0, 0)
                  else
                    if b < 342 then
                      (20, 112406845064113721930565)
                    else
                      (29, 60641541916586217145370180049512025)
                else
                  if b < 344 then
                    (16, 15837092606913075993)
                  else
                    if b < 345 then
                      (18, 2300712803233339297201)
                    else
                      (42, 183919710055580198765751201907241759483116524686776)
  else
    if b < 519 then
      if b < 432 then
        if b < 389 then
          if b < 367 then
            if b < 356 then
              if b < 351 then
                if b < 348 then
                  if b < 347 then
                    (51, 20468741203902098066050896138888308374954318298604116155321777)
                  else
                    (14, 38501398279460441)
                else
                  if b < 349 then
                    (20, 970534252750464544302473)
                  else
                    if b < 350 then
                      (48, 4996670457954411871319582105053934257961603425887270001545)
                    else
                      (16, 10060351862317081993)
              else
                if b < 353 then
                  if b < 352 then
                    (40, 862522395499998424663091782342211402541068996025)
                  else
                    (13, 2473333580683621)
                else
                  if b < 354 then
                    (42, 48633283500290627555595622103497664075018527270402)
                  else
                    if b < 355 then
                      (42, 48633283500290627555595622103497697972858999817732)
                    else
                      (31, 11697126377434831956369400316544699833)
            else
              if b < 361 then
                if b < 358 then
                  if b < 357 then
                    (24, 43477526252138631522481622457)
                  else
                    (25, 350179497806554752142514061412)
                else
                  if b < 359 then
                    (25, 593539347942084582282088471433)
                  else
                    if b < 360 then
                      (77, 349430148891239984907013599041883263997976970597782222559552653890007694256234670365847080376)
                    else
                      (0, 0)
              else
                if b < 364 then
                  if b < 362 then
                    (13, 3609031126435333)
                  else
                    if b < 363 then
                      (15, 149862875195008869)
                    else
                      (31, 11001013841792567876861235526475211331)
                else
                  if b < 365 then
                    (14, 12616230491608630)
                  else
                    if b < 366 then
                      (31, 3346019356681867238111441340964472324)
                    else
                      (17, 81532517624143590720)
          else
            if b < 378 then
              if b < 372 then
                if b < 369 then
                  if b < 368 then
                    (8, 3451728137)
                  else
                    (7, 213633905)
                else
                  if b < 370 then
                    (40, 207920796439539818205087018080809193079508976901)
                  else
                    if b < 371 then
                      (30, 731330886091727361337458794775864596)
                    else
                      (15, 637214874073029496)
              else
                if b < 375 then
                  if b < 373 then
                    (24, 38857122757140894271982816696)
                  else
                    if b < 374 then
                      (21, 9353990512421283689716505)
                    else
                      (14, 39637827977610836)
                else
                  if b < 376 then
                    (17, 142693121064129922267)
                  else
                    if b < 377 then
                      (20, 96430191621161637538675)
                    else
                      (47, 61723162665661967088244664232849333370280805806574478897)
            else
              if b < 383 then
                if b < 380 then
                  if b < 379 then
                    (25, 101114381126169148449857033748)
                  else
                    (7, 190269209)
                else
                  if b < 381 then
                    (31, 3389786872709798950003551815741084933)
                  else
                    if b < 382 then
                      (18, 746255550905141241426)
                    else
                      (54, 83862564013470916359344834984800049009260279301632432026985749385)
              else
                if b < 386 then
                  if b < 384 then
                    (4, 51033)
                  else
                    if b < 385 then
                      (52, 356325080221150799378879586659210433678220234052927060852398873)
                    else
                      (42, 53227723888522193460502276628686231154585058435648)
                else
                  if b < 387 then
                    (50, 1186894598220157008258525345589188456156548232538334370483640)
                  else
                    if b < 388 then
                      (21, 10336519220960592434450457)
                    else
                      (24, 58102848738453644030298807041)
        else
          if b < 410 then
            if b < 399 then
              if b < 394 then
                if b < 391 then
                  if b < 390 then
                    (13, 640705420678772)
                  else
                    (52, 303383648737546837578165216952275703649384011743055186403282360)
                else
                  if b < 392 then
                    (28, 3849210463111254673938647837855160)
                  else
                    if b < 393 then
                      (14, 11484563509367652)
                    else
                      (54, 89211562125539990207159699212082207942484996077938405583209421593)
              else
                if b < 396 then
                  if b < 395 then
                    (40, 403729468370831254874022623860381049926293275203)
                  else
                    (0, 0)
                else
                  if b < 397 then
                    (16, 2915060745618477904)
                  else
                    if b < 398 then
                      (40, 1048511130553289522987088115617537024331543348443)
                    else
                      (40, 1146029434661409458751544821509738672795607387576)
            else
              if b < 404 then
                if b < 401 then
                  if b < 400 then
                    (7, 35403028)
                  else
                    (27, 258035386231359199408338572783641)
                else
                  if b < 402 then
                    (12, 31689963357813)
                  else
                    if b < 403 then
                      (45, 199201929217190410467719668135926441738084912126585702)
                    else
                      (20, 1028808053589969746283961)
              else
                if b < 407 then
                  if b < 405 then
                    (16, 2411754587131241302)
                  else
                    if b < 406 then
                      (23, 624260503560779696084163684)
                    else
                      (26, 10717471762488195361183856203282)
                else
                  if b < 408 then
                    (10, 531699087129)
                  else
                    if b < 409 then
                      (16, 13131609641468110416)
                    else
                      (25, 101114383322336554373895185765)
          else
            if b < 421 then
              if b < 415 then
                if b < 412 then
                  if b < 411 then
                    (14, 10251286731328353)
                  else
                    (42, 53227723888522193460502276628686231154585045655651)
                else
                  if b < 413 then
                    (13, 1598171390466953)
                  else
                    if b < 414 then
                      (42, 48633283500290627555595622103497664075018631725158)
                    else
                      (30, 1067470156210531468792109821865252453)
              else
                if b < 418 then
                  if b < 416 then
                    (24, 67382828064642266662446816009)
                  else
                    if b < 417 then
                      (25, 695990366471377124842472342747)
                    else
                      (39, 25233091773176953429626413991273815622333912118)
                else
                  if b < 419 then
                    (59, 94814316422136188728099496357963362879738082869445399803165382906534681)
                  else
                    if b < 420 then
                      (52, 58524501335480517294858840538561291080087328647905442909144577)
                    else
                      (42, 48633283500290627555595622103497662907917713957124)
            else
              if b < 426 then
                if b < 423 then
                  if b < 422 then
                    (15, 850257480566806105)
                  else
                    (17, 46435346578082137088)
                else
                  if b < 424 then
                    (13, 3888222961368496)
                  else
                    if b < 425 then
                      (9, 10865628245)
                    else
                      (23, 704463074701623136077203521)
              else
                if b < 429 then
                  if b < 427 then
                    (20, 956220093146493603011448)
                  else
                    if b < 428 then
                      (46, 6773456496422604062572530349391456537663535293064037904)
                    else
                      (6, 11735065)
                else
                  if b < 430 then
                    (13, 2688021687015001)
                  else
                    if b < 431 then
                      (41, 17068317297937579085958612205890476436302231260593)
                    else
                      (15, 609217736392141893)
      else
        if b < 475 then
          if b < 453 then
            if b < 442 then
              if b < 437 then
                if b < 434 then
                  if b < 433 then
                    (68, 605302100661034835059148914663843304386559366401746691069503013629999279811859797)
                  else
                    (18, 3113740486855564797528)
                else
                  if b < 435 then
                    (38, 455378687915462444599049672015773879632183393)
                  else
                    if b < 436 then
                      (24, 21886220768143026236071175236)
                    else
                      (51, 15247199348120213283532067315857220674700415315793860708289976)
              else
                if b < 439 then
                  if b < 438 then
                    (68, 986400176323408950101090316357661547658147674781036668803080466544920065913414229)
                  else
                    (19, 8506709879386957759749)
                else
                  if b < 440 then
                    (26, 1843917558824554214451342356804)
                  else
                    if b < 441 then
                      (27, 238914958596210790519167130644505)
                    else
                      (16, 13676536466367164553)
            else
              if b < 447 then
                if b < 444 then
                  if b < 443 then
                    (14, 42746319485291953)
                  else
                    (23, 3722044078495304502929251080)
                else
                  if b < 445 then
                    (81, 29602329514391227814441435365700958097679775852184846016220587686450672271406831538628885433306552)
                  else
                    if b < 446 then
                      (14, 11484563676488726)
                    else
                      (54, 90441415853142712797658092941732002910144241323510413280992877449)
              else
                if b < 450 then
                  if b < 448 then
                    (16, 8996333331985793125)
                  else
                    if b < 449 then
                      (40, 712126519302219057332970733757953073622374810843)
                    else
                      (13, 2193377594461624)
                else
                  if b < 451 then
                    (20, 625335234600570232045666)
                  else
                    if b < 452 then
                      (39, 12995049777471238637817938630050362619641094500)
                    else
                      (43, 477499163059643948307893108883611506183339445147237)
          else
            if b < 464 then
              if b < 458 then
                if b < 455 then
                  if b < 454 then
                    (50, 228611333341720770683042345853753837117694555472895509117990)
                  else
                    (20, 625335237702561882793510)
                else
                  if b < 456 then
                    (24, 38546920229917841403888553401)
                  else
                    if b < 457 then
                      (27, 50094084927422021143921010164996)
                    else
                      (41, 3678987185100434248938838495781977973597103506276)
              else
                if b < 461 then
                  if b < 459 then
                    (71, 2479317404307598684402273954463102174767347164781554446620684343842975836672808937088)
                  else
                    if b < 460 then
                      (68, 1193899600236679572300129521493230278531207487301864559561788457090491557573846598)
                    else
                      (57, 311460147766681682688154029196048480097809939788150480711538738256665)
                else
                  if b < 462 then
                    (22, 44028941854393562210676817)
                  else
                    if b < 463 then
                      (26, 2636415581305926790337619306064)
                    else
                      (24, 31209462699445166295421570489)
            else
              if b < 469 then
                if b < 466 then
                  if b < 465 then
                    (39, 25233091773176953429626413991273815622523683664)
                  else
                    (42, 29843697691227746769243319305225702840090262595094)
                else
                  if b < 467 then
                    (14, 57640542423324248)
                  else
                    if b < 468 then
                      (15, 899969495255552137)
                    else
                      (14, 8112630625751382)
              else
                if b < 472 then
                  if b < 470 then
                    (56, 13945441719703541104435999631167472750645533431059666921904957448804)
                  else
                    if b < 471 then
                      (26, 9867884641875028189497855424393)
                    else
                      (19, 60455981015251494446680)
                else
                  if b < 473 then
                    (15, 609217736385123908)
                  else
                    if b < 474 then
                      (51, 7102483919192828477516053583643779021384148874966144904463937)
                    else
                      (49, 80533010624677618216014405988583861933492462146394762792376)
        else
          if b < 497 then
            if b < 486 then
              if b < 480 then
                if b < 477 then
                  if b < 476 then
                    (42, 58863794961606947983021415932511645212610039017990)
                  else
                    (30, 1151604614736609262450665529148460465)
                else
                  if b < 478 then
                    (16, 2940048259114467427)
                  else
                    if b < 479 then
                      (17, 155959740546486174275)
                    else
                      (34, 40784513030978440595249497749522407771577)
              else
                if b < 483 then
                  if b < 481 then
                    (11, 15100161036313)
                  else
                    if b < 482 then
                      (79, 18992286526970800883155945482176430026999047021870774214884848254458606022376791851921968604166)
                    else
                      (26, 9220271366575012954265944875040)
                else
                  if b < 484 then
                    (24, 6319648828456022310364012624)
                  else
                    if b < 485 then
                      (15, 318486429871187523)
                    else
                      (14, 38225167333524577)
            else
              if b < 491 then
                if b < 488 then
                  if b < 487 then
                    (26, 16146602809606568615413373841665)
                  else
                    (22, 5290483980893380671845717)
                else
                  if b < 489 then
                    (68, 2096283250319803177667234561092122141113048147380527052222155992593906321919989314)
                  else
                    if b < 490 then
                      (23, 2616570254285688576000030209)
                    else
                      (70, 1553573744120399652932863441520575297488114608733042881975156724476541309925915417369)
              else
                if b < 494 then
                  if b < 492 then
                    (51, 20453098955225493436711951460944366120424113474383563838512009)
                  else
                    if b < 493 then
                      (41, 3678987185100434248938838495781981364760269055556)
                    else
                      (25, 576266958491049016541443408469)
                else
                  if b < 495 then
                    (40, 986536905665316431451855159652167349348369488665)
                  else
                    if b < 496 then
                      (15, 884050810680695689)
                    else
                      (70, 1666038323440690934946916154646454187543705339227363772804105569169611818964441422617)
          else
            if b < 508 then
              if b < 502 then
                if b < 499 then
                  if b < 498 then
                    (48, 2128396030556154089274030878070649569654831997970144054705)
                  else
                    (50, 1367571225001622706905287097170256889380462458624945730637233)
                else
                  if b < 500 then
                    (13, 2772680583808219)
                  else
                    if b < 501 then
                      (48, 3077040128602076875309446513165814458145123592010956331913)
                    else
                      (39, 25233091773176953429626413991272676738187265350)
              else
                if b < 505 then
                  if b < 503 then
                    (9, 7437640001)
                  else
                    if b < 504 then
                      (25, 593535830075553553194503625488)
                    else
                      (17, 236095522899768796417)
                else
                  if b < 506 then
                    (70, 1553573744120399652932863441520575297488114608733042881975156724476541309925915417369)
                  else
                    if b < 507 then
                      (28, 820516655479562417981118288897382)
                    else
                      (35, 198288723411121195035063760834508498892385)
            else
              if b < 513 then
                if b < 510 then
                  if b < 509 then
                    (19, 41571347883957939492374)
                  else
                    (28, 816899256094166637698049707960419)
                else
                  if b < 511 then
                    (31, 2808249629505658428827435767994278212)
                  else
                    if b < 512 then
                      (15, 318486393801557329)
                    else
                      (43, 778132536004650040889529953655962625200296173462336)
              else
                if b < 516 then
                  if b < 514 then
                    (25, 199438294936095830533942760453)
                  else
                    if b < 515 then
                      (15, 848028675445490907)
                    else
                      (11, 9678532434277)
                else
                  if b < 517 then
                    (26, 2636415581393760703829697242453)
                  else
                    if b < 518 then
                      (23, 2317341931011016227509634267)
                    else
                      (41, 3678987185100434248938838495781981364760405746742)
    else
      if b < 606 then
        if b < 562 then
          if b < 540 then
            if b < 529 then
              if b < 524 then
                if b < 521 then
                  if b < 520 then
                    (41, 12095742567018054600503501285590607048121755338246)
                  else
                    (38, 1577068235823559589351650874454613476301472853)
                else
                  if b < 522 then
                    (30, 648254136355170119280970853525962832)
                  else
                    if b < 523 then
                      (32, 54236589987607166368866613791634640980)
                    else
                      (9, 54687188761)
              else
                if b < 526 then
                  if b < 525 then
                    (8, 2025140305)
                  else
                    (69, 57293634677659292714098311905198921959853136478348645825401081676287420701377318328)
                else
                  if b < 527 then
                    (20, 211665220107255686455300)
                  else
                    if b < 528 then
                      (36, 2898769587295688841080404645413022176011558)
                    else
                      (25, 1077159920311454143283380203545)
            else
              if b < 534 then
                if b < 531 then
                  if b < 530 then
                    (24, 68644837729274097638748587227)
                  else
                    (51, 21767759456382610475980026062712723953712907618413467372899768)
                else
                  if b < 532 then
                    (69, 9684833610576557360946382634621492870184949862427947057112048218394094086801216784)
                  else
                    if b < 533 then
                      (70, 252518445138792691225879120987561356200485804743945387213588599435499536838332658948)
                    else
                      (36, 19054738353773822940850191441262624318479129)
              else
                if b < 537 then
                  if b < 535 then
                    (24, 68353666333290056933500650715)
                  else
                    if b < 536 then
                      (23, 2624416763038666701058475227)
                    else
                      (14, 37272884517013060)
                else
                  if b < 538 then
                    (27, 42408736766022619265932655617328)
                  else
                    if b < 539 then
                      (46, 3857697666603872943015291514553086891535205610000041489)
                    else
                      (16, 2868113812447389233)
          else
            if b < 551 then
              if b < 545 then
                if b < 542 then
                  if b < 541 then
                    (40, 229936699068777140558677405986373835297534510677)
                  else
                    (27, 51282290967620225076409570590790)
                else
                  if b < 543 then
                    (17, 248719413130790194616)
                  else
                    if b < 544 then
                      (35, 181173099205980552567525290338313820067408)
                    else
                      (14, 39365530410080613)
              else
                if b < 548 then
                  if b < 546 then
                    (68, 5922732579539252296306754151785918070292881538429885858024180742527338794056699320)
                  else
                    if b < 547 then
                      (52, 330676575967749495760858726444729549220056060551434409326544091)
                    else
                      (47, 31293385150276825796306082783796673452151905832965335138)
                else
                  if b < 549 then
                    (13, 3812955148144777)
                  else
                    if b < 550 then
                      (69, 103150353806775174785999930578637812325350082201526030325013546909634649819124652825)
                    else
                      (53, 3637815008382617183056273122378710831574965366613925203041115017)
            else
              if b < 556 then
                if b < 553 then
                  if b < 552 then
                    (16, 2902209161136071424)
                  else
                    (36, 11535399024026922798636914525595290229888866)
                else
                  if b < 554 then
                    (25, 194473010068921323360124757028)
                  else
                    if b < 555 then
                      (40, 717138742972990418761652736258724505240628907448)
                    else
                      (13, 2329555289576533)
              else
                if b < 559 then
                  if b < 557 then
                    (6, 5445220)
                  else
                    if b < 558 then
                      (49, 8011106598470867403854357192651948403746465938620501646181)
                    else
                      (19, 55729549507644632176209)
                else
                  if b < 560 then
                    (41, 12095742567018054600503501285590607048119876208180)
                  else
                    if b < 561 then
                      (26, 9942471665670927412476023987081)
                    else
                      (80, 1046994714129059815460420591364340139508657689298652266853963721977700501941364091507372731008219)
        else
          if b < 584 then
            if b < 573 then
              if b < 567 then
                if b < 564 then
                  if b < 563 then
                    (16, 10222350318776987905)
                  else
                    (20, 594070312348332012359097)
                else
                  if b < 565 then
                    (80, 1315985244650227410875327505114799506337108442697885226202966314049669694052651248090391651569080)
                  else
                    if b < 566 then
                      (29, 13070388098715592022783424501975908)
                    else
                      (70, 1303252518531189231081096904177606546998144360033178662301276109405982140552779793627)
              else
                if b < 570 then
                  if b < 568 then
                    (13, 414299362570593)
                  else
                    if b < 569 then
                      (57, 34407440845202179108306888489542193062386183404154045236820210640390)
                    else
                      (40, 1076341089887403403646884865684375553030588747185)
                else
                  if b < 571 then
                    (21, 10714405446703520031073545)
                  else
                    if b < 572 then
                      (41, 19689191002202859206586327828611634565847638738139)
                    else
                      (30, 1037085539737315030496693582454643481)
            else
              if b < 578 then
                if b < 575 then
                  if b < 574 then
                    (15, 850575441484860857)
                  else
                    (67, 74618725014792473268758095093326892408200467956366534972611778568155722463338562)
                else
                  if b < 576 then
                    (46, 6773456496422604062572530349391416731333610656865739875)
                  else
                    if b < 577 then
                      (23, 3556271288430577168895313115)
                    else
                      (21, 2179784270988827594932307)
              else
                if b < 581 then
                  if b < 579 then
                    (46, 18185332734814785103255975019347127165241970506368080777)
                  else
                    if b < 580 then
                      (78, 5597944352069306377140499536210007685065777783535009680187812150794049149710385436058433411865)
                    else
                      (68, 5624121517048825320575581358467014347467617365769998880689097224715669782642613129)
                else
                  if b < 582 then
                    (52, 212790553584343583746887201403312592144261270757658412342842881)
                  else
                    if b < 583 then
                      (40, 1259027352097394307604449743618956661804920866011)
                    else
                      (14, 8112630626846037)
          else
            if b < 595 then
              if b < 589 then
                if b < 586 then
                  if b < 585 then
                    (19, 6026886764855936964150)
                  else
                    (13, 3751827535147265)
                else
                  if b < 587 then
                    (26, 17072579542596253673303757347609)
                  else
                    if b < 588 then
                      (66, 8188606446561731162762635004266102113722844325705183797742796847076168845039141)
                    else
                      (51, 13944529097952976304318017277062066262090017684585377100221881)
              else
                if b < 592 then
                  if b < 590 then
                    (44, 7639986608954303172926289742137784098933480716882374)
                  else
                    if b < 591 then
                      (26, 17102409785739384806469344628873)
                    else
                      (27, 278446714498782511743644558940936)
                else
                  if b < 593 then
                    (6, 2188896)
                  else
                    if b < 594 then
                      (20, 665141563018201995305734)
                    else
                      (46, 1955836571892301612269130173987272729326971063520092741)
            else
              if b < 600 then
                if b < 597 then
                  if b < 596 then
                    (24, 21886218612909672008906793318)
                  else
                    (27, 258352125952414139892305670495001)
                else
                  if b < 598 then
                    (26, 10491384334373368086814296203366)
                  else
                    if b < 599 then
                      (14, 9425947378206048)
                    else
                      (45, 199201929217190410467719668135926663981375452752499458)
              else
                if b < 603 then
                  if b < 601 then
                    (67, 67474156136067623219630979328714310934597076474513152585945079857973659984934518)
                  else
                    if b < 602 then
                      (15, 609217736471892022)
                    else
                      (26, 14931979243985232794808578060545)
                else
                  if b < 604 then
                    (12, 49282149798950)
                  else
                    if b < 605 then
                      (27, 49785090573878353802160448294993)
                    else
                      (13, 3303241321697544)
      else
        if b < 649 then
          if b < 627 then
            if b < 616 then
              if b < 611 then
                if b < 608 then
                  if b < 607 then
                    (16, 13599822010471930632)
                  else
                    (6, 10189896)
                else
                  if b < 609 then
                    (25, 1093136934283613472547416160025)
                  else
                    if b < 610 then
                      (24, 40981970013847812912642864134)
                    else
                      (41, 3039580218768164222224726381468604152497764910609)
              else
                if b < 613 then
                  if b < 612 then
                    (23, 1367888669886591776381232454)
                  else
                    (71, 24742400251818801843003957002772426752437359495599967836754842596018238245019998018441)
                else
                  if b < 614 then
                    (27, 277336903595511138103015834639105)
                  else
                    if b < 615 then
                      (31, 18400135905249875318178808798960051464)
                    else
                      (20, 593705806636248902477401)
            else
              if b < 621 then
                if b < 618 then
                  if b < 617 then
                    (18, 3975080763570954568923)
                  else
                    (42, 245125895687549662030143836781665812525123939356088)
                else
                  if b < 619 then
                    (73, 6396152087479366258817489525302807251635595593062902629393628863866635959059754864627128)
                  else
                    if b < 620 then
                      (16, 14735089280550004105)
                    else
                      (24, 40981969907567155346848965985)
              else
                if b < 624 then
                  if b < 622 then
                    (8, 3164913801)
                  else
                    if b < 623 then
                      (79, 10648587167904745873800391942451617079332232481415099332279216973903060218522313291292089931270)
                    else
                      (15, 629320717037626632)
                else
                  if b < 625 then
                    (69, 17273383970833311544225530708150863599256851577475367062001940443641256956128216341)
                  else
                    if b < 626 then
                      (71, 4421986296533327755321735861286621081409754003833693967872496753719685349119213527136)
                    else
                      (46, 13316100343778359763181813594840264814843007666506488713)
          else
            if b < 638 then
              if b < 632 then
                if b < 629 then
                  if b < 628 then
                    (26, 13773279536547035743900611227912)
                  else
                    (20, 953175290116351552808217)
                else
                  if b < 630 then
                    (29, 22949363808901891650817463337505811)
                  else
                    if b < 631 then
                      (26, 2651752211891973981772079060486)
                    else
                      (15, 638240873028836233)
              else
                if b < 635 then
                  if b < 633 then
                    (40, 1237374751569898118858421869918816747854485278136)
                  else
                    if b < 634 then
                      (69, 9684833610576557360946382634621492870184949862427947057112048218098662090183435331)
                    else
                      (15, 182251583082731105)
                else
                  if b < 636 then
                    (41, 12867024689109980228768368680524384496940079926713)
                  else
                    if b < 637 then
                      (19, 54233773467007249829305)
                    else
                      (48, 987570602650591473411914627725589334053653448365521200195)
            else
              if b < 643 then
                if b < 640 then
                  if b < 639 then
                    (29, 42972710319502218331793023312356691)
                  else
                    (76, 16859004560880647201974918632940748953369124576319536989872713852079275337078719525692728421)
                else
                  if b < 641 then
                    (16, 13319263782822307097)
                  else
                    if b < 642 then
                      (39, 47248994402414275783216801896838245892826949408)
                    else
                      (46, 12051048226070847670384373897578651231902582247740802267)
              else
                if b < 646 then
                  if b < 644 then
                    (17, 45279276104228548677)
                  else
                    if b < 645 then
                      (13, 2047311513809989)
                    else
                      (41, 12881202111374999904887559404485266466528806886281)
                else
                  if b < 647 then
                    (53, 3592861128532914137433519800158137373935892832483361561224695217)
                  else
                    if b < 648 then
                      (40, 229936699068777140558677405986373835297518794005)
                    else
                      (15, 709272692216004016)
        else
          if b < 671 then
            if b < 660 then
              if b < 654 then
                if b < 651 then
                  if b < 650 then
                    (79, 17352935416126156635823631575852851962791893610999793473478713621978749630391701718921912868950)
                  else
                    (14, 61883640557233424)
                else
                  if b < 652 then
                    (21, 13118085561155680995397041)
                  else
                    if b < 653 then
                      (13, 3813900261131483)
                    else
                      (28, 4169805512454340060208356636640261)
              else
                if b < 657 then
                  if b < 655 then
                    (67, 245330805204585299390236012302058937397219772920937058950551928897667199446292065)
                  else
                    if b < 656 then
                      (48, 4653695374044403636955068765951024743471174547557496933816)
                    else
                      (30, 891697587939134158365259461446231305)
                else
                  if b < 658 then
                    (45, 1129094454911741313902324912826496367719880375459139000)
                  else
                    if b < 659 then
                      (41, 3678987185100434248938838495781977973597284664897)
                    else
                      (30, 189102866692692146245557138676319312)
            else
              if b < 665 then
                if b < 662 then
                  if b < 661 then
                    (24, 21886218741032019372277104992)
                  else
                    (21, 16604384574162215140085177)
                else
                  if b < 663 then
                    (39, 44194259079964521283644933833276703228028800440)
                  else
                    if b < 664 then
                      (62, 353126024964704000896248476682071251326876532318871585821222277729931513272)
                    else
                      (15, 565057807621186817)
              else
                if b < 668 then
                  if b < 666 then
                    (16, 2917445688801707536)
                  else
                    if b < 667 then
                      (16, 2829954756742893633)
                    else
                      (27, 33497881090382219268410929335736)
                else
                  if b < 669 then
                    (22, 266850511313812921282356617)
                  else
                    if b < 670 then
                      (35, 1202491157677581739326756232267853824580377)
                    else
                      (54, 14982272341883012427483863177871528312622888556208918718432019777)
          else
            if b < 682 then
              if b < 676 then
                if b < 673 then
                  if b < 672 then
                    (49, 9361698237234247675079787869957278961814752374555922156985)
                  else
                    (31, 3389786877661559123222851356969755744)
                else
                  if b < 674 then
                    (30, 189102866692692040969760725394673667)
                  else
                    if b < 675 then
                      (42, 58863794961606947983021415932511647577553713389635)
                    else
                      (15, 557536028072073985)
              else
                if b < 679 then
                  if b < 677 then
                    (15, 683875433136511864)
                  else
                    if b < 678 then
                      (43, 4781718537837685199748082443448189690171829788888505)
                    else
                      (21, 10717368348817442588484872)
                else
                  if b < 680 then
                    (23, 3885099404275669089139051953)
                  else
                    if b < 681 then
                      (51, 2050843289208542055386715441318878489426855521481164367332449)
                    else
                      (51, 19031261763045546463733102763569838829147008088482460960050617)
            else
              if b < 687 then
                if b < 684 then
                  if b < 683 then
                    (50, 208878362130844651846599618735297349104272401445243072173380)
                  else
                    (15, 164020587745117254)
                else
                  if b < 685 then
                    (28, 678539788287041212615133630980421)
                  else
                    if b < 686 then
                      (13, 788514390958405)
                    else
                      (42, 205321302448773528809777690305969663438140454489529)
              else
                if b < 690 then
                  if b < 688 then
                    (14, 34565847621657881)
                  else
                    if b < 689 then
                      (24, 12154563119803913270611763558)
                    else
                      (26, 2636415583459796040085184472084)
                else
                  if b < 691 then
                    (23, 643656147873268703371379810)
                  else
                    if b < 692 then
                      (15, 524111745635083332)
                    else
                      (11, 14097777566726)

def forward2Blocks (b : Nat) : Nat :=
  if b < 1 then
    108136045982255308103785297945192983253526491626416305505498358892389365478994961807206853018800366571687817171922304546705175103182912043148960510140941022349085228299996750388707206911533112225815184035510787176763849979133894970934139522389033755613833754618167901695531360925828112099319191012988240683851649250386330016088764891776506032390739472941259452007899541703343888310315990399788458170283469639636172408583557253903081532557745345080065758502097856584280793868329397756178920240089642210684178252378760325019944325898868395381844724429027539438363170587923557237996882944305866440843485038996744678676503943212359049864991573510154741702782858387039545013863747167527638842209176744531086853228225935410096272729231573170184162998870210350948212797394125824
  else
    if b < 2 then
      69062468031237269304320299885445801010188996532031984999273489433164869524418575573977691044778607430584631214953601560090774805816878024801367151217080389328905733411115444644718029462355967337985038445165697275178682606102746188044056144385113032658193847161392827050778176749283829912930349288376350154672906682102127832685335694076824000488439729940287795165782211561529930167423251259968101691711774241240196924325719159270252564996204585346486194143303796505760778167949459371459367324645406669831680293101122320781556434736165184400211882430184954507001936801726375214621185179075440521649985044830951257377390480360296759436862108706617016806445232765757415445415604450446009554389048051258322351159984483359867745776256178077288511409840837984449231758953752641
    else
      46345674239233025987204268428317755503134789646566561814894117879351635183157778330688059623023082415985135105420979871388397320414953488967323059460629132156257914396791489248375398536055173901004383890270726902262338071372608934972929414671793569563526168581206229105361605707500561346332400849821677455413480441700139622189198191653111649021028040605138025580097303430303336264179440057918205738298811276742416963874855831398036065227689984523864393663923969656007638592476139295265497799692685651151200722484868102025669629561977150092224973

def backward2Blocks (b : Nat) : Nat :=
  if b < 1 then
    108136045982255308103785297945192983253526491626416305505498358892389365478994961807206853018800366571687817171922304546705175103182912043148960510140941022349085228299996750388707206911533112225815184035510787176763849979133894970934139522389033755613833754618167901695531360925828112099319191012988240683851649250386330016088764891776506032390739472941259452007899541703343888310315990399788458170283469639636172408583557253903081532557745345080065758502097856584280793868329397756178920240089642210684178252378760325019944325898868395381844724429027539438363170587923557237996882944305866440843485038996744678676503943212359049864991573510154741702782858387039545013863747167527638842209176744531086853228225935410096272729231573170184162998870210350948212797394125824
  else
    if b < 2 then
      69062468031237269304320299885445801010188996532031984999273489433164869524418575573977691044778607430584631214953601560090774805816878024801367151217080389328905733411115444644718029462355967337985038445165697275178682606102746188044056144385113032658193847161392827050778176749283829912930349288376350154672906682102127832685335694076824000488439729940287795165782211561529930167423251259968101691711774241240196924325719159270252564996204585346486194143303796505760778167949459371459367324645406669831680293101122320781556434736165184400211882430184954507001936801726375214621185179075440521649985044830951257377390480360296759436862108706617016806445232765757415445415604450446009554389048051258322351159984483359867745776256178077288511409840837984449231758953752641
    else
      46345674239233025987204268428317755503134789646566561814894117879351635183157778330688059623023082415985135105420979871388397320414953488967323059460629132156257914396791489248375398536055173901004383890270726902262338071372608934972929414671793569563526168581206229105361605707500561346332400849821677455413480441700139622189198191653111649021028040605138025580097303430303336264179440057918205738298811276742416963874855831398036065227689984523864393663923969656007638592476139295265497799692685651151200722484868102025669629561977150092224973

def factorCode2 (b : Nat) : Nat × Nat :=
  if b < 346 then
    if b < 173 then
      if b < 86 then
        if b < 43 then
          if b < 21 then
            if b < 10 then
              if b < 5 then
                if b < 2 then
                  if b < 1 then
                    (1, 9)
                  else
                    (2, 137)
                else
                  if b < 3 then
                    (2, 25)
                  else
                    if b < 4 then
                      (4, 17177)
                    else
                      (16, 15549245918741894744)
              else
                if b < 7 then
                  if b < 6 then
                    (5, 475161)
                  else
                    (4, 43801)
                else
                  if b < 8 then
                    (4, 16521)
                  else
                    if b < 9 then
                      (4, 29817)
                    else
                      (0, 0)
            else
              if b < 15 then
                if b < 12 then
                  if b < 11 then
                    (3, 25)
                  else
                    (3, 1817)
                else
                  if b < 13 then
                    (6, 1773705)
                  else
                    if b < 14 then
                      (0, 0)
                    else
                      (2, 169)
              else
                if b < 18 then
                  if b < 16 then
                    (5, 266265)
                  else
                    if b < 17 then
                      (3, 1817)
                    else
                      (2, 121)
                else
                  if b < 19 then
                    (9, 2362598664)
                  else
                    (0, 0)
          else
            if b < 32 then
              if b < 26 then
                if b < 23 then
                  if b < 22 then
                    (0, 0)
                  else
                    (39, 12995049777471238637817938630050353381580986434)
                else
                  if b < 24 then
                    (0, 0)
                  else
                    if b < 25 then
                      (4, 45961)
                    else
                      (4, 17273)
              else
                if b < 29 then
                  if b < 27 then
                    (5, 500745)
                  else
                    if b < 28 then
                      (39, 55336535443226185752312081671520102497673825721)
                    else
                      (2, 32)
                else
                  if b < 30 then
                    (6, 1773705)
                  else
                    if b < 31 then
                      (0, 0)
                    else
                      (3, 25)
            else
              if b < 37 then
                if b < 34 then
                  if b < 33 then
                    (5, 274569)
                  else
                    (0, 0)
                else
                  if b < 35 then
                    (19, 60678654217354647755545)
                  else
                    if b < 36 then
                      (7, 201609241)
                    else
                      (0, 0)
              else
                if b < 40 then
                  if b < 38 then
                    (8, 466109268)
                  else
                    if b < 39 then
                      (0, 0)
                    else
                      (7, 210502848)
                else
                  if b < 41 then
                    (0, 0)
                  else
                    if b < 42 then
                      (0, 0)
                    else
                      (9, 49857778696)
        else
          if b < 64 then
            if b < 53 then
              if b < 48 then
                if b < 45 then
                  if b < 44 then
                    (0, 0)
                  else
                    (2, 121)
                else
                  if b < 46 then
                    (4, 29817)
                  else
                    if b < 47 then
                      (0, 0)
                    else
                      (5, 110857)
              else
                if b < 50 then
                  if b < 49 then
                    (5, 477065)
                  else
                    (2, 32)
                else
                  if b < 51 then
                    (0, 0)
                  else
                    if b < 52 then
                      (84, 93933882536087458826476914618888409499471259762098275584015812793343273122859212008803201115989495224)
                    else
                      (15, 318486425813464388)
            else
              if b < 58 then
                if b < 55 then
                  (0, 0)
                else
                  if b < 56 then
                    (9, 54496923785)
                  else
                    (0, 0)
              else
                if b < 61 then
                  if b < 59 then
                    (4, 16521)
                  else
                    if b < 60 then
                      (31, 2782048624828587121324023892773585253)
                    else
                      (0, 0)
                else
                  if b < 62 then
                    (10, 874238791944)
                  else
                    if b < 63 then
                      (3, 1033)
                    else
                      (10, 858112438529)
          else
            if b < 75 then
              if b < 69 then
                if b < 66 then
                  (0, 0)
                else
                  if b < 67 then
                    (0, 0)
                  else
                    if b < 68 then
                      (22, 44028941620784796381132597)
                    else
                      (70, 1439854572086722154534360080008430301128550143461914999454477315026478781114953816857)
              else
                (0, 0)
            else
              if b < 80 then
                if b < 77 then
                  if b < 76 then
                    (7, 203116569)
                  else
                    (0, 0)
                else
                  if b < 78 then
                    (0, 0)
                  else
                    if b < 79 then
                      (0, 0)
                    else
                      (25, 101114380921224122394795640070)
              else
                if b < 83 then
                  if b < 81 then
                    (0, 0)
                  else
                    if b < 82 then
                      (80, 1847993418373505096429604008158210894313764262889257874559019604135132520682502116560548525300505)
                    else
                      (0, 0)
                else
                  if b < 84 then
                    (7, 203116569)
                  else
                    if b < 85 then
                      (34, 69583163067401222117649530444960233817307)
                    else
                      (22, 244225978866313248108465593)
      else
        if b < 129 then
          if b < 107 then
            if b < 96 then
              if b < 91 then
                if b < 88 then
                  (0, 0)
                else
                  if b < 89 then
                    (30, 979028414633732309764495151583094024)
                  else
                    (0, 0)
              else
                if b < 93 then
                  (0, 0)
                else
                  if b < 94 then
                    (0, 0)
                  else
                    if b < 95 then
                      (52, 64721427015309162801523237042624219987792795125561035116402260)
                    else
                      (0, 0)
            else
              if b < 101 then
                if b < 98 then
                  if b < 97 then
                    (4, 16521)
                  else
                    (5, 725017)
                else
                  if b < 99 then
                    (25, 195680019247805073915478565972)
                  else
                    if b < 100 then
                      (9, 36378448981)
                    else
                      (0, 0)
              else
                if b < 104 then
                  if b < 102 then
                    (4, 49241)
                  else
                    if b < 103 then
                      (9, 54954475777)
                    else
                      (18, 2283092714897854506577)
                else
                  if b < 105 then
                    (34, 6948527600837265222299203719690402354737)
                  else
                    if b < 106 then
                      (0, 0)
                    else
                      (50, 1179244288867369842688884764866544743237289234605993303005977)
          else
            if b < 118 then
              if b < 112 then
                if b < 109 then
                  if b < 108 then
                    (0, 0)
                  else
                    (26, 14795072100310197783340032449289)
                else
                  if b < 110 then
                    (0, 0)
                  else
                    if b < 111 then
                      (36, 18884235589467085925891856292931085581736841)
                    else
                      (17, 161711995907480561241)
              else
                if b < 115 then
                  if b < 113 then
                    (0, 0)
                  else
                    if b < 114 then
                      (9, 54889529608)
                    else
                      (67, 131017703144987698604202160068257633819565509211282940763884749537119145361171779)
                else
                  if b < 116 then
                    (34, 47251754038209407410126010071893829242296)
                  else
                    if b < 117 then
                      (52, 53472860705496230872729502396236102072071657116672474528941397)
                    else
                      (29, 61222284347815774739930857222252113)
            else
              if b < 123 then
                if b < 120 then
                  if b < 119 then
                    (78, 7161803627091410192287942908110606796215492218621864573681188338343973942565767393929571880376)
                  else
                    (0, 0)
                else
                  if b < 121 then
                    (0, 0)
                  else
                    if b < 122 then
                      (30, 984200701444356686217083679378787768)
                    else
                      (0, 0)
              else
                if b < 126 then
                  if b < 124 then
                    (31, 17012720048420688273131875801827171097)
                  else
                    if b < 125 then
                      (8, 3165328712)
                    else
                      (8, 3161802521)
                else
                  if b < 127 then
                    (23, 2376095235963658394318949816)
                  else
                    if b < 128 then
                      (9, 49857778696)
                    else
                      (0, 0)
        else
          if b < 151 then
            if b < 140 then
              if b < 134 then
                if b < 131 then
                  (0, 0)
                else
                  if b < 132 then
                    (0, 0)
                  else
                    if b < 133 then
                      (67, 318296098582209052980949305264656897497959436526679806813306256329726471302415579)
                    else
                      (4, 43801)
              else
                if b < 137 then
                  if b < 135 then
                    (5, 148740)
                  else
                    if b < 136 then
                      (0, 0)
                    else
                      (17, 51707612129941760849)
                else
                  if b < 138 then
                    (8, 3098330121)
                  else
                    if b < 139 then
                      (0, 0)
                    else
                      (25, 1009073210458383813130024144313)
            else
              if b < 145 then
                if b < 142 then
                  if b < 141 then
                    (0, 0)
                  else
                    (9, 49605185673)
                else
                  if b < 143 then
                    (18, 613838336783924155476)
                  else
                    if b < 144 then
                      (56, 14898739421208182196993127607695864853906088923614708011853886279089)
                    else
                      (0, 0)
              else
                if b < 148 then
                  if b < 146 then
                    (0, 0)
                  else
                    if b < 147 then
                      (31, 17076110342553873217738651114836217993)
                    else
                      (0, 0)
                else
                  if b < 149 then
                    (19, 10749253265317768996352)
                  else
                    if b < 150 then
                      (9, 49857778696)
                    else
                      (0, 0)
          else
            if b < 162 then
              if b < 156 then
                if b < 153 then
                  if b < 152 then
                    (53, 4821899185287803408848976653333724847623388472718156223788407577)
                  else
                    (7, 210502848)
                else
                  if b < 154 then
                    (48, 5382973362139271278157991255373964290618740977946100518321)
                  else
                    (0, 0)
              else
                if b < 159 then
                  if b < 157 then
                    (25, 934601042080602069220495044873)
                  else
                    if b < 158 then
                      (44, 70895317776446416548254747637906085212947659941534601)
                    else
                      (27, 49785090543144047334116077690981)
                else
                  if b < 160 then
                    (0, 0)
                  else
                    if b < 161 then
                      (0, 0)
                    else
                      (6, 7885254)
            else
              if b < 167 then
                if b < 164 then
                  (0, 0)
                else
                  if b < 165 then
                    (14, 35393078924514905)
                  else
                    if b < 166 then
                      (53, 5212685670335794806916089028448306365131202955596423780378889656)
                    else
                      (9, 54888481033)
              else
                if b < 170 then
                  if b < 168 then
                    (0, 0)
                  else
                    if b < 169 then
                      (51, 17354563174819034410888031212411804984652782326188901597728177)
                    else
                      (51, 2050843289208542055386715441318881098174225294837596728613718)
                else
                  if b < 171 then
                    (26, 3111568158669801797276616647732)
                  else
                    if b < 172 then
                      (4, 16521)
                    else
                      (25, 180342543746714143609176065349)
    else
      if b < 259 then
        if b < 216 then
          if b < 194 then
            if b < 183 then
              if b < 178 then
                if b < 175 then
                  if b < 174 then
                    (9, 49590088456)
                  else
                    (4, 17177)
                else
                  if b < 176 then
                    (41, 12588804749538492076979815714517434794750131886873)
                  else
                    if b < 177 then
                      (51, 22068628174093125370050756181580285562316617235841973487685048)
                    else
                      (47, 212776199341984200345676150517974715787736091713698024889)
              else
                if b < 180 then
                  (0, 0)
                else
                  if b < 181 then
                    (0, 0)
                  else
                    if b < 182 then
                      (8, 3161802521)
                    else
                      (29, 59991385711473849710408001199820209)
            else
              if b < 188 then
                if b < 185 then
                  if b < 184 then
                    (6, 13995024)
                  else
                    (45, 1135735187224450188208957518901141960804032934287039257)
                else
                  if b < 186 then
                    (9, 8984539216)
                  else
                    if b < 187 then
                      (9, 54889529608)
                    else
                      (15, 182191296600892261)
              else
                if b < 191 then
                  if b < 189 then
                    (15, 845740886909650139)
                  else
                    if b < 190 then
                      (9, 54496923785)
                    else
                      (0, 0)
                else
                  if b < 192 then
                    (25, 1083125366224202372847092387249)
                  else
                    if b < 193 then
                      (78, 7161803627091410192287942908110606796215492218621864573681188338343973942565767393929571880376)
                    else
                      (19, 60678654217354647755545)
          else
            if b < 205 then
              if b < 199 then
                if b < 196 then
                  if b < 195 then
                    (0, 0)
                  else
                    (15, 638896896295671384)
                else
                  if b < 197 then
                    (66, 18119591015531267614894188144737936213705870333743801524368764440373492665681115)
                  else
                    if b < 198 then
                      (0, 0)
                    else
                      (9, 54496923785)
              else
                if b < 202 then
                  if b < 200 then
                    (0, 0)
                  else
                    if b < 201 then
                      (57, 316337433017103285353714413218429698099714193318702608689262206406065)
                    else
                      (84, 93933882536087458826476914618888409499471259762098275584015812793343273122859212008803201115989495224)
                else
                  if b < 203 then
                    (42, 193531881072288873608056020569449712769916127417937)
                  else
                    if b < 204 then
                      (16, 12517988777323911944)
                    else
                      (0, 0)
            else
              if b < 210 then
                if b < 207 then
                  if b < 206 then
                    (6, 13416648)
                  else
                    (0, 0)
                else
                  if b < 208 then
                    (15, 75666625094030182)
                  else
                    if b < 209 then
                      (76, 23469082727937116457600100130484252804353753134475340574596800904263277441902450348721720760)
                    else
                      (0, 0)
              else
                if b < 213 then
                  if b < 211 then
                    (67, 131017703144987698604202160068257633819565509211282940763884749537119147290353750)
                  else
                    if b < 212 then
                      (67, 340297500609801425522754191966201027003165564131450734025176031294767547100974520)
                    else
                      (42, 202403982379883844746433526414660644589593650584345)
                else
                  if b < 214 then
                    (78, 6148768160012397007586787519462452505548661289264894713016369518575888570206934080942239665593)
                  else
                    if b < 215 then
                      (31, 17931452277009135474061076849785887625)
                    else
                      (76, 2599752726539244598095798814075101826008845820657983235419730706519301811158748904504548372)
        else
          if b < 237 then
            if b < 226 then
              if b < 221 then
                if b < 218 then
                  if b < 217 then
                    (0, 0)
                  else
                    (43, 3096510097156621977728896329111190677406770491979078)
                else
                  if b < 219 then
                    (23, 2376095235963658394318949816)
                  else
                    if b < 220 then
                      (40, 1064902081448353217916489973883160848779438250777)
                    else
                      (29, 39870769623179748992812006686870961)
              else
                if b < 223 then
                  if b < 222 then
                    (26, 17087621597589949682618507713289)
                  else
                    (0, 0)
                else
                  if b < 224 then
                    (19, 35373351249525849738681)
                  else
                    if b < 225 then
                      (0, 0)
                    else
                      (80, 1033310464427133493698052138247649290933768690615475876564694246690913642858036821546936119384969)
            else
              if b < 231 then
                if b < 228 then
                  if b < 227 then
                    (6, 13401201)
                  else
                    (25, 1067662676086285184303169330057)
                else
                  if b < 229 then
                    (15, 164020587700051972)
                  else
                    if b < 230 then
                      (19, 9874053478227666822741)
                    else
                      (0, 0)
              else
                if b < 234 then
                  if b < 232 then
                    (0, 0)
                  else
                    if b < 233 then
                      (31, 10357691466679903550205169883868718361)
                    else
                      (0, 0)
                else
                  if b < 235 then
                    (75, 1255663133560830080034223235122521660276395892683936689422061505328625189447952136071564721)
                  else
                    if b < 236 then
                      (26, 12423267309121105597724562348937)
                    else
                      (70, 1439854572086722154534360080008430301128550143461914999454477315026478781114953816857)
          else
            if b < 248 then
              if b < 242 then
                if b < 239 then
                  if b < 238 then
                    (0, 0)
                  else
                    (26, 15909267701625644230268132462617)
                else
                  if b < 240 then
                    (57, 316337433017103285353714413218429698099714193318702608689262206406065)
                  else
                    if b < 241 then
                      (1, 9)
                    else
                      (7, 210502848)
              else
                if b < 245 then
                  if b < 243 then
                    (80, 1450491565171031359581155971191936914583853480653820447692541076716798109097596470474774092766089)
                  else
                    if b < 244 then
                      (0, 0)
                    else
                      (3, 635)
                else
                  if b < 246 then
                    (14, 6619473613578835)
                  else
                    if b < 247 then
                      (80, 1575704092564359550389348522537159402710777308219831983933226514312933342397898911946880816831369)
                    else
                      (80, 1847993418373505096429604008158210894313764262889257874559019604135132520682502116560548525300505)
            else
              if b < 253 then
                if b < 250 then
                  if b < 249 then
                    (28, 2685794394968889056970643696541712)
                  else
                    (5, 752825)
                else
                  if b < 251 then
                    (0, 0)
                  else
                    if b < 252 then
                      (4, 4233)
                    else
                      (25, 1086867671953181892173832932785)
              else
                if b < 256 then
                  if b < 254 then
                    (0, 0)
                  else
                    if b < 255 then
                      (54, 49566486327832885755858022841409447543897044018533224396498161080)
                    else
                      (4, 49241)
                else
                  if b < 257 then
                    (0, 0)
                  else
                    if b < 258 then
                      (42, 205846176288046995410545268850324844710891043704241)
                    else
                      (25, 655711520603187600246591217734)
      else
        if b < 302 then
          if b < 280 then
            if b < 269 then
              if b < 264 then
                if b < 261 then
                  if b < 260 then
                    (0, 0)
                  else
                    (5, 842085)
                else
                  if b < 262 then
                    (50, 252818074278551417193450144697750938631746335919428058441284)
                  else
                    if b < 263 then
                      (80, 277646966658018506173178105213645631404670297775996695575659417951680525940720405086643425388116)
                    else
                      (15, 826372359905627577)
              else
                if b < 266 then
                  if b < 265 then
                    (74, 78322743115577581029034629503745890440561635250980071640467431853879587936462014108796123)
                  else
                    (68, 5124218267111343869134501842868496083010244492263525230044900894136212476978846489)
                else
                  if b < 267 then
                    (27, 260490029061080803011573925272329)
                  else
                    if b < 268 then
                      (15, 179257113395331920)
                    else
                      (0, 0)
            else
              if b < 274 then
                if b < 271 then
                  if b < 270 then
                    (15, 181388072593085189)
                  else
                    (43, 3637389216164677920704088111471733982037244947782425)
                else
                  if b < 272 then
                    (25, 1068493057022828003133734538680)
                  else
                    if b < 273 then
                      (0, 0)
                    else
                      (65, 291479394589033098706086308958308173469533077954556777236764760031858290616163)
              else
                if b < 277 then
                  if b < 275 then
                    (80, 1847993418373505096429604008158210894313764262889257874559019604135132520682502116560548525300505)
                  else
                    if b < 276 then
                      (60, 1413856887965015905630318112946181440845110933812574618212464075993384155)
                    else
                      (15, 926289637117112345)
                else
                  if b < 278 then
                    (27, 167862148852871047857651990221923)
                  else
                    if b < 279 then
                      (0, 0)
                    else
                      (52, 271154827686916966376851620199128623045899089518211179919461817)
          else
            if b < 291 then
              if b < 285 then
                if b < 282 then
                  if b < 281 then
                    (25, 194473010027628028336348226835)
                  else
                    (27, 220238459530861459225901705219505)
                else
                  if b < 283 then
                    (60, 251360819250597146226581109049597050750989751795355798996780365188046944)
                  else
                    if b < 284 then
                      (82, 463223854811413279459392244449629488729529227490598638618792048050204707799969746917654387883003313)
                    else
                      (29, 42972710106334988251558909497595440)
              else
                if b < 288 then
                  if b < 286 then
                    (26, 2636415581377682925388204107090)
                  else
                    (0, 0)
                else
                  if b < 289 then
                    (15, 972153933425435905)
                  else
                    if b < 290 then
                      (28, 3808883347822833502785795504080091)
                    else
                      (34, 69583163067401222117649530444960233817307)
            else
              if b < 296 then
                if b < 293 then
                  if b < 292 then
                    (41, 3678987185100434248938838495781977973597101188676)
                  else
                    (7, 203116569)
                else
                  if b < 294 then
                    (29, 50823726686534319772423906214151387)
                  else
                    if b < 295 then
                      (29, 61551843812745510914100016123269733)
                    else
                      (40, 755983910438628412531468830349411722818572695557)
              else
                if b < 299 then
                  if b < 297 then
                    (80, 1847993418373505096429604008158210894313764262889257874559019604135132520682502116560548525300505)
                  else
                    if b < 298 then
                      (0, 0)
                    else
                      (34, 69583163067401222117649530444960233817307)
                else
                  if b < 300 then
                    (17, 152669734890607304804)
                  else
                    if b < 301 then
                      (30, 985517508463681731851172677337238969)
                    else
                      (26, 3206349349491824344926886454549)
        else
          if b < 324 then
            if b < 313 then
              if b < 307 then
                if b < 304 then
                  if b < 303 then
                    (0, 0)
                  else
                    (40, 403729468370831254874022623860381049932076105813)
                else
                  if b < 305 then
                    (17, 213041563517121663113)
                  else
                    if b < 306 then
                      (26, 3111568159036705837506638668550)
                    else
                      (16, 15549245918741894744)
              else
                if b < 310 then
                  if b < 308 then
                    (0, 0)
                  else
                    if b < 309 then
                      (41, 17160353026387721335979125758233726209065558006553)
                    else
                      (19, 60465815831379460337801)
                else
                  if b < 311 then
                    (26, 12348844554242944857363439737625)
                  else
                    if b < 312 then
                      (19, 63950568503934920582537)
                    else
                      (34, 69583163067401222117649530444960233817307)
            else
              if b < 318 then
                if b < 315 then
                  if b < 314 then
                    (19, 65476417592544507799121)
                  else
                    (7, 203116569)
                else
                  if b < 316 then
                    (17, 163119670986610159753)
                  else
                    if b < 317 then
                      (53, 3182615039626936336495508468390954897281510274923080283943095737)
                    else
                      (26, 10491384295189093607984414852454)
              else
                if b < 321 then
                  if b < 319 then
                    (0, 0)
                  else
                    if b < 320 then
                      (68, 1079586498177081971514095669259428974953553223592210441375121277729943503293015398)
                    else
                      (65, 1451862887558217063492793550869560477779313010378681669224230451612065735247067)
                else
                  if b < 322 then
                    (53, 936392021367688276717741448616975716834076915294758446840419648)
                  else
                    if b < 323 then
                      (48, 3246926171636102046919055197194095875752515492741959258438)
                    else
                      (8, 3161802521)
          else
            if b < 335 then
              if b < 329 then
                if b < 326 then
                  if b < 325 then
                    (30, 1136073211029808281576474574474726841)
                  else
                    (52, 329067981295810829459566516902699032084457552153142441988643721)
                else
                  if b < 327 then
                    (36, 6160422796185779645904886228338019640651975)
                  else
                    if b < 328 then
                      (51, 3342053794093514429545593899764757586513656448681432416961349)
                    else
                      (0, 0)
              else
                if b < 332 then
                  if b < 330 then
                    (31, 16578269725278041369577055355098517529)
                  else
                    if b < 331 then
                      (34, 69583163067401222117649530444960233817307)
                    else
                      (0, 0)
                else
                  if b < 333 then
                    (30, 979028414633732309764495151583094024)
                  else
                    if b < 334 then
                      (41, 12947003602970780451657796089197935776511461182904)
                    else
                      (14, 12616230687368288)
            else
              if b < 340 then
                if b < 337 then
                  if b < 336 then
                    (41, 15879859522956847317715090874321789392356697758601)
                  else
                    (77, 413235475476601188274397715243587214238214349602008005113170967464026008191375004800530121947)
                else
                  if b < 338 then
                    (13, 2477364389642260)
                  else
                    if b < 339 then
                      (0, 0)
                    else
                      (81, 25171209205591111471721949058572838341442233972810631382727625364445457495739990688696041275186057)
              else
                if b < 343 then
                  if b < 341 then
                    (45, 241106104162742058938455719659567708477659343771538532)
                  else
                    if b < 342 then
                      (0, 0)
                    else
                      (16, 1471407904380772406)
                else
                  if b < 344 then
                    (21, 10260990228773351296484934)
                  else
                    if b < 345 then
                      (15, 561397239207060745)
                    else
                      (0, 0)
  else
    if b < 519 then
      if b < 432 then
        if b < 389 then
          if b < 367 then
            if b < 356 then
              if b < 351 then
                if b < 348 then
                  if b < 347 then
                    (0, 0)
                  else
                    (69, 58559049796310416104910913831912859885891329734437791847945337794092165636877733305)
                else
                  if b < 349 then
                    (47, 241702259208491013447902184016778488764385667084624124809)
                  else
                    if b < 350 then
                      (41, 12095742567018054600503501285590590948566634612320)
                    else
                      (52, 303486781060432143660305491306186154613403529575258781370342169)
              else
                if b < 353 then
                  if b < 352 then
                    (0, 0)
                  else
                    (81, 4442351466528296098770849683418330102474724764415947129210550687226888415051421205589881598060099)
                else
                  if b < 354 then
                    (51, 22125497553247770089265883958004548552234423702795224998759864)
                  else
                    if b < 355 then
                      (31, 18258625533445197613668891098465229705)
                    else
                      (81, 25196228089446041005153606244822728910754851482369882675122669988259417228791057589488745663749001)
            else
              if b < 361 then
                if b < 358 then
                  if b < 357 then
                    (66, 8188606446561731162762635004266102113722844325705183797742796847076168962555986)
                  else
                    (25, 835877024317638391641780247305)
                else
                  if b < 359 then
                    (58, 897125734194022652537651371274170330851257145460468982778069575341568)
                  else
                    if b < 360 then
                      (0, 0)
                    else
                      (77, 144055488052418179027802400170425258229088621309964028104599105873820207388506887953658697269)
              else
                if b < 364 then
                  if b < 362 then
                    (24, 58717970015217774994669981112)
                  else
                    if b < 363 then
                      (18, 3481592581208332884873)
                    else
                      (27, 199619461937178131323067780356889)
                else
                  if b < 365 then
                    (40, 1167395027002979486278237692109962034857053127899)
                  else
                    if b < 366 then
                      (54, 54474381717591957439203123559247940432208680604133252888418150198)
                    else
                      (28, 678539788251918611898790527981076)
          else
            if b < 378 then
              if b < 372 then
                if b < 369 then
                  if b < 368 then
                    (8, 666194708)
                  else
                    (8, 3417949304)
                else
                  if b < 370 then
                    (74, 107331153161092872938553372329659031457535192578592005264649906900233925866515328512576953)
                  else
                    if b < 371 then
                      (39, 78778453911669941723429325076243591741067775417)
                    else
                      (0, 0)
              else
                if b < 375 then
                  if b < 373 then
                    (23, 2376095235963658394318949816)
                  else
                    if b < 374 then
                      (8, 3161802521)
                    else
                      (50, 1391477964165097182647588762567654230465187990400718302367160)
                else
                  if b < 376 then
                    (4, 4233)
                  else
                    if b < 377 then
                      (53, 5129124670361618403629522021544624062900506314917247078698900361)
                    else
                      (9, 33414713481)
            else
              if b < 383 then
                if b < 380 then
                  if b < 379 then
                    (18, 2598209230539851543872)
                  else
                    (8, 3430203656)
                else
                  if b < 381 then
                    (31, 11001013841792567892939013967963369797)
                  else
                    if b < 382 then
                      (14, 37272884510861411)
                    else
                      (0, 0)
              else
                if b < 386 then
                  if b < 384 then
                    (66, 23747077933080744759415078947840366847812595464556162530546822641505737812269849)
                  else
                    if b < 385 then
                      (24, 6319648940352212079265723492)
                    else
                      (26, 9630164948884597914816244669321)
                else
                  if b < 387 then
                    (65, 1373440468055638943148066340763965986336665919965670177882821734677859625469147)
                  else
                    if b < 388 then
                      (0, 0)
                    else
                      (52, 303287876869603180072136592842006326271036615395482098928209337)
        else
          if b < 410 then
            if b < 399 then
              if b < 394 then
                if b < 391 then
                  if b < 390 then
                    (42, 316676212189995459016386751601136580959527652838833)
                  else
                    (9, 8982373717)
                else
                  if b < 392 then
                    (44, 70895317776446416548254747637906085212947659941534601)
                  else
                    if b < 393 then
                      (51, 22280878802622773538382282056775259222000346958118075133611441)
                    else
                      (0, 0)
              else
                if b < 396 then
                  if b < 395 then
                    (48, 1734004863084186640018567769444357425725794450037509831525)
                  else
                    (16, 2397806003203630646)
                else
                  if b < 397 then
                    (39, 67027489724158012494803877556397816426075803064)
                  else
                    if b < 398 then
                      (30, 149793632984066509800522106306561620)
                    else
                      (41, 3678987185100434248938838495781978979819350427169)
            else
              if b < 404 then
                if b < 401 then
                  if b < 400 then
                    (29, 71267142656852876827935835827788569)
                  else
                    (0, 0)
                else
                  if b < 402 then
                    (75, 1598134172301759310548170526023991366967732690676493718983048335148463190052722186974976793)
                  else
                    if b < 403 then
                      (9, 49857778696)
                    else
                      (29, 13070388097506666203168795327349318)
              else
                if b < 407 then
                  if b < 405 then
                    (27, 159450608248202268042357341739913)
                  else
                    if b < 406 then
                      (60, 866002863857457382404942877486766945886820873896611836260361535186030009)
                    else
                      (17, 249884274015543693337)
                else
                  if b < 408 then
                    (35, 1115292554792494948245626134870833858891185)
                  else
                    if b < 409 then
                      (45, 122239785743268850766820635874204701076401787688604690)
                    else
                      (27, 171479548162708964414806359958292)
          else
            if b < 421 then
              if b < 415 then
                if b < 412 then
                  if b < 411 then
                    (39, 79140966235754418610819513579923509181619166089)
                  else
                    (30, 979028414633732309764495151583094024)
                else
                  if b < 413 then
                    (65, 511787902910108197672664687766631382107677770356573987358924802870133600444949)
                  else
                    (0, 0)
              else
                if b < 418 then
                  if b < 416 then
                    (17, 38570521397658271841)
                  else
                    if b < 417 then
                      (52, 58524501335480517294858840538560982302129783354510300159173651)
                    else
                      (21, 16611989749062252847326465)
                else
                  if b < 419 then
                    (29, 42972710086992176142585995295348244)
                  else
                    if b < 420 then
                      (41, 3326732743032637091281392289292892830628355252294)
                    else
                      (0, 0)
            else
              if b < 426 then
                if b < 423 then
                  if b < 422 then
                    (27, 234108529532377911511052530998017)
                  else
                    (8, 3161802521)
                else
                  if b < 424 then
                    (0, 0)
                  else
                    if b < 425 then
                      (7, 202707081)
                    else
                      (28, 3749437409166053003887713783230601)
              else
                if b < 429 then
                  if b < 427 then
                    (9, 36383773701)
                  else
                    if b < 428 then
                      (17, 231511263390695534857)
                    else
                      (25, 1067662676086285184303169330057)
                else
                  if b < 430 then
                    (53, 855565771287939693963672038339777633153111756810858452335550469)
                  else
                    if b < 431 then
                      (53, 525015882037386766178999152977632893293246567349801301469127733)
                    else
                      (68, 6574886636173003390102997929219822418390420704825549985457053648635520947836702137)
      else
        if b < 475 then
          if b < 453 then
            if b < 442 then
              if b < 437 then
                if b < 434 then
                  if b < 433 then
                    (81, 22941942218241892602464522687439643982088660609771228059991453613166401941480587424223529055607689)
                  else
                    (53, 3228010647058394350112653265976787158630031634203443949863980472)
                else
                  if b < 435 then
                    (67, 407319149534957615337613435324929774966630672513192885652850133556903701301448120)
                  else
                    if b < 436 then
                      (30, 1067272900513329515213308449482679896)
                    else
                      (41, 10948614297026923748122983547818280159492411022105)
              else
                if b < 439 then
                  if b < 438 then
                    (4, 49241)
                  else
                    (0, 0)
                else
                  if b < 440 then
                    (27, 51056203537615035172221925855330)
                  else
                    if b < 441 then
                      (51, 14234793614952742539963869000078068667822412527502466025391323)
                    else
                      (0, 0)
            else
              if b < 447 then
                if b < 444 then
                  if b < 443 then
                    (28, 2685794380437011008911624706086211)
                  else
                    (25, 655711520922186917528701981750)
                else
                  if b < 445 then
                    (44, 70895317776446416548254747637906085212947659941534601)
                  else
                    if b < 446 then
                      (48, 4630709465924463883051150909194649452123232414990073875897)
                    else
                      (0, 0)
              else
                if b < 450 then
                  if b < 448 then
                    (6, 9227148)
                  else
                    if b < 449 then
                      (62, 216968415260865747893782107638550612144456413580336343138594862422646869432)
                    else
                      (25, 194473009939794114844159018594)
                else
                  if b < 451 then
                    (0, 0)
                  else
                    if b < 452 then
                      (41, 3039580218768164222224726381468607543660830275140)
                    else
                      (69, 9684833610576557360946382634621492870184949862427947057112048218098662091743323201)
          else
            if b < 464 then
              if b < 458 then
                if b < 455 then
                  if b < 454 then
                    (39, 25233091773176953429626413991273815620387476579)
                  else
                    (51, 22068628174093125370050756181580285562316617235841973487685048)
                else
                  if b < 456 then
                    (39, 12995049777471238637817938630050362619652805974)
                  else
                    if b < 457 then
                      (7, 201609241)
                    else
                      (38, 2805738460750629372061685457830272868047783131)
              else
                if b < 461 then
                  if b < 459 then
                    (0, 0)
                  else
                    if b < 460 then
                      (17, 213108220506143568136)
                    else
                      (30, 189102866692692146245557138607068470)
                else
                  if b < 462 then
                    (29, 39445269824636735224824419930099128)
                  else
                    if b < 463 then
                      (14, 11054510760809332)
                    else
                      (0, 0)
            else
              if b < 469 then
                if b < 466 then
                  if b < 465 then
                    (43, 5046632402234366169434483238742886461798250761440689)
                  else
                    (62, 334911034733699990647578828678005096213901613586448931004683029350132876507)
                else
                  if b < 467 then
                    (14, 49729228483582729)
                  else
                    if b < 468 then
                      (44, 70895317776446416548254747637906085212947659941534601)
                    else
                      (45, 800610395934190105318988307255997232628066966839512504)
              else
                if b < 472 then
                  if b < 470 then
                    (31, 2764482104805805853615796014880458246)
                  else
                    if b < 471 then
                      (0, 0)
                    else
                      (14, 36254361458196834)
                else
                  if b < 473 then
                    (13, 2194434029675777)
                  else
                    if b < 474 then
                      (42, 58863794961606947983021415932511663677109850693681)
                    else
                      (14, 44345346152293745)
        else
          if b < 497 then
            if b < 486 then
              if b < 480 then
                if b < 477 then
                  if b < 476 then
                    (19, 9976906860023672165142)
                  else
                    (27, 273460255676862742104035636534025)
                else
                  if b < 478 then
                    (40, 229936699068777140558677405986373614111752061236)
                  else
                    if b < 479 then
                      (30, 189102866692692039964899572805493856)
                    else
                      (14, 62436143992247889)
              else
                if b < 483 then
                  if b < 481 then
                    (39, 61985778956797227606803122914685263813833786587)
                  else
                    if b < 482 then
                      (0, 0)
                    else
                      (8, 2019890514)
                else
                  if b < 484 then
                    (79, 97930104646006916374419716325464183116746448066715650881719214740844750430235470134242564918713)
                  else
                    if b < 485 then
                      (38, 1577068235823559589351650874454464417475819104)
                    else
                      (12, 22451902864774)
            else
              if b < 491 then
                if b < 488 then
                  if b < 487 then
                    (68, 1193899600236679572300129521493230278531207487301864559561788457090491557287716435)
                  else
                    (62, 124948218483913134197427902286775239772382268153460446132550000736646291812)
                else
                  if b < 489 then
                    (65, 1252390320278023975183484318636868560977319477160550989225352182288294844095257)
                  else
                    if b < 490 then
                      (31, 17019644038436987644639800352977347865)
                    else
                      (0, 0)
              else
                if b < 494 then
                  if b < 492 then
                    (47, 55813313804131047530039635218201310607134746437591828017)
                  else
                    if b < 493 then
                      (51, 20453098955225493436711951460944366120424113474383563838512009)
                    else
                      (0, 0)
                else
                  if b < 495 then
                    (17, 46658536227044615190)
                  else
                    if b < 496 then
                      (13, 2199834151243785)
                    else
                      (67, 37831381291314677191196807166490206524159960400109168191843938354347507576103684)
          else
            if b < 508 then
              if b < 502 then
                if b < 499 then
                  if b < 498 then
                    (31, 3389786874225447898054163361977230933)
                  else
                    (27, 49785090573879358663313041265670)
                else
                  if b < 500 then
                    (9, 49857778696)
                  else
                    if b < 501 then
                      (67, 408496783687078222911355827171144052807965295881508491468457457064944097372275931)
                    else
                      (39, 72630502775937655627662571626687395940807345371)
              else
                if b < 505 then
                  if b < 503 then
                    (13, 3244752527791697)
                  else
                    if b < 504 then
                      (34, 6948527600837265222300208580842998227973)
                    else
                      (7, 210502848)
                else
                  if b < 506 then
                    (0, 0)
                  else
                    if b < 507 then
                      (15, 899243110734027545)
                    else
                      (0, 0)
            else
              if b < 513 then
                if b < 510 then
                  if b < 509 then
                    (40, 116576944106358385817356716036041504351108358224)
                  else
                    (31, 18258625533445197613668891098465229705)
                else
                  if b < 511 then
                    (43, 5138717709743908347980423320348783163250097382247857)
                  else
                    if b < 512 then
                      (0, 0)
                    else
                      (29, 6626632309758430506955672244343072)
              else
                if b < 516 then
                  if b < 514 then
                    (48, 5033175363551001346528362108885728362199935484222822024411)
                  else
                    if b < 515 then
                      (15, 998264806728885624)
                    else
                      (9, 54888481033)
                else
                  if b < 517 then
                    (51, 17354563174819034410888031212411804984652782326188901597728177)
                  else
                    if b < 518 then
                      (77, 443493895649267284047670381847224070001007821782625660634223931541835468597570835723573022129)
                    else
                      (29, 22949363499416881829472394614821458)
    else
      if b < 606 then
        if b < 562 then
          if b < 540 then
            if b < 529 then
              if b < 524 then
                if b < 521 then
                  if b < 520 then
                    (24, 7202802968580369518829129798)
                  else
                    (18, 3776816794388745673480)
                else
                  if b < 522 then
                    (8, 2630585481)
                  else
                    if b < 523 then
                      (26, 2636415583459796040085156417824)
                    else
                      (25, 1067662676086285184303169330057)
              else
                if b < 526 then
                  if b < 525 then
                    (17, 45560304831643936021)
                  else
                    (66, 4663670313424529579297380943332930775512529247272908435788236160509732653680741)
                else
                  if b < 527 then
                    (14, 48723584400510385)
                  else
                    if b < 528 then
                      (14, 48587266015998216)
                    else
                      (0, 0)
            else
              if b < 534 then
                if b < 531 then
                  if b < 530 then
                    (25, 194473010011550249894726156388)
                  else
                    (52, 299642496103256375843276479789955251723718148807271608408660761)
                else
                  if b < 532 then
                    (36, 475162193523549038762153851455991953360091)
                  else
                    if b < 533 then
                      (23, 1367888800441709726734681700)
                    else
                      (0, 0)
              else
                if b < 537 then
                  if b < 535 then
                    (27, 42182649340444647939435202635075)
                  else
                    if b < 536 then
                      (50, 1284742816241640100065879363735627286461959431211455489639643)
                    else
                      (9, 54972371081)
                else
                  if b < 538 then
                    (41, 20047741988938248961915591517866657335877490986425)
                  else
                    if b < 539 then
                      (40, 1136553977397113705518702946680933223353097932209)
                    else
                      (30, 652875933843503951896052290853817785)
          else
            if b < 551 then
              if b < 545 then
                if b < 542 then
                  if b < 541 then
                    (13, 717785227662854)
                  else
                    (17, 38588073394102867220)
                else
                  if b < 543 then
                    (82, 463223854811413279459392244449629488729529227490598638618792048050204707799969746917654387883003313)
                  else
                    if b < 544 then
                      (7, 30250584)
                    else
                      (13, 1244087614440800)
              else
                if b < 548 then
                  if b < 546 then
                    (24, 53683242806846185791031193864)
                  else
                    if b < 547 then
                      (31, 10425378774937095101133901310175896969)
                    else
                      (9, 54496923785)
                else
                  if b < 549 then
                    (37, 307271166631890869531050649886236087599629531)
                  else
                    if b < 550 then
                      (16, 1677033250166805603)
                    else
                      (20, 211665220107255788405062)
            else
              if b < 556 then
                if b < 553 then
                  if b < 552 then
                    (31, 3363585872984487815719439481640870149)
                  else
                    (7, 210502848)
                else
                  if b < 554 then
                    (31, 17012720048420688273131875801827171097)
                  else
                    if b < 555 then
                      (9, 54496923785)
                    else
                      (0, 0)
              else
                if b < 559 then
                  if b < 557 then
                    (4, 49241)
                  else
                    if b < 558 then
                      (4, 4233)
                    else
                      (48, 893013020866096760480634163491225926240827708606447498836)
                else
                  if b < 560 then
                    (39, 11873360229563141493065337427611748217429316966)
                  else
                    if b < 561 then
                      (0, 0)
                    else
                      (6, 13416648)
        else
          if b < 584 then
            if b < 573 then
              if b < 567 then
                if b < 564 then
                  if b < 563 then
                    (16, 15770897570219744137)
                  else
                    (69, 97454036593472105953424079319352659603708613158473989342045774543853245494337002265)
                else
                  if b < 565 then
                    (0, 0)
                  else
                    if b < 566 then
                      (8, 3430203656)
                    else
                      (54, 8400254112598188258863986447642381302664581104899509840930103312)
              else
                if b < 570 then
                  if b < 568 then
                    (9, 54496923785)
                  else
                    if b < 569 then
                      (27, 217783863728010461798594754435977)
                    else
                      (28, 2443821702351976720115209099824561)
                else
                  if b < 571 then
                    (41, 1865231105701734173077707456576625910528229401697)
                  else
                    if b < 572 then
                      (0, 0)
                    else
                      (19, 60678654217354647755545)
            else
              if b < 578 then
                if b < 575 then
                  if b < 574 then
                    (75, 320484983607750788916270236961097070730531692084490222696207844653672548835512019774932501)
                  else
                    (45, 122239785743268850766820635874205755672468382160020673)
                else
                  if b < 576 then
                    (54, 89702178459033352288151363537406241956619740011212324078320897457)
                  else
                    if b < 577 then
                      (13, 2212748918654171)
                    else
                      (19, 60678654217354647755545)
              else
                if b < 581 then
                  if b < 579 then
                    (84, 93933882536087458826476914618888409499471259762098275584015812793343273122859212008803201115989495224)
                  else
                    if b < 580 then
                      (13, 3609031294870854)
                    else
                      (29, 45450096040712200237627708891221425)
                else
                  if b < 582 then
                    (23, 2376095235963658394318949816)
                  else
                    if b < 583 then
                      (0, 0)
                    else
                      (17, 27113560757957101076)
          else
            if b < 595 then
              if b < 589 then
                if b < 586 then
                  if b < 585 then
                    (26, 17571240206910722211754408955313)
                  else
                    (50, 208878362130844651846599618735297349104272464249065109701680)
                else
                  if b < 587 then
                    (25, 931197915898386888162604331145)
                  else
                    if b < 588 then
                      (18, 429320512488275862613)
                    else
                      (58, 3231065770711852977267768985062797727767878096807665339415996137790345)
              else
                if b < 592 then
                  if b < 590 then
                    (25, 781480915846972693392853031689)
                  else
                    if b < 591 then
                      (19, 41571347602482957387366)
                    else
                      (52, 348478508424983758456825160979641840094583619111248887885989083)
                else
                  if b < 593 then
                    (56, 23034103505571767527208868130135266579642834898823939942371366555064)
                  else
                    if b < 594 then
                      (53, 525015882037386766178999152977632893293253166884372813108760928)
                    else
                      (52, 113639742707085255640256857338295267047562691144285460016547350)
            else
              if b < 600 then
                if b < 597 then
                  if b < 596 then
                    (84, 111467533628234162208799629147970279665993433355420656098203413639621712922724010233290765499216747289)
                  else
                    (16, 13658427839953230600)
                else
                  if b < 598 then
                    (27, 260955223033386739612087857175297)
                  else
                    if b < 599 then
                      (27, 171479548166497315943789353780837)
                    else
                      (8, 2630405392)
              else
                if b < 603 then
                  if b < 601 then
                    (26, 16226256514009337302012116917129)
                  else
                    if b < 602 then
                      (0, 0)
                    else
                      (39, 56231142475766475329223288337775750707297668537)
                else
                  if b < 604 then
                    (0, 0)
                  else
                    if b < 605 then
                      (22, 48946616485996357335990353)
                    else
                      (0, 0)
      else
        if b < 649 then
          if b < 627 then
            if b < 616 then
              if b < 611 then
                if b < 608 then
                  if b < 607 then
                    (34, 67967860931960104326929158421261267783096)
                  else
                    (42, 205771027704016620225747244429410335344619591585201)
                else
                  if b < 609 then
                    (42, 193531881072288873608056020569449712769948110832977)
                  else
                    if b < 610 then
                      (69, 17273383970833311544225530708150863599256851577475367062001940443936688978891505728)
                    else
                      (0, 0)
              else
                if b < 613 then
                  if b < 612 then
                    (41, 3039580218768164222224726381468605158719879517795)
                  else
                    (52, 226250978152080785238975961657932519326575234885475205539450289)
                else
                  if b < 614 then
                    (8, 3350532233)
                  else
                    if b < 615 then
                      (70, 1439854572086722154534360080008430301128550143461914999454477315026478781114953816857)
                    else
                      (25, 938277385533858034426018519817)
            else
              if b < 621 then
                if b < 618 then
                  if b < 617 then
                    (40, 710715674078853759844041725791100855716344253880)
                  else
                    (9, 53616521473)
                else
                  if b < 619 then
                    (0, 0)
                  else
                    if b < 620 then
                      (13, 3621638777693456)
                    else
                      (17, 218468567307975151025)
              else
                if b < 624 then
                  if b < 622 then
                    (8, 280306757)
                  else
                    if b < 623 then
                      (67, 37831381291314677191196807166490206524159960400109168191843938352095707952199238)
                    else
                      (0, 0)
                else
                  if b < 625 then
                    (80, 1573200559934700237830320179732872820923524824024602148356980743527413297675633392610461937359641)
                  else
                    if b < 626 then
                      (41, 17159347200451307883478442738117754615540778064777)
                    else
                      (40, 755983910438628412531468830349412940507506552932)
          else
            if b < 638 then
              if b < 632 then
                if b < 629 then
                  if b < 628 then
                    (34, 69673955907935007113239335669648393784753)
                  else
                    (45, 914334827564970450038343546925418517538049195897802168)
                else
                  if b < 630 then
                    (30, 980527480808028948721509256385078872)
                  else
                    if b < 631 then
                      (4, 51033)
                    else
                      (27, 51301603116636593578369784022530)
              else
                if b < 635 then
                  if b < 633 then
                    (26, 3191012721377640859369513641538)
                  else
                    if b < 634 then
                      (43, 941820719385711167728342654920186618833753600315714)
                    else
                      (39, 54052636833675430948897990372648534120048493787)
                else
                  if b < 636 then
                    (16, 1677033251907458148)
                  else
                    if b < 637 then
                      (16, 15549245918741894744)
                    else
                      (16, 15743894562120158648)
            else
              if b < 643 then
                if b < 640 then
                  if b < 639 then
                    (16, 10195525970280211720)
                  else
                    (28, 3484523231058095927995564766023089)
                else
                  if b < 641 then
                    (37, 98566764738972474334478179653407793997000790)
                  else
                    if b < 642 then
                      (31, 16909644847551200441678141117717040561)
                    else
                      (69, 66276588904449170945847537663745405237670613576562667693144338367694024556519902648)
              else
                if b < 646 then
                  if b < 644 then
                    (27, 192483811185801718592157804859417)
                  else
                    if b < 645 then
                      (14, 12616230481802580)
                    else
                      (16, 13672031337114491656)
                else
                  if b < 647 then
                    (56, 23034103505571767527208868130135266579642834898823939942371366555064)
                  else
                    if b < 648 then
                      (70, 1076376958421597141158693308183091474736897090293777281057878624829414401652493179785)
                    else
                      (13, 2194053119763712)
        else
          if b < 671 then
            if b < 660 then
              if b < 654 then
                if b < 651 then
                  if b < 650 then
                    (12, 230238237773240)
                  else
                    (24, 67928124162482019077946071816)
                else
                  if b < 652 then
                    (34, 69583163067401222117649530444960233817307)
                  else
                    if b < 653 then
                      (20, 1036703359132709830891097)
                    else
                      (40, 1081730880695820591722189696811389568205264539057)
              else
                if b < 657 then
                  if b < 655 then
                    (13, 3866809716234597)
                  else
                    if b < 656 then
                      (13, 2389072958612560)
                    else
                      (19, 10749253265317767308886)
                else
                  if b < 658 then
                    (0, 0)
                  else
                    if b < 659 then
                      (56, 17677574791283145762568685260890817046258360256857902031869699294427)
                    else
                      (30, 984200701444356686217083679378787768)
            else
              if b < 665 then
                if b < 662 then
                  if b < 661 then
                    (19, 65188324697023885364665)
                  else
                    (39, 25233091773176953429626413991273815622518460418)
                else
                  if b < 663 then
                    (39, 12995049777471238637817938630050574567408534114)
                  else
                    if b < 664 then
                      (13, 3797215430141209)
                    else
                      (7, 203116569)
              else
                if b < 668 then
                  if b < 666 then
                    (41, 11496298213331624729122243327380941757161075133873)
                  else
                    if b < 667 then
                      (0, 0)
                    else
                      (56, 7447494178051539313639873402522562388749038981597394977275089602051)
                else
                  if b < 669 then
                    (50, 770251970533866072223226746907161730796934835246424289237897)
                  else
                    if b < 670 then
                      (52, 303287876869603180072136592842006326271036615395482098928209337)
                    else
                      (23, 3672059299328991195677721819)
          else
            if b < 682 then
              if b < 676 then
                if b < 673 then
                  if b < 672 then
                    (26, 14552252168155426052408899787521)
                  else
                    (58, 3311471294024657059010118860456984463505728256462018177463696731986825)
                else
                  if b < 674 then
                    (22, 169834151486452512151982105)
                  else
                    if b < 675 then
                      (45, 1230135395293902789595772920755442505726516417532320537)
                    else
                      (49, 14288208333857548167690146615859535515425644701837968194401)
              else
                if b < 679 then
                  if b < 677 then
                    (39, 25233091773176953429626413991271430679545930053)
                  else
                    if b < 678 then
                      (41, 3678987185100434248938838495781978979819371714048)
                    else
                      (5, 842085)
                else
                  if b < 680 then
                    (30, 1067272900513329515213308449482679896)
                  else
                    if b < 681 then
                      (0, 0)
                    else
                      (80, 1033310464427133493698052138247649290933768690615475876564694246690913642858036821546936119384969)
            else
              if b < 687 then
                if b < 684 then
                  if b < 683 then
                    (0, 0)
                  else
                    (26, 2636415581711755159959229588821)
                else
                  if b < 685 then
                    (16, 15747924035886474633)
                  else
                    if b < 686 then
                      (13, 694674827593568)
                    else
                      (6, 13401201)
              else
                if b < 690 then
                  if b < 688 then
                    (14, 53133673805747801)
                  else
                    if b < 689 then
                      (26, 10717471760169310275925391594244)
                    else
                      (25, 931197915898386888162604331145)
                else
                  if b < 691 then
                    (7, 210533384)
                  else
                    if b < 692 then
                      (49, 55422460959708315393905932973719152687424144512413887122873)
                    else
                      (13, 2107597986661456)

def forward3Blocks (b : Nat) : Nat :=
  if b < 1 then
    60768629481662002724040844240193128395875620402103257715783839071196353363858761627491000308947048441246949945038269621324486387035688755792157198112387551709263868653188426115240536499095822481535322470068846267283514686999842884253977651478665298374002122213923865622984581757919035727327691704178213486243596205931606783966885500969067144500005572044383044076541478842716406332994193043004428034070255597580642797616597923766732931315530895838396096812294676038803325594766961577063602246784270765864961154505362216747337682641212813034140384742889644486864899324692920916497901024594798761217890299533642719891989318843319643271836078386802899864021947433654609022253408105239160665119067923554659561833851130742772920192748163429808944695868122266037148444503579651
  else
    if b < 2 then
      121727728836776970937492058893519696371849526608794330588054402866883918384715612701415140016693531486411030239626855388179938294996545065243365404900855692734124333952963499769034512205871286623682011096357055076652014787014171447358002297565975878476574611621145122331820741519954408341241567941224567247596612447713204625062247014545340502282458011404794890053184387176568922082768121534271413706062122464574465642308719048917967684417068428271894922925434671723409241951220066845969494137216353331130751891128215105537096186544485032600981737319418777398489781611934040719017618788408389927515171218885759123715204389231858881732907670588325307802111204535131302665992661335461224530116932416394781525062991766836747817118148416911415364762074167602591942213607471310
    else
      38400144108247805022538796582390855111790781069371996634681500986290260124995128841278399807706204789597334448187580229353293922793346026614611997283096277364135848536100939109215993393427738118022223489005987107487138306492422610345829625186662223336601210625094359528488600534528705188634520504466270593976712580839745656588659467301110694498126303928780772218191724129453792315326524329224669134278443136997347008714947831074811871254537921107850677836024483736104521515481315956725188528363713483901898588896458311569651202651629542009390749

def backward3Blocks (b : Nat) : Nat :=
  if b < 1 then
    171179257198149621435071310718910873076325764551320076085360801527940272111053793282018216863770580361441157486947042375267598363154644354410240261411434773333895557151140972162501851233783598284300021780651034718714539570505671806608074245107379485961455170567419746375844180196628026522060277507436816090847211261995834055018396603903212912133220421150197117891048269749447079042122467275831750593105185334278883961962114194827194062686800411722390699423477678724881296233189510590613099202617924704561587176358917010069922383923569349544230231653975674672092950052383776039589714401431670995756840374580983342668579312823155524230202262502396660284497802408918280190751628240095985842956634684250782480939416534413994963732008824440968710203887893213060871892202713094
  else
    if b < 2 then
      125473392428695007166107705181576970944540431443912202295896190746858495101100763609794391551757455908321352497035444982853351791858500342809716046048771021610878493546996595597879681744164568003538736328353101447440361548959979700592875336212621076569489249246867879550404978508665921184180305481328317900754430735366146340158031480609667776173429647194022054079377145053581264813531468664474530431850548615590451518468161886080888107972317178978875984512352265658044800883771157368542190714666735733126227944562944897686647103291019197565623136421424401041686147846263851876525370601062845568574084520085976549776927873038604958290467388458061666286127484283215431723319788415541276607969650200246874288082899283679085810847459942843562699011431426837532208723911574657
    else
      43131114245893525621805234549602065501737670884778372851994711609477509125380432817881997845641127332962408240201729960311613691008483182466559558476015749957914560035356939107688520241002834909801109952015500173315194236229571373881244585343344310488242031638465059574637475381865418663579564171225186947222690887933840280503770132809876993745798228748481297480308325727159724058947445787899583942278935078551773401439818707860006450051348244429883829425201578026685765183819155067646854598772346171096359706417680472873936361596666161991423368

def factorCode3 (b : Nat) : Nat × Nat :=
  if b < 346 then
    if b < 173 then
      if b < 86 then
        if b < 43 then
          if b < 21 then
            if b < 10 then
              if b < 5 then
                (0, 0)
              else
                if b < 7 then
                  if b < 6 then
                    (0, 0)
                  else
                    (1, 4)
                else
                  if b < 8 then
                    (2, 113)
                  else
                    (0, 0)
            else
              if b < 15 then
                if b < 12 then
                  if b < 11 then
                    (4, 43792)
                  else
                    (3, 2164)
                else
                  if b < 13 then
                    (2, 164)
                  else
                    if b < 14 then
                      (0, 0)
                    else
                      (4, 31296)
              else
                if b < 18 then
                  if b < 16 then
                    (3, 1857)
                  else
                    if b < 17 then
                      (4, 16641)
                    else
                      (0, 0)
                else
                  (0, 0)
          else
            if b < 32 then
              if b < 26 then
                if b < 23 then
                  if b < 22 then
                    (0, 0)
                  else
                    (16, 8987992643204340617)
                else
                  if b < 24 then
                    (0, 0)
                  else
                    if b < 25 then
                      (0, 0)
                    else
                      (2, 161)
              else
                if b < 29 then
                  if b < 27 then
                    (0, 0)
                  else
                    if b < 28 then
                      (0, 0)
                    else
                      (4, 32840)
                else
                  if b < 30 then
                    (0, 0)
                  else
                    if b < 31 then
                      (0, 0)
                    else
                      (4, 30884)
            else
              if b < 37 then
                if b < 34 then
                  (0, 0)
                else
                  if b < 35 then
                    (11, 13931745382537)
                  else
                    (0, 0)
              else
                (0, 0)
        else
          if b < 64 then
            if b < 53 then
              if b < 48 then
                if b < 45 then
                  if b < 44 then
                    (0, 0)
                  else
                    (3, 2872)
                else
                  if b < 46 then
                    (0, 0)
                  else
                    if b < 47 then
                      (0, 0)
                    else
                      (3, 1072)
              else
                if b < 50 then
                  if b < 49 then
                    (1, 4)
                  else
                    (0, 0)
                else
                  if b < 51 then
                    (34, 6948527600837265222300208580842996392034)
                  else
                    (0, 0)
            else
              if b < 58 then
                if b < 55 then
                  (0, 0)
                else
                  if b < 56 then
                    (17, 163486373728551228005)
                  else
                    (0, 0)
              else
                if b < 61 then
                  if b < 59 then
                    (0, 0)
                  else
                    if b < 60 then
                      (0, 0)
                    else
                      (22, 48118965466346736657172070)
                else
                  if b < 62 then
                    (0, 0)
                  else
                    if b < 63 then
                      (7, 142299216)
                    else
                      (20, 886814270882059677492617)
          else
            if b < 75 then
              if b < 69 then
                if b < 66 then
                  (0, 0)
                else
                  if b < 67 then
                    (20, 96430188237694976414032)
                  else
                    if b < 68 then
                      (35, 181173099464357758515547002724755721049621)
                    else
                      (20, 96430188237694991164228)
              else
                if b < 72 then
                  if b < 70 then
                    (15, 970477033901542841)
                  else
                    if b < 71 then
                      (0, 0)
                    else
                      (8, 105271652)
                else
                  if b < 73 then
                    (0, 0)
                  else
                    if b < 74 then
                      (17, 216302498597601915017)
                    else
                      (27, 46167691099688306896518863267394)
            else
              if b < 80 then
                if b < 77 then
                  if b < 76 then
                    (41, 20034174851862641994971313220383516778528690799835)
                  else
                    (0, 0)
                else
                  (0, 0)
              else
                if b < 83 then
                  (0, 0)
                else
                  if b < 84 then
                    (0, 0)
                  else
                    if b < 85 then
                      (56, 7447494178051539313639873402522518621229600374221301760573479192086)
                    else
                      (0, 0)
      else
        if b < 129 then
          if b < 107 then
            if b < 96 then
              if b < 91 then
                if b < 88 then
                  if b < 87 then
                    (26, 17576424689804998563161679351224)
                  else
                    (0, 0)
                else
                  (0, 0)
              else
                if b < 93 then
                  if b < 92 then
                    (0, 0)
                  else
                    (13, 640705428218180)
                else
                  if b < 94 then
                    (25, 756644630563005402847160008112)
                  else
                    (0, 0)
            else
              if b < 101 then
                if b < 98 then
                  if b < 97 then
                    (4, 45832)
                  else
                    (20, 665141563018201989317952)
                else
                  if b < 99 then
                    (15, 635495766156434313)
                  else
                    (0, 0)
              else
                if b < 104 then
                  if b < 102 then
                    (20, 942939608552476682243512)
                  else
                    if b < 103 then
                      (0, 0)
                    else
                      (63, 6215524360104764916551529550372602391019219158862823304588338267033572793113)
                else
                  if b < 105 then
                    (19, 55446070636819262891273)
                  else
                    if b < 106 then
                      (42, 58863794961606947983021415932511663677109599356225)
                    else
                      (0, 0)
          else
            if b < 118 then
              if b < 112 then
                if b < 109 then
                  if b < 108 then
                    (41, 11462518001651130269291833100561269104293317725625)
                  else
                    (61, 14622855496679860317125082749251063906980739409979406532678123050720069157)
                else
                  (0, 0)
              else
                if b < 115 then
                  if b < 113 then
                    (0, 0)
                  else
                    if b < 114 then
                      (9, 37711266049)
                    else
                      (8, 2159367249)
                else
                  if b < 116 then
                    (34, 42147518534395330458175390960417306070449)
                  else
                    if b < 117 then
                      (27, 259929299033631230768942558326809)
                    else
                      (0, 0)
            else
              if b < 123 then
                if b < 120 then
                  if b < 119 then
                    (52, 53472860705496230872729502396236080486896337296319357377713744)
                  else
                    (25, 180342543640433486043405444710)
                else
                  if b < 121 then
                    (41, 15326093039266804143800725048607733786314568686473)
                  else
                    if b < 122 then
                      (28, 414164512986724775376744069026853)
                    else
                      (26, 14566793132657730152862637378993)
              else
                if b < 126 then
                  if b < 124 then
                    (29, 9362102061504157867393784239248982)
                  else
                    if b < 125 then
                      (0, 0)
                    else
                      (6, 12367753)
                else
                  if b < 127 then
                    (50, 128177705575533878461669715082431174459919581458083092915542)
                  else
                    (0, 0)
        else
          if b < 151 then
            if b < 140 then
              if b < 134 then
                if b < 131 then
                  if b < 130 then
                    (78, 7160387280244163490251490796813533838704549973657285990478532501697017797829861176030685092633)
                  else
                    (78, 4427592087856446242965852129806664810270826007211874945011589077848045739628483000834224836024)
                else
                  if b < 132 then
                    (0, 0)
                  else
                    if b < 133 then
                      (77, 74188619245979690949827912039751679792965027429182711776893938495247800544223053566915776576)
                    else
                      (48, 5341476267386335555883774312546550949521104500668030274993)
              else
                if b < 137 then
                  if b < 135 then
                    (26, 9961043184111847345411195394817)
                  else
                    if b < 136 then
                      (48, 4261091024951428687331568244080156736720920469236642798473)
                    else
                      (49, 51950818746177632750704883155105534012039777613949605079894)
                else
                  if b < 138 then
                    (6, 8081489)
                  else
                    if b < 139 then
                      (77, 286823088964160466507041598232334570290901690487356766050140795441044530079449926501285627099)
                    else
                      (7, 197905532)
            else
              if b < 145 then
                if b < 142 then
                  (0, 0)
                else
                  if b < 143 then
                    (21, 10642264986235636805882949)
                  else
                    if b < 144 then
                      (0, 0)
                    else
                      (48, 893013020866096760480634163491220969714155943001504088673)
              else
                if b < 148 then
                  (0, 0)
                else
                  if b < 149 then
                    (79, 106279839987463228593561509499561832362789013387019995077866727522313068481385828027430049172913)
                  else
                    if b < 150 then
                      (20, 96430188237695008194896)
                    else
                      (0, 0)
          else
            if b < 162 then
              if b < 156 then
                if b < 153 then
                  if b < 152 then
                    (20, 192687075335786580891222)
                  else
                    (0, 0)
                else
                  if b < 154 then
                    (42, 318227615010223879383828423013341546452945500917177)
                  else
                    if b < 155 then
                      (42, 29843697691227746769243319305225756975554464470053)
                    else
                      (23, 2628038481488292164495792921)
              else
                if b < 159 then
                  (0, 0)
                else
                  if b < 160 then
                    (0, 0)
                  else
                    if b < 161 then
                      (0, 0)
                    else
                      (67, 74618725014792473268758095093326892408200467956366534972611778567943774631847265)
            else
              if b < 167 then
                if b < 164 then
                  if b < 163 then
                    (0, 0)
                  else
                    (66, 19837455287245208823211704903716460529382045577034492919821992330683870135769881)
                else
                  if b < 165 then
                    (16, 13598493486881233801)
                  else
                    if b < 166 then
                      (0, 0)
                    else
                      (11, 1403243955828)
              else
                if b < 170 then
                  if b < 168 then
                    (0, 0)
                  else
                    if b < 169 then
                      (28, 4112089210316711392017067230121393)
                    else
                      (0, 0)
                else
                  if b < 171 then
                    (0, 0)
                  else
                    if b < 172 then
                      (0, 0)
                    else
                      (30, 106026116956134798913272784125714528)
    else
      if b < 259 then
        if b < 216 then
          if b < 194 then
            if b < 183 then
              if b < 178 then
                if b < 175 then
                  if b < 174 then
                    (17, 47042742933181539588)
                  else
                    (0, 0)
                else
                  if b < 176 then
                    (68, 6069095915473902431056347766170704849748691942983340595308281147903045207312358169)
                  else
                    if b < 177 then
                      (46, 6773456496422604062572530349391416731331992536343713125)
                    else
                      (0, 0)
              else
                if b < 180 then
                  if b < 179 then
                    (52, 322666908237426470476310062582200492999088278936911930468916105)
                  else
                    (24, 43208051695612875802207604145)
                else
                  if b < 181 then
                    (22, 85493050027606857921094497)
                  else
                    if b < 182 then
                      (25, 350179493363258396010710786627)
                    else
                      (18, 429320512488399590672)
            else
              if b < 188 then
                if b < 185 then
                  if b < 184 then
                    (7, 210580857)
                  else
                    (85, 291133945710398413129046404852503681595783562160763511059942649838101359172758308970735896213192971845)
                else
                  if b < 186 then
                    (25, 613326436777768011104300060088)
                  else
                    if b < 187 then
                      (7, 147309632)
                    else
                      (79, 21003303885717555702416686249482457627396124972449151234618677307223084160475346650014486505027)
              else
                if b < 191 then
                  if b < 189 then
                    (0, 0)
                  else
                    if b < 190 then
                      (37, 242307186374369894966242071704489971180428169)
                    else
                      (24, 62106471042630529243301676251)
                else
                  if b < 192 then
                    (0, 0)
                  else
                    if b < 193 then
                      (0, 0)
                    else
                      (45, 792706584872095226298597460252464813416147274090724417)
          else
            if b < 205 then
              if b < 199 then
                if b < 196 then
                  if b < 195 then
                    (18, 2610995605535818010033)
                  else
                    (14, 11396272215447108)
                else
                  if b < 197 then
                    (45, 939035042621294552664011232123353922280170711412955929)
                  else
                    if b < 198 then
                      (58, 897125734194022652537651371274170330851255056833034294513482240104003)
                    else
                      (0, 0)
              else
                if b < 202 then
                  if b < 200 then
                    (42, 299408127584139682090469327068639470390858328591800)
                  else
                    if b < 201 then
                      (27, 147524341865200207268255102142049)
                    else
                      (0, 0)
                else
                  if b < 203 then
                    (31, 3025645867083074339928914218820130150)
                  else
                    if b < 204 then
                      (0, 0)
                    else
                      (73, 2198112305487337936825598147131733066239755574187683534310899442050470750874125769721441)
            else
              if b < 210 then
                if b < 207 then
                  if b < 206 then
                    (34, 53591091890753068825258065702655266672056)
                  else
                    (0, 0)
                else
                  if b < 208 then
                    (0, 0)
                  else
                    if b < 209 then
                      (0, 0)
                    else
                      (24, 21886218702107689980572927510)
              else
                if b < 213 then
                  if b < 211 then
                    (26, 10717471762234340751028266487907)
                  else
                    if b < 212 then
                      (51, 12431733878877703095348732492007297121877408415472733697101240)
                    else
                      (13, 3867909108235696)
                else
                  if b < 214 then
                    (0, 0)
                  else
                    if b < 215 then
                      (0, 0)
                    else
                      (14, 37272884617761126)
        else
          if b < 237 then
            if b < 226 then
              if b < 221 then
                if b < 218 then
                  if b < 217 then
                    (48, 5438412680517311816753791697986096257062641333129363981531)
                  else
                    (66, 16194490940415201876693287669334271078010300791986851134110624417206529450593713)
                else
                  if b < 219 then
                    (50, 977960286160665184255595743773302176772336519058582149287345)
                  else
                    if b < 220 then
                      (51, 22270013504731096472199909905987004363249533453884523437641137)
                    else
                      (0, 0)
              else
                if b < 223 then
                  if b < 222 then
                    (26, 16205773609745602755962681012489)
                  else
                    (0, 0)
                else
                  if b < 224 then
                    (7, 126734679)
                  else
                    if b < 225 then
                      (40, 690017972916121251936219958643009300987904318233)
                    else
                      (9, 8984482901)
            else
              if b < 231 then
                if b < 228 then
                  if b < 227 then
                    (13, 507039439349334)
                  else
                    (10, 535725617289)
                else
                  if b < 229 then
                    (39, 78333936169596348713260406188984505657255658715)
                  else
                    if b < 230 then
                      (12, 136054835042661)
                    else
                      (38, 4879484538981277188592475283444095248157246683)
              else
                if b < 234 then
                  if b < 232 then
                    (72, 390217110888861436061280775363638133394711643401632905510846637835414470637451720281529)
                  else
                    if b < 233 then
                      (6, 10189896)
                    else
                      (0, 0)
                else
                  if b < 235 then
                    (0, 0)
                  else
                    if b < 236 then
                      (26, 11160510218453944051545577675657)
                    else
                      (26, 3111568158670806658429203383652)
          else
            if b < 248 then
              if b < 242 then
                if b < 239 then
                  if b < 238 then
                    (57, 346346567019474696419414746735657942261288961188174055567803958709681)
                  else
                    (79, 113001171504860829973927052399769031707871844992451449535547585765142002043028272674170206178744)
                else
                  if b < 240 then
                    (16, 9042257941127777720)
                  else
                    if b < 241 then
                      (0, 0)
                    else
                      (7, 209470329)
              else
                if b < 245 then
                  if b < 243 then
                    (7, 146914329)
                  else
                    if b < 244 then
                      (15, 625116139066457520)
                    else
                      (11, 12630368784521)
                else
                  if b < 246 then
                    (40, 116576944106358385817356716036040216407812752214)
                  else
                    if b < 247 then
                      (0, 0)
                    else
                      (15, 596366151922311942)
            else
              if b < 253 then
                if b < 250 then
                  if b < 249 then
                    (37, 194912769860927294537300027730576431653378953)
                  else
                    (18, 3792415825680462992721)
                else
                  if b < 251 then
                    (51, 22222823340012867525877488325845570349209007861039215015156617)
                  else
                    if b < 252 then
                      (7, 147479417)
                    else
                      (42, 251154838737096605776703488458633882986036712197561)
              else
                if b < 256 then
                  if b < 254 then
                    (0, 0)
                  else
                    if b < 255 then
                      (0, 0)
                    else
                      (65, 774819718888233937385802904126517340821575607154921784161472748718960194935689)
                else
                  if b < 257 then
                    (42, 205846176288046995410545268850324844710891043704241)
                  else
                    if b < 258 then
                      (68, 5449840415941673202872425703249155626025065132281661688089109484875007576714304281)
                    else
                      (17, 38590450638462148929)
      else
        if b < 302 then
          if b < 280 then
            if b < 269 then
              if b < 264 then
                if b < 261 then
                  if b < 260 then
                    (21, 5343315549090063354061237)
                  else
                    (39, 25233091773176953429626413991273815620637230640)
                else
                  if b < 262 then
                    (29, 65156828878659626515958426559860153)
                  else
                    if b < 263 then
                      (16, 15541303805591673608)
                    else
                      (26, 3205143185610966151914795918896)
              else
                if b < 266 then
                  if b < 265 then
                    (25, 776746766854220819732986088889)
                  else
                    (46, 19585286469233222877768075475942216702645042879287057177)
                else
                  if b < 267 then
                    (0, 0)
                  else
                    if b < 268 then
                      (52, 330800046068485978694520131150309516829496255724887555585363385)
                    else
                      (14, 62443172521993480)
            else
              if b < 274 then
                if b < 271 then
                  if b < 270 then
                    (78, 7188298554192749852244731764529817142148584334981511124074062825635725829800819004766048093403)
                  else
                    (39, 72712786867281285141683780289550958124163531995)
                else
                  if b < 272 then
                    (29, 66716884763158215794645711271125524)
                  else
                    if b < 273 then
                      (53, 4661512587600752864723415279503248564036990950359298051756393691)
                    else
                      (19, 54233773467007249829305)
              else
                if b < 277 then
                  if b < 275 then
                    (80, 170377394686475933980806271079225873269315719702641589316467471582448963490140105543957424002145)
                  else
                    if b < 276 then
                      (54, 8400254112598188258863986447642126292691946520842886813474632806)
                    else
                      (0, 0)
                else
                  if b < 278 then
                    (52, 53472860705496230872729502396236102072069591081336219075953701)
                  else
                    if b < 279 then
                      (47, 202932885727256377932440949824630992234532218296366883685)
                    else
                      (40, 958258955630020945140815867386901321875804521691)
          else
            if b < 291 then
              if b < 285 then
                if b < 282 then
                  if b < 281 then
                    (30, 641144461363691802924047128202333625)
                  else
                    (28, 3808883347822833502785795504080091)
                else
                  if b < 283 then
                    (14, 34196002428475749)
                  else
                    if b < 284 then
                      (26, 10893181810548248327191969389321)
                    else
                      (85, 1099941174536129394159452110865987927149151558888632222580163620057246298000252281542476184697887018424)
              else
                if b < 288 then
                  if b < 286 then
                    (20, 594274305976694011350457)
                  else
                    if b < 287 then
                      (27, 147524341302873050991565891526980)
                    else
                      (40, 1146527765569013088806475806367435154251199827384)
                else
                  if b < 289 then
                    (30, 819005431919646571579648680531086776)
                  else
                    if b < 290 then
                      (51, 19065024328326251580238355662858065952684349064295733958859657)
                    else
                      (14, 37272884517077572)
            else
              if b < 296 then
                if b < 293 then
                  if b < 292 then
                    (20, 333957215995030301722115)
                  else
                    (34, 42823529930651547494643644154104479275801)
                else
                  if b < 294 then
                    (25, 989691040845782801943223094713)
                  else
                    if b < 295 then
                      (51, 3657781333467532330928677533660061393880915292250969729144368)
                    else
                      (27, 158265170008586458827819652115286)
              else
                if b < 299 then
                  if b < 297 then
                    (34, 42823529930651547494643644154104479275801)
                  else
                    if b < 298 then
                      (43, 851643582216355095368036426058994454853946340763233)
                    else
                      (25, 350179493274060378039023310369)
                else
                  if b < 300 then
                    (45, 1215906229883091061982084653654305667368131881850654136)
                  else
                    if b < 301 then
                      (0, 0)
                    else
                      (49, 27744077809346986240297084311107242931543426615909250654981)
        else
          if b < 324 then
            if b < 313 then
              if b < 307 then
                if b < 304 then
                  if b < 303 then
                    (25, 199438295083669783123614052434)
                  else
                    (79, 69054482681367130939289266720525307712999934264604823510518635937791880847148884057082376045907)
                else
                  if b < 305 then
                    (51, 3657781333467532330928677533660061393883112887566328145512019)
                  else
                    if b < 306 then
                      (65, 240820355547707263208274003017007213783727459663339030469502067027568375438614)
                    else
                      (41, 3678987185100434248938838495781977973597100525110)
              else
                if b < 310 then
                  if b < 308 then
                    (25, 21669822128494832168730911846)
                  else
                    if b < 309 then
                      (78, 2304887808838690864444838402726804131665417940959424449673585693672345360911983488740049182722)
                    else
                      (14, 57101889636738640)
                else
                  if b < 311 then
                    (24, 6319648940289408257228191062)
                  else
                    if b < 312 then
                      (29, 66716884763158215794645711271125524)
                    else
                      (13, 3339963165105033)
            else
              if b < 318 then
                if b < 315 then
                  if b < 314 then
                    (42, 316916241363994070514193302095535286350179844771256)
                  else
                    (21, 1542883008567321584231984)
                else
                  if b < 316 then
                    (13, 1244087481341510)
                  else
                    if b < 317 then
                      (66, 25646796753884787045029704930192103212648245783205895904711849171088159130649819)
                    else
                      (35, 198288727545156490203411159017579006469219)
              else
                if b < 321 then
                  if b < 319 then
                    (0, 0)
                  else
                    if b < 320 then
                      (77, 350092366462127892609767271574750450170486818293235841985530905173196423923454053243154728155)
                    else
                      (71, 19157704545920293277146126254479420784467453968482119279121325269243247626291490344369)
                else
                  if b < 322 then
                    (30, 901063144093069746281492693397818809)
                  else
                    if b < 323 then
                      (16, 10194897734408430985)
                    else
                      (42, 193531881072288873608056020569449417337923411792228)
          else
            if b < 335 then
              if b < 329 then
                if b < 326 then
                  if b < 325 then
                    (24, 57206087859682360430444957113)
                  else
                    (50, 443905244949551779844753348977755487461035975150062877947206)
                else
                  if b < 327 then
                    (13, 388627624210569)
                  else
                    if b < 328 then
                      (58, 1085845360864077131100320476883307745566718787951508402110944705775106)
                    else
                      (14, 52802729589886385)
              else
                if b < 332 then
                  if b < 330 then
                    (49, 14288208333857548167690146615859614819854248198855759955461)
                  else
                    if b < 331 then
                      (16, 14782590980328876101)
                    else
                      (47, 61723162665661967088244664232849333370280805806574556180)
                else
                  if b < 333 then
                    (12, 173566302411109)
                  else
                    if b < 334 then
                      (41, 19898637536249352139884296750582384124087211711257)
                    else
                      (51, 13743611361680538593591933525652121092205318097178199481929137)
            else
              if b < 340 then
                if b < 337 then
                  if b < 336 then
                    (36, 10496037892668628977389446613193700520512953)
                  else
                    (40, 1145979343055304374876187226382888290918188057819)
                else
                  if b < 338 then
                    (14, 33733760111365560)
                  else
                    if b < 339 then
                      (58, 3229281245688842793716919756116539971365389085221027752432868987820937)
                    else
                      (68, 5087194038192000506876080051242311172730408945817216296578129934014525423141313305)
              else
                if b < 343 then
                  if b < 341 then
                    (52, 58524501335480517294858840538560982302129806201061250326487556)
                  else
                    if b < 342 then
                      (43, 1653675902446924819963996667331898568765511546123780)
                    else
                      (70, 1546871644579264790842191817332419596451920158950376649498654081669579409601805474697)
                else
                  if b < 344 then
                    (67, 409193511846489716556210645003363996830110746688557588451345882166378597550411185)
                  else
                    if b < 345 then
                      (29, 61267753267418991971515818288403045)
                    else
                      (67, 245330805204585299390236012302058937397219772920937058950551928897667199624696419)
  else
    if b < 519 then
      if b < 432 then
        if b < 389 then
          if b < 367 then
            if b < 356 then
              if b < 351 then
                if b < 348 then
                  if b < 347 then
                    (16, 15820260920315416601)
                  else
                    (26, 16200570539389729503535026778249)
                else
                  if b < 349 then
                    (25, 1068058523734345249443562183561)
                  else
                    if b < 350 then
                      (19, 10749253247725583009360)
                    else
                      (50, 208878362130844651846599618735297349104272401445243072111616)
              else
                if b < 353 then
                  if b < 352 then
                    (13, 700223105340496)
                  else
                    (39, 7286059006647399113584794752252594021808366930)
                else
                  if b < 354 then
                    (16, 15902399981252238081)
                  else
                    if b < 355 then
                      (51, 19037537488305280988972318013852777634218298718293951062006665)
                    else
                      (16, 8988537249352440601)
            else
              if b < 361 then
                if b < 358 then
                  if b < 357 then
                    (27, 260612825185583077125133457601888)
                  else
                    (15, 182340355548915010)
                else
                  if b < 359 then
                    (0, 0)
                  else
                    if b < 360 then
                      (81, 17677947566429985520458052280454478774527983171738834818692770800074721496306725538864053377983588)
                    else
                      (50, 208878362130844651846599618735297194414599513866462489327282)
              else
                if b < 364 then
                  if b < 362 then
                    (40, 755983910438628412531468830349415325448432670053)
                  else
                    if b < 363 then
                      (20, 211794379284241357034580)
                    else
                      (48, 815931102073611921275779760684754705488354666680962539877)
                else
                  if b < 365 then
                    (22, 146117061938957382884580121)
                  else
                    if b < 366 then
                      (15, 778484793436116568)
                    else
                      (11, 6958188875185)
          else
            if b < 378 then
              if b < 372 then
                if b < 369 then
                  if b < 368 then
                    (7, 129793137)
                  else
                    (27, 89645951169597131842554504656224)
                else
                  if b < 370 then
                    (51, 20661689893229130043188549690902367850969971787621351446039993)
                  else
                    if b < 371 then
                      (24, 63151554342926975691129150233)
                    else
                      (33, 1504009730102249806885210000782103294293)
              else
                if b < 375 then
                  if b < 373 then
                    (15, 998634577575355984)
                  else
                    if b < 374 then
                      (16, 1677033250245460294)
                    else
                      (27, 49785090538716828756425853781584)
                else
                  if b < 376 then
                    (7, 209409033)
                  else
                    if b < 377 then
                      (9, 50126214265)
                    else
                      (6, 13088055)
            else
              if b < 383 then
                if b < 380 then
                  if b < 379 then
                    (13, 2196370309386324)
                  else
                    (18, 2598209225155185214786)
                else
                  if b < 381 then
                    (15, 179257113467749936)
                  else
                    if b < 382 then
                      (19, 20872324511780653060176)
                    else
                      (0, 0)
              else
                if b < 386 then
                  if b < 384 then
                    (68, 4027305729298701350370653451754360795379235550981121069184454326205609739466853817)
                  else
                    if b < 385 then
                      (56, 19916282203749620853719000662832907003326744922810987100157100707249)
                    else
                      (24, 68238860563613446287472778009)
                else
                  if b < 387 then
                    (43, 2895036010842901531485445600277453592456294169893657)
                  else
                    if b < 388 then
                      (26, 3130866783212550040396977169936)
                    else
                      (55, 465468386128221207102492087657657413826961219789443485175189480966)
        else
          if b < 410 then
            if b < 399 then
              if b < 394 then
                if b < 391 then
                  if b < 390 then
                    (25, 928064356880188305234836380553)
                  else
                    (25, 1018663623616761909122360376752)
                else
                  if b < 392 then
                    (18, 2616595275210132099097)
                  else
                    if b < 393 then
                      (52, 64721427015309162801523237042624219987792814577166261422392144)
                    else
                      (0, 0)
              else
                if b < 396 then
                  if b < 395 then
                    (42, 316488497652211643240774990566635678828213942898105)
                  else
                    (14, 39644319947003473)
                else
                  if b < 397 then
                    (14, 35141926908208678)
                  else
                    if b < 398 then
                      (17, 46640971929833845061)
                    else
                      (14, 4729164067526146)
            else
              if b < 404 then
                if b < 401 then
                  if b < 400 then
                    (17, 231435855172598607897)
                  else
                    (78, 4613614848541472651138425039567037082183964957675889773813550533659399131526180409651453363419)
                else
                  if b < 402 then
                    (6, 5484681)
                  else
                    if b < 403 then
                      (20, 159630509955699064587605)
                    else
                      (42, 193531881072288873608056020569449455177019418870789)
              else
                if b < 407 then
                  if b < 405 then
                    (16, 10123381958176660232)
                  else
                    if b < 406 then
                      (13, 700223099462741)
                    else
                      (25, 1007835279567332689795281640217)
                else
                  if b < 408 then
                    (35, 181173099464357758515548007585908315787365)
                  else
                    if b < 409 then
                      (26, 14957028186995944536432491944729)
                    else
                      (31, 2764482104583443490105061192906401205)
          else
            if b < 421 then
              if b < 415 then
                if b < 412 then
                  if b < 411 then
                    (14, 34213303411244464)
                  else
                    (13, 1244087617045588)
                else
                  if b < 413 then
                    (24, 48830765773631756219974026459)
                  else
                    if b < 414 then
                      (15, 182340355439883350)
                    else
                      (80, 1016806462604245747879371266659626049779933210572848858541549607685551879435557208869093840539064)
              else
                if b < 418 then
                  if b < 416 then
                    (51, 3657781333467532330928677533660080692505441962715648549197350)
                  else
                    if b < 417 then
                      (15, 616381209746231321)
                    else
                      (16, 8385787956809250054)
                else
                  if b < 419 then
                    (27, 167862148721598329440202454864981)
                  else
                    if b < 420 then
                      (19, 37129491522779687495256)
                    else
                      (25, 608085214444692512234945370881)
            else
              if b < 426 then
                if b < 423 then
                  if b < 422 then
                    (14, 5747687123452240)
                  else
                    (42, 48633283500290627555595622103497666439962027210336)
                else
                  if b < 424 then
                    (12, 132858444271025)
                  else
                    if b < 425 then
                      (15, 634328424110152636)
                    else
                      (26, 2636415581377682925388271206502)
              else
                if b < 429 then
                  if b < 427 then
                    (26, 5602872458018628282426682861078)
                  else
                    if b < 428 then
                      (57, 67865335054004820693770029805206734097919822276140811884112178251332)
                    else
                      (5, 637380)
                else
                  if b < 430 then
                    (27, 274881437367862311523843521774811)
                  else
                    if b < 431 then
                      (16, 15960119587798626561)
                    else
                      (17, 38364896051901826118)
      else
        if b < 475 then
          if b < 453 then
            if b < 442 then
              if b < 437 then
                if b < 434 then
                  if b < 433 then
                    (77, 74188619245979690949827912039751679792965027429182711776893938493898727216929154987691757634)
                  else
                    (42, 29843697691227746769243319305226014568455828951395)
                else
                  if b < 435 then
                    (56, 4241583440875301293360626862825424961279542018300812357525597938433)
                  else
                    if b < 436 then
                      (42, 53227723888522193460502276628686247450953632171062)
                    else
                      (23, 2561373127356201563463209828)
              else
                if b < 439 then
                  if b < 438 then
                    (55, 1405435796251794908621308784762838065048045156149547052790458633657)
                  else
                    (75, 1053687785055040450123432414558796809585570286019971061867044615749998181871912431853659750)
                else
                  if b < 440 then
                    (27, 179356849751724456829661853978649)
                  else
                    if b < 441 then
                      (24, 21886220784220804677658625365)
                    else
                      (78, 4427592087856446242965852129806664810270826007211874945011589077848045739628483000834224836024)
            else
              if b < 447 then
                if b < 444 then
                  if b < 443 then
                    (45, 1202302611650165313162544443831485852594883144779320761)
                  else
                    (24, 66641797286158294048638819097)
                else
                  if b < 445 then
                    (16, 11014552861386726152)
                  else
                    if b < 446 then
                      (16, 14608987461538697241)
                    else
                      (42, 29843697691227746769243319305225756975554548360784)
              else
                if b < 450 then
                  if b < 448 then
                    (52, 58524501335480517294858840538560636939328727902622913283768912)
                  else
                    if b < 449 then
                      (25, 691850707046919453853762444153)
                    else
                      (15, 177836755881702484)
                else
                  if b < 451 then
                    (27, 51056203502508512234320331555169)
                  else
                    if b < 452 then
                      (30, 1056487249181869369091884797169313369)
                    else
                      (56, 13239674715265327006636361571764040426721232344478264227972635446713)
          else
            if b < 464 then
              if b < 458 then
                if b < 455 then
                  if b < 454 then
                    (54, 90447567763755354140024913924887378262458291618823313933832870793)
                  else
                    (41, 3678987185100434248938838495781981364762539614308)
                else
                  if b < 456 then
                    (27, 257139271128975548232870150557112)
                  else
                    if b < 457 then
                      (15, 150815158146065920)
                    else
                      (40, 1249305437736224704257228861629158732697797264603)
              else
                if b < 461 then
                  if b < 459 then
                    (13, 359230443965126)
                  else
                    if b < 460 then
                      (38, 2805738460750629372061685457830272868047783131)
                    else
                      (55, 1039077963066325947859427490026633446782269327871926588780654382520)
                else
                  if b < 462 then
                    (16, 15698947631804207129)
                  else
                    if b < 463 then
                      (30, 731330882655616153251410394012341268)
                    else
                      (14, 11203569593832769)
            else
              if b < 469 then
                if b < 466 then
                  if b < 465 then
                    (13, 708547159155990)
                  else
                    (48, 3061590010820637319962645736485413510835070166779834981145)
                else
                  if b < 467 then
                    (14, 51964110421089032)
                  else
                    if b < 468 then
                      (26, 9972133941850736181023470366857)
                    else
                      (14, 6550911141103158)
              else
                if b < 472 then
                  if b < 470 then
                    (15, 998617913113762149)
                  else
                    if b < 471 then
                      (45, 423341031026412753910783146836963545708350666054085638)
                    else
                      (41, 14418342077083474446426980102558577256540257180441)
                else
                  if b < 473 then
                    (10, 582164505920)
                  else
                    if b < 474 then
                      (18, 3784343396517307245157)
                    else
                      (30, 172780131680902080519003787639529809)
        else
          if b < 497 then
            if b < 486 then
              if b < 480 then
                if b < 477 then
                  if b < 476 then
                    (37, 50761913193247025928976322773635056904398112)
                  else
                    (24, 68003386866456259722899490011)
                else
                  if b < 478 then
                    (40, 403729468370831254874022623860342890872549749094)
                  else
                    if b < 479 then
                      (48, 893013020866096760480634163491220969714155943001504088673)
                    else
                      (76, 746404203926316043801866049653164351452734797072297918830766467823093321161575838076915129)
              else
                if b < 483 then
                  if b < 481 then
                    (67, 349213322699772073143397968099903708108901907590725176318520173433076479124590009)
                  else
                    if b < 482 then
                      (26, 10763530638037400988704693046712)
                    else
                      (21, 2554088159291185032487010)
                else
                  if b < 484 then
                    (16, 2868113842602665060)
                  else
                    if b < 485 then
                      (40, 207920796439539818205087018080807772720324826212)
                    else
                      (42, 48633283500290627555595622103497682539518072607312)
            else
              if b < 491 then
                if b < 488 then
                  if b < 487 then
                    (42, 275823400993361765105480569827437210659007259532057)
                  else
                    (51, 17385948653967622184355749459254883996270844782553514601929609)
                else
                  if b < 489 then
                    (42, 324073998668633289646750895579067624995463603703225)
                  else
                    if b < 490 then
                      (52, 32813492627336672886187447061102689656128118045656767028094228)
                    else
                      (15, 318486393801434176)
              else
                if b < 494 then
                  if b < 492 then
                    (66, 4663670313424529579297380943332930775512529247272908435788236160509732651557985)
                  else
                    if b < 493 then
                      (42, 48633283500290627555595622103497666439962010461461)
                    else
                      (24, 36016684999099353149261504528)
                else
                  if b < 495 then
                    (29, 71324147119176248212711229262472793)
                  else
                    if b < 496 then
                      (17, 155959740518532931664)
                    else
                      (25, 1098314758860851466830651841296)
          else
            if b < 508 then
              if b < 502 then
                if b < 499 then
                  if b < 498 then
                    (9, 49857778696)
                  else
                    (34, 42786176550688160736839900835868378680761)
                else
                  if b < 500 then
                    (63, 577261067067179522570752062476962379824218145753618899411681188230528521814)
                  else
                    if b < 501 then
                      (39, 79147183875162797998423916360750502450378890121)
                    else
                      (43, 778132536004650040889529953655962920632321070990357)
              else
                if b < 505 then
                  if b < 503 then
                    (52, 296836976439035224367087405211526426801531376166600482228293048)
                  else
                    if b < 504 then
                      (25, 934481358742571787203247473883)
                    else
                      (26, 13694631656970326586403428227848)
                else
                  if b < 506 then
                    (62, 334911034733699990647578828678005096213901613586448931004683029350132876507)
                  else
                    if b < 507 then
                      (50, 1272322706130692503792095080657664811005705717064263815679416)
                    else
                      (48, 815931102073611921275779760684754665682029351040665916497)
            else
              if b < 513 then
                if b < 510 then
                  if b < 509 then
                    (67, 67474156136067623219630979328714310934597076474513152585945079858121468944277590)
                  else
                    (16, 15676137810625056184)
                else
                  if b < 511 then
                    (0, 0)
                  else
                    if b < 512 then
                      (70, 1653292035516988094540574072846734305563232988944275755983152437708244797026736295353)
                    else
                      (15, 854799066300043401)
              else
                if b < 516 then
                  if b < 514 then
                    (41, 20048923991681712194735747174774442335960851340057)
                  else
                    if b < 515 then
                      (15, 611602677605221990)
                    else
                      (40, 1140902621082849227651855839119691078953957983451)
                else
                  if b < 517 then
                    (26, 1617830100100819489894669832294)
                  else
                    if b < 518 then
                      (16, 13530921954091356185)
                    else
                      (18, 2315776755322553479305)
    else
      if b < 606 then
        if b < 562 then
          if b < 540 then
            if b < 529 then
              if b < 524 then
                if b < 521 then
                  if b < 520 then
                    (57, 119159906848824629018237974440360998220008874088727129421140944355428)
                  else
                    (38, 2757611823722344334838318714040085528545985755)
                else
                  if b < 522 then
                    (42, 58863794961606947983021415932511701836197686285584)
                  else
                    if b < 523 then
                      (55, 1346265058485837646371253151447735115921441262530208286239151676185)
                    else
                      (49, 49330575319764949147917534770873316555286106195039558323641)
              else
                if b < 526 then
                  if b < 525 then
                    (24, 11271409195225970177235177556)
                  else
                    (30, 1056963098166788767820449179408587657)
                else
                  if b < 527 then
                    (29, 42972710086992175137724842702689285)
                  else
                    if b < 528 then
                      (27, 42428035390287661486794883879974)
                    else
                      (74, 62003831233236042360147970797606192961972390068400115639667345783799979464141849053420425)
            else
              if b < 534 then
                if b < 531 then
                  if b < 530 then
                    (17, 23542526374549275924)
                  else
                    (79, 105593416553624817819173849708142087724389688615896424593207124222873305029852630732893923069361)
                else
                  if b < 532 then
                    (16, 9930652752536918792)
                  else
                    if b < 533 then
                      (24, 7202802968580369518824875617)
                    else
                      (49, 72918734954668637334905097822304386014777116056250333810097)
              else
                if b < 537 then
                  if b < 535 then
                    (52, 155652307563089455248222817687980582905742901890130324786007481)
                  else
                    if b < 536 then
                      (29, 55637015492308765972392809393573305)
                    else
                      (13, 2495732823850416)
                else
                  if b < 538 then
                    (62, 333138331120259139362166122135588075860469425418228166863586322600029081016)
                  else
                    if b < 539 then
                      (45, 723543039977680468898297042480164816151333190242422200)
                    else
                      (13, 3512306358183176)
          else
            if b < 551 then
              if b < 545 then
                if b < 542 then
                  if b < 541 then
                    (70, 1515742051815855603621548214523647119334997350830098692245648710476117353083785501577)
                  else
                    (57, 223127067515256657670975994098679564010330166430316363373195066496340)
                else
                  if b < 543 then
                    (39, 25233091773176953429626413991270424457272123492)
                  else
                    if b < 544 then
                      (19, 40371694021680782396857)
                    else
                      (6, 2647634)
              else
                if b < 548 then
                  if b < 546 then
                    (27, 173473993013227055795903519841049)
                  else
                    if b < 547 then
                      (46, 13105846110768874204447522736756642658731135460096400153)
                    else
                      (38, 3154661472501263309916739961960471981098814904)
                else
                  if b < 549 then
                    (30, 106026115324601543501307634266223958)
                  else
                    if b < 550 then
                      (40, 116576944106358385817356716036041504349301794065)
                    else
                      (12, 132376373484304)
            else
              if b < 556 then
                if b < 553 then
                  if b < 552 then
                    (17, 255766878696612617097)
                  else
                    (15, 524111747298492692)
                else
                  if b < 554 then
                    (33, 2674226008446257411658384127903633114331)
                  else
                    if b < 555 then
                      (14, 38225167331513174)
                    else
                      (34, 53591091890753068825258065702655266672056)
              else
                if b < 559 then
                  if b < 557 then
                    (18, 3784343396517313274960)
                  else
                    if b < 558 then
                      (41, 3678987185100434248938838495781977825788135032161)
                    else
                      (15, 182340355424146454)
                else
                  if b < 560 then
                    (15, 850575441484860856)
                  else
                    if b < 561 then
                      (50, 1354183252343833654162402633428682261984500605513498504482225)
                    else
                      (22, 267988907160383226593305993)
        else
          if b < 584 then
            if b < 573 then
              if b < 567 then
                if b < 564 then
                  if b < 563 then
                    (8, 2271381094)
                  else
                    (47, 338302634098161076551115266306518417122134034751489592761)
                else
                  if b < 565 then
                    (42, 275753460383896638219939723060842664112918617935289)
                  else
                    if b < 566 then
                      (30, 232870384236272699907621593806885142)
                    else
                      (41, 1865231105701734173077707456576609810972181707616)
              else
                if b < 570 then
                  if b < 568 then
                    (54, 14982272341883012427483863177871528312623522780485910797275718726)
                  else
                    if b < 569 then
                      (26, 17354948335660966127386264732891)
                    else
                      (53, 3081384463600132560252902827335038105314447471364513125476879801)
                else
                  if b < 571 then
                    (13, 418748123408226)
                  else
                    if b < 572 then
                      (65, 1240972068858023279545650941691291338914556449095744236587010262144085236516059)
                    else
                      (25, 931197915898386888162604331145)
            else
              if b < 578 then
                if b < 575 then
                  if b < 574 then
                    (16, 12381599641603084425)
                  else
                    (15, 73289380810597477)
                else
                  if b < 576 then
                    (42, 58863794961606947983021415932511647577555738165345)
                  else
                    if b < 577 then
                      (42, 48633283500290627555595622103497664075018515014497)
                    else
                      (68, 3925292883273364790243776196832942998355516366734992943208830862306051633673195857)
              else
                if b < 581 then
                  if b < 579 then
                    (52, 32813492627336672886187447061102055830830388965609556289807397)
                  else
                    if b < 580 then
                      (77, 144055488052418179027802400170425258229088621309964028104599105834219650894294020255835817286)
                    else
                      (13, 2196370432070981)
                else
                  if b < 582 then
                    (78, 1312706492857347231401042890592653601712257810778071952163667331701362557473037872347197362944)
                  else
                    if b < 583 then
                      (38, 812190611091952414863621164378160910466864997)
                    else
                      (30, 646365917395722148081424040274847113)
          else
            if b < 595 then
              if b < 589 then
                if b < 586 then
                  if b < 585 then
                    (15, 201859687736743427)
                  else
                    (16, 9785642840178968128)
                else
                  if b < 587 then
                    (29, 40418820829868730617709747830279608)
                  else
                    if b < 588 then
                      (36, 13529906571357274608701251826415104843337137)
                    else
                      (58, 4121033414337246390259742929079715488543767263273606770355802651024265)
              else
                if b < 592 then
                  if b < 590 then
                    (51, 20447592703353709782274077087915323225857655851255581691479259)
                  else
                    if b < 591 then
                      (14, 34780652899815449)
                    else
                      (14, 57744497610088480)
                else
                  if b < 593 then
                    (46, 12683305357953523620777559364039496388793192722596901988)
                  else
                    if b < 594 then
                      (25, 860326118142299957198748089776)
                    else
                      (16, 12526707076963866193)
            else
              if b < 600 then
                if b < 597 then
                  if b < 596 then
                    (39, 67250466031757589604505643152265172611204777179)
                  else
                    (21, 2751808885553212106884117)
                else
                  if b < 598 then
                    (48, 5289933022089502330957256807234336864021556902009134665137)
                  else
                    if b < 599 then
                      (43, 4413066168072787634289808422367779904039165779827481)
                    else
                      (32, 252261196549888890652634878264566143769)
              else
                if b < 603 then
                  if b < 601 then
                    (26, 3191012719183483175750664021504)
                  else
                    if b < 602 then
                      (77, 144055488052418179027802400170425258229088621309964028104599105834219651046352731286173726017)
                    else
                      (10, 552512865878)
                else
                  if b < 604 then
                    (67, 67474156136067623219630979328714310934597076474513152585945079861512632132788229)
                  else
                    if b < 605 then
                      (13, 3040960205133400)
                    else
                      (23, 2481170562551653930470106690)
      else
        if b < 649 then
          if b < 627 then
            if b < 616 then
              if b < 611 then
                if b < 608 then
                  if b < 607 then
                    (10, 87702066773)
                  else
                    (30, 901139639179994140852075860141821369)
                else
                  if b < 609 then
                    (15, 832543409060597897)
                  else
                    if b < 610 then
                      (59, 53294534491636446523664423637862537924141479683162909770968513089166105)
                    else
                      (27, 159068735178154038207462839409417)
              else
                if b < 613 then
                  if b < 612 then
                    (13, 3866002098853464)
                  else
                    (28, 2685794388595711862858836213057042)
                else
                  if b < 614 then
                    (16, 9785642842035983461)
                  else
                    if b < 615 then
                      (23, 1367888880942927978036466790)
                    else
                      (13, 414299362469120)
            else
              if b < 621 then
                if b < 618 then
                  if b < 617 then
                    (36, 2898769591429724136248752043596091503289956)
                  else
                    (79, 115499588648344068526850250509888180894610266430578617159938725258445782542656382285034282831288)
                else
                  if b < 619 then
                    (78, 4033019313351576389421773580918897104207161784969452443487614279603674477379925508207776124345)
                  else
                    if b < 620 then
                      (48, 987570602650591473411914627725589294247328132725220968016)
                    else
                      (29, 6626632077248381738011368395965493)
              else
                if b < 624 then
                  if b < 622 then
                    (25, 1009166231633363379401240478939)
                  else
                    if b < 623 then
                      (25, 1013404871859301998156009954056)
                    else
                      (40, 1265160431013008557728106518771518566453687111096)
                else
                  if b < 625 then
                    (19, 39083452162535637521764)
                  else
                    if b < 626 then
                      (30, 189102865061158784552934422938207826)
                    else
                      (14, 11484563609097731)
          else
            if b < 638 then
              if b < 632 then
                if b < 629 then
                  if b < 628 then
                    (78, 1187017907935675055197246592636026876687440438866923388430303015902379635469861618650471355684)
                  else
                    (23, 3646938676510318625783774647)
                else
                  if b < 630 then
                    (22, 49327891235959365419688978)
                  else
                    if b < 631 then
                      (15, 544315170907592280)
                    else
                      (16, 2397806002875813985)
              else
                if b < 635 then
                  if b < 633 then
                    (17, 38570521397579489382)
                  else
                    if b < 634 then
                      (28, 2877288592934160750889239415489755)
                    else
                      (43, 3175590245903328455019434864042168759953581215636361)
                else
                  if b < 636 then
                    (25, 1009182022930383386721674124057)
                  else
                    if b < 637 then
                      (69, 17273383970833311544225530708150863599256851577475367062001940443641256954149819971)
                    else
                      (41, 3678987185100434248938838495781981364760217935954)
            else
              if b < 643 then
                if b < 640 then
                  if b < 639 then
                    (35, 720962439001682674914807157849704566772790)
                  else
                    (15, 149862875306616401)
                else
                  if b < 641 then
                    (43, 2934498066130340666580707581245251710415920276232985)
                  else
                    if b < 642 then
                      (38, 1577068235823559589351650874454464417471218006)
                    else
                      (42, 205680505621479198317243900767341559748368814591416)
              else
                if b < 646 then
                  if b < 644 then
                    (27, 89645952378522951457183682093077)
                  else
                    if b < 645 then
                      (16, 8635559753861714184)
                    else
                      (68, 3925292883273364790243776196832942998355516366734992943208830862362675221205767457)
                else
                  if b < 647 then
                    (50, 252818074278551417193450144697750859327315084282804298933797)
                  else
                    if b < 648 then
                      (20, 211665220107255698243942)
                    else
                      (22, 40484135719139080664147537)
        else
          if b < 671 then
            if b < 660 then
              if b < 654 then
                if b < 651 then
                  if b < 650 then
                    (50, 252818074278551417193450144697750938631745407103679175438436)
                  else
                    (13, 788514478232898)
                else
                  if b < 652 then
                    (53, 855565771287939693963672038339777308322196215817872688304625248)
                  else
                    if b < 653 then
                      (24, 58083845935726576577045464283)
                    else
                      (68, 6546511922166100696172752700923989004370037426461481942162339509535344295984254385)
              else
                if b < 657 then
                  if b < 655 then
                    (29, 14554398920038985495924280570177076)
                  else
                    if b < 656 then
                      (25, 929961189543095483201946518747)
                    else
                      (17, 181862527304393445401)
                else
                  if b < 658 then
                    (37, 98566764738972474334478179653404026092257637)
                  else
                    if b < 659 then
                      (9, 37460952136)
                    else
                      (29, 45708180071247950262246105948771651)
            else
              if b < 665 then
                if b < 662 then
                  if b < 661 then
                    (19, 60678653210887402685765)
                  else
                    (26, 9730746514522463559029322960312)
                else
                  if b < 663 then
                    (17, 138111199379239459585)
                  else
                    if b < 664 then
                      (25, 1097063294246262836279867309488)
                    else
                      (40, 116576944106358385817356716036041504349338604819)
              else
                if b < 668 then
                  if b < 666 then
                    (15, 637184870465949105)
                  else
                    if b < 667 then
                      (14, 12616230230840933)
                    else
                      (17, 38570521399555085409)
                else
                  if b < 669 then
                    (62, 36078816691698720160672003904810148739013634109601181213230074264503603253)
                  else
                    if b < 670 then
                      (25, 672762745885066413200663512283)
                    else
                      (67, 61650011020213059381318144772353846728634229673814791800192529159180679483430502)
          else
            if b < 682 then
              if b < 676 then
                if b < 673 then
                  if b < 672 then
                    (14, 42745221910177360)
                  else
                    (17, 214285094717689586945)
                else
                  if b < 674 then
                    (47, 192775989875455595180478695204569057566714237466907564937)
                  else
                    if b < 675 then
                      (26, 13292939453974335348993668995856)
                    else
                      (56, 19363188521427506857755224725105438118624321598353272825142531382153)
              else
                if b < 679 then
                  if b < 677 then
                    (23, 1367888779562195066043122512)
                  else
                    if b < 678 then
                      (43, 851643582216355095368036426058980564640797220553826)
                    else
                      (14, 39561815663183067)
                else
                  if b < 680 then
                    (52, 198412068643921052184669082761205407806377608276863388976434616)
                  else
                    if b < 681 then
                      (28, 2856761260373500598638321851612432)
                    else
                      (21, 1542883016306719323325701)
            else
              if b < 687 then
                if b < 684 then
                  if b < 683 then
                    (19, 60678653210887401529860)
                  else
                    (57, 34407440845202179108306888489542149294866744796745796463235467444581)
                else
                  if b < 685 then
                    (22, 44028941683588618418275158)
                  else
                    if b < 686 then
                      (14, 53388833443564985)
                    else
                      (42, 297483217833350664849561085082151951476553175551416)
              else
                if b < 690 then
                  if b < 688 then
                    (25, 199438294937100691686538236438)
                  else
                    if b < 689 then
                      (11, 8579572287555)
                    else
                      (17, 26832531998525174884)
                else
                  if b < 691 then
                    (67, 349676611796587420388811326949983169494681109626262671001571730444168691569413553)
                  else
                    if b < 692 then
                      (14, 53401758701790800)
                    else
                      (25, 199438294955547435760247399504)

def forward4Blocks (b : Nat) : Nat :=
  if b < 1 then
    29812947722582684780491251166858558432869035177118187738335795926791191924629269465150908916864952405480392753605841305076162088262242728325493224751965221276226393412881083106791310093122799674122760867667865179375656898138637089397051125545677338305553854852300116383574921844164206647816826934227440095814979461372521779978350428691216095031541228157654197497158291244418942484052781414363983478686573742085951656271444273872178478093296742491942788689870741357960953918283424104371382420848363407986413953836608785357174219488667921568030334988405994450437544186031277260229977243959285900802494907194884831236336513294010868599241452600318412230414149667945325014189478886222698881270653746534804499270757203848779892443591124412355547595984731458277124764406390786
  else
    if b < 2 then
      22457458102676936383131448919714938498418370066976637729811506479058661488431837368527135505490598076361968366705801805262285985285864870763933519187286877091722743075513906276644107847120687002229591678208874418209150834639847406055029960020205160513071583734720988174143449682191712731883866713513071109200352036217112940501547724062486367408814199993186111034455742273350936407447841876823862521685816455438288721390479098952838920156378193772182097658417662395024988289036565161293870704158909577320879349265427175953864100038036263360126039079147884984239314036133628269936118843638967710182714130410184244319557006147656552746279420086536208323912167748560459037989077474555335481694081360937901311077111300437384856340212185815061477395459470198567850968366632564
    else
      33808888999413103254351394687273662234647031446296149244297224214047465306149604847062229478009977522724432966331748049604027935162808898187758950365001363953509204638402626112081340898731611188476018401437089899648441629969009597778646807953517027444272257903166123320527131562573666100177780066465977691213185744410937620885210220418686653469259554972647283057452848905463237189163734853336822387977708343143021189248939055628934740351783365829898631874624907903697189737051640845439285690850422570018379500952859698411434325039461032654860960

def backward4Blocks (b : Nat) : Nat :=
  if b < 1 then
    128716202362164999256929746374710247055520297078552363355144774530437166161762205238187184084787511577667845474242518894938127132553533136104409724524586735211668562641930491629195998225609040340303854785349940367908092271171709875312725021004133310466536966741742973770537481393803106003966558582293210954784942730569073566468173695211146557882457668922875427574123885189117655956357167481180625697983687795520139180644223772747847165725355835005882777922161321073395135109664466098114253437841846605536045610584870305286616574964738432988220717410703392069245306929439344361420160981984539188820909487345327517976244969378091709787271488043637253759234677653719911724630556790921601201742638907188084009416175276235758877328432211154523797287286036923499188046671135045
  else
    if b < 2 then
      119110138783185074291382862851344962687860496326162552242274502482199198579013148386597214331476190721776732538158896118406895281331763005071377724023181844978269438700096791547733151473849477711559770451254338510383295010326205100775517625308228530361293710051346719625778215685886878027742319528074025853969821355361630997327351045886722757327912030840040200510092077164716804651061770191634782472376826550220796979588399247183973628300084358827374071572206305803139070313922001837467003556828686145774714961109116203248984704484352762148003235290890799587472358122292350927060711243382935529320469680188819700647351772608609139877047127922501030659767096546501257817873370827798353028731951479921085880810977845227791666312647315757863475233609024716474113176644013378
    else
      45837649644857013458896363500342086468899667415339530585807876766502677526233224103603724855455323507993092619233083171719536828010254980606686976130437420349973490974839171119984118634947384861719466830134909210107064908043599753144121272908473677570543231641565181168879558786683503600992422988210732709879855995268067368912565887852305700037913963362698431799992613904599217343077182530435422160144144889432123393658135178579828336290466086470337223156911423742900935508537376364657197936630947542773065502769623341899994271553337577578245583

def factorCode4 (b : Nat) : Nat × Nat :=
  if b < 346 then
    if b < 173 then
      if b < 86 then
        if b < 43 then
          if b < 21 then
            if b < 10 then
              if b < 5 then
                if b < 2 then
                  if b < 1 then
                    (6, 12307249)
                  else
                    (0, 0)
                else
                  if b < 3 then
                    (7, 129807105)
                  else
                    (0, 0)
              else
                (0, 0)
            else
              if b < 15 then
                if b < 12 then
                  if b < 11 then
                    (29, 9362102156232216178499675321187424)
                  else
                    (0, 0)
                else
                  if b < 13 then
                    (0, 0)
                  else
                    if b < 14 then
                      (0, 0)
                    else
                      (20, 891424237868856525350169)
              else
                if b < 18 then
                  if b < 16 then
                    (0, 0)
                  else
                    if b < 17 then
                      (15, 560337355430241880)
                    else
                      (0, 0)
                else
                  if b < 19 then
                    (0, 0)
                  else
                    if b < 20 then
                      (23, 2251042812443709571828421653)
                    else
                      (0, 0)
          else
            if b < 32 then
              if b < 26 then
                (0, 0)
              else
                if b < 29 then
                  (0, 0)
                else
                  if b < 30 then
                    (0, 0)
                  else
                    if b < 31 then
                      (0, 0)
                    else
                      (9, 10909717589)
            else
              if b < 37 then
                if b < 34 then
                  (0, 0)
                else
                  if b < 35 then
                    (16, 8956772788700466616)
                  else
                    if b < 36 then
                      (12, 240851639565751)
                    else
                      (19, 58952172278605138437712)
              else
                if b < 40 then
                  if b < 38 then
                    (5, 701836)
                  else
                    (0, 0)
                else
                  (0, 0)
        else
          if b < 64 then
            if b < 53 then
              if b < 48 then
                if b < 45 then
                  (0, 0)
                else
                  if b < 46 then
                    (5, 763209)
                  else
                    if b < 47 then
                      (0, 0)
                    else
                      (5, 636345)
              else
                if b < 50 then
                  if b < 49 then
                    (1, 5)
                  else
                    (23, 2721687768786497037481823673)
                else
                  (0, 0)
            else
              if b < 58 then
                (0, 0)
              else
                if b < 61 then
                  (0, 0)
                else
                  if b < 62 then
                    (0, 0)
                  else
                    if b < 63 then
                      (9, 36412085332)
                    else
                      (9, 10743387392)
          else
            if b < 75 then
              if b < 69 then
                if b < 66 then
                  if b < 65 then
                    (0, 0)
                  else
                    (24, 62831869021502632193049484033)
                else
                  if b < 67 then
                    (15, 107199519699525957)
                  else
                    (0, 0)
              else
                if b < 72 then
                  (0, 0)
                else
                  if b < 73 then
                    (46, 21148697154233779226536945622959080592846035782247402929)
                  else
                    if b < 74 then
                      (45, 1058390869387300474447978350221731752235030923465513865)
                    else
                      (25, 159810688927637380639161214502)
            else
              if b < 80 then
                if b < 77 then
                  if b < 76 then
                    (24, 11271409114787555747964454403)
                  else
                    (39, 24385297572574660641583668597144846632275168689)
                else
                  if b < 78 then
                    (0, 0)
                  else
                    if b < 79 then
                      (0, 0)
                    else
                      (26, 9220271366536088624874237744213)
              else
                if b < 83 then
                  if b < 81 then
                    (0, 0)
                  else
                    if b < 82 then
                      (24, 38256253568227043483602901776)
                    else
                      (0, 0)
                else
                  (0, 0)
      else
        if b < 129 then
          if b < 107 then
            if b < 96 then
              if b < 91 then
                if b < 88 then
                  if b < 87 then
                    (45, 1213381481590959825399267943889825339736143590112382385)
                  else
                    (0, 0)
                else
                  if b < 89 then
                    (0, 0)
                  else
                    if b < 90 then
                      (0, 0)
                    else
                      (80, 277646966658018506173178105213645631404670297775996695575659417951680525941086304265720761959505)
              else
                if b < 93 then
                  (0, 0)
                else
                  if b < 94 then
                    (0, 0)
                  else
                    if b < 95 then
                      (0, 0)
                    else
                      (70, 1430196867765726916102364574495370801262777953626856531249140530614565842598609869593)
            else
              if b < 101 then
                if b < 98 then
                  if b < 97 then
                    (7, 142234708)
                  else
                    (23, 3962687899784237772229303056)
                else
                  if b < 99 then
                    (0, 0)
                  else
                    if b < 100 then
                      (4, 21832)
                    else
                      (0, 0)
              else
                if b < 104 then
                  if b < 102 then
                    (0, 0)
                  else
                    if b < 103 then
                      (6, 676944)
                    else
                      (29, 11818928935783209366541864732939860)
                else
                  if b < 105 then
                    (0, 0)
                  else
                    if b < 106 then
                      (48, 500694162404429212740897324540741505416465454133578917328)
                    else
                      (0, 0)
          else
            if b < 118 then
              if b < 112 then
                if b < 109 then
                  (0, 0)
                else
                  if b < 110 then
                    (0, 0)
                  else
                    if b < 111 then
                      (14, 39364457814713608)
                    else
                      (9, 58113396761)
              else
                if b < 115 then
                  if b < 113 then
                    (0, 0)
                  else
                    if b < 114 then
                      (22, 229038565066527307279620865)
                    else
                      (21, 13944479803481853775144329)
                else
                  if b < 116 then
                    (51, 21943786395912117763799349300031466542585893453268793274944945)
                  else
                    if b < 117 then
                      (7, 33894480)
                    else
                      (0, 0)
            else
              if b < 123 then
                if b < 120 then
                  if b < 119 then
                    (44, 12450120576074400654232479258495416498835965797032020)
                  else
                    (0, 0)
                else
                  if b < 121 then
                    (27, 173487866718429817834023725554440)
                  else
                    if b < 122 then
                      (0, 0)
                    else
                      (21, 16374747254394184872912137)
              else
                if b < 126 then
                  if b < 124 then
                    (26, 16911765801596799764045280161817)
                  else
                    if b < 125 then
                      (0, 0)
                    else
                      (7, 130534281)
                else
                  if b < 127 then
                    (17, 138190909544141937409)
                  else
                    if b < 128 then
                      (24, 62164239751815473612369419016)
                    else
                      (0, 0)
        else
          if b < 151 then
            if b < 140 then
              if b < 134 then
                if b < 131 then
                  if b < 130 then
                    (27, 29502680970187759048821522718818)
                  else
                    (0, 0)
                else
                  if b < 132 then
                    (0, 0)
                  else
                    if b < 133 then
                      (9, 6313886022)
                    else
                      (17, 162216399065746056793)
              else
                if b < 137 then
                  if b < 135 then
                    (7, 38424580)
                  else
                    if b < 136 then
                      (0, 0)
                    else
                      (40, 403729468370831254874022623860324426372758963525)
                else
                  if b < 138 then
                    (18, 532173888899708552272)
                  else
                    if b < 139 then
                      (5, 314233)
                    else
                      (8, 2343654513)
            else
              if b < 145 then
                if b < 142 then
                  if b < 141 then
                    (42, 29843697691227746769243319305225756975556573815888)
                  else
                    (39, 73446526718431275685067100328803164315030258907)
                else
                  if b < 143 then
                    (22, 44028941844890552105129025)
                  else
                    if b < 144 then
                      (0, 0)
                    else
                      (77, 252212935138098735948411514438440460386022240571299350230248763381708883990901248193328074168)
              else
                if b < 148 then
                  if b < 146 then
                    (25, 593240776617703857762586348985)
                  else
                    if b < 147 then
                      (21, 15478696661013781789893913)
                    else
                      (0, 0)
                else
                  if b < 149 then
                    (18, 532173894284381742145)
                  else
                    if b < 150 then
                      (27, 25885282459993869167795594671621)
                    else
                      (15, 566549597846373595)
          else
            if b < 162 then
              if b < 156 then
                if b < 153 then
                  if b < 152 then
                    (50, 443905244949551779844753348977736188838942244061869461738816)
                  else
                    (0, 0)
                else
                  if b < 154 then
                    (19, 39083452144943451473430)
                  else
                    if b < 155 then
                      (19, 41797855989431614465289)
                    else
                      (0, 0)
              else
                if b < 159 then
                  if b < 157 then
                    (42, 58863794961606947983021415932511647577553663713558)
                  else
                    if b < 158 then
                      (53, 936392021367688276717741448616975716834076899216980005323297893)
                    else
                      (0, 0)
                else
                  if b < 160 then
                    (0, 0)
                  else
                    if b < 161 then
                      (44, 12450120576074400654232479258495402003204738775322694)
                    else
                      (44, 56789336503074948375882663927999190936103154287434633)
            else
              if b < 167 then
                if b < 164 then
                  if b < 163 then
                    (12, 241281025254992)
                  else
                    (15, 683616204050813065)
                else
                  if b < 165 then
                    (48, 893013020866096760480634163491225926240551336442783491332)
                  else
                    if b < 166 then
                      (18, 827321794079068292630)
                    else
                      (13, 3864493583369435)
              else
                if b < 170 then
                  if b < 168 then
                    (0, 0)
                  else
                    if b < 169 then
                      (51, 18459305465799008999912303329739268616579236876029380815506872)
                    else
                      (0, 0)
                else
                  if b < 171 then
                    (0, 0)
                  else
                    if b < 172 then
                      (10, 810801709313)
                    else
                      (74, 10155284088043924211311714117480866507847053986945247013358323072380829031515425021649174)
    else
      if b < 259 then
        if b < 216 then
          if b < 194 then
            if b < 183 then
              if b < 178 then
                if b < 175 then
                  if b < 174 then
                    (8, 2881765640)
                  else
                    (51, 3657781333467532330928677533660041091949081361814907374949889)
                else
                  if b < 176 then
                    (16, 15960149909650791176)
                  else
                    if b < 177 then
                      (25, 1008637397331787982057907441073)
                    else
                      (26, 2885480733385614271478889866337)
              else
                if b < 180 then
                  if b < 179 then
                    (0, 0)
                  else
                    (44, 52564040866896871576836294526344025705477711763361201)
                else
                  if b < 181 then
                    (63, 4886307116760597420891256734290540964339597634488544081937165502507221572377)
                  else
                    if b < 182 then
                      (12, 182643557682616)
                    else
                      (0, 0)
            else
              if b < 188 then
                if b < 185 then
                  if b < 184 then
                    (16, 9041764671689317128)
                  else
                    (0, 0)
                else
                  if b < 186 then
                    (7, 172315729)
                  else
                    if b < 187 then
                      (15, 638046905982930969)
                    else
                      (77, 445831314766961398350883769420709137054430392338242407161110247277021377731329849226168389048)
              else
                if b < 191 then
                  if b < 189 then
                    (0, 0)
                  else
                    if b < 190 then
                      (30, 1067357833088660248874759869669991681)
                    else
                      (13, 3609030983172707)
                else
                  if b < 192 then
                    (0, 0)
                  else
                    if b < 193 then
                      (42, 320844502212078563593583142447752085241064619039625)
                    else
                      (0, 0)
          else
            if b < 205 then
              if b < 199 then
                if b < 196 then
                  if b < 195 then
                    (6, 12258576)
                  else
                    (12, 207298707166808)
                else
                  if b < 197 then
                    (20, 1001687483299976569703864)
                  else
                    if b < 198 then
                      (42, 193531881072288873608056020569449417337923479553539)
                    else
                      (13, 2384624202679381)
              else
                if b < 202 then
                  if b < 200 then
                    (14, 62059509720127057)
                  else
                    if b < 201 then
                      (55, 134404065801571012141823783162278100842633297679397018607470142788)
                    else
                      (0, 0)
                else
                  if b < 203 then
                    (63, 1138591385113410541820649644368391302615363585759987411081112343871187215633)
                  else
                    if b < 204 then
                      (50, 228611333341720770683042345853752568246815152342844730270004)
                    else
                      (25, 1088298959752384164239602146064)
            else
              if b < 210 then
                if b < 207 then
                  if b < 206 then
                    (24, 68009693881044314845580643769)
                  else
                    (0, 0)
                else
                  if b < 208 then
                    (0, 0)
                  else
                    if b < 209 then
                      (24, 58641193783287806389375075547)
                    else
                      (28, 816899256038451783006514520151141)
              else
                if b < 213 then
                  if b < 211 then
                    (18, 3451476802753316015544)
                  else
                    if b < 212 then
                      (41, 16869304038437838047353053126828823042548440554265)
                    else
                      (55, 239716357470128198839741810845948533161528393078941268709186233669)
                else
                  if b < 214 then
                    (0, 0)
                  else
                    if b < 215 then
                      (30, 687563363480502237896723223139223142)
                    else
                      (15, 183753016055432801)
        else
          if b < 237 then
            if b < 226 then
              if b < 221 then
                if b < 218 then
                  if b < 217 then
                    (14, 42746525375286705)
                  else
                    (27, 278316401966834611636044492026121)
                else
                  if b < 219 then
                    (51, 7102483919192828477516053583643779021388592171322276836623440)
                  else
                    if b < 220 then
                      (17, 237338250542926632537)
                    else
                      (0, 0)
              else
                if b < 223 then
                  if b < 222 then
                    (15, 993899998969226504)
                  else
                    (26, 3130866783196472261955461080128)
                else
                  if b < 224 then
                    (26, 9709663984884459813786168580873)
                  else
                    if b < 225 then
                      (13, 2458150843029079)
                    else
                      (7, 130782536)
            else
              if b < 231 then
                if b < 228 then
                  if b < 227 then
                    (21, 13886796879209302909412745)
                  else
                    (10, 169723581520)
                else
                  if b < 229 then
                    (19, 55714673735775909209369)
                  else
                    if b < 230 then
                      (0, 0)
                    else
                      (30, 705129881414656068906964208483464709)
              else
                if b < 234 then
                  (0, 0)
                else
                  if b < 235 then
                    (14, 52787383545455897)
                  else
                    if b < 236 then
                      (10, 539216426777)
                    else
                      (15, 19708590157070597)
          else
            if b < 248 then
              if b < 242 then
                if b < 239 then
                  if b < 238 then
                    (51, 22197739452999974657043878870551392937282570567904335839419273)
                  else
                    (0, 0)
                else
                  if b < 240 then
                    (12, 44495015396966)
                  else
                    if b < 241 then
                      (18, 3168790357742897352113)
                    else
                      (19, 58968853611624961953209)
              else
                if b < 245 then
                  if b < 243 then
                    (5, 837464)
                  else
                    if b < 244 then
                      (18, 2303310798232037415817)
                    else
                      (7, 22303765)
                else
                  if b < 246 then
                    (0, 0)
                  else
                    if b < 247 then
                      (51, 15340005807090025922908558452119251023003764952126177210139867)
                    else
                      (25, 180342547123615522835654853908)
            else
              if b < 253 then
                if b < 250 then
                  if b < 249 then
                    (40, 1237953480890828000645296050424507761509351312824)
                  else
                    (9, 50676382584)
                else
                  if b < 251 then
                    (30, 106026113235974107808181894459514896)
                  else
                    if b < 252 then
                      (7, 213633793)
                    else
                      (38, 742085014347696343316583589225733435668389157)
              else
                if b < 256 then
                  if b < 254 then
                    (0, 0)
                  else
                    if b < 255 then
                      (17, 155959740516392961616)
                    else
                      (26, 1617830128714088513850392577348)
                else
                  if b < 257 then
                    (0, 0)
                  else
                    if b < 258 then
                      (60, 251360819250597146226581109049597050750989751795355798996780365181764453)
                    else
                      (15, 832283884314060040)
      else
        if b < 302 then
          if b < 280 then
            if b < 269 then
              if b < 264 then
                if b < 261 then
                  if b < 260 then
                    (60, 488078978452785680458702743307715780360868234974454867705273440237171042)
                  else
                    (13, 2770494765944248)
                else
                  if b < 262 then
                    (47, 337901709583934292859453458979494182289001980614785650104)
                  else
                    if b < 263 then
                      (45, 423341031026412753910783146836963545708443407993230437)
                    else
                      (14, 42710840512767241)
              else
                if b < 266 then
                  if b < 265 then
                    (19, 13229076362256604497477)
                  else
                    (25, 1067256019237844539348042665393)
                else
                  if b < 267 then
                    (69, 17273383970833311544225530708150863599256851577475367062001940443641256954071156273)
                  else
                    if b < 268 then
                      (66, 21913681645794195101441475909261743871047146634516442401476572783226687355637177)
                    else
                      (0, 0)
            else
              if b < 274 then
                if b < 271 then
                  if b < 270 then
                    (25, 859058219113548543090350902712)
                  else
                    (27, 232680689007495826056600979615769)
                else
                  if b < 272 then
                    (54, 16568685315919145677189948682911800316874921363557862534896031057)
                  else
                    if b < 273 then
                      (16, 2883535548403180549)
                    else
                      (26, 9529265720134758074468042695504)
              else
                if b < 277 then
                  if b < 275 then
                    (39, 14371043691798571284917337874148364706097382245)
                  else
                    if b < 276 then
                      (25, 701541753643735053718884178801)
                    else
                      (43, 941820719385711167728342654920186323401760785711958)
                else
                  if b < 278 then
                    (39, 49876562901156684144828118002348431980529470905)
                  else
                    if b < 279 then
                      (78, 4610940772476927064641025937702305983098206717843179617112043020822827004611808465631777410489)
                    else
                      (48, 5439579542035597697442559788031752732369420268933935848217)
          else
            if b < 291 then
              if b < 285 then
                if b < 282 then
                  if b < 281 then
                    (53, 5677342633833775387113364984185508564875065727811860029165817265)
                  else
                    (13, 3585285178579301)
                else
                  if b < 283 then
                    (14, 19905401849070944)
                  else
                    if b < 284 then
                      (7, 35004769)
                    else
                      (33, 4350382103996291638051042589294697926072)
              else
                if b < 288 then
                  if b < 286 then
                    (0, 0)
                  else
                    if b < 287 then
                      (31, 15274375650958367338844636976133757833)
                    else
                      (48, 987570602650591473411914627725589334053653448365519930980)
                else
                  if b < 289 then
                    (49, 86233122063129251339452267398204869754714061667518697047259)
                  else
                    if b < 290 then
                      (41, 18335776323800003925491957717878861669965785746872)
                    else
                      (50, 128177705575533878461669715082429905589180126033001760318549)
            else
              if b < 296 then
                if b < 293 then
                  if b < 292 then
                    (14, 6699969962927173)
                  else
                    (19, 65371359993079802992216)
                else
                  if b < 294 then
                    (44, 26458814439150797119423946677310376595709154521646614)
                  else
                    if b < 295 then
                      (67, 260270663730450818562914107069071907916913075999074819273365366855713089397327067)
                    else
                      (25, 655711518816222390728955987476)
              else
                if b < 299 then
                  if b < 297 then
                    (18, 3204102110086980492169)
                  else
                    if b < 298 then
                      (24, 12154563126726751771021043283)
                    else
                      (28, 4053019663402170185399621243653553)
                else
                  if b < 300 then
                    (14, 39649262106892645)
                  else
                    if b < 301 then
                      (40, 1169567250544002684725929310041241697402740933851)
                    else
                      (19, 41571347883957938316389)
        else
          if b < 324 then
            if b < 313 then
              if b < 307 then
                if b < 304 then
                  if b < 303 then
                    (0, 0)
                  else
                    (53, 3404648857349497339950195222452996277013069545012161529577227621)
                else
                  if b < 305 then
                    (32, 54236589987607166368866613791562073668)
                  else
                    if b < 306 then
                      (20, 819579457517739339572489)
                    else
                      (0, 0)
              else
                if b < 310 then
                  if b < 308 then
                    (24, 41940509314773150192880018529)
                  else
                    if b < 309 then
                      (13, 2436349219935825)
                    else
                      (14, 53137024074403256)
                else
                  if b < 311 then
                    (34, 42021610413690377773241904817711090107611)
                  else
                    if b < 312 then
                      (0, 0)
                    else
                      (25, 576266958343475063951766722097)
            else
              if b < 318 then
                if b < 315 then
                  if b < 314 then
                    (42, 292002646350117553789803919227777793669076275747721)
                  else
                    (17, 38570521397334926085)
                else
                  if b < 316 then
                    (14, 34841108518086224)
                  else
                    if b < 317 then
                      (0, 0)
                    else
                      (24, 6319648913857165215449236833)
              else
                if b < 321 then
                  if b < 319 then
                    (19, 60549492655427039941637)
                  else
                    if b < 320 then
                      (77, 144055488052418179027802400170425258229088621309964028104599105834219650911650646646976165142)
                    else
                      (19, 55817273399059883566680)
                else
                  if b < 322 then
                    (0, 0)
                  else
                    if b < 323 then
                      (34, 12393045213195074689691485052156869174613)
                    else
                      (14, 33721567805727060)
          else
            if b < 335 then
              if b < 329 then
                if b < 326 then
                  if b < 325 then
                    (44, 47044052137688271353794468242394973321684033634360089)
                  else
                    (14, 62167816893431945)
                else
                  if b < 327 then
                    (46, 19507826099367377998380212500541985212999760329256076507)
                  else
                    if b < 328 then
                      (51, 18729639911986346646964018466573712706419392970329406430006712)
                    else
                      (70, 1004874978117981386302406706389233407579012189884158193461460700750954643753460454726)
              else
                if b < 332 then
                  if b < 330 then
                    (16, 9042574631762284569)
                  else
                    if b < 331 then
                      (35, 739656709251097872374330475784796345748913)
                    else
                      (23, 2741077789601600346167201201)
                else
                  if b < 333 then
                    (0, 0)
                  else
                    if b < 334 then
                      (41, 10943159657000521415224665284524714513529416582363)
                    else
                      (41, 3039580218768164222224726381468604152497633117538)
            else
              if b < 340 then
                if b < 337 then
                  if b < 336 then
                    (0, 0)
                  else
                    (13, 2384041938234464)
                else
                  if b < 338 then
                    (39, 50485777228302254176182208402798892088842800569)
                  else
                    if b < 339 then
                      (37, 284896775760720754339989185727225133816743131)
                    else
                      (51, 3657781333467532330928677533660061393881191993412075370468438)
              else
                if b < 343 then
                  if b < 341 then
                    (66, 8188606446561731162762635004266102113722844325705183797742796847076168948237379)
                  else
                    if b < 342 then
                      (31, 11282078102634497102511427335751881812)
                    else
                      (27, 154454640091689079182653524531976)
                else
                  if b < 344 then
                    (51, 20474920163838430313023001699124511578976594816900991689969080)
                  else
                    if b < 345 then
                      (40, 1237954543722470561385024721523937010712183852473)
                    else
                      (28, 820516655512618983361205906982229)
  else
    if b < 519 then
      if b < 432 then
        if b < 389 then
          if b < 367 then
            if b < 356 then
              if b < 351 then
                if b < 348 then
                  if b < 347 then
                    (41, 3039580218768164222224726381468607543661000082529)
                  else
                    (23, 759660195357618163651203169)
                else
                  if b < 349 then
                    (68, 986400176323408950101090316357661547658147674781036668803080466548311229308618052)
                  else
                    if b < 350 then
                      (39, 61767878569930316713179068982177723017528214747)
                    else
                      (15, 183753018301632592)
              else
                if b < 353 then
                  if b < 352 then
                    (70, 1551734155198686410536169169281742272696049708486659850334261861839407594035325754137)
                  else
                    (74, 93741239982548701571486115376021141304062987885959378376192212709336099690198012849947867)
                else
                  if b < 354 then
                    (15, 596366153915696193)
                  else
                    if b < 355 then
                      (24, 21886218612909672008913737270)
                    else
                      (30, 985479013169318683640648588954229641)
            else
              if b < 361 then
                if b < 358 then
                  if b < 357 then
                    (14, 33914245985703512)
                  else
                    (53, 855565771287939693963672038339777308322198281853208943755859030)
                else
                  if b < 359 then
                    (25, 771482721634429711429044030904)
                  else
                    if b < 360 then
                      (35, 198288723411121195035063760834508497815076)
                    else
                      (11, 15031527594341)
              else
                if b < 364 then
                  if b < 362 then
                    (27, 25885281627309354890021231246453)
                  else
                    if b < 363 then
                      (8, 561661204)
                    else
                      (23, 1367888783210690979669197891)
                else
                  if b < 365 then
                    (16, 2397806003043566182)
                  else
                    if b < 366 then
                      (17, 46435346578081666372)
                    else
                      (16, 2413042530331788036)
          else
            if b < 378 then
              if b < 372 then
                if b < 369 then
                  if b < 368 then
                    (34, 73686776114778109778028103279679853579704)
                  else
                    (27, 49785090538716828756425753781345)
                else
                  if b < 370 then
                    (26, 14936937124329336114951609142705)
                  else
                    if b < 371 then
                      (26, 10717471762235345612180862288709)
                    else
                      (16, 2624329439891443796)
              else
                if b < 375 then
                  if b < 373 then
                    (25, 1009454102280801389981892365745)
                  else
                    if b < 374 then
                      (47, 192866104537492447198629417958967996576031084211213753225)
                    else
                      (47, 215669313907593249129904103266673675262953076276435671945)
                else
                  if b < 376 then
                    (67, 409068944201480121179083239577843695632458669254624081359642044218317213211690203)
                  else
                    if b < 377 then
                      (41, 3326732743032637091281392289292928859425272513892)
                    else
                      (68, 6513170798943958329199500396678533647313703642522077673704094364810264596846009113)
            else
              if b < 383 then
                if b < 380 then
                  if b < 379 then
                    (8, 561560645)
                  else
                    (52, 58524501335480517294858840538560657471183441703589470218372675)
                else
                  if b < 381 then
                    (28, 4477727476336913664068231995870649)
                  else
                    if b < 382 then
                      (65, 147778833169197957778112527994102369234999845312926438249390384201120594793984)
                    else
                      (33, 707707419782647435191302592535507264614)
              else
                if b < 386 then
                  if b < 384 then
                    (9, 54640745865)
                  else
                    if b < 385 then
                      (13, 2256611480854614)
                    else
                      (52, 64721427015309162801523237042624218704551759257660059827267172)
                else
                  if b < 387 then
                    (14, 9420399106023442)
                  else
                    if b < 388 then
                      (0, 0)
                    else
                      (9, 36385612881)
        else
          if b < 410 then
            if b < 399 then
              if b < 394 then
                if b < 391 then
                  if b < 390 then
                    (15, 149862875189831270)
                  else
                    (40, 898915817867425493466131728580781487996234911160)
                else
                  if b < 392 then
                    (36, 7515720742256269873489087505257128773307832)
                  else
                    if b < 393 then
                      (0, 0)
                    else
                      (6, 13395554)
              else
                if b < 396 then
                  if b < 395 then
                    (27, 29502680937131193668734002742788)
                  else
                    (0, 0)
                else
                  if b < 397 then
                    (41, 18769998105473166883568052187883336619217526250377)
                  else
                    if b < 398 then
                      (72, 257247994398203234893416116835643752340227120610344497526133939392244893335132961465414)
                    else
                      (60, 488078978452785680458702743307715780360868234974454867705273440238056964)
            else
              if b < 404 then
                if b < 401 then
                  if b < 400 then
                    (41, 18804647414652325214890070128901429270852629712305)
                  else
                    (19, 36760700756493589096017)
                else
                  if b < 402 then
                    (43, 778132536004650040889529953655962663039392023070049)
                  else
                    if b < 403 then
                      (30, 968319698814718229167217431237643705)
                    else
                      (12, 243850210070665)
              else
                if b < 407 then
                  if b < 405 then
                    (43, 4740861731698982692447772896214475015976980742200201)
                  else
                    if b < 406 then
                      (41, 6459671493933300077984361981765190821965740466212)
                    else
                      (42, 282592020392228636814012739735075337501729523817241)
                else
                  if b < 408 then
                    (52, 330595252467765121855652890160630274515599729479874841315134897)
                  else
                    if b < 409 then
                      (15, 925909135644446137)
                    else
                      (12, 220661759682128)
          else
            if b < 421 then
              if b < 415 then
                if b < 412 then
                  if b < 411 then
                    (12, 172957284227429)
                  else
                    (50, 1272605445105913164774310918896486237576346229390049277922744)
                else
                  if b < 413 then
                    (13, 2379756782782029)
                  else
                    if b < 414 then
                      (52, 212790553584343583746887201403312267313316789192186630183920963)
                    else
                      (50, 252818074278551417193450144697750938631737340578385804806852)
              else
                if b < 418 then
                  if b < 416 then
                    (52, 53472860705496230872729502396236081770137263488617043019465797)
                  else
                    if b < 417 then
                      (65, 1257753966002809184663656804395578163836729882823618154138918457575738018497755)
                    else
                      (16, 2381509634279494144)
                else
                  if b < 419 then
                    (26, 17176646819388507249129547094792)
                  else
                    if b < 420 then
                      (44, 53050662408329248410991904239912620166292090493655945)
                    else
                      (52, 53472860705496230872729502396236081770137475549814397261329924)
            else
              if b < 426 then
                if b < 423 then
                  if b < 422 then
                    (73, 5777237780391223760655866121215214180822281553471781707930978806169071118471631301041033)
                  else
                    (46, 15874514899338924439498328982712885007467607076553229531)
                else
                  if b < 424 then
                    (57, 34407440845202179108306888489542149294870155472426075347903905681748)
                  else
                    if b < 425 then
                      (20, 430857819649712314516699)
                    else
                      (41, 3039580218768164222224726381468605158720017929539)
              else
                if b < 429 then
                  if b < 427 then
                    (27, 51282290967619220215256974779654)
                  else
                    if b < 428 then
                      (26, 2636415583754943945264608969797)
                    else
                      (18, 3754827170228994067889)
                else
                  if b < 430 then
                    (14, 35141925273486870)
                  else
                    if b < 431 then
                      (52, 354379066807126167694196396302928553997689005589150219586522553)
                    else
                      (51, 20568977169271858889505146822946054971529930031255517325708728)
      else
        if b < 475 then
          if b < 453 then
            if b < 442 then
              if b < 437 then
                if b < 434 then
                  if b < 433 then
                    (39, 48833442277784691806373535531749073526112406961)
                  else
                    (40, 717142473845139839619580150166817059451445464505)
                else
                  if b < 435 then
                    (25, 756881542153726767114025139632)
                  else
                    if b < 436 then
                      (48, 2937326081027822638967181418184882583686116330829722439097)
                    else
                      (24, 12464893433505989408371007574)
              else
                if b < 439 then
                  if b < 438 then
                    (26, 3191012719312610384266630939989)
                  else
                    (26, 16127102913149908214233821600521)
                else
                  if b < 440 then
                    (13, 788514411456054)
                  else
                    if b < 441 then
                      (0, 0)
                    else
                      (16, 1715192334662391073)
            else
              if b < 447 then
                if b < 444 then
                  if b < 443 then
                    (14, 38700453455291673)
                  else
                    (24, 56784175121777124301592350129)
                else
                  if b < 445 then
                    (17, 253480975777445239577)
                  else
                    if b < 446 then
                      (42, 29843697691227746769243319305225719136459091739202)
                    else
                      (15, 179257113736200546)
              else
                if b < 450 then
                  if b < 448 then
                    (47, 61723162665661967088244664232849333370280805806572398085)
                  else
                    if b < 449 then
                      (48, 3246926171636102046919055197194096512653744284920265991782)
                    else
                      (56, 13945441719703541104435999631167472750645635401888192973548860892438)
                else
                  if b < 451 then
                    (14, 32756984276452101)
                  else
                    if b < 452 then
                      (45, 241106104162742058938455719659567708509192399875696485)
                    else
                      (14, 42992916494135553)
          else
            if b < 464 then
              if b < 458 then
                if b < 455 then
                  if b < 454 then
                    (25, 180342543730636365167772172326)
                  else
                    (20, 584605874408494520755593)
                else
                  if b < 456 then
                    (9, 57923197809)
                  else
                    if b < 457 then
                      (7, 45425733)
                    else
                      (41, 3039580218768164222224726381468604004688669991188)
              else
                if b < 461 then
                  if b < 459 then
                    (31, 10288451042490095229034739666648357769)
                  else
                    if b < 460 then
                      (58, 3570033080244106522735615905578873024165228092072734105750435324642821)
                    else
                      (6, 8404084)
                else
                  if b < 462 then
                    (19, 59270383325223089134473)
                  else
                    if b < 463 then
                      (23, 704463061447798301439320640)
                    else
                      (25, 101114383321331693221299574339)
            else
              if b < 469 then
                if b < 466 then
                  if b < 465 then
                    (53, 3620178288059669044628947525864223971040636839572977666536525233)
                  else
                    (26, 9868194580232031890069071911705)
                else
                  if b < 467 then
                    (67, 231082915611372599029074123303054120050107725441124474697602256118426703969518811)
                  else
                    if b < 468 then
                      (40, 229936699068777140558677405986373623349825119761)
                    else
                      (42, 183951364230087984534371950671497104888476947766041)
              else
                if b < 472 then
                  if b < 470 then
                    (79, 10648587167904745873800391942451617079332232481415099332279216973882528363687158749880444605536)
                  else
                    if b < 471 then
                      (31, 15689981314276512812297257455481838473)
                    else
                      (27, 252883699914188997034539946924937)
                else
                  if b < 473 then
                    (66, 4217134758504226451226936208044644433412317279657072036621567491132591814639622)
                  else
                    if b < 474 then
                      (23, 1367888663244050678522734101)
                    else
                      (14, 34777262746633435)
        else
          if b < 497 then
            if b < 486 then
              if b < 480 then
                if b < 477 then
                  if b < 476 then
                    (41, 3039580218768164222224726381468604152497633059906)
                  else
                    (52, 212790553584343583746887201403312901138614837271551123188498517)
                else
                  if b < 478 then
                    (42, 53227723888522193460502276628686247450953893959008)
                  else
                    if b < 479 then
                      (60, 251360819250597146226581109049597050751005900370727550416608339832389729)
                    else
                      (0, 0)
              else
                if b < 483 then
                  if b < 481 then
                    (10, 802298845065)
                  else
                    if b < 482 then
                      (14, 36105783693366598)
                    else
                      (19, 65107586293861746288209)
                else
                  if b < 484 then
                    (70, 276374143533332984707608491330413817588109625239605872992031047102987023661436044900)
                  else
                    if b < 485 then
                      (67, 312851807157489291395444179922460932247000089615341082678547342881141489640951224)
                    else
                      (8, 210128901)
            else
              if b < 491 then
                if b < 488 then
                  if b < 487 then
                    (40, 805586592284618742358092883958769195589449341833)
                  else
                    (42, 53227723888522193460502276628686247450954006955524)
                else
                  if b < 489 then
                    (24, 58110329158274957846134148529)
                  else
                    if b < 490 then
                      (41, 13872063920794563650855654988998506009416123305400)
                    else
                      (50, 228611333341720770683042345853752568246817809219187435198020)
              else
                if b < 494 then
                  if b < 492 then
                    (20, 594276649268857797449304)
                  else
                    if b < 493 then
                      (15, 994372825603132857)
                    else
                      (51, 2050843289208542055386715441318898791358841425676692858753300)
                else
                  if b < 495 then
                    (46, 3857697666603872943015291514553086891537115678421500262)
                  else
                    if b < 496 then
                      (19, 55404635892170434301369)
                    else
                      (10, 607617799961)
          else
            if b < 508 then
              if b < 502 then
                if b < 499 then
                  if b < 498 then
                    (15, 826647305766034185)
                  else
                    (67, 67474156136067623219630979328714310934597076474513152585945079860224690997121380)
                else
                  if b < 500 then
                    (41, 3678987185100434248938838495781980225878048114180)
                  else
                    if b < 501 then
                      (46, 6773456496422604062572530349391416731331992536342618128)
                    else
                      (22, 260588810375911080294931337)
              else
                if b < 505 then
                  if b < 503 then
                    (21, 16587542697075413004340664)
                  else
                    if b < 504 then
                      (39, 78758349883343086341486632455009610780280638897)
                    else
                      (35, 198288727545156490203411159017579076800837)
                else
                  if b < 506 then
                    (7, 33960288)
                  else
                    if b < 507 then
                      (26, 3111568160864964342048048432737)
                    else
                      (29, 66158515474203070004815445998194104)
            else
              if b < 513 then
                if b < 510 then
                  if b < 509 then
                    (19, 10749253366450306298198)
                  else
                    (40, 116576944106358385817356716036038113185900073572)
                else
                  if b < 511 then
                    (42, 29843697691227746769243319305225719136460660032788)
                  else
                    if b < 512 then
                      (17, 38970321587629483008)
                    else
                      (35, 111176441613396243556803337293487937048900)
              else
                if b < 516 then
                  if b < 514 then
                    (25, 1092743806734611099790530858424)
                  else
                    if b < 515 then
                      (47, 31293385150276825796306082783796363669231818491191182694)
                    else
                      (16, 14805825428973649328)
                else
                  if b < 517 then
                    (25, 180342545501523796243878642694)
                  else
                    if b < 518 then
                      (38, 455378687915462444599049672015787126374670436)
                    else
                      (29, 13241354990865465262285441075689268)
    else
      if b < 606 then
        if b < 562 then
          if b < 540 then
            if b < 529 then
              if b < 524 then
                if b < 521 then
                  if b < 520 then
                    (16, 5095782300835472224)
                  else
                    (53, 3404648857349497339950195222452995948503363444892336408888677894)
                else
                  if b < 522 then
                    (18, 724468417187397584468)
                  else
                    if b < 523 then
                      (25, 601582482535708162035825302297)
                    else
                      (18, 2209305091688868161112)
              else
                if b < 526 then
                  if b < 525 then
                    (17, 234924589632863995099)
                  else
                    (21, 10643277045691337277597065)
                else
                  if b < 527 then
                    (21, 15553035454363762448491801)
                  else
                    if b < 528 then
                      (66, 23562668016832202183837882431525076164481557912617637221110965640287777210781113)
                    else
                      (71, 17220448922718820730129294268054981463119547344898896993187904021643487609146813992376)
            else
              if b < 534 then
                if b < 531 then
                  if b < 530 then
                    (42, 320786675682642552499123187126359910059530793274808)
                  else
                    (54, 90034716135736855849932334576142992665511276328677292956543485147)
                else
                  if b < 532 then
                    (78, 2304887808838690864444838402726804131665417940959424449673585693347514414714532693714983282241)
                  else
                    if b < 533 then
                      (23, 3980828581167228841619377592)
                    else
                      (15, 904515291383948665)
              else
                if b < 537 then
                  if b < 535 then
                    (13, 2477364252927248)
                  else
                    if b < 536 then
                      (54, 13689052340607035103418752613436436933155140075875233278309245013)
                    else
                      (73, 2198112305487337936825598147131733066239755574187683534310899442050470749390254918350400)
                else
                  if b < 538 then
                    (30, 653535666752760231059339839657008009)
                  else
                    if b < 539 then
                      (54, 72527224641993264223158785582177964300615787789762331721957658040)
                    else
                      (39, 11873360229563141493065337427611748217433118400)
          else
            if b < 551 then
              if b < 545 then
                if b < 542 then
                  if b < 541 then
                    (67, 74618725014792473268758095093326892408200467956366534972611778568075226008667654)
                  else
                    (16, 9069594099230068993)
                else
                  if b < 543 then
                    (65, 848399353529032043687656147989703973119465534950145062398076942419955466765531)
                  else
                    if b < 544 then
                      (41, 15424127917828688207834358861186702006831267466681)
                    else
                      (16, 13595695269489429945)
              else
                if b < 548 then
                  if b < 546 then
                    (30, 209126209579449473369395944627504707)
                  else
                    if b < 547 then
                      (16, 1715192309823726404)
                    else
                      (20, 362690500047608486055352)
                else
                  if b < 549 then
                    (29, 9362102061504156862532631651902288)
                  else
                    if b < 550 then
                      (38, 4878033623848398974390408893357617536819023288)
                    else
                      (18, 2596211698056824347393)
            else
              if b < 556 then
                if b < 553 then
                  if b < 552 then
                    (31, 10248251069736504182239149186409844153)
                  else
                    (51, 2050843289208542055386715441318898791358988999629282537006338)
                else
                  if b < 554 then
                    (52, 348453634485253416729805374117679944345437509462867969233443609)
                  else
                    if b < 555 then
                      (29, 71553554436094571263395611325891803)
                    else
                      (42, 175150492487450594694144397711234320931370091695545)
              else
                if b < 559 then
                  if b < 557 then
                    (53, 4418655863467465019927573946464447205192473951347680888616256731)
                  else
                    if b < 558 then
                      (42, 29843697691227746769243319305225702840090140999776)
                    else
                      (44, 65003377236509281907304102315515886064013157762878897)
                else
                  if b < 560 then
                    (57, 34407440845202179108306888489542193062387699053087022931077514019157)
                  else
                    if b < 561 then
                      (50, 1353438557137465738143259756978926769783852991011060978156763)
                    else
                      (21, 2554088156166060079601248)
        else
          if b < 584 then
            if b < 573 then
              if b < 567 then
                if b < 564 then
                  if b < 563 then
                    (15, 985682282503527193)
                  else
                    (41, 3326732743032637091281392289292890465684773225552)
                else
                  if b < 565 then
                    (16, 9785642870153306964)
                  else
                    if b < 566 then
                      (41, 20172624768244142870700230872770989966463764585241)
                    else
                      (49, 15801129642409463574590634043609433664483921889208529458275)
              else
                if b < 570 then
                  if b < 568 then
                    (41, 3678987185100434248938838495781977825788133720416)
                  else
                    if b < 569 then
                      (14, 35111300867397207)
                    else
                      (26, 1617830093591487797507490464854)
                else
                  if b < 571 then
                    (23, 2644850424278874356919360281)
                  else
                    if b < 572 then
                      (66, 2364461330707167324449800447905637907759997525006823011990246147005981740392803)
                    else
                      (46, 19490395096919019727253953457977056962351235488918406363)
            else
              if b < 578 then
                if b < 575 then
                  if b < 574 then
                    (78, 4084805083140780935702644797041187182424608485559578580118341399562556951648637692687201655577)
                  else
                    (29, 61614859101321601841759549283359489)
                else
                  if b < 576 then
                    (70, 1425150015510988136193330892619639460426491887471759274700657472286231229004360207801)
                  else
                    if b < 577 then
                      (49, 13054897633177790740412476170956079607438861084852973233731)
                    else
                      (18, 617128342389224931424)
              else
                if b < 581 then
                  if b < 579 then
                    (46, 3488332112758190470627477201137581912945727777884164101)
                  else
                    if b < 580 then
                      (42, 315301081233286352318618410991295794394750892956553)
                    else
                      (11, 912571292005)
                else
                  if b < 582 then
                    (27, 196551702281322380222801683809499)
                  else
                    if b < 583 then
                      (51, 12640619059467102562183542904904015374871370520440678205676425)
                    else
                      (15, 183753016322844000)
          else
            if b < 595 then
              if b < 589 then
                if b < 586 then
                  if b < 585 then
                    (58, 5978133221093032841800392541885052020888159003662602479372428034497305)
                  else
                    (39, 7286059006647399113584794752252382074120857094)
                else
                  if b < 587 then
                    (9, 54970407793)
                  else
                    if b < 588 then
                      (56, 3504397399195400986475200669039727854887729597631739842204578264678)
                    else
                      (42, 229226595324016167189412554757220622817873023225265)
              else
                if b < 592 then
                  if b < 590 then
                    (23, 4037117309233194530930274569)
                  else
                    if b < 591 then
                      (14, 35141925324809045)
                    else
                      (10, 173824237571)
                else
                  if b < 593 then
                    (40, 712141955029355297338925312313290637199238254009)
                  else
                    if b < 594 then
                      (60, 251360819250597146226581109049597050750989751795355798996780365187978836)
                    else
                      (41, 19687404189167326574600865547525536355925260371163)
            else
              if b < 600 then
                if b < 597 then
                  if b < 596 then
                    (71, 15282266229705966739106790051386903939627301918581270736240484755622582497917704395657)
                  else
                    (16, 14446894187554170121)
                else
                  if b < 598 then
                    (27, 237881858947800913003434806336264)
                  else
                    if b < 599 then
                      (49, 78258212059663753818886157944845553389116576689225547963273)
                    else
                      (53, 3637661219390100209377559145537842243747770858905535834195548953)
              else
                if b < 603 then
                  if b < 601 then
                    (28, 3199375788844948119420763650710297)
                  else
                    if b < 602 then
                      (47, 339817364673126918184658028424772851028321625921533529528)
                    else
                      (74, 109799257628163976779905007896260820441548056209022323382200398447841451415106614383139721)
                else
                  if b < 604 then
                    (17, 46679130989367677973)
                  else
                    if b < 605 then
                      (26, 2636415583443718261643668768260)
                    else
                      (26, 10717471760040183067409432338528)
      else
        if b < 649 then
          if b < 627 then
            if b < 616 then
              if b < 611 then
                if b < 608 then
                  if b < 607 then
                    (19, 10749253265317769082214)
                  else
                    (15, 201859683884348516)
                else
                  if b < 609 then
                    (24, 6319648807576507649674577505)
                  else
                    if b < 610 then
                      (40, 1162057926492799351349045741184399396470997929400)
                    else
                      (78, 1187017907935675055197246592636026876687440438866923388430303015903662876507739241930956366160)
              else
                if b < 613 then
                  if b < 612 then
                    (25, 930245211552841195144592481032)
                  else
                    (76, 15880457208339059136939376042271512281190882671003013001418009877801560548742031893420068281)
                else
                  if b < 614 then
                    (58, 3231454110282784214541180139972642355737685924478788293744742138662321)
                  else
                    if b < 615 then
                      (29, 45936871088181456995732900542809307)
                    else
                      (66, 8188606446561731162762635004266102113722844325705183797742796845858479911142931)
            else
              if b < 621 then
                if b < 618 then
                  if b < 617 then
                    (51, 7102483919192828477516053583643454190475101135894326629778966)
                  else
                    (51, 2050843289208542055386715441318898791359095280286848312042758)
                else
                  if b < 619 then
                    (52, 113639742707085255640256857338295267047567118362863150302381158)
                  else
                    if b < 620 then
                      (52, 53472860705496230872729502396236081770137351322530535180735509)
                    else
                      (78, 7035383095479617978775597755919839082633648745225686184723108420289372368836459458288041348537)
              else
                if b < 624 then
                  if b < 622 then
                    (27, 259456589776785358019822562368281)
                  else
                    if b < 623 then
                      (19, 64859098053462272115931)
                    else
                      (21, 16532041017881394265875849)
                else
                  if b < 625 then
                    (20, 1046738896815565719836249)
                  else
                    if b < 626 then
                      (20, 891876744058274919032401)
                    else
                      (33, 4269297656276834508582591901303923147995)
          else
            if b < 638 then
              if b < 632 then
                if b < 629 then
                  if b < 628 then
                    (16, 9767413023167039043)
                  else
                    (77, 288342660113010569597706532270153755835455216685481616212257630549034470064679152559069351352)
                else
                  if b < 630 then
                    (24, 48429331283718767900125842872)
                  else
                    if b < 631 then
                      (26, 2650546048012120649912583022133)
                    else
                      (24, 41865124072219513129624035648)
              else
                if b < 635 then
                  if b < 633 then
                    (25, 695950169778866178515545873168)
                  else
                    if b < 634 then
                      (16, 15829200344780787849)
                    else
                      (57, 342987435081215295362255203848929564833572166038842644652488484998577)
                else
                  if b < 636 then
                    (41, 19957133788508579929150010255920215741385559526841)
                  else
                    if b < 637 then
                      (24, 40981969903082396906188842037)
                    else
                      (17, 87930170126082663817)
            else
              if b < 643 then
                if b < 640 then
                  if b < 639 then
                    (17, 38364896045828359701)
                  else
                    (16, 12384010039101075481)
                else
                  if b < 641 then
                    (23, 704463061447798301439321685)
                  else
                    if b < 642 then
                      (26, 3111568160867397112635028033634)
                    else
                      (17, 38364896049932666448)
              else
                if b < 646 then
                  if b < 644 then
                    (32, 53536309706909875809783061455446546001)
                  else
                    if b < 645 then
                      (40, 229936699068777140558677405986373686238712828004)
                    else
                      (75, 1714702254638186778323097838385297045364601692209482648016083915180775221951061970795908537)
                else
                  if b < 647 then
                    (16, 13580742615121113353)
                  else
                    if b < 648 then
                      (24, 67115768732608407503840271241)
                    else
                      (69, 62804686132373836643900419149327087973688261867759887091341293796896826140643374612)
        else
          if b < 671 then
            if b < 660 then
              if b < 654 then
                if b < 651 then
                  if b < 650 then
                    (24, 63402253878909717466414832385)
                  else
                    (50, 443905244949551779844753348977736188838705472091308089828676)
                else
                  if b < 652 then
                    (31, 15659273587918412077488328122774343096)
                  else
                    if b < 653 then
                      (13, 2493391066441296)
                    else
                      (27, 49785090543160125112557595002182)
              else
                if b < 657 then
                  if b < 655 then
                    (21, 16626225519145487297807579)
                  else
                    if b < 656 then
                      (28, 4496964445724057897094818670948489)
                    else
                      (52, 64721427015309162801523237042624259588349171804240217811338772)
                else
                  if b < 658 then
                    (43, 2935864140947852568172857336715074986108931069500185)
                  else
                    if b < 659 then
                      (13, 695774339621460)
                    else
                      (14, 5747687114888289)
            else
              if b < 665 then
                if b < 662 then
                  if b < 661 then
                    (13, 3612340300512688)
                  else
                    (25, 350179493274060378039023310369)
                else
                  if b < 663 then
                    (15, 926541064920124849)
                  else
                    if b < 664 then
                      (52, 58524501335480517294858840538560657471185301789038518005491011)
                    else
                      (40, 1242014614973171799168867317463789854500648406457)
              else
                if b < 668 then
                  if b < 666 then
                    (25, 929941648672893056997023679707)
                  else
                    if b < 667 then
                      (14, 39263153380711193)
                    else
                      (68, 2096283250319803177667234561092122141113048147380527052222155992593906321735181616)
                else
                  if b < 669 then
                    (30, 106026116956134904189069197319628294)
                  else
                    if b < 670 then
                      (53, 3517260131077353045554895051355831645918455199860478809370283448)
                    else
                      (17, 216550197612343479737)
          else
            if b < 682 then
              if b < 676 then
                if b < 673 then
                  if b < 672 then
                    (51, 18526812498876234086574360361518941555450871474764689973839067)
                  else
                    (20, 549570997806858838039936)
                else
                  if b < 674 then
                    (27, 171479548195765529794893879206212)
                  else
                    if b < 675 then
                      (15, 149862875262181476)
                    else
                      (26, 1617830100084741711453154010134)
              else
                if b < 679 then
                  if b < 677 then
                    (28, 816899256094166637698049707958309)
                  else
                    if b < 678 then
                      (25, 180342545559899730861789357585)
                    else
                      (25, 669841985097136275456073745669)
                else
                  if b < 680 then
                    (17, 249780750131208258779)
                  else
                    if b < 681 then
                      (41, 12095742567018054600503501285590645207207720870499)
                    else
                      (53, 936392021367688276717741448616971187378361199750300315255453024)
            else
              if b < 687 then
                if b < 684 then
                  if b < 683 then
                    (51, 17428958170850368985791125094650520603507101758727423409838873)
                  else
                    (14, 53161130726336080)
                else
                  if b < 685 then
                    (63, 4904496878092536593360928137806269832644552470236691497089625362064199703433)
                  else
                    if b < 686 then
                      (41, 1865231105701734173077707456576607446028792108625)
                    else
                      (40, 403729468370831254874022623860323407849702180385)
              else
                if b < 690 then
                  if b < 688 then
                    (38, 3160856913038360159943574253359163551101879515)
                  else
                    if b < 689 then
                      (29, 66684110167447100149376531039069785)
                    else
                      (46, 18084758353680773989874740657934373034910100688300166577)
                else
                  if b < 691 then
                    (37, 46380313396731021457286474326608355082256981)
                  else
                    if b < 692 then
                      (14, 35141925269279846)
                    else
                      (24, 10353695500047346288721023329)

def forward5Blocks (b : Nat) : Nat :=
  if b < 1 then
    155976492605066875612637722134020692382206720257375073509406946906690493199012408489843816692884577200110411273072163118909843641531145413668298282022246745562590522684046727684394056087457970034727837413274369255143732086249915187640631074829285441384495703649552805973522794744874754828480040927307671356261249881186896412318475656218619208648494727257509569175187757362436619915003327691194704595104401722437086150785719956979187018291115844484819415641866577317612915766757895023870154522563538372386247488523675239660359682664364428312826430931591057262167329441214868692514315782594441711949130174982314618598185654748120775195147641485489858476674976126890317700421696628876946035960390928504783277299660464559718172487041855140236733299614702751137470975031911428
  else
    if b < 2 then
      220318584416705398164028227184666251367117784448371122008567169007962187103332937936884626341023896318082812637533554747276173753137453761305648617111082138850119542827730705655410402741800398873915142077242709930460241715638383259398940308466546204996706354371366714505916399051899779719167639534277652502426528743806467372539291511303486006724068669225423449479830416267342214609576679453786420981643396710070358624071195235938394561686182482942769029690665504241605294329854225051760681177654987173982115668645775538211082794803202650212302245923173099765067093758067779811726113587043267350618464812613288440008277191351643806437632758264076809040511623972937054678514651417372512067158640359322965884003788482153443296430131255510029142761128253983862490757240823927
    else
      7599987445994064222163021861702594122174749642548735382070269505689888045708842808372856195240469869492670968926024028593885376133105294892034308467676564167577514824201734958640331238831331961905267656775071974072240328889223390083144422467002140212137216318839579938802591030550778184265108891437824550146408927383762543704704309297782657171706833833689127690160935021590095761325210411734308591570137385099749993968629660644566556491021587521275141583626394374226111358840307835544533886206454801717171392024312735990115370645534761945691737

def backward5Blocks (b : Nat) : Nat :=
  if b < 1 then
    88571574708813608415005248372198357745576546463835898721177237866284778359497977961332378788673934500315261222324163399024675241618132300913003520063151491855026124979860880905365489250671153699034968587209905574346472164434559335402407788758751638145131148732975019323081885349831584107253419434800195360476596149160571150345059429295523261179334649130230113888908227243005800130843473539797974564195540468864122494534230708059882120871015414041164280713847836261985331389470399075416408115285941025792954658290271411353657920275448957110554596173387890650334875672748335802663883793680994192055861593530133943047657654265384065349375782586407965517332481865458734505436610912957030415329551132135559789906456080151827855325874143197889755707343187571763292985834724563
  else
    if b < 2 then
      275636797803284866053352378820537219759341167041623648998800175626835396010769805705637366798876045159788434877391908558386288559909921406801859694809101907377370717248082572260884756371775361449309320672427110298085665685420038270440571705461858820862950774816125986875840719324225437080291978853672703904129831011407994876687176747554304113753443679799106203420713216274889655193203360873892042433727864892039075340141917387967263899972728799857475816157255068359603967791022102671300694916381223268731130510406337807151388184915674624611162623833357728804404645346684503319578208043485490841455389072281136996120595980311419394648426388923327034943631435540899610158290624697495708471491679991486431130453458171754175600340007799447471430256143101275520260548243556733
    else
      41619264406372324465017692859292216031708751716767729214664969885899328344646715989251178562919299572213465513838169140316559700236961350639646176425602283116935231492319704889988938950235088902324814682446140982204964663734557066297121120010183884176856512160710130733092813818626975576628295234950490762437753127469499574664369152587217607148675972839067929463971557552693905031506560219275404771450692569398178494764887534595562335456371250209142388721840641671334729323574093218299043632708633459029849467369858334360721223016452794334257386

def factorCode5 (b : Nat) : Nat × Nat :=
  if b < 346 then
    if b < 173 then
      if b < 86 then
        if b < 43 then
          if b < 21 then
            if b < 10 then
              if b < 5 then
                (0, 0)
              else
                if b < 7 then
                  (0, 0)
                else
                  if b < 8 then
                    (0, 0)
                  else
                    if b < 9 then
                      (47, 191091007099758841555992529537570780909518422903095614233)
                    else
                      (35, 934340755160406325130312170099654053088697)
            else
              if b < 15 then
                (0, 0)
              else
                if b < 18 then
                  (0, 0)
                else
                  if b < 19 then
                    (0, 0)
                  else
                    if b < 20 then
                      (16, 11302870082206413057)
                    else
                      (0, 0)
          else
            if b < 32 then
              if b < 26 then
                (0, 0)
              else
                if b < 29 then
                  (0, 0)
                else
                  if b < 30 then
                    (0, 0)
                  else
                    if b < 31 then
                      (14, 62144155683409337)
                    else
                      (0, 0)
            else
              if b < 37 then
                (0, 0)
              else
                if b < 40 then
                  (0, 0)
                else
                  if b < 41 then
                    (0, 0)
                  else
                    if b < 42 then
                      (0, 0)
                    else
                      (22, 48690990030909120679405076)
        else
          if b < 64 then
            if b < 53 then
              (0, 0)
            else
              if b < 58 then
                if b < 55 then
                  (0, 0)
                else
                  if b < 56 then
                    (0, 0)
                  else
                    if b < 57 then
                      (0, 0)
                    else
                      (25, 1073446021574735104259080575753)
              else
                (0, 0)
          else
            if b < 75 then
              if b < 69 then
                if b < 66 then
                  if b < 65 then
                    (0, 0)
                  else
                    (24, 63287028136727698553126629633)
                else
                  if b < 67 then
                    (56, 3835461719522051181435868973535111248031493076205398059021191177252)
                  else
                    (0, 0)
              else
                if b < 72 then
                  (0, 0)
                else
                  if b < 73 then
                    (0, 0)
                  else
                    if b < 74 then
                      (52, 356016732918748789862556714341668587408164025860591770055007113)
                    else
                      (0, 0)
            else
              if b < 80 then
                if b < 77 then
                  (0, 0)
                else
                  if b < 78 then
                    (0, 0)
                  else
                    if b < 79 then
                      (25, 576266958596324812954735633462)
                    else
                      (16, 12528372928257265801)
              else
                if b < 83 then
                  if b < 81 then
                    (0, 0)
                  else
                    if b < 82 then
                      (0, 0)
                    else
                      (19, 41571347883957933986405)
                else
                  if b < 84 then
                    (0, 0)
                  else
                    if b < 85 then
                      (0, 0)
                    else
                      (25, 593530885461347279891379106049)
      else
        if b < 129 then
          if b < 107 then
            if b < 96 then
              if b < 91 then
                if b < 88 then
                  if b < 87 then
                    (40, 229936699068777140558677405986373835297535649349)
                  else
                    (18, 746255550877224293126)
                else
                  if b < 89 then
                    (24, 43556222104541562427496782617)
                  else
                    if b < 90 then
                      (16, 9069472940529419483)
                    else
                      (0, 0)
              else
                if b < 93 then
                  if b < 92 then
                    (0, 0)
                  else
                    (14, 53358048695353481)
                else
                  if b < 94 then
                    (27, 42408736767940075788445851993685)
                  else
                    if b < 95 then
                      (0, 0)
                    else
                      (39, 56119546651774327095695393144405066510741330825)
            else
              if b < 101 then
                if b < 98 then
                  (0, 0)
                else
                  if b < 99 then
                    (49, 13054897633177790740412476170956074650912445874716912280932)
                  else
                    (0, 0)
              else
                if b < 104 then
                  if b < 102 then
                    (46, 3488332112758190470627477201137584392768824716711781970)
                  else
                    if b < 103 then
                      (5, 832905)
                    else
                      (13, 3550153358022232)
                else
                  if b < 105 then
                    (0, 0)
                  else
                    if b < 106 then
                      (49, 27744077809346986240297084311108511802305767906503469307460)
                    else
                      (24, 11271408965722889901866447713)
          else
            if b < 118 then
              if b < 112 then
                if b < 109 then
                  if b < 108 then
                    (14, 57744497469113872)
                  else
                    (0, 0)
                else
                  if b < 110 then
                    (0, 0)
                  else
                    if b < 111 then
                      (14, 44394817010898521)
                    else
                      (77, 341947175413506131385249215856659999582102123682167885845851033408771034565765461744386704603)
              else
                if b < 115 then
                  if b < 113 then
                    (45, 733644299887909607950367499393121796675593560846781881)
                  else
                    (0, 0)
                else
                  (0, 0)
            else
              if b < 123 then
                if b < 120 then
                  if b < 119 then
                    (0, 0)
                  else
                    (40, 990817270498338252457631654792271169386750954936)
                else
                  if b < 121 then
                    (24, 9988168057977336289947963475)
                  else
                    (0, 0)
              else
                if b < 126 then
                  if b < 124 then
                    (0, 0)
                  else
                    if b < 125 then
                      (0, 0)
                    else
                      (60, 1267221730249995741153386513160789118199217863711896901476398792326830873)
                else
                  if b < 127 then
                    (0, 0)
                  else
                    if b < 128 then
                      (0, 0)
                    else
                      (31, 11619322469576624175875427333008841609)
        else
          if b < 151 then
            if b < 140 then
              if b < 134 then
                if b < 131 then
                  if b < 130 then
                    (19, 12042942190894475601440)
                  else
                    (0, 0)
                else
                  if b < 132 then
                    (42, 193531881072288873608056020569449712769916109850196)
                  else
                    if b < 133 then
                      (16, 14464925047753857929)
                    else
                      (42, 193531881072288873608056020569449417337923212305684)
              else
                if b < 137 then
                  (0, 0)
                else
                  if b < 138 then
                    (0, 0)
                  else
                    if b < 139 then
                      (0, 0)
                    else
                      (66, 4217134758504226451226936208044644433412317279657072036621567491344539626571301)
            else
              if b < 145 then
                if b < 142 then
                  if b < 141 then
                    (31, 18348783137013872244704215496541920025)
                  else
                    (41, 3326732743032637091281392289292947089238065964053)
                else
                  if b < 143 then
                    (56, 19459681941939485845982145081830825335555973916573196111430377557433)
                  else
                    if b < 144 then
                      (14, 4580586302038785)
                    else
                      (0, 0)
              else
                if b < 148 then
                  if b < 146 then
                    (46, 12055583900845359808233847674647093703100444104567686363)
                  else
                    (0, 0)
                else
                  if b < 149 then
                    (0, 0)
                  else
                    if b < 150 then
                      (43, 778132536004650040889529953655962663039396292673616)
                    else
                      (15, 164020587946136662)
          else
            if b < 162 then
              if b < 156 then
                if b < 153 then
                  if b < 152 then
                    (0, 0)
                  else
                    (25, 830859415391268496088225566136)
                else
                  if b < 154 then
                    (0, 0)
                  else
                    if b < 155 then
                      (14, 48920416577670585)
                    else
                      (0, 0)
              else
                if b < 159 then
                  if b < 157 then
                    (14, 53136485466137864)
                  else
                    if b < 158 then
                      (9, 53651102465)
                    else
                      (23, 1367888668881730623786845536)
                else
                  if b < 160 then
                    (18, 617128342357260263505)
                  else
                    if b < 161 then
                      (15, 782439810939113737)
                    else
                      (40, 1169572819119674403783976966163655321423054243035)
            else
              if b < 167 then
                if b < 164 then
                  if b < 163 then
                    (63, 3743451007150044241184021183808272360187069288954728072365599501002001945805)
                  else
                    (17, 143941333598000727552)
                else
                  if b < 165 then
                    (39, 12995049777471238637817938630050574567525598566)
                  else
                    if b < 166 then
                      (14, 57945656900032088)
                    else
                      (15, 149862875201438817)
              else
                if b < 170 then
                  if b < 168 then
                    (25, 180342545796671701423145485397)
                  else
                    if b < 169 then
                      (0, 0)
                    else
                      (41, 11302393424388526436632129796490044415656773832121)
                else
                  if b < 171 then
                    (20, 509083861016566453230337)
                  else
                    if b < 172 then
                      (56, 22942879335800196182316348626082310573717984189239835319272810237369)
                    else
                      (23, 1367888669886591776382657892)
    else
      if b < 259 then
        if b < 216 then
          if b < 194 then
            if b < 183 then
              if b < 178 then
                if b < 175 then
                  if b < 174 then
                    (55, 134404065801571012141823783162278100842633297679397018607468414532)
                  else
                    (72, 137382019092958621051599884195733316639984723386730220894431215130642317175705716875601)
                else
                  if b < 176 then
                    (38, 4523977777953563679441975432455164333457278171)
                  else
                    if b < 177 then
                      (15, 152227818686342468)
                    else
                      (14, 39931837691041361)
              else
                if b < 180 then
                  if b < 179 then
                    (0, 0)
                  else
                    (35, 945215179452512661064289805560724303698825)
                else
                  if b < 181 then
                    (0, 0)
                  else
                    if b < 182 then
                      (0, 0)
                    else
                      (15, 854484186404381953)
            else
              if b < 188 then
                if b < 185 then
                  if b < 184 then
                    (0, 0)
                  else
                    (42, 291551662291314279477519449781500194321342224718729)
                else
                  if b < 186 then
                    (1, 6)
                  else
                    if b < 187 then
                      (10, 806342111489)
                    else
                      (50, 252818074278551417193450144697750859327315151836798709490792)
              else
                if b < 191 then
                  if b < 189 then
                    (27, 254390716621409028616566810194177)
                  else
                    if b < 190 then
                      (70, 276374143533332984707608491330413817588109625239605872992031047097999369366524663397)
                    else
                      (14, 5747687126950211)
                else
                  if b < 192 then
                    (25, 768081181835243817507024121881)
                  else
                    if b < 193 then
                      (0, 0)
                    else
                      (76, 16859004560880647201974918632940748953369124576319536989872713851999970910010434244931138821)
          else
            if b < 205 then
              if b < 199 then
                if b < 196 then
                  if b < 195 then
                    (0, 0)
                  else
                    (40, 1264845392007106115826095434696537604440375446968)
                else
                  if b < 197 then
                    (0, 0)
                  else
                    if b < 198 then
                      (19, 20872324511780664796454)
                    else
                      (47, 108375303942761665001160485590267624228096081870480695908)
              else
                if b < 202 then
                  if b < 200 then
                    (0, 0)
                  else
                    if b < 201 then
                      (70, 305638297660589970508833157502266951303989116749277327247817845014297700885049266480)
                    else
                      (41, 20144059298078581448812626339571378268587581001144)
                else
                  if b < 203 then
                    (28, 4376859947997291921014801012415257)
                  else
                    if b < 204 then
                      (0, 0)
                    else
                      (9, 36295414100)
            else
              if b < 210 then
                if b < 207 then
                  if b < 206 then
                    (50, 831213099938842124011278130481689813063535387145263259059028)
                  else
                    (0, 0)
                else
                  if b < 208 then
                    (0, 0)
                  else
                    if b < 209 then
                      (5, 515385)
                    else
                      (67, 245330805204585299390236012302058937397219772920937058950551928897667201329684485)
              else
                if b < 213 then
                  if b < 211 then
                    (0, 0)
                  else
                    if b < 212 then
                      (23, 2704729940290421338243652377)
                    else
                      (78, 7035395528560528223434760835444482802447571294262747260219488662203665855918086902783330504113)
                else
                  if b < 214 then
                    (21, 15373914072681247375779209)
                  else
                    if b < 215 then
                      (25, 1009188056936804888845784319195)
                    else
                      (0, 0)
        else
          if b < 237 then
            if b < 226 then
              if b < 221 then
                if b < 218 then
                  if b < 217 then
                    (0, 0)
                  else
                    (68, 4144024119235940373272900108956267465282208003844893876103495528355107164435831689)
                else
                  if b < 219 then
                    (17, 213109449360282213121)
                  else
                    if b < 220 then
                      (51, 21881130471743704606524440196089250446083298132066117393337785)
                    else
                      (14, 48639909989803401)
              else
                if b < 223 then
                  if b < 222 then
                    (25, 199438294948904894662379812160)
                  else
                    (0, 0)
                else
                  if b < 224 then
                    (23, 2935034841749581868946181560)
                  else
                    if b < 225 then
                      (16, 13244397210276715273)
                    else
                      (23, 394978056111211673372919364)
            else
              if b < 231 then
                if b < 228 then
                  if b < 227 then
                    (35, 181173099205980552567525290338313886000437)
                  else
                    (31, 15663737143899987778998071209020939033)
                else
                  if b < 229 then
                    (14, 37272884634388052)
                  else
                    if b < 230 then
                      (28, 4091777096115318781712384506253925)
                    else
                      (0, 0)
              else
                if b < 234 then
                  if b < 232 then
                    (52, 197337116566316062977844765499456726223511352319794613630029240)
                  else
                    if b < 233 then
                      (13, 359230455828833)
                    else
                      (51, 13845933029966780519156650164427119656178044893190718130357467)
                else
                  if b < 235 then
                    (23, 3632169751951879691729337776)
                  else
                    if b < 236 then
                      (78, 4315905167585445683705579170032831732062495891537801469407414746132294485144054037768346928133)
                    else
                      (26, 2636415583501089335109061665856)
          else
            if b < 248 then
              if b < 242 then
                if b < 239 then
                  if b < 238 then
                    (0, 0)
                  else
                    (42, 48633283500290627555595622103497664075018537423972)
                else
                  if b < 240 then
                    (57, 289067554571455655304657191801930155395903516466814765595913625816504)
                  else
                    if b < 241 then
                      (32, 159318750504176314157699823824291390857)
                    else
                      (51, 16857490589675187289032100000417107495374429573196182777253304)
              else
                if b < 245 then
                  if b < 243 then
                    (19, 9883822204516644401249)
                  else
                    if b < 244 then
                      (0, 0)
                    else
                      (13, 507039433769990)
                else
                  if b < 246 then
                    (24, 56903068672661471522027581465)
                  else
                    if b < 247 then
                      (16, 2917445688598070849)
                    else
                      (0, 0)
            else
              if b < 253 then
                if b < 250 then
                  if b < 249 then
                    (47, 31293385150276825796306082783796363669231537016203011172)
                  else
                    (53, 3075465156663662920292353285241342271415867723792982798871354249)
                else
                  if b < 251 then
                    (49, 79907171744468251948483591502270696360846162782603326803377)
                  else
                    if b < 252 then
                      (15, 560656911054537947)
                    else
                      (41, 11354279844207632495534233196233777437872486669193)
              else
                if b < 256 then
                  if b < 254 then
                    (50, 443905244949551779844753348977715886904567126555466428450371)
                  else
                    if b < 255 then
                      (0, 0)
                    else
                      (30, 900777130626998893788568246927123849)
                else
                  if b < 257 then
                    (17, 139326811038676791561)
                  else
                    if b < 258 then
                      (40, 116576944106358385817356716036040365466682869270)
                    else
                      (40, 1260921883362269122324869700166940797397154942392)
      else
        if b < 302 then
          if b < 280 then
            if b < 269 then
              if b < 264 then
                if b < 261 then
                  if b < 260 then
                    (23, 3322798078926123494220516792)
                  else
                    (25, 180342545796671701423130814005)
                else
                  if b < 262 then
                    (47, 31293385150276825796306082783796363669234920482751668805)
                  else
                    if b < 263 then
                      (13, 3826013888306040)
                    else
                      (12, 155152620033624)
              else
                if b < 266 then
                  if b < 265 then
                    (0, 0)
                  else
                    (41, 19957451672591126237950805485262473277164828511672)
                else
                  if b < 267 then
                    (26, 13764826727216290256728394583481)
                  else
                    if b < 268 then
                      (32, 270958872944277387060721902522816922843)
                    else
                      (43, 778132536004650040889529953655962663039396221117733)
            else
              if b < 274 then
                if b < 271 then
                  if b < 270 then
                    (0, 0)
                  else
                    (69, 65356281761949209364126385595687075094797012597614878385741468994574961142632078217)
                else
                  if b < 272 then
                    (26, 1617830100084741711453154059526)
                  else
                    if b < 273 then
                      (0, 0)
                    else
                      (74, 67350083238930160765995329892050657387755510270080950641536484258625475082431200800146651)
              else
                if b < 277 then
                  if b < 275 then
                    (25, 199438295166603771961896167012)
                  else
                    if b < 276 then
                      (0, 0)
                    else
                      (49, 15801129642409463574590634043609428707957192752342304319588)
                else
                  if b < 278 then
                    (69, 94791457432912457322455523984529106362418726729341366592953506884473630923929475865)
                  else
                    if b < 279 then
                      (16, 13586044724009390217)
                    else
                      (17, 47040772143779825157)
          else
            if b < 291 then
              if b < 285 then
                if b < 282 then
                  if b < 281 then
                    (25, 164775973848977050787241572149)
                  else
                    (26, 3191012721378645720522100986948)
                else
                  if b < 283 then
                    (14, 52017652391568665)
                  else
                    if b < 284 then
                      (17, 38608680457106429284)
                    else
                      (23, 4285456914564867135408983473)
              else
                if b < 288 then
                  if b < 286 then
                    (0, 0)
                  else
                    if b < 287 then
                      (26, 13773581763485080387016047218097)
                    else
                      (15, 596366154136953952)
                else
                  if b < 289 then
                    (53, 5241109195084215490424942270384235276645343040712647423520201497)
                  else
                    if b < 290 then
                      (16, 8632727861793547529)
                    else
                      (14, 12616232535998545)
            else
              if b < 296 then
                if b < 293 then
                  if b < 292 then
                    (0, 0)
                  else
                    (51, 3342053794093514429545593899764757585668359427985041748153696)
                else
                  if b < 294 then
                    (25, 350179499872590088397966688596)
                  else
                    if b < 295 then
                      (14, 53073252541687041)
                    else
                      (21, 10260990228773351193601120)
              else
                if b < 299 then
                  if b < 297 then
                    (46, 1955836571892301612269130173987272729326971063514435681)
                  else
                    if b < 298 then
                      (15, 917850609091974737)
                    else
                      (48, 3747019420911712268228223384390424418081435007377559837577)
                else
                  if b < 300 then
                    (52, 53472860705496230872729502396236080486896338301180509975626068)
                  else
                    if b < 301 then
                      (24, 67076634544259481737267381467)
                    else
                      (66, 25534326817114908483501899454126331663395009678098177612617803942826487155317641)
        else
          if b < 324 then
            if b < 313 then
              if b < 307 then
                if b < 304 then
                  if b < 303 then
                    (47, 192313899527852829525074819481183233621133959780213512985)
                  else
                    (14, 48898429445099521)
                else
                  if b < 305 then
                    (53, 525015882037386766178999152977638090588392932808585039397130595)
                  else
                    if b < 306 then
                      (0, 0)
                    else
                      (52, 32813492627336672886187447061102055830827987853177577174885685)
              else
                if b < 310 then
                  if b < 308 then
                    (12, 225564463350882)
                  else
                    if b < 309 then
                      (30, 189102862972531349864669835727094372)
                    else
                      (14, 39637828013220630)
                else
                  if b < 311 then
                    (47, 333392556120297602955042102691305799875049788072429374905)
                  else
                    if b < 312 then
                      (30, 232870384236272700912482746401621556)
                    else
                      (25, 159810688927637380639061460497)
            else
              if b < 318 then
                if b < 315 then
                  if b < 314 then
                    (27, 42408736765745918104827005653861)
                  else
                    (24, 38524592598883145334615199153)
                else
                  if b < 316 then
                    (70, 1384845213919974916979655469170608229221734572119041219120428420903212401659499007409)
                  else
                    if b < 317 then
                      (25, 1018996111082408863966202711473)
                    else
                      (66, 4217134758504226451226936208044644433412317279657072036621567491123353749053877)
              else
                if b < 321 then
                  if b < 319 then
                    (8, 3684423897)
                  else
                    if b < 320 then
                      (69, 66303039015753174618696694668283924724548396456066274901737419272416024982756580233)
                    else
                      (56, 2150465052825136194269180530596384330929282746198229265244165441090)
                else
                  if b < 322 then
                    (14, 47249624370531769)
                  else
                    if b < 323 then
                      (47, 184650625305131039891192663337197857328794551686059580297)
                    else
                      (20, 641311889298334456022372)
          else
            if b < 335 then
              if b < 329 then
                if b < 326 then
                  if b < 325 then
                    (30, 687563361701359828102720993450344528)
                  else
                    (13, 788514388878916)
                else
                  if b < 327 then
                    (43, 3668167678600780153009794750962456319402540261497737)
                  else
                    if b < 328 then
                      (47, 108375303942761665001160485590262667701337770509857735267)
                    else
                      (0, 0)
              else
                if b < 332 then
                  if b < 330 then
                    (45, 908896889005929334946140734005884148351179558303583665)
                  else
                    if b < 331 then
                      (13, 3618345823557989)
                    else
                      (30, 788489912845652519336265400948415257)
                else
                  if b < 333 then
                    (31, 2808249624553898271685914668485197924)
                  else
                    if b < 334 then
                      (14, 33739303953420901)
                    else
                      (50, 128177705575533878461669715082431174460056872286709834208869)
            else
              if b < 340 then
                if b < 337 then
                  if b < 336 then
                    (29, 13128266488202285356372937441044036)
                  else
                    (67, 410930678021025363860702478487566511844260152346697508558290613159044051840140507)
                else
                  if b < 338 then
                    (50, 1385959639284381725104747649716264360883624863164125423881656)
                  else
                    if b < 339 then
                      (68, 4499853124576340021037238961865110015851080707137851447907132430683526243540815289)
                    else
                      (24, 6319648803154553031050933573)
              else
                if b < 343 then
                  if b < 341 then
                    (16, 13595695269631124745)
                  else
                    if b < 342 then
                      (38, 1577068235823559589351650874454613476346189349)
                    else
                      (16, 2868113814416852294)
                else
                  if b < 344 then
                    (17, 38570521397580293684)
                  else
                    if b < 345 then
                      (24, 40981970037699225015411607044)
                    else
                      (42, 48633283500290627555595622103497682539518070449446)
  else
    if b < 519 then
      if b < 432 then
        if b < 389 then
          if b < 367 then
            if b < 356 then
              if b < 351 then
                if b < 348 then
                  if b < 347 then
                    (19, 6026886976322601182549)
                  else
                    (19, 63896696827493654482353)
                else
                  if b < 349 then
                    (41, 19780844729829665408893693402149245864158710222265)
                  else
                    if b < 350 then
                      (16, 13437848790749207312)
                    else
                      (67, 341916288035839838449907132444640899377322717786724777242790116239364954056426715)
              else
                if b < 353 then
                  if b < 352 then
                    (41, 17331499526846559385436898001870988699463231789849)
                  else
                    (41, 3326732743032637091281392289292890465684602007652)
                else
                  if b < 354 then
                    (46, 18053141756181081507720376848793212751012844961412733721)
                  else
                    if b < 355 then
                      (15, 925452028859278601)
                    else
                      (27, 42182649335099492186300025406790)
            else
              if b < 361 then
                if b < 358 then
                  if b < 357 then
                    (24, 43263666814369183352042806136)
                  else
                    (26, 3111568159036705837506625949701)
                else
                  if b < 359 then
                    (14, 51964111513032280)
                  else
                    if b < 360 then
                      (27, 197563080326939466711755587784841)
                    else
                      (44, 12450120576074400654232479258495402608630277884503621)
              else
                if b < 364 then
                  if b < 362 then
                    (40, 792742343063477965293541044522011947820990352817)
                  else
                    if b < 363 then
                      (45, 792706584872095226298597460252468524297727365628364310)
                    else
                      (0, 0)
                else
                  if b < 365 then
                    (39, 7286059006647399113584794752252444963001387890)
                  else
                    if b < 366 then
                      (24, 36016684905627759711803045428)
                    else
                      (70, 276374143533332984707608491330413817588109625239605872992031047098260111262270887446)
          else
            if b < 378 then
              if b < 372 then
                if b < 369 then
                  if b < 368 then
                    (30, 106026116956134797908411631537968660)
                  else
                    (6, 10241817)
                else
                  if b < 370 then
                    (17, 155959740546485870949)
                  else
                    if b < 371 then
                      (0, 0)
                    else
                      (15, 620508823846981657)
              else
                if b < 375 then
                  if b < 373 then
                    (26, 10763821984643069100118216768944)
                  else
                    if b < 374 then
                      (67, 377574118416330620316104629819850174147090040808257224811547704091978129744088497)
                    else
                      (14, 53157873066594441)
                else
                  if b < 376 then
                    (39, 14371043691798571284917337874148355389920076388)
                  else
                    if b < 377 then
                      (51, 20568318202202994815570031526266325726684844530636071809076657)
                    else
                      (41, 11285889804438703144072004088503120620086018198961)
            else
              if b < 383 then
                if b < 380 then
                  if b < 379 then
                    (70, 305638297660589970508833157502266951303989116749277327247817845014259861791344756293)
                  else
                    (51, 21671638269222898593158093320557384495596094005180975894813577)
                else
                  if b < 381 then
                    (17, 38590450638355170817)
                  else
                    if b < 382 then
                      (64, 85086114843332944679557627147408655878840853618952743240279976539923149096155)
                    else
                      (40, 755983910438628412531468830349415325450650408017)
              else
                if b < 386 then
                  if b < 384 then
                    (26, 2650546047969822493736119051777)
                  else
                    if b < 385 then
                      (34, 24064155681635996910179437790955280139792)
                    else
                      (17, 46640971931791156833)
                else
                  if b < 387 then
                    (68, 605302100661034835059148914663843304386559366401746691069503013633531324373165638)
                  else
                    if b < 388 then
                      (39, 61925665801478304233743823380764162195550391736)
                    else
                      (11, 15106822710864)
        else
          if b < 410 then
            if b < 399 then
              if b < 394 then
                if b < 391 then
                  if b < 390 then
                    (14, 53141420995118299)
                  else
                    (29, 42972710086992176142585995297362438)
                else
                  if b < 392 then
                    (18, 531669367461684928593)
                  else
                    if b < 393 then
                      (77, 269744072974090355231598698127051983253905993221112591837963421634474569332493640041173767761)
                    else
                      (14, 11203569564169780)
              else
                if b < 396 then
                  if b < 395 then
                    (9, 10542469174)
                  else
                    (31, 10259273528624642072293094132332782985)
                else
                  if b < 397 then
                    (29, 60917968679581613067549735777600731)
                  else
                    if b < 398 then
                      (35, 1103702933030846791652545291547818615692057)
                    else
                      (29, 56313931024194883860236463766316625)
            else
              if b < 404 then
                if b < 401 then
                  if b < 400 then
                    (67, 340557108782751033260259350625946159282437195186158135726387581253667367286004617)
                  else
                    (25, 1067677178679261545692833795505)
                else
                  if b < 402 then
                    (58, 1085845360864077131100320476883307745566715067790818301881207494894612)
                  else
                    if b < 403 then
                      (78, 4315905167585445683705579170032831732062495891537801469407414746132294484906277206054386603349)
                    else
                      (34, 24064155681635996910163360012513667584097)
              else
                if b < 407 then
                  if b < 405 then
                    (43, 778132536004650040889529953655962625200296553375269)
                  else
                    if b < 406 then
                      (52, 322641406075350253359954537524184900885144215468194687470292409)
                    else
                      (40, 1152407449505879551263330355721485813649304997304)
                else
                  if b < 408 then
                    (69, 9684833610576557360946382634621492870184949862427947057112048218098662090065600772)
                  else
                    if b < 409 then
                      (28, 3479526905989824987759773724574939)
                    else
                      (14, 11396272215187968)
          else
            if b < 421 then
              if b < 415 then
                if b < 412 then
                  if b < 411 then
                    (20, 136107356381341396592213)
                  else
                    (52, 245615582042816049431485266268681052573294788288378324014615993)
                else
                  if b < 413 then
                    (15, 972070331746057648)
                  else
                    if b < 414 then
                      (25, 621597836194566592228172815129)
                    else
                      (47, 330222034457247847611835044621589511362791219266825768377)
              else
                if b < 418 then
                  if b < 416 then
                    (56, 23251295740758735667920566331985685023756361070514793397572163918729)
                  else
                    if b < 417 then
                      (0, 0)
                    else
                      (14, 5747687131993190)
                else
                  if b < 419 then
                    (52, 226062703382879360823348296847410809660199756422523151569669561)
                  else
                    if b < 420 then
                      (41, 14274048562294076643750652323299176936639123443121)
                    else
                      (25, 1018471970904108679172141895096)
            else
              if b < 426 then
                if b < 423 then
                  if b < 422 then
                    (14, 39084432121029897)
                  else
                    (13, 788514411271473)
                else
                  if b < 424 then
                    (69, 17273383970833311544225530708150863599256851577475367062001940443641256955810436677)
                  else
                    if b < 425 then
                      (50, 443905244949551779844753348977715886904564693784879447606628)
                    else
                      (79, 105074117100030431613818440252850419576790964878828489575849840813445676464873214731139604827577)
              else
                if b < 429 then
                  if b < 427 then
                    (66, 15333175325286581211889750768878683587326235807558566184409495556104199987290211)
                  else
                    if b < 428 then
                      (67, 262361736998490517254629573466694837792785380072217931637532213230563674661640985)
                    else
                      (14, 11484563503340390)
                else
                  if b < 430 then
                    (25, 669841985155512210073991012416)
                  else
                    if b < 431 then
                      (14, 56784022270922168)
                    else
                      (40, 207920796439539818205087018080805801914395538950)
      else
        if b < 475 then
          if b < 453 then
            if b < 442 then
              if b < 437 then
                if b < 434 then
                  if b < 433 then
                    (30, 647690569544600352969141131634615896)
                  else
                    (0, 0)
                else
                  if b < 435 then
                    (39, 14371043691798571284917337874148359157824315749)
                  else
                    if b < 436 then
                      (54, 8400254112598188258863986447642126292691945093674599265022784608)
                    else
                      (29, 70684577777279849347487345706608217)
              else
                if b < 439 then
                  if b < 438 then
                    (18, 734237136495501995078)
                  else
                    (0, 0)
                else
                  if b < 440 then
                    (18, 2579638359932925248731)
                  else
                    if b < 441 then
                      (0, 0)
                    else
                      (15, 903204068201227521)
            else
              if b < 447 then
                if b < 444 then
                  if b < 443 then
                    (53, 1035542832244946604824371792681987519804682967199323927255998805)
                  else
                    (64, 56478110366098650825644991802623554281709784375711508847817950616016151436057)
                else
                  if b < 445 then
                    (13, 708547158555652)
                  else
                    if b < 446 then
                      (15, 201859687738901090)
                    else
                      (55, 1339770921250126711799144079866571264224515881533109490135538654089)
              else
                if b < 450 then
                  if b < 448 then
                    (42, 53227723888522193460502276628686285290051621750374)
                  else
                    if b < 449 then
                      (24, 54660205757701931397173009289)
                    else
                      (43, 4366668415952209259512797278745833273167096016031153)
                else
                  if b < 451 then
                    (14, 48370590849323033)
                  else
                    if b < 452 then
                      (42, 300771646716051117914735315774847917208767293610889)
                    else
                      (15, 183753018297439045)
          else
            if b < 464 then
              if b < 458 then
                if b < 455 then
                  if b < 454 then
                    (70, 1645640277376252558582161124112449972772159390702132247066906639477088276654699371401)
                  else
                    (6, 12898568)
                else
                  if b < 456 then
                    (39, 44062853968047005331989578888024682571312942513)
                  else
                    if b < 457 then
                      (43, 4758361331089874548531577603532050954928130346732977)
                    else
                      (20, 589583702417412691677540)
              else
                if b < 461 then
                  if b < 459 then
                    (19, 55983120181065922137521)
                  else
                    if b < 460 then
                      (67, 231329872291948743772552458563509942170881164001916063041090272094313167338884529)
                    else
                      (18, 4055821471307417855569)
                else
                  if b < 462 then
                    (41, 3326732743032637091281392289292947089238047215670)
                  else
                    if b < 463 then
                      (15, 561399425077437712)
                    else
                      (27, 51282290969775458430636807050758)
            else
              if b < 469 then
                if b < 466 then
                  if b < 465 then
                    (51, 3342053794093514429545593899764757585668359427985041753663076)
                  else
                    (24, 39698728999821601734926935601)
                else
                  if b < 467 then
                    (25, 929857221908413604713550544304)
                  else
                    if b < 468 then
                      (14, 38225167366905893)
                    else
                      (42, 277026941650865579638109227560837464715672441343416)
              else
                if b < 472 then
                  if b < 470 then
                    (46, 12029431833767947923933309616738687790410216139640556985)
                  else
                    if b < 471 then
                      (16, 2917445688508171588)
                    else
                      (25, 1019092867840588828391824706993)
                else
                  if b < 473 then
                    (28, 678539788287057290393575075746118)
                  else
                    if b < 474 then
                      (55, 1023937390878148082721635116934341991160568027724677291494493670841)
                    else
                      (16, 13510089458545872312)
        else
          if b < 497 then
            if b < 486 then
              if b < 480 then
                if b < 477 then
                  if b < 476 then
                    (25, 1000349609436419064451377770753)
                  else
                    (44, 52695427573198642570384447426551978581115009920683449)
                else
                  if b < 478 then
                    (15, 632982090490144025)
                  else
                    if b < 479 then
                      (66, 8188606446561731162762635004266102113722844325705183797742796846069946579756086)
                    else
                      (41, 19797653178643987842096849907604941348521405373321)
              else
                if b < 483 then
                  if b < 481 then
                    (51, 4045089188456822675095202315164015018107813252363485558044230)
                  else
                    if b < 482 then
                      (16, 2917445687054852164)
                    else
                      (20, 1017592532272346409487801)
                else
                  if b < 484 then
                    (25, 350179497790476973700985258006)
                  else
                    if b < 485 then
                      (15, 105911577918047269)
                    else
                      (23, 3552871477472823836982398385)
            else
              if b < 491 then
                if b < 488 then
                  if b < 487 then
                    (27, 235807090412071610025403957957221)
                  else
                    (24, 39698728999821601734926947604)
                else
                  if b < 489 then
                    (39, 66310992193216385228950786373113307575338683832)
                  else
                    if b < 490 then
                      (66, 15333175325286581211889750768878683587326235807558566184409495556023703633090641)
                    else
                      (15, 182340355427296352)
              else
                if b < 494 then
                  if b < 492 then
                    (67, 408496298577130999696208335957024005080400293997961055556327267801441454967358683)
                  else
                    if b < 493 then
                      (11, 9336215725313)
                    else
                      (47, 55813313804131047530039635218201350413458683603299205189)
                else
                  if b < 495 then
                    (57, 34407440845202179108306888489542149294866744796761874241676963612241)
                  else
                    if b < 496 then
                      (16, 2435645102884996706)
                    else
                      (50, 1289744055594143189387640082687315645237562168282565702976731)
          else
            if b < 508 then
              if b < 502 then
                if b < 499 then
                  if b < 498 then
                    (15, 596366154220770897)
                  else
                    (53, 3518979641107412904842920165979372135750172882514619132948044569)
                else
                  if b < 500 then
                    (26, 11219716302659478352575451909561)
                  else
                    if b < 501 then
                      (34, 47572799252028749490597404414530199804809)
                    else
                      (44, 52680960997883343810292589312961328347050186366799289)
              else
                if b < 505 then
                  if b < 503 then
                    (20, 333957246323953780483392)
                  else
                    if b < 504 then
                      (67, 288653148512153504844142889212077185218503405383070275880135392936694011402407352)
                    else
                      (47, 108375303942761665001160485590262667701337770509868360789)
                else
                  if b < 506 then
                    (28, 4050845962771408454851359179004680)
                  else
                    if b < 507 then
                      (56, 13005087567875189844311365837975099538187132063593921958448296119736)
                    else
                      (24, 58643167437219207029761377499)
            else
              if b < 513 then
                if b < 510 then
                  if b < 509 then
                    (42, 48633283500290627555595622103497666439962011858196)
                  else
                    (36, 15139796169580164603970058759228194195262904)
                else
                  if b < 511 then
                    (19, 9874053478227595563366)
                  else
                    if b < 512 then
                      (23, 2561373127293397741426074176)
                    else
                      (36, 17730025546582348187853266270998813820865976)
              else
                if b < 516 then
                  if b < 514 then
                    (25, 994458586187181203147860728584)
                  else
                    if b < 515 then
                      (59, 14354011747104362440602421940386725993900421129190165477222288588277248)
                    else
                      (45, 840989311553591827405145155637245319610883929395973561)
                else
                  if b < 517 then
                    (38, 4220833147412347252210793422945193541781966257)
                  else
                    if b < 518 then
                      (77, 419076319388019579491440845691680083481388686273518334677009553894549045130805146727007782107)
                    else
                      (48, 3424893237296971739392477027184852582393231696691655400329)
    else
      if b < 606 then
        if b < 562 then
          if b < 540 then
            if b < 529 then
              if b < 524 then
                if b < 521 then
                  if b < 520 then
                    (16, 12085371905341672888)
                  else
                    (0, 0)
                else
                  if b < 522 then
                    (12, 49282155890021)
                  else
                    if b < 523 then
                      (16, 9747483782575117669)
                    else
                      (41, 3678987185100434248938838495781981364762355048517)
              else
                if b < 526 then
                  if b < 525 then
                    (15, 920912126020838664)
                  else
                    (32, 44231713736415464715534190475083145984)
                else
                  if b < 527 then
                    (66, 15333175325286581211889750768878683587326235807558566184409495556104199973066308)
                  else
                    if b < 528 then
                      (30, 710631996665802425772344333945556409)
                    else
                      (51, 3342053794093514429545593899764755110633578968038565191378246)
            else
              if b < 534 then
                if b < 531 then
                  if b < 530 then
                    (56, 13945441719703541104435999631167475486115696632629944771700221948005)
                  else
                    (73, 1132028491912531905362364380489374996840897024981425655775359168916961311200772462368017)
                else
                  if b < 532 then
                    (41, 3326732743032637091281392289292890465684691502355)
                  else
                    if b < 533 then
                      (18, 3797398280918789894169)
                    else
                      (19, 50725109112879148019849)
              else
                if b < 537 then
                  if b < 535 then
                    (41, 17055549234399146455397766576245880190037963853240)
                  else
                    if b < 536 then
                      (14, 10251286735769606)
                    else
                      (15, 782936649529189633)
                else
                  if b < 538 then
                    (24, 43542928664505142279170706872)
                  else
                    if b < 539 then
                      (32, 165943166120939482240888671619367587256)
                    else
                      (21, 16305663597231315141807537)
          else
            if b < 551 then
              if b < 545 then
                if b < 542 then
                  if b < 541 then
                    (66, 24995119949711506265468936062935982975517423618904423214325703412917942056144312)
                  else
                    (34, 13705295284968929151465372726141647610880)
                else
                  if b < 543 then
                    (73, 4750897546186267646573613596771154694882628978987342963435075241427305173788268788319451)
                  else
                    if b < 544 then
                      (28, 685607818864635547768248968043078)
                    else
                      (70, 1433221180069424419065414144526428017139244633685605738377175253418289453595319356857)
              else
                if b < 548 then
                  if b < 546 then
                    (46, 6773456496422604062572530349391416731333610656866776404)
                  else
                    if b < 547 then
                      (41, 1865231105701734173077707456576625910528346842181)
                    else
                      (53, 855565771287939693963672038339777308322198045081238382322673216)
                else
                  if b < 549 then
                    (15, 629830846026930969)
                  else
                    if b < 550 then
                      (16, 1715192303904440677)
                    else
                      (44, 80718083189121793704161252987220015529035460533083017)
            else
              if b < 556 then
                if b < 553 then
                  if b < 552 then
                    (16, 9747483782408316260)
                  else
                    (57, 345197053535972608407589181140074028675149986511070729414508139269553)
                else
                  if b < 554 then
                    (36, 19065941636104805601528830892990900218121656)
                  else
                    if b < 555 then
                      (52, 53472860705496230872729502396236080486896338301180509981255189)
                    else
                      (53, 5549640476643456499238602973430804736691798863191597089313279417)
              else
                if b < 559 then
                  if b < 557 then
                    (78, 6675086306021298659837009917496131863164356315601327523636941757421958738346957711397678501297)
                  else
                    if b < 558 then
                      (50, 228611333341720770683042345853753837117581142129352572667184)
                    else
                      (24, 63364098910086681456271183281)
                else
                  if b < 560 then
                    (23, 3574174088640608261103439289)
                  else
                    if b < 561 then
                      (40, 798473282380278615662808399727154560901868178865)
                    else
                      (13, 2923975563961601)
        else
          if b < 584 then
            if b < 573 then
              if b < 567 then
                if b < 564 then
                  if b < 563 then
                    (41, 12405889958679313104357146593203543567301817533659)
                  else
                    (65, 1359136591991655734350845621478846101924126494580057169196102367172430697352632)
                else
                  if b < 565 then
                    (41, 3326732743032637091281392289292890465684622304560)
                  else
                    if b < 566 then
                      (29, 66716884763158216799506863864808022)
                    else
                      (40, 207920796439539818205087018080805801914442735936)
              else
                if b < 570 then
                  if b < 568 then
                    (51, 22272672281261393406636469302931618633951095665479899802521009)
                  else
                    if b < 569 then
                      (43, 4391557912723610568076739727967827670646988141364443)
                    else
                      (50, 783016029674405918110168788462318962367941912009819591560633)
                else
                  if b < 571 then
                    (39, 25233091773176953429626413991272527679316181856)
                  else
                    if b < 572 then
                      (30, 1068898028567937547597578363796088201)
                    else
                      (29, 45708180071247951267107258545472352)
            else
              if b < 578 then
                if b < 575 then
                  if b < 574 then
                    (51, 7102483919192828477516053583643454190475140060223718325712389)
                  else
                    (27, 274891353047902869378148029280281)
                else
                  if b < 576 then
                    (17, 38364896049935500868)
                  else
                    if b < 577 then
                      (38, 2953062150150892236451050118552390368302096688)
                    else
                      (14, 9420399105692436)
              else
                if b < 581 then
                  if b < 579 then
                    (40, 1230239102831988693128101623568660623731028151736)
                  else
                    if b < 580 then
                      (43, 3096510097156621977728896329111190677406806531139120)
                    else
                      (14, 35333753272290745)
                else
                  if b < 582 then
                    (35, 111176441613396243556803337293487847920677)
                  else
                    if b < 583 then
                      (0, 0)
                    else
                      (52, 353169111100752761952499194401727359178816056094564172636900792)
          else
            if b < 595 then
              if b < 589 then
                if b < 586 then
                  if b < 585 then
                    (14, 9366429710960228)
                  else
                    (30, 647614545170907759195699026617771608)
                else
                  if b < 587 then
                    (21, 1542883035609659476428304)
                  else
                    if b < 588 then
                      (62, 233965687946877765074001323988017022511691830559670504522849968809180530275)
                    else
                      (13, 1244087496827221)
              else
                if b < 592 then
                  if b < 590 then
                    (42, 198475683812417476949428868105215363061953694325529)
                  else
                    if b < 591 then
                      (29, 6626632309758424869275726970767190)
                    else
                      (43, 3096510097156621977728896329111191282832309617120801)
                else
                  if b < 593 then
                    (45, 842474197217126345453486537602063954246033276777399515)
                  else
                    if b < 594 then
                      (51, 20466780214111872401665794808787457788127664448757580695621048)
                    else
                      (31, 16599027503856778626026563870086549529)
            else
              if b < 600 then
                if b < 597 then
                  if b < 596 then
                    (8, 280376646)
                  else
                    (47, 289436941565313101482895729443051590388861670739746882779)
                else
                  if b < 598 then
                    (40, 207920796439539818205087018080805590447597953364)
                  else
                    if b < 599 then
                      (16, 10132206668565961480)
                    else
                      (15, 970751949685447561)
              else
                if b < 603 then
                  if b < 601 then
                    (20, 211665221796105580584981)
                  else
                    if b < 602 then
                      (30, 954606571223197870494298009523873025)
                    else
                      (68, 4500348469739434282902832555281406877730476096380603787640395757179244926046588345)
                else
                  if b < 604 then
                    (12, 202137379789569)
                  else
                    if b < 605 then
                      (17, 46679131017523052885)
                    else
                      (12, 206551366854025)
      else
        if b < 649 then
          if b < 627 then
            if b < 616 then
              if b < 611 then
                if b < 608 then
                  if b < 607 then
                    (16, 13676266811140454169)
                  else
                    (42, 275823395505287751404585031090131541999449545169689)
                else
                  if b < 609 then
                    (49, 8011106598470867403854357192651948403750887893239125336676)
                  else
                    if b < 610 then
                      (28, 4046170144791591008791732933876481)
                    else
                      (40, 792676661754042929144525704157076143974754831793)
              else
                if b < 613 then
                  if b < 612 then
                    (66, 4663670313424529579297380943332930775512529247272908435788236160496485914414475)
                  else
                    (20, 967065763926990475251121)
                else
                  if b < 614 then
                    (52, 226125080578407570736939095933998048317997148525274570619749595)
                  else
                    if b < 615 then
                      (58, 897125734194022652537651371274170374618779756685609506153235323441232)
                    else
                      (52, 53472860705496230872729502396236102072071641038894033010713859)
            else
              if b < 621 then
                if b < 618 then
                  if b < 617 then
                    (78, 4583011099613585329757227612637127671416420357806550197310887208221425868258812879702841492699)
                  else
                    (15, 183753016054392165)
                else
                  if b < 619 then
                    (15, 926810616940881153)
                  else
                    if b < 620 then
                      (30, 970023812076913230346941331358931849)
                    else
                      (40, 798430538346641050759941347939560871917844301019)
              else
                if b < 624 then
                  if b < 622 then
                    (30, 1042284813721322501076387208249528933)
                  else
                    if b < 623 then
                      (41, 13871331211044725642981065835809372716737633471921)
                    else
                      (68, 1079586498177081971514095669259428974953553223592210441375121277727578559757046022)
                else
                  if b < 625 then
                    (40, 1173498208545265444572220891025398555878005015771)
                  else
                    if b < 626 then
                      (53, 3593902366236144272770573793658321495001968540817688311653260057)
                    else
                      (16, 11375443227417142529)
          else
            if b < 638 then
              if b < 632 then
                if b < 629 then
                  if b < 628 then
                    (53, 5575553151099393947567911926062076788643581623379287067890866969)
                  else
                    (9, 33166244865)
                else
                  if b < 630 then
                    (43, 1653675902446924819963996667331898568764748575356516)
                  else
                    if b < 631 then
                      (50, 1091311298495244877651296703016096338854572520099069118700425)
                    else
                      (24, 67423062627076316040433520057)
              else
                if b < 635 then
                  if b < 633 then
                    (16, 9747483782161982806)
                  else
                    if b < 634 then
                      (18, 4086837869799167285605)
                    else
                      (14, 52876397942689201)
                else
                  if b < 636 then
                    (8, 3097287433)
                  else
                    if b < 637 then
                      (81, 4442351466528296098770849683418330102474724764415947129210550687226888415051420200728729003058246)
                    else
                      (41, 3039580218768164222224726381468607543661115609187)
            else
              if b < 643 then
                if b < 640 then
                  if b < 639 then
                    (31, 2764482105115290879514919525138392064)
                  else
                    (67, 131017703144987698604202160068257633819565509211282940763884749534754201749193824)
                else
                  if b < 641 then
                    (16, 10937228951156843784)
                  else
                    if b < 642 then
                      (43, 851643582216355095368036426058979959215262302357072)
                    else
                      (51, 12524898784074230933942566563767203727573205660179441022684593)
              else
                if b < 646 then
                  if b < 644 then
                    (23, 2561373119285751031215326469)
                  else
                    if b < 645 then
                      (35, 1109586013163487019234293608481628476165560)
                    else
                      (38, 2647559068718331330110759146875200397036018569)
                else
                  if b < 647 then
                    (14, 11203569569792098)
                  else
                    if b < 648 then
                      (73, 6771755700263206548529238632218029525102747505023932539062820523497264824911918333746057)
                    else
                      (39, 67176053336497652634301382476808819140796108209)
        else
          if b < 671 then
            if b < 660 then
              if b < 654 then
                if b < 651 then
                  if b < 650 then
                    (40, 403729468370831254874022623860326791316220495361)
                  else
                    (17, 46658523926347604309)
                else
                  if b < 652 then
                    (26, 10717471760406082246486834549860)
                  else
                    if b < 653 then
                      (26, 1863216182984320638900244975702)
                    else
                      (24, 11271408983164772822984970566)
              else
                if b < 657 then
                  if b < 655 then
                    (24, 36016685041397509325631935505)
                  else
                    if b < 656 then
                      (85, 352376966004322747011476467211797079825672306225773459279864226817580043150340834820994265169855135841)
                    else
                      (13, 2329555286832742)
                else
                  if b < 658 then
                    (16, 11374839315452910337)
                  else
                    if b < 659 then
                      (40, 1266407860527724413228509205641823687474600532873)
                    else
                      (27, 51282290969791536209078249476196)
            else
              if b < 665 then
                if b < 662 then
                  if b < 661 then
                    (49, 61901881922744142132320493918277287478198452723694889356729)
                  else
                    (28, 472042895523643011829852653307232)
                else
                  if b < 663 then
                    (14, 53133231200776457)
                  else
                    if b < 664 then
                      (27, 260749066854351435974269635910401)
                    else
                      (26, 15904197466738180475722264992520)
              else
                if b < 668 then
                  if b < 666 then
                    (20, 1038195280299813242037512)
                  else
                    if b < 667 then
                      (42, 253009457465512206359317646446295651809924334541705)
                    else
                      (42, 193531881072288873608056020569449455177023191343184)
                else
                  if b < 669 then
                    (17, 235816872653770045321)
                  else
                    if b < 670 then
                      (68, 1079586498177081971514095669259428974953553223592210441375121277765972300203971171)
                    else
                      (13, 507039413478724)
          else
            if b < 682 then
              if b < 676 then
                if b < 673 then
                  if b < 672 then
                    (27, 42182649304287809045651184321892)
                  else
                    (27, 157808214894670265554890444842584)
                else
                  if b < 674 then
                    (48, 5436981709741116643898230314267956259564144514249529511353)
                  else
                    if b < 675 then
                      (20, 584918354098514281260297)
                    else
                      (43, 851643582216355095368036426058979959215264098354257)
              else
                if b < 679 then
                  if b < 677 then
                    (21, 10699660195082597639480601)
                  else
                    if b < 678 then
                      (21, 15524737390416470446253657)
                    else
                      (78, 1187017907935675055197246592636026876687440438866923388430303015903662876483887829828183134790)
                else
                  if b < 680 then
                    (16, 2940048256870278753)
                  else
                    if b < 681 then
                      (16, 10149254785761875521)
                    else
                      (69, 33540532005116850842675752977473954257808770358088432835554495880897075617703810629)
            else
              if b < 687 then
                if b < 684 then
                  if b < 683 then
                    (22, 227641026891286278354371803)
                  else
                    (15, 854432084859017993)
                else
                  if b < 685 then
                    (70, 1060721938785241372142447384767519701552913701085566019631910350474817932735413243321)
                  else
                    if b < 686 then
                      (25, 933648404130490824832481363163)
                    else
                      (24, 6319648897779386773949255764)
              else
                if b < 690 then
                  if b < 688 then
                    (69, 17273383970833311544225530708150863599256851577475367062001940443641256956146361440)
                  else
                    if b < 689 then
                      (25, 1076947150823061810485726825913)
                    else
                      (30, 808964292597977682277117991869351131)
                else
                  if b < 691 then
                    (20, 191197720652353826611812)
                  else
                    if b < 692 then
                      (69, 89387492875382839403340177199991577033712170335888564278989875317899104770383545563)
                    else
                      (19, 36848981401088288294436)

def forwardBlocks : Fin 6 → Nat → Nat
  | 0 => forward0Blocks
  | 1 => forward1Blocks
  | 2 => forward2Blocks
  | 3 => forward3Blocks
  | 4 => forward4Blocks
  | 5 => forward5Blocks


def transitionForward (a : Fin 6) (r : Fin 693) : Fin 693 :=
  Fin.ofNat 693 (((forwardBlocks a) (r.val / 256) >>> (10 * (r.val % 256))) % 1024)

def backwardBlocks : Fin 6 → Nat → Nat
  | 0 => backward0Blocks
  | 1 => backward1Blocks
  | 2 => backward2Blocks
  | 3 => backward3Blocks
  | 4 => backward4Blocks
  | 5 => backward5Blocks


def transitionBackward (a : Fin 6) (r : Fin 693) : Fin 693 :=
  Fin.ofNat 693 (((backwardBlocks a) (r.val / 256) >>> (10 * (r.val % 256))) % 1024)

def factorCode : Fin 6 → Nat → Nat × Nat
  | 0 => factorCode0
  | 1 => factorCode1
  | 2 => factorCode2
  | 3 => factorCode3
  | 4 => factorCode4
  | 5 => factorCode5


end Sporadic.Fischer.Fi23.CentralizerSection.KernelUpperThird
