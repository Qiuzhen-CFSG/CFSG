module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.ElementaryCentralizer.Coverage.Level6
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.ElementaryCentralizer.Coverage.Words

/-!
# Candidate membership of all surviving outer centralizer permutations

Finite witnesses for the centralizer of the specified outer HS involution.
The existing HS order certificate supplies a stabilizer chain. Orbit colors
of its residual groups restrict each successive representative. All finite
identities are checked by Lean's kernel; the generator supplies no trusted facts.

Source: ATLAS HSG1-p100B0; GLS volume 3, Table 5.3m, printed p.274;
Aschbacher–Smith 16.1.5(10), printed p.1172; GLS3 class 2C.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.ElementaryCentralizer.Coverage
open Theory.GroupTheory Sporadic.LeechRelated.HS.OrderCertificate
set_option maxRecDepth 100000
set_option Elab.async false

def kernelCode (i : Fin 1920) : Fin 16 :=
  ⟨(if i.val < 960 then
(if i.val < 480 then
(if i.val < 240 then
(if i.val < 120 then
(if i.val < 60 then
(if i.val < 30 then
(if i.val < 15 then
(if i.val < 7 then
(if i.val < 3 then
(if i.val < 1 then
(0) else
(if i.val < 2 then
(12) else
(14))) else
(if i.val < 5 then
(if i.val < 4 then
(1) else
(0)) else
(if i.val < 6 then
(4) else
(5)))) else
(if i.val < 11 then
(if i.val < 9 then
(if i.val < 8 then
(4) else
(15)) else
(if i.val < 10 then
(10) else
(14))) else
(if i.val < 13 then
(if i.val < 12 then
(14) else
(9)) else
(if i.val < 14 then
(7) else
(1))))) else
(if i.val < 22 then
(if i.val < 18 then
(if i.val < 16 then
(5) else
(if i.val < 17 then
(1) else
(0))) else
(if i.val < 20 then
(if i.val < 19 then
(14) else
(14)) else
(if i.val < 21 then
(6) else
(0)))) else
(if i.val < 26 then
(if i.val < 24 then
(if i.val < 23 then
(9) else
(4)) else
(if i.val < 25 then
(7) else
(10))) else
(if i.val < 28 then
(if i.val < 27 then
(14) else
(7)) else
(if i.val < 29 then
(4) else
(10)))))) else
(if i.val < 45 then
(if i.val < 37 then
(if i.val < 33 then
(if i.val < 31 then
(13) else
(if i.val < 32 then
(5) else
(12))) else
(if i.val < 35 then
(if i.val < 34 then
(13) else
(12)) else
(if i.val < 36 then
(10) else
(5)))) else
(if i.val < 41 then
(if i.val < 39 then
(if i.val < 38 then
(12) else
(12)) else
(if i.val < 40 then
(10) else
(9))) else
(if i.val < 43 then
(if i.val < 42 then
(7) else
(9)) else
(if i.val < 44 then
(15) else
(6))))) else
(if i.val < 52 then
(if i.val < 48 then
(if i.val < 46 then
(1) else
(if i.val < 47 then
(0) else
(4))) else
(if i.val < 50 then
(if i.val < 49 then
(10) else
(14)) else
(if i.val < 51 then
(5) else
(10)))) else
(if i.val < 56 then
(if i.val < 54 then
(if i.val < 53 then
(7) else
(1)) else
(if i.val < 55 then
(1) else
(7))) else
(if i.val < 58 then
(if i.val < 57 then
(6) else
(12)) else
(if i.val < 59 then
(0) else
(1))))))) else
(if i.val < 90 then
(if i.val < 75 then
(if i.val < 67 then
(if i.val < 63 then
(if i.val < 61 then
(3) else
(if i.val < 62 then
(12) else
(1))) else
(if i.val < 65 then
(if i.val < 64 then
(0) else
(1)) else
(if i.val < 66 then
(10) else
(4)))) else
(if i.val < 71 then
(if i.val < 69 then
(if i.val < 68 then
(9) else
(2)) else
(if i.val < 70 then
(11) else
(15))) else
(if i.val < 73 then
(if i.val < 72 then
(2) else
(9)) else
(if i.val < 74 then
(11) else
(2))))) else
(if i.val < 82 then
(if i.val < 78 then
(if i.val < 76 then
(9) else
(if i.val < 77 then
(1) else
(1))) else
(if i.val < 80 then
(if i.val < 79 then
(9) else
(8)) else
(if i.val < 81 then
(12) else
(1)))) else
(if i.val < 86 then
(if i.val < 84 then
(if i.val < 83 then
(12) else
(2)) else
(if i.val < 85 then
(2) else
(5))) else
(if i.val < 88 then
(if i.val < 87 then
(9) else
(10)) else
(if i.val < 89 then
(1) else
(1)))))) else
(if i.val < 105 then
(if i.val < 97 then
(if i.val < 93 then
(if i.val < 91 then
(8) else
(if i.val < 92 then
(0) else
(10))) else
(if i.val < 95 then
(if i.val < 94 then
(8) else
(12)) else
(if i.val < 96 then
(4) else
(10)))) else
(if i.val < 101 then
(if i.val < 99 then
(if i.val < 98 then
(3) else
(11)) else
(if i.val < 100 then
(7) else
(8))) else
(if i.val < 103 then
(if i.val < 102 then
(8) else
(2)) else
(if i.val < 104 then
(12) else
(3))))) else
(if i.val < 112 then
(if i.val < 108 then
(if i.val < 106 then
(6) else
(if i.val < 107 then
(6) else
(2))) else
(if i.val < 110 then
(if i.val < 109 then
(13) else
(5)) else
(if i.val < 111 then
(2) else
(9)))) else
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
(9) else
(12)) else
(if i.val < 115 then
(13) else
(7))) else
(if i.val < 118 then
(if i.val < 117 then
(8) else
(9)) else
(if i.val < 119 then
(0) else
(0)))))))) else
(if i.val < 180 then
(if i.val < 150 then
(if i.val < 135 then
(if i.val < 127 then
(if i.val < 123 then
(if i.val < 121 then
(11) else
(if i.val < 122 then
(10) else
(7))) else
(if i.val < 125 then
(if i.val < 124 then
(5) else
(7)) else
(if i.val < 126 then
(1) else
(14)))) else
(if i.val < 131 then
(if i.val < 129 then
(if i.val < 128 then
(7) else
(14)) else
(if i.val < 130 then
(15) else
(15))) else
(if i.val < 133 then
(if i.val < 132 then
(11) else
(10)) else
(if i.val < 134 then
(10) else
(12))))) else
(if i.val < 142 then
(if i.val < 138 then
(if i.val < 136 then
(12) else
(if i.val < 137 then
(5) else
(5))) else
(if i.val < 140 then
(if i.val < 139 then
(1) else
(4)) else
(if i.val < 141 then
(1) else
(6)))) else
(if i.val < 146 then
(if i.val < 144 then
(if i.val < 143 then
(15) else
(14)) else
(if i.val < 145 then
(5) else
(5))) else
(if i.val < 148 then
(if i.val < 147 then
(11) else
(10)) else
(if i.val < 149 then
(1) else
(1)))))) else
(if i.val < 165 then
(if i.val < 157 then
(if i.val < 153 then
(if i.val < 151 then
(5) else
(if i.val < 152 then
(14) else
(11))) else
(if i.val < 155 then
(if i.val < 154 then
(10) else
(13)) else
(if i.val < 156 then
(7) else
(12)))) else
(if i.val < 161 then
(if i.val < 159 then
(if i.val < 158 then
(5) else
(1)) else
(if i.val < 160 then
(12) else
(2))) else
(if i.val < 163 then
(if i.val < 162 then
(2) else
(4)) else
(if i.val < 164 then
(12) else
(13))))) else
(if i.val < 172 then
(if i.val < 168 then
(if i.val < 166 then
(10) else
(if i.val < 167 then
(11) else
(15))) else
(if i.val < 170 then
(if i.val < 169 then
(14) else
(12)) else
(if i.val < 171 then
(10) else
(2)))) else
(if i.val < 176 then
(if i.val < 174 then
(if i.val < 173 then
(13) else
(11)) else
(if i.val < 175 then
(15) else
(2))) else
(if i.val < 178 then
(if i.val < 177 then
(7) else
(6)) else
(if i.val < 179 then
(1) else
(7))))))) else
(if i.val < 210 then
(if i.val < 195 then
(if i.val < 187 then
(if i.val < 183 then
(if i.val < 181 then
(11) else
(if i.val < 182 then
(9) else
(12))) else
(if i.val < 185 then
(if i.val < 184 then
(13) else
(13)) else
(if i.val < 186 then
(1) else
(3)))) else
(if i.val < 191 then
(if i.val < 189 then
(if i.val < 188 then
(12) else
(12)) else
(if i.val < 190 then
(13) else
(1))) else
(if i.val < 193 then
(if i.val < 192 then
(11) else
(8)) else
(if i.val < 194 then
(7) else
(3))))) else
(if i.val < 202 then
(if i.val < 198 then
(if i.val < 196 then
(7) else
(if i.val < 197 then
(2) else
(3))) else
(if i.val < 200 then
(if i.val < 199 then
(7) else
(3)) else
(if i.val < 201 then
(8) else
(1)))) else
(if i.val < 206 then
(if i.val < 204 then
(if i.val < 203 then
(7) else
(1)) else
(if i.val < 205 then
(10) else
(3))) else
(if i.val < 208 then
(if i.val < 207 then
(10) else
(7)) else
(if i.val < 209 then
(2) else
(4)))))) else
(if i.val < 225 then
(if i.val < 217 then
(if i.val < 213 then
(if i.val < 211 then
(4) else
(if i.val < 212 then
(10) else
(9))) else
(if i.val < 215 then
(if i.val < 214 then
(7) else
(0)) else
(if i.val < 216 then
(8) else
(12)))) else
(if i.val < 221 then
(if i.val < 219 then
(if i.val < 218 then
(12) else
(10)) else
(if i.val < 220 then
(10) else
(0))) else
(if i.val < 223 then
(if i.val < 222 then
(7) else
(1)) else
(if i.val < 224 then
(1) else
(8))))) else
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(9) else
(if i.val < 227 then
(13) else
(9))) else
(if i.val < 230 then
(if i.val < 229 then
(13) else
(3)) else
(if i.val < 231 then
(12) else
(3)))) else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
(8) else
(4)) else
(if i.val < 235 then
(12) else
(10))) else
(if i.val < 238 then
(if i.val < 237 then
(13) else
(4)) else
(if i.val < 239 then
(11) else
(9))))))))) else
(if i.val < 360 then
(if i.val < 300 then
(if i.val < 270 then
(if i.val < 255 then
(if i.val < 247 then
(if i.val < 243 then
(if i.val < 241 then
(5) else
(if i.val < 242 then
(13) else
(9))) else
(if i.val < 245 then
(if i.val < 244 then
(11) else
(0)) else
(if i.val < 246 then
(13) else
(12)))) else
(if i.val < 251 then
(if i.val < 249 then
(if i.val < 248 then
(10) else
(2)) else
(if i.val < 250 then
(11) else
(6))) else
(if i.val < 253 then
(if i.val < 252 then
(11) else
(9)) else
(if i.val < 254 then
(6) else
(0))))) else
(if i.val < 262 then
(if i.val < 258 then
(if i.val < 256 then
(0) else
(if i.val < 257 then
(13) else
(2))) else
(if i.val < 260 then
(if i.val < 259 then
(12) else
(2)) else
(if i.val < 261 then
(12) else
(2)))) else
(if i.val < 266 then
(if i.val < 264 then
(if i.val < 263 then
(0) else
(13)) else
(if i.val < 265 then
(3) else
(5))) else
(if i.val < 268 then
(if i.val < 267 then
(11) else
(5)) else
(if i.val < 269 then
(12) else
(8)))))) else
(if i.val < 285 then
(if i.val < 277 then
(if i.val < 273 then
(if i.val < 271 then
(9) else
(if i.val < 272 then
(8) else
(12))) else
(if i.val < 275 then
(if i.val < 274 then
(8) else
(13)) else
(if i.val < 276 then
(10) else
(8)))) else
(if i.val < 281 then
(if i.val < 279 then
(if i.val < 278 then
(12) else
(10)) else
(if i.val < 280 then
(5) else
(6))) else
(if i.val < 283 then
(if i.val < 282 then
(3) else
(2)) else
(if i.val < 284 then
(2) else
(13))))) else
(if i.val < 292 then
(if i.val < 288 then
(if i.val < 286 then
(13) else
(if i.val < 287 then
(11) else
(11))) else
(if i.val < 290 then
(if i.val < 289 then
(1) else
(6)) else
(if i.val < 291 then
(0) else
(0)))) else
(if i.val < 296 then
(if i.val < 294 then
(if i.val < 293 then
(9) else
(6)) else
(if i.val < 295 then
(2) else
(6))) else
(if i.val < 298 then
(if i.val < 297 then
(9) else
(6)) else
(if i.val < 299 then
(8) else
(1))))))) else
(if i.val < 330 then
(if i.val < 315 then
(if i.val < 307 then
(if i.val < 303 then
(if i.val < 301 then
(12) else
(if i.val < 302 then
(5) else
(14))) else
(if i.val < 305 then
(if i.val < 304 then
(14) else
(2)) else
(if i.val < 306 then
(5) else
(14)))) else
(if i.val < 311 then
(if i.val < 309 then
(if i.val < 308 then
(10) else
(7)) else
(if i.val < 310 then
(6) else
(15))) else
(if i.val < 313 then
(if i.val < 312 then
(6) else
(11)) else
(if i.val < 314 then
(13) else
(15))))) else
(if i.val < 322 then
(if i.val < 318 then
(if i.val < 316 then
(3) else
(if i.val < 317 then
(15) else
(7))) else
(if i.val < 320 then
(if i.val < 319 then
(14) else
(7)) else
(if i.val < 321 then
(11) else
(0)))) else
(if i.val < 326 then
(if i.val < 324 then
(if i.val < 323 then
(10) else
(14)) else
(if i.val < 325 then
(3) else
(6))) else
(if i.val < 328 then
(if i.val < 327 then
(14) else
(13)) else
(if i.val < 329 then
(11) else
(6)))))) else
(if i.val < 345 then
(if i.val < 337 then
(if i.val < 333 then
(if i.val < 331 then
(11) else
(if i.val < 332 then
(5) else
(6))) else
(if i.val < 335 then
(if i.val < 334 then
(6) else
(14)) else
(if i.val < 336 then
(15) else
(5)))) else
(if i.val < 341 then
(if i.val < 339 then
(if i.val < 338 then
(15) else
(15)) else
(if i.val < 340 then
(11) else
(1))) else
(if i.val < 343 then
(if i.val < 342 then
(5) else
(1)) else
(if i.val < 344 then
(4) else
(5))))) else
(if i.val < 352 then
(if i.val < 348 then
(if i.val < 346 then
(13) else
(if i.val < 347 then
(14) else
(2))) else
(if i.val < 350 then
(if i.val < 349 then
(12) else
(13)) else
(if i.val < 351 then
(4) else
(0)))) else
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
(11) else
(6)) else
(if i.val < 355 then
(7) else
(4))) else
(if i.val < 358 then
(if i.val < 357 then
(8) else
(5)) else
(if i.val < 359 then
(5) else
(12)))))))) else
(if i.val < 420 then
(if i.val < 390 then
(if i.val < 375 then
(if i.val < 367 then
(if i.val < 363 then
(if i.val < 361 then
(12) else
(if i.val < 362 then
(10) else
(10))) else
(if i.val < 365 then
(if i.val < 364 then
(4) else
(13)) else
(if i.val < 366 then
(6) else
(9)))) else
(if i.val < 371 then
(if i.val < 369 then
(if i.val < 368 then
(9) else
(2)) else
(if i.val < 370 then
(3) else
(13))) else
(if i.val < 373 then
(if i.val < 372 then
(13) else
(3)) else
(if i.val < 374 then
(5) else
(10))))) else
(if i.val < 382 then
(if i.val < 378 then
(if i.val < 376 then
(7) else
(if i.val < 377 then
(9) else
(13))) else
(if i.val < 380 then
(if i.val < 379 then
(12) else
(13)) else
(if i.val < 381 then
(3) else
(13)))) else
(if i.val < 386 then
(if i.val < 384 then
(if i.val < 383 then
(15) else
(2)) else
(if i.val < 385 then
(9) else
(6))) else
(if i.val < 388 then
(if i.val < 387 then
(15) else
(15)) else
(if i.val < 389 then
(9) else
(6)))))) else
(if i.val < 405 then
(if i.val < 397 then
(if i.val < 393 then
(if i.val < 391 then
(14) else
(if i.val < 392 then
(7) else
(6))) else
(if i.val < 395 then
(if i.val < 394 then
(4) else
(10)) else
(if i.val < 396 then
(2) else
(2)))) else
(if i.val < 401 then
(if i.val < 399 then
(if i.val < 398 then
(2) else
(4)) else
(if i.val < 400 then
(4) else
(5))) else
(if i.val < 403 then
(if i.val < 402 then
(2) else
(7)) else
(if i.val < 404 then
(3) else
(2))))) else
(if i.val < 412 then
(if i.val < 408 then
(if i.val < 406 then
(5) else
(if i.val < 407 then
(3) else
(15))) else
(if i.val < 410 then
(if i.val < 409 then
(15) else
(9)) else
(if i.val < 411 then
(14) else
(15)))) else
(if i.val < 416 then
(if i.val < 414 then
(if i.val < 413 then
(3) else
(7)) else
(if i.val < 415 then
(6) else
(7))) else
(if i.val < 418 then
(if i.val < 417 then
(4) else
(9)) else
(if i.val < 419 then
(4) else
(13))))))) else
(if i.val < 450 then
(if i.val < 435 then
(if i.val < 427 then
(if i.val < 423 then
(if i.val < 421 then
(10) else
(if i.val < 422 then
(11) else
(2))) else
(if i.val < 425 then
(if i.val < 424 then
(11) else
(9)) else
(if i.val < 426 then
(1) else
(0)))) else
(if i.val < 431 then
(if i.val < 429 then
(if i.val < 428 then
(13) else
(3)) else
(if i.val < 430 then
(2) else
(11))) else
(if i.val < 433 then
(if i.val < 432 then
(11) else
(9)) else
(if i.val < 434 then
(12) else
(12))))) else
(if i.val < 442 then
(if i.val < 438 then
(if i.val < 436 then
(8) else
(if i.val < 437 then
(3) else
(15))) else
(if i.val < 440 then
(if i.val < 439 then
(7) else
(8)) else
(if i.val < 441 then
(0) else
(11)))) else
(if i.val < 446 then
(if i.val < 444 then
(if i.val < 443 then
(3) else
(14)) else
(if i.val < 445 then
(3) else
(8))) else
(if i.val < 448 then
(if i.val < 447 then
(3) else
(1)) else
(if i.val < 449 then
(15) else
(8)))))) else
(if i.val < 465 then
(if i.val < 457 then
(if i.val < 453 then
(if i.val < 451 then
(0) else
(if i.val < 452 then
(3) else
(7))) else
(if i.val < 455 then
(if i.val < 454 then
(3) else
(6)) else
(if i.val < 456 then
(13) else
(0)))) else
(if i.val < 461 then
(if i.val < 459 then
(if i.val < 458 then
(2) else
(6)) else
(if i.val < 460 then
(14) else
(3))) else
(if i.val < 463 then
(if i.val < 462 then
(10) else
(2)) else
(if i.val < 464 then
(10) else
(2))))) else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(6) else
(if i.val < 467 then
(8) else
(2))) else
(if i.val < 470 then
(if i.val < 469 then
(6) else
(6)) else
(if i.val < 471 then
(11) else
(8)))) else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
(10) else
(6)) else
(if i.val < 475 then
(11) else
(9))) else
(if i.val < 478 then
(if i.val < 477 then
(5) else
(8)) else
(if i.val < 479 then
(8) else
(1)))))))))) else
(if i.val < 720 then
(if i.val < 600 then
(if i.val < 540 then
(if i.val < 510 then
(if i.val < 495 then
(if i.val < 487 then
(if i.val < 483 then
(if i.val < 481 then
(7) else
(if i.val < 482 then
(9) else
(13))) else
(if i.val < 485 then
(if i.val < 484 then
(13) else
(2)) else
(if i.val < 486 then
(9) else
(12)))) else
(if i.val < 491 then
(if i.val < 489 then
(if i.val < 488 then
(8) else
(15)) else
(if i.val < 490 then
(9) else
(1))) else
(if i.val < 493 then
(if i.val < 492 then
(13) else
(7)) else
(if i.val < 494 then
(12) else
(8))))) else
(if i.val < 502 then
(if i.val < 498 then
(if i.val < 496 then
(0) else
(if i.val < 497 then
(4) else
(5))) else
(if i.val < 500 then
(if i.val < 499 then
(4) else
(13)) else
(if i.val < 501 then
(9) else
(5)))) else
(if i.val < 506 then
(if i.val < 504 then
(if i.val < 503 then
(4) else
(6)) else
(if i.val < 505 then
(15) else
(2))) else
(if i.val < 508 then
(if i.val < 507 then
(6) else
(14)) else
(if i.val < 509 then
(10) else
(14)))))) else
(if i.val < 525 then
(if i.val < 517 then
(if i.val < 513 then
(if i.val < 511 then
(7) else
(if i.val < 512 then
(7) else
(13))) else
(if i.val < 515 then
(if i.val < 514 then
(5) else
(5)) else
(if i.val < 516 then
(12) else
(9)))) else
(if i.val < 521 then
(if i.val < 519 then
(if i.val < 518 then
(9) else
(7)) else
(if i.val < 520 then
(4) else
(7))) else
(if i.val < 523 then
(if i.val < 522 then
(3) else
(6)) else
(if i.val < 524 then
(3) else
(12))))) else
(if i.val < 532 then
(if i.val < 528 then
(if i.val < 526 then
(1) else
(if i.val < 527 then
(4) else
(15))) else
(if i.val < 530 then
(if i.val < 529 then
(4) else
(4)) else
(if i.val < 531 then
(12) else
(13)))) else
(if i.val < 536 then
(if i.val < 534 then
(if i.val < 533 then
(14) else
(12)) else
(if i.val < 535 then
(7) else
(12))) else
(if i.val < 538 then
(if i.val < 537 then
(7) else
(0)) else
(if i.val < 539 then
(15) else
(12))))))) else
(if i.val < 570 then
(if i.val < 555 then
(if i.val < 547 then
(if i.val < 543 then
(if i.val < 541 then
(6) else
(if i.val < 542 then
(0) else
(6))) else
(if i.val < 545 then
(if i.val < 544 then
(7) else
(13)) else
(if i.val < 546 then
(3) else
(15)))) else
(if i.val < 551 then
(if i.val < 549 then
(if i.val < 548 then
(11) else
(12)) else
(if i.val < 550 then
(10) else
(14))) else
(if i.val < 553 then
(if i.val < 552 then
(11) else
(15)) else
(if i.val < 554 then
(0) else
(0))))) else
(if i.val < 562 then
(if i.val < 558 then
(if i.val < 556 then
(4) else
(if i.val < 557 then
(14) else
(7))) else
(if i.val < 560 then
(if i.val < 559 then
(0) else
(15)) else
(if i.val < 561 then
(0) else
(4)))) else
(if i.val < 566 then
(if i.val < 564 then
(if i.val < 563 then
(13) else
(13)) else
(if i.val < 565 then
(14) else
(15))) else
(if i.val < 568 then
(if i.val < 567 then
(14) else
(10)) else
(if i.val < 569 then
(11) else
(13)))))) else
(if i.val < 585 then
(if i.val < 577 then
(if i.val < 573 then
(if i.val < 571 then
(11) else
(if i.val < 572 then
(13) else
(5))) else
(if i.val < 575 then
(if i.val < 574 then
(3) else
(3)) else
(if i.val < 576 then
(13) else
(4)))) else
(if i.val < 581 then
(if i.val < 579 then
(if i.val < 578 then
(4) else
(10)) else
(if i.val < 580 then
(11) else
(14))) else
(if i.val < 583 then
(if i.val < 582 then
(3) else
(12)) else
(if i.val < 584 then
(10) else
(6))))) else
(if i.val < 592 then
(if i.val < 588 then
(if i.val < 586 then
(11) else
(if i.val < 587 then
(4) else
(10))) else
(if i.val < 590 then
(if i.val < 589 then
(5) else
(4)) else
(if i.val < 591 then
(0) else
(4)))) else
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
(12) else
(6)) else
(if i.val < 595 then
(10) else
(11))) else
(if i.val < 598 then
(if i.val < 597 then
(15) else
(6)) else
(if i.val < 599 then
(0) else
(6)))))))) else
(if i.val < 660 then
(if i.val < 630 then
(if i.val < 615 then
(if i.val < 607 then
(if i.val < 603 then
(if i.val < 601 then
(11) else
(if i.val < 602 then
(14) else
(5))) else
(if i.val < 605 then
(if i.val < 604 then
(6) else
(13)) else
(if i.val < 606 then
(7) else
(7)))) else
(if i.val < 611 then
(if i.val < 609 then
(if i.val < 608 then
(3) else
(2)) else
(if i.val < 610 then
(6) else
(8))) else
(if i.val < 613 then
(if i.val < 612 then
(3) else
(13)) else
(if i.val < 614 then
(9) else
(9))))) else
(if i.val < 622 then
(if i.val < 618 then
(if i.val < 616 then
(12) else
(if i.val < 617 then
(14) else
(14))) else
(if i.val < 620 then
(if i.val < 619 then
(15) else
(7)) else
(if i.val < 621 then
(13) else
(6)))) else
(if i.val < 626 then
(if i.val < 624 then
(if i.val < 623 then
(6) else
(4)) else
(if i.val < 625 then
(7) else
(14))) else
(if i.val < 628 then
(if i.val < 627 then
(6) else
(14)) else
(if i.val < 629 then
(4) else
(8)))))) else
(if i.val < 645 then
(if i.val < 637 then
(if i.val < 633 then
(if i.val < 631 then
(5) else
(if i.val < 632 then
(12) else
(5))) else
(if i.val < 635 then
(if i.val < 634 then
(7) else
(3)) else
(if i.val < 636 then
(11) else
(12)))) else
(if i.val < 641 then
(if i.val < 639 then
(if i.val < 638 then
(15) else
(3)) else
(if i.val < 640 then
(14) else
(13))) else
(if i.val < 643 then
(if i.val < 642 then
(2) else
(10)) else
(if i.val < 644 then
(6) else
(6))))) else
(if i.val < 652 then
(if i.val < 648 then
(if i.val < 646 then
(13) else
(if i.val < 647 then
(10) else
(5))) else
(if i.val < 650 then
(if i.val < 649 then
(6) else
(15)) else
(if i.val < 651 then
(7) else
(15)))) else
(if i.val < 656 then
(if i.val < 654 then
(if i.val < 653 then
(3) else
(14)) else
(if i.val < 655 then
(3) else
(13))) else
(if i.val < 658 then
(if i.val < 657 then
(0) else
(13)) else
(if i.val < 659 then
(4) else
(13))))))) else
(if i.val < 690 then
(if i.val < 675 then
(if i.val < 667 then
(if i.val < 663 then
(if i.val < 661 then
(13) else
(if i.val < 662 then
(8) else
(3))) else
(if i.val < 665 then
(if i.val < 664 then
(0) else
(1)) else
(if i.val < 666 then
(5) else
(11)))) else
(if i.val < 671 then
(if i.val < 669 then
(if i.val < 668 then
(1) else
(1)) else
(if i.val < 670 then
(0) else
(9))) else
(if i.val < 673 then
(if i.val < 672 then
(9) else
(8)) else
(if i.val < 674 then
(5) else
(11))))) else
(if i.val < 682 then
(if i.val < 678 then
(if i.val < 676 then
(5) else
(if i.val < 677 then
(5) else
(14))) else
(if i.val < 680 then
(if i.val < 679 then
(4) else
(0)) else
(if i.val < 681 then
(8) else
(8)))) else
(if i.val < 686 then
(if i.val < 684 then
(if i.val < 683 then
(1) else
(0)) else
(if i.val < 685 then
(5) else
(13))) else
(if i.val < 688 then
(if i.val < 687 then
(1) else
(3)) else
(if i.val < 689 then
(0) else
(11)))))) else
(if i.val < 705 then
(if i.val < 697 then
(if i.val < 693 then
(if i.val < 691 then
(12) else
(if i.val < 692 then
(4) else
(11))) else
(if i.val < 695 then
(if i.val < 694 then
(0) else
(2)) else
(if i.val < 696 then
(0) else
(10)))) else
(if i.val < 701 then
(if i.val < 699 then
(if i.val < 698 then
(15) else
(15)) else
(if i.val < 700 then
(11) else
(14))) else
(if i.val < 703 then
(if i.val < 702 then
(10) else
(2)) else
(if i.val < 704 then
(3) else
(9))))) else
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(8) else
(if i.val < 707 then
(8) else
(1))) else
(if i.val < 710 then
(if i.val < 709 then
(10) else
(9)) else
(if i.val < 711 then
(5) else
(8)))) else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
(12) else
(3)) else
(if i.val < 715 then
(0) else
(11))) else
(if i.val < 718 then
(if i.val < 717 then
(11) else
(11)) else
(if i.val < 719 then
(6) else
(2))))))))) else
(if i.val < 840 then
(if i.val < 780 then
(if i.val < 750 then
(if i.val < 735 then
(if i.val < 727 then
(if i.val < 723 then
(if i.val < 721 then
(15) else
(if i.val < 722 then
(9) else
(9))) else
(if i.val < 725 then
(if i.val < 724 then
(15) else
(10)) else
(if i.val < 726 then
(7) else
(8)))) else
(if i.val < 731 then
(if i.val < 729 then
(if i.val < 728 then
(14) else
(10)) else
(if i.val < 730 then
(10) else
(11))) else
(if i.val < 733 then
(if i.val < 732 then
(14) else
(15)) else
(if i.val < 734 then
(0) else
(14))))) else
(if i.val < 742 then
(if i.val < 738 then
(if i.val < 736 then
(0) else
(if i.val < 737 then
(8) else
(14))) else
(if i.val < 740 then
(if i.val < 739 then
(10) else
(15)) else
(if i.val < 741 then
(9) else
(7)))) else
(if i.val < 746 then
(if i.val < 744 then
(if i.val < 743 then
(1) else
(7)) else
(if i.val < 745 then
(3) else
(2))) else
(if i.val < 748 then
(if i.val < 747 then
(2) else
(4)) else
(if i.val < 749 then
(11) else
(4)))))) else
(if i.val < 765 then
(if i.val < 757 then
(if i.val < 753 then
(if i.val < 751 then
(4) else
(if i.val < 752 then
(0) else
(9))) else
(if i.val < 755 then
(if i.val < 754 then
(9) else
(0)) else
(if i.val < 756 then
(4) else
(11)))) else
(if i.val < 761 then
(if i.val < 759 then
(if i.val < 758 then
(3) else
(10)) else
(if i.val < 760 then
(4) else
(14))) else
(if i.val < 763 then
(if i.val < 762 then
(2) else
(15)) else
(if i.val < 764 then
(8) else
(0))))) else
(if i.val < 772 then
(if i.val < 768 then
(if i.val < 766 then
(1) else
(if i.val < 767 then
(4) else
(0))) else
(if i.val < 770 then
(if i.val < 769 then
(7) else
(15)) else
(if i.val < 771 then
(9) else
(11)))) else
(if i.val < 776 then
(if i.val < 774 then
(if i.val < 773 then
(2) else
(11)) else
(if i.val < 775 then
(2) else
(4))) else
(if i.val < 778 then
(if i.val < 777 then
(15) else
(0)) else
(if i.val < 779 then
(2) else
(14))))))) else
(if i.val < 810 then
(if i.val < 795 then
(if i.val < 787 then
(if i.val < 783 then
(if i.val < 781 then
(1) else
(if i.val < 782 then
(3) else
(7))) else
(if i.val < 785 then
(if i.val < 784 then
(14) else
(7)) else
(if i.val < 786 then
(6) else
(1)))) else
(if i.val < 791 then
(if i.val < 789 then
(if i.val < 788 then
(3) else
(11)) else
(if i.val < 790 then
(11) else
(10))) else
(if i.val < 793 then
(if i.val < 792 then
(13) else
(2)) else
(if i.val < 794 then
(14) else
(6))))) else
(if i.val < 802 then
(if i.val < 798 then
(if i.val < 796 then
(0) else
(if i.val < 797 then
(2) else
(9))) else
(if i.val < 800 then
(if i.val < 799 then
(13) else
(13)) else
(if i.val < 801 then
(7) else
(3)))) else
(if i.val < 806 then
(if i.val < 804 then
(if i.val < 803 then
(2) else
(3)) else
(if i.val < 805 then
(7) else
(9))) else
(if i.val < 808 then
(if i.val < 807 then
(6) else
(9)) else
(if i.val < 809 then
(2) else
(10)))))) else
(if i.val < 825 then
(if i.val < 817 then
(if i.val < 813 then
(if i.val < 811 then
(3) else
(if i.val < 812 then
(13) else
(1))) else
(if i.val < 815 then
(if i.val < 814 then
(7) else
(11)) else
(if i.val < 816 then
(6) else
(9)))) else
(if i.val < 821 then
(if i.val < 819 then
(if i.val < 818 then
(13) else
(0)) else
(if i.val < 820 then
(0) else
(8))) else
(if i.val < 823 then
(if i.val < 822 then
(9) else
(13)) else
(if i.val < 824 then
(9) else
(14))))) else
(if i.val < 832 then
(if i.val < 828 then
(if i.val < 826 then
(8) else
(if i.val < 827 then
(14) else
(0))) else
(if i.val < 830 then
(if i.val < 829 then
(11) else
(2)) else
(if i.val < 831 then
(13) else
(11)))) else
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
(0) else
(6)) else
(if i.val < 835 then
(0) else
(6))) else
(if i.val < 838 then
(if i.val < 837 then
(11) else
(9)) else
(if i.val < 839 then
(7) else
(6)))))))) else
(if i.val < 900 then
(if i.val < 870 then
(if i.val < 855 then
(if i.val < 847 then
(if i.val < 843 then
(if i.val < 841 then
(3) else
(if i.val < 842 then
(12) else
(8))) else
(if i.val < 845 then
(if i.val < 844 then
(12) else
(15)) else
(if i.val < 846 then
(2) else
(0)))) else
(if i.val < 851 then
(if i.val < 849 then
(if i.val < 848 then
(6) else
(2)) else
(if i.val < 850 then
(3) else
(2))) else
(if i.val < 853 then
(if i.val < 852 then
(6) else
(15)) else
(if i.val < 854 then
(1) else
(3))))) else
(if i.val < 862 then
(if i.val < 858 then
(if i.val < 856 then
(7) else
(if i.val < 857 then
(10) else
(6))) else
(if i.val < 860 then
(if i.val < 859 then
(0) else
(7)) else
(if i.val < 861 then
(1) else
(7)))) else
(if i.val < 866 then
(if i.val < 864 then
(if i.val < 863 then
(7) else
(1)) else
(if i.val < 865 then
(6) else
(7))) else
(if i.val < 868 then
(if i.val < 867 then
(0) else
(2)) else
(if i.val < 869 then
(10) else
(10)))))) else
(if i.val < 885 then
(if i.val < 877 then
(if i.val < 873 then
(if i.val < 871 then
(12) else
(if i.val < 872 then
(11) else
(12))) else
(if i.val < 875 then
(if i.val < 874 then
(3) else
(11)) else
(if i.val < 876 then
(2) else
(12)))) else
(if i.val < 881 then
(if i.val < 879 then
(if i.val < 878 then
(8) else
(8)) else
(if i.val < 880 then
(9) else
(1))) else
(if i.val < 883 then
(if i.val < 882 then
(15) else
(9)) else
(if i.val < 884 then
(15) else
(8))))) else
(if i.val < 892 then
(if i.val < 888 then
(if i.val < 886 then
(6) else
(if i.val < 887 then
(7) else
(10))) else
(if i.val < 890 then
(if i.val < 889 then
(8) else
(8)) else
(if i.val < 891 then
(7) else
(6)))) else
(if i.val < 896 then
(if i.val < 894 then
(if i.val < 893 then
(1) else
(8)) else
(if i.val < 895 then
(1) else
(12))) else
(if i.val < 898 then
(if i.val < 897 then
(12) else
(10)) else
(if i.val < 899 then
(10) else
(3))))))) else
(if i.val < 930 then
(if i.val < 915 then
(if i.val < 907 then
(if i.val < 903 then
(if i.val < 901 then
(0) else
(if i.val < 902 then
(15) else
(9))) else
(if i.val < 905 then
(if i.val < 904 then
(9) else
(0)) else
(if i.val < 906 then
(15) else
(11)))) else
(if i.val < 911 then
(if i.val < 909 then
(if i.val < 908 then
(15) else
(4)) else
(if i.val < 910 then
(5) else
(9))) else
(if i.val < 913 then
(if i.val < 912 then
(11) else
(5)) else
(if i.val < 914 then
(1) else
(4))))) else
(if i.val < 922 then
(if i.val < 918 then
(if i.val < 916 then
(3) else
(if i.val < 917 then
(15) else
(2))) else
(if i.val < 920 then
(if i.val < 919 then
(2) else
(11)) else
(if i.val < 921 then
(1) else
(5)))) else
(if i.val < 926 then
(if i.val < 924 then
(if i.val < 923 then
(12) else
(3)) else
(if i.val < 925 then
(1) else
(15))) else
(if i.val < 928 then
(if i.val < 927 then
(0) else
(8)) else
(if i.val < 929 then
(9) else
(4)))))) else
(if i.val < 945 then
(if i.val < 937 then
(if i.val < 933 then
(if i.val < 931 then
(5) else
(if i.val < 932 then
(3) else
(4))) else
(if i.val < 935 then
(if i.val < 934 then
(2) else
(2)) else
(if i.val < 936 then
(4) else
(11)))) else
(if i.val < 941 then
(if i.val < 939 then
(if i.val < 938 then
(4) else
(11)) else
(if i.val < 940 then
(5) else
(12))) else
(if i.val < 943 then
(if i.val < 942 then
(0) else
(4)) else
(if i.val < 944 then
(2) else
(11))))) else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(10) else
(if i.val < 947 then
(11) else
(15))) else
(if i.val < 950 then
(if i.val < 949 then
(0) else
(1)) else
(if i.val < 951 then
(1) else
(5)))) else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
(9) else
(8)) else
(if i.val < 955 then
(9) else
(15))) else
(if i.val < 958 then
(if i.val < 957 then
(10) else
(12)) else
(if i.val < 959 then
(12) else
(2))))))))))) else
(if i.val < 1440 then
(if i.val < 1200 then
(if i.val < 1080 then
(if i.val < 1020 then
(if i.val < 990 then
(if i.val < 975 then
(if i.val < 967 then
(if i.val < 963 then
(if i.val < 961 then
(4) else
(if i.val < 962 then
(2) else
(6))) else
(if i.val < 965 then
(if i.val < 964 then
(11) else
(2)) else
(if i.val < 966 then
(4) else
(3)))) else
(if i.val < 971 then
(if i.val < 969 then
(if i.val < 968 then
(14) else
(3)) else
(if i.val < 970 then
(12) else
(2))) else
(if i.val < 973 then
(if i.val < 972 then
(12) else
(12)) else
(if i.val < 974 then
(5) else
(5))))) else
(if i.val < 982 then
(if i.val < 978 then
(if i.val < 976 then
(8) else
(if i.val < 977 then
(14) else
(2))) else
(if i.val < 980 then
(if i.val < 979 then
(3) else
(12)) else
(if i.val < 981 then
(8) else
(14)))) else
(if i.val < 986 then
(if i.val < 984 then
(if i.val < 983 then
(14) else
(7)) else
(if i.val < 985 then
(15) else
(14))) else
(if i.val < 988 then
(if i.val < 987 then
(8) else
(14)) else
(if i.val < 989 then
(5) else
(3)))))) else
(if i.val < 1005 then
(if i.val < 997 then
(if i.val < 993 then
(if i.val < 991 then
(5) else
(if i.val < 992 then
(3) else
(4))) else
(if i.val < 995 then
(if i.val < 994 then
(3) else
(6)) else
(if i.val < 996 then
(2) else
(12)))) else
(if i.val < 1001 then
(if i.val < 999 then
(if i.val < 998 then
(12) else
(13)) else
(if i.val < 1000 then
(8) else
(13))) else
(if i.val < 1003 then
(if i.val < 1002 then
(5) else
(11)) else
(if i.val < 1004 then
(11) else
(7))))) else
(if i.val < 1012 then
(if i.val < 1008 then
(if i.val < 1006 then
(12) else
(if i.val < 1007 then
(8) else
(8))) else
(if i.val < 1010 then
(if i.val < 1009 then
(7) else
(15)) else
(if i.val < 1011 then
(8) else
(6)))) else
(if i.val < 1016 then
(if i.val < 1014 then
(if i.val < 1013 then
(2) else
(6)) else
(if i.val < 1015 then
(7) else
(6))) else
(if i.val < 1018 then
(if i.val < 1017 then
(3) else
(11)) else
(if i.val < 1019 then
(7) else
(5))))))) else
(if i.val < 1050 then
(if i.val < 1035 then
(if i.val < 1027 then
(if i.val < 1023 then
(if i.val < 1021 then
(6) else
(if i.val < 1022 then
(15) else
(15))) else
(if i.val < 1025 then
(if i.val < 1024 then
(7) else
(8)) else
(if i.val < 1026 then
(8) else
(13)))) else
(if i.val < 1031 then
(if i.val < 1029 then
(if i.val < 1028 then
(12) else
(7)) else
(if i.val < 1030 then
(12) else
(7))) else
(if i.val < 1033 then
(if i.val < 1032 then
(5) else
(9)) else
(if i.val < 1034 then
(2) else
(3))))) else
(if i.val < 1042 then
(if i.val < 1038 then
(if i.val < 1036 then
(7) else
(if i.val < 1037 then
(13) else
(9))) else
(if i.val < 1040 then
(if i.val < 1039 then
(5) else
(4)) else
(if i.val < 1041 then
(12) else
(1)))) else
(if i.val < 1046 then
(if i.val < 1044 then
(if i.val < 1043 then
(5) else
(12)) else
(if i.val < 1045 then
(3) else
(7))) else
(if i.val < 1048 then
(if i.val < 1047 then
(11) else
(12)) else
(if i.val < 1049 then
(12) else
(4)))))) else
(if i.val < 1065 then
(if i.val < 1057 then
(if i.val < 1053 then
(if i.val < 1051 then
(11) else
(if i.val < 1052 then
(7) else
(13))) else
(if i.val < 1055 then
(if i.val < 1054 then
(15) else
(14)) else
(if i.val < 1056 then
(2) else
(15)))) else
(if i.val < 1061 then
(if i.val < 1059 then
(if i.val < 1058 then
(2) else
(12)) else
(if i.val < 1060 then
(2) else
(7))) else
(if i.val < 1063 then
(if i.val < 1062 then
(14) else
(6)) else
(if i.val < 1064 then
(14) else
(10))))) else
(if i.val < 1072 then
(if i.val < 1068 then
(if i.val < 1066 then
(7) else
(if i.val < 1067 then
(4) else
(15))) else
(if i.val < 1070 then
(if i.val < 1069 then
(14) else
(6)) else
(if i.val < 1071 then
(15) else
(15)))) else
(if i.val < 1076 then
(if i.val < 1074 then
(if i.val < 1073 then
(2) else
(12)) else
(if i.val < 1075 then
(6) else
(6))) else
(if i.val < 1078 then
(if i.val < 1077 then
(6) else
(2)) else
(if i.val < 1079 then
(10) else
(4)))))))) else
(if i.val < 1140 then
(if i.val < 1110 then
(if i.val < 1095 then
(if i.val < 1087 then
(if i.val < 1083 then
(if i.val < 1081 then
(3) else
(if i.val < 1082 then
(13) else
(11))) else
(if i.val < 1085 then
(if i.val < 1084 then
(13) else
(8)) else
(if i.val < 1086 then
(8) else
(14)))) else
(if i.val < 1091 then
(if i.val < 1089 then
(if i.val < 1088 then
(1) else
(5)) else
(if i.val < 1090 then
(2) else
(0))) else
(if i.val < 1093 then
(if i.val < 1092 then
(4) else
(4)) else
(if i.val < 1094 then
(5) else
(10))))) else
(if i.val < 1102 then
(if i.val < 1098 then
(if i.val < 1096 then
(10) else
(if i.val < 1097 then
(10) else
(3))) else
(if i.val < 1100 then
(if i.val < 1099 then
(14) else
(3)) else
(if i.val < 1101 then
(5) else
(3)))) else
(if i.val < 1106 then
(if i.val < 1104 then
(if i.val < 1103 then
(5) else
(3)) else
(if i.val < 1105 then
(4) else
(5))) else
(if i.val < 1108 then
(if i.val < 1107 then
(10) else
(8)) else
(if i.val < 1109 then
(10) else
(14)))))) else
(if i.val < 1125 then
(if i.val < 1117 then
(if i.val < 1113 then
(if i.val < 1111 then
(1) else
(if i.val < 1112 then
(14) else
(4))) else
(if i.val < 1115 then
(if i.val < 1114 then
(2) else
(8)) else
(if i.val < 1116 then
(5) else
(4)))) else
(if i.val < 1121 then
(if i.val < 1119 then
(if i.val < 1118 then
(2) else
(0)) else
(if i.val < 1120 then
(13) else
(0))) else
(if i.val < 1123 then
(if i.val < 1122 then
(0) else
(1)) else
(if i.val < 1124 then
(4) else
(10))))) else
(if i.val < 1132 then
(if i.val < 1128 then
(if i.val < 1126 then
(10) else
(if i.val < 1127 then
(14) else
(11))) else
(if i.val < 1130 then
(if i.val < 1129 then
(14) else
(8)) else
(if i.val < 1131 then
(8) else
(9)))) else
(if i.val < 1136 then
(if i.val < 1134 then
(if i.val < 1133 then
(9) else
(0)) else
(if i.val < 1135 then
(14) else
(1))) else
(if i.val < 1138 then
(if i.val < 1137 then
(3) else
(1)) else
(if i.val < 1139 then
(5) else
(13))))))) else
(if i.val < 1170 then
(if i.val < 1155 then
(if i.val < 1147 then
(if i.val < 1143 then
(if i.val < 1141 then
(0) else
(if i.val < 1142 then
(15) else
(7))) else
(if i.val < 1145 then
(if i.val < 1144 then
(11) else
(2)) else
(if i.val < 1146 then
(10) else
(3)))) else
(if i.val < 1151 then
(if i.val < 1149 then
(if i.val < 1148 then
(3) else
(14)) else
(if i.val < 1150 then
(2) else
(3))) else
(if i.val < 1153 then
(if i.val < 1152 then
(1) else
(14)) else
(if i.val < 1154 then
(0) else
(10))))) else
(if i.val < 1162 then
(if i.val < 1158 then
(if i.val < 1156 then
(10) else
(if i.val < 1157 then
(15) else
(5))) else
(if i.val < 1160 then
(if i.val < 1159 then
(11) else
(14)) else
(if i.val < 1161 then
(8) else
(0)))) else
(if i.val < 1166 then
(if i.val < 1164 then
(if i.val < 1163 then
(11) else
(7)) else
(if i.val < 1165 then
(9) else
(11))) else
(if i.val < 1168 then
(if i.val < 1167 then
(0) else
(11)) else
(if i.val < 1169 then
(3) else
(10)))))) else
(if i.val < 1185 then
(if i.val < 1177 then
(if i.val < 1173 then
(if i.val < 1171 then
(3) else
(if i.val < 1172 then
(11) else
(10))) else
(if i.val < 1175 then
(if i.val < 1174 then
(2) else
(2)) else
(if i.val < 1176 then
(11) else
(9)))) else
(if i.val < 1181 then
(if i.val < 1179 then
(if i.val < 1178 then
(1) else
(8)) else
(if i.val < 1180 then
(5) else
(0))) else
(if i.val < 1183 then
(if i.val < 1182 then
(13) else
(0)) else
(if i.val < 1184 then
(9) else
(0))))) else
(if i.val < 1192 then
(if i.val < 1188 then
(if i.val < 1186 then
(3) else
(if i.val < 1187 then
(14) else
(14))) else
(if i.val < 1190 then
(if i.val < 1189 then
(0) else
(1)) else
(if i.val < 1191 then
(4) else
(4)))) else
(if i.val < 1196 then
(if i.val < 1194 then
(if i.val < 1193 then
(14) else
(10)) else
(if i.val < 1195 then
(8) else
(6))) else
(if i.val < 1198 then
(if i.val < 1197 then
(6) else
(11)) else
(if i.val < 1199 then
(8) else
(3))))))))) else
(if i.val < 1320 then
(if i.val < 1260 then
(if i.val < 1230 then
(if i.val < 1215 then
(if i.val < 1207 then
(if i.val < 1203 then
(if i.val < 1201 then
(11) else
(if i.val < 1202 then
(2) else
(11))) else
(if i.val < 1205 then
(if i.val < 1204 then
(3) else
(13)) else
(if i.val < 1206 then
(8) else
(9)))) else
(if i.val < 1211 then
(if i.val < 1209 then
(if i.val < 1208 then
(13) else
(14)) else
(if i.val < 1210 then
(6) else
(9))) else
(if i.val < 1213 then
(if i.val < 1212 then
(2) else
(1)) else
(if i.val < 1214 then
(0) else
(8))))) else
(if i.val < 1222 then
(if i.val < 1218 then
(if i.val < 1216 then
(12) else
(if i.val < 1217 then
(7) else
(12))) else
(if i.val < 1220 then
(if i.val < 1219 then
(2) else
(6)) else
(if i.val < 1221 then
(4) else
(9)))) else
(if i.val < 1226 then
(if i.val < 1224 then
(if i.val < 1223 then
(0) else
(9)) else
(if i.val < 1225 then
(11) else
(8))) else
(if i.val < 1228 then
(if i.val < 1227 then
(10) else
(7)) else
(if i.val < 1229 then
(14) else
(1)))))) else
(if i.val < 1245 then
(if i.val < 1237 then
(if i.val < 1233 then
(if i.val < 1231 then
(9) else
(if i.val < 1232 then
(2) else
(0))) else
(if i.val < 1235 then
(if i.val < 1234 then
(2) else
(9)) else
(if i.val < 1236 then
(2) else
(10)))) else
(if i.val < 1241 then
(if i.val < 1239 then
(if i.val < 1238 then
(2) else
(10)) else
(if i.val < 1240 then
(3) else
(7))) else
(if i.val < 1243 then
(if i.val < 1242 then
(3) else
(9)) else
(if i.val < 1244 then
(3) else
(10))))) else
(if i.val < 1252 then
(if i.val < 1248 then
(if i.val < 1246 then
(15) else
(if i.val < 1247 then
(1) else
(2))) else
(if i.val < 1250 then
(if i.val < 1249 then
(3) else
(15)) else
(if i.val < 1251 then
(7) else
(1)))) else
(if i.val < 1256 then
(if i.val < 1254 then
(if i.val < 1253 then
(7) else
(9)) else
(if i.val < 1255 then
(10) else
(7))) else
(if i.val < 1258 then
(if i.val < 1257 then
(10) else
(10)) else
(if i.val < 1259 then
(11) else
(3))))))) else
(if i.val < 1290 then
(if i.val < 1275 then
(if i.val < 1267 then
(if i.val < 1263 then
(if i.val < 1261 then
(6) else
(if i.val < 1262 then
(0) else
(14))) else
(if i.val < 1265 then
(if i.val < 1264 then
(0) else
(0)) else
(if i.val < 1266 then
(14) else
(8)))) else
(if i.val < 1271 then
(if i.val < 1269 then
(if i.val < 1268 then
(12) else
(13)) else
(if i.val < 1270 then
(0) else
(9))) else
(if i.val < 1273 then
(if i.val < 1272 then
(15) else
(5)) else
(if i.val < 1274 then
(9) else
(8))))) else
(if i.val < 1282 then
(if i.val < 1278 then
(if i.val < 1276 then
(7) else
(if i.val < 1277 then
(7) else
(8))) else
(if i.val < 1280 then
(if i.val < 1279 then
(7) else
(9)) else
(if i.val < 1281 then
(5) else
(4)))) else
(if i.val < 1286 then
(if i.val < 1284 then
(if i.val < 1283 then
(5) else
(3)) else
(if i.val < 1285 then
(14) else
(8))) else
(if i.val < 1288 then
(if i.val < 1287 then
(14) else
(8)) else
(if i.val < 1289 then
(8) else
(5)))))) else
(if i.val < 1305 then
(if i.val < 1297 then
(if i.val < 1293 then
(if i.val < 1291 then
(9) else
(if i.val < 1292 then
(15) else
(12))) else
(if i.val < 1295 then
(if i.val < 1294 then
(3) else
(5)) else
(if i.val < 1296 then
(5) else
(8)))) else
(if i.val < 1301 then
(if i.val < 1299 then
(if i.val < 1298 then
(15) else
(9)) else
(if i.val < 1300 then
(13) else
(3))) else
(if i.val < 1303 then
(if i.val < 1302 then
(7) else
(14)) else
(if i.val < 1304 then
(14) else
(6))))) else
(if i.val < 1312 then
(if i.val < 1308 then
(if i.val < 1306 then
(7) else
(if i.val < 1307 then
(7) else
(3))) else
(if i.val < 1310 then
(if i.val < 1309 then
(12) else
(13)) else
(if i.val < 1311 then
(13) else
(9)))) else
(if i.val < 1316 then
(if i.val < 1314 then
(if i.val < 1313 then
(3) else
(12)) else
(if i.val < 1315 then
(3) else
(7))) else
(if i.val < 1318 then
(if i.val < 1317 then
(12) else
(3)) else
(if i.val < 1319 then
(4) else
(13)))))))) else
(if i.val < 1380 then
(if i.val < 1350 then
(if i.val < 1335 then
(if i.val < 1327 then
(if i.val < 1323 then
(if i.val < 1321 then
(0) else
(if i.val < 1322 then
(9) else
(1))) else
(if i.val < 1325 then
(if i.val < 1324 then
(9) else
(4)) else
(if i.val < 1326 then
(0) else
(12)))) else
(if i.val < 1331 then
(if i.val < 1329 then
(if i.val < 1328 then
(2) else
(4)) else
(if i.val < 1330 then
(10) else
(4))) else
(if i.val < 1333 then
(if i.val < 1332 then
(9) else
(11)) else
(if i.val < 1334 then
(9) else
(8))))) else
(if i.val < 1342 then
(if i.val < 1338 then
(if i.val < 1336 then
(4) else
(if i.val < 1337 then
(3) else
(10))) else
(if i.val < 1340 then
(if i.val < 1339 then
(10) else
(7)) else
(if i.val < 1341 then
(10) else
(1)))) else
(if i.val < 1346 then
(if i.val < 1344 then
(if i.val < 1343 then
(1) else
(3)) else
(if i.val < 1345 then
(10) else
(0))) else
(if i.val < 1348 then
(if i.val < 1347 then
(4) else
(0)) else
(if i.val < 1349 then
(1) else
(5)))))) else
(if i.val < 1365 then
(if i.val < 1357 then
(if i.val < 1353 then
(if i.val < 1351 then
(13) else
(if i.val < 1352 then
(10) else
(15))) else
(if i.val < 1355 then
(if i.val < 1354 then
(3) else
(11)) else
(if i.val < 1356 then
(2) else
(1)))) else
(if i.val < 1361 then
(if i.val < 1359 then
(if i.val < 1358 then
(0) else
(8)) else
(if i.val < 1360 then
(8) else
(1))) else
(if i.val < 1363 then
(if i.val < 1362 then
(2) else
(12)) else
(if i.val < 1364 then
(9) else
(2))))) else
(if i.val < 1372 then
(if i.val < 1368 then
(if i.val < 1366 then
(13) else
(if i.val < 1367 then
(10) else
(1))) else
(if i.val < 1370 then
(if i.val < 1369 then
(10) else
(14)) else
(if i.val < 1371 then
(11) else
(14)))) else
(if i.val < 1376 then
(if i.val < 1374 then
(if i.val < 1373 then
(1) else
(15)) else
(if i.val < 1375 then
(5) else
(4))) else
(if i.val < 1378 then
(if i.val < 1377 then
(9) else
(9)) else
(if i.val < 1379 then
(0) else
(8))))))) else
(if i.val < 1410 then
(if i.val < 1395 then
(if i.val < 1387 then
(if i.val < 1383 then
(if i.val < 1381 then
(8) else
(if i.val < 1382 then
(14) else
(6))) else
(if i.val < 1385 then
(if i.val < 1384 then
(10) else
(1)) else
(if i.val < 1386 then
(3) else
(14)))) else
(if i.val < 1391 then
(if i.val < 1389 then
(if i.val < 1388 then
(15) else
(6)) else
(if i.val < 1390 then
(11) else
(15))) else
(if i.val < 1393 then
(if i.val < 1392 then
(9) else
(5)) else
(if i.val < 1394 then
(8) else
(8))))) else
(if i.val < 1402 then
(if i.val < 1398 then
(if i.val < 1396 then
(1) else
(if i.val < 1397 then
(11) else
(15))) else
(if i.val < 1400 then
(if i.val < 1399 then
(9) else
(14)) else
(if i.val < 1401 then
(8) else
(6)))) else
(if i.val < 1406 then
(if i.val < 1404 then
(if i.val < 1403 then
(0) else
(6)) else
(if i.val < 1405 then
(0) else
(5))) else
(if i.val < 1408 then
(if i.val < 1407 then
(1) else
(1)) else
(if i.val < 1409 then
(1) else
(1)))))) else
(if i.val < 1425 then
(if i.val < 1417 then
(if i.val < 1413 then
(if i.val < 1411 then
(14) else
(if i.val < 1412 then
(15) else
(1))) else
(if i.val < 1415 then
(if i.val < 1414 then
(5) else
(5)) else
(if i.val < 1416 then
(10) else
(5)))) else
(if i.val < 1421 then
(if i.val < 1419 then
(if i.val < 1418 then
(11) else
(10)) else
(if i.val < 1420 then
(2) else
(5))) else
(if i.val < 1423 then
(if i.val < 1422 then
(3) else
(10)) else
(if i.val < 1424 then
(3) else
(11))))) else
(if i.val < 1432 then
(if i.val < 1428 then
(if i.val < 1426 then
(10) else
(if i.val < 1427 then
(15) else
(11))) else
(if i.val < 1430 then
(if i.val < 1429 then
(8) else
(8)) else
(if i.val < 1431 then
(14) else
(14)))) else
(if i.val < 1436 then
(if i.val < 1434 then
(if i.val < 1433 then
(15) else
(14)) else
(if i.val < 1435 then
(9) else
(3))) else
(if i.val < 1438 then
(if i.val < 1437 then
(2) else
(3)) else
(if i.val < 1439 then
(3) else
(5)))))))))) else
(if i.val < 1680 then
(if i.val < 1560 then
(if i.val < 1500 then
(if i.val < 1470 then
(if i.val < 1455 then
(if i.val < 1447 then
(if i.val < 1443 then
(if i.val < 1441 then
(9) else
(if i.val < 1442 then
(3) else
(13))) else
(if i.val < 1445 then
(if i.val < 1444 then
(8) else
(5)) else
(if i.val < 1446 then
(12) else
(5)))) else
(if i.val < 1451 then
(if i.val < 1449 then
(if i.val < 1448 then
(13) else
(14)) else
(if i.val < 1450 then
(8) else
(12))) else
(if i.val < 1453 then
(if i.val < 1452 then
(0) else
(13)) else
(if i.val < 1454 then
(14) else
(0))))) else
(if i.val < 1462 then
(if i.val < 1458 then
(if i.val < 1456 then
(5) else
(if i.val < 1457 then
(14) else
(6))) else
(if i.val < 1460 then
(if i.val < 1459 then
(13) else
(1)) else
(if i.val < 1461 then
(13) else
(4)))) else
(if i.val < 1466 then
(if i.val < 1464 then
(if i.val < 1463 then
(12) else
(4)) else
(if i.val < 1465 then
(8) else
(5))) else
(if i.val < 1468 then
(if i.val < 1467 then
(4) else
(7)) else
(if i.val < 1469 then
(5) else
(8)))))) else
(if i.val < 1485 then
(if i.val < 1477 then
(if i.val < 1473 then
(if i.val < 1471 then
(6) else
(if i.val < 1472 then
(8) else
(2))) else
(if i.val < 1475 then
(if i.val < 1474 then
(2) else
(7)) else
(if i.val < 1476 then
(6) else
(5)))) else
(if i.val < 1481 then
(if i.val < 1479 then
(if i.val < 1478 then
(12) else
(4)) else
(if i.val < 1480 then
(5) else
(12))) else
(if i.val < 1483 then
(if i.val < 1482 then
(6) else
(12)) else
(if i.val < 1484 then
(8) else
(6))))) else
(if i.val < 1492 then
(if i.val < 1488 then
(if i.val < 1486 then
(15) else
(if i.val < 1487 then
(13) else
(13))) else
(if i.val < 1490 then
(if i.val < 1489 then
(6) else
(1)) else
(if i.val < 1491 then
(9) else
(13)))) else
(if i.val < 1496 then
(if i.val < 1494 then
(if i.val < 1493 then
(3) else
(14)) else
(if i.val < 1495 then
(7) else
(15))) else
(if i.val < 1498 then
(if i.val < 1497 then
(6) else
(6)) else
(if i.val < 1499 then
(15) else
(11))))))) else
(if i.val < 1530 then
(if i.val < 1515 then
(if i.val < 1507 then
(if i.val < 1503 then
(if i.val < 1501 then
(4) else
(if i.val < 1502 then
(2) else
(13))) else
(if i.val < 1505 then
(if i.val < 1504 then
(4) else
(15)) else
(if i.val < 1506 then
(15) else
(6)))) else
(if i.val < 1511 then
(if i.val < 1509 then
(if i.val < 1508 then
(2) else
(7)) else
(if i.val < 1510 then
(2) else
(6))) else
(if i.val < 1513 then
(if i.val < 1512 then
(6) else
(15)) else
(if i.val < 1514 then
(9) else
(1))))) else
(if i.val < 1522 then
(if i.val < 1518 then
(if i.val < 1516 then
(13) else
(if i.val < 1517 then
(1) else
(1))) else
(if i.val < 1520 then
(if i.val < 1519 then
(15) else
(7)) else
(if i.val < 1521 then
(14) else
(1)))) else
(if i.val < 1526 then
(if i.val < 1524 then
(if i.val < 1523 then
(12) else
(8)) else
(if i.val < 1525 then
(8) else
(9))) else
(if i.val < 1528 then
(if i.val < 1527 then
(4) else
(6)) else
(if i.val < 1529 then
(12) else
(12)))))) else
(if i.val < 1545 then
(if i.val < 1537 then
(if i.val < 1533 then
(if i.val < 1531 then
(8) else
(if i.val < 1532 then
(13) else
(4))) else
(if i.val < 1535 then
(if i.val < 1534 then
(8) else
(9)) else
(if i.val < 1536 then
(14) else
(2)))) else
(if i.val < 1541 then
(if i.val < 1539 then
(if i.val < 1538 then
(5) else
(4)) else
(if i.val < 1540 then
(4) else
(9))) else
(if i.val < 1543 then
(if i.val < 1542 then
(6) else
(6)) else
(if i.val < 1544 then
(8) else
(2))))) else
(if i.val < 1552 then
(if i.val < 1548 then
(if i.val < 1546 then
(13) else
(if i.val < 1547 then
(2) else
(6))) else
(if i.val < 1550 then
(if i.val < 1549 then
(14) else
(8)) else
(if i.val < 1551 then
(12) else
(9)))) else
(if i.val < 1556 then
(if i.val < 1554 then
(if i.val < 1553 then
(15) else
(9)) else
(if i.val < 1555 then
(9) else
(15))) else
(if i.val < 1558 then
(if i.val < 1557 then
(5) else
(12)) else
(if i.val < 1559 then
(13) else
(2)))))))) else
(if i.val < 1620 then
(if i.val < 1590 then
(if i.val < 1575 then
(if i.val < 1567 then
(if i.val < 1563 then
(if i.val < 1561 then
(10) else
(if i.val < 1562 then
(8) else
(10))) else
(if i.val < 1565 then
(if i.val < 1564 then
(1) else
(9)) else
(if i.val < 1566 then
(6) else
(1)))) else
(if i.val < 1571 then
(if i.val < 1569 then
(if i.val < 1568 then
(10) else
(0)) else
(if i.val < 1570 then
(9) else
(8))) else
(if i.val < 1573 then
(if i.val < 1572 then
(4) else
(0)) else
(if i.val < 1574 then
(5) else
(5))))) else
(if i.val < 1582 then
(if i.val < 1578 then
(if i.val < 1576 then
(1) else
(if i.val < 1577 then
(3) else
(3))) else
(if i.val < 1580 then
(if i.val < 1579 then
(11) else
(10)) else
(if i.val < 1581 then
(15) else
(2)))) else
(if i.val < 1586 then
(if i.val < 1584 then
(if i.val < 1583 then
(0) else
(3)) else
(if i.val < 1585 then
(15) else
(9))) else
(if i.val < 1588 then
(if i.val < 1587 then
(7) else
(11)) else
(if i.val < 1589 then
(8) else
(12)))))) else
(if i.val < 1605 then
(if i.val < 1597 then
(if i.val < 1593 then
(if i.val < 1591 then
(1) else
(if i.val < 1592 then
(1) else
(3))) else
(if i.val < 1595 then
(if i.val < 1594 then
(11) else
(2)) else
(if i.val < 1596 then
(2) else
(9)))) else
(if i.val < 1601 then
(if i.val < 1599 then
(if i.val < 1598 then
(10) else
(7)) else
(if i.val < 1600 then
(2) else
(14))) else
(if i.val < 1603 then
(if i.val < 1602 then
(1) else
(10)) else
(if i.val < 1604 then
(6) else
(15))))) else
(if i.val < 1612 then
(if i.val < 1608 then
(if i.val < 1606 then
(2) else
(if i.val < 1607 then
(1) else
(15))) else
(if i.val < 1610 then
(if i.val < 1609 then
(10) else
(11)) else
(if i.val < 1611 then
(2) else
(2)))) else
(if i.val < 1616 then
(if i.val < 1614 then
(if i.val < 1613 then
(11) else
(11)) else
(if i.val < 1615 then
(15) else
(1))) else
(if i.val < 1618 then
(if i.val < 1617 then
(15) else
(4)) else
(if i.val < 1619 then
(10) else
(14))))))) else
(if i.val < 1650 then
(if i.val < 1635 then
(if i.val < 1627 then
(if i.val < 1623 then
(if i.val < 1621 then
(8) else
(if i.val < 1622 then
(11) else
(3))) else
(if i.val < 1625 then
(if i.val < 1624 then
(4) else
(10)) else
(if i.val < 1626 then
(3) else
(14)))) else
(if i.val < 1631 then
(if i.val < 1629 then
(if i.val < 1628 then
(3) else
(13)) else
(if i.val < 1630 then
(0) else
(13))) else
(if i.val < 1633 then
(if i.val < 1632 then
(3) else
(1)) else
(if i.val < 1634 then
(0) else
(13))))) else
(if i.val < 1642 then
(if i.val < 1638 then
(if i.val < 1636 then
(2) else
(if i.val < 1637 then
(8) else
(13))) else
(if i.val < 1640 then
(if i.val < 1639 then
(12) else
(6)) else
(if i.val < 1641 then
(8) else
(0)))) else
(if i.val < 1646 then
(if i.val < 1644 then
(if i.val < 1643 then
(9) else
(0)) else
(if i.val < 1645 then
(6) else
(10))) else
(if i.val < 1648 then
(if i.val < 1647 then
(2) else
(11)) else
(if i.val < 1649 then
(9) else
(1)))))) else
(if i.val < 1665 then
(if i.val < 1657 then
(if i.val < 1653 then
(if i.val < 1651 then
(0) else
(if i.val < 1652 then
(0) else
(9))) else
(if i.val < 1655 then
(if i.val < 1654 then
(1) else
(1)) else
(if i.val < 1656 then
(8) else
(7)))) else
(if i.val < 1661 then
(if i.val < 1659 then
(if i.val < 1658 then
(2) else
(7)) else
(if i.val < 1660 then
(3) else
(3))) else
(if i.val < 1663 then
(if i.val < 1662 then
(9) else
(13)) else
(if i.val < 1664 then
(9) else
(13))))) else
(if i.val < 1672 then
(if i.val < 1668 then
(if i.val < 1666 then
(5) else
(if i.val < 1667 then
(9) else
(11))) else
(if i.val < 1670 then
(if i.val < 1669 then
(8) else
(8)) else
(if i.val < 1671 then
(3) else
(10)))) else
(if i.val < 1676 then
(if i.val < 1674 then
(if i.val < 1673 then
(11) else
(5)) else
(if i.val < 1675 then
(0) else
(8))) else
(if i.val < 1678 then
(if i.val < 1677 then
(4) else
(3)) else
(if i.val < 1679 then
(12) else
(8))))))))) else
(if i.val < 1800 then
(if i.val < 1740 then
(if i.val < 1710 then
(if i.val < 1695 then
(if i.val < 1687 then
(if i.val < 1683 then
(if i.val < 1681 then
(13) else
(if i.val < 1682 then
(5) else
(13))) else
(if i.val < 1685 then
(if i.val < 1684 then
(4) else
(0)) else
(if i.val < 1686 then
(14) else
(13)))) else
(if i.val < 1691 then
(if i.val < 1689 then
(if i.val < 1688 then
(0) else
(0)) else
(if i.val < 1690 then
(11) else
(1))) else
(if i.val < 1693 then
(if i.val < 1692 then
(5) else
(7)) else
(if i.val < 1694 then
(14) else
(5))))) else
(if i.val < 1702 then
(if i.val < 1698 then
(if i.val < 1696 then
(5) else
(if i.val < 1697 then
(4) else
(12))) else
(if i.val < 1700 then
(if i.val < 1699 then
(5) else
(12)) else
(if i.val < 1701 then
(14) else
(7)))) else
(if i.val < 1706 then
(if i.val < 1704 then
(if i.val < 1703 then
(3) else
(14)) else
(if i.val < 1705 then
(0) else
(8))) else
(if i.val < 1708 then
(if i.val < 1707 then
(4) else
(6)) else
(if i.val < 1709 then
(4) else
(12)))))) else
(if i.val < 1725 then
(if i.val < 1717 then
(if i.val < 1713 then
(if i.val < 1711 then
(13) else
(if i.val < 1712 then
(13) else
(7))) else
(if i.val < 1715 then
(if i.val < 1714 then
(6) else
(11)) else
(if i.val < 1716 then
(15) else
(6)))) else
(if i.val < 1721 then
(if i.val < 1719 then
(if i.val < 1718 then
(13) else
(8)) else
(if i.val < 1720 then
(5) else
(15))) else
(if i.val < 1723 then
(if i.val < 1722 then
(10) else
(14)) else
(if i.val < 1724 then
(10) else
(14))))) else
(if i.val < 1732 then
(if i.val < 1728 then
(if i.val < 1726 then
(4) else
(if i.val < 1727 then
(0) else
(4))) else
(if i.val < 1730 then
(if i.val < 1729 then
(1) else
(14)) else
(if i.val < 1731 then
(5) else
(9)))) else
(if i.val < 1736 then
(if i.val < 1734 then
(if i.val < 1733 then
(9) else
(5)) else
(if i.val < 1735 then
(6) else
(14))) else
(if i.val < 1738 then
(if i.val < 1737 then
(12) else
(15)) else
(if i.val < 1739 then
(0) else
(13))))))) else
(if i.val < 1770 then
(if i.val < 1755 then
(if i.val < 1747 then
(if i.val < 1743 then
(if i.val < 1741 then
(1) else
(if i.val < 1742 then
(5) else
(0))) else
(if i.val < 1745 then
(if i.val < 1744 then
(7) else
(15)) else
(if i.val < 1746 then
(11) else
(4)))) else
(if i.val < 1751 then
(if i.val < 1749 then
(if i.val < 1748 then
(11) else
(11)) else
(if i.val < 1750 then
(14) else
(15))) else
(if i.val < 1753 then
(if i.val < 1752 then
(15) else
(1)) else
(if i.val < 1754 then
(7) else
(0))))) else
(if i.val < 1762 then
(if i.val < 1758 then
(if i.val < 1756 then
(13) else
(if i.val < 1757 then
(13) else
(13))) else
(if i.val < 1760 then
(if i.val < 1759 then
(11) else
(4)) else
(if i.val < 1761 then
(12) else
(13)))) else
(if i.val < 1766 then
(if i.val < 1764 then
(if i.val < 1763 then
(13) else
(11)) else
(if i.val < 1765 then
(15) else
(6))) else
(if i.val < 1768 then
(if i.val < 1767 then
(11) else
(6)) else
(if i.val < 1769 then
(1) else
(4)))))) else
(if i.val < 1785 then
(if i.val < 1777 then
(if i.val < 1773 then
(if i.val < 1771 then
(5) else
(if i.val < 1772 then
(5) else
(1))) else
(if i.val < 1775 then
(if i.val < 1774 then
(0) else
(15)) else
(if i.val < 1776 then
(15) else
(12)))) else
(if i.val < 1781 then
(if i.val < 1779 then
(if i.val < 1778 then
(4) else
(11)) else
(if i.val < 1780 then
(5) else
(4))) else
(if i.val < 1783 then
(if i.val < 1782 then
(6) else
(8)) else
(if i.val < 1784 then
(0) else
(1))))) else
(if i.val < 1792 then
(if i.val < 1788 then
(if i.val < 1786 then
(0) else
(if i.val < 1787 then
(15) else
(13))) else
(if i.val < 1790 then
(if i.val < 1789 then
(7) else
(5)) else
(if i.val < 1791 then
(1) else
(8)))) else
(if i.val < 1796 then
(if i.val < 1794 then
(if i.val < 1793 then
(6) else
(0)) else
(if i.val < 1795 then
(0) else
(6))) else
(if i.val < 1798 then
(if i.val < 1797 then
(6) else
(8)) else
(if i.val < 1799 then
(8) else
(14)))))))) else
(if i.val < 1860 then
(if i.val < 1830 then
(if i.val < 1815 then
(if i.val < 1807 then
(if i.val < 1803 then
(if i.val < 1801 then
(4) else
(if i.val < 1802 then
(10) else
(10))) else
(if i.val < 1805 then
(if i.val < 1804 then
(7) else
(2)) else
(if i.val < 1806 then
(10) else
(12)))) else
(if i.val < 1811 then
(if i.val < 1809 then
(if i.val < 1808 then
(14) else
(14)) else
(if i.val < 1810 then
(7) else
(15))) else
(if i.val < 1813 then
(if i.val < 1812 then
(7) else
(7)) else
(if i.val < 1814 then
(7) else
(14))))) else
(if i.val < 1822 then
(if i.val < 1818 then
(if i.val < 1816 then
(6) else
(if i.val < 1817 then
(10) else
(14))) else
(if i.val < 1820 then
(if i.val < 1819 then
(14) else
(4)) else
(if i.val < 1821 then
(15) else
(6)))) else
(if i.val < 1826 then
(if i.val < 1824 then
(if i.val < 1823 then
(14) else
(6)) else
(if i.val < 1825 then
(3) else
(15))) else
(if i.val < 1828 then
(if i.val < 1827 then
(11) else
(4)) else
(if i.val < 1829 then
(4) else
(12)))))) else
(if i.val < 1845 then
(if i.val < 1837 then
(if i.val < 1833 then
(if i.val < 1831 then
(15) else
(if i.val < 1832 then
(3) else
(15))) else
(if i.val < 1835 then
(if i.val < 1834 then
(11) else
(1)) else
(if i.val < 1836 then
(10) else
(4)))) else
(if i.val < 1841 then
(if i.val < 1839 then
(if i.val < 1838 then
(13) else
(9)) else
(if i.val < 1840 then
(4) else
(7))) else
(if i.val < 1843 then
(if i.val < 1842 then
(15) else
(2)) else
(if i.val < 1844 then
(12) else
(13))))) else
(if i.val < 1852 then
(if i.val < 1848 then
(if i.val < 1846 then
(5) else
(if i.val < 1847 then
(1) else
(12))) else
(if i.val < 1850 then
(if i.val < 1849 then
(5) else
(7)) else
(if i.val < 1851 then
(6) else
(10)))) else
(if i.val < 1856 then
(if i.val < 1854 then
(if i.val < 1853 then
(15) else
(15)) else
(if i.val < 1855 then
(13) else
(4))) else
(if i.val < 1858 then
(if i.val < 1857 then
(4) else
(0)) else
(if i.val < 1859 then
(5) else
(0))))))) else
(if i.val < 1890 then
(if i.val < 1875 then
(if i.val < 1867 then
(if i.val < 1863 then
(if i.val < 1861 then
(6) else
(if i.val < 1862 then
(2) else
(15))) else
(if i.val < 1865 then
(if i.val < 1864 then
(15) else
(12)) else
(if i.val < 1866 then
(12) else
(5)))) else
(if i.val < 1871 then
(if i.val < 1869 then
(if i.val < 1868 then
(4) else
(4)) else
(if i.val < 1870 then
(0) else
(8))) else
(if i.val < 1873 then
(if i.val < 1872 then
(15) else
(12)) else
(if i.val < 1874 then
(4) else
(9))))) else
(if i.val < 1882 then
(if i.val < 1878 then
(if i.val < 1876 then
(7) else
(if i.val < 1877 then
(12) else
(5))) else
(if i.val < 1880 then
(if i.val < 1879 then
(12) else
(13)) else
(if i.val < 1881 then
(1) else
(4)))) else
(if i.val < 1886 then
(if i.val < 1884 then
(if i.val < 1883 then
(10) else
(0)) else
(if i.val < 1885 then
(7) else
(15))) else
(if i.val < 1888 then
(if i.val < 1887 then
(4) else
(8)) else
(if i.val < 1889 then
(4) else
(6)))))) else
(if i.val < 1905 then
(if i.val < 1897 then
(if i.val < 1893 then
(if i.val < 1891 then
(15) else
(if i.val < 1892 then
(4) else
(9))) else
(if i.val < 1895 then
(if i.val < 1894 then
(5) else
(7)) else
(if i.val < 1896 then
(1) else
(7)))) else
(if i.val < 1901 then
(if i.val < 1899 then
(if i.val < 1898 then
(6) else
(10)) else
(if i.val < 1900 then
(14) else
(15))) else
(if i.val < 1903 then
(if i.val < 1902 then
(1) else
(12)) else
(if i.val < 1904 then
(1) else
(1))))) else
(if i.val < 1912 then
(if i.val < 1908 then
(if i.val < 1906 then
(13) else
(if i.val < 1907 then
(12) else
(14))) else
(if i.val < 1910 then
(if i.val < 1909 then
(11) else
(15)) else
(if i.val < 1911 then
(14) else
(11)))) else
(if i.val < 1916 then
(if i.val < 1914 then
(if i.val < 1913 then
(13) else
(4)) else
(if i.val < 1915 then
(13) else
(5))) else
(if i.val < 1918 then
(if i.val < 1917 then
(15) else
(5)) else
(if i.val < 1919 then
(5) else
(1))))))))))) : Nat) % 16, Nat.mod_lt _ (by decide)⟩

def representativeIndex (i : Fin 1920) : Fin 120 :=
  ⟨(if i.val < 960 then
(if i.val < 480 then
(if i.val < 240 then
(if i.val < 120 then
(if i.val < 60 then
(if i.val < 30 then
(if i.val < 15 then
(if i.val < 7 then
(if i.val < 3 then
(if i.val < 1 then
(0) else
(if i.val < 2 then
(53) else
(42))) else
(if i.val < 5 then
(if i.val < 4 then
(8) else
(109)) else
(if i.val < 6 then
(74) else
(105)))) else
(if i.val < 11 then
(if i.val < 9 then
(if i.val < 8 then
(112) else
(55)) else
(if i.val < 10 then
(5) else
(114))) else
(if i.val < 13 then
(if i.val < 12 then
(17) else
(3)) else
(if i.val < 14 then
(13) else
(1))))) else
(if i.val < 22 then
(if i.val < 18 then
(if i.val < 16 then
(51) else
(if i.val < 17 then
(88) else
(39))) else
(if i.val < 20 then
(if i.val < 19 then
(28) else
(63)) else
(if i.val < 21 then
(10) else
(12)))) else
(if i.val < 26 then
(if i.val < 24 then
(if i.val < 23 then
(2) else
(16)) else
(if i.val < 25 then
(15) else
(9))) else
(if i.val < 28 then
(if i.val < 27 then
(54) else
(102)) else
(if i.val < 29 then
(118) else
(36)))))) else
(if i.val < 45 then
(if i.val < 37 then
(if i.val < 33 then
(if i.val < 31 then
(104) else
(if i.val < 32 then
(4) else
(19))) else
(if i.val < 35 then
(if i.val < 34 then
(106) else
(111)) else
(if i.val < 36 then
(38) else
(43)))) else
(if i.val < 41 then
(if i.val < 39 then
(if i.val < 38 then
(6) else
(66)) else
(if i.val < 40 then
(25) else
(110))) else
(if i.val < 43 then
(if i.val < 42 then
(96) else
(40)) else
(if i.val < 44 then
(64) else
(21))))) else
(if i.val < 52 then
(if i.val < 48 then
(if i.val < 46 then
(80) else
(if i.val < 47 then
(107) else
(79))) else
(if i.val < 50 then
(if i.val < 49 then
(24) else
(20)) else
(if i.val < 51 then
(82) else
(116)))) else
(if i.val < 56 then
(if i.val < 54 then
(if i.val < 53 then
(68) else
(101)) else
(if i.val < 55 then
(26) else
(78))) else
(if i.val < 58 then
(if i.val < 57 then
(22) else
(76)) else
(if i.val < 59 then
(86) else
(90))))))) else
(if i.val < 90 then
(if i.val < 75 then
(if i.val < 67 then
(if i.val < 63 then
(if i.val < 61 then
(7) else
(if i.val < 62 then
(37) else
(85))) else
(if i.val < 65 then
(if i.val < 64 then
(100) else
(103)) else
(if i.val < 66 then
(31) else
(65)))) else
(if i.val < 71 then
(if i.val < 69 then
(if i.val < 68 then
(41) else
(58)) else
(if i.val < 70 then
(81) else
(50))) else
(if i.val < 73 then
(if i.val < 72 then
(73) else
(99)) else
(if i.val < 74 then
(83) else
(60))))) else
(if i.val < 82 then
(if i.val < 78 then
(if i.val < 76 then
(92) else
(if i.val < 77 then
(59) else
(29))) else
(if i.val < 80 then
(if i.val < 79 then
(89) else
(115)) else
(if i.val < 81 then
(47) else
(71)))) else
(if i.val < 86 then
(if i.val < 84 then
(if i.val < 83 then
(46) else
(70)) else
(if i.val < 85 then
(62) else
(94))) else
(if i.val < 88 then
(if i.val < 87 then
(93) else
(113)) else
(if i.val < 89 then
(84) else
(75)))))) else
(if i.val < 105 then
(if i.val < 97 then
(if i.val < 93 then
(if i.val < 91 then
(98) else
(if i.val < 92 then
(35) else
(18))) else
(if i.val < 95 then
(if i.val < 94 then
(117) else
(11)) else
(if i.val < 96 then
(56) else
(14)))) else
(if i.val < 101 then
(if i.val < 99 then
(if i.val < 98 then
(52) else
(44)) else
(if i.val < 100 then
(67) else
(32))) else
(if i.val < 103 then
(if i.val < 102 then
(61) else
(30)) else
(if i.val < 104 then
(91) else
(57))))) else
(if i.val < 112 then
(if i.val < 108 then
(if i.val < 106 then
(34) else
(if i.val < 107 then
(48) else
(72))) else
(if i.val < 110 then
(if i.val < 109 then
(69) else
(95)) else
(if i.val < 111 then
(119) else
(27)))) else
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
(87) else
(45)) else
(if i.val < 115 then
(77) else
(49))) else
(if i.val < 118 then
(if i.val < 117 then
(23) else
(108)) else
(if i.val < 119 then
(33) else
(97)))))))) else
(if i.val < 180 then
(if i.val < 150 then
(if i.val < 135 then
(if i.val < 127 then
(if i.val < 123 then
(if i.val < 121 then
(0) else
(if i.val < 122 then
(8) else
(53))) else
(if i.val < 125 then
(if i.val < 124 then
(42) else
(6)) else
(if i.val < 126 then
(25) else
(43)))) else
(if i.val < 131 then
(if i.val < 129 then
(if i.val < 128 then
(66) else
(105)) else
(if i.val < 130 then
(112) else
(74))) else
(if i.val < 133 then
(if i.val < 132 then
(109) else
(101)) else
(if i.val < 134 then
(26) else
(68))))) else
(if i.val < 142 then
(if i.val < 138 then
(if i.val < 136 then
(78) else
(if i.val < 137 then
(17) else
(114))) else
(if i.val < 140 then
(if i.val < 139 then
(5) else
(55)) else
(if i.val < 141 then
(36) else
(104)))) else
(if i.val < 146 then
(if i.val < 144 then
(if i.val < 143 then
(118) else
(4)) else
(if i.val < 145 then
(28) else
(63))) else
(if i.val < 148 then
(if i.val < 147 then
(39) else
(88)) else
(if i.val < 149 then
(24) else
(116)))))) else
(if i.val < 165 then
(if i.val < 157 then
(if i.val < 153 then
(if i.val < 151 then
(20) else
(if i.val < 152 then
(82) else
(86))) else
(if i.val < 155 then
(if i.val < 154 then
(90) else
(22)) else
(if i.val < 156 then
(76) else
(15)))) else
(if i.val < 161 then
(if i.val < 159 then
(if i.val < 158 then
(54) else
(9)) else
(if i.val < 160 then
(102) else
(110))) else
(if i.val < 163 then
(if i.val < 162 then
(40) else
(64)) else
(if i.val < 164 then
(96) else
(21))))) else
(if i.val < 172 then
(if i.val < 168 then
(if i.val < 166 then
(80) else
(if i.val < 167 then
(107) else
(79))) else
(if i.val < 170 then
(if i.val < 169 then
(51) else
(13)) else
(if i.val < 171 then
(1) else
(3)))) else
(if i.val < 176 then
(if i.val < 174 then
(if i.val < 173 then
(10) else
(12)) else
(if i.val < 175 then
(16) else
(2))) else
(if i.val < 178 then
(if i.val < 177 then
(19) else
(106)) else
(if i.val < 179 then
(38) else
(111))))))) else
(if i.val < 210 then
(if i.val < 195 then
(if i.val < 187 then
(if i.val < 183 then
(if i.val < 181 then
(21) else
(if i.val < 182 then
(79) else
(80))) else
(if i.val < 185 then
(if i.val < 184 then
(107) else
(0)) else
(if i.val < 186 then
(53) else
(42)))) else
(if i.val < 191 then
(if i.val < 189 then
(if i.val < 188 then
(8) else
(90)) else
(if i.val < 190 then
(86) else
(76))) else
(if i.val < 193 then
(if i.val < 192 then
(22) else
(82)) else
(if i.val < 194 then
(116) else
(20))))) else
(if i.val < 202 then
(if i.val < 198 then
(if i.val < 196 then
(24) else
(if i.val < 197 then
(55) else
(114))) else
(if i.val < 200 then
(if i.val < 199 then
(5) else
(17)) else
(if i.val < 201 then
(43) else
(66)))) else
(if i.val < 206 then
(if i.val < 204 then
(if i.val < 203 then
(25) else
(6)) else
(if i.val < 205 then
(102) else
(54))) else
(if i.val < 208 then
(if i.val < 207 then
(15) else
(9)) else
(if i.val < 209 then
(64) else
(40)))))) else
(if i.val < 225 then
(if i.val < 217 then
(if i.val < 213 then
(if i.val < 211 then
(110) else
(if i.val < 212 then
(96) else
(118))) else
(if i.val < 215 then
(if i.val < 214 then
(36) else
(104)) else
(if i.val < 216 then
(4) else
(101)))) else
(if i.val < 221 then
(if i.val < 219 then
(if i.val < 218 then
(26) else
(78)) else
(if i.val < 220 then
(68) else
(106))) else
(if i.val < 223 then
(if i.val < 222 then
(38) else
(19)) else
(if i.val < 224 then
(111) else
(105))))) else
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(112) else
(if i.val < 227 then
(109) else
(74))) else
(if i.val < 230 then
(if i.val < 229 then
(39) else
(63)) else
(if i.val < 231 then
(88) else
(28)))) else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
(51) else
(3)) else
(if i.val < 235 then
(1) else
(13))) else
(if i.val < 238 then
(if i.val < 237 then
(12) else
(2)) else
(if i.val < 239 then
(10) else
(16))))))))) else
(if i.val < 360 then
(if i.val < 300 then
(if i.val < 270 then
(if i.val < 255 then
(if i.val < 247 then
(if i.val < 243 then
(if i.val < 241 then
(3) else
(if i.val < 242 then
(1) else
(51))) else
(if i.val < 245 then
(if i.val < 244 then
(13) else
(76)) else
(if i.val < 246 then
(90) else
(86)))) else
(if i.val < 251 then
(if i.val < 249 then
(if i.val < 248 then
(22) else
(54)) else
(if i.val < 250 then
(102) else
(9))) else
(if i.val < 253 then
(if i.val < 252 then
(15) else
(43)) else
(if i.val < 254 then
(25) else
(66))))) else
(if i.val < 262 then
(if i.val < 258 then
(if i.val < 256 then
(6) else
(if i.val < 257 then
(88) else
(28))) else
(if i.val < 260 then
(if i.val < 259 then
(39) else
(63)) else
(if i.val < 261 then
(0) else
(42)))) else
(if i.val < 266 then
(if i.val < 264 then
(if i.val < 263 then
(53) else
(8)) else
(if i.val < 265 then
(64) else
(110))) else
(if i.val < 268 then
(if i.val < 267 then
(96) else
(40)) else
(if i.val < 269 then
(109) else
(112)))))) else
(if i.val < 285 then
(if i.val < 277 then
(if i.val < 273 then
(if i.val < 271 then
(105) else
(if i.val < 272 then
(74) else
(107))) else
(if i.val < 275 then
(if i.val < 274 then
(79) else
(80)) else
(if i.val < 276 then
(21) else
(16)))) else
(if i.val < 281 then
(if i.val < 279 then
(if i.val < 278 then
(12) else
(10)) else
(if i.val < 280 then
(2) else
(5))) else
(if i.val < 283 then
(if i.val < 282 then
(55) else
(17)) else
(if i.val < 284 then
(114) else
(26))))) else
(if i.val < 292 then
(if i.val < 288 then
(if i.val < 286 then
(101) else
(if i.val < 287 then
(68) else
(78))) else
(if i.val < 290 then
(if i.val < 289 then
(106) else
(38)) else
(if i.val < 291 then
(19) else
(111)))) else
(if i.val < 296 then
(if i.val < 294 then
(if i.val < 293 then
(82) else
(116)) else
(if i.val < 295 then
(20) else
(24))) else
(if i.val < 298 then
(if i.val < 297 then
(4) else
(36)) else
(if i.val < 299 then
(118) else
(104))))))) else
(if i.val < 330 then
(if i.val < 315 then
(if i.val < 307 then
(if i.val < 303 then
(if i.val < 301 then
(83) else
(if i.val < 302 then
(60) else
(99))) else
(if i.val < 305 then
(if i.val < 304 then
(92) else
(95)) else
(if i.val < 306 then
(119) else
(27)))) else
(if i.val < 311 then
(if i.val < 309 then
(if i.val < 308 then
(69) else
(35)) else
(if i.val < 310 then
(84) else
(98))) else
(if i.val < 313 then
(if i.val < 312 then
(75) else
(11)) else
(if i.val < 314 then
(18) else
(117))))) else
(if i.val < 322 then
(if i.val < 318 then
(if i.val < 316 then
(56) else
(if i.val < 317 then
(23) else
(33))) else
(if i.val < 320 then
(if i.val < 319 then
(108) else
(97)) else
(if i.val < 321 then
(45) else
(49)))) else
(if i.val < 326 then
(if i.val < 324 then
(if i.val < 323 then
(77) else
(87)) else
(if i.val < 325 then
(65) else
(103))) else
(if i.val < 328 then
(if i.val < 327 then
(41) else
(31)) else
(if i.val < 329 then
(47) else
(71)))))) else
(if i.val < 345 then
(if i.val < 337 then
(if i.val < 333 then
(if i.val < 331 then
(46) else
(if i.val < 332 then
(70) else
(59))) else
(if i.val < 335 then
(if i.val < 334 then
(29) else
(89)) else
(if i.val < 336 then
(115) else
(30)))) else
(if i.val < 341 then
(if i.val < 339 then
(if i.val < 338 then
(61) else
(32)) else
(if i.val < 340 then
(91) else
(34))) else
(if i.val < 343 then
(if i.val < 342 then
(72) else
(48)) else
(if i.val < 344 then
(57) else
(62))))) else
(if i.val < 352 then
(if i.val < 348 then
(if i.val < 346 then
(113) else
(if i.val < 347 then
(93) else
(94))) else
(if i.val < 350 then
(if i.val < 349 then
(44) else
(14)) else
(if i.val < 351 then
(52) else
(67)))) else
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
(37) else
(85)) else
(if i.val < 355 then
(100) else
(7))) else
(if i.val < 358 then
(if i.val < 357 then
(50) else
(58)) else
(if i.val < 359 then
(73) else
(81)))))))) else
(if i.val < 420 then
(if i.val < 390 then
(if i.val < 375 then
(if i.val < 367 then
(if i.val < 363 then
(if i.val < 361 then
(64) else
(if i.val < 362 then
(40) else
(110))) else
(if i.val < 365 then
(if i.val < 364 then
(96) else
(20)) else
(if i.val < 366 then
(82) else
(116)))) else
(if i.val < 371 then
(if i.val < 369 then
(if i.val < 368 then
(24) else
(88)) else
(if i.val < 370 then
(39) else
(28))) else
(if i.val < 373 then
(if i.val < 372 then
(63) else
(12)) else
(if i.val < 374 then
(10) else
(2))))) else
(if i.val < 382 then
(if i.val < 378 then
(if i.val < 376 then
(16) else
(if i.val < 377 then
(5) else
(114))) else
(if i.val < 380 then
(if i.val < 379 then
(55) else
(17)) else
(if i.val < 381 then
(0) else
(42)))) else
(if i.val < 386 then
(if i.val < 384 then
(if i.val < 383 then
(53) else
(8)) else
(if i.val < 385 then
(25) else
(43))) else
(if i.val < 388 then
(if i.val < 387 then
(66) else
(6)) else
(if i.val < 389 then
(36) else
(4)))))) else
(if i.val < 405 then
(if i.val < 397 then
(if i.val < 393 then
(if i.val < 391 then
(104) else
(if i.val < 392 then
(118) else
(51))) else
(if i.val < 395 then
(if i.val < 394 then
(13) else
(3)) else
(if i.val < 396 then
(1) else
(26)))) else
(if i.val < 401 then
(if i.val < 399 then
(if i.val < 398 then
(101) else
(78)) else
(if i.val < 400 then
(68) else
(21))) else
(if i.val < 403 then
(if i.val < 402 then
(80) else
(79)) else
(if i.val < 404 then
(107) else
(90))))) else
(if i.val < 412 then
(if i.val < 408 then
(if i.val < 406 then
(22) else
(if i.val < 407 then
(86) else
(76))) else
(if i.val < 410 then
(if i.val < 409 then
(111) else
(38)) else
(if i.val < 411 then
(106) else
(19)))) else
(if i.val < 416 then
(if i.val < 414 then
(if i.val < 413 then
(109) else
(112)) else
(if i.val < 415 then
(105) else
(74))) else
(if i.val < 418 then
(if i.val < 417 then
(102) else
(9)) else
(if i.val < 419 then
(15) else
(54))))))) else
(if i.val < 450 then
(if i.val < 435 then
(if i.val < 427 then
(if i.val < 423 then
(if i.val < 421 then
(35) else
(if i.val < 422 then
(75) else
(98))) else
(if i.val < 425 then
(if i.val < 424 then
(84) else
(52)) else
(if i.val < 426 then
(44) else
(14)))) else
(if i.val < 431 then
(if i.val < 429 then
(if i.val < 428 then
(67) else
(89)) else
(if i.val < 430 then
(115) else
(29))) else
(if i.val < 433 then
(if i.val < 432 then
(59) else
(57)) else
(if i.val < 434 then
(48) else
(34))))) else
(if i.val < 442 then
(if i.val < 438 then
(if i.val < 436 then
(72) else
(if i.val < 437 then
(27) else
(95))) else
(if i.val < 440 then
(if i.val < 439 then
(69) else
(119)) else
(if i.val < 441 then
(31) else
(103)))) else
(if i.val < 446 then
(if i.val < 444 then
(if i.val < 443 then
(41) else
(65)) else
(if i.val < 445 then
(99) else
(60))) else
(if i.val < 448 then
(if i.val < 447 then
(92) else
(83)) else
(if i.val < 449 then
(94) else
(62)))))) else
(if i.val < 465 then
(if i.val < 457 then
(if i.val < 453 then
(if i.val < 451 then
(113) else
(if i.val < 452 then
(93) else
(77))) else
(if i.val < 455 then
(if i.val < 454 then
(87) else
(45)) else
(if i.val < 456 then
(49) else
(18)))) else
(if i.val < 461 then
(if i.val < 459 then
(if i.val < 458 then
(117) else
(11)) else
(if i.val < 460 then
(56) else
(108))) else
(if i.val < 463 then
(if i.val < 462 then
(97) else
(23)) else
(if i.val < 464 then
(33) else
(32))))) else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(91) else
(if i.val < 467 then
(30) else
(61))) else
(if i.val < 470 then
(if i.val < 469 then
(47) else
(46)) else
(if i.val < 471 then
(71) else
(70)))) else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
(100) else
(37)) else
(if i.val < 475 then
(85) else
(7))) else
(if i.val < 478 then
(if i.val < 477 then
(50) else
(58)) else
(if i.val < 479 then
(73) else
(81)))))))))) else
(if i.val < 720 then
(if i.val < 600 then
(if i.val < 540 then
(if i.val < 510 then
(if i.val < 495 then
(if i.val < 487 then
(if i.val < 483 then
(if i.val < 481 then
(30) else
(if i.val < 482 then
(91) else
(61))) else
(if i.val < 485 then
(if i.val < 484 then
(32) else
(49)) else
(if i.val < 486 then
(45) else
(87)))) else
(if i.val < 491 then
(if i.val < 489 then
(if i.val < 488 then
(77) else
(18)) else
(if i.val < 490 then
(11) else
(56))) else
(if i.val < 493 then
(if i.val < 492 then
(117) else
(119)) else
(if i.val < 494 then
(27) else
(69))))) else
(if i.val < 502 then
(if i.val < 498 then
(if i.val < 496 then
(95) else
(if i.val < 497 then
(75) else
(35))) else
(if i.val < 500 then
(if i.val < 499 then
(84) else
(98)) else
(if i.val < 501 then
(37) else
(100)))) else
(if i.val < 506 then
(if i.val < 504 then
(if i.val < 503 then
(85) else
(7)) else
(if i.val < 505 then
(14) else
(67))) else
(if i.val < 508 then
(if i.val < 507 then
(52) else
(44)) else
(if i.val < 509 then
(50) else
(81)))))) else
(if i.val < 525 then
(if i.val < 517 then
(if i.val < 513 then
(if i.val < 511 then
(73) else
(if i.val < 512 then
(58) else
(23))) else
(if i.val < 515 then
(if i.val < 514 then
(33) else
(97)) else
(if i.val < 516 then
(108) else
(46)))) else
(if i.val < 521 then
(if i.val < 519 then
(if i.val < 518 then
(47) else
(70)) else
(if i.val < 520 then
(71) else
(72))) else
(if i.val < 523 then
(if i.val < 522 then
(34) else
(57)) else
(if i.val < 524 then
(48) else
(41))))) else
(if i.val < 532 then
(if i.val < 528 then
(if i.val < 526 then
(65) else
(if i.val < 527 then
(103) else
(31))) else
(if i.val < 530 then
(if i.val < 529 then
(59) else
(29)) else
(if i.val < 531 then
(89) else
(115)))) else
(if i.val < 536 then
(if i.val < 534 then
(if i.val < 533 then
(83) else
(92)) else
(if i.val < 535 then
(60) else
(99))) else
(if i.val < 538 then
(if i.val < 537 then
(62) else
(94)) else
(if i.val < 539 then
(113) else
(93))))))) else
(if i.val < 570 then
(if i.val < 555 then
(if i.val < 547 then
(if i.val < 543 then
(if i.val < 541 then
(111) else
(if i.val < 542 then
(38) else
(19))) else
(if i.val < 545 then
(if i.val < 544 then
(106) else
(13)) else
(if i.val < 546 then
(3) else
(51)))) else
(if i.val < 551 then
(if i.val < 549 then
(if i.val < 548 then
(1) else
(21)) else
(if i.val < 550 then
(107) else
(79))) else
(if i.val < 553 then
(if i.val < 552 then
(80) else
(82)) else
(if i.val < 554 then
(116) else
(24))))) else
(if i.val < 562 then
(if i.val < 558 then
(if i.val < 556 then
(20) else
(if i.val < 557 then
(118) else
(104))) else
(if i.val < 560 then
(if i.val < 559 then
(36) else
(4)) else
(if i.val < 561 then
(9) else
(54)))) else
(if i.val < 566 then
(if i.val < 564 then
(if i.val < 563 then
(102) else
(15)) else
(if i.val < 565 then
(112) else
(105))) else
(if i.val < 568 then
(if i.val < 567 then
(74) else
(109)) else
(if i.val < 569 then
(101) else
(68)))))) else
(if i.val < 585 then
(if i.val < 577 then
(if i.val < 573 then
(if i.val < 571 then
(26) else
(if i.val < 572 then
(78) else
(64))) else
(if i.val < 575 then
(if i.val < 574 then
(40) else
(110)) else
(if i.val < 576 then
(96) else
(63)))) else
(if i.val < 581 then
(if i.val < 579 then
(if i.val < 578 then
(28) else
(39)) else
(if i.val < 580 then
(88) else
(16))) else
(if i.val < 583 then
(if i.val < 582 then
(2) else
(10)) else
(if i.val < 584 then
(12) else
(53))))) else
(if i.val < 592 then
(if i.val < 588 then
(if i.val < 586 then
(8) else
(if i.val < 587 then
(42) else
(0))) else
(if i.val < 590 then
(if i.val < 589 then
(55) else
(17)) else
(if i.val < 591 then
(5) else
(114)))) else
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
(22) else
(76)) else
(if i.val < 595 then
(86) else
(90))) else
(if i.val < 598 then
(if i.val < 597 then
(43) else
(66)) else
(if i.val < 599 then
(25) else
(6)))))))) else
(if i.val < 660 then
(if i.val < 630 then
(if i.val < 615 then
(if i.val < 607 then
(if i.val < 603 then
(if i.val < 601 then
(65) else
(if i.val < 602 then
(103) else
(31))) else
(if i.val < 605 then
(if i.val < 604 then
(41) else
(30)) else
(if i.val < 606 then
(32) else
(61)))) else
(if i.val < 611 then
(if i.val < 609 then
(if i.val < 608 then
(91) else
(77)) else
(if i.val < 610 then
(87) else
(49))) else
(if i.val < 613 then
(if i.val < 612 then
(45) else
(72)) else
(if i.val < 614 then
(48) else
(34))))) else
(if i.val < 622 then
(if i.val < 618 then
(if i.val < 616 then
(57) else
(if i.val < 617 then
(75) else
(84))) else
(if i.val < 620 then
(if i.val < 619 then
(35) else
(98)) else
(if i.val < 621 then
(60) else
(92)))) else
(if i.val < 626 then
(if i.val < 624 then
(if i.val < 623 then
(99) else
(83)) else
(if i.val < 625 then
(115) else
(29))) else
(if i.val < 628 then
(if i.val < 627 then
(89) else
(59)) else
(if i.val < 629 then
(44) else
(67)))))) else
(if i.val < 645 then
(if i.val < 637 then
(if i.val < 633 then
(if i.val < 631 then
(14) else
(if i.val < 632 then
(52) else
(18))) else
(if i.val < 635 then
(if i.val < 634 then
(117) else
(11)) else
(if i.val < 636 then
(56) else
(7)))) else
(if i.val < 641 then
(if i.val < 639 then
(if i.val < 638 then
(100) else
(37)) else
(if i.val < 640 then
(85) else
(119))) else
(if i.val < 643 then
(if i.val < 642 then
(69) else
(95)) else
(if i.val < 644 then
(27) else
(93))))) else
(if i.val < 652 then
(if i.val < 648 then
(if i.val < 646 then
(62) else
(if i.val < 647 then
(94) else
(113))) else
(if i.val < 650 then
(if i.val < 649 then
(108) else
(33)) else
(if i.val < 651 then
(23) else
(97)))) else
(if i.val < 656 then
(if i.val < 654 then
(if i.val < 653 then
(47) else
(71)) else
(if i.val < 655 then
(46) else
(70))) else
(if i.val < 658 then
(if i.val < 657 then
(50) else
(73)) else
(if i.val < 659 then
(81) else
(58))))))) else
(if i.val < 690 then
(if i.val < 675 then
(if i.val < 667 then
(if i.val < 663 then
(if i.val < 661 then
(65) else
(if i.val < 662 then
(103) else
(31))) else
(if i.val < 665 then
(if i.val < 664 then
(41) else
(32)) else
(if i.val < 666 then
(91) else
(30)))) else
(if i.val < 671 then
(if i.val < 669 then
(if i.val < 668 then
(61) else
(23)) else
(if i.val < 670 then
(108) else
(97))) else
(if i.val < 673 then
(if i.val < 672 then
(33) else
(71)) else
(if i.val < 674 then
(47) else
(70))))) else
(if i.val < 682 then
(if i.val < 678 then
(if i.val < 676 then
(46) else
(if i.val < 677 then
(45) else
(49))) else
(if i.val < 680 then
(if i.val < 679 then
(77) else
(87)) else
(if i.val < 681 then
(29) else
(59)))) else
(if i.val < 686 then
(if i.val < 684 then
(if i.val < 683 then
(115) else
(89)) else
(if i.val < 685 then
(11) else
(56))) else
(if i.val < 688 then
(if i.val < 687 then
(117) else
(18)) else
(if i.val < 689 then
(27) else
(119)))))) else
(if i.val < 705 then
(if i.val < 697 then
(if i.val < 693 then
(if i.val < 691 then
(95) else
(if i.val < 692 then
(69) else
(60))) else
(if i.val < 695 then
(if i.val < 694 then
(99) else
(83)) else
(if i.val < 696 then
(92) else
(57)))) else
(if i.val < 701 then
(if i.val < 699 then
(if i.val < 698 then
(48) else
(34)) else
(if i.val < 700 then
(72) else
(67))) else
(if i.val < 703 then
(if i.val < 702 then
(52) else
(44)) else
(if i.val < 704 then
(14) else
(35))))) else
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(75) else
(if i.val < 707 then
(84) else
(98))) else
(if i.val < 710 then
(if i.val < 709 then
(7) else
(100)) else
(if i.val < 711 then
(37) else
(85)))) else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
(94) else
(113)) else
(if i.val < 715 then
(93) else
(62))) else
(if i.val < 718 then
(if i.val < 717 then
(73) else
(58)) else
(if i.val < 719 then
(50) else
(81))))))))) else
(if i.val < 840 then
(if i.val < 780 then
(if i.val < 750 then
(if i.val < 735 then
(if i.val < 727 then
(if i.val < 723 then
(if i.val < 721 then
(101) else
(if i.val < 722 then
(78) else
(68))) else
(if i.val < 725 then
(if i.val < 724 then
(26) else
(16)) else
(if i.val < 726 then
(2) else
(10)))) else
(if i.val < 731 then
(if i.val < 729 then
(if i.val < 728 then
(12) else
(112)) else
(if i.val < 730 then
(74) else
(105))) else
(if i.val < 733 then
(if i.val < 732 then
(109) else
(88)) else
(if i.val < 734 then
(63) else
(39))))) else
(if i.val < 742 then
(if i.val < 738 then
(if i.val < 736 then
(28) else
(if i.val < 737 then
(21) else
(107))) else
(if i.val < 740 then
(if i.val < 739 then
(79) else
(80)) else
(if i.val < 741 then
(96) else
(110)))) else
(if i.val < 746 then
(if i.val < 744 then
(if i.val < 743 then
(64) else
(40)) else
(if i.val < 745 then
(106) else
(111))) else
(if i.val < 748 then
(if i.val < 747 then
(19) else
(38)) else
(if i.val < 749 then
(82) else
(24)))))) else
(if i.val < 765 then
(if i.val < 757 then
(if i.val < 753 then
(if i.val < 751 then
(116) else
(if i.val < 752 then
(20) else
(102))) else
(if i.val < 755 then
(if i.val < 754 then
(15) else
(54)) else
(if i.val < 756 then
(9) else
(4)))) else
(if i.val < 761 then
(if i.val < 759 then
(if i.val < 758 then
(104) else
(118)) else
(if i.val < 760 then
(36) else
(86))) else
(if i.val < 763 then
(if i.val < 762 then
(76) else
(90)) else
(if i.val < 764 then
(22) else
(17))))) else
(if i.val < 772 then
(if i.val < 768 then
(if i.val < 766 then
(55) else
(if i.val < 767 then
(5) else
(114))) else
(if i.val < 770 then
(if i.val < 769 then
(3) else
(1)) else
(if i.val < 771 then
(13) else
(51)))) else
(if i.val < 776 then
(if i.val < 774 then
(if i.val < 773 then
(6) else
(43)) else
(if i.val < 775 then
(66) else
(25))) else
(if i.val < 778 then
(if i.val < 777 then
(8) else
(42)) else
(if i.val < 779 then
(53) else
(0))))))) else
(if i.val < 810 then
(if i.val < 795 then
(if i.val < 787 then
(if i.val < 783 then
(if i.val < 781 then
(10) else
(if i.val < 782 then
(16) else
(12))) else
(if i.val < 785 then
(if i.val < 784 then
(2) else
(107)) else
(if i.val < 786 then
(80) else
(21)))) else
(if i.val < 791 then
(if i.val < 789 then
(if i.val < 788 then
(79) else
(19)) else
(if i.val < 790 then
(111) else
(106))) else
(if i.val < 793 then
(if i.val < 792 then
(38) else
(51)) else
(if i.val < 794 then
(3) else
(1))))) else
(if i.val < 802 then
(if i.val < 798 then
(if i.val < 796 then
(13) else
(if i.val < 797 then
(82) else
(20))) else
(if i.val < 800 then
(if i.val < 799 then
(24) else
(116)) else
(if i.val < 801 then
(109) else
(74)))) else
(if i.val < 806 then
(if i.val < 804 then
(if i.val < 803 then
(105) else
(112)) else
(if i.val < 805 then
(39) else
(63))) else
(if i.val < 808 then
(if i.val < 807 then
(88) else
(28)) else
(if i.val < 809 then
(4) else
(104)))))) else
(if i.val < 825 then
(if i.val < 817 then
(if i.val < 813 then
(if i.val < 811 then
(118) else
(if i.val < 812 then
(36) else
(22))) else
(if i.val < 815 then
(if i.val < 814 then
(86) else
(76)) else
(if i.val < 816 then
(90) else
(54)))) else
(if i.val < 821 then
(if i.val < 819 then
(if i.val < 818 then
(9) else
(15)) else
(if i.val < 820 then
(102) else
(55))) else
(if i.val < 823 then
(if i.val < 822 then
(17) else
(5)) else
(if i.val < 824 then
(114) else
(110))))) else
(if i.val < 832 then
(if i.val < 828 then
(if i.val < 826 then
(64) else
(if i.val < 827 then
(40) else
(96))) else
(if i.val < 830 then
(if i.val < 829 then
(6) else
(43)) else
(if i.val < 831 then
(25) else
(66)))) else
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
(78) else
(101)) else
(if i.val < 835 then
(68) else
(26))) else
(if i.val < 838 then
(if i.val < 837 then
(53) else
(42)) else
(if i.val < 839 then
(0) else
(8)))))))) else
(if i.val < 900 then
(if i.val < 870 then
(if i.val < 855 then
(if i.val < 847 then
(if i.val < 843 then
(if i.val < 841 then
(82) else
(if i.val < 842 then
(116) else
(20))) else
(if i.val < 845 then
(if i.val < 844 then
(24) else
(2)) else
(if i.val < 846 then
(16) else
(10)))) else
(if i.val < 851 then
(if i.val < 849 then
(if i.val < 848 then
(12) else
(112)) else
(if i.val < 850 then
(105) else
(74))) else
(if i.val < 853 then
(if i.val < 852 then
(109) else
(3)) else
(if i.val < 854 then
(13) else
(51))))) else
(if i.val < 862 then
(if i.val < 858 then
(if i.val < 856 then
(1) else
(if i.val < 857 then
(76) else
(86))) else
(if i.val < 860 then
(if i.val < 859 then
(22) else
(90)) else
(if i.val < 861 then
(78) else
(26)))) else
(if i.val < 866 then
(if i.val < 864 then
(if i.val < 863 then
(101) else
(68)) else
(if i.val < 865 then
(107) else
(80))) else
(if i.val < 868 then
(if i.val < 867 then
(21) else
(79)) else
(if i.val < 869 then
(19) else
(111)))))) else
(if i.val < 885 then
(if i.val < 877 then
(if i.val < 873 then
(if i.val < 871 then
(38) else
(if i.val < 872 then
(106) else
(36))) else
(if i.val < 875 then
(if i.val < 874 then
(4) else
(104)) else
(if i.val < 876 then
(118) else
(5)))) else
(if i.val < 881 then
(if i.val < 879 then
(if i.val < 878 then
(114) else
(17)) else
(if i.val < 880 then
(55) else
(96))) else
(if i.val < 883 then
(if i.val < 882 then
(40) else
(64)) else
(if i.val < 884 then
(110) else
(42))))) else
(if i.val < 892 then
(if i.val < 888 then
(if i.val < 886 then
(0) else
(if i.val < 887 then
(8) else
(53))) else
(if i.val < 890 then
(if i.val < 889 then
(63) else
(28)) else
(if i.val < 891 then
(88) else
(39)))) else
(if i.val < 896 then
(if i.val < 894 then
(if i.val < 893 then
(102) else
(54)) else
(if i.val < 895 then
(15) else
(9))) else
(if i.val < 898 then
(if i.val < 897 then
(25) else
(6)) else
(if i.val < 899 then
(66) else
(43))))))) else
(if i.val < 930 then
(if i.val < 915 then
(if i.val < 907 then
(if i.val < 903 then
(if i.val < 901 then
(43) else
(if i.val < 902 then
(25) else
(6))) else
(if i.val < 905 then
(if i.val < 904 then
(66) else
(82)) else
(if i.val < 906 then
(24) else
(20)))) else
(if i.val < 911 then
(if i.val < 909 then
(if i.val < 908 then
(116) else
(8)) else
(if i.val < 910 then
(0) else
(53))) else
(if i.val < 913 then
(if i.val < 912 then
(42) else
(107)) else
(if i.val < 914 then
(79) else
(80))))) else
(if i.val < 922 then
(if i.val < 918 then
(if i.val < 916 then
(21) else
(if i.val < 917 then
(9) else
(15))) else
(if i.val < 920 then
(if i.val < 919 then
(102) else
(54)) else
(if i.val < 921 then
(16) else
(12)))) else
(if i.val < 926 then
(if i.val < 924 then
(if i.val < 923 then
(2) else
(10)) else
(if i.val < 925 then
(118) else
(36))) else
(if i.val < 928 then
(if i.val < 927 then
(4) else
(104)) else
(if i.val < 929 then
(76) else
(90)))))) else
(if i.val < 945 then
(if i.val < 937 then
(if i.val < 933 then
(if i.val < 931 then
(86) else
(if i.val < 932 then
(22) else
(26))) else
(if i.val < 935 then
(if i.val < 934 then
(68) else
(78)) else
(if i.val < 936 then
(101) else
(28)))) else
(if i.val < 941 then
(if i.val < 939 then
(if i.val < 938 then
(88) else
(63)) else
(if i.val < 940 then
(39) else
(3))) else
(if i.val < 943 then
(if i.val < 942 then
(51) else
(1)) else
(if i.val < 944 then
(13) else
(114))))) else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(55) else
(if i.val < 947 then
(17) else
(5))) else
(if i.val < 950 then
(if i.val < 949 then
(105) else
(74)) else
(if i.val < 951 then
(112) else
(109)))) else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
(19) else
(106)) else
(if i.val < 955 then
(111) else
(38))) else
(if i.val < 958 then
(if i.val < 957 then
(64) else
(110)) else
(if i.val < 959 then
(40) else
(96))))))))))) else
(if i.val < 1440 then
(if i.val < 1200 then
(if i.val < 1080 then
(if i.val < 1020 then
(if i.val < 990 then
(if i.val < 975 then
(if i.val < 967 then
(if i.val < 963 then
(if i.val < 961 then
(10) else
(if i.val < 962 then
(12) else
(16))) else
(if i.val < 965 then
(if i.val < 964 then
(2) else
(86)) else
(if i.val < 966 then
(22) else
(90)))) else
(if i.val < 971 then
(if i.val < 969 then
(if i.val < 968 then
(76) else
(88)) else
(if i.val < 970 then
(63) else
(39))) else
(if i.val < 973 then
(if i.val < 972 then
(28) else
(54)) else
(if i.val < 974 then
(102) else
(15))))) else
(if i.val < 982 then
(if i.val < 978 then
(if i.val < 976 then
(9) else
(if i.val < 977 then
(53) else
(0))) else
(if i.val < 980 then
(if i.val < 979 then
(8) else
(42)) else
(if i.val < 981 then
(25) else
(66)))) else
(if i.val < 986 then
(if i.val < 984 then
(if i.val < 983 then
(6) else
(43)) else
(if i.val < 985 then
(106) else
(111))) else
(if i.val < 988 then
(if i.val < 987 then
(38) else
(19)) else
(if i.val < 989 then
(68) else
(101)))))) else
(if i.val < 1005 then
(if i.val < 997 then
(if i.val < 993 then
(if i.val < 991 then
(78) else
(if i.val < 992 then
(26) else
(21))) else
(if i.val < 995 then
(if i.val < 994 then
(80) else
(79)) else
(if i.val < 996 then
(107) else
(17)))) else
(if i.val < 1001 then
(if i.val < 999 then
(if i.val < 998 then
(114) else
(55)) else
(if i.val < 1000 then
(5) else
(64))) else
(if i.val < 1003 then
(if i.val < 1002 then
(96) else
(110)) else
(if i.val < 1004 then
(40) else
(82))))) else
(if i.val < 1012 then
(if i.val < 1008 then
(if i.val < 1006 then
(20) else
(if i.val < 1007 then
(24) else
(116))) else
(if i.val < 1010 then
(if i.val < 1009 then
(4) else
(104)) else
(if i.val < 1011 then
(36) else
(118)))) else
(if i.val < 1016 then
(if i.val < 1014 then
(if i.val < 1013 then
(109) else
(74)) else
(if i.val < 1015 then
(105) else
(112))) else
(if i.val < 1018 then
(if i.val < 1017 then
(1) else
(3)) else
(if i.val < 1019 then
(51) else
(13))))))) else
(if i.val < 1050 then
(if i.val < 1035 then
(if i.val < 1027 then
(if i.val < 1023 then
(if i.val < 1021 then
(115) else
(if i.val < 1022 then
(29) else
(59))) else
(if i.val < 1025 then
(if i.val < 1024 then
(89) else
(34)) else
(if i.val < 1026 then
(48) else
(57)))) else
(if i.val < 1031 then
(if i.val < 1029 then
(if i.val < 1028 then
(72) else
(92)) else
(if i.val < 1030 then
(60) else
(99))) else
(if i.val < 1033 then
(if i.val < 1032 then
(83) else
(49)) else
(if i.val < 1034 then
(45) else
(77))))) else
(if i.val < 1042 then
(if i.val < 1038 then
(if i.val < 1036 then
(87) else
(if i.val < 1037 then
(52) else
(67))) else
(if i.val < 1040 then
(if i.val < 1039 then
(44) else
(14)) else
(if i.val < 1041 then
(58) else
(50)))) else
(if i.val < 1046 then
(if i.val < 1044 then
(if i.val < 1043 then
(81) else
(73)) else
(if i.val < 1045 then
(69) else
(27))) else
(if i.val < 1048 then
(if i.val < 1047 then
(95) else
(119)) else
(if i.val < 1049 then
(62) else
(113)))))) else
(if i.val < 1065 then
(if i.val < 1057 then
(if i.val < 1053 then
(if i.val < 1051 then
(94) else
(if i.val < 1052 then
(93) else
(7))) else
(if i.val < 1055 then
(if i.val < 1054 then
(85) else
(100)) else
(if i.val < 1056 then
(37) else
(71)))) else
(if i.val < 1061 then
(if i.val < 1059 then
(if i.val < 1058 then
(47) else
(70)) else
(if i.val < 1060 then
(46) else
(108))) else
(if i.val < 1063 then
(if i.val < 1062 then
(33) else
(23)) else
(if i.val < 1064 then
(97) else
(65))))) else
(if i.val < 1072 then
(if i.val < 1068 then
(if i.val < 1066 then
(41) else
(if i.val < 1067 then
(31) else
(103))) else
(if i.val < 1070 then
(if i.val < 1069 then
(35) else
(98)) else
(if i.val < 1071 then
(84) else
(75)))) else
(if i.val < 1076 then
(if i.val < 1074 then
(if i.val < 1073 then
(91) else
(30)) else
(if i.val < 1075 then
(61) else
(32))) else
(if i.val < 1078 then
(if i.val < 1077 then
(117) else
(11)) else
(if i.val < 1079 then
(56) else
(18)))))))) else
(if i.val < 1140 then
(if i.val < 1110 then
(if i.val < 1095 then
(if i.val < 1087 then
(if i.val < 1083 then
(if i.val < 1081 then
(96) else
(if i.val < 1082 then
(110) else
(64))) else
(if i.val < 1085 then
(if i.val < 1084 then
(40) else
(66)) else
(if i.val < 1086 then
(6) else
(25)))) else
(if i.val < 1091 then
(if i.val < 1089 then
(if i.val < 1088 then
(43) else
(80)) else
(if i.val < 1090 then
(21) else
(79))) else
(if i.val < 1093 then
(if i.val < 1092 then
(107) else
(39)) else
(if i.val < 1094 then
(88) else
(63))))) else
(if i.val < 1102 then
(if i.val < 1098 then
(if i.val < 1096 then
(28) else
(if i.val < 1097 then
(54) else
(15))) else
(if i.val < 1100 then
(if i.val < 1099 then
(9) else
(102)) else
(if i.val < 1101 then
(101) else
(78)))) else
(if i.val < 1106 then
(if i.val < 1104 then
(if i.val < 1103 then
(26) else
(68)) else
(if i.val < 1105 then
(0) else
(8))) else
(if i.val < 1108 then
(if i.val < 1107 then
(42) else
(53)) else
(if i.val < 1109 then
(20) else
(24)))))) else
(if i.val < 1125 then
(if i.val < 1117 then
(if i.val < 1113 then
(if i.val < 1111 then
(82) else
(if i.val < 1112 then
(116) else
(86))) else
(if i.val < 1115 then
(if i.val < 1114 then
(22) else
(76)) else
(if i.val < 1116 then
(90) else
(12)))) else
(if i.val < 1121 then
(if i.val < 1119 then
(if i.val < 1118 then
(10) else
(16)) else
(if i.val < 1120 then
(2) else
(112))) else
(if i.val < 1123 then
(if i.val < 1122 then
(74) else
(105)) else
(if i.val < 1124 then
(109) else
(114))))) else
(if i.val < 1132 then
(if i.val < 1128 then
(if i.val < 1126 then
(17) else
(if i.val < 1127 then
(5) else
(55))) else
(if i.val < 1130 then
(if i.val < 1129 then
(38) else
(111)) else
(if i.val < 1131 then
(19) else
(106)))) else
(if i.val < 1136 then
(if i.val < 1134 then
(if i.val < 1133 then
(104) else
(118)) else
(if i.val < 1135 then
(36) else
(4))) else
(if i.val < 1138 then
(if i.val < 1137 then
(13) else
(51)) else
(if i.val < 1139 then
(1) else
(3))))))) else
(if i.val < 1170 then
(if i.val < 1155 then
(if i.val < 1147 then
(if i.val < 1143 then
(if i.val < 1141 then
(119) else
(if i.val < 1142 then
(69) else
(95))) else
(if i.val < 1145 then
(if i.val < 1144 then
(27) else
(35)) else
(if i.val < 1146 then
(98) else
(75)))) else
(if i.val < 1151 then
(if i.val < 1149 then
(if i.val < 1148 then
(84) else
(37)) else
(if i.val < 1150 then
(100) else
(85))) else
(if i.val < 1153 then
(if i.val < 1152 then
(7) else
(91)) else
(if i.val < 1154 then
(30) else
(61))))) else
(if i.val < 1162 then
(if i.val < 1158 then
(if i.val < 1156 then
(32) else
(if i.val < 1157 then
(77) else
(49))) else
(if i.val < 1160 then
(if i.val < 1159 then
(87) else
(45)) else
(if i.val < 1161 then
(113) else
(62)))) else
(if i.val < 1166 then
(if i.val < 1164 then
(if i.val < 1163 then
(93) else
(94)) else
(if i.val < 1165 then
(83) else
(99))) else
(if i.val < 1168 then
(if i.val < 1167 then
(60) else
(92)) else
(if i.val < 1169 then
(29) else
(115)))))) else
(if i.val < 1185 then
(if i.val < 1177 then
(if i.val < 1173 then
(if i.val < 1171 then
(59) else
(if i.val < 1172 then
(89) else
(23))) else
(if i.val < 1175 then
(if i.val < 1174 then
(33) else
(97)) else
(if i.val < 1176 then
(108) else
(44)))) else
(if i.val < 1181 then
(if i.val < 1179 then
(if i.val < 1178 then
(52) else
(14)) else
(if i.val < 1180 then
(67) else
(73))) else
(if i.val < 1183 then
(if i.val < 1182 then
(50) else
(58)) else
(if i.val < 1184 then
(81) else
(70))))) else
(if i.val < 1192 then
(if i.val < 1188 then
(if i.val < 1186 then
(71) else
(if i.val < 1187 then
(47) else
(46))) else
(if i.val < 1190 then
(if i.val < 1189 then
(72) else
(57)) else
(if i.val < 1191 then
(34) else
(48)))) else
(if i.val < 1196 then
(if i.val < 1194 then
(if i.val < 1193 then
(11) else
(117)) else
(if i.val < 1195 then
(18) else
(56))) else
(if i.val < 1198 then
(if i.val < 1197 then
(65) else
(41)) else
(if i.val < 1199 then
(31) else
(103))))))))) else
(if i.val < 1320 then
(if i.val < 1260 then
(if i.val < 1230 then
(if i.val < 1215 then
(if i.val < 1207 then
(if i.val < 1203 then
(if i.val < 1201 then
(33) else
(if i.val < 1202 then
(108) else
(97))) else
(if i.val < 1205 then
(if i.val < 1204 then
(23) else
(48)) else
(if i.val < 1206 then
(57) else
(72)))) else
(if i.val < 1211 then
(if i.val < 1209 then
(if i.val < 1208 then
(34) else
(95)) else
(if i.val < 1210 then
(69) else
(119))) else
(if i.val < 1213 then
(if i.val < 1212 then
(27) else
(14)) else
(if i.val < 1214 then
(44) else
(52))))) else
(if i.val < 1222 then
(if i.val < 1218 then
(if i.val < 1216 then
(67) else
(if i.val < 1217 then
(45) else
(49))) else
(if i.val < 1220 then
(if i.val < 1219 then
(87) else
(77)) else
(if i.val < 1221 then
(50) else
(73)))) else
(if i.val < 1226 then
(if i.val < 1224 then
(if i.val < 1223 then
(81) else
(58)) else
(if i.val < 1225 then
(100) else
(7))) else
(if i.val < 1228 then
(if i.val < 1227 then
(85) else
(37)) else
(if i.val < 1229 then
(94) else
(113)))))) else
(if i.val < 1245 then
(if i.val < 1237 then
(if i.val < 1233 then
(if i.val < 1231 then
(62) else
(if i.val < 1232 then
(93) else
(83))) else
(if i.val < 1235 then
(if i.val < 1234 then
(92) else
(60)) else
(if i.val < 1236 then
(99) else
(29)))) else
(if i.val < 1241 then
(if i.val < 1239 then
(if i.val < 1238 then
(89) else
(59)) else
(if i.val < 1240 then
(115) else
(91))) else
(if i.val < 1243 then
(if i.val < 1242 then
(32) else
(30)) else
(if i.val < 1244 then
(61) else
(103))))) else
(if i.val < 1252 then
(if i.val < 1248 then
(if i.val < 1246 then
(65) else
(if i.val < 1247 then
(31) else
(41))) else
(if i.val < 1250 then
(if i.val < 1249 then
(117) else
(56)) else
(if i.val < 1251 then
(11) else
(18)))) else
(if i.val < 1256 then
(if i.val < 1254 then
(if i.val < 1253 then
(46) else
(70)) else
(if i.val < 1255 then
(71) else
(47))) else
(if i.val < 1258 then
(if i.val < 1257 then
(84) else
(75)) else
(if i.val < 1259 then
(35) else
(98))))))) else
(if i.val < 1290 then
(if i.val < 1275 then
(if i.val < 1267 then
(if i.val < 1263 then
(if i.val < 1261 then
(64) else
(if i.val < 1262 then
(40) else
(96))) else
(if i.val < 1265 then
(if i.val < 1264 then
(110) else
(3)) else
(if i.val < 1266 then
(13) else
(1)))) else
(if i.val < 1271 then
(if i.val < 1269 then
(if i.val < 1268 then
(51) else
(16)) else
(if i.val < 1270 then
(2) else
(12))) else
(if i.val < 1273 then
(if i.val < 1272 then
(10) else
(53)) else
(if i.val < 1274 then
(0) else
(8))))) else
(if i.val < 1282 then
(if i.val < 1278 then
(if i.val < 1276 then
(42) else
(if i.val < 1277 then
(63) else
(88))) else
(if i.val < 1280 then
(if i.val < 1279 then
(28) else
(39)) else
(if i.val < 1281 then
(111) else
(106)))) else
(if i.val < 1286 then
(if i.val < 1284 then
(if i.val < 1283 then
(19) else
(38)) else
(if i.val < 1285 then
(68) else
(26))) else
(if i.val < 1288 then
(if i.val < 1287 then
(78) else
(101)) else
(if i.val < 1289 then
(90) else
(76)))))) else
(if i.val < 1305 then
(if i.val < 1297 then
(if i.val < 1293 then
(if i.val < 1291 then
(86) else
(if i.val < 1292 then
(22) else
(43))) else
(if i.val < 1295 then
(if i.val < 1294 then
(25) else
(6)) else
(if i.val < 1296 then
(66) else
(80)))) else
(if i.val < 1301 then
(if i.val < 1299 then
(if i.val < 1298 then
(21) else
(107)) else
(if i.val < 1300 then
(79) else
(9))) else
(if i.val < 1303 then
(if i.val < 1302 then
(54) else
(102)) else
(if i.val < 1304 then
(15) else
(55))))) else
(if i.val < 1312 then
(if i.val < 1308 then
(if i.val < 1306 then
(114) else
(if i.val < 1307 then
(17) else
(5))) else
(if i.val < 1310 then
(if i.val < 1309 then
(105) else
(112)) else
(if i.val < 1311 then
(74) else
(109)))) else
(if i.val < 1316 then
(if i.val < 1314 then
(if i.val < 1313 then
(24) else
(82)) else
(if i.val < 1315 then
(116) else
(20))) else
(if i.val < 1318 then
(if i.val < 1317 then
(4) else
(36)) else
(if i.val < 1319 then
(104) else
(118)))))))) else
(if i.val < 1380 then
(if i.val < 1350 then
(if i.val < 1335 then
(if i.val < 1327 then
(if i.val < 1323 then
(if i.val < 1321 then
(115) else
(if i.val < 1322 then
(29) else
(89))) else
(if i.val < 1325 then
(if i.val < 1324 then
(59) else
(11)) else
(if i.val < 1326 then
(117) else
(56)))) else
(if i.val < 1331 then
(if i.val < 1329 then
(if i.val < 1328 then
(18) else
(46)) else
(if i.val < 1330 then
(70) else
(47))) else
(if i.val < 1333 then
(if i.val < 1332 then
(71) else
(7)) else
(if i.val < 1334 then
(85) else
(100))))) else
(if i.val < 1342 then
(if i.val < 1338 then
(if i.val < 1336 then
(37) else
(if i.val < 1337 then
(81) else
(58))) else
(if i.val < 1340 then
(if i.val < 1339 then
(73) else
(50)) else
(if i.val < 1341 then
(60) else
(92)))) else
(if i.val < 1346 then
(if i.val < 1344 then
(if i.val < 1343 then
(99) else
(83)) else
(if i.val < 1345 then
(30) else
(32))) else
(if i.val < 1348 then
(if i.val < 1347 then
(91) else
(61)) else
(if i.val < 1349 then
(27) else
(69)))))) else
(if i.val < 1365 then
(if i.val < 1357 then
(if i.val < 1353 then
(if i.val < 1351 then
(95) else
(if i.val < 1352 then
(119) else
(67))) else
(if i.val < 1355 then
(if i.val < 1354 then
(44) else
(52)) else
(if i.val < 1356 then
(14) else
(108)))) else
(if i.val < 1361 then
(if i.val < 1359 then
(if i.val < 1358 then
(23) else
(97)) else
(if i.val < 1360 then
(33) else
(41))) else
(if i.val < 1363 then
(if i.val < 1362 then
(31) else
(65)) else
(if i.val < 1364 then
(103) else
(113))))) else
(if i.val < 1372 then
(if i.val < 1368 then
(if i.val < 1366 then
(94) else
(if i.val < 1367 then
(62) else
(93))) else
(if i.val < 1370 then
(if i.val < 1369 then
(72) else
(34)) else
(if i.val < 1371 then
(57) else
(48)))) else
(if i.val < 1376 then
(if i.val < 1374 then
(if i.val < 1373 then
(87) else
(49)) else
(if i.val < 1375 then
(77) else
(45))) else
(if i.val < 1378 then
(if i.val < 1377 then
(75) else
(84)) else
(if i.val < 1379 then
(98) else
(35))))))) else
(if i.val < 1410 then
(if i.val < 1395 then
(if i.val < 1387 then
(if i.val < 1383 then
(if i.val < 1381 then
(13) else
(if i.val < 1382 then
(1) else
(3))) else
(if i.val < 1385 then
(if i.val < 1384 then
(51) else
(42)) else
(if i.val < 1386 then
(53) else
(8)))) else
(if i.val < 1391 then
(if i.val < 1389 then
(if i.val < 1388 then
(0) else
(2)) else
(if i.val < 1390 then
(16) else
(12))) else
(if i.val < 1393 then
(if i.val < 1392 then
(10) else
(9)) else
(if i.val < 1394 then
(102) else
(15))))) else
(if i.val < 1402 then
(if i.val < 1398 then
(if i.val < 1396 then
(54) else
(if i.val < 1397 then
(79) else
(107))) else
(if i.val < 1400 then
(if i.val < 1399 then
(21) else
(80)) else
(if i.val < 1401 then
(96) else
(40)))) else
(if i.val < 1406 then
(if i.val < 1404 then
(if i.val < 1403 then
(64) else
(110)) else
(if i.val < 1405 then
(55) else
(5))) else
(if i.val < 1408 then
(if i.val < 1407 then
(17) else
(114)) else
(if i.val < 1409 then
(28) else
(63)))))) else
(if i.val < 1425 then
(if i.val < 1417 then
(if i.val < 1413 then
(if i.val < 1411 then
(88) else
(if i.val < 1412 then
(39) else
(20))) else
(if i.val < 1415 then
(if i.val < 1414 then
(24) else
(116)) else
(if i.val < 1416 then
(82) else
(36)))) else
(if i.val < 1421 then
(if i.val < 1419 then
(if i.val < 1418 then
(118) else
(4)) else
(if i.val < 1420 then
(104) else
(25))) else
(if i.val < 1423 then
(if i.val < 1422 then
(66) else
(43)) else
(if i.val < 1424 then
(6) else
(112))))) else
(if i.val < 1432 then
(if i.val < 1428 then
(if i.val < 1426 then
(105) else
(if i.val < 1427 then
(109) else
(74))) else
(if i.val < 1430 then
(if i.val < 1429 then
(78) else
(68)) else
(if i.val < 1431 then
(101) else
(26)))) else
(if i.val < 1436 then
(if i.val < 1434 then
(if i.val < 1433 then
(86) else
(90)) else
(if i.val < 1435 then
(22) else
(76))) else
(if i.val < 1438 then
(if i.val < 1437 then
(106) else
(19)) else
(if i.val < 1439 then
(111) else
(38)))))))))) else
(if i.val < 1680 then
(if i.val < 1560 then
(if i.val < 1500 then
(if i.val < 1470 then
(if i.val < 1455 then
(if i.val < 1447 then
(if i.val < 1443 then
(if i.val < 1441 then
(77) else
(if i.val < 1442 then
(49) else
(87))) else
(if i.val < 1445 then
(if i.val < 1444 then
(45) else
(29)) else
(if i.val < 1446 then
(115) else
(59)))) else
(if i.val < 1451 then
(if i.val < 1449 then
(if i.val < 1448 then
(89) else
(18)) else
(if i.val < 1450 then
(11) else
(117))) else
(if i.val < 1453 then
(if i.val < 1452 then
(56) else
(41)) else
(if i.val < 1454 then
(31) else
(65))))) else
(if i.val < 1462 then
(if i.val < 1458 then
(if i.val < 1456 then
(103) else
(if i.val < 1457 then
(113) else
(62))) else
(if i.val < 1460 then
(if i.val < 1459 then
(93) else
(94)) else
(if i.val < 1461 then
(108) else
(33)))) else
(if i.val < 1466 then
(if i.val < 1464 then
(if i.val < 1463 then
(23) else
(97)) else
(if i.val < 1465 then
(37) else
(85))) else
(if i.val < 1468 then
(if i.val < 1467 then
(100) else
(7)) else
(if i.val < 1469 then
(71) else
(46)))))) else
(if i.val < 1485 then
(if i.val < 1477 then
(if i.val < 1473 then
(if i.val < 1471 then
(70) else
(if i.val < 1472 then
(47) else
(48))) else
(if i.val < 1475 then
(if i.val < 1474 then
(34) else
(57)) else
(if i.val < 1476 then
(72) else
(75)))) else
(if i.val < 1481 then
(if i.val < 1479 then
(if i.val < 1478 then
(98) else
(35)) else
(if i.val < 1480 then
(84) else
(32))) else
(if i.val < 1483 then
(if i.val < 1482 then
(30) else
(61)) else
(if i.val < 1484 then
(91) else
(60))))) else
(if i.val < 1492 then
(if i.val < 1488 then
(if i.val < 1486 then
(83) else
(if i.val < 1487 then
(99) else
(92))) else
(if i.val < 1490 then
(if i.val < 1489 then
(119) else
(95)) else
(if i.val < 1491 then
(69) else
(27)))) else
(if i.val < 1496 then
(if i.val < 1494 then
(if i.val < 1493 then
(67) else
(14)) else
(if i.val < 1495 then
(52) else
(44))) else
(if i.val < 1498 then
(if i.val < 1497 then
(73) else
(58)) else
(if i.val < 1499 then
(81) else
(50))))))) else
(if i.val < 1530 then
(if i.val < 1515 then
(if i.val < 1507 then
(if i.val < 1503 then
(if i.val < 1501 then
(6) else
(if i.val < 1502 then
(25) else
(43))) else
(if i.val < 1505 then
(if i.val < 1504 then
(66) else
(102)) else
(if i.val < 1506 then
(15) else
(54)))) else
(if i.val < 1511 then
(if i.val < 1509 then
(if i.val < 1508 then
(9) else
(55)) else
(if i.val < 1510 then
(5) else
(17))) else
(if i.val < 1513 then
(if i.val < 1512 then
(114) else
(13)) else
(if i.val < 1514 then
(1) else
(3))))) else
(if i.val < 1522 then
(if i.val < 1518 then
(if i.val < 1516 then
(51) else
(if i.val < 1517 then
(40) else
(110))) else
(if i.val < 1520 then
(if i.val < 1519 then
(96) else
(64)) else
(if i.val < 1521 then
(10) else
(2)))) else
(if i.val < 1526 then
(if i.val < 1524 then
(if i.val < 1523 then
(16) else
(12)) else
(if i.val < 1525 then
(0) else
(8))) else
(if i.val < 1528 then
(if i.val < 1527 then
(53) else
(42)) else
(if i.val < 1529 then
(74) else
(112)))))) else
(if i.val < 1545 then
(if i.val < 1537 then
(if i.val < 1533 then
(if i.val < 1531 then
(109) else
(if i.val < 1532 then
(105) else
(76))) else
(if i.val < 1535 then
(if i.val < 1534 then
(86) else
(90)) else
(if i.val < 1536 then
(22) else
(38)))) else
(if i.val < 1541 then
(if i.val < 1539 then
(if i.val < 1538 then
(106) else
(19)) else
(if i.val < 1540 then
(111) else
(88))) else
(if i.val < 1543 then
(if i.val < 1542 then
(28) else
(63)) else
(if i.val < 1544 then
(39) else
(24))))) else
(if i.val < 1552 then
(if i.val < 1548 then
(if i.val < 1546 then
(82) else
(if i.val < 1547 then
(116) else
(20))) else
(if i.val < 1550 then
(if i.val < 1549 then
(21) else
(107)) else
(if i.val < 1551 then
(79) else
(80)))) else
(if i.val < 1556 then
(if i.val < 1554 then
(if i.val < 1553 then
(78) else
(26)) else
(if i.val < 1555 then
(101) else
(68))) else
(if i.val < 1558 then
(if i.val < 1557 then
(104) else
(118)) else
(if i.val < 1559 then
(4) else
(36)))))))) else
(if i.val < 1620 then
(if i.val < 1590 then
(if i.val < 1575 then
(if i.val < 1567 then
(if i.val < 1563 then
(if i.val < 1561 then
(92) else
(if i.val < 1562 then
(83) else
(99))) else
(if i.val < 1565 then
(if i.val < 1564 then
(60) else
(113)) else
(if i.val < 1566 then
(94) else
(62)))) else
(if i.val < 1571 then
(if i.val < 1569 then
(if i.val < 1568 then
(93) else
(52)) else
(if i.val < 1570 then
(14) else
(44))) else
(if i.val < 1573 then
(if i.val < 1572 then
(67) else
(57)) else
(if i.val < 1574 then
(34) else
(48))))) else
(if i.val < 1582 then
(if i.val < 1578 then
(if i.val < 1576 then
(72) else
(if i.val < 1577 then
(97) else
(33))) else
(if i.val < 1580 then
(if i.val < 1579 then
(23) else
(108)) else
(if i.val < 1581 then
(37) else
(85)))) else
(if i.val < 1586 then
(if i.val < 1584 then
(if i.val < 1583 then
(7) else
(100)) else
(if i.val < 1585 then
(11) else
(18))) else
(if i.val < 1588 then
(if i.val < 1587 then
(56) else
(117)) else
(if i.val < 1589 then
(81) else
(50)))))) else
(if i.val < 1605 then
(if i.val < 1597 then
(if i.val < 1593 then
(if i.val < 1591 then
(73) else
(if i.val < 1592 then
(58) else
(35))) else
(if i.val < 1595 then
(if i.val < 1594 then
(98) else
(75)) else
(if i.val < 1596 then
(84) else
(31)))) else
(if i.val < 1601 then
(if i.val < 1599 then
(if i.val < 1598 then
(41) else
(65)) else
(if i.val < 1600 then
(103) else
(69))) else
(if i.val < 1603 then
(if i.val < 1602 then
(119) else
(27)) else
(if i.val < 1604 then
(95) else
(47))))) else
(if i.val < 1612 then
(if i.val < 1608 then
(if i.val < 1606 then
(71) else
(if i.val < 1607 then
(70) else
(46))) else
(if i.val < 1610 then
(if i.val < 1609 then
(89) else
(115)) else
(if i.val < 1611 then
(29) else
(59)))) else
(if i.val < 1616 then
(if i.val < 1614 then
(if i.val < 1613 then
(61) else
(32)) else
(if i.val < 1615 then
(91) else
(30))) else
(if i.val < 1618 then
(if i.val < 1617 then
(45) else
(49)) else
(if i.val < 1619 then
(87) else
(77))))))) else
(if i.val < 1650 then
(if i.val < 1635 then
(if i.val < 1627 then
(if i.val < 1623 then
(if i.val < 1621 then
(93) else
(if i.val < 1622 then
(113) else
(62))) else
(if i.val < 1625 then
(if i.val < 1624 then
(94) else
(81)) else
(if i.val < 1626 then
(73) else
(50)))) else
(if i.val < 1631 then
(if i.val < 1629 then
(if i.val < 1628 then
(58) else
(47)) else
(if i.val < 1630 then
(71) else
(46))) else
(if i.val < 1633 then
(if i.val < 1632 then
(70) else
(100)) else
(if i.val < 1634 then
(85) else
(37))))) else
(if i.val < 1642 then
(if i.val < 1638 then
(if i.val < 1636 then
(7) else
(if i.val < 1637 then
(87) else
(45))) else
(if i.val < 1640 then
(if i.val < 1639 then
(77) else
(49)) else
(if i.val < 1641 then
(89) else
(29)))) else
(if i.val < 1646 then
(if i.val < 1644 then
(if i.val < 1643 then
(115) else
(59)) else
(if i.val < 1645 then
(67) else
(44))) else
(if i.val < 1648 then
(if i.val < 1647 then
(52) else
(14)) else
(if i.val < 1649 then
(98) else
(35)))))) else
(if i.val < 1665 then
(if i.val < 1657 then
(if i.val < 1653 then
(if i.val < 1651 then
(84) else
(if i.val < 1652 then
(75) else
(23))) else
(if i.val < 1655 then
(if i.val < 1654 then
(97) else
(33)) else
(if i.val < 1656 then
(108) else
(34)))) else
(if i.val < 1661 then
(if i.val < 1659 then
(if i.val < 1658 then
(57) else
(48)) else
(if i.val < 1660 then
(72) else
(30))) else
(if i.val < 1663 then
(if i.val < 1662 then
(61) else
(91)) else
(if i.val < 1664 then
(32) else
(11))))) else
(if i.val < 1672 then
(if i.val < 1668 then
(if i.val < 1666 then
(56) else
(if i.val < 1667 then
(117) else
(18))) else
(if i.val < 1670 then
(if i.val < 1669 then
(92) else
(99)) else
(if i.val < 1671 then
(60) else
(83)))) else
(if i.val < 1676 then
(if i.val < 1674 then
(if i.val < 1673 then
(31) else
(65)) else
(if i.val < 1675 then
(103) else
(41))) else
(if i.val < 1678 then
(if i.val < 1677 then
(95) else
(119)) else
(if i.val < 1679 then
(69) else
(27))))))))) else
(if i.val < 1800 then
(if i.val < 1740 then
(if i.val < 1710 then
(if i.val < 1695 then
(if i.val < 1687 then
(if i.val < 1683 then
(if i.val < 1681 then
(29) else
(if i.val < 1682 then
(89) else
(59))) else
(if i.val < 1685 then
(if i.val < 1684 then
(115) else
(47)) else
(if i.val < 1686 then
(70) else
(71)))) else
(if i.val < 1691 then
(if i.val < 1689 then
(if i.val < 1688 then
(46) else
(45)) else
(if i.val < 1690 then
(49) else
(77))) else
(if i.val < 1693 then
(if i.val < 1692 then
(87) else
(83)) else
(if i.val < 1694 then
(60) else
(92))))) else
(if i.val < 1702 then
(if i.val < 1698 then
(if i.val < 1696 then
(99) else
(if i.val < 1697 then
(23) else
(97))) else
(if i.val < 1700 then
(if i.val < 1699 then
(108) else
(33)) else
(if i.val < 1701 then
(58) else
(81)))) else
(if i.val < 1706 then
(if i.val < 1704 then
(if i.val < 1703 then
(50) else
(73)) else
(if i.val < 1705 then
(11) else
(56))) else
(if i.val < 1708 then
(if i.val < 1707 then
(117) else
(18)) else
(if i.val < 1709 then
(98) else
(35)))))) else
(if i.val < 1725 then
(if i.val < 1717 then
(if i.val < 1713 then
(if i.val < 1711 then
(75) else
(if i.val < 1712 then
(84) else
(44))) else
(if i.val < 1715 then
(if i.val < 1714 then
(14) else
(67)) else
(if i.val < 1716 then
(52) else
(31)))) else
(if i.val < 1721 then
(if i.val < 1719 then
(if i.val < 1718 then
(103) else
(65)) else
(if i.val < 1720 then
(41) else
(57))) else
(if i.val < 1723 then
(if i.val < 1722 then
(48) else
(72)) else
(if i.val < 1724 then
(34) else
(30))))) else
(if i.val < 1732 then
(if i.val < 1728 then
(if i.val < 1726 then
(61) else
(if i.val < 1727 then
(91) else
(32))) else
(if i.val < 1730 then
(if i.val < 1729 then
(69) else
(119)) else
(if i.val < 1731 then
(27) else
(95)))) else
(if i.val < 1736 then
(if i.val < 1734 then
(if i.val < 1733 then
(94) else
(93)) else
(if i.val < 1735 then
(113) else
(62))) else
(if i.val < 1738 then
(if i.val < 1737 then
(100) else
(7)) else
(if i.val < 1739 then
(37) else
(85))))))) else
(if i.val < 1770 then
(if i.val < 1755 then
(if i.val < 1747 then
(if i.val < 1743 then
(if i.val < 1741 then
(107) else
(if i.val < 1742 then
(79) else
(80))) else
(if i.val < 1745 then
(if i.val < 1744 then
(21) else
(20)) else
(if i.val < 1746 then
(24) else
(82)))) else
(if i.val < 1751 then
(if i.val < 1749 then
(if i.val < 1748 then
(116) else
(5)) else
(if i.val < 1750 then
(55) else
(114))) else
(if i.val < 1753 then
(if i.val < 1752 then
(17) else
(86)) else
(if i.val < 1754 then
(22) else
(90))))) else
(if i.val < 1762 then
(if i.val < 1758 then
(if i.val < 1756 then
(76) else
(if i.val < 1757 then
(66) else
(6))) else
(if i.val < 1760 then
(if i.val < 1759 then
(25) else
(43)) else
(if i.val < 1761 then
(106) else
(111)))) else
(if i.val < 1766 then
(if i.val < 1764 then
(if i.val < 1763 then
(19) else
(38)) else
(if i.val < 1765 then
(54) else
(15))) else
(if i.val < 1768 then
(if i.val < 1767 then
(9) else
(102)) else
(if i.val < 1769 then
(109) else
(105)))))) else
(if i.val < 1785 then
(if i.val < 1777 then
(if i.val < 1773 then
(if i.val < 1771 then
(112) else
(if i.val < 1772 then
(74) else
(39))) else
(if i.val < 1775 then
(if i.val < 1774 then
(88) else
(63)) else
(if i.val < 1776 then
(28) else
(104)))) else
(if i.val < 1781 then
(if i.val < 1779 then
(if i.val < 1778 then
(4) else
(36)) else
(if i.val < 1780 then
(118) else
(51))) else
(if i.val < 1783 then
(if i.val < 1782 then
(13) else
(3)) else
(if i.val < 1784 then
(1) else
(0))))) else
(if i.val < 1792 then
(if i.val < 1788 then
(if i.val < 1786 then
(8) else
(if i.val < 1787 then
(42) else
(53))) else
(if i.val < 1790 then
(if i.val < 1789 then
(10) else
(16)) else
(if i.val < 1791 then
(12) else
(2)))) else
(if i.val < 1796 then
(if i.val < 1794 then
(if i.val < 1793 then
(78) else
(101)) else
(if i.val < 1795 then
(26) else
(68))) else
(if i.val < 1798 then
(if i.val < 1797 then
(96) else
(40)) else
(if i.val < 1799 then
(110) else
(64)))))))) else
(if i.val < 1860 then
(if i.val < 1830 then
(if i.val < 1815 then
(if i.val < 1807 then
(if i.val < 1803 then
(if i.val < 1801 then
(70) else
(if i.val < 1802 then
(46) else
(47))) else
(if i.val < 1805 then
(if i.val < 1804 then
(71) else
(56)) else
(if i.val < 1806 then
(11) else
(18)))) else
(if i.val < 1811 then
(if i.val < 1809 then
(if i.val < 1808 then
(117) else
(115)) else
(if i.val < 1810 then
(29) else
(89))) else
(if i.val < 1813 then
(if i.val < 1812 then
(59) else
(75)) else
(if i.val < 1814 then
(84) else
(98))))) else
(if i.val < 1822 then
(if i.val < 1818 then
(if i.val < 1816 then
(35) else
(if i.val < 1817 then
(91) else
(32))) else
(if i.val < 1820 then
(if i.val < 1819 then
(61) else
(30)) else
(if i.val < 1821 then
(108) else
(33)))) else
(if i.val < 1826 then
(if i.val < 1824 then
(if i.val < 1823 then
(23) else
(97)) else
(if i.val < 1825 then
(95) else
(27))) else
(if i.val < 1828 then
(if i.val < 1827 then
(69) else
(119)) else
(if i.val < 1829 then
(62) else
(113)))))) else
(if i.val < 1845 then
(if i.val < 1837 then
(if i.val < 1833 then
(if i.val < 1831 then
(93) else
(if i.val < 1832 then
(94) else
(87))) else
(if i.val < 1835 then
(if i.val < 1834 then
(77) else
(49)) else
(if i.val < 1836 then
(45) else
(58)))) else
(if i.val < 1841 then
(if i.val < 1839 then
(if i.val < 1838 then
(81) else
(50)) else
(if i.val < 1840 then
(73) else
(103))) else
(if i.val < 1843 then
(if i.val < 1842 then
(41) else
(65)) else
(if i.val < 1844 then
(31) else
(44))))) else
(if i.val < 1852 then
(if i.val < 1848 then
(if i.val < 1846 then
(52) else
(if i.val < 1847 then
(67) else
(14))) else
(if i.val < 1850 then
(if i.val < 1849 then
(7) else
(85)) else
(if i.val < 1851 then
(100) else
(37)))) else
(if i.val < 1856 then
(if i.val < 1854 then
(if i.val < 1853 then
(92) else
(99)) else
(if i.val < 1855 then
(83) else
(60))) else
(if i.val < 1858 then
(if i.val < 1857 then
(72) else
(34)) else
(if i.val < 1859 then
(57) else
(48))))))) else
(if i.val < 1890 then
(if i.val < 1875 then
(if i.val < 1867 then
(if i.val < 1863 then
(if i.val < 1861 then
(81) else
(if i.val < 1862 then
(50) else
(58))) else
(if i.val < 1865 then
(if i.val < 1864 then
(73) else
(59)) else
(if i.val < 1866 then
(29) else
(115)))) else
(if i.val < 1871 then
(if i.val < 1869 then
(if i.val < 1868 then
(89) else
(27)) else
(if i.val < 1870 then
(69) else
(95))) else
(if i.val < 1873 then
(if i.val < 1872 then
(119) else
(103)) else
(if i.val < 1874 then
(41) else
(65))))) else
(if i.val < 1882 then
(if i.val < 1878 then
(if i.val < 1876 then
(31) else
(if i.val < 1877 then
(84) else
(98))) else
(if i.val < 1880 then
(if i.val < 1879 then
(75) else
(35)) else
(if i.val < 1881 then
(45) else
(87)))) else
(if i.val < 1886 then
(if i.val < 1884 then
(if i.val < 1883 then
(49) else
(77)) else
(if i.val < 1885 then
(113) else
(62))) else
(if i.val < 1888 then
(if i.val < 1887 then
(93) else
(94)) else
(if i.val < 1889 then
(92) else
(83)))))) else
(if i.val < 1905 then
(if i.val < 1897 then
(if i.val < 1893 then
(if i.val < 1891 then
(60) else
(if i.val < 1892 then
(99) else
(56))) else
(if i.val < 1895 then
(if i.val < 1894 then
(117) else
(18)) else
(if i.val < 1896 then
(11) else
(14)))) else
(if i.val < 1901 then
(if i.val < 1899 then
(if i.val < 1898 then
(44) else
(67)) else
(if i.val < 1900 then
(52) else
(70))) else
(if i.val < 1903 then
(if i.val < 1902 then
(47) else
(71)) else
(if i.val < 1904 then
(46) else
(37))))) else
(if i.val < 1912 then
(if i.val < 1908 then
(if i.val < 1906 then
(100) else
(if i.val < 1907 then
(85) else
(7))) else
(if i.val < 1910 then
(if i.val < 1909 then
(34) else
(72)) else
(if i.val < 1911 then
(57) else
(48)))) else
(if i.val < 1916 then
(if i.val < 1914 then
(if i.val < 1913 then
(33) else
(108)) else
(if i.val < 1915 then
(97) else
(23))) else
(if i.val < 1918 then
(if i.val < 1917 then
(30) else
(32)) else
(if i.val < 1919 then
(61) else
(91))))))))))) : Nat) % 120, Nat.mod_lt _ (by decide)⟩

/-- An explicit candidate word for each final survivor. -/
def witness (i : Fin 1920) : C :=
  kernelHom (coordinates (kernelCode i)) * representative (representativeIndex i)

theorem witness_mem (i : Fin 1920) : witness i ∈ candidate :=
  candidate.mul_mem (kernel_le_candidate ⟨coordinates (kernelCode i), rfl⟩)
    (representative_mem (representativeIndex i))

def fastWitness (i : Fin 1920) : Perm :=
  fastKernel (kernelCode i) * fastRepresentative (representativeIndex i)

theorem fastWitness_eq (i : Fin 1920) : fastWitness i = (witness i).val.val := by
  change fastKernel (kernelCode i) * fastRepresentative (representativeIndex i) =
    (kernelHom (coordinates (kernelCode i))).val.val *
      (representative (representativeIndex i)).val.val
  rw [fastKernel_eq, fastRepresentative_eq]

def survivorCheck (b : Fin 60) : Prop :=
  ∀ (i : Fin 32) (x : Fin 100),
    prefix6 (blockIndex b i) x = fastWitness (blockIndex b i) x

theorem survivor_block0 : survivorCheck 0 := by
  apply allFin
  decide +kernel

theorem survivor_block1 : survivorCheck 1 := by
  apply allFin
  decide +kernel

theorem survivor_block2 : survivorCheck 2 := by
  apply allFin
  decide +kernel

theorem survivor_block3 : survivorCheck 3 := by
  apply allFin
  decide +kernel

theorem survivor_block4 : survivorCheck 4 := by
  apply allFin
  decide +kernel

theorem survivor_block5 : survivorCheck 5 := by
  apply allFin
  decide +kernel

theorem survivor_block6 : survivorCheck 6 := by
  apply allFin
  decide +kernel

theorem survivor_block7 : survivorCheck 7 := by
  apply allFin
  decide +kernel

theorem survivor_block8 : survivorCheck 8 := by
  apply allFin
  decide +kernel

theorem survivor_block9 : survivorCheck 9 := by
  apply allFin
  decide +kernel

theorem survivor_block10 : survivorCheck 10 := by
  apply allFin
  decide +kernel

theorem survivor_block11 : survivorCheck 11 := by
  apply allFin
  decide +kernel

theorem survivor_block12 : survivorCheck 12 := by
  apply allFin
  decide +kernel

theorem survivor_block13 : survivorCheck 13 := by
  apply allFin
  decide +kernel

theorem survivor_block14 : survivorCheck 14 := by
  apply allFin
  decide +kernel

theorem survivor_block15 : survivorCheck 15 := by
  apply allFin
  decide +kernel

theorem survivor_block16 : survivorCheck 16 := by
  apply allFin
  decide +kernel

theorem survivor_block17 : survivorCheck 17 := by
  apply allFin
  decide +kernel

theorem survivor_block18 : survivorCheck 18 := by
  apply allFin
  decide +kernel

theorem survivor_block19 : survivorCheck 19 := by
  apply allFin
  decide +kernel

theorem survivor_block20 : survivorCheck 20 := by
  apply allFin
  decide +kernel

theorem survivor_block21 : survivorCheck 21 := by
  apply allFin
  decide +kernel

theorem survivor_block22 : survivorCheck 22 := by
  apply allFin
  decide +kernel

theorem survivor_block23 : survivorCheck 23 := by
  apply allFin
  decide +kernel

theorem survivor_block24 : survivorCheck 24 := by
  apply allFin
  decide +kernel

theorem survivor_block25 : survivorCheck 25 := by
  apply allFin
  decide +kernel

theorem survivor_block26 : survivorCheck 26 := by
  apply allFin
  decide +kernel

theorem survivor_block27 : survivorCheck 27 := by
  apply allFin
  decide +kernel

theorem survivor_block28 : survivorCheck 28 := by
  apply allFin
  decide +kernel

theorem survivor_block29 : survivorCheck 29 := by
  apply allFin
  decide +kernel

theorem survivor_block30 : survivorCheck 30 := by
  apply allFin
  decide +kernel

theorem survivor_block31 : survivorCheck 31 := by
  apply allFin
  decide +kernel

theorem survivor_block32 : survivorCheck 32 := by
  apply allFin
  decide +kernel

theorem survivor_block33 : survivorCheck 33 := by
  apply allFin
  decide +kernel

theorem survivor_block34 : survivorCheck 34 := by
  apply allFin
  decide +kernel

theorem survivor_block35 : survivorCheck 35 := by
  apply allFin
  decide +kernel

theorem survivor_block36 : survivorCheck 36 := by
  apply allFin
  decide +kernel

theorem survivor_block37 : survivorCheck 37 := by
  apply allFin
  decide +kernel

theorem survivor_block38 : survivorCheck 38 := by
  apply allFin
  decide +kernel

theorem survivor_block39 : survivorCheck 39 := by
  apply allFin
  decide +kernel

theorem survivor_block40 : survivorCheck 40 := by
  apply allFin
  decide +kernel

theorem survivor_block41 : survivorCheck 41 := by
  apply allFin
  decide +kernel

theorem survivor_block42 : survivorCheck 42 := by
  apply allFin
  decide +kernel

theorem survivor_block43 : survivorCheck 43 := by
  apply allFin
  decide +kernel

theorem survivor_block44 : survivorCheck 44 := by
  apply allFin
  decide +kernel

theorem survivor_block45 : survivorCheck 45 := by
  apply allFin
  decide +kernel

theorem survivor_block46 : survivorCheck 46 := by
  apply allFin
  decide +kernel

theorem survivor_block47 : survivorCheck 47 := by
  apply allFin
  decide +kernel

theorem survivor_block48 : survivorCheck 48 := by
  apply allFin
  decide +kernel

theorem survivor_block49 : survivorCheck 49 := by
  apply allFin
  decide +kernel

theorem survivor_block50 : survivorCheck 50 := by
  apply allFin
  decide +kernel

theorem survivor_block51 : survivorCheck 51 := by
  apply allFin
  decide +kernel

theorem survivor_block52 : survivorCheck 52 := by
  apply allFin
  decide +kernel

theorem survivor_block53 : survivorCheck 53 := by
  apply allFin
  decide +kernel

theorem survivor_block54 : survivorCheck 54 := by
  apply allFin
  decide +kernel

theorem survivor_block55 : survivorCheck 55 := by
  apply allFin
  decide +kernel

theorem survivor_block56 : survivorCheck 56 := by
  apply allFin
  decide +kernel

theorem survivor_block57 : survivorCheck 57 := by
  apply allFin
  decide +kernel

theorem survivor_block58 : survivorCheck 58 := by
  apply allFin
  decide +kernel

theorem survivor_block59 : survivorCheck 59 := by
  apply allFin
  decide +kernel

theorem survivor_blocks (b : Fin 60) : survivorCheck b := by
  fin_cases b
  · exact survivor_block0
  · exact survivor_block1
  · exact survivor_block2
  · exact survivor_block3
  · exact survivor_block4
  · exact survivor_block5
  · exact survivor_block6
  · exact survivor_block7
  · exact survivor_block8
  · exact survivor_block9
  · exact survivor_block10
  · exact survivor_block11
  · exact survivor_block12
  · exact survivor_block13
  · exact survivor_block14
  · exact survivor_block15
  · exact survivor_block16
  · exact survivor_block17
  · exact survivor_block18
  · exact survivor_block19
  · exact survivor_block20
  · exact survivor_block21
  · exact survivor_block22
  · exact survivor_block23
  · exact survivor_block24
  · exact survivor_block25
  · exact survivor_block26
  · exact survivor_block27
  · exact survivor_block28
  · exact survivor_block29
  · exact survivor_block30
  · exact survivor_block31
  · exact survivor_block32
  · exact survivor_block33
  · exact survivor_block34
  · exact survivor_block35
  · exact survivor_block36
  · exact survivor_block37
  · exact survivor_block38
  · exact survivor_block39
  · exact survivor_block40
  · exact survivor_block41
  · exact survivor_block42
  · exact survivor_block43
  · exact survivor_block44
  · exact survivor_block45
  · exact survivor_block46
  · exact survivor_block47
  · exact survivor_block48
  · exact survivor_block49
  · exact survivor_block50
  · exact survivor_block51
  · exact survivor_block52
  · exact survivor_block53
  · exact survivor_block54
  · exact survivor_block55
  · exact survivor_block56
  · exact survivor_block57
  · exact survivor_block58
  · exact survivor_block59

/-- The exhaustive computation uses the identified fast permutation tables. -/
theorem survivor_fast_pointwise : ∀ (i : Fin 1920) (x : Fin 100),
    prefix6 i x = fastWitness i x := by
  apply allFin_blocks (t := 60)
  exact survivor_blocks

/-- Every survivor equals its candidate word on all one hundred letters. -/
theorem survivor_word_pointwise (i : Fin 1920) (x : Fin 100) :
    prefix6 i x = (witness i).val.val x := by
  rw [← fastWitness_eq]
  exact survivor_fast_pointwise i x

theorem survivor_word (i : Fin 1920) : prefix6 i = (witness i).val.val := by
  apply Equiv.ext
  exact survivor_word_pointwise i

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.ElementaryCentralizer.Coverage
