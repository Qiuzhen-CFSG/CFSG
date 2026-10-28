module

public meta import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.WordLiteral
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Data
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.RecoveryRules
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.ReducedData

/-!
# Recovering every eliminated Schreier generator

The signed elimination equations recover subgroup membership in reverse order.
The subgroup is arbitrary: no normal closure or quotient is involved.

Source: John Bray, ATLAS `HeG1-P1.M`; the retained 17-generator trace and
the untrusted producer are documented in `TietzeTransfer/source/README.md`.
-/

@[expose] public section

namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Membership
open Replay

open Data Theory.GroupTheory.CosetEnumeration

variable {G : Type*} [Group G] {g : Nat → G}
variable (H : Subgroup G) (hv : ValidBefore g db factCount)
variable (hs : ∀ a : Fin 17, g (Reduced.originalLabel a) ∈ H)
include hv hs

omit hv in
private theorem m1 : g 1 ∈ H := hs 0

omit hv in
private theorem m2 : g 2 ∈ H := hs 1

omit hv in
private theorem m3 : g 3 ∈ H := hs 2

omit hv in
private theorem m23 : g 23 ∈ H := hs 3

omit hv in
private theorem m235 : g 235 ∈ H := hs 4

omit hv in
private theorem m273 : g 273 ∈ H := hs 5

omit hv in
private theorem m348 : g 348 ∈ H := hs 6

omit hv in
private theorem m422 : g 422 ∈ H := hs 7

omit hv in
private theorem m480 : g 480 ∈ H := hs 8

omit hv in
private theorem m688 : g 688 ∈ H := hs 9

omit hv in
private theorem m906 : g 906 ∈ H := hs 10

omit hv in
private theorem m1041 : g 1041 ∈ H := hs 11

omit hv in
private theorem m1106 : g 1106 ∈ H := hs 12

omit hv in
private theorem m1115 : g 1115 ∈ H := hs 13

omit hv in
private theorem m1772 : g 1772 ∈ H := hs 14

omit hv in
private theorem m1958 : g 1958 ∈ H := hs 15

omit hv in
private theorem m1972 : g 1972 ∈ H := hs 16

omit hs in
private theorem m1194 : g 1194 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 4 (by decide))
    H.one_mem

omit hs in
private theorem m1333 : g 1333 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 9 (by decide))
    H.one_mem

omit hs in
private theorem m7 : g 7 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 12 (by decide))
    H.one_mem

omit hs in
private theorem m833 : g 833 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 18 (by decide))
    H.one_mem

omit hs in
private theorem m9 : g 9 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 21 (by decide))
    H.one_mem

omit hs in
private theorem m2060 : g 2060 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 22 (by decide))
    H.one_mem

omit hs in
private theorem m1423 : g 1423 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 35 (by decide))
    H.one_mem

omit hs in
private theorem m1713 : g 1713 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 36 (by decide))
    H.one_mem

omit hs in
private theorem m13 : g 13 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 41 (by decide))
    H.one_mem

omit hs in
private theorem m1461 : g 1461 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 46 (by decide))
    H.one_mem

omit hs in
private theorem m15 : g 15 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 47 (by decide))
    H.one_mem

omit hs in
private theorem m353 : g 353 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 50 (by decide))
    H.one_mem

omit hs in
private theorem m1742 : g 1742 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 51 (by decide))
    H.one_mem

omit hs in
private theorem m577 : g 577 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 56 (by decide))
    H.one_mem

omit hs in
private theorem m1763 : g 1763 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 57 (by decide))
    H.one_mem

omit hs in
private theorem m283 : g 283 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 62 (by decide))
    H.one_mem

omit hs in
private theorem m1324 : g 1324 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 63 (by decide))
    H.one_mem

omit hs in
private theorem m16 : g 16 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 66 (by decide))
    H.one_mem

omit hs in
private theorem m17 : g 17 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 70 (by decide))
    H.one_mem

omit hs in
private theorem m18 : g 18 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 76 (by decide))
    H.one_mem

omit hs in
private theorem m21 : g 21 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 88 (by decide))
    H.one_mem

private theorem m1609 : g 1609 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-23")) (hv 4734 (by decide))
    (H.mul_mem (H.inv_mem (m23 H hs)) H.one_mem)

omit hs in
private theorem m25 : g 25 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 99 (by decide))
    H.one_mem

omit hs in
private theorem m26 : g 26 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 106 (by decide))
    H.one_mem

omit hs in
private theorem m132 : g 132 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 111 (by decide))
    H.one_mem

omit hs in
private theorem m1230 : g 1230 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 118 (by decide))
    H.one_mem

omit hs in
private theorem m29 : g 29 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 119 (by decide))
    H.one_mem

omit hs in
private theorem m32 : g 32 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 127 (by decide))
    H.one_mem

omit hs in
private theorem m34 : g 34 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 130 (by decide))
    H.one_mem

omit hs in
private theorem m35 : g 35 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 135 (by decide))
    H.one_mem

omit hs in
private theorem m797 : g 797 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 139 (by decide))
    H.one_mem

omit hs in
private theorem m1049 : g 1049 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 148 (by decide))
    H.one_mem

omit hs in
private theorem m1143 : g 1143 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 154 (by decide))
    H.one_mem

omit hs in
private theorem m1677 : g 1677 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 157 (by decide))
    H.one_mem

omit hs in
private theorem m43 : g 43 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 164 (by decide))
    H.one_mem

omit hs in
private theorem m44 : g 44 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 169 (by decide))
    H.one_mem

omit hs in
private theorem m45 : g 45 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 175 (by decide))
    H.one_mem

omit hs in
private theorem m46 : g 46 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 177 (by decide))
    H.one_mem

omit hs in
private theorem m1195 : g 1195 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 180 (by decide))
    H.one_mem

omit hs in
private theorem m69 : g 69 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 181 (by decide))
    H.one_mem

omit hs in
private theorem m980 : g 980 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 185 (by decide))
    H.one_mem

omit hs in
private theorem m1637 : g 1637 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 186 (by decide))
    H.one_mem

omit hs in
private theorem m48 : g 48 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 188 (by decide))
    H.one_mem

omit hs in
private theorem m50 : g 50 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 192 (by decide))
    H.one_mem

omit hs in
private theorem m52 : g 52 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 201 (by decide))
    H.one_mem

omit hs in
private theorem m54 : g 54 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 205 (by decide))
    H.one_mem

omit hs in
private theorem m1975 : g 1975 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 206 (by decide))
    H.one_mem

omit hs in
private theorem m55 : g 55 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 211 (by decide))
    H.one_mem

omit hs in
private theorem m57 : g 57 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 215 (by decide))
    H.one_mem

omit hs in
private theorem m58 : g 58 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 217 (by decide))
    H.one_mem

omit hs in
private theorem m63 : g 63 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 233 (by decide))
    H.one_mem

omit hs in
private theorem m397 : g 397 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 239 (by decide))
    H.one_mem

omit hs in
private theorem m67 : g 67 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 240 (by decide))
    H.one_mem

omit hs in
private theorem m1695 : g 1695 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 244 (by decide))
    H.one_mem

omit hs in
private theorem m1170 : g 1170 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 245 (by decide))
    H.one_mem

omit hs in
private theorem m1350 : g 1350 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 249 (by decide))
    H.one_mem

omit hs in
private theorem m266 : g 266 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 251 (by decide))
    H.one_mem

omit hs in
private theorem m2044 : g 2044 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 255 (by decide))
    H.one_mem

omit hs in
private theorem m71 : g 71 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 260 (by decide))
    H.one_mem

omit hs in
private theorem m75 : g 75 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 269 (by decide))
    H.one_mem

omit hs in
private theorem m79 : g 79 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 278 (by decide))
    H.one_mem

omit hs in
private theorem m83 : g 83 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 282 (by decide))
    H.one_mem

omit hs in
private theorem m779 : g 779 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 283 (by decide))
    H.one_mem

omit hs in
private theorem m1563 : g 1563 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 287 (by decide))
    H.one_mem

omit hs in
private theorem m1624 : g 1624 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 288 (by decide))
    H.one_mem

omit hs in
private theorem m85 : g 85 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 297 (by decide))
    H.one_mem

omit hs in
private theorem m86 : g 86 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 301 (by decide))
    H.one_mem

omit hs in
private theorem m1337 : g 1337 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 302 (by decide))
    H.one_mem

omit hs in
private theorem m2031 : g 2031 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 310 (by decide))
    H.one_mem

omit hs in
private theorem m1794 : g 1794 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 317 (by decide))
    H.one_mem

omit hs in
private theorem m419 : g 419 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 325 (by decide))
    H.one_mem

omit hs in
private theorem m92 : g 92 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 328 (by decide))
    H.one_mem

omit hs in
private theorem m94 : g 94 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 336 (by decide))
    H.one_mem

omit hs in
private theorem m96 : g 96 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 339 (by decide))
    H.one_mem

omit hs in
private theorem m396 : g 396 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 340 (by decide))
    H.one_mem

omit hs in
private theorem m445 : g 445 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 347 (by decide))
    H.one_mem

omit hs in
private theorem m1187 : g 1187 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 348 (by decide))
    H.one_mem

omit hs in
private theorem m100 : g 100 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 353 (by decide))
    H.one_mem

omit hs in
private theorem m1129 : g 1129 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 357 (by decide))
    H.one_mem

omit hs in
private theorem m165 : g 165 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 358 (by decide))
    H.one_mem

omit hs in
private theorem m2061 : g 2061 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 360 (by decide))
    H.one_mem

omit hs in
private theorem m143 : g 143 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 361 (by decide))
    H.one_mem

omit hs in
private theorem m1826 : g 1826 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 365 (by decide))
    H.one_mem

omit hs in
private theorem m540 : g 540 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 370 (by decide))
    H.one_mem

omit hs in
private theorem m102 : g 102 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 373 (by decide))
    H.one_mem

omit hs in
private theorem m103 : g 103 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 378 (by decide))
    H.one_mem

omit hs in
private theorem m105 : g 105 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 380 (by decide))
    H.one_mem

omit hs in
private theorem m907 : g 907 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 383 (by decide))
    H.one_mem

omit hs in
private theorem m108 : g 108 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 387 (by decide))
    H.one_mem

omit hs in
private theorem m1290 : g 1290 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 388 (by decide))
    H.one_mem

omit hs in
private theorem m1919 : g 1919 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 392 (by decide))
    H.one_mem

omit hs in
private theorem m140 : g 140 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 398 (by decide))
    H.one_mem

omit hs in
private theorem m111 : g 111 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 402 (by decide))
    H.one_mem

omit hs in
private theorem m2036 : g 2036 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 427 (by decide))
    H.one_mem

omit hs in
private theorem m714 : g 714 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 429 (by decide))
    H.one_mem

omit hs in
private theorem m304 : g 304 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 430 (by decide))
    H.one_mem

omit hs in
private theorem m1411 : g 1411 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 435 (by decide))
    H.one_mem

omit hs in
private theorem m1990 : g 1990 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 439 (by decide))
    H.one_mem

omit hs in
private theorem m123 : g 123 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 446 (by decide))
    H.one_mem

omit hs in
private theorem m1480 : g 1480 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 449 (by decide))
    H.one_mem

omit hs in
private theorem m377 : g 377 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 450 (by decide))
    H.one_mem

omit hs in
private theorem m211 : g 211 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 457 (by decide))
    H.one_mem

omit hs in
private theorem m158 : g 158 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 458 (by decide))
    H.one_mem

omit hs in
private theorem m1931 : g 1931 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 465 (by decide))
    H.one_mem

omit hs in
private theorem m128 : g 128 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 472 (by decide))
    H.one_mem

omit hs in
private theorem m378 : g 378 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 481 (by decide))
    H.one_mem

omit hs in
private theorem m1064 : g 1064 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 489 (by decide))
    H.one_mem

omit hs in
private theorem m1659 : g 1659 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 494 (by decide))
    H.one_mem

omit hs in
private theorem m136 : g 136 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 495 (by decide))
    H.one_mem

omit hs in
private theorem m141 : g 141 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 502 (by decide))
    H.one_mem

omit hs in
private theorem m1346 : g 1346 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 505 (by decide))
    H.one_mem

omit hs in
private theorem m1174 : g 1174 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 507 (by decide))
    H.one_mem

omit hs in
private theorem m1606 : g 1606 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 508 (by decide))
    H.one_mem

omit hs in
private theorem m1987 : g 1987 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 510 (by decide))
    H.one_mem

omit hs in
private theorem m209 : g 209 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 511 (by decide))
    H.one_mem

omit hs in
private theorem m144 : g 144 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 516 (by decide))
    H.one_mem

omit hs in
private theorem m146 : g 146 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 520 (by decide))
    H.one_mem

omit hs in
private theorem m286 : g 286 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 526 (by decide))
    H.one_mem

omit hs in
private theorem m1438 : g 1438 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 527 (by decide))
    H.one_mem

omit hs in
private theorem m1227 : g 1227 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 531 (by decide))
    H.one_mem

omit hs in
private theorem m150 : g 150 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 534 (by decide))
    H.one_mem

omit hs in
private theorem m1055 : g 1055 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 535 (by decide))
    H.one_mem

omit hs in
private theorem m151 : g 151 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 539 (by decide))
    H.one_mem

private theorem m1098 : g 1098 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1041")) (hv 5328 (by decide))
    (H.mul_mem (H.inv_mem (m1041 H hs)) H.one_mem)

omit hs in
private theorem m152 : g 152 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 542 (by decide))
    H.one_mem

omit hs in
private theorem m1317 : g 1317 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 546 (by decide))
    H.one_mem

omit hs in
private theorem m1970 : g 1970 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 549 (by decide))
    H.one_mem

omit hs in
private theorem m1768 : g 1768 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 550 (by decide))
    H.one_mem

omit hs in
private theorem m1422 : g 1422 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 555 (by decide))
    H.one_mem

omit hs in
private theorem m502 : g 502 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 556 (by decide))
    H.one_mem

omit hs in
private theorem m1430 : g 1430 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 563 (by decide))
    H.one_mem

omit hs in
private theorem m770 : g 770 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 566 (by decide))
    H.one_mem

omit hs in
private theorem m607 : g 607 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 567 (by decide))
    H.one_mem

omit hs in
private theorem m1007 : g 1007 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 575 (by decide))
    H.one_mem

omit hs in
private theorem m653 : g 653 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 578 (by decide))
    H.one_mem

omit hs in
private theorem m633 : g 633 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 581 (by decide))
    H.one_mem

omit hs in
private theorem m1369 : g 1369 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 582 (by decide))
    H.one_mem

omit hs in
private theorem m678 : g 678 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 592 (by decide))
    H.one_mem

omit hs in
private theorem m166 : g 166 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 594 (by decide))
    H.one_mem

omit hs in
private theorem m1731 : g 1731 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 599 (by decide))
    H.one_mem

omit hs in
private theorem m168 : g 168 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 603 (by decide))
    H.one_mem

omit hs in
private theorem m873 : g 873 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 608 (by decide))
    H.one_mem

omit hs in
private theorem m279 : g 279 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 618 (by decide))
    H.one_mem

omit hs in
private theorem m300 : g 300 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 625 (by decide))
    H.one_mem

omit hs in
private theorem m654 : g 654 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 629 (by decide))
    H.one_mem

omit hs in
private theorem m1275 : g 1275 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 630 (by decide))
    H.one_mem

omit hs in
private theorem m1305 : g 1305 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 633 (by decide))
    H.one_mem

omit hs in
private theorem m344 : g 344 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 634 (by decide))
    H.one_mem

omit hs in
private theorem m854 : g 854 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 637 (by decide))
    H.one_mem

omit hs in
private theorem m174 : g 174 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 640 (by decide))
    H.one_mem

omit hs in
private theorem m178 : g 178 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 646 (by decide))
    H.one_mem

omit hs in
private theorem m1371 : g 1371 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 649 (by decide))
    H.one_mem

omit hs in
private theorem m181 : g 181 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 653 (by decide))
    H.one_mem

omit hs in
private theorem m1983 : g 1983 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 654 (by decide))
    H.one_mem

omit hs in
private theorem m1355 : g 1355 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 663 (by decide))
    H.one_mem

omit hs in
private theorem m1761 : g 1761 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 665 (by decide))
    H.one_mem

omit hs in
private theorem m1977 : g 1977 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 666 (by decide))
    H.one_mem

omit hs in
private theorem m183 : g 183 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 670 (by decide))
    H.one_mem

omit hs in
private theorem m1295 : g 1295 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 672 (by decide))
    H.one_mem

omit hs in
private theorem m184 : g 184 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 675 (by decide))
    H.one_mem

omit hs in
private theorem m1524 : g 1524 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 677 (by decide))
    H.one_mem

omit hs in
private theorem m186 : g 186 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 682 (by decide))
    H.one_mem

omit hs in
private theorem m188 : g 188 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 685 (by decide))
    H.one_mem

omit hs in
private theorem m528 : g 528 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 694 (by decide))
    H.one_mem

omit hs in
private theorem m191 : g 191 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 699 (by decide))
    H.one_mem

omit hs in
private theorem m583 : g 583 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 703 (by decide))
    H.one_mem

omit hs in
private theorem m1426 : g 1426 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 706 (by decide))
    H.one_mem

omit hs in
private theorem m960 : g 960 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 707 (by decide))
    H.one_mem

omit hs in
private theorem m193 : g 193 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 711 (by decide))
    H.one_mem

omit hs in
private theorem m2004 : g 2004 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 715 (by decide))
    H.one_mem

omit hs in
private theorem m554 : g 554 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 717 (by decide))
    H.one_mem

omit hs in
private theorem m1862 : g 1862 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 721 (by decide))
    H.one_mem

omit hs in
private theorem m196 : g 196 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 723 (by decide))
    H.one_mem

omit hs in
private theorem m198 : g 198 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 726 (by decide))
    H.one_mem

omit hs in
private theorem m1123 : g 1123 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 729 (by decide))
    H.one_mem

omit hs in
private theorem m199 : g 199 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 733 (by decide))
    H.one_mem

omit hs in
private theorem m202 : g 202 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 740 (by decide))
    H.one_mem

omit hs in
private theorem m204 : g 204 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 747 (by decide))
    H.one_mem

omit hs in
private theorem m206 : g 206 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 750 (by decide))
    H.one_mem

omit hs in
private theorem m955 : g 955 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 756 (by decide))
    H.one_mem

omit hs in
private theorem m1844 : g 1844 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 761 (by decide))
    H.one_mem

omit hs in
private theorem m1709 : g 1709 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 765 (by decide))
    H.one_mem

omit hs in
private theorem m1527 : g 1527 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 766 (by decide))
    H.one_mem

omit hs in
private theorem m210 : g 210 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 769 (by decide))
    H.one_mem

omit hs in
private theorem m1798 : g 1798 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 772 (by decide))
    H.one_mem

omit hs in
private theorem m964 : g 964 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 782 (by decide))
    H.one_mem

omit hs in
private theorem m1512 : g 1512 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 783 (by decide))
    H.one_mem

omit hs in
private theorem m900 : g 900 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 785 (by decide))
    H.one_mem

omit hs in
private theorem m1705 : g 1705 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 789 (by decide))
    H.one_mem

omit hs in
private theorem m1825 : g 1825 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 790 (by decide))
    H.one_mem

omit hs in
private theorem m1934 : g 1934 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 796 (by decide))
    H.one_mem

omit hs in
private theorem m218 : g 218 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 798 (by decide))
    H.one_mem

omit hs in
private theorem m1498 : g 1498 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 801 (by decide))
    H.one_mem

omit hs in
private theorem m1672 : g 1672 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 807 (by decide))
    H.one_mem

omit hs in
private theorem m2016 : g 2016 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 812 (by decide))
    H.one_mem

omit hs in
private theorem m221 : g 221 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 816 (by decide))
    H.one_mem

omit hs in
private theorem m222 : g 222 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 817 (by decide))
    H.one_mem

omit hs in
private theorem m1102 : g 1102 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 820 (by decide))
    H.one_mem

omit hs in
private theorem m225 : g 225 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 825 (by decide))
    H.one_mem

omit hs in
private theorem m1579 : g 1579 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 839 (by decide))
    H.one_mem

omit hs in
private theorem m234 : g 234 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 843 (by decide))
    H.one_mem

omit hs in
private theorem m1051 : g 1051 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 853 (by decide))
    H.one_mem

omit hs in
private theorem m1254 : g 1254 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 856 (by decide))
    H.one_mem

omit hs in
private theorem m238 : g 238 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 859 (by decide))
    H.one_mem

omit hs in
private theorem m695 : g 695 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 862 (by decide))
    H.one_mem

omit hs in
private theorem m1079 : g 1079 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 867 (by decide))
    H.one_mem

omit hs in
private theorem m1674 : g 1674 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 870 (by decide))
    H.one_mem

omit hs in
private theorem m245 : g 245 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 881 (by decide))
    H.one_mem

omit hs in
private theorem m248 : g 248 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 885 (by decide))
    H.one_mem

omit hs in
private theorem m1431 : g 1431 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 887 (by decide))
    H.one_mem

omit hs in
private theorem m1623 : g 1623 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 890 (by decide))
    H.one_mem

omit hs in
private theorem m1074 : g 1074 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 895 (by decide))
    H.one_mem

omit hs in
private theorem m452 : g 452 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 897 (by decide))
    H.one_mem

omit hs in
private theorem m252 : g 252 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 901 (by decide))
    H.one_mem

omit hs in
private theorem m253 : g 253 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 904 (by decide))
    H.one_mem

omit hs in
private theorem m1628 : g 1628 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 907 (by decide))
    H.one_mem

omit hs in
private theorem m257 : g 257 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 913 (by decide))
    H.one_mem

omit hs in
private theorem m1238 : g 1238 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 918 (by decide))
    H.one_mem

omit hs in
private theorem m458 : g 458 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 924 (by decide))
    H.one_mem

omit hs in
private theorem m710 : g 710 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 927 (by decide))
    H.one_mem

omit hs in
private theorem m450 : g 450 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 936 (by decide))
    H.one_mem

omit hs in
private theorem m265 : g 265 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 937 (by decide))
    H.one_mem

omit hs in
private theorem m1774 : g 1774 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 939 (by decide))
    H.one_mem

omit hs in
private theorem m1315 : g 1315 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 942 (by decide))
    H.one_mem

omit hs in
private theorem m605 : g 605 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 945 (by decide))
    H.one_mem

omit hs in
private theorem m269 : g 269 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 952 (by decide))
    H.one_mem

omit hs in
private theorem m272 : g 272 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 960 (by decide))
    H.one_mem

private theorem m1641 : g 1641 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-273")) (hv 5375 (by decide))
    (H.mul_mem (H.inv_mem (m273 H hs)) H.one_mem)

omit hs in
private theorem m1169 : g 1169 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 966 (by decide))
    H.one_mem

omit hs in
private theorem m298 : g 298 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 968 (by decide))
    H.one_mem

omit hs in
private theorem m275 : g 275 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 976 (by decide))
    H.one_mem

omit hs in
private theorem m278 : g 278 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 982 (by decide))
    H.one_mem

omit hs in
private theorem m548 : g 548 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 984 (by decide))
    H.one_mem

omit hs in
private theorem m280 : g 280 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 987 (by decide))
    H.one_mem

omit hs in
private theorem m285 : g 285 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 993 (by decide))
    H.one_mem

omit hs in
private theorem m1379 : g 1379 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 994 (by decide))
    H.one_mem

omit hs in
private theorem m1860 : g 1860 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 997 (by decide))
    H.one_mem

omit hs in
private theorem m589 : g 589 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 998 (by decide))
    H.one_mem

omit hs in
private theorem m761 : g 761 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1002 (by decide))
    H.one_mem

omit hs in
private theorem m1560 : g 1560 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1003 (by decide))
    H.one_mem

omit hs in
private theorem m805 : g 805 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1006 (by decide))
    H.one_mem

omit hs in
private theorem m1815 : g 1815 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1010 (by decide))
    H.one_mem

omit hs in
private theorem m1330 : g 1330 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1011 (by decide))
    H.one_mem

omit hs in
private theorem m1551 : g 1551 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1015 (by decide))
    H.one_mem

omit hs in
private theorem m1616 : g 1616 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1018 (by decide))
    H.one_mem

omit hs in
private theorem m1694 : g 1694 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1024 (by decide))
    H.one_mem

omit hs in
private theorem m290 : g 290 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1027 (by decide))
    H.one_mem

omit hs in
private theorem m974 : g 974 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1031 (by decide))
    H.one_mem

omit hs in
private theorem m1791 : g 1791 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1034 (by decide))
    H.one_mem

omit hs in
private theorem m296 : g 296 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1044 (by decide))
    H.one_mem

omit hs in
private theorem m297 : g 297 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1046 (by decide))
    H.one_mem

omit hs in
private theorem m706 : g 706 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1051 (by decide))
    H.one_mem

omit hs in
private theorem m299 : g 299 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1054 (by decide))
    H.one_mem

omit hs in
private theorem m1404 : g 1404 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1057 (by decide))
    H.one_mem

omit hs in
private theorem m301 : g 301 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1060 (by decide))
    H.one_mem

omit hs in
private theorem m763 : g 763 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1067 (by decide))
    H.one_mem

omit hs in
private theorem m308 : g 308 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1074 (by decide))
    H.one_mem

omit hs in
private theorem m747 : g 747 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1079 (by decide))
    H.one_mem

omit hs in
private theorem m315 : g 315 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1092 (by decide))
    H.one_mem

omit hs in
private theorem m317 : g 317 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1095 (by decide))
    H.one_mem

omit hs in
private theorem m318 : g 318 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1097 (by decide))
    H.one_mem

omit hs in
private theorem m321 : g 321 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1099 (by decide))
    H.one_mem

omit hs in
private theorem m324 : g 324 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1103 (by decide))
    H.one_mem

omit hs in
private theorem m326 : g 326 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1110 (by decide))
    H.one_mem

omit hs in
private theorem m327 : g 327 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1113 (by decide))
    H.one_mem

private theorem m1917 : g 1917 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1115")) (hv 4733 (by decide))
    (H.mul_mem (H.inv_mem (m1115 H hs)) H.one_mem)

omit hs in
private theorem m466 : g 466 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1117 (by decide))
    H.one_mem

omit hs in
private theorem m328 : g 328 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1120 (by decide))
    H.one_mem

omit hs in
private theorem m329 : g 329 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1123 (by decide))
    H.one_mem

omit hs in
private theorem m330 : g 330 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1126 (by decide))
    H.one_mem

omit hs in
private theorem m332 : g 332 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1129 (by decide))
    H.one_mem

omit hs in
private theorem m1654 : g 1654 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1132 (by decide))
    H.one_mem

omit hs in
private theorem m1025 : g 1025 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1134 (by decide))
    H.one_mem

omit hs in
private theorem m1605 : g 1605 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1135 (by decide))
    H.one_mem

omit hs in
private theorem m334 : g 334 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1138 (by decide))
    H.one_mem

omit hs in
private theorem m337 : g 337 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1144 (by decide))
    H.one_mem

omit hs in
private theorem m339 : g 339 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1146 (by decide))
    H.one_mem

omit hs in
private theorem m340 : g 340 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1150 (by decide))
    H.one_mem

omit hs in
private theorem m1732 : g 1732 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1152 (by decide))
    H.one_mem

omit hs in
private theorem m1257 : g 1257 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1161 (by decide))
    H.one_mem

omit hs in
private theorem m487 : g 487 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1163 (by decide))
    H.one_mem

omit hs in
private theorem m347 : g 347 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1169 (by decide))
    H.one_mem

omit hs in
private theorem m1554 : g 1554 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1172 (by decide))
    H.one_mem

omit hs in
private theorem m702 : g 702 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1175 (by decide))
    H.one_mem

omit hs in
private theorem m1225 : g 1225 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1176 (by decide))
    H.one_mem

private theorem m975 : g 975 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-348")) (hv 5403 (by decide))
    (H.mul_mem (H.inv_mem (m348 H hs)) H.one_mem)

omit hs in
private theorem m350 : g 350 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1184 (by decide))
    H.one_mem

omit hs in
private theorem m1667 : g 1667 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1190 (by decide))
    H.one_mem

omit hs in
private theorem m1308 : g 1308 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1202 (by decide))
    H.one_mem

omit hs in
private theorem m556 : g 556 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1205 (by decide))
    H.one_mem

omit hs in
private theorem m448 : g 448 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1209 (by decide))
    H.one_mem

omit hs in
private theorem m1836 : g 1836 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1213 (by decide))
    H.one_mem

omit hs in
private theorem m361 : g 361 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1216 (by decide))
    H.one_mem

omit hs in
private theorem m367 : g 367 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1222 (by decide))
    H.one_mem

omit hs in
private theorem m470 : g 470 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1224 (by decide))
    H.one_mem

omit hs in
private theorem m368 : g 368 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1227 (by decide))
    H.one_mem

omit hs in
private theorem m1325 : g 1325 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1232 (by decide))
    H.one_mem

omit hs in
private theorem m370 : g 370 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1233 (by decide))
    H.one_mem

omit hs in
private theorem m372 : g 372 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1235 (by decide))
    H.one_mem

omit hs in
private theorem m373 : g 373 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1237 (by decide))
    H.one_mem

omit hs in
private theorem m375 : g 375 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1241 (by decide))
    H.one_mem

omit hs in
private theorem m1618 : g 1618 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1243 (by decide))
    H.one_mem

omit hs in
private theorem m1625 : g 1625 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1245 (by decide))
    H.one_mem

omit hs in
private theorem m382 : g 382 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1254 (by decide))
    H.one_mem

omit hs in
private theorem m1583 : g 1583 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1262 (by decide))
    H.one_mem

omit hs in
private theorem m1550 : g 1550 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1267 (by decide))
    H.one_mem

omit hs in
private theorem m388 : g 388 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1271 (by decide))
    H.one_mem

omit hs in
private theorem m390 : g 390 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1274 (by decide))
    H.one_mem

omit hs in
private theorem m1995 : g 1995 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1287 (by decide))
    H.one_mem

omit hs in
private theorem m399 : g 399 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1291 (by decide))
    H.one_mem

omit hs in
private theorem m670 : g 670 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1297 (by decide))
    H.one_mem

omit hs in
private theorem m407 : g 407 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1301 (by decide))
    H.one_mem

omit hs in
private theorem m409 : g 409 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1304 (by decide))
    H.one_mem

omit hs in
private theorem m1120 : g 1120 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1315 (by decide))
    H.one_mem

omit hs in
private theorem m413 : g 413 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1316 (by decide))
    H.one_mem

omit hs in
private theorem m417 : g 417 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1321 (by decide))
    H.one_mem

omit hs in
private theorem m1463 : g 1463 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1324 (by decide))
    H.one_mem

omit hs in
private theorem m623 : g 623 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1326 (by decide))
    H.one_mem

omit hs in
private theorem m418 : g 418 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1328 (by decide))
    H.one_mem

private theorem m1800 : g 1800 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-422")) (hv 5504 (by decide))
    (H.mul_mem (H.inv_mem (m422 H hs)) H.one_mem)

omit hs in
private theorem m423 : g 423 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1336 (by decide))
    H.one_mem

omit hs in
private theorem m426 : g 426 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1341 (by decide))
    H.one_mem

omit hs in
private theorem m428 : g 428 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1344 (by decide))
    H.one_mem

omit hs in
private theorem m485 : g 485 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1349 (by decide))
    H.one_mem

omit hs in
private theorem m891 : g 891 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1351 (by decide))
    H.one_mem

omit hs in
private theorem m432 : g 432 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1354 (by decide))
    H.one_mem

omit hs in
private theorem m1019 : g 1019 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1356 (by decide))
    H.one_mem

omit hs in
private theorem m437 : g 437 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1361 (by decide))
    H.one_mem

omit hs in
private theorem m439 : g 439 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1364 (by decide))
    H.one_mem

omit hs in
private theorem m441 : g 441 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1366 (by decide))
    H.one_mem

omit hs in
private theorem m443 : g 443 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1368 (by decide))
    H.one_mem

omit hs in
private theorem m446 : g 446 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1376 (by decide))
    H.one_mem

omit hs in
private theorem m1561 : g 1561 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1380 (by decide))
    H.one_mem

omit hs in
private theorem m1614 : g 1614 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1383 (by decide))
    H.one_mem

omit hs in
private theorem m451 : g 451 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1384 (by decide))
    H.one_mem

omit hs in
private theorem m454 : g 454 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1389 (by decide))
    H.one_mem

omit hs in
private theorem m1435 : g 1435 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1393 (by decide))
    H.one_mem

omit hs in
private theorem m461 : g 461 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1401 (by decide))
    H.one_mem

omit hs in
private theorem m1021 : g 1021 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1403 (by decide))
    H.one_mem

omit hs in
private theorem m902 : g 902 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1405 (by decide))
    H.one_mem

omit hs in
private theorem m802 : g 802 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1407 (by decide))
    H.one_mem

omit hs in
private theorem m1895 : g 1895 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1409 (by decide))
    H.one_mem

omit hs in
private theorem m1967 : g 1967 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1411 (by decide))
    H.one_mem

omit hs in
private theorem m1481 : g 1481 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1413 (by decide))
    H.one_mem

omit hs in
private theorem m464 : g 464 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1418 (by decide))
    H.one_mem

omit hs in
private theorem m1773 : g 1773 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1420 (by decide))
    H.one_mem

omit hs in
private theorem m465 : g 465 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1422 (by decide))
    H.one_mem

omit hs in
private theorem m467 : g 467 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1425 (by decide))
    H.one_mem

omit hs in
private theorem m471 : g 471 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1429 (by decide))
    H.one_mem

omit hs in
private theorem m474 : g 474 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1434 (by decide))
    H.one_mem

omit hs in
private theorem m476 : g 476 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1435 (by decide))
    H.one_mem

private theorem m1861 : g 1861 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-480")) (hv 5749 (by decide))
    (H.mul_mem (H.inv_mem (m480 H hs)) H.one_mem)

omit hs in
private theorem m488 : g 488 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1454 (by decide))
    H.one_mem

omit hs in
private theorem m1806 : g 1806 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1455 (by decide))
    H.one_mem

omit hs in
private theorem m1781 : g 1781 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1457 (by decide))
    H.one_mem

omit hs in
private theorem m766 : g 766 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1462 (by decide))
    H.one_mem

omit hs in
private theorem m493 : g 493 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1465 (by decide))
    H.one_mem

omit hs in
private theorem m668 : g 668 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1470 (by decide))
    H.one_mem

omit hs in
private theorem m1872 : g 1872 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1472 (by decide))
    H.one_mem

omit hs in
private theorem m1989 : g 1989 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1478 (by decide))
    H.one_mem

omit hs in
private theorem m500 : g 500 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1485 (by decide))
    H.one_mem

omit hs in
private theorem m1852 : g 1852 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1491 (by decide))
    H.one_mem

omit hs in
private theorem m1678 : g 1678 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1493 (by decide))
    H.one_mem

omit hs in
private theorem m731 : g 731 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1497 (by decide))
    H.one_mem

omit hs in
private theorem m1610 : g 1610 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1499 (by decide))
    H.one_mem

omit hs in
private theorem m505 : g 505 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1500 (by decide))
    H.one_mem

omit hs in
private theorem m825 : g 825 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1505 (by decide))
    H.one_mem

omit hs in
private theorem m508 : g 508 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1507 (by decide))
    H.one_mem

omit hs in
private theorem m564 : g 564 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1511 (by decide))
    H.one_mem

omit hs in
private theorem m1117 : g 1117 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1518 (by decide))
    H.one_mem

omit hs in
private theorem m663 : g 663 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1521 (by decide))
    H.one_mem

omit hs in
private theorem m924 : g 924 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1523 (by decide))
    H.one_mem

omit hs in
private theorem m515 : g 515 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1524 (by decide))
    H.one_mem

omit hs in
private theorem m885 : g 885 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1527 (by decide))
    H.one_mem

omit hs in
private theorem m518 : g 518 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1529 (by decide))
    H.one_mem

omit hs in
private theorem m519 : g 519 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1531 (by decide))
    H.one_mem

omit hs in
private theorem m520 : g 520 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1534 (by decide))
    H.one_mem

omit hs in
private theorem m1665 : g 1665 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1536 (by decide))
    H.one_mem

omit hs in
private theorem m1784 : g 1784 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1542 (by decide))
    H.one_mem

omit hs in
private theorem m1224 : g 1224 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1543 (by decide))
    H.one_mem

omit hs in
private theorem m525 : g 525 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1547 (by decide))
    H.one_mem

omit hs in
private theorem m527 : g 527 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1551 (by decide))
    H.one_mem

omit hs in
private theorem m529 : g 529 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1554 (by decide))
    H.one_mem

omit hs in
private theorem m1832 : g 1832 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1561 (by decide))
    H.one_mem

omit hs in
private theorem m1375 : g 1375 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1562 (by decide))
    H.one_mem

omit hs in
private theorem m1136 : g 1136 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1565 (by decide))
    H.one_mem

omit hs in
private theorem m532 : g 532 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1568 (by decide))
    H.one_mem

omit hs in
private theorem m1162 : g 1162 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1575 (by decide))
    H.one_mem

omit hs in
private theorem m535 : g 535 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1578 (by decide))
    H.one_mem

omit hs in
private theorem m537 : g 537 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1580 (by decide))
    H.one_mem

omit hs in
private theorem m1901 : g 1901 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1583 (by decide))
    H.one_mem

omit hs in
private theorem m538 : g 538 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1585 (by decide))
    H.one_mem

omit hs in
private theorem m905 : g 905 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1591 (by decide))
    H.one_mem

omit hs in
private theorem m546 : g 546 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1594 (by decide))
    H.one_mem

omit hs in
private theorem m549 : g 549 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1600 (by decide))
    H.one_mem

omit hs in
private theorem m971 : g 971 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1602 (by decide))
    H.one_mem

omit hs in
private theorem m1207 : g 1207 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1609 (by decide))
    H.one_mem

omit hs in
private theorem m562 : g 562 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1610 (by decide))
    H.one_mem

omit hs in
private theorem m1189 : g 1189 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1613 (by decide))
    H.one_mem

omit hs in
private theorem m982 : g 982 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1619 (by decide))
    H.one_mem

omit hs in
private theorem m2003 : g 2003 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1623 (by decide))
    H.one_mem

omit hs in
private theorem m742 : g 742 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1626 (by decide))
    H.one_mem

omit hs in
private theorem m1547 : g 1547 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1627 (by decide))
    H.one_mem

omit hs in
private theorem m1501 : g 1501 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1632 (by decide))
    H.one_mem

omit hs in
private theorem m563 : g 563 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1634 (by decide))
    H.one_mem

omit hs in
private theorem m2030 : g 2030 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1639 (by decide))
    H.one_mem

omit hs in
private theorem m567 : g 567 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1641 (by decide))
    H.one_mem

omit hs in
private theorem m568 : g 568 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1643 (by decide))
    H.one_mem

omit hs in
private theorem m569 : g 569 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1645 (by decide))
    H.one_mem

omit hs in
private theorem m687 : g 687 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1648 (by decide))
    H.one_mem

omit hs in
private theorem m570 : g 570 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1651 (by decide))
    H.one_mem

omit hs in
private theorem m580 : g 580 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1662 (by decide))
    H.one_mem

omit hs in
private theorem m586 : g 586 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1671 (by decide))
    H.one_mem

omit hs in
private theorem m1805 : g 1805 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1677 (by decide))
    H.one_mem

omit hs in
private theorem m593 : g 593 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1685 (by decide))
    H.one_mem

omit hs in
private theorem m594 : g 594 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1687 (by decide))
    H.one_mem

omit hs in
private theorem m597 : g 597 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1694 (by decide))
    H.one_mem

omit hs in
private theorem m600 : g 600 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1699 (by decide))
    H.one_mem

omit hs in
private theorem m603 : g 603 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1706 (by decide))
    H.one_mem

omit hs in
private theorem m716 : g 716 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1710 (by decide))
    H.one_mem

omit hs in
private theorem m618 : g 618 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1726 (by decide))
    H.one_mem

omit hs in
private theorem m621 : g 621 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1730 (by decide))
    H.one_mem

omit hs in
private theorem m1320 : g 1320 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1743 (by decide))
    H.one_mem

omit hs in
private theorem m631 : g 631 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1745 (by decide))
    H.one_mem

omit hs in
private theorem m1491 : g 1491 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1747 (by decide))
    H.one_mem

omit hs in
private theorem m632 : g 632 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1749 (by decide))
    H.one_mem

omit hs in
private theorem m897 : g 897 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1752 (by decide))
    H.one_mem

private theorem m1642 : g 1642 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-906")) (hv 5112 (by decide))
    (H.mul_mem (H.inv_mem (m906 H hs)) H.one_mem)

omit hs in
private theorem m635 : g 635 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1758 (by decide))
    H.one_mem

omit hs in
private theorem m638 : g 638 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1763 (by decide))
    H.one_mem

omit hs in
private theorem m641 : g 641 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1767 (by decide))
    H.one_mem

omit hs in
private theorem m1571 : g 1571 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1769 (by decide))
    H.one_mem

omit hs in
private theorem m642 : g 642 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1772 (by decide))
    H.one_mem

omit hs in
private theorem m646 : g 646 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1780 (by decide))
    H.one_mem

omit hs in
private theorem m648 : g 648 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1784 (by decide))
    H.one_mem

omit hs in
private theorem m655 : g 655 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1787 (by decide))
    H.one_mem

omit hs in
private theorem m1684 : g 1684 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1790 (by decide))
    H.one_mem

omit hs in
private theorem m660 : g 660 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1798 (by decide))
    H.one_mem

omit hs in
private theorem m662 : g 662 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1801 (by decide))
    H.one_mem

omit hs in
private theorem m1218 : g 1218 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1804 (by decide))
    H.one_mem

omit hs in
private theorem m664 : g 664 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1806 (by decide))
    H.one_mem

omit hs in
private theorem m666 : g 666 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1809 (by decide))
    H.one_mem

omit hs in
private theorem m669 : g 669 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1811 (by decide))
    H.one_mem

omit hs in
private theorem m1362 : g 1362 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1822 (by decide))
    H.one_mem

omit hs in
private theorem m852 : g 852 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1825 (by decide))
    H.one_mem

omit hs in
private theorem m1380 : g 1380 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1826 (by decide))
    H.one_mem

omit hs in
private theorem m679 : g 679 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1832 (by decide))
    H.one_mem

omit hs in
private theorem m682 : g 682 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1837 (by decide))
    H.one_mem

omit hs in
private theorem m1031 : g 1031 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1839 (by decide))
    H.one_mem

omit hs in
private theorem m684 : g 684 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1841 (by decide))
    H.one_mem

omit hs in
private theorem m1936 : g 1936 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1846 (by decide))
    H.one_mem

omit hs in
private theorem m1539 : g 1539 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1847 (by decide))
    H.one_mem

omit hs in
private theorem m1922 : g 1922 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1849 (by decide))
    H.one_mem

omit hs in
private theorem m1592 : g 1592 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1853 (by decide))
    H.one_mem

omit hs in
private theorem m1453 : g 1453 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1857 (by decide))
    H.one_mem

omit hs in
private theorem m696 : g 696 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1860 (by decide))
    H.one_mem

omit hs in
private theorem m698 : g 698 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1864 (by decide))
    H.one_mem

omit hs in
private theorem m700 : g 700 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1866 (by decide))
    H.one_mem

omit hs in
private theorem m1883 : g 1883 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1869 (by decide))
    H.one_mem

omit hs in
private theorem m1730 : g 1730 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1870 (by decide))
    H.one_mem

omit hs in
private theorem m1352 : g 1352 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1875 (by decide))
    H.one_mem

omit hs in
private theorem m1105 : g 1105 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1881 (by decide))
    H.one_mem

omit hs in
private theorem m1827 : g 1827 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1883 (by decide))
    H.one_mem

omit hs in
private theorem m817 : g 817 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1885 (by decide))
    H.one_mem

omit hs in
private theorem m1892 : g 1892 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1889 (by decide))
    H.one_mem

omit hs in
private theorem m718 : g 718 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1891 (by decide))
    H.one_mem

omit hs in
private theorem m720 : g 720 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1894 (by decide))
    H.one_mem

omit hs in
private theorem m721 : g 721 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1896 (by decide))
    H.one_mem

omit hs in
private theorem m1535 : g 1535 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1898 (by decide))
    H.one_mem

omit hs in
private theorem m722 : g 722 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1900 (by decide))
    H.one_mem

omit hs in
private theorem m725 : g 725 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1905 (by decide))
    H.one_mem

omit hs in
private theorem m726 : g 726 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1907 (by decide))
    H.one_mem

omit hs in
private theorem m733 : g 733 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1919 (by decide))
    H.one_mem

omit hs in
private theorem m958 : g 958 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1922 (by decide))
    H.one_mem

omit hs in
private theorem m739 : g 739 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1930 (by decide))
    H.one_mem

omit hs in
private theorem m744 : g 744 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1939 (by decide))
    H.one_mem

omit hs in
private theorem m746 : g 746 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1940 (by decide))
    H.one_mem

omit hs in
private theorem m1285 : g 1285 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1943 (by decide))
    H.one_mem

omit hs in
private theorem m1940 : g 1940 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1945 (by decide))
    H.one_mem

omit hs in
private theorem m751 : g 751 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1948 (by decide))
    H.one_mem

omit hs in
private theorem m1997 : g 1997 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1950 (by decide))
    H.one_mem

omit hs in
private theorem m1419 : g 1419 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1952 (by decide))
    H.one_mem

omit hs in
private theorem m756 : g 756 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1956 (by decide))
    H.one_mem

omit hs in
private theorem m868 : g 868 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1968 (by decide))
    H.one_mem

omit hs in
private theorem m1078 : g 1078 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1969 (by decide))
    H.one_mem

omit hs in
private theorem m1039 : g 1039 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1973 (by decide))
    H.one_mem

omit hs in
private theorem m1471 : g 1471 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1974 (by decide))
    H.one_mem

omit hs in
private theorem m1251 : g 1251 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1976 (by decide))
    H.one_mem

omit hs in
private theorem m1956 : g 1956 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1983 (by decide))
    H.one_mem

omit hs in
private theorem m774 : g 774 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1985 (by decide))
    H.one_mem

omit hs in
private theorem m1685 : g 1685 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1987 (by decide))
    H.one_mem

omit hs in
private theorem m775 : g 775 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1990 (by decide))
    H.one_mem

omit hs in
private theorem m1687 : g 1687 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1994 (by decide))
    H.one_mem

omit hs in
private theorem m1644 : g 1644 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1996 (by decide))
    H.one_mem

omit hs in
private theorem m781 : g 781 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 1998 (by decide))
    H.one_mem

omit hs in
private theorem m783 : g 783 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2001 (by decide))
    H.one_mem

omit hs in
private theorem m789 : g 789 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2011 (by decide))
    H.one_mem

omit hs in
private theorem m1915 : g 1915 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2015 (by decide))
    H.one_mem

omit hs in
private theorem m1928 : g 1928 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2019 (by decide))
    H.one_mem

omit hs in
private theorem m1146 : g 1146 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2024 (by decide))
    H.one_mem

omit hs in
private theorem m1099 : g 1099 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2026 (by decide))
    H.one_mem

omit hs in
private theorem m1998 : g 1998 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2028 (by decide))
    H.one_mem

omit hs in
private theorem m794 : g 794 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2031 (by decide))
    H.one_mem

omit hs in
private theorem m795 : g 795 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2034 (by decide))
    H.one_mem

omit hs in
private theorem m1777 : g 1777 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2037 (by decide))
    H.one_mem

omit hs in
private theorem m800 : g 800 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2048 (by decide))
    H.one_mem

omit hs in
private theorem m811 : g 811 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2058 (by decide))
    H.one_mem

omit hs in
private theorem m815 : g 815 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2062 (by decide))
    H.one_mem

omit hs in
private theorem m819 : g 819 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2064 (by decide))
    H.one_mem

omit hs in
private theorem m1441 : g 1441 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2071 (by decide))
    H.one_mem

omit hs in
private theorem m1263 : g 1263 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2074 (by decide))
    H.one_mem

omit hs in
private theorem m826 : g 826 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2077 (by decide))
    H.one_mem

omit hs in
private theorem m972 : g 972 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2083 (by decide))
    H.one_mem

omit hs in
private theorem m920 : g 920 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2086 (by decide))
    H.one_mem

omit hs in
private theorem m1179 : g 1179 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2089 (by decide))
    H.one_mem

omit hs in
private theorem m832 : g 832 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2091 (by decide))
    H.one_mem

omit hs in
private theorem m930 : g 930 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2094 (by decide))
    H.one_mem

omit hs in
private theorem m838 : g 838 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2101 (by decide))
    H.one_mem

omit hs in
private theorem m840 : g 840 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2103 (by decide))
    H.one_mem

omit hs in
private theorem m842 : g 842 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2105 (by decide))
    H.one_mem

omit hs in
private theorem m844 : g 844 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2107 (by decide))
    H.one_mem

omit hs in
private theorem m1722 : g 1722 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2110 (by decide))
    H.one_mem

omit hs in
private theorem m927 : g 927 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2113 (by decide))
    H.one_mem

omit hs in
private theorem m848 : g 848 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2117 (by decide))
    H.one_mem

omit hs in
private theorem m1312 : g 1312 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2137 (by decide))
    H.one_mem

omit hs in
private theorem m870 : g 870 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2140 (by decide))
    H.one_mem

omit hs in
private theorem m2035 : g 2035 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2141 (by decide))
    H.one_mem

omit hs in
private theorem m872 : g 872 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2143 (by decide))
    H.one_mem

omit hs in
private theorem m1004 : g 1004 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2145 (by decide))
    H.one_mem

omit hs in
private theorem m1833 : g 1833 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2149 (by decide))
    H.one_mem

omit hs in
private theorem m1044 : g 1044 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2150 (by decide))
    H.one_mem

omit hs in
private theorem m876 : g 876 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2153 (by decide))
    H.one_mem

omit hs in
private theorem m879 : g 879 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2159 (by decide))
    H.one_mem

omit hs in
private theorem m2017 : g 2017 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2161 (by decide))
    H.one_mem

omit hs in
private theorem m881 : g 881 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2164 (by decide))
    H.one_mem

omit hs in
private theorem m882 : g 882 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2167 (by decide))
    H.one_mem

omit hs in
private theorem m1339 : g 1339 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2170 (by decide))
    H.one_mem

omit hs in
private theorem m883 : g 883 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2173 (by decide))
    H.one_mem

omit hs in
private theorem m1811 : g 1811 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2178 (by decide))
    H.one_mem

omit hs in
private theorem m1978 : g 1978 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2183 (by decide))
    H.one_mem

omit hs in
private theorem m889 : g 889 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2189 (by decide))
    H.one_mem

omit hs in
private theorem m892 : g 892 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2191 (by decide))
    H.one_mem

omit hs in
private theorem m895 : g 895 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2194 (by decide))
    H.one_mem

omit hs in
private theorem m1717 : g 1717 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2197 (by decide))
    H.one_mem

omit hs in
private theorem m899 : g 899 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2203 (by decide))
    H.one_mem

omit hs in
private theorem m931 : g 931 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2207 (by decide))
    H.one_mem

omit hs in
private theorem m1300 : g 1300 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2208 (by decide))
    H.one_mem

omit hs in
private theorem m904 : g 904 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2211 (by decide))
    H.one_mem

omit hs in
private theorem m1803 : g 1803 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2215 (by decide))
    H.one_mem

omit hs in
private theorem m911 : g 911 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2221 (by decide))
    H.one_mem

omit hs in
private theorem m917 : g 917 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2229 (by decide))
    H.one_mem

omit hs in
private theorem m1889 : g 1889 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2230 (by decide))
    H.one_mem

omit hs in
private theorem m1469 : g 1469 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2233 (by decide))
    H.one_mem

omit hs in
private theorem m1354 : g 1354 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2238 (by decide))
    H.one_mem

omit hs in
private theorem m1716 : g 1716 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2242 (by decide))
    H.one_mem

omit hs in
private theorem m1877 : g 1877 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2248 (by decide))
    H.one_mem

omit hs in
private theorem m1859 : g 1859 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2251 (by decide))
    H.one_mem

omit hs in
private theorem m1601 : g 1601 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2255 (by decide))
    H.one_mem

omit hs in
private theorem m1068 : g 1068 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2257 (by decide))
    H.one_mem

omit hs in
private theorem m2008 : g 2008 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2260 (by decide))
    H.one_mem

omit hs in
private theorem m1994 : g 1994 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2262 (by decide))
    H.one_mem

omit hs in
private theorem m935 : g 935 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2265 (by decide))
    H.one_mem

omit hs in
private theorem m1126 : g 1126 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2267 (by decide))
    H.one_mem

omit hs in
private theorem m936 : g 936 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2269 (by decide))
    H.one_mem

omit hs in
private theorem m939 : g 939 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2274 (by decide))
    H.one_mem

omit hs in
private theorem m1938 : g 1938 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2277 (by decide))
    H.one_mem

omit hs in
private theorem m942 : g 942 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2281 (by decide))
    H.one_mem

omit hs in
private theorem m1082 : g 1082 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2298 (by decide))
    H.one_mem

omit hs in
private theorem m1640 : g 1640 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2301 (by decide))
    H.one_mem

omit hs in
private theorem m1513 : g 1513 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2308 (by decide))
    H.one_mem

omit hs in
private theorem m1944 : g 1944 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2310 (by decide))
    H.one_mem

omit hs in
private theorem m2024 : g 2024 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2317 (by decide))
    H.one_mem

omit hs in
private theorem m1103 : g 1103 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2321 (by decide))
    H.one_mem

omit hs in
private theorem m966 : g 966 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2327 (by decide))
    H.one_mem

omit hs in
private theorem m967 : g 967 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2329 (by decide))
    H.one_mem

omit hs in
private theorem m969 : g 969 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2330 (by decide))
    H.one_mem

omit hs in
private theorem m1634 : g 1634 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2342 (by decide))
    H.one_mem

omit hs in
private theorem m984 : g 984 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2345 (by decide))
    H.one_mem

omit hs in
private theorem m988 : g 988 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2348 (by decide))
    H.one_mem

omit hs in
private theorem m995 : g 995 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2353 (by decide))
    H.one_mem

omit hs in
private theorem m1842 : g 1842 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2357 (by decide))
    H.one_mem

omit hs in
private theorem m1003 : g 1003 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2365 (by decide))
    H.one_mem

omit hs in
private theorem m1006 : g 1006 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2368 (by decide))
    H.one_mem

omit hs in
private theorem m1008 : g 1008 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2369 (by decide))
    H.one_mem

omit hs in
private theorem m1743 : g 1743 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2385 (by decide))
    H.one_mem

omit hs in
private theorem m1302 : g 1302 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2391 (by decide))
    H.one_mem

omit hs in
private theorem m1034 : g 1034 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2394 (by decide))
    H.one_mem

omit hs in
private theorem m1036 : g 1036 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2397 (by decide))
    H.one_mem

omit hs in
private theorem m1429 : g 1429 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2400 (by decide))
    H.one_mem

omit hs in
private theorem m1037 : g 1037 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2402 (by decide))
    H.one_mem

omit hs in
private theorem m1838 : g 1838 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2407 (by decide))
    H.one_mem

omit hs in
private theorem m1046 : g 1046 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2410 (by decide))
    H.one_mem

omit hs in
private theorem m1726 : g 1726 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2417 (by decide))
    H.one_mem

omit hs in
private theorem m1847 : g 1847 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2418 (by decide))
    H.one_mem

omit hs in
private theorem m1310 : g 1310 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2424 (by decide))
    H.one_mem

omit hs in
private theorem m1056 : g 1056 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2427 (by decide))
    H.one_mem

omit hs in
private theorem m1533 : g 1533 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2430 (by decide))
    H.one_mem

omit hs in
private theorem m1059 : g 1059 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2432 (by decide))
    H.one_mem

omit hs in
private theorem m1061 : g 1061 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2433 (by decide))
    H.one_mem

omit hs in
private theorem m1456 : g 1456 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2435 (by decide))
    H.one_mem

omit hs in
private theorem m1066 : g 1066 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2438 (by decide))
    H.one_mem

omit hs in
private theorem m1072 : g 1072 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2441 (by decide))
    H.one_mem

omit hs in
private theorem m1081 : g 1081 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2448 (by decide))
    H.one_mem

omit hs in
private theorem m1960 : g 1960 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2450 (by decide))
    H.one_mem

omit hs in
private theorem m1086 : g 1086 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2452 (by decide))
    H.one_mem

omit hs in
private theorem m1088 : g 1088 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2455 (by decide))
    H.one_mem

omit hs in
private theorem m1089 : g 1089 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2458 (by decide))
    H.one_mem

omit hs in
private theorem m1092 : g 1092 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2463 (by decide))
    H.one_mem

omit hs in
private theorem m1094 : g 1094 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2466 (by decide))
    H.one_mem

omit hs in
private theorem m1097 : g 1097 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2471 (by decide))
    H.one_mem

omit hs in
private theorem m1834 : g 1834 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2473 (by decide))
    H.one_mem

omit hs in
private theorem m1101 : g 1101 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2476 (by decide))
    H.one_mem

omit hs in
private theorem m1619 : g 1619 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2480 (by decide))
    H.one_mem

omit hs in
private theorem m1278 : g 1278 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2486 (by decide))
    H.one_mem

omit hs in
private theorem m1894 : g 1894 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2488 (by decide))
    H.one_mem

omit hs in
private theorem m1111 : g 1111 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2490 (by decide))
    H.one_mem

omit hs in
private theorem m1767 : g 1767 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2498 (by decide))
    H.one_mem

omit hs in
private theorem m1119 : g 1119 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2500 (by decide))
    H.one_mem

omit hs in
private theorem m1280 : g 1280 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2502 (by decide))
    H.one_mem

omit hs in
private theorem m1293 : g 1293 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2504 (by decide))
    H.one_mem

omit hs in
private theorem m1124 : g 1124 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2509 (by decide))
    H.one_mem

omit hs in
private theorem m1747 : g 1747 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2511 (by decide))
    H.one_mem

omit hs in
private theorem m1130 : g 1130 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2514 (by decide))
    H.one_mem

omit hs in
private theorem m1656 : g 1656 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2523 (by decide))
    H.one_mem

omit hs in
private theorem m1389 : g 1389 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2527 (by decide))
    H.one_mem

omit hs in
private theorem m1138 : g 1138 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2530 (by decide))
    H.one_mem

omit hs in
private theorem m1140 : g 1140 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2534 (by decide))
    H.one_mem

omit hs in
private theorem m1366 : g 1366 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2546 (by decide))
    H.one_mem

omit hs in
private theorem m1149 : g 1149 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2549 (by decide))
    H.one_mem

omit hs in
private theorem m1150 : g 1150 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2552 (by decide))
    H.one_mem

omit hs in
private theorem m1151 : g 1151 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2555 (by decide))
    H.one_mem

omit hs in
private theorem m1153 : g 1153 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2557 (by decide))
    H.one_mem

omit hs in
private theorem m1155 : g 1155 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2559 (by decide))
    H.one_mem

omit hs in
private theorem m1797 : g 1797 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2561 (by decide))
    H.one_mem

omit hs in
private theorem m1548 : g 1548 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2565 (by decide))
    H.one_mem

omit hs in
private theorem m1167 : g 1167 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2570 (by decide))
    H.one_mem

omit hs in
private theorem m1651 : g 1651 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2571 (by decide))
    H.one_mem

omit hs in
private theorem m1171 : g 1171 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2574 (by decide))
    H.one_mem

omit hs in
private theorem m1176 : g 1176 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2579 (by decide))
    H.one_mem

omit hs in
private theorem m1181 : g 1181 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2582 (by decide))
    H.one_mem

omit hs in
private theorem m1182 : g 1182 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2584 (by decide))
    H.one_mem

omit hs in
private theorem m1183 : g 1183 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2586 (by decide))
    H.one_mem

omit hs in
private theorem m1528 : g 1528 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2588 (by decide))
    H.one_mem

omit hs in
private theorem m1759 : g 1759 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2598 (by decide))
    H.one_mem

omit hs in
private theorem m1508 : g 1508 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2606 (by decide))
    H.one_mem

omit hs in
private theorem m1789 : g 1789 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2611 (by decide))
    H.one_mem

omit hs in
private theorem m2023 : g 2023 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2613 (by decide))
    H.one_mem

omit hs in
private theorem m1205 : g 1205 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2620 (by decide))
    H.one_mem

omit hs in
private theorem m1209 : g 1209 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2622 (by decide))
    H.one_mem

omit hs in
private theorem m1980 : g 1980 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2625 (by decide))
    H.one_mem

omit hs in
private theorem m1212 : g 1212 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2627 (by decide))
    H.one_mem

omit hs in
private theorem m1518 : g 1518 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2633 (by decide))
    H.one_mem

omit hs in
private theorem m1217 : g 1217 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2641 (by decide))
    H.one_mem

omit hs in
private theorem m1587 : g 1587 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2642 (by decide))
    H.one_mem

omit hs in
private theorem m1887 : g 1887 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2643 (by decide))
    H.one_mem

omit hs in
private theorem m1949 : g 1949 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2648 (by decide))
    H.one_mem

omit hs in
private theorem m1232 : g 1232 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2657 (by decide))
    H.one_mem

omit hs in
private theorem m1234 : g 1234 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2660 (by decide))
    H.one_mem

omit hs in
private theorem m1242 : g 1242 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2667 (by decide))
    H.one_mem

omit hs in
private theorem m1243 : g 1243 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2669 (by decide))
    H.one_mem

omit hs in
private theorem m1246 : g 1246 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2671 (by decide))
    H.one_mem

omit hs in
private theorem m1248 : g 1248 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2674 (by decide))
    H.one_mem

omit hs in
private theorem m1256 : g 1256 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2683 (by decide))
    H.one_mem

omit hs in
private theorem m1260 : g 1260 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2687 (by decide))
    H.one_mem

omit hs in
private theorem m1271 : g 1271 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2697 (by decide))
    H.one_mem

omit hs in
private theorem m1276 : g 1276 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2701 (by decide))
    H.one_mem

omit hs in
private theorem m1282 : g 1282 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2707 (by decide))
    H.one_mem

omit hs in
private theorem m1517 : g 1517 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2709 (by decide))
    H.one_mem

omit hs in
private theorem m1955 : g 1955 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2713 (by decide))
    H.one_mem

omit hs in
private theorem m2012 : g 2012 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2719 (by decide))
    H.one_mem

omit hs in
private theorem m1297 : g 1297 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2721 (by decide))
    H.one_mem

omit hs in
private theorem m1301 : g 1301 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2725 (by decide))
    H.one_mem

omit hs in
private theorem m1849 : g 1849 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2729 (by decide))
    H.one_mem

omit hs in
private theorem m1358 : g 1358 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2733 (by decide))
    H.one_mem

omit hs in
private theorem m1607 : g 1607 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2736 (by decide))
    H.one_mem

omit hs in
private theorem m1309 : g 1309 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2741 (by decide))
    H.one_mem

omit hs in
private theorem m1710 : g 1710 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2744 (by decide))
    H.one_mem

omit hs in
private theorem m1439 : g 1439 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2746 (by decide))
    H.one_mem

omit hs in
private theorem m1322 : g 1322 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2754 (by decide))
    H.one_mem

omit hs in
private theorem m1397 : g 1397 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2768 (by decide))
    H.one_mem

omit hs in
private theorem m1817 : g 1817 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2774 (by decide))
    H.one_mem

omit hs in
private theorem m1652 : g 1652 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2779 (by decide))
    H.one_mem

omit hs in
private theorem m1344 : g 1344 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2782 (by decide))
    H.one_mem

omit hs in
private theorem m1349 : g 1349 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2785 (by decide))
    H.one_mem

omit hs in
private theorem m1736 : g 1736 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2787 (by decide))
    H.one_mem

omit hs in
private theorem m1360 : g 1360 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2790 (by decide))
    H.one_mem

omit hs in
private theorem m1750 : g 1750 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2793 (by decide))
    H.one_mem

omit hs in
private theorem m1370 : g 1370 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2795 (by decide))
    H.one_mem

omit hs in
private theorem m1912 : g 1912 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2801 (by decide))
    H.one_mem

omit hs in
private theorem m1377 : g 1377 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2804 (by decide))
    H.one_mem

omit hs in
private theorem m1410 : g 1410 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2809 (by decide))
    H.one_mem

omit hs in
private theorem m1387 : g 1387 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2812 (by decide))
    H.one_mem

omit hs in
private theorem m1529 : g 1529 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2824 (by decide))
    H.one_mem

omit hs in
private theorem m1400 : g 1400 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2826 (by decide))
    H.one_mem

omit hs in
private theorem m1407 : g 1407 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2832 (by decide))
    H.one_mem

omit hs in
private theorem m1648 : g 1648 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2837 (by decide))
    H.one_mem

omit hs in
private theorem m1443 : g 1443 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2845 (by decide))
    H.one_mem

omit hs in
private theorem m2014 : g 2014 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2848 (by decide))
    H.one_mem

omit hs in
private theorem m1427 : g 1427 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2854 (by decide))
    H.one_mem

omit hs in
private theorem m1971 : g 1971 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2863 (by decide))
    H.one_mem

omit hs in
private theorem m1882 : g 1882 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2866 (by decide))
    H.one_mem

omit hs in
private theorem m1446 : g 1446 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2869 (by decide))
    H.one_mem

omit hs in
private theorem m2005 : g 2005 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2872 (by decide))
    H.one_mem

omit hs in
private theorem m1984 : g 1984 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2884 (by decide))
    H.one_mem

omit hs in
private theorem m1457 : g 1457 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2889 (by decide))
    H.one_mem

omit hs in
private theorem m1467 : g 1467 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2897 (by decide))
    H.one_mem

omit hs in
private theorem m1493 : g 1493 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2914 (by decide))
    H.one_mem

omit hs in
private theorem m1494 : g 1494 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2917 (by decide))
    H.one_mem

omit hs in
private theorem m1497 : g 1497 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2922 (by decide))
    H.one_mem

omit hs in
private theorem m1502 : g 1502 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2928 (by decide))
    H.one_mem

omit hs in
private theorem m1503 : g 1503 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2930 (by decide))
    H.one_mem

omit hs in
private theorem m1786 : g 1786 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2932 (by decide))
    H.one_mem

omit hs in
private theorem m2051 : g 2051 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2942 (by decide))
    H.one_mem

omit hs in
private theorem m1522 : g 1522 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2946 (by decide))
    H.one_mem

omit hs in
private theorem m1519 : g 1519 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2954 (by decide))
    H.one_mem

omit hs in
private theorem m1521 : g 1521 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2957 (by decide))
    H.one_mem

omit hs in
private theorem m1523 : g 1523 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2960 (by decide))
    H.one_mem

omit hs in
private theorem m1525 : g 1525 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2963 (by decide))
    H.one_mem

omit hs in
private theorem m1537 : g 1537 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2976 (by decide))
    H.one_mem

omit hs in
private theorem m1540 : g 1540 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2979 (by decide))
    H.one_mem

omit hs in
private theorem m1541 : g 1541 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2982 (by decide))
    H.one_mem

omit hs in
private theorem m1542 : g 1542 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2984 (by decide))
    H.one_mem

omit hs in
private theorem m1897 : g 1897 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2989 (by decide))
    H.one_mem

omit hs in
private theorem m1598 : g 1598 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2997 (by decide))
    H.one_mem

omit hs in
private theorem m1557 : g 1557 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 2999 (by decide))
    H.one_mem

omit hs in
private theorem m1566 : g 1566 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3006 (by decide))
    H.one_mem

omit hs in
private theorem m1590 : g 1590 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3030 (by decide))
    H.one_mem

omit hs in
private theorem m1812 : g 1812 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3033 (by decide))
    H.one_mem

omit hs in
private theorem m1608 : g 1608 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3045 (by decide))
    H.one_mem

omit hs in
private theorem m2027 : g 2027 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3059 (by decide))
    H.one_mem

omit hs in
private theorem m1633 : g 1633 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3064 (by decide))
    H.one_mem

omit hs in
private theorem m1771 : g 1771 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3070 (by decide))
    H.one_mem

omit hs in
private theorem m1643 : g 1643 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3080 (by decide))
    H.one_mem

omit hs in
private theorem m2010 : g 2010 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3084 (by decide))
    H.one_mem

omit hs in
private theorem m2015 : g 2015 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3086 (by decide))
    H.one_mem

omit hs in
private theorem m1655 : g 1655 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3089 (by decide))
    H.one_mem

omit hs in
private theorem m1661 : g 1661 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3092 (by decide))
    H.one_mem

omit hs in
private theorem m1921 : g 1921 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3096 (by decide))
    H.one_mem

omit hs in
private theorem m1758 : g 1758 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3099 (by decide))
    H.one_mem

omit hs in
private theorem m1782 : g 1782 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3107 (by decide))
    H.one_mem

omit hs in
private theorem m1952 : g 1952 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3112 (by decide))
    H.one_mem

omit hs in
private theorem m2042 : g 2042 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3117 (by decide))
    H.one_mem

omit hs in
private theorem m1697 : g 1697 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3120 (by decide))
    H.one_mem

omit hs in
private theorem m1714 : g 1714 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3133 (by decide))
    H.one_mem

omit hs in
private theorem m1900 : g 1900 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3141 (by decide))
    H.one_mem

omit hs in
private theorem m1723 : g 1723 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3144 (by decide))
    H.one_mem

omit hs in
private theorem m1963 : g 1963 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3146 (by decide))
    H.one_mem

omit hs in
private theorem m1890 : g 1890 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3148 (by decide))
    H.one_mem

omit hs in
private theorem m1754 : g 1754 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3152 (by decide))
    H.one_mem

omit hs in
private theorem m1734 : g 1734 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3156 (by decide))
    H.one_mem

omit hs in
private theorem m1737 : g 1737 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3159 (by decide))
    H.one_mem

omit hs in
private theorem m2020 : g 2020 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3213 (by decide))
    H.one_mem

omit hs in
private theorem m1823 : g 1823 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3220 (by decide))
    H.one_mem

omit hs in
private theorem m1962 : g 1962 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3223 (by decide))
    H.one_mem

omit hs in
private theorem m1821 : g 1821 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3224 (by decide))
    H.one_mem

omit hs in
private theorem m1965 : g 1965 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3240 (by decide))
    H.one_mem

omit hs in
private theorem m1856 : g 1856 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3251 (by decide))
    H.one_mem

omit hs in
private theorem m1857 : g 1857 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3254 (by decide))
    H.one_mem

omit hs in
private theorem m1888 : g 1888 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3266 (by decide))
    H.one_mem

omit hs in
private theorem m1878 : g 1878 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3269 (by decide))
    H.one_mem

omit hs in
private theorem m1880 : g 1880 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3273 (by decide))
    H.one_mem

omit hs in
private theorem m1907 : g 1907 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3283 (by decide))
    H.one_mem

omit hs in
private theorem m1957 : g 1957 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3290 (by decide))
    H.one_mem

omit hs in
private theorem m1939 : g 1939 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3324 (by decide))
    H.one_mem

omit hs in
private theorem m1942 : g 1942 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3326 (by decide))
    H.one_mem

omit hs in
private theorem m1951 : g 1951 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3332 (by decide))
    H.one_mem

private theorem m1986 : g 1986 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1958")) (hv 5856 (by decide))
    (H.mul_mem (H.inv_mem (m1958 H hs)) H.one_mem)

omit hs in
private theorem m2059 : g 2059 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 3351 (by decide))
    H.one_mem

private theorem m1216 : g 1216 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1")) (hv 4666 (by decide))
    (H.mul_mem (m1 H hs) H.one_mem)

private theorem m1215 : g 1215 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "2")) (hv 4633 (by decide))
    (H.mul_mem (m2 H hs) H.one_mem)

private theorem m963 : g 963 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "3")) (hv 4715 (by decide))
    (H.mul_mem (m3 H hs) H.one_mem)

private theorem m599 : g 599 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "348")) (hv 6014 (by decide))
    (H.mul_mem (m348 H hs) H.one_mem)

omit hs in
private theorem m584 : g 584 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "")) (hv 4976 (by decide))
    H.one_mem

private theorem m1266 : g 1266 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "348")) (hv 6043 (by decide))
    (H.mul_mem (m348 H hs) H.one_mem)

private theorem m1746 : g 1746 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1")) (hv 5864 (by decide))
    (H.mul_mem (m1 H hs) H.one_mem)

private theorem m342 : g 342 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1")) (hv 5886 (by decide))
    (H.mul_mem (m1 H hs) H.one_mem)

private theorem m1409 : g 1409 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "342")) (hv 5972 (by decide))
    (H.mul_mem (m342 H hv hs) H.one_mem)

private theorem m1075 : g 1075 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-3")) (hv 31018 (by decide))
    (H.mul_mem (H.inv_mem (m3 H hs)) H.one_mem)

private theorem m1204 : g 1204 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1409")) (hv 6037 (by decide))
    (H.mul_mem (H.inv_mem (m1409 H hv hs)) H.one_mem)

private theorem m671 : g 671 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1")) (hv 5872 (by decide))
    (H.mul_mem (m1 H hs) H.one_mem)

private theorem m171 : g 171 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "3")) (hv 5871 (by decide))
    (H.mul_mem (m3 H hs) H.one_mem)

private theorem m945 : g 945 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1746")) (hv 5863 (by decide))
    (H.mul_mem (m1746 H hv hs) H.one_mem)

private theorem m1475 : g 1475 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "3")) (hv 7595 (by decide))
    (H.mul_mem (m3 H hs) H.one_mem)

private theorem m39 : g 39 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1")) (hv 7578 (by decide))
    (H.mul_mem (m1 H hs) H.one_mem)

private theorem m1363 : g 1363 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-422")) (hv 7675 (by decide))
    (H.mul_mem (H.inv_mem (m422 H hs)) H.one_mem)

private theorem m1299 : g 1299 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-273")) (hv 7714 (by decide))
    (H.mul_mem (H.inv_mem (m273 H hs)) H.one_mem)

private theorem m707 : g 707 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "2")) (hv 8472 (by decide))
    (H.mul_mem (m2 H hs) H.one_mem)

private theorem m1316 : g 1316 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-3")) (hv 8814 (by decide))
    (H.mul_mem (H.inv_mem (m3 H hs)) H.one_mem)

private theorem m1235 : g 1235 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "23")) (hv 29385 (by decide))
    (H.mul_mem (m23 H hs) H.one_mem)

private theorem m400 : g 400 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1972,-273")) (hv 11858 (by decide))
    (H.mul_mem (m1972 H hs) (H.mul_mem (H.inv_mem (m273 H hs)) H.one_mem))

private theorem m1831 : g 1831 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-2,-1041")) (hv 12001 (by decide))
    (H.mul_mem (H.inv_mem (m2 H hs)) (H.mul_mem (H.inv_mem (m1041 H hs)) H.one_mem))

private theorem m176 : g 176 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-235,-3")) (hv 12702 (by decide))
    (H.mul_mem (H.inv_mem (m235 H hs)) (H.mul_mem (H.inv_mem (m3 H hs)) H.one_mem))

private theorem m1741 : g 1741 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "480,3")) (hv 14730 (by decide))
    (H.mul_mem (m480 H hs) (H.mul_mem (m3 H hs) H.one_mem))

private theorem m869 : g 869 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "2,23")) (hv 14866 (by decide))
    (H.mul_mem (m2 H hs) (H.mul_mem (m23 H hs) H.one_mem))

private theorem m354 : g 354 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1,-688")) (hv 16026 (by decide))
    (H.mul_mem (m1 H hs) (H.mul_mem (H.inv_mem (m688 H hs)) H.one_mem))

private theorem m116 : g 116 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "3,-273")) (hv 16064 (by decide))
    (H.mul_mem (m3 H hs) (H.mul_mem (H.inv_mem (m273 H hs)) H.one_mem))

private theorem m1087 : g 1087 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-906,-348")) (hv 17580 (by decide))
    (H.mul_mem (H.inv_mem (m906 H hs)) (H.mul_mem (H.inv_mem (m348 H hs)) H.one_mem))

private theorem m803 : g 803 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-348,-23,-2")) (hv 17590 (by decide))
    (H.mul_mem (H.inv_mem (m348 H hs)) (H.mul_mem (H.inv_mem (m23 H hs)) (H.mul_mem (H.inv_mem (m2 H hs)) H.one_mem)))

private theorem m20 : g 20 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1,-2")) (hv 17801 (by decide))
    (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (H.inv_mem (m2 H hs)) H.one_mem))

private theorem m216 : g 216 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1772,2")) (hv 19119 (by decide))
    (H.mul_mem (m1772 H hs) (H.mul_mem (m2 H hs) H.one_mem))

private theorem m1018 : g 1018 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "688,1,422")) (hv 21655 (by decide))
    (H.mul_mem (m688 H hs) (H.mul_mem (m1 H hs) (H.mul_mem (m422 H hs) H.one_mem)))

private theorem m1168 : g 1168 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1106,1,2")) (hv 27693 (by decide))
    (H.mul_mem (H.inv_mem (m1106 H hs)) (H.mul_mem (m1 H hs) (H.mul_mem (m2 H hs) H.one_mem)))

private theorem m1824 : g 1824 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "480,-688")) (hv 27924 (by decide))
    (H.mul_mem (m480 H hs) (H.mul_mem (H.inv_mem (m688 H hs)) H.one_mem))

private theorem m1203 : g 1203 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-688,-273,-480")) (hv 28897 (by decide))
    (H.mul_mem (H.inv_mem (m688 H hs)) (H.mul_mem (H.inv_mem (m273 H hs)) (H.mul_mem (H.inv_mem (m480 H hs)) H.one_mem)))

private theorem m19 : g 19 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1,1972,422")) (hv 29555 (by decide))
    (H.mul_mem (m1 H hs) (H.mul_mem (m1972 H hs) (H.mul_mem (m422 H hs) H.one_mem)))

private theorem m758 : g 758 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-480,-1,-688,-1,273,-1972,-1772,-23,1106")) (hv 29593 (by decide))
    (H.mul_mem (H.inv_mem (m480 H hs)) (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (H.inv_mem (m688 H hs)) (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (m273 H hs) (H.mul_mem (H.inv_mem (m1972 H hs)) (H.mul_mem (H.inv_mem (m1772 H hs)) (H.mul_mem (H.inv_mem (m23 H hs)) (H.mul_mem (m1106 H hs) H.one_mem)))))))))

private theorem m533 : g 533 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "480,3,422,1,1106")) (hv 30050 (by decide))
    (H.mul_mem (m480 H hs) (H.mul_mem (m3 H hs) (H.mul_mem (m422 H hs) (H.mul_mem (m1 H hs) (H.mul_mem (m1106 H hs) H.one_mem)))))

private theorem m701 : g 701 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1958,273,480,273,-3,-1958,235,688")) (hv 30768 (by decide))
    (H.mul_mem (H.inv_mem (m1958 H hs)) (H.mul_mem (m273 H hs) (H.mul_mem (m480 H hs) (H.mul_mem (m273 H hs) (H.mul_mem (H.inv_mem (m3 H hs)) (H.mul_mem (H.inv_mem (m1958 H hs)) (H.mul_mem (m235 H hs) (H.mul_mem (m688 H hs) H.one_mem))))))))

private theorem m189 : g 189 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "906,480,-1772")) (hv 30821 (by decide))
    (H.mul_mem (m906 H hs) (H.mul_mem (m480 H hs) (H.mul_mem (H.inv_mem (m1772 H hs)) H.one_mem)))

private theorem m208 : g 208 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1772,235,1,422")) (hv 30858 (by decide))
    (H.mul_mem (H.inv_mem (m1772 H hs)) (H.mul_mem (m235 H hs) (H.mul_mem (m1 H hs) (H.mul_mem (m422 H hs) H.one_mem))))

private theorem m1053 : g 1053 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "688,-906,23,1106,906")) (hv 30933 (by decide))
    (H.mul_mem (m688 H hs) (H.mul_mem (H.inv_mem (m906 H hs)) (H.mul_mem (m23 H hs) (H.mul_mem (m1106 H hs) (H.mul_mem (m906 H hs) H.one_mem)))))

private theorem m1620 : g 1620 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "480,-2,-1,1772")) (hv 30967 (by decide))
    (H.mul_mem (m480 H hs) (H.mul_mem (H.inv_mem (m2 H hs)) (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (m1772 H hs) H.one_mem))))

private theorem m729 : g 729 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1772,3,-1041,23")) (hv 31019 (by decide))
    (H.mul_mem (m1772 H hs) (H.mul_mem (m3 H hs) (H.mul_mem (H.inv_mem (m1041 H hs)) (H.mul_mem (m23 H hs) H.one_mem))))

private theorem m814 : g 814 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-19")) (hv 5048 (by decide))
    (H.mul_mem (H.inv_mem (m19 H hv hs)) H.one_mem)

private theorem m1468 : g 1468 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-20")) (hv 4607 (by decide))
    (H.mul_mem (H.inv_mem (m20 H hv hs)) H.one_mem)

private theorem m1916 : g 1916 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-116")) (hv 5021 (by decide))
    (H.mul_mem (H.inv_mem (m116 H hv hs)) H.one_mem)

private theorem m127 : g 127 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-39")) (hv 5243 (by decide))
    (H.mul_mem (H.inv_mem (m39 H hv hs)) H.one_mem)

private theorem m1425 : g 1425 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-171")) (hv 4970 (by decide))
    (H.mul_mem (H.inv_mem (m171 H hv hs)) H.one_mem)

private theorem m571 : g 571 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-176")) (hv 5219 (by decide))
    (H.mul_mem (H.inv_mem (m176 H hv hs)) H.one_mem)

private theorem m913 : g 913 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-189")) (hv 5275 (by decide))
    (H.mul_mem (H.inv_mem (m189 H hv hs)) H.one_mem)

private theorem m846 : g 846 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-208")) (hv 5001 (by decide))
    (H.mul_mem (H.inv_mem (m208 H hv hs)) H.one_mem)

private theorem m1460 : g 1460 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-216")) (hv 5294 (by decide))
    (H.mul_mem (H.inv_mem (m216 H hv hs)) H.one_mem)

private theorem m281 : g 281 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1216")) (hv 4665 (by decide))
    (H.mul_mem (m1216 H hv hs) H.one_mem)

private theorem m918 : g 918 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-869")) (hv 4857 (by decide))
    (H.mul_mem (H.inv_mem (m869 H hv hs)) H.one_mem)

private theorem m1043 : g 1043 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-342")) (hv 5330 (by decide))
    (H.mul_mem (H.inv_mem (m342 H hv hs)) H.one_mem)

private theorem m615 : g 615 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-533")) (hv 5262 (by decide))
    (H.mul_mem (H.inv_mem (m533 H hv hs)) H.one_mem)

omit hs in
private theorem m1950 : g 1950 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-584")) (hv 5374 (by decide))
    (H.mul_mem (H.inv_mem (m584 H hv)) H.one_mem)

private theorem m1810 : g 1810 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-599")) (hv 5733 (by decide))
    (H.mul_mem (H.inv_mem (m599 H hv hs)) H.one_mem)

private theorem m1192 : g 1192 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-671")) (hv 5353 (by decide))
    (H.mul_mem (H.inv_mem (m671 H hv hs)) H.one_mem)

private theorem m1604 : g 1604 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-729")) (hv 5038 (by decide))
    (H.mul_mem (H.inv_mem (m729 H hv hs)) H.one_mem)

private theorem m1720 : g 1720 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-758")) (hv 4784 (by decide))
    (H.mul_mem (H.inv_mem (m758 H hv hs)) H.one_mem)

private theorem m1050 : g 1050 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1720")) (hv 4783 (by decide))
    (H.mul_mem (m1720 H hv hs) H.one_mem)

private theorem m784 : g 784 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "963")) (hv 4714 (by decide))
    (H.mul_mem (m963 H hv hs) H.one_mem)

private theorem m1304 : g 1304 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-945")) (hv 4941 (by decide))
    (H.mul_mem (H.inv_mem (m945 H hv hs)) H.one_mem)

private theorem m2022 : g 2022 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1018")) (hv 5572 (by decide))
    (H.mul_mem (H.inv_mem (m1018 H hv hs)) H.one_mem)

private theorem m1364 : g 1364 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1053")) (hv 5734 (by decide))
    (H.mul_mem (H.inv_mem (m1053 H hv hs)) H.one_mem)

private theorem m1738 : g 1738 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1203")) (hv 4838 (by decide))
    (H.mul_mem (H.inv_mem (m1203 H hv hs)) H.one_mem)

private theorem m1245 : g 1245 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1204")) (hv 5357 (by decide))
    (H.mul_mem (H.inv_mem (m1204 H hv hs)) H.one_mem)

private theorem m1415 : g 1415 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1266")) (hv 5225 (by decide))
    (H.mul_mem (H.inv_mem (m1266 H hv hs)) H.one_mem)

private theorem m1384 : g 1384 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1299")) (hv 5248 (by decide))
    (H.mul_mem (H.inv_mem (m1299 H hv hs)) H.one_mem)

private theorem m1414 : g 1414 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1409")) (hv 5093 (by decide))
    (H.mul_mem (H.inv_mem (m1409 H hv hs)) H.one_mem)

private theorem m2007 : g 2007 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1475")) (hv 5793 (by decide))
    (H.mul_mem (H.inv_mem (m1475 H hv hs)) H.one_mem)

private theorem m1992 : g 1992 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1741")) (hv 5457 (by decide))
    (H.mul_mem (H.inv_mem (m1741 H hv hs)) H.one_mem)

private theorem m1954 : g 1954 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1746")) (hv 31020 (by decide))
    (H.mul_mem (H.inv_mem (m1746 H hv hs)) H.one_mem)

private theorem m1937 : g 1937 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1215")) (hv 31021 (by decide))
    (H.mul_mem (m1215 H hv hs) H.one_mem)

private theorem m472 : g 472 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-176")) (hv 5946 (by decide))
    (H.mul_mem (H.inv_mem (m176 H hv hs)) H.one_mem)

private theorem m1347 : g 1347 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1018")) (hv 6147 (by decide))
    (H.mul_mem (m1018 H hv hs) H.one_mem)

private theorem m1981 : g 1981 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "533")) (hv 31022 (by decide))
    (H.mul_mem (m533 H hv hs) H.one_mem)

private theorem m1988 : g 1988 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1316")) (hv 6062 (by decide))
    (H.mul_mem (m1316 H hv hs) H.one_mem)

private theorem m511 : g 511 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "208")) (hv 6138 (by decide))
    (H.mul_mem (m208 H hv hs) H.one_mem)

private theorem m242 : g 242 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "945")) (hv 5920 (by decide))
    (H.mul_mem (m945 H hv hs) H.one_mem)

private theorem m506 : g 506 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-671")) (hv 5937 (by decide))
    (H.mul_mem (H.inv_mem (m671 H hv hs)) H.one_mem)

private theorem m730 : g 730 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "729")) (hv 6015 (by decide))
    (H.mul_mem (m729 H hv hs) H.one_mem)

private theorem m1365 : g 1365 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1053")) (hv 6297 (by decide))
    (H.mul_mem (H.inv_mem (m1053 H hv hs)) H.one_mem)

private theorem m1017 : g 1017 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "20")) (hv 7717 (by decide))
    (H.mul_mem (m20 H hv hs) H.one_mem)

private theorem m1466 : g 1466 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "400,-3")) (hv 10158 (by decide))
    (H.mul_mem (m400 H hv hs) (H.mul_mem (H.inv_mem (m3 H hs)) H.one_mem))

private theorem m1585 : g 1585 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-20,19,-2")) (hv 11001 (by decide))
    (H.mul_mem (H.inv_mem (m20 H hv hs)) (H.mul_mem (m19 H hv hs) (H.mul_mem (H.inv_mem (m2 H hs)) H.one_mem)))

private theorem m1715 : g 1715 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1741,-1")) (hv 11191 (by decide))
    (H.mul_mem (H.inv_mem (m1741 H hv hs)) (H.mul_mem (H.inv_mem (m1 H hs)) H.one_mem))

private theorem m277 : g 277 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-216,-189")) (hv 11841 (by decide))
    (H.mul_mem (H.inv_mem (m216 H hv hs)) (H.mul_mem (H.inv_mem (m189 H hv hs)) H.one_mem))

private theorem m617 : g 617 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-19,-480")) (hv 11941 (by decide))
    (H.mul_mem (H.inv_mem (m19 H hv hs)) (H.mul_mem (H.inv_mem (m480 H hs)) H.one_mem))

private theorem m1318 : g 1318 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-2,20")) (hv 11956 (by decide))
    (H.mul_mem (H.inv_mem (m2 H hs)) (H.mul_mem (m20 H hv hs) H.one_mem))

private theorem m932 : g 932 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-354,208")) (hv 11964 (by decide))
    (H.mul_mem (H.inv_mem (m354 H hv hs)) (H.mul_mem (m208 H hv hs) H.one_mem))

private theorem m137 : g 137 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-19,-688")) (hv 11972 (by decide))
    (H.mul_mem (H.inv_mem (m19 H hv hs)) (H.mul_mem (H.inv_mem (m688 H hs)) H.one_mem))

private theorem m1449 : g 1449 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1824,-1")) (hv 12692 (by decide))
    (H.mul_mem (m1824 H hv hs) (H.mul_mem (H.inv_mem (m1 H hs)) H.one_mem))

private theorem m395 : g 395 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1,1168")) (hv 12759 (by decide))
    (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (m1168 H hv hs) H.one_mem))

private theorem m1253 : g 1253 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-803,-2")) (hv 12794 (by decide))
    (H.mul_mem (H.inv_mem (m803 H hv hs)) (H.mul_mem (H.inv_mem (m2 H hs)) H.one_mem))

private theorem m1223 : g 1223 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "2,-116")) (hv 12889 (by decide))
    (H.mul_mem (m2 H hs) (H.mul_mem (H.inv_mem (m116 H hv hs)) H.one_mem))

private theorem m341 : g 341 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "235,1018")) (hv 13729 (by decide))
    (H.mul_mem (m235 H hs) (H.mul_mem (m1018 H hv hs) H.one_mem))

private theorem m1778 : g 1778 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-189,906")) (hv 14705 (by decide))
    (H.mul_mem (H.inv_mem (m189 H hv hs)) (H.mul_mem (m906 H hs) H.one_mem))

private theorem m970 : g 970 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "533,-20")) (hv 14823 (by decide))
    (H.mul_mem (m533 H hv hs) (H.mul_mem (H.inv_mem (m20 H hv hs)) H.one_mem))

private theorem m463 : g 463 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-208,-1620,1958,-2")) (hv 14832 (by decide))
    (H.mul_mem (H.inv_mem (m208 H hv hs)) (H.mul_mem (H.inv_mem (m1620 H hv hs)) (H.mul_mem (m1958 H hs) (H.mul_mem (H.inv_mem (m2 H hs)) H.one_mem))))

private theorem m14 : g 14 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1203,-273,-2")) (hv 15033 (by decide))
    (H.mul_mem (m1203 H hv hs) (H.mul_mem (H.inv_mem (m273 H hs)) (H.mul_mem (H.inv_mem (m2 H hs)) H.one_mem)))

private theorem m231 : g 231 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-758,1")) (hv 15965 (by decide))
    (H.mul_mem (H.inv_mem (m758 H hv hs)) (H.mul_mem (m1 H hs) H.one_mem))

private theorem m741 : g 741 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "480,19,-3")) (hv 16150 (by decide))
    (H.mul_mem (m480 H hs) (H.mul_mem (m19 H hv hs) (H.mul_mem (H.inv_mem (m3 H hs)) H.one_mem)))

private theorem m228 : g 228 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "273,-1972,-1018,-235,533")) (hv 19025 (by decide))
    (H.mul_mem (m273 H hs) (H.mul_mem (H.inv_mem (m1972 H hs)) (H.mul_mem (H.inv_mem (m1018 H hv hs)) (H.mul_mem (H.inv_mem (m235 H hs)) (H.mul_mem (m533 H hv hs) H.one_mem)))))

private theorem m360 : g 360 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-480,235,1018,2")) (hv 19061 (by decide))
    (H.mul_mem (H.inv_mem (m480 H hs)) (H.mul_mem (m235 H hs) (H.mul_mem (m1018 H hv hs) (H.mul_mem (m2 H hs) H.one_mem))))

private theorem m1424 : g 1424 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-480,-1,-23,1106,-758,-1")) (hv 20277 (by decide))
    (H.mul_mem (H.inv_mem (m480 H hs)) (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (H.inv_mem (m23 H hs)) (H.mul_mem (m1106 H hs) (H.mul_mem (H.inv_mem (m758 H hv hs)) (H.mul_mem (H.inv_mem (m1 H hs)) H.one_mem))))))

private theorem m322 : g 322 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "3,-1972,701,2,1972")) (hv 20312 (by decide))
    (H.mul_mem (m3 H hs) (H.mul_mem (H.inv_mem (m1972 H hs)) (H.mul_mem (m701 H hv hs) (H.mul_mem (m2 H hs) (H.mul_mem (m1972 H hs) H.one_mem)))))

private theorem m1208 : g 1208 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-348,-1053,273,-1203,422,-1018")) (hv 20353 (by decide))
    (H.mul_mem (H.inv_mem (m348 H hs)) (H.mul_mem (H.inv_mem (m1053 H hv hs)) (H.mul_mem (m273 H hs) (H.mul_mem (H.inv_mem (m1203 H hv hs)) (H.mul_mem (m422 H hs) (H.mul_mem (H.inv_mem (m1018 H hv hs)) H.one_mem))))))

private theorem m12 : g 12 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "533,-1106,1")) (hv 20416 (by decide))
    (H.mul_mem (m533 H hv hs) (H.mul_mem (H.inv_mem (m1106 H hs)) (H.mul_mem (m1 H hs) H.one_mem)))

private theorem m37 : g 37 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-2,23,-729")) (hv 24223 (by decide))
    (H.mul_mem (H.inv_mem (m2 H hs)) (H.mul_mem (m23 H hs) (H.mul_mem (H.inv_mem (m729 H hv hs)) H.one_mem)))

private theorem m197 : g 197 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "348,906,729,-1168,-1,-189,-1")) (hv 24749 (by decide))
    (H.mul_mem (m348 H hs) (H.mul_mem (m906 H hs) (H.mul_mem (m729 H hv hs) (H.mul_mem (H.inv_mem (m1168 H hv hs)) (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (H.inv_mem (m189 H hv hs)) (H.mul_mem (H.inv_mem (m1 H hs)) H.one_mem)))))))

private theorem m119 : g 119 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1620,208,-422,480,-729")) (hv 26775 (by decide))
    (H.mul_mem (m1620 H hv hs) (H.mul_mem (m208 H hv hs) (H.mul_mem (H.inv_mem (m422 H hs)) (H.mul_mem (m480 H hs) (H.mul_mem (H.inv_mem (m729 H hv hs)) H.one_mem)))))

private theorem m514 : g 514 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1958,1620,208,1235,-23")) (hv 28535 (by decide))
    (H.mul_mem (H.inv_mem (m1958 H hs)) (H.mul_mem (m1620 H hv hs) (H.mul_mem (m208 H hv hs) (H.mul_mem (m1235 H hv hs) (H.mul_mem (H.inv_mem (m23 H hs)) H.one_mem)))))

private theorem m735 : g 735 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1115,3,-273,-701,-1958,-480,422,1972,-1772,-906")) (hv 29203 (by decide))
    (H.mul_mem (m1115 H hs) (H.mul_mem (m3 H hs) (H.mul_mem (H.inv_mem (m273 H hs)) (H.mul_mem (H.inv_mem (m701 H hv hs)) (H.mul_mem (H.inv_mem (m1958 H hs)) (H.mul_mem (H.inv_mem (m480 H hs)) (H.mul_mem (m422 H hs) (H.mul_mem (m1972 H hs) (H.mul_mem (H.inv_mem (m1772 H hs)) (H.mul_mem (H.inv_mem (m906 H hs)) H.one_mem))))))))))

private theorem m475 : g 475 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-3,1053,688")) (hv 29575 (by decide))
    (H.mul_mem (H.inv_mem (m3 H hs)) (H.mul_mem (m1053 H hv hs) (H.mul_mem (m688 H hs) H.one_mem)))

private theorem m274 : g 274 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "729,-23,-348")) (hv 29583 (by decide))
    (H.mul_mem (m729 H hv hs) (H.mul_mem (H.inv_mem (m23 H hs)) (H.mul_mem (H.inv_mem (m348 H hs)) H.one_mem)))

private theorem m84 : g 84 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-3,1772,1620")) (hv 30033 (by decide))
    (H.mul_mem (H.inv_mem (m3 H hs)) (H.mul_mem (m1772 H hs) (H.mul_mem (m1620 H hv hs) H.one_mem)))

private theorem m243 : g 243 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1,422,-208,-2,-1106,-1106,-1,-422,-3,-1115,348,-1115,-1620,480,-1041,-422,-3,-348,1115,-23,906,-688")) (hv 31023 (by decide))
    (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (m422 H hs) (H.mul_mem (H.inv_mem (m208 H hv hs)) (H.mul_mem (H.inv_mem (m2 H hs)) (H.mul_mem (H.inv_mem (m1106 H hs)) (H.mul_mem (H.inv_mem (m1106 H hs)) (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (H.inv_mem (m422 H hs)) (H.mul_mem (H.inv_mem (m3 H hs)) (H.mul_mem (H.inv_mem (m1115 H hs)) (H.mul_mem (m348 H hs) (H.mul_mem (H.inv_mem (m1115 H hs)) (H.mul_mem (H.inv_mem (m1620 H hv hs)) (H.mul_mem (m480 H hs) (H.mul_mem (H.inv_mem (m1041 H hs)) (H.mul_mem (H.inv_mem (m422 H hs)) (H.mul_mem (H.inv_mem (m3 H hs)) (H.mul_mem (H.inv_mem (m348 H hs)) (H.mul_mem (m1115 H hs) (H.mul_mem (H.inv_mem (m23 H hs)) (H.mul_mem (m906 H hs) (H.mul_mem (H.inv_mem (m688 H hs)) H.one_mem))))))))))))))))))))))

private theorem m288 : g 288 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-729,1,-688,-1053,688,-23,906,2")) (hv 30577 (by decide))
    (H.mul_mem (H.inv_mem (m729 H hv hs)) (H.mul_mem (m1 H hs) (H.mul_mem (H.inv_mem (m688 H hs)) (H.mul_mem (H.inv_mem (m1053 H hv hs)) (H.mul_mem (m688 H hs) (H.mul_mem (H.inv_mem (m23 H hs)) (H.mul_mem (m906 H hs) (H.mul_mem (m2 H hs) H.one_mem))))))))

private theorem m1602 : g 1602 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-12")) (hv 4632 (by decide))
    (H.mul_mem (H.inv_mem (m12 H hv hs)) H.one_mem)

private theorem m1751 : g 1751 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-84")) (hv 4946 (by decide))
    (H.mul_mem (H.inv_mem (m84 H hv hs)) H.one_mem)

private theorem m251 : g 251 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-119")) (hv 5718 (by decide))
    (H.mul_mem (H.inv_mem (m119 H hv hs)) H.one_mem)

private theorem m1445 : g 1445 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1365")) (hv 4777 (by decide))
    (H.mul_mem (H.inv_mem (m1365 H hv hs)) H.one_mem)

private theorem m1599 : g 1599 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-360")) (hv 4839 (by decide))
    (H.mul_mem (H.inv_mem (m360 H hv hs)) H.one_mem)

private theorem m392 : g 392 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-137")) (hv 5132 (by decide))
    (H.mul_mem (H.inv_mem (m137 H hv hs)) H.one_mem)

private theorem m680 : g 680 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-617")) (hv 5400 (by decide))
    (H.mul_mem (H.inv_mem (m617 H hv hs)) H.one_mem)

private theorem m1792 : g 1792 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-231")) (hv 5051 (by decide))
    (H.mul_mem (H.inv_mem (m231 H hv hs)) H.one_mem)

private theorem m807 : g 807 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-242")) (hv 5480 (by decide))
    (H.mul_mem (H.inv_mem (m242 H hv hs)) H.one_mem)

private theorem m1668 : g 1668 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-274")) (hv 5379 (by decide))
    (H.mul_mem (H.inv_mem (m274 H hv hs)) H.one_mem)

private theorem m812 : g 812 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-277")) (hv 5303 (by decide))
    (H.mul_mem (H.inv_mem (m277 H hv hs)) H.one_mem)

private theorem m1368 : g 1368 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-288")) (hv 4930 (by decide))
    (H.mul_mem (H.inv_mem (m288 H hv hs)) H.one_mem)

private theorem m1748 : g 1748 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-730")) (hv 5498 (by decide))
    (H.mul_mem (H.inv_mem (m730 H hv hs)) H.one_mem)

private theorem m1185 : g 1185 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1050")) (hv 5369 (by decide))
    (H.mul_mem (H.inv_mem (m1050 H hv hs)) H.one_mem)

private theorem m2054 : g 2054 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1318")) (hv 31024 (by decide))
    (H.mul_mem (H.inv_mem (m1318 H hv hs)) H.one_mem)

private theorem m507 : g 507 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-506")) (hv 4828 (by decide))
    (H.mul_mem (H.inv_mem (m506 H hv hs)) H.one_mem)

private theorem m1600 : g 1600 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-511")) (hv 5180 (by decide))
    (H.mul_mem (H.inv_mem (m511 H hv hs)) H.one_mem)

private theorem m1054 : g 1054 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-735")) (hv 5540 (by decide))
    (H.mul_mem (H.inv_mem (m735 H hv hs)) H.one_mem)

private theorem m1562 : g 1562 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1017")) (hv 5329 (by decide))
    (H.mul_mem (H.inv_mem (m1017 H hv hs)) H.one_mem)

private theorem m1376 : g 1376 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1223")) (hv 5320 (by decide))
    (H.mul_mem (H.inv_mem (m1223 H hv hs)) H.one_mem)

private theorem m1906 : g 1906 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1715")) (hv 5129 (by decide))
    (H.mul_mem (H.inv_mem (m1715 H hv hs)) H.one_mem)

private theorem m2034 : g 2034 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1778")) (hv 31025 (by decide))
    (H.mul_mem (H.inv_mem (m1778 H hv hs)) H.one_mem)

private theorem m1953 : g 1953 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "514")) (hv 5987 (by decide))
    (H.mul_mem (m514 H hv hs) H.one_mem)

private theorem m1172 : g 1172 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "475")) (hv 6249 (by decide))
    (H.mul_mem (m475 H hv hs) H.one_mem)

private theorem m740 : g 740 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1953")) (hv 5974 (by decide))
    (H.mul_mem (H.inv_mem (m1953 H hv hs)) H.one_mem)

private theorem m106 : g 106 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-242")) (hv 5949 (by decide))
    (H.mul_mem (H.inv_mem (m242 H hv hs)) H.one_mem)

private theorem m965 : g 965 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "84")) (hv 5895 (by decide))
    (H.mul_mem (m84 H hv hs) H.one_mem)

private theorem m247 : g 247 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-965")) (hv 5894 (by decide))
    (H.mul_mem (H.inv_mem (m965 H hv hs)) H.one_mem)

private theorem m1277 : g 1277 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-37")) (hv 6237 (by decide))
    (H.mul_mem (H.inv_mem (m37 H hv hs)) H.one_mem)

private theorem m1733 : g 1733 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-735")) (hv 6313 (by decide))
    (H.mul_mem (H.inv_mem (m735 H hv hs)) H.one_mem)

private theorem m647 : g 647 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-12")) (hv 7570 (by decide))
    (H.mul_mem (H.inv_mem (m12 H hv hs)) H.one_mem)

private theorem m1326 : g 1326 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1208")) (hv 7655 (by decide))
    (H.mul_mem (m1208 H hv hs) H.one_mem)

private theorem m1306 : g 1306 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-14")) (hv 8476 (by decide))
    (H.mul_mem (H.inv_mem (m14 H hv hs)) H.one_mem)

private theorem m491 : g 491 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "228")) (hv 8478 (by decide))
    (H.mul_mem (m228 H hv hs) H.one_mem)

private theorem m1417 : g 1417 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "514,1831")) (hv 10069 (by decide))
    (H.mul_mem (m514 H hv hs) (H.mul_mem (m1831 H hv hs) H.one_mem))

private theorem m393 : g 393 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-137,-514")) (hv 10103 (by decide))
    (H.mul_mem (H.inv_mem (m137 H hv hs)) (H.mul_mem (H.inv_mem (m514 H hv hs)) H.one_mem))

private theorem m1437 : g 1437 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-14,-2")) (hv 10111 (by decide))
    (H.mul_mem (H.inv_mem (m14 H hv hs)) (H.mul_mem (H.inv_mem (m2 H hs)) H.one_mem))

private theorem m1296 : g 1296 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-228,-235")) (hv 10161 (by decide))
    (H.mul_mem (H.inv_mem (m228 H hv hs)) (H.mul_mem (H.inv_mem (m235 H hs)) H.one_mem))

private theorem m276 : g 276 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-514,-2")) (hv 10219 (by decide))
    (H.mul_mem (H.inv_mem (m514 H hv hs)) (H.mul_mem (H.inv_mem (m2 H hs)) H.one_mem))

private theorem m22 : g 22 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-37,-3")) (hv 11003 (by decide))
    (H.mul_mem (H.inv_mem (m37 H hv hs)) (H.mul_mem (H.inv_mem (m3 H hs)) H.one_mem))

private theorem m877 : g 877 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-37,-906")) (hv 11057 (by decide))
    (H.mul_mem (H.inv_mem (m37 H hv hs)) (H.mul_mem (H.inv_mem (m906 H hs)) H.one_mem))

private theorem m236 : g 236 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-228,-400")) (hv 11115 (by decide))
    (H.mul_mem (H.inv_mem (m228 H hv hs)) (H.mul_mem (H.inv_mem (m400 H hv hs)) H.one_mem))

private theorem m289 : g 289 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1053,-475")) (hv 11158 (by decide))
    (H.mul_mem (m1053 H hv hs) (H.mul_mem (H.inv_mem (m475 H hv hs)) H.one_mem))

private theorem m604 : g 604 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-37,274,-3")) (hv 11180 (by decide))
    (H.mul_mem (H.inv_mem (m37 H hv hs)) (H.mul_mem (m274 H hv hs) (H.mul_mem (H.inv_mem (m3 H hs)) H.one_mem)))

private theorem m1250 : g 1250 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-3,-475")) (hv 11198 (by decide))
    (H.mul_mem (H.inv_mem (m3 H hs)) (H.mul_mem (H.inv_mem (m475 H hv hs)) H.one_mem))

private theorem m110 : g 110 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1,274")) (hv 11889 (by decide))
    (H.mul_mem (m1 H hs) (H.mul_mem (m274 H hv hs) H.one_mem))

private theorem m1966 : g 1966 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1778,274,-480")) (hv 12053 (by decide))
    (H.mul_mem (m1778 H hv hs) (H.mul_mem (m274 H hv hs) (H.mul_mem (H.inv_mem (m480 H hs)) H.one_mem)))

private theorem m112 : g 112 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "741,729")) (hv 13676 (by decide))
    (H.mul_mem (m741 H hv hs) (H.mul_mem (m729 H hv hs) H.one_mem))

private theorem m499 : g 499 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-729,-906,-735")) (hv 13804 (by decide))
    (H.mul_mem (H.inv_mem (m729 H hv hs)) (H.mul_mem (H.inv_mem (m906 H hs)) (H.mul_mem (H.inv_mem (m735 H hv hs)) H.one_mem)))

private theorem m38 : g 38 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-533,12")) (hv 13867 (by decide))
    (H.mul_mem (H.inv_mem (m533 H hv hs)) (H.mul_mem (m12 H hv hs) H.one_mem))

private theorem m104 : g 104 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1620,-84")) (hv 14758 (by decide))
    (H.mul_mem (H.inv_mem (m1620 H hv hs)) (H.mul_mem (H.inv_mem (m84 H hv hs)) H.one_mem))

private theorem m1244 : g 1244 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "19,3,-119")) (hv 14770 (by decide))
    (H.mul_mem (m19 H hv hs) (H.mul_mem (m3 H hs) (H.mul_mem (H.inv_mem (m119 H hv hs)) H.one_mem)))

private theorem m585 : g 585 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-84,1620,-37,-273,-354")) (hv 14970 (by decide))
    (H.mul_mem (H.inv_mem (m84 H hv hs)) (H.mul_mem (m1620 H hv hs) (H.mul_mem (H.inv_mem (m37 H hv hs)) (H.mul_mem (H.inv_mem (m273 H hs)) (H.mul_mem (H.inv_mem (m354 H hv hs)) H.one_mem)))))

private theorem m933 : g 933 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "475,348")) (hv 14974 (by decide))
    (H.mul_mem (m475 H hv hs) (H.mul_mem (m348 H hs) H.one_mem))

private theorem m1188 : g 1188 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-235,3,37")) (hv 15007 (by decide))
    (H.mul_mem (H.inv_mem (m235 H hs)) (H.mul_mem (m3 H hs) (H.mul_mem (m37 H hv hs) H.one_mem)))

private theorem m841 : g 841 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "12,-1958")) (hv 15043 (by decide))
    (H.mul_mem (m12 H hv hs) (H.mul_mem (H.inv_mem (m1958 H hs)) H.one_mem))

private theorem m323 : g 323 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "84,235,228")) (hv 15987 (by decide))
    (H.mul_mem (m84 H hv hs) (H.mul_mem (m235 H hs) (H.mul_mem (m228 H hv hs) H.one_mem)))

private theorem m1420 : g 1420 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1235,-235,-84,-3")) (hv 16003 (by decide))
    (H.mul_mem (m1235 H hv hs) (H.mul_mem (H.inv_mem (m235 H hs)) (H.mul_mem (H.inv_mem (m84 H hv hs)) (H.mul_mem (H.inv_mem (m3 H hs)) H.one_mem))))

private theorem m616 : g 616 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-37,-1972,-12")) (hv 16011 (by decide))
    (H.mul_mem (H.inv_mem (m37 H hv hs)) (H.mul_mem (H.inv_mem (m1972 H hs)) (H.mul_mem (H.inv_mem (m12 H hv hs)) H.one_mem)))

private theorem m302 : g 302 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "216,-514")) (hv 16050 (by decide))
    (H.mul_mem (m216 H hv hs) (H.mul_mem (H.inv_mem (m514 H hv hs)) H.one_mem))

private theorem m1594 : g 1594 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-514,1972,422")) (hv 16210 (by decide))
    (H.mul_mem (H.inv_mem (m514 H hv hs)) (H.mul_mem (m1972 H hs) (H.mul_mem (m422 H hs) H.one_mem)))

private theorem m172 : g 172 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "84,422")) (hv 16226 (by decide))
    (H.mul_mem (m84 H hv hs) (H.mul_mem (m422 H hs) H.one_mem))

private theorem m1112 : g 1112 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1115,-274,37")) (hv 16331 (by decide))
    (H.mul_mem (H.inv_mem (m1115 H hs)) (H.mul_mem (H.inv_mem (m274 H hv hs)) (H.mul_mem (m37 H hv hs) H.one_mem)))

private theorem m801 : g 801 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-348,-475,-514")) (hv 16414 (by decide))
    (H.mul_mem (H.inv_mem (m348 H hs)) (H.mul_mem (H.inv_mem (m475 H hv hs)) (H.mul_mem (H.inv_mem (m514 H hv hs)) H.one_mem)))

private theorem m1649 : g 1649 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1,-197,735")) (hv 17577 (by decide))
    (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (H.inv_mem (m197 H hv hs)) (H.mul_mem (m735 H hv hs) H.one_mem)))

private theorem m1408 : g 1408 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-360,-360,-3,-84")) (hv 17647 (by decide))
    (H.mul_mem (H.inv_mem (m360 H hv hs)) (H.mul_mem (H.inv_mem (m360 H hv hs)) (H.mul_mem (H.inv_mem (m3 H hs)) (H.mul_mem (H.inv_mem (m84 H hv hs)) H.one_mem))))

private theorem m138 : g 138 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "514,2,1972,-273,228")) (hv 17664 (by decide))
    (H.mul_mem (m514 H hv hs) (H.mul_mem (m2 H hs) (H.mul_mem (m1972 H hs) (H.mul_mem (H.inv_mem (m273 H hs)) (H.mul_mem (m228 H hv hs) H.one_mem)))))

private theorem m798 : g 798 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1235,1424,3,-906,2")) (hv 17706 (by decide))
    (H.mul_mem (m1235 H hv hs) (H.mul_mem (m1424 H hv hs) (H.mul_mem (m3 H hs) (H.mul_mem (H.inv_mem (m906 H hs)) (H.mul_mem (m2 H hs) H.one_mem)))))

private theorem m255 : g 255 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "322,-84,1620,-322")) (hv 17715 (by decide))
    (H.mul_mem (m322 H hv hs) (H.mul_mem (H.inv_mem (m84 H hv hs)) (H.mul_mem (m1620 H hv hs) (H.mul_mem (H.inv_mem (m322 H hv hs)) H.one_mem))))

private theorem m1686 : g 1686 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1958,-514,-1041,-2")) (hv 17767 (by decide))
    (H.mul_mem (m1958 H hs) (H.mul_mem (H.inv_mem (m514 H hv hs)) (H.mul_mem (H.inv_mem (m1041 H hs)) (H.mul_mem (H.inv_mem (m2 H hs)) H.one_mem))))

private theorem m258 : g 258 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "322,208,-514,-208,-322")) (hv 17790 (by decide))
    (H.mul_mem (m322 H hv hs) (H.mul_mem (m208 H hv hs) (H.mul_mem (H.inv_mem (m514 H hv hs)) (H.mul_mem (H.inv_mem (m208 H hv hs)) (H.mul_mem (H.inv_mem (m322 H hv hs)) H.one_mem)))))

private theorem m282 : g 282 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "84,758,-348,197")) (hv 18927 (by decide))
    (H.mul_mem (m84 H hv hs) (H.mul_mem (m758 H hv hs) (H.mul_mem (H.inv_mem (m348 H hs)) (H.mul_mem (m197 H hv hs) H.one_mem))))

private theorem m1428 : g 1428 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "273,-1203,480,1424,1")) (hv 18972 (by decide))
    (H.mul_mem (m273 H hs) (H.mul_mem (H.inv_mem (m1203 H hv hs)) (H.mul_mem (m480 H hs) (H.mul_mem (m1424 H hv hs) (H.mul_mem (m1 H hs) H.one_mem)))))

private theorem m30 : g 30 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-701,-1958,-37,1958,701")) (hv 18984 (by decide))
    (H.mul_mem (H.inv_mem (m701 H hv hs)) (H.mul_mem (H.inv_mem (m1958 H hs)) (H.mul_mem (H.inv_mem (m37 H hv hs)) (H.mul_mem (m1958 H hs) (H.mul_mem (m701 H hv hs) H.one_mem)))))

private theorem m1703 : g 1703 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-19,1,37,208")) (hv 19176 (by decide))
    (H.mul_mem (H.inv_mem (m19 H hv hs)) (H.mul_mem (m1 H hs) (H.mul_mem (m37 H hv hs) (H.mul_mem (m208 H hv hs) H.one_mem))))

private theorem m799 : g 799 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-3,-273,-23,906,274,-480")) (hv 20223 (by decide))
    (H.mul_mem (H.inv_mem (m3 H hs)) (H.mul_mem (H.inv_mem (m273 H hs)) (H.mul_mem (H.inv_mem (m23 H hs)) (H.mul_mem (m906 H hs) (H.mul_mem (m274 H hv hs) (H.mul_mem (H.inv_mem (m480 H hs)) H.one_mem))))))

private theorem m863 : g 863 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1106,-480,422,37,274,1115")) (hv 20250 (by decide))
    (H.mul_mem (H.inv_mem (m1106 H hs)) (H.mul_mem (H.inv_mem (m480 H hs)) (H.mul_mem (m422 H hs) (H.mul_mem (m37 H hv hs) (H.mul_mem (m274 H hv hs) (H.mul_mem (m1115 H hs) H.one_mem))))))

private theorem m764 : g 764 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-2,-1018,-235,-1,688,-729,274")) (hv 20336 (by decide))
    (H.mul_mem (H.inv_mem (m2 H hs)) (H.mul_mem (H.inv_mem (m1018 H hv hs)) (H.mul_mem (H.inv_mem (m235 H hs)) (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (m688 H hs) (H.mul_mem (H.inv_mem (m729 H hv hs)) (H.mul_mem (m274 H hv hs) H.one_mem)))))))

private theorem m250 : g 250 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1620,84,-1972,2,-23,1106,-758")) (hv 20343 (by decide))
    (H.mul_mem (H.inv_mem (m1620 H hv hs)) (H.mul_mem (m84 H hv hs) (H.mul_mem (H.inv_mem (m1972 H hs)) (H.mul_mem (m2 H hs) (H.mul_mem (H.inv_mem (m23 H hs)) (H.mul_mem (m1106 H hs) (H.mul_mem (H.inv_mem (m758 H hv hs)) H.one_mem)))))))

private theorem m522 : g 522 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "2,37,274,3,514")) (hv 20358 (by decide))
    (H.mul_mem (m2 H hs) (H.mul_mem (m37 H hv hs) (H.mul_mem (m274 H hv hs) (H.mul_mem (m3 H hs) (H.mul_mem (m514 H hv hs) H.one_mem)))))

private theorem m77 : g 77 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "288,288,-729,3")) (hv 20381 (by decide))
    (H.mul_mem (m288 H hv hs) (H.mul_mem (m288 H hv hs) (H.mul_mem (H.inv_mem (m729 H hv hs)) (H.mul_mem (m3 H hs) H.one_mem))))

private theorem m180 : g 180 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-480,-1041,2,1,37,208")) (hv 21465 (by decide))
    (H.mul_mem (H.inv_mem (m480 H hs)) (H.mul_mem (H.inv_mem (m1041 H hs)) (H.mul_mem (m2 H hs) (H.mul_mem (m1 H hs) (H.mul_mem (m37 H hv hs) (H.mul_mem (m208 H hv hs) H.one_mem))))))

private theorem m214 : g 214 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-235,-84,-1620,235,-3")) (hv 21481 (by decide))
    (H.mul_mem (H.inv_mem (m235 H hs)) (H.mul_mem (H.inv_mem (m84 H hv hs)) (H.mul_mem (H.inv_mem (m1620 H hv hs)) (H.mul_mem (m235 H hs) (H.mul_mem (H.inv_mem (m3 H hs)) H.one_mem)))))

private theorem m1451 : g 1451 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1824,274,348,-1106,-480")) (hv 21536 (by decide))
    (H.mul_mem (H.inv_mem (m1824 H hv hs)) (H.mul_mem (m274 H hv hs) (H.mul_mem (m348 H hs) (H.mul_mem (H.inv_mem (m1106 H hs)) (H.mul_mem (H.inv_mem (m480 H hs)) H.one_mem)))))

private theorem m148 : g 148 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "3,475,348,-1115,-23,1235")) (hv 21581 (by decide))
    (H.mul_mem (m3 H hs) (H.mul_mem (m475 H hv hs) (H.mul_mem (m348 H hs) (H.mul_mem (H.inv_mem (m1115 H hs)) (H.mul_mem (H.inv_mem (m23 H hs)) (H.mul_mem (m1235 H hv hs) H.one_mem))))))

private theorem m56 : g 56 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1041,2,3,-1041,1972,422,514,2")) (hv 21624 (by decide))
    (H.mul_mem (H.inv_mem (m1041 H hs)) (H.mul_mem (m2 H hs) (H.mul_mem (m3 H hs) (H.mul_mem (H.inv_mem (m1041 H hs)) (H.mul_mem (m1972 H hs) (H.mul_mem (m422 H hs) (H.mul_mem (m514 H hv hs) (H.mul_mem (m2 H hs) H.one_mem))))))))

private theorem m524 : g 524 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-274,-119,2,1041,480,-274,1772,2")) (hv 21730 (by decide))
    (H.mul_mem (H.inv_mem (m274 H hv hs)) (H.mul_mem (H.inv_mem (m119 H hv hs)) (H.mul_mem (m2 H hs) (H.mul_mem (m1041 H hs) (H.mul_mem (m480 H hs) (H.mul_mem (H.inv_mem (m274 H hv hs)) (H.mul_mem (m1772 H hs) (H.mul_mem (m2 H hs) H.one_mem))))))))

private theorem m1450 : g 1450 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-422,3,729,-288,-729,-119,533,-1106,-1106,1")) (hv 21774 (by decide))
    (H.mul_mem (H.inv_mem (m422 H hs)) (H.mul_mem (m3 H hs) (H.mul_mem (m729 H hv hs) (H.mul_mem (H.inv_mem (m288 H hv hs)) (H.mul_mem (H.inv_mem (m729 H hv hs)) (H.mul_mem (H.inv_mem (m119 H hv hs)) (H.mul_mem (m533 H hv hs) (H.mul_mem (H.inv_mem (m1106 H hs)) (H.mul_mem (H.inv_mem (m1106 H hs)) (H.mul_mem (m1 H hs) H.one_mem))))))))))

private theorem m736 : g 736 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "735,906,2,480,19,3,729")) (hv 21800 (by decide))
    (H.mul_mem (m735 H hv hs) (H.mul_mem (m906 H hs) (H.mul_mem (m2 H hs) (H.mul_mem (m480 H hs) (H.mul_mem (m19 H hv hs) (H.mul_mem (m3 H hs) (H.mul_mem (m729 H hv hs) H.one_mem)))))))

private theorem m692 : g 692 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-906,2,514,-348,-480,2,1041,1620,208")) (hv 23322 (by decide))
    (H.mul_mem (H.inv_mem (m906 H hs)) (H.mul_mem (m2 H hs) (H.mul_mem (m514 H hv hs) (H.mul_mem (H.inv_mem (m348 H hs)) (H.mul_mem (H.inv_mem (m480 H hs)) (H.mul_mem (m2 H hs) (H.mul_mem (m1041 H hs) (H.mul_mem (m1620 H hv hs) (H.mul_mem (m208 H hv hs) H.one_mem)))))))))

private theorem m227 : g 227 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-274,729,3,-1972,2,19")) (hv 23800 (by decide))
    (H.mul_mem (H.inv_mem (m274 H hv hs)) (H.mul_mem (m729 H hv hs) (H.mul_mem (m3 H hs) (H.mul_mem (H.inv_mem (m1972 H hs)) (H.mul_mem (m2 H hs) (H.mul_mem (m19 H hv hs) H.one_mem))))))

private theorem m890 : g 890 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1053,1053,688,-274,729,-23,1824,1,1168")) (hv 25327 (by decide))
    (H.mul_mem (m1053 H hv hs) (H.mul_mem (m1053 H hv hs) (H.mul_mem (m688 H hs) (H.mul_mem (H.inv_mem (m274 H hv hs)) (H.mul_mem (m729 H hv hs) (H.mul_mem (H.inv_mem (m23 H hs)) (H.mul_mem (m1824 H hv hs) (H.mul_mem (m1 H hs) (H.mul_mem (m1168 H hv hs) H.one_mem)))))))))

private theorem m780 : g 780 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "2,23,-729,3,1041,-1772,3,475")) (hv 25674 (by decide))
    (H.mul_mem (m2 H hs) (H.mul_mem (m23 H hs) (H.mul_mem (H.inv_mem (m729 H hv hs)) (H.mul_mem (m3 H hs) (H.mul_mem (m1041 H hs) (H.mul_mem (H.inv_mem (m1772 H hs)) (H.mul_mem (m3 H hs) (H.mul_mem (m475 H hv hs) H.one_mem))))))))

private theorem m284 : g 284 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-480,-235,84,-1620,-1620,235,688")) (hv 26145 (by decide))
    (H.mul_mem (H.inv_mem (m480 H hs)) (H.mul_mem (H.inv_mem (m235 H hs)) (H.mul_mem (m84 H hv hs) (H.mul_mem (H.inv_mem (m1620 H hv hs)) (H.mul_mem (H.inv_mem (m1620 H hv hs)) (H.mul_mem (m235 H hs) (H.mul_mem (m688 H hs) H.one_mem)))))))

private theorem m645 : g 645 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1168,480,-274,-1,1106,-348")) (hv 27409 (by decide))
    (H.mul_mem (H.inv_mem (m1168 H hv hs)) (H.mul_mem (m480 H hs) (H.mul_mem (H.inv_mem (m274 H hv hs)) (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (m1106 H hs) (H.mul_mem (H.inv_mem (m348 H hs)) H.one_mem))))))

private theorem m1288 : g 1288 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-172")) (hv 4703 (by decide))
    (H.mul_mem (H.inv_mem (m172 H hv hs)) H.one_mem)

private theorem m1221 : g 1221 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-77")) (hv 4926 (by decide))
    (H.mul_mem (H.inv_mem (m77 H hv hs)) H.one_mem)

private theorem m1154 : g 1154 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-214")) (hv 4943 (by decide))
    (H.mul_mem (H.inv_mem (m214 H hv hs)) H.one_mem)

private theorem m1959 : g 1959 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-841")) (hv 5724 (by decide))
    (H.mul_mem (H.inv_mem (m841 H hv hs)) H.one_mem)

private theorem m628 : g 628 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-106")) (hv 4837 (by decide))
    (H.mul_mem (H.inv_mem (m106 H hv hs)) H.one_mem)

private theorem m1161 : g 1161 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-764")) (hv 5736 (by decide))
    (H.mul_mem (H.inv_mem (m764 H hv hs)) H.one_mem)

private theorem m1042 : g 1042 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-110")) (hv 5032 (by decide))
    (H.mul_mem (H.inv_mem (m110 H hv hs)) H.one_mem)

private theorem m694 : g 694 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-112")) (hv 5036 (by decide))
    (H.mul_mem (H.inv_mem (m112 H hv hs)) H.one_mem)

private theorem m1175 : g 1175 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-933")) (hv 4978 (by decide))
    (H.mul_mem (H.inv_mem (m933 H hv hs)) H.one_mem)

private theorem m489 : g 489 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-148")) (hv 4642 (by decide))
    (H.mul_mem (H.inv_mem (m148 H hv hs)) H.one_mem)

private theorem m1281 : g 1281 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-180")) (hv 4894 (by decide))
    (H.mul_mem (H.inv_mem (m180 H hv hs)) H.one_mem)

private theorem m888 : g 888 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-282")) (hv 4604 (by decide))
    (H.mul_mem (H.inv_mem (m282 H hv hs)) H.one_mem)

private theorem m1911 : g 1911 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1428")) (hv 4986 (by decide))
    (H.mul_mem (H.inv_mem (m1428 H hv hs)) H.one_mem)

private theorem m2039 : g 2039 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-801")) (hv 31026 (by decide))
    (H.mul_mem (H.inv_mem (m801 H hv hs)) H.one_mem)

private theorem m555 : g 555 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-227")) (hv 5308 (by decide))
    (H.mul_mem (H.inv_mem (m227 H hv hs)) H.one_mem)

private theorem m1682 : g 1682 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1420")) (hv 4830 (by decide))
    (H.mul_mem (H.inv_mem (m1420 H hv hs)) H.one_mem)

private theorem m1406 : g 1406 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-250")) (hv 5024 (by decide))
    (H.mul_mem (H.inv_mem (m250 H hv hs)) H.one_mem)

private theorem m914 : g 914 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-289")) (hv 5015 (by decide))
    (H.mul_mem (H.inv_mem (m289 H hv hs)) H.one_mem)

private theorem m1048 : g 1048 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-302")) (hv 5256 (by decide))
    (H.mul_mem (H.inv_mem (m302 H hv hs)) H.one_mem)

private theorem m517 : g 517 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-323")) (hv 5118 (by decide))
    (H.mul_mem (H.inv_mem (m323 H hv hs)) H.one_mem)

private theorem m691 : g 691 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-522")) (hv 4599 (by decide))
    (H.mul_mem (H.inv_mem (m522 H hv hs)) H.one_mem)

private theorem m705 : g 705 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-585")) (hv 5780 (by decide))
    (H.mul_mem (H.inv_mem (m585 H hv hs)) H.one_mem)

private theorem m2056 : g 2056 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1649")) (hv 5853 (by decide))
    (H.mul_mem (H.inv_mem (m1649 H hv hs)) H.one_mem)

private theorem m1351 : g 1351 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-645")) (hv 4861 (by decide))
    (H.mul_mem (H.inv_mem (m645 H hv hs)) H.one_mem)

private theorem m1009 : g 1009 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-647")) (hv 5373 (by decide))
    (H.mul_mem (H.inv_mem (m647 H hv hs)) H.one_mem)

private theorem m1393 : g 1393 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-692")) (hv 5397 (by decide))
    (H.mul_mem (H.inv_mem (m692 H hv hs)) H.one_mem)

private theorem m998 : g 998 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-780")) (hv 4931 (by decide))
    (H.mul_mem (H.inv_mem (m780 H hv hs)) H.one_mem)

private theorem m1416 : g 1416 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-740")) (hv 5183 (by decide))
    (H.mul_mem (H.inv_mem (m740 H hv hs)) H.one_mem)

private theorem m1462 : g 1462 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-798")) (hv 4641 (by decide))
    (H.mul_mem (H.inv_mem (m798 H hv hs)) H.one_mem)

private theorem m923 : g 923 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-799")) (hv 4744 (by decide))
    (H.mul_mem (H.inv_mem (m799 H hv hs)) H.one_mem)

private theorem m1270 : g 1270 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-863")) (hv 5842 (by decide))
    (H.mul_mem (H.inv_mem (m863 H hv hs)) H.one_mem)

private theorem m1669 : g 1669 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1450")) (hv 31027 (by decide))
    (H.mul_mem (H.inv_mem (m1450 H hv hs)) H.one_mem)

private theorem m2026 : g 2026 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1703")) (hv 31028 (by decide))
    (H.mul_mem (H.inv_mem (m1703 H hv hs)) H.one_mem)

private theorem m1586 : g 1586 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-890")) (hv 5970 (by decide))
    (H.mul_mem (H.inv_mem (m890 H hv hs)) H.one_mem)

private theorem m1680 : g 1680 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-255")) (hv 6096 (by decide))
    (H.mul_mem (H.inv_mem (m255 H hv hs)) H.one_mem)

private theorem m1484 : g 1484 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-56")) (hv 5991 (by decide))
    (H.mul_mem (H.inv_mem (m56 H hv hs)) H.one_mem)

private theorem m551 : g 551 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1484")) (hv 6023 (by decide))
    (H.mul_mem (H.inv_mem (m1484 H hv hs)) H.one_mem)

private theorem m1145 : g 1145 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1277")) (hv 5925 (by decide))
    (H.mul_mem (m1277 H hv hs) H.one_mem)

private theorem m871 : g 871 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "30")) (hv 5983 (by decide))
    (H.mul_mem (m30 H hv hs) H.one_mem)

private theorem m1666 : g 1666 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1649")) (hv 6123 (by decide))
    (H.mul_mem (m1649 H hv hs) H.one_mem)

private theorem m1755 : g 1755 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1408")) (hv 5994 (by decide))
    (H.mul_mem (H.inv_mem (m1408 H hv hs)) H.one_mem)

private theorem m1858 : g 1858 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-56")) (hv 6025 (by decide))
    (H.mul_mem (H.inv_mem (m56 H hv hs)) H.one_mem)

private theorem m331 : g 331 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "258")) (hv 5929 (by decide))
    (H.mul_mem (m258 H hv hs) H.one_mem)

private theorem m1670 : g 1670 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1451")) (hv 31029 (by decide))
    (H.mul_mem (H.inv_mem (m1451 H hv hs)) H.one_mem)

private theorem m362 : g 362 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "112")) (hv 6295 (by decide))
    (H.mul_mem (m112 H hv hs) H.one_mem)

private theorem m1040 : g 1040 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-284")) (hv 6289 (by decide))
    (H.mul_mem (H.inv_mem (m284 H hv hs)) H.one_mem)

private theorem m1065 : g 1065 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1040")) (hv 6346 (by decide))
    (H.mul_mem (H.inv_mem (m1040 H hv hs)) H.one_mem)

private theorem m391 : g 391 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "56")) (hv 7654 (by decide))
    (H.mul_mem (m56 H hv hs) H.one_mem)

private theorem m1329 : g 1329 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "104")) (hv 7577 (by decide))
    (H.mul_mem (m104 H hv hs) H.one_mem)

private theorem m1526 : g 1526 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-736")) (hv 7680 (by decide))
    (H.mul_mem (H.inv_mem (m736 H hv hs)) H.one_mem)

private theorem m233 : g 233 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "227")) (hv 7605 (by decide))
    (H.mul_mem (m227 H hv hs) H.one_mem)

private theorem m384 : g 384 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "77")) (hv 7597 (by decide))
    (H.mul_mem (m77 H hv hs) H.one_mem)

private theorem m640 : g 640 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "524")) (hv 7593 (by decide))
    (H.mul_mem (m524 H hv hs) H.one_mem)

private theorem m1314 : g 1314 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-863")) (hv 7798 (by decide))
    (H.mul_mem (H.inv_mem (m863 H hv hs)) H.one_mem)

private theorem m381 : g 381 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1244,-480")) (hv 10120 (by decide))
    (H.mul_mem (H.inv_mem (m1244 H hv hs)) (H.mul_mem (H.inv_mem (m480 H hs)) H.one_mem))

private theorem m1396 : g 1396 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1223,-323")) (hv 10136 (by decide))
    (H.mul_mem (m1223 H hv hs) (H.mul_mem (H.inv_mem (m323 H hv hs)) H.one_mem))

private theorem m1152 : g 1152 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "617,-22")) (hv 10168 (by decide))
    (H.mul_mem (m617 H hv hs) (H.mul_mem (H.inv_mem (m22 H hv hs)) H.one_mem))

private theorem m1638 : g 1638 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "176,-1188")) (hv 10195 (by decide))
    (H.mul_mem (m176 H hv hs) (H.mul_mem (H.inv_mem (m1188 H hv hs)) H.one_mem))

private theorem m699 : g 699 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-38,863")) (hv 10205 (by decide))
    (H.mul_mem (H.inv_mem (m38 H hv hs)) (H.mul_mem (m863 H hv hs) H.one_mem))

private theorem m1505 : g 1505 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-735,-869,877")) (hv 10230 (by decide))
    (H.mul_mem (H.inv_mem (m735 H hv hs)) (H.mul_mem (H.inv_mem (m869 H hv hs)) (H.mul_mem (m877 H hv hs) H.one_mem)))

private theorem m1313 : g 1313 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-863,799")) (hv 10233 (by decide))
    (H.mul_mem (H.inv_mem (m863 H hv hs)) (H.mul_mem (m799 H hv hs) H.one_mem))

private theorem m572 : g 572 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-176,-1451")) (hv 10240 (by decide))
    (H.mul_mem (H.inv_mem (m176 H hv hs)) (H.mul_mem (H.inv_mem (m1451 H hv hs)) H.one_mem))

private theorem m592 : g 592 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-3,214")) (hv 10270 (by decide))
    (H.mul_mem (H.inv_mem (m3 H hs)) (H.mul_mem (m214 H hv hs) H.one_mem))

private theorem m167 : g 167 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-3,1408")) (hv 10277 (by decide))
    (H.mul_mem (H.inv_mem (m3 H hs)) (H.mul_mem (m1408 H hv hs) H.one_mem))

private theorem m1721 : g 1721 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1106,1420")) (hv 11031 (by decide))
    (H.mul_mem (H.inv_mem (m1106 H hs)) (H.mul_mem (m1420 H hv hs) H.one_mem))

private theorem m843 : g 843 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "803,56")) (hv 11042 (by decide))
    (H.mul_mem (m803 H hv hs) (H.mul_mem (m56 H hv hs) H.one_mem))

private theorem m1866 : g 1866 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-798,-1")) (hv 11078 (by decide))
    (H.mul_mem (H.inv_mem (m798 H hv hs)) (H.mul_mem (H.inv_mem (m1 H hs)) H.one_mem))

private theorem m1807 : g 1807 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-56,-422")) (hv 11082 (by decide))
    (H.mul_mem (H.inv_mem (m56 H hv hs)) (H.mul_mem (H.inv_mem (m422 H hs)) H.one_mem))

private theorem m53 : g 53 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-736,-354")) (hv 11095 (by decide))
    (H.mul_mem (H.inv_mem (m736 H hv hs)) (H.mul_mem (H.inv_mem (m354 H hv hs)) H.one_mem))

private theorem m1923 : g 1923 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "208,1450")) (hv 11145 (by decide))
    (H.mul_mem (m208 H hv hs) (H.mul_mem (m1450 H hv hs) H.one_mem))

private theorem m113 : g 113 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "56,-3,-617,-56")) (hv 11189 (by decide))
    (H.mul_mem (m56 H hv hs) (H.mul_mem (H.inv_mem (m3 H hs)) (H.mul_mem (H.inv_mem (m617 H hv hs)) (H.mul_mem (H.inv_mem (m56 H hv hs)) H.one_mem))))

private theorem m637 : g 637 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-138,514")) (hv 11205 (by decide))
    (H.mul_mem (H.inv_mem (m138 H hv hs)) (H.mul_mem (m514 H hv hs) H.one_mem))

private theorem m444 : g 444 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-227,524")) (hv 11212 (by decide))
    (H.mul_mem (H.inv_mem (m227 H hv hs)) (H.mul_mem (m524 H hv hs) H.one_mem))

private theorem m1839 : g 1839 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1041,-1594,-2")) (hv 31030 (by decide))
    (H.mul_mem (m1041 H hs) (H.mul_mem (H.inv_mem (m1594 H hv hs)) (H.mul_mem (H.inv_mem (m2 H hs)) H.one_mem)))

private theorem m481 : g 481 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1,-522")) (hv 11856 (by decide))
    (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (H.inv_mem (m522 H hv hs)) H.one_mem))

private theorem m1597 : g 1597 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "84,323,2")) (hv 11863 (by decide))
    (H.mul_mem (m84 H hv hs) (H.mul_mem (m323 H hv hs) (H.mul_mem (m2 H hs) H.one_mem)))

private theorem m1342 : g 1342 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "323,-20,-360")) (hv 11895 (by decide))
    (H.mul_mem (m323 H hv hs) (H.mul_mem (H.inv_mem (m20 H hv hs)) (H.mul_mem (H.inv_mem (m360 H hv hs)) H.one_mem)))

private theorem m1530 : g 1530 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1450,701")) (hv 11977 (by decide))
    (H.mul_mem (m1450 H hv hs) (H.mul_mem (m701 H hv hs) H.one_mem))

private theorem m1496 : g 1496 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-282,-3,282")) (hv 11986 (by decide))
    (H.mul_mem (H.inv_mem (m282 H hv hs)) (H.mul_mem (H.inv_mem (m3 H hs)) (H.mul_mem (m282 H hv hs) H.one_mem)))

private theorem m1688 : g 1688 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-780,3")) (hv 12006 (by decide))
    (H.mul_mem (H.inv_mem (m780 H hv hs)) (H.mul_mem (m3 H hs) H.one_mem))

private theorem m1395 : g 1395 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "214,-3")) (hv 12020 (by decide))
    (H.mul_mem (m214 H hv hs) (H.mul_mem (H.inv_mem (m3 H hs)) H.one_mem))

private theorem m724 : g 724 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-322,-258")) (hv 12681 (by decide))
    (H.mul_mem (H.inv_mem (m322 H hv hs)) (H.mul_mem (H.inv_mem (m258 H hv hs)) H.one_mem))

private theorem m434 : g 434 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1,172,-282")) (hv 12700 (by decide))
    (H.mul_mem (m1 H hs) (H.mul_mem (m172 H hv hs) (H.mul_mem (H.inv_mem (m282 H hv hs)) H.one_mem)))

private theorem m657 : g 657 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "422,-803,-1649")) (hv 12707 (by decide))
    (H.mul_mem (m422 H hs) (H.mul_mem (H.inv_mem (m803 H hv hs)) (H.mul_mem (H.inv_mem (m1649 H hv hs)) H.one_mem)))

private theorem m187 : g 187 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-3,-104")) (hv 12725 (by decide))
    (H.mul_mem (H.inv_mem (m3 H hs)) (H.mul_mem (H.inv_mem (m104 H hv hs)) H.one_mem))

private theorem m685 : g 685 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "422,-1112")) (hv 12738 (by decide))
    (H.mul_mem (m422 H hs) (H.mul_mem (H.inv_mem (m1112 H hv hs)) H.one_mem))

private theorem m1356 : g 1356 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "692,1")) (hv 12809 (by decide))
    (H.mul_mem (m692 H hv hs) (H.mul_mem (m1 H hs) H.one_mem))

private theorem m769 : g 769 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-348,-354,1741,-56")) (hv 12843 (by decide))
    (H.mul_mem (H.inv_mem (m348 H hs)) (H.mul_mem (H.inv_mem (m354 H hv hs)) (H.mul_mem (m1741 H hv hs) (H.mul_mem (H.inv_mem (m56 H hv hs)) H.one_mem))))

private theorem m859 : g 859 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1,148,-1235")) (hv 12913 (by decide))
    (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (m148 H hv hs) (H.mul_mem (H.inv_mem (m1235 H hv hs)) H.one_mem)))

private theorem m677 : g 677 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1087,1115,1112")) (hv 13657 (by decide))
    (H.mul_mem (m1087 H hv hs) (H.mul_mem (m1115 H hs) (H.mul_mem (m1112 H hv hs) H.one_mem)))

private theorem m1319 : g 1319 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1106,231,-841")) (hv 13693 (by decide))
    (H.mul_mem (m1106 H hs) (H.mul_mem (m231 H hv hs) (H.mul_mem (H.inv_mem (m841 H hv hs)) H.one_mem)))

private theorem m1520 : g 1520 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-255,522,906")) (hv 13736 (by decide))
    (H.mul_mem (H.inv_mem (m255 H hv hs)) (H.mul_mem (m522 H hv hs) (H.mul_mem (m906 H hs) H.one_mem)))

private theorem m494 : g 494 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1450,-1018,524")) (hv 13759 (by decide))
    (H.mul_mem (H.inv_mem (m1450 H hv hs)) (H.mul_mem (H.inv_mem (m1018 H hv hs)) (H.mul_mem (m524 H hv hs) H.one_mem)))

private theorem m644 : g 644 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-2,273,-1408")) (hv 13774 (by decide))
    (H.mul_mem (H.inv_mem (m2 H hs)) (H.mul_mem (m273 H hs) (H.mul_mem (H.inv_mem (m1408 H hv hs)) H.one_mem)))

private theorem m1213 : g 1213 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-12,172")) (hv 13811 (by decide))
    (H.mul_mem (H.inv_mem (m12 H hv hs)) (H.mul_mem (m172 H hv hs) H.one_mem))

private theorem m1095 : g 1095 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-890,-475")) (hv 13878 (by decide))
    (H.mul_mem (H.inv_mem (m890 H hv hs)) (H.mul_mem (H.inv_mem (m475 H hv hs)) H.one_mem))

private theorem m343 : g 343 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-863,-1106,-228")) (hv 13884 (by decide))
    (H.mul_mem (H.inv_mem (m863 H hv hs)) (H.mul_mem (H.inv_mem (m1106 H hs)) (H.mul_mem (H.inv_mem (m228 H hv hs)) H.one_mem)))

private theorem m246 : g 246 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1420,-1778,1451")) (hv 13890 (by decide))
    (H.mul_mem (m1420 H hv hs) (H.mul_mem (H.inv_mem (m1778 H hv hs)) (H.mul_mem (m1451 H hv hs) H.one_mem)))

private theorem m490 : g 490 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-214,-1203,-1")) (hv 13896 (by decide))
    (H.mul_mem (H.inv_mem (m214 H hv hs)) (H.mul_mem (H.inv_mem (m1203 H hv hs)) (H.mul_mem (H.inv_mem (m1 H hs)) H.one_mem)))

private theorem m1869 : g 1869 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1972,-422,3,282")) (hv 13906 (by decide))
    (H.mul_mem (H.inv_mem (m1972 H hs)) (H.mul_mem (H.inv_mem (m422 H hs)) (H.mul_mem (m3 H hs) (H.mul_mem (m282 H hv hs) H.one_mem))))

private theorem m232 : g 232 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "227,-1")) (hv 14719 (by decide))
    (H.mul_mem (m227 H hv hs) (H.mul_mem (H.inv_mem (m1 H hs)) H.one_mem))

private theorem m93 : g 93 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "282,2,-12")) (hv 14751 (by decide))
    (H.mul_mem (m282 H hv hs) (H.mul_mem (m2 H hs) (H.mul_mem (H.inv_mem (m12 H hv hs)) H.one_mem)))

private theorem m379 : g 379 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "764,1018")) (hv 14795 (by decide))
    (H.mul_mem (m764 H hv hs) (H.mul_mem (m1018 H hv hs) H.one_mem))

private theorem m97 : g 97 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-890,1053")) (hv 14801 (by decide))
    (H.mul_mem (H.inv_mem (m890 H hv hs)) (H.mul_mem (m1053 H hv hs) H.one_mem))

private theorem m101 : g 101 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "214,1203,-273")) (hv 14816 (by decide))
    (H.mul_mem (m214 H hv hs) (H.mul_mem (m1203 H hv hs) (H.mul_mem (H.inv_mem (m273 H hs)) H.one_mem)))

private theorem m414 : g 414 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "735,284,758")) (hv 14877 (by decide))
    (H.mul_mem (m735 H hv hs) (H.mul_mem (m284 H hv hs) (H.mul_mem (m758 H hv hs) H.one_mem)))

private theorem m436 : g 436 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-20,348,1420,3,-1620")) (hv 14884 (by decide))
    (H.mul_mem (H.inv_mem (m20 H hv hs)) (H.mul_mem (m348 H hs) (H.mul_mem (m1420 H hv hs) (H.mul_mem (m3 H hs) (H.mul_mem (H.inv_mem (m1620 H hv hs)) H.one_mem)))))

private theorem m1139 : g 1139 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1,119,274,524")) (hv 14889 (by decide))
    (H.mul_mem (m1 H hs) (H.mul_mem (m119 H hv hs) (H.mul_mem (m274 H hv hs) (H.mul_mem (m524 H hv hs) H.one_mem))))

private theorem m575 : g 575 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-20,19,-1594")) (hv 14911 (by decide))
    (H.mul_mem (H.inv_mem (m20 H hv hs)) (H.mul_mem (m19 H hv hs) (H.mul_mem (H.inv_mem (m1594 H hv hs)) H.one_mem)))

private theorem m1482 : g 1482 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-616,-3,-616,-741")) (hv 14921 (by decide))
    (H.mul_mem (H.inv_mem (m616 H hv hs)) (H.mul_mem (H.inv_mem (m3 H hs)) (H.mul_mem (H.inv_mem (m616 H hv hs)) (H.mul_mem (H.inv_mem (m741 H hv hs)) H.one_mem))))

private theorem m149 : g 149 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "148,-1235,-1")) (hv 14930 (by decide))
    (H.mul_mem (m148 H hv hs) (H.mul_mem (H.inv_mem (m1235 H hv hs)) (H.mul_mem (H.inv_mem (m1 H hs)) H.one_mem)))

private theorem m291 : g 291 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "533,-180")) (hv 14963 (by decide))
    (H.mul_mem (m533 H hv hs) (H.mul_mem (H.inv_mem (m180 H hv hs)) H.one_mem))

private theorem m1394 : g 1394 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-197,-780")) (hv 14983 (by decide))
    (H.mul_mem (H.inv_mem (m197 H hv hs)) (H.mul_mem (H.inv_mem (m780 H hv hs)) H.one_mem))

private theorem m118 : g 118 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "208,-172,1620")) (hv 14991 (by decide))
    (H.mul_mem (m208 H hv hs) (H.mul_mem (H.inv_mem (m172 H hv hs)) (H.mul_mem (m1620 H hv hs) H.one_mem)))

private theorem m1753 : g 1753 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1115,-2,-1112")) (hv 15980 (by decide))
    (H.mul_mem (m1115 H hs) (H.mul_mem (H.inv_mem (m2 H hs)) (H.mul_mem (H.inv_mem (m1112 H hv hs)) H.one_mem)))

private theorem m752 : g 752 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-322,-258,799,-1")) (hv 15982 (by decide))
    (H.mul_mem (H.inv_mem (m322 H hv hs)) (H.mul_mem (H.inv_mem (m258 H hv hs)) (H.mul_mem (m799 H hv hs) (H.mul_mem (H.inv_mem (m1 H hs)) H.one_mem))))

private theorem m850 : g 850 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-645,348,1235,-148,-148")) (hv 16001 (by decide))
    (H.mul_mem (H.inv_mem (m645 H hv hs)) (H.mul_mem (m348 H hs) (H.mul_mem (m1235 H hv hs) (H.mul_mem (H.inv_mem (m148 H hv hs)) (H.mul_mem (H.inv_mem (m148 H hv hs)) H.one_mem)))))

private theorem m1499 : g 1499 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-701,-1958,-1,-284,20")) (hv 16018 (by decide))
    (H.mul_mem (H.inv_mem (m701 H hv hs)) (H.mul_mem (H.inv_mem (m1958 H hs)) (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (H.inv_mem (m284 H hv hs)) (H.mul_mem (m20 H hv hs) H.one_mem)))))

private theorem m590 : g 590 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "890,645")) (hv 16046 (by decide))
    (H.mul_mem (m890 H hv hs) (H.mul_mem (m645 H hv hs) H.one_mem))

private theorem m937 : g 937 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1,-1824,1168,645")) (hv 16085 (by decide))
    (H.mul_mem (m1 H hs) (H.mul_mem (H.inv_mem (m1824 H hv hs)) (H.mul_mem (m1168 H hv hs) (H.mul_mem (m645 H hv hs) H.one_mem))))

private theorem m293 : g 293 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-20,84,-273,227")) (hv 16115 (by decide))
    (H.mul_mem (H.inv_mem (m20 H hv hs)) (H.mul_mem (m84 H hv hs) (H.mul_mem (H.inv_mem (m273 H hs)) (H.mul_mem (m227 H hv hs) H.one_mem))))

private theorem m836 : g 836 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "216,1041,56")) (hv 16133 (by decide))
    (H.mul_mem (m216 H hv hs) (H.mul_mem (m1041 H hs) (H.mul_mem (m56 H hv hs) H.one_mem)))

private theorem m1206 : g 1206 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "906,3,-322,258")) (hv 16136 (by decide))
    (H.mul_mem (m906 H hs) (H.mul_mem (m3 H hs) (H.mul_mem (H.inv_mem (m322 H hv hs)) (H.mul_mem (m258 H hv hs) H.one_mem))))

private theorem m177 : g 177 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-235,-3,-56,-1041,138")) (hv 16157 (by decide))
    (H.mul_mem (H.inv_mem (m235 H hs)) (H.mul_mem (H.inv_mem (m3 H hs)) (H.mul_mem (H.inv_mem (m56 H hv hs)) (H.mul_mem (H.inv_mem (m1041 H hs)) (H.mul_mem (m138 H hv hs) H.one_mem)))))

private theorem m415 : g 415 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1451,-235,37,235")) (hv 16183 (by decide))
    (H.mul_mem (m1451 H hv hs) (H.mul_mem (H.inv_mem (m235 H hs)) (H.mul_mem (m37 H hv hs) (H.mul_mem (m235 H hs) H.one_mem))))

private theorem m325 : g 325 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-180,360,-214,-273,-273")) (hv 16195 (by decide))
    (H.mul_mem (H.inv_mem (m180 H hv hs)) (H.mul_mem (m360 H hv hs) (H.mul_mem (H.inv_mem (m214 H hv hs)) (H.mul_mem (H.inv_mem (m273 H hs)) (H.mul_mem (H.inv_mem (m273 H hs)) H.one_mem)))))

private theorem m526 : g 526 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "514,-522,-1115")) (hv 16254 (by decide))
    (H.mul_mem (m514 H hv hs) (H.mul_mem (H.inv_mem (m522 H hv hs)) (H.mul_mem (H.inv_mem (m1115 H hs)) H.one_mem)))

private theorem m743 : g 743 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "692,-1772,3,-1686")) (hv 31031 (by decide))
    (H.mul_mem (m692 H hv hs) (H.mul_mem (H.inv_mem (m1772 H hs)) (H.mul_mem (m3 H hs) (H.mul_mem (H.inv_mem (m1686 H hv hs)) H.one_mem))))

private theorem m1367 : g 1367 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1106,284,-688")) (hv 16282 (by decide))
    (H.mul_mem (H.inv_mem (m1106 H hs)) (H.mul_mem (m284 H hv hs) (H.mul_mem (H.inv_mem (m688 H hs)) H.one_mem)))

private theorem m928 : g 928 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "273,-3,799,1168")) (hv 16291 (by decide))
    (H.mul_mem (m273 H hs) (H.mul_mem (H.inv_mem (m3 H hs)) (H.mul_mem (m799 H hv hs) (H.mul_mem (m1168 H hv hs) H.one_mem))))

private theorem m625 : g 625 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-758,-250,-3,-906")) (hv 16302 (by decide))
    (H.mul_mem (H.inv_mem (m758 H hv hs)) (H.mul_mem (H.inv_mem (m250 H hv hs)) (H.mul_mem (H.inv_mem (m3 H hs)) (H.mul_mem (H.inv_mem (m906 H hs)) H.one_mem))))

private theorem m135 : g 135 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-197,-780,3,729")) (hv 16311 (by decide))
    (H.mul_mem (H.inv_mem (m197 H hv hs)) (H.mul_mem (H.inv_mem (m780 H hv hs)) (H.mul_mem (m3 H hs) (H.mul_mem (m729 H hv hs) H.one_mem))))

private theorem m674 : g 674 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "688,-360,-2,20,56")) (hv 16351 (by decide))
    (H.mul_mem (m688 H hs) (H.mul_mem (H.inv_mem (m360 H hv hs)) (H.mul_mem (H.inv_mem (m2 H hs)) (H.mul_mem (m20 H hv hs) (H.mul_mem (m56 H hv hs) H.one_mem)))))

private theorem m560 : g 560 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-758,-1,119,-906,-522")) (hv 16381 (by decide))
    (H.mul_mem (H.inv_mem (m758 H hv hs)) (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (m119 H hv hs) (H.mul_mem (H.inv_mem (m906 H hs)) (H.mul_mem (H.inv_mem (m522 H hv hs)) H.one_mem)))))

private theorem m1264 : g 1264 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "148,1424,780,197,-692")) (hv 17574 (by decide))
    (H.mul_mem (m148 H hv hs) (H.mul_mem (m1424 H hv hs) (H.mul_mem (m780 H hv hs) (H.mul_mem (m197 H hv hs) (H.mul_mem (H.inv_mem (m692 H hv hs)) H.one_mem)))))

private theorem m1930 : g 1930 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "906,-37,56")) (hv 17609 (by decide))
    (H.mul_mem (m906 H hs) (H.mul_mem (H.inv_mem (m37 H hv hs)) (H.mul_mem (m56 H hv hs) H.one_mem)))

private theorem m822 : g 822 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-422,235,228,-180,360,1203")) (hv 17696 (by decide))
    (H.mul_mem (H.inv_mem (m422 H hs)) (H.mul_mem (m235 H hs) (H.mul_mem (m228 H hv hs) (H.mul_mem (H.inv_mem (m180 H hv hs)) (H.mul_mem (m360 H hv hs) (H.mul_mem (m1203 H hv hs) H.one_mem))))))

private theorem m376 : g 376 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-736,-1208,-348,-1053,1772,701,-30")) (hv 17711 (by decide))
    (H.mul_mem (H.inv_mem (m736 H hv hs)) (H.mul_mem (H.inv_mem (m1208 H hv hs)) (H.mul_mem (H.inv_mem (m348 H hs)) (H.mul_mem (H.inv_mem (m1053 H hv hs)) (H.mul_mem (m1772 H hs) (H.mul_mem (m701 H hv hs) (H.mul_mem (H.inv_mem (m30 H hv hs)) H.one_mem)))))))

private theorem m237 : g 237 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-692,1703,-208,1958")) (hv 17723 (by decide))
    (H.mul_mem (H.inv_mem (m692 H hv hs)) (H.mul_mem (m1703 H hv hs) (H.mul_mem (H.inv_mem (m208 H hv hs)) (H.mul_mem (m1958 H hs) H.one_mem))))

private theorem m359 : g 359 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1018,-1451,533")) (hv 17733 (by decide))
    (H.mul_mem (H.inv_mem (m1018 H hv hs)) (H.mul_mem (H.inv_mem (m1451 H hv hs)) (H.mul_mem (m533 H hv hs) H.one_mem)))

private theorem m268 : g 268 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-227,-23,1106,-758")) (hv 17755 (by decide))
    (H.mul_mem (H.inv_mem (m227 H hv hs)) (H.mul_mem (H.inv_mem (m23 H hs)) (H.mul_mem (m1106 H hs) (H.mul_mem (H.inv_mem (m758 H hv hs)) H.one_mem))))

private theorem m893 : g 893 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-688,-214,12,-692,-19,-284")) (hv 17874 (by decide))
    (H.mul_mem (H.inv_mem (m688 H hs)) (H.mul_mem (H.inv_mem (m214 H hv hs)) (H.mul_mem (m12 H hv hs) (H.mul_mem (H.inv_mem (m692 H hv hs)) (H.mul_mem (H.inv_mem (m19 H hv hs)) (H.mul_mem (H.inv_mem (m284 H hv hs)) H.one_mem))))))

private theorem m28 : g 28 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "692,-214,-235,84,3,-1041")) (hv 18951 (by decide))
    (H.mul_mem (m692 H hv hs) (H.mul_mem (H.inv_mem (m214 H hv hs)) (H.mul_mem (H.inv_mem (m235 H hs)) (H.mul_mem (m84 H hv hs) (H.mul_mem (m3 H hs) (H.mul_mem (H.inv_mem (m1041 H hs)) H.one_mem))))))

private theorem m345 : g 345 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1208,273,-3,799,-1,77")) (hv 18963 (by decide))
    (H.mul_mem (m1208 H hv hs) (H.mul_mem (m273 H hs) (H.mul_mem (H.inv_mem (m3 H hs)) (H.mul_mem (m799 H hv hs) (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (m77 H hv hs) H.one_mem))))))

private theorem m785 : g 785 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1,19,-2,692,-1450,-1018,524")) (hv 18969 (by decide))
    (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (m19 H hv hs) (H.mul_mem (H.inv_mem (m2 H hs)) (H.mul_mem (m692 H hv hs) (H.mul_mem (H.inv_mem (m1450 H hv hs)) (H.mul_mem (H.inv_mem (m1018 H hv hs)) (H.mul_mem (m524 H hv hs) H.one_mem)))))))

private theorem m1156 : g 1156 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-729,274,227")) (hv 18996 (by decide))
    (H.mul_mem (H.inv_mem (m729 H hv hs)) (H.mul_mem (m274 H hv hs) (H.mul_mem (m227 H hv hs) H.one_mem)))

private theorem m712 : g 712 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1,208,-422,84,524")) (hv 19095 (by decide))
    (H.mul_mem (m1 H hs) (H.mul_mem (m208 H hv hs) (H.mul_mem (H.inv_mem (m422 H hs)) (H.mul_mem (m84 H hv hs) (H.mul_mem (m524 H hv hs) H.one_mem)))))

private theorem m313 : g 313 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "524,2,-1772,-780,37,3")) (hv 19205 (by decide))
    (H.mul_mem (m524 H hv hs) (H.mul_mem (m2 H hs) (H.mul_mem (H.inv_mem (m1772 H hs)) (H.mul_mem (H.inv_mem (m780 H hv hs)) (H.mul_mem (m37 H hv hs) (H.mul_mem (m3 H hs) H.one_mem))))))

private theorem m510 : g 510 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-524,-274,-119,1620,208")) (hv 20289 (by decide))
    (H.mul_mem (H.inv_mem (m524 H hv hs)) (H.mul_mem (H.inv_mem (m274 H hv hs)) (H.mul_mem (H.inv_mem (m119 H hv hs)) (H.mul_mem (m1620 H hv hs) (H.mul_mem (m208 H hv hs) H.one_mem)))))

private theorem m2037 : g 2037 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "3,-1972,-1772,148,-1235")) (hv 20327 (by decide))
    (H.mul_mem (m3 H hs) (H.mul_mem (H.inv_mem (m1972 H hs)) (H.mul_mem (H.inv_mem (m1772 H hs)) (H.mul_mem (m148 H hv hs) (H.mul_mem (H.inv_mem (m1235 H hv hs)) H.one_mem)))))

private theorem m398 : g 398 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "906,-37,56,-906,-514,-2,-348,180,-227,-688,736,735")) (hv 31032 (by decide))
    (H.mul_mem (m906 H hs) (H.mul_mem (H.inv_mem (m37 H hv hs)) (H.mul_mem (m56 H hv hs) (H.mul_mem (H.inv_mem (m906 H hs)) (H.mul_mem (H.inv_mem (m514 H hv hs)) (H.mul_mem (H.inv_mem (m2 H hs)) (H.mul_mem (H.inv_mem (m348 H hs)) (H.mul_mem (m180 H hv hs) (H.mul_mem (H.inv_mem (m227 H hv hs)) (H.mul_mem (H.inv_mem (m688 H hs)) (H.mul_mem (m736 H hv hs) (H.mul_mem (m735 H hv hs) H.one_mem))))))))))))

private theorem m107 : g 107 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1451,84,208,-1041,1,1106")) (hv 20491 (by decide))
    (H.mul_mem (m1451 H hv hs) (H.mul_mem (m84 H hv hs) (H.mul_mem (m208 H hv hs) (H.mul_mem (H.inv_mem (m1041 H hs)) (H.mul_mem (m1 H hs) (H.mul_mem (m1106 H hs) H.one_mem))))))

private theorem m1432 : g 1432 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "906,-3,-84,235,-1235,189,-148")) (hv 21454 (by decide))
    (H.mul_mem (m906 H hs) (H.mul_mem (H.inv_mem (m3 H hs)) (H.mul_mem (H.inv_mem (m84 H hv hs)) (H.mul_mem (m235 H hs) (H.mul_mem (H.inv_mem (m1235 H hv hs)) (H.mul_mem (m189 H hv hs) (H.mul_mem (H.inv_mem (m148 H hv hs)) H.one_mem)))))))

private theorem m588 : g 588 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-3,-906,284,-645,-890,1053,688,1772")) (hv 21523 (by decide))
    (H.mul_mem (H.inv_mem (m3 H hs)) (H.mul_mem (H.inv_mem (m906 H hs)) (H.mul_mem (m284 H hv hs) (H.mul_mem (H.inv_mem (m645 H hv hs)) (H.mul_mem (H.inv_mem (m890 H hv hs)) (H.mul_mem (m1053 H hv hs) (H.mul_mem (m688 H hs) (H.mul_mem (m1772 H hs) H.one_mem))))))))

private theorem m755 : g 755 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "906,2,-197,1772,2,480,-890")) (hv 21544 (by decide))
    (H.mul_mem (m906 H hs) (H.mul_mem (m2 H hs) (H.mul_mem (H.inv_mem (m197 H hv hs)) (H.mul_mem (m1772 H hs) (H.mul_mem (m2 H hs) (H.mul_mem (m480 H hs) (H.mul_mem (H.inv_mem (m890 H hv hs)) H.one_mem)))))))

private theorem m675 : g 675 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1,1958,701,688,19,-3,692,-1")) (hv 21561 (by decide))
    (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (m1958 H hs) (H.mul_mem (m701 H hv hs) (H.mul_mem (m688 H hs) (H.mul_mem (m19 H hv hs) (H.mul_mem (H.inv_mem (m3 H hs)) (H.mul_mem (m692 H hv hs) (H.mul_mem (H.inv_mem (m1 H hs)) H.one_mem))))))))

private theorem m1405 : g 1405 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-890,1053,688,-1235,-348,-729,-906")) (hv 21592 (by decide))
    (H.mul_mem (H.inv_mem (m890 H hv hs)) (H.mul_mem (m1053 H hv hs) (H.mul_mem (m688 H hs) (H.mul_mem (H.inv_mem (m1235 H hv hs)) (H.mul_mem (H.inv_mem (m348 H hs)) (H.mul_mem (H.inv_mem (m729 H hv hs)) (H.mul_mem (H.inv_mem (m906 H hs)) H.one_mem)))))))

private theorem m161 : g 161 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-758,-284,-735,1115,-348,1772,-197,-780,119")) (hv 21609 (by decide))
    (H.mul_mem (H.inv_mem (m758 H hv hs)) (H.mul_mem (H.inv_mem (m284 H hv hs)) (H.mul_mem (H.inv_mem (m735 H hv hs)) (H.mul_mem (m1115 H hs) (H.mul_mem (H.inv_mem (m348 H hs)) (H.mul_mem (m1772 H hs) (H.mul_mem (H.inv_mem (m197 H hv hs)) (H.mul_mem (H.inv_mem (m780 H hv hs)) (H.mul_mem (m119 H hv hs) H.one_mem)))))))))

private theorem m109 : g 109 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "758,-227,-235,37,235,273,84,1,2,1,2,-533")) (hv 22791 (by decide))
    (H.mul_mem (m758 H hv hs) (H.mul_mem (H.inv_mem (m227 H hv hs)) (H.mul_mem (H.inv_mem (m235 H hs)) (H.mul_mem (m37 H hv hs) (H.mul_mem (m235 H hs) (H.mul_mem (m273 H hs) (H.mul_mem (m84 H hv hs) (H.mul_mem (m1 H hs) (H.mul_mem (m2 H hs) (H.mul_mem (m1 H hs) (H.mul_mem (m2 H hs) (H.mul_mem (H.inv_mem (m533 H hv hs)) H.one_mem))))))))))))

private theorem m1083 : g 1083 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-189,906,-3,780,-480,274,348,23,-729,-1,-688,348,-758")) (hv 22796 (by decide))
    (H.mul_mem (H.inv_mem (m189 H hv hs)) (H.mul_mem (m906 H hs) (H.mul_mem (H.inv_mem (m3 H hs)) (H.mul_mem (m780 H hv hs) (H.mul_mem (H.inv_mem (m480 H hs)) (H.mul_mem (m274 H hv hs) (H.mul_mem (m348 H hs) (H.mul_mem (m23 H hs) (H.mul_mem (H.inv_mem (m729 H hv hs)) (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (H.inv_mem (m688 H hs)) (H.mul_mem (m348 H hs) (H.mul_mem (H.inv_mem (m758 H hv hs)) H.one_mem)))))))))))))

private theorem m778 : g 778 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-28")) (hv 5139 (by decide))
    (H.mul_mem (H.inv_mem (m28 H hv hs)) H.one_mem)

private theorem m440 : g 440 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-161")) (hv 4817 (by decide))
    (H.mul_mem (H.inv_mem (m161 H hv hs)) H.one_mem)

private theorem m1418 : g 1418 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-93")) (hv 4693 (by decide))
    (H.mul_mem (H.inv_mem (m93 H hv hs)) H.one_mem)

private theorem m1122 : g 1122 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-97")) (hv 5447 (by decide))
    (H.mul_mem (H.inv_mem (m97 H hv hs)) H.one_mem)

private theorem m1343 : g 1343 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-822")) (hv 5197 (by decide))
    (H.mul_mem (H.inv_mem (m822 H hv hs)) H.one_mem)

private theorem m1328 : g 1328 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-109")) (hv 5023 (by decide))
    (H.mul_mem (H.inv_mem (m109 H hv hs)) H.one_mem)

private theorem m559 : g 559 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-118")) (hv 5204 (by decide))
    (H.mul_mem (H.inv_mem (m118 H hv hs)) H.one_mem)

private theorem m1626 : g 1626 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1586")) (hv 5091 (by decide))
    (H.mul_mem (H.inv_mem (m1586 H hv hs)) H.one_mem)

private theorem m1202 : g 1202 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-785")) (hv 4990 (by decide))
    (H.mul_mem (H.inv_mem (m785 H hv hs)) H.one_mem)

private theorem m478 : g 478 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-135")) (hv 4835 (by decide))
    (H.mul_mem (H.inv_mem (m135 H hv hs)) H.one_mem)

private theorem m1340 : g 1340 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-510")) (hv 5348 (by decide))
    (H.mul_mem (H.inv_mem (m510 H hv hs)) H.one_mem)

private theorem m856 : g 856 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-232")) (hv 5313 (by decide))
    (H.mul_mem (H.inv_mem (m232 H hv hs)) H.one_mem)

private theorem m1976 : g 1976 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-233")) (hv 5026 (by decide))
    (H.mul_mem (H.inv_mem (m233 H hv hs)) H.one_mem)

private theorem m829 : g 829 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-436")) (hv 5158 (by decide))
    (H.mul_mem (H.inv_mem (m436 H hv hs)) H.one_mem)

private theorem m1131 : g 1131 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-268")) (hv 4903 (by decide))
    (H.mul_mem (H.inv_mem (m268 H hv hs)) H.one_mem)

private theorem m1261 : g 1261 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-675")) (hv 4915 (by decide))
    (H.mul_mem (H.inv_mem (m675 H hv hs)) H.one_mem)

private theorem m810 : g 810 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-313")) (hv 5627 (by decide))
    (H.mul_mem (H.inv_mem (m313 H hv hs)) H.one_mem)

private theorem m1691 : g 1691 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-325")) (hv 5617 (by decide))
    (H.mul_mem (H.inv_mem (m325 H hv hs)) H.one_mem)

private theorem m651 : g 651 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-343")) (hv 5137 (by decide))
    (H.mul_mem (H.inv_mem (m343 H hv hs)) H.one_mem)

private theorem m401 : g 401 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-345")) (hv 31033 (by decide))
    (H.mul_mem (H.inv_mem (m345 H hv hs)) H.one_mem)

private theorem m1947 : g 1947 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-384")) (hv 5481 (by decide))
    (H.mul_mem (H.inv_mem (m384 H hv hs)) H.one_mem)

private theorem m1629 : g 1629 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-391")) (hv 5047 (by decide))
    (H.mul_mem (H.inv_mem (m391 H hv hs)) H.one_mem)

private theorem m1881 : g 1881 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-398")) (hv 5075 (by decide))
    (H.mul_mem (H.inv_mem (m398 H hv hs)) H.one_mem)

private theorem m523 : g 523 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-415")) (hv 5685 (by decide))
    (H.mul_mem (H.inv_mem (m415 H hv hs)) H.one_mem)

private theorem m1023 : g 1023 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-444")) (hv 5514 (by decide))
    (H.mul_mem (H.inv_mem (m444 H hv hs)) H.one_mem)

private theorem m1891 : g 1891 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-481")) (hv 5676 (by decide))
    (H.mul_mem (H.inv_mem (m481 H hv hs)) H.one_mem)

private theorem m1658 : g 1658 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-490")) (hv 4605 (by decide))
    (H.mul_mem (H.inv_mem (m490 H hv hs)) H.one_mem)

private theorem m1201 : g 1201 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-494")) (hv 4999 (by decide))
    (H.mul_mem (H.inv_mem (m494 H hv hs)) H.one_mem)

private theorem m1596 : g 1596 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1432")) (hv 5371 (by decide))
    (H.mul_mem (H.inv_mem (m1432 H hv hs)) H.one_mem)

private theorem m624 : g 624 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-551")) (hv 5186 (by decide))
    (H.mul_mem (H.inv_mem (m551 H hv hs)) H.one_mem)

private theorem m1127 : g 1127 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-560")) (hv 5061 (by decide))
    (H.mul_mem (H.inv_mem (m560 H hv hs)) H.one_mem)

private theorem m667 : g 667 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-588")) (hv 5468 (by decide))
    (H.mul_mem (H.inv_mem (m588 H hv hs)) H.one_mem)

private theorem m768 : g 768 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-590")) (hv 5393 (by decide))
    (H.mul_mem (H.inv_mem (m590 H hv hs)) H.one_mem)

private theorem m1572 : g 1572 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-625")) (hv 4900 (by decide))
    (H.mul_mem (H.inv_mem (m625 H hv hs)) H.one_mem)

private theorem m1028 : g 1028 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-637")) (hv 4650 (by decide))
    (H.mul_mem (H.inv_mem (m637 H hv hs)) H.one_mem)

private theorem m2062 : g 2062 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-640")) (hv 31034 (by decide))
    (H.mul_mem (H.inv_mem (m640 H hv hs)) H.one_mem)

private theorem m708 : g 708 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-657")) (hv 5666 (by decide))
    (H.mul_mem (H.inv_mem (m657 H hv hs)) H.one_mem)

private theorem m1850 : g 1850 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-674")) (hv 4802 (by decide))
    (H.mul_mem (H.inv_mem (m674 H hv hs)) H.one_mem)

private theorem m1113 : g 1113 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-712")) (hv 5479 (by decide))
    (H.mul_mem (H.inv_mem (m712 H hv hs)) H.one_mem)

private theorem m944 : g 944 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-724")) (hv 5598 (by decide))
    (H.mul_mem (H.inv_mem (m724 H hv hs)) H.one_mem)

private theorem m1063 : g 1063 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-755")) (hv 5651 (by decide))
    (H.mul_mem (H.inv_mem (m755 H hv hs)) H.one_mem)

private theorem m2053 : g 2053 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-769")) (hv 4782 (by decide))
    (H.mul_mem (H.inv_mem (m769 H hv hs)) H.one_mem)

private theorem m1262 : g 1262 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-836")) (hv 4991 (by decide))
    (H.mul_mem (H.inv_mem (m836 H hv hs)) H.one_mem)

private theorem m1564 : g 1564 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-850")) (hv 5679 (by decide))
    (H.mul_mem (H.inv_mem (m850 H hv hs)) H.one_mem)

private theorem m1128 : g 1128 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-859")) (hv 5326 (by decide))
    (H.mul_mem (H.inv_mem (m859 H hv hs)) H.one_mem)

private theorem m1214 : g 1214 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1065")) (hv 5502 (by decide))
    (H.mul_mem (H.inv_mem (m1065 H hv hs)) H.one_mem)

private theorem m1104 : g 1104 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-937")) (hv 5673 (by decide))
    (H.mul_mem (H.inv_mem (m937 H hv hs)) H.one_mem)

private theorem m1268 : g 1268 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1095")) (hv 4776 (by decide))
    (H.mul_mem (H.inv_mem (m1095 H hv hs)) H.one_mem)

private theorem m1690 : g 1690 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1139")) (hv 5425 (by decide))
    (H.mul_mem (H.inv_mem (m1139 H hv hs)) H.one_mem)

private theorem m1813 : g 1813 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1145")) (hv 5213 (by decide))
    (H.mul_mem (H.inv_mem (m1145 H hv hs)) H.one_mem)

private theorem m1683 : g 1683 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1313")) (hv 31035 (by decide))
    (H.mul_mem (H.inv_mem (m1313 H hv hs)) H.one_mem)

private theorem m1486 : g 1486 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1319")) (hv 5526 (by decide))
    (H.mul_mem (H.inv_mem (m1319 H hv hs)) H.one_mem)

private theorem m1622 : g 1622 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1342")) (hv 5074 (by decide))
    (H.mul_mem (H.inv_mem (m1342 H hv hs)) H.one_mem)

private theorem m1788 : g 1788 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1396")) (hv 4808 (by decide))
    (H.mul_mem (H.inv_mem (m1396 H hv hs)) H.one_mem)

private theorem m1570 : g 1570 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1484")) (hv 5476 (by decide))
    (H.mul_mem (H.inv_mem (m1484 H hv hs)) H.one_mem)

private theorem m1974 : g 1974 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1499")) (hv 31036 (by decide))
    (H.mul_mem (H.inv_mem (m1499 H hv hs)) H.one_mem)

private theorem m1559 : g 1559 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1530")) (hv 5387 (by decide))
    (H.mul_mem (H.inv_mem (m1530 H hv hs)) H.one_mem)

private theorem m1719 : g 1719 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1597")) (hv 5660 (by decide))
    (H.mul_mem (H.inv_mem (m1597 H hv hs)) H.one_mem)

private theorem m1875 : g 1875 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1866")) (hv 4640 (by decide))
    (H.mul_mem (H.inv_mem (m1866 H hv hs)) H.one_mem)

private theorem m316 : g 316 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-161")) (hv 5867 (by decide))
    (H.mul_mem (H.inv_mem (m161 H hv hs)) H.one_mem)

private theorem m497 : g 497 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-313")) (hv 5961 (by decide))
    (H.mul_mem (H.inv_mem (m313 H hv hs)) H.one_mem)

private theorem m1252 : g 1252 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-625")) (hv 5891 (by decide))
    (H.mul_mem (H.inv_mem (m625 H hv hs)) H.one_mem)

private theorem m1229 : g 1229 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1213")) (hv 31037 (by decide))
    (H.mul_mem (H.inv_mem (m1213 H hv hs)) H.one_mem)

private theorem m1239 : g 1239 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-93")) (hv 6077 (by decide))
    (H.mul_mem (H.inv_mem (m93 H hv hs)) H.one_mem)

private theorem m303 : g 303 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "268")) (hv 6143 (by decide))
    (H.mul_mem (m268 H hv hs) H.one_mem)

private theorem m557 : g 557 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-107")) (hv 6285 (by decide))
    (H.mul_mem (H.inv_mem (m107 H hv hs)) H.one_mem)

private theorem m591 : g 591 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "590")) (hv 6369 (by decide))
    (H.mul_mem (m590 H hv hs) H.one_mem)

private theorem m1549 : g 1549 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "232")) (hv 7762 (by decide))
    (H.mul_mem (m232 H hv hs) H.one_mem)

private theorem m1536 : g 1536 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "755")) (hv 31038 (by decide))
    (H.mul_mem (m755 H hv hs) H.one_mem)

private theorem m1727 : g 1727 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-291")) (hv 7768 (by decide))
    (H.mul_mem (H.inv_mem (m291 H hv hs)) H.one_mem)

private theorem m98 : g 98 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "97,-937")) (hv 10126 (by decide))
    (H.mul_mem (m97 H hv hs) (H.mul_mem (H.inv_mem (m937 H hv hs)) H.one_mem))

private theorem m2038 : g 2038 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-107,291")) (hv 10189 (by decide))
    (H.mul_mem (H.inv_mem (m107 H hv hs)) (H.mul_mem (m291 H hv hs) H.one_mem))

private theorem m1374 : g 1374 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "227,-379")) (hv 10199 (by decide))
    (H.mul_mem (m227 H hv hs) (H.mul_mem (H.inv_mem (m379 H hv hs)) H.one_mem))

private theorem m433 : g 433 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-359,637")) (hv 10211 (by decide))
    (H.mul_mem (H.inv_mem (m359 H hv hs)) (H.mul_mem (m637 H hv hs) H.one_mem))

private theorem m1879 : g 1879 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1156,-644")) (hv 10222 (by decide))
    (H.mul_mem (H.inv_mem (m1156 H hv hs)) (H.mul_mem (H.inv_mem (m644 H hv hs)) H.one_mem))

private theorem m244 : g 244 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-803,625")) (hv 10244 (by decide))
    (H.mul_mem (H.inv_mem (m803 H hv hs)) (H.mul_mem (m625 H hv hs) H.one_mem))

private theorem m1577 : g 1577 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-490,1156")) (hv 10258 (by decide))
    (H.mul_mem (H.inv_mem (m490 H hv hs)) (H.mul_mem (m1156 H hv hs) H.one_mem))

private theorem m665 : g 665 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "893,1319")) (hv 10266 (by decide))
    (H.mul_mem (m893 H hv hs) (H.mul_mem (m1319 H hv hs) H.one_mem))

private theorem m1532 : g 1532 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "12,-101")) (hv 10984 (by decide))
    (H.mul_mem (m12 H hv hs) (H.mul_mem (H.inv_mem (m101 H hv hs)) H.one_mem))

private theorem m727 : g 727 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-325,-2")) (hv 11016 (by decide))
    (H.mul_mem (H.inv_mem (m325 H hv hs)) (H.mul_mem (H.inv_mem (m2 H hs)) H.one_mem))

private theorem m310 : g 310 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1213,325")) (hv 11035 (by decide))
    (H.mul_mem (H.inv_mem (m1213 H hv hs)) (H.mul_mem (m325 H hv hs) H.one_mem))

private theorem m1291 : g 1291 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-2,-325")) (hv 11037 (by decide))
    (H.mul_mem (H.inv_mem (m2 H hs)) (H.mul_mem (H.inv_mem (m325 H hv hs)) H.one_mem))

private theorem m1538 : g 1538 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-237,-2")) (hv 11052 (by decide))
    (H.mul_mem (H.inv_mem (m237 H hv hs)) (H.mul_mem (H.inv_mem (m2 H hs)) H.one_mem))

private theorem m1591 : g 1591 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-313,736")) (hv 11086 (by decide))
    (H.mul_mem (H.inv_mem (m313 H hv hs)) (H.mul_mem (m736 H hv hs) H.one_mem))

private theorem m1402 : g 1402 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "107,-1115,-1451")) (hv 11105 (by decide))
    (H.mul_mem (m107 H hv hs) (H.mul_mem (H.inv_mem (m1115 H hs)) (H.mul_mem (H.inv_mem (m1451 H hv hs)) H.one_mem)))

private theorem m447 : g 447 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "313,-1831")) (hv 11124 (by decide))
    (H.mul_mem (m313 H hv hs) (H.mul_mem (H.inv_mem (m1831 H hv hs)) H.one_mem))

private theorem m1198 : g 1198 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1139,-216")) (hv 11150 (by decide))
    (H.mul_mem (m1139 H hv hs) (H.mul_mem (H.inv_mem (m216 H hv hs)) H.one_mem))

private theorem m1311 : g 1311 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-752,-1620")) (hv 11195 (by decide))
    (H.mul_mem (H.inv_mem (m752 H hv hs)) (H.mul_mem (H.inv_mem (m1620 H hv hs)) H.one_mem))

private theorem m818 : g 818 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1405,97")) (hv 11202 (by decide))
    (H.mul_mem (H.inv_mem (m1405 H hv hs)) (H.mul_mem (m97 H hv hs) H.one_mem))

private theorem m66 : g 66 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "302,933,755")) (hv 11833 (by decide))
    (H.mul_mem (m302 H hv hs) (H.mul_mem (m933 H hv hs) (H.mul_mem (m755 H hv hs) H.one_mem)))

private theorem m1785 : g 1785 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1223,343,-235")) (hv 11852 (by decide))
    (H.mul_mem (m1223 H hv hs) (H.mul_mem (m343 H hv hs) (H.mul_mem (H.inv_mem (m235 H hs)) H.one_mem)))

private theorem m864 : g 864 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "863,-685,-93")) (hv 11866 (by decide))
    (H.mul_mem (m863 H hv hs) (H.mul_mem (H.inv_mem (m685 H hv hs)) (H.mul_mem (H.inv_mem (m93 H hv hs)) H.one_mem)))

private theorem m1876 : g 1876 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1,1432,149")) (hv 11876 (by decide))
    (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (m1432 H hv hs) (H.mul_mem (m149 H hv hs) H.one_mem)))

private theorem m847 : g 847 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "77,588,-1041")) (hv 11883 (by decide))
    (H.mul_mem (m77 H hv hs) (H.mul_mem (m588 H hv hs) (H.mul_mem (H.inv_mem (m1041 H hs)) H.one_mem)))

private theorem m1382 : g 1382 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "93,-1972")) (hv 11886 (by decide))
    (H.mul_mem (m93 H hv hs) (H.mul_mem (H.inv_mem (m1972 H hs)) H.one_mem))

private theorem m254 : g 254 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-475,1356")) (hv 11887 (by decide))
    (H.mul_mem (H.inv_mem (m475 H hv hs)) (H.mul_mem (m1356 H hv hs) H.one_mem))

private theorem m1279 : g 1279 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "859,1432,-1,1741")) (hv 11925 (by decide))
    (H.mul_mem (m859 H hv hs) (H.mul_mem (m1432 H hv hs) (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (m1741 H hv hs) H.one_mem))))

private theorem m264 : g 264 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1778,645,850")) (hv 11937 (by decide))
    (H.mul_mem (H.inv_mem (m1778 H hv hs)) (H.mul_mem (m645 H hv hs) (H.mul_mem (m850 H hv hs) H.one_mem)))

private theorem m95 : g 95 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1482,741,2")) (hv 11939 (by decide))
    (H.mul_mem (m1482 H hv hs) (H.mul_mem (m741 H hv hs) (H.mul_mem (m2 H hs) H.one_mem)))

private theorem m1020 : g 1020 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1213,1972")) (hv 11980 (by decide))
    (H.mul_mem (m1213 H hv hs) (H.mul_mem (m1972 H hs) H.one_mem))

private theorem m153 : g 153 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1,107")) (hv 11984 (by decide))
    (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (m107 H hv hs) H.one_mem))

private theorem m1884 : g 1884 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "282,-12,-93")) (hv 11997 (by decide))
    (H.mul_mem (m282 H hv hs) (H.mul_mem (H.inv_mem (m12 H hv hs)) (H.mul_mem (H.inv_mem (m93 H hv hs)) H.one_mem)))

private theorem m1552 : g 1552 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-863,161")) (hv 12014 (by decide))
    (H.mul_mem (H.inv_mem (m863 H hv hs)) (H.mul_mem (m161 H hv hs) H.one_mem))

private theorem m1002 : g 1002 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-313,-1367,38")) (hv 12025 (by decide))
    (H.mul_mem (H.inv_mem (m313 H hv hs)) (H.mul_mem (H.inv_mem (m1367 H hv hs)) (H.mul_mem (m38 H hv hs) H.one_mem)))

private theorem m292 : g 292 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1264,-712")) (hv 12047 (by decide))
    (H.mul_mem (m1264 H hv hs) (H.mul_mem (H.inv_mem (m712 H hv hs)) H.one_mem))

private theorem m156 : g 156 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "138,-177,524")) (hv 12678 (by decide))
    (H.mul_mem (m138 H hv hs) (H.mul_mem (H.inv_mem (m177 H hv hs)) (H.mul_mem (m524 H hv hs) H.one_mem)))

private theorem m1660 : g 1660 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-674,348,1")) (hv 12715 (by decide))
    (H.mul_mem (H.inv_mem (m674 H hv hs)) (H.mul_mem (m348 H hs) (H.mul_mem (m1 H hs) H.one_mem)))

private theorem m374 : g 374 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "422,-1156,490")) (hv 12733 (by decide))
    (H.mul_mem (m422 H hs) (H.mul_mem (H.inv_mem (m1156 H hv hs)) (H.mul_mem (m490 H hv hs) H.one_mem)))

private theorem m1177 : g 1177 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-422,1869,-463")) (hv 12747 (by decide))
    (H.mul_mem (H.inv_mem (m422 H hs)) (H.mul_mem (m1869 H hv hs) (H.mul_mem (H.inv_mem (m463 H hv hs)) H.one_mem)))

private theorem m1269 : g 1269 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-799,755,-1168")) (hv 12793 (by decide))
    (H.mul_mem (H.inv_mem (m799 H hv hs)) (H.mul_mem (m755 H hv hs) (H.mul_mem (H.inv_mem (m1168 H hv hs)) H.one_mem)))

private theorem m1298 : g 1298 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-107,712")) (hv 12813 (by decide))
    (H.mul_mem (H.inv_mem (m107 H hv hs)) (H.mul_mem (m712 H hv hs) H.one_mem))

private theorem m185 : g 185 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1,-675")) (hv 12832 (by decide))
    (H.mul_mem (m1 H hs) (H.mul_mem (H.inv_mem (m675 H hv hs)) H.one_mem))

private theorem m887 : g 887 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "822,736,273")) (hv 12866 (by decide))
    (H.mul_mem (m822 H hv hs) (H.mul_mem (m736 H hv hs) (H.mul_mem (m273 H hs) H.one_mem)))

private theorem m898 : g 898 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-3,-1394,-1772")) (hv 12882 (by decide))
    (H.mul_mem (H.inv_mem (m3 H hs)) (H.mul_mem (H.inv_mem (m1394 H hv hs)) (H.mul_mem (H.inv_mem (m1772 H hs)) H.one_mem)))

private theorem m827 : g 827 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-12,526")) (hv 12886 (by decide))
    (H.mul_mem (H.inv_mem (m12 H hv hs)) (H.mul_mem (m526 H hv hs) H.one_mem))

private theorem m949 : g 949 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-526,3,1424,1")) (hv 12908 (by decide))
    (H.mul_mem (H.inv_mem (m526 H hv hs)) (H.mul_mem (m3 H hs) (H.mul_mem (m1424 H hv hs) (H.mul_mem (m1 H hs) H.one_mem))))

private theorem m639 : g 639 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-343,764,-1083")) (hv 12909 (by decide))
    (H.mul_mem (H.inv_mem (m343 H hv hs)) (H.mul_mem (m764 H hv hs) (H.mul_mem (H.inv_mem (m1083 H hv hs)) H.one_mem)))

private theorem m88 : g 88 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "161,-119,1139,-216")) (hv 12911 (by decide))
    (H.mul_mem (m161 H hv hs) (H.mul_mem (H.inv_mem (m119 H hv hs)) (H.mul_mem (m1139 H hv hs) (H.mul_mem (H.inv_mem (m216 H hv hs)) H.one_mem))))

private theorem m1147 : g 1147 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-675,-1053")) (hv 13642 (by decide))
    (H.mul_mem (H.inv_mem (m675 H hv hs)) (H.mul_mem (H.inv_mem (m1053 H hv hs)) H.one_mem))

private theorem m853 : g 853 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-232,-274,-119")) (hv 13653 (by decide))
    (H.mul_mem (H.inv_mem (m232 H hv hs)) (H.mul_mem (H.inv_mem (m274 H hv hs)) (H.mul_mem (H.inv_mem (m119 H hv hs)) H.one_mem)))

private theorem m314 : g 314 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1367,-422,208,-422")) (hv 13666 (by decide))
    (H.mul_mem (H.inv_mem (m1367 H hv hs)) (H.mul_mem (H.inv_mem (m422 H hs)) (H.mul_mem (m208 H hv hs) (H.mul_mem (H.inv_mem (m422 H hs)) H.one_mem))))

private theorem m473 : g 473 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-414,1115,-560")) (hv 13672 (by decide))
    (H.mul_mem (H.inv_mem (m414 H hv hs)) (H.mul_mem (m1115 H hs) (H.mul_mem (H.inv_mem (m560 H hv hs)) H.one_mem)))

private theorem m979 : g 979 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1428,758,-293,1778")) (hv 13682 (by decide))
    (H.mul_mem (m1428 H hv hs) (H.mul_mem (m758 H hv hs) (H.mul_mem (H.inv_mem (m293 H hv hs)) (H.mul_mem (m1778 H hv hs) H.one_mem))))

private theorem m1514 : g 1514 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "12,822,415,1188")) (hv 13688 (by decide))
    (H.mul_mem (m12 H hv hs) (H.mul_mem (m822 H hv hs) (H.mul_mem (m415 H hv hs) (H.mul_mem (m1188 H hv hs) H.one_mem))))

private theorem m1412 : g 1412 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "237,-12,1958")) (hv 13690 (by decide))
    (H.mul_mem (m237 H hv hs) (H.mul_mem (H.inv_mem (m12 H hv hs)) (H.mul_mem (m1958 H hs) H.one_mem)))

private theorem m271 : g 271 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-475,-161,-1206")) (hv 13715 (by decide))
    (H.mul_mem (H.inv_mem (m475 H hv hs)) (H.mul_mem (H.inv_mem (m161 H hv hs)) (H.mul_mem (H.inv_mem (m1206 H hv hs)) H.one_mem)))

private theorem m821 : g 821 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "801,-216,-755")) (hv 31039 (by decide))
    (H.mul_mem (m801 H hv hs) (H.mul_mem (H.inv_mem (m216 H hv hs)) (H.mul_mem (H.inv_mem (m755 H hv hs)) H.one_mem)))

private theorem m295 : g 295 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "104,235,177")) (hv 13763 (by decide))
    (H.mul_mem (m104 H hv hs) (H.mul_mem (m235 H hs) (H.mul_mem (m177 H hv hs) H.one_mem)))

private theorem m220 : g 220 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-37,-56,-1041,-1394,-1772")) (hv 13767 (by decide))
    (H.mul_mem (H.inv_mem (m37 H hv hs)) (H.mul_mem (H.inv_mem (m56 H hv hs)) (H.mul_mem (H.inv_mem (m1041 H hs)) (H.mul_mem (H.inv_mem (m1394 H hv hs)) (H.mul_mem (H.inv_mem (m1772 H hs)) H.one_mem)))))

private theorem m1035 : g 1035 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-77,-928,-1208")) (hv 13772 (by decide))
    (H.mul_mem (H.inv_mem (m77 H hv hs)) (H.mul_mem (H.inv_mem (m928 H hv hs)) (H.mul_mem (H.inv_mem (m1208 H hv hs)) H.one_mem)))

private theorem m2052 : g 2052 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-510,1041,-1")) (hv 13820 (by decide))
    (H.mul_mem (H.inv_mem (m510 H hv hs)) (H.mul_mem (m1041 H hs) (H.mul_mem (H.inv_mem (m1 H hs)) H.one_mem)))

private theorem m1093 : g 1093 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-863,-1106,-107")) (hv 13831 (by decide))
    (H.mul_mem (H.inv_mem (m863 H hv hs)) (H.mul_mem (H.inv_mem (m1106 H hs)) (H.mul_mem (H.inv_mem (m107 H hv hs)) H.one_mem)))

private theorem m715 : g 715 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-359,2037,1432")) (hv 13836 (by decide))
    (H.mul_mem (H.inv_mem (m359 H hv hs)) (H.mul_mem (m2037 H hv hs) (H.mul_mem (m1432 H hv hs) H.one_mem)))

private theorem m408 : g 408 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1156,1")) (hv 13841 (by decide))
    (H.mul_mem (m1156 H hv hs) (H.mul_mem (m1 H hs) H.one_mem))

private theorem m263 : g 263 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1018,-1156,3,1408")) (hv 13856 (by decide))
    (H.mul_mem (m1018 H hv hs) (H.mul_mem (H.inv_mem (m1156 H hv hs)) (H.mul_mem (m3 H hs) (H.mul_mem (m1408 H hv hs) H.one_mem))))

private theorem m1390 : g 1390 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-522,-1206,803")) (hv 13911 (by decide))
    (H.mul_mem (H.inv_mem (m522 H hv hs)) (H.mul_mem (H.inv_mem (m1206 H hv hs)) (H.mul_mem (m803 H hv hs) H.one_mem)))

private theorem m72 : g 72 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "84,758,625")) (hv 14713 (by decide))
    (H.mul_mem (m84 H hv hs) (H.mul_mem (m758 H hv hs) (H.mul_mem (m625 H hv hs) H.one_mem)))

private theorem m1488 : g 1488 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-414,1115,116,-701,-1450")) (hv 31040 (by decide))
    (H.mul_mem (H.inv_mem (m414 H hv hs)) (H.mul_mem (m1115 H hs) (H.mul_mem (m116 H hv hs) (H.mul_mem (H.inv_mem (m701 H hv hs)) (H.mul_mem (H.inv_mem (m1450 H hv hs)) H.one_mem)))))

private theorem m689 : g 689 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1703,-359,-1703")) (hv 14743 (by decide))
    (H.mul_mem (m1703 H hv hs) (H.mul_mem (H.inv_mem (m359 H hv hs)) (H.mul_mem (H.inv_mem (m1703 H hv hs)) H.one_mem)))

private theorem m1159 : g 1159 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "359,-1018")) (hv 14784 (by decide))
    (H.mul_mem (m359 H hv hs) (H.mul_mem (H.inv_mem (m1018 H hv hs)) H.one_mem))

private theorem m981 : g 981 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-798,1106,-758,-1083")) (hv 14851 (by decide))
    (H.mul_mem (H.inv_mem (m798 H hv hs)) (H.mul_mem (m1106 H hs) (H.mul_mem (H.inv_mem (m758 H hv hs)) (H.mul_mem (H.inv_mem (m1083 H hv hs)) H.one_mem))))

private theorem m1378 : g 1378 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-323,172,822")) (hv 14906 (by decide))
    (H.mul_mem (H.inv_mem (m323 H hv hs)) (H.mul_mem (m172 H hv hs) (H.mul_mem (m822 H hv hs) H.one_mem)))

private theorem m74 : g 74 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1686,-743,-1264")) (hv 14918 (by decide))
    (H.mul_mem (H.inv_mem (m1686 H hv hs)) (H.mul_mem (H.inv_mem (m743 H hv hs)) (H.mul_mem (H.inv_mem (m1264 H hv hs)) H.one_mem)))

private theorem m992 : g 992 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-227,736,3,1753")) (hv 14926 (by decide))
    (H.mul_mem (H.inv_mem (m227 H hv hs)) (H.mul_mem (m736 H hv hs) (H.mul_mem (m3 H hs) (H.mul_mem (m1753 H hv hs) H.one_mem))))

private theorem m587 : g 587 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-84,-231,1367,-354")) (hv 14933 (by decide))
    (H.mul_mem (H.inv_mem (m84 H hv hs)) (H.mul_mem (H.inv_mem (m231 H hv hs)) (H.mul_mem (m1367 H hv hs) (H.mul_mem (H.inv_mem (m354 H hv hs)) H.one_mem))))

private theorem m249 : g 249 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1432,-2037,189,216")) (hv 14938 (by decide))
    (H.mul_mem (H.inv_mem (m1432 H hv hs)) (H.mul_mem (H.inv_mem (m2037 H hv hs)) (H.mul_mem (m189 H hv hs) (H.mul_mem (m216 H hv hs) H.one_mem))))

private theorem m1455 : g 1455 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-84,1620,235,1428,-1083")) (hv 14950 (by decide))
    (H.mul_mem (H.inv_mem (m84 H hv hs)) (H.mul_mem (m1620 H hv hs) (H.mul_mem (m235 H hs) (H.mul_mem (m1428 H hv hs) (H.mul_mem (H.inv_mem (m1083 H hv hs)) H.one_mem)))))

private theorem m1029 : g 1029 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "533,-293,-20,-107")) (hv 15017 (by decide))
    (H.mul_mem (m533 H hv hs) (H.mul_mem (H.inv_mem (m293 H hv hs)) (H.mul_mem (H.inv_mem (m20 H hv hs)) (H.mul_mem (H.inv_mem (m107 H hv hs)) H.one_mem))))

private theorem m649 : g 649 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "510,-692,-119")) (hv 15049 (by decide))
    (H.mul_mem (m510 H hv hs) (H.mul_mem (H.inv_mem (m692 H hv hs)) (H.mul_mem (H.inv_mem (m119 H hv hs)) H.one_mem)))

private theorem m629 : g 629 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1,107,522,-514")) (hv 15992 (by decide))
    (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (m107 H hv hs) (H.mul_mem (m522 H hv hs) (H.mul_mem (H.inv_mem (m514 H hv hs)) H.one_mem))))

private theorem m1338 : g 1338 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1264,-712,1018,-172,12")) (hv 15998 (by decide))
    (H.mul_mem (m1264 H hv hs) (H.mul_mem (H.inv_mem (m712 H hv hs)) (H.mul_mem (m1018 H hv hs) (H.mul_mem (H.inv_mem (m172 H hv hs)) (H.mul_mem (m12 H hv hs) H.one_mem)))))

private theorem m131 : g 131 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "282,822,-1428,1053,216")) (hv 16000 (by decide))
    (H.mul_mem (m282 H hv hs) (H.mul_mem (m822 H hv hs) (H.mul_mem (H.inv_mem (m1428 H hv hs)) (H.mul_mem (m1053 H hv hs) (H.mul_mem (m216 H hv hs) H.one_mem)))))

private theorem m1166 : g 1166 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-906,-785,-3,785")) (hv 16056 (by decide))
    (H.mul_mem (H.inv_mem (m906 H hs)) (H.mul_mem (H.inv_mem (m785 H hv hs)) (H.mul_mem (H.inv_mem (m3 H hs)) (H.mul_mem (m785 H hv hs) H.one_mem))))

private theorem m745 : g 745 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-255,322,250,-1083")) (hv 16062 (by decide))
    (H.mul_mem (H.inv_mem (m255 H hv hs)) (H.mul_mem (m322 H hv hs) (H.mul_mem (m250 H hv hs) (H.mul_mem (H.inv_mem (m1083 H hv hs)) H.one_mem))))

private theorem m513 : g 513 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1083,1,-1424,-688,-937")) (hv 16078 (by decide))
    (H.mul_mem (m1083 H hv hs) (H.mul_mem (m1 H hs) (H.mul_mem (H.inv_mem (m1424 H hv hs)) (H.mul_mem (H.inv_mem (m688 H hs)) (H.mul_mem (H.inv_mem (m937 H hv hs)) H.one_mem)))))

private theorem m782 : g 782 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1432,-2037,23,273")) (hv 16092 (by decide))
    (H.mul_mem (H.inv_mem (m1432 H hv hs)) (H.mul_mem (H.inv_mem (m2037 H hv hs)) (H.mul_mem (m23 H hs) (H.mul_mem (m273 H hs) H.one_mem))))

private theorem m412 : g 412 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1203,214,1156,1,-12")) (hv 16124 (by decide))
    (H.mul_mem (m1203 H hv hs) (H.mul_mem (m214 H hv hs) (H.mul_mem (m1156 H hv hs) (H.mul_mem (m1 H hs) (H.mul_mem (H.inv_mem (m12 H hv hs)) H.one_mem)))))

private theorem m462 : g 462 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "274,-1087,216,-785,3")) (hv 16159 (by decide))
    (H.mul_mem (m274 H hv hs) (H.mul_mem (H.inv_mem (m1087 H hv hs)) (H.mul_mem (m216 H hv hs) (H.mul_mem (H.inv_mem (m785 H hv hs)) (H.mul_mem (m3 H hs) H.one_mem)))))

private theorem m1908 : g 1908 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-588,-3,729")) (hv 16165 (by decide))
    (H.mul_mem (H.inv_mem (m588 H hv hs)) (H.mul_mem (H.inv_mem (m3 H hs)) (H.mul_mem (m729 H hv hs) H.one_mem)))

private theorem m903 : g 903 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "107,522,510,20,1041")) (hv 16200 (by decide))
    (H.mul_mem (m107 H hv hs) (H.mul_mem (m522 H hv hs) (H.mul_mem (m510 H hv hs) (H.mul_mem (m20 H hv hs) (H.mul_mem (m1041 H hs) H.one_mem)))))

private theorem m36 : g 36 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "161,475,1053,348,863")) (hv 16268 (by decide))
    (H.mul_mem (m161 H hv hs) (H.mul_mem (m475 H hv hs) (H.mul_mem (m1053 H hv hs) (H.mul_mem (m348 H hs) (H.mul_mem (m863 H hv hs) H.one_mem)))))

private theorem m634 : g 634 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1087,-701,237,701")) (hv 16280 (by decide))
    (H.mul_mem (m1087 H hv hs) (H.mul_mem (H.inv_mem (m701 H hv hs)) (H.mul_mem (m237 H hv hs) (H.mul_mem (m701 H hv hs) H.one_mem))))

private theorem m1392 : g 1392 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1018,-1156,360,1408,480")) (hv 16320 (by decide))
    (H.mul_mem (m1018 H hv hs) (H.mul_mem (H.inv_mem (m1156 H hv hs)) (H.mul_mem (m360 H hv hs) (H.mul_mem (m1408 H hv hs) (H.mul_mem (m480 H hs) H.one_mem)))))

private theorem m831 : g 831 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1703,-675,736,3")) (hv 16366 (by decide))
    (H.mul_mem (m1703 H hv hs) (H.mul_mem (H.inv_mem (m675 H hv hs)) (H.mul_mem (m736 H hv hs) (H.mul_mem (m3 H hs) H.one_mem))))

private theorem m1701 : g 1701 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "214,-510,-524,227,1")) (hv 17601 (by decide))
    (H.mul_mem (m214 H hv hs) (H.mul_mem (H.inv_mem (m510 H hv hs)) (H.mul_mem (H.inv_mem (m524 H hv hs)) (H.mul_mem (m227 H hv hs) (H.mul_mem (m1 H hs) H.one_mem)))))

private theorem m855 : g 855 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "675,284,-755,-1115")) (hv 17619 (by decide))
    (H.mul_mem (m675 H hv hs) (H.mul_mem (m284 H hv hs) (H.mul_mem (H.inv_mem (m755 H hv hs)) (H.mul_mem (H.inv_mem (m1115 H hs)) H.one_mem))))

private theorem m957 : g 957 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1958,-1450,-1703,692,-510")) (hv 17632 (by decide))
    (H.mul_mem (m1958 H hs) (H.mul_mem (H.inv_mem (m1450 H hv hs)) (H.mul_mem (H.inv_mem (m1703 H hv hs)) (H.mul_mem (m692 H hv hs) (H.mul_mem (H.inv_mem (m510 H hv hs)) H.one_mem)))))

private theorem m630 : g 630 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1208,23,227,-1156,1772,701")) (hv 17679 (by decide))
    (H.mul_mem (H.inv_mem (m1208 H hv hs)) (H.mul_mem (m23 H hs) (H.mul_mem (m227 H hv hs) (H.mul_mem (H.inv_mem (m1156 H hv hs)) (H.mul_mem (m1772 H hs) (H.mul_mem (m701 H hv hs) H.one_mem))))))

private theorem m147 : g 147 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "313,1041,-197,216,729")) (hv 17681 (by decide))
    (H.mul_mem (m313 H hv hs) (H.mul_mem (m1041 H hs) (H.mul_mem (H.inv_mem (m197 H hv hs)) (H.mul_mem (m216 H hv hs) (H.mul_mem (m729 H hv hs) H.one_mem)))))

private theorem m1265 : g 1265 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "510,-214,-84,161")) (hv 17741 (by decide))
    (H.mul_mem (m510 H hv hs) (H.mul_mem (H.inv_mem (m214 H hv hs)) (H.mul_mem (H.inv_mem (m84 H hv hs)) (H.mul_mem (m161 H hv hs) H.one_mem))))

private theorem m1210 : g 1210 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1018,1451,-729,274,1115,-107,243,-109,1,-1424")) (hv 31041 (by decide))
    (H.mul_mem (H.inv_mem (m1018 H hv hs)) (H.mul_mem (m1451 H hv hs) (H.mul_mem (H.inv_mem (m729 H hv hs)) (H.mul_mem (m274 H hv hs) (H.mul_mem (m1115 H hs) (H.mul_mem (H.inv_mem (m107 H hv hs)) (H.mul_mem (m243 H hv hs) (H.mul_mem (H.inv_mem (m109 H hv hs)) (H.mul_mem (m1 H hs) (H.mul_mem (H.inv_mem (m1424 H hv hs)) H.one_mem))))))))))

private theorem m1273 : g 1273 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "675,-1703,-37,274,1115,-3,-273")) (hv 17864 (by decide))
    (H.mul_mem (m675 H hv hs) (H.mul_mem (H.inv_mem (m1703 H hv hs)) (H.mul_mem (H.inv_mem (m37 H hv hs)) (H.mul_mem (m274 H hv hs) (H.mul_mem (m1115 H hs) (H.mul_mem (H.inv_mem (m3 H hs)) (H.mul_mem (H.inv_mem (m273 H hs)) H.one_mem)))))))

private theorem m42 : g 42 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1824,-890,-755,799,1824,1203,214")) (hv 17885 (by decide))
    (H.mul_mem (m1824 H hv hs) (H.mul_mem (H.inv_mem (m890 H hv hs)) (H.mul_mem (H.inv_mem (m755 H hv hs)) (H.mul_mem (m799 H hv hs) (H.mul_mem (m1824 H hv hs) (H.mul_mem (m1203 H hv hs) (H.mul_mem (m214 H hv hs) H.one_mem)))))))

private theorem m10 : g 10 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-161,-533,12,-1450,-422")) (hv 18925 (by decide))
    (H.mul_mem (H.inv_mem (m161 H hv hs)) (H.mul_mem (H.inv_mem (m533 H hv hs)) (H.mul_mem (m12 H hv hs) (H.mul_mem (H.inv_mem (m1450 H hv hs)) (H.mul_mem (H.inv_mem (m422 H hs)) H.one_mem)))))

private theorem m1574 : g 1574 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "107,-1115,3,-736,-480,729,-1168,284")) (hv 18950 (by decide))
    (H.mul_mem (m107 H hv hs) (H.mul_mem (H.inv_mem (m1115 H hs)) (H.mul_mem (m3 H hs) (H.mul_mem (H.inv_mem (m736 H hv hs)) (H.mul_mem (H.inv_mem (m480 H hs)) (H.mul_mem (m729 H hv hs) (H.mul_mem (H.inv_mem (m1168 H hv hs)) (H.mul_mem (m284 H hv hs) H.one_mem))))))))

private theorem m431 : g 431 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-274,216,510,-197,-780,3,-906,2")) (hv 19018 (by decide))
    (H.mul_mem (H.inv_mem (m274 H hv hs)) (H.mul_mem (m216 H hv hs) (H.mul_mem (m510 H hv hs) (H.mul_mem (H.inv_mem (m197 H hv hs)) (H.mul_mem (H.inv_mem (m780 H hv hs)) (H.mul_mem (m3 H hs) (H.mul_mem (H.inv_mem (m906 H hs)) (H.mul_mem (m2 H hs) H.one_mem))))))))

private theorem m1816 : g 1816 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-701,-1772,-1432,1235,-148,-1824,1,-189")) (hv 19021 (by decide))
    (H.mul_mem (H.inv_mem (m701 H hv hs)) (H.mul_mem (H.inv_mem (m1772 H hs)) (H.mul_mem (H.inv_mem (m1432 H hv hs)) (H.mul_mem (m1235 H hv hs) (H.mul_mem (H.inv_mem (m148 H hv hs)) (H.mul_mem (H.inv_mem (m1824 H hv hs)) (H.mul_mem (m1 H hs) (H.mul_mem (H.inv_mem (m189 H hv hs)) H.one_mem))))))))

private theorem m1765 : g 1765 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-736,-1208,1106,-1405,-1168")) (hv 19033 (by decide))
    (H.mul_mem (H.inv_mem (m736 H hv hs)) (H.mul_mem (H.inv_mem (m1208 H hv hs)) (H.mul_mem (m1106 H hs) (H.mul_mem (H.inv_mem (m1405 H hv hs)) (H.mul_mem (H.inv_mem (m1168 H hv hs)) H.one_mem)))))

private theorem m1030 : g 1030 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "243,109,243,-109,758,-1106,23,227")) (hv 19040 (by decide))
    (H.mul_mem (m243 H hv hs) (H.mul_mem (m109 H hv hs) (H.mul_mem (m243 H hv hs) (H.mul_mem (H.inv_mem (m109 H hv hs)) (H.mul_mem (m758 H hv hs) (H.mul_mem (H.inv_mem (m1106 H hs)) (H.mul_mem (m23 H hs) (H.mul_mem (m227 H hv hs) H.one_mem))))))))

private theorem m574 : g 574 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-148,-1432,-2037,23,-688,736,688,-284,1106,273,-1203,3,-273,1,-23")) (hv 31042 (by decide))
    (H.mul_mem (H.inv_mem (m148 H hv hs)) (H.mul_mem (H.inv_mem (m1432 H hv hs)) (H.mul_mem (H.inv_mem (m2037 H hv hs)) (H.mul_mem (m23 H hs) (H.mul_mem (H.inv_mem (m688 H hs)) (H.mul_mem (m736 H hv hs) (H.mul_mem (m688 H hs) (H.mul_mem (H.inv_mem (m284 H hv hs)) (H.mul_mem (m1106 H hs) (H.mul_mem (m273 H hs) (H.mul_mem (H.inv_mem (m1203 H hv hs)) (H.mul_mem (m3 H hs) (H.mul_mem (H.inv_mem (m273 H hs)) (H.mul_mem (m1 H hs) (H.mul_mem (H.inv_mem (m23 H hs)) H.one_mem)))))))))))))))

private theorem m195 : g 195 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "780,197,-588,-77,-288,1083,-1451,-189,-863")) (hv 19042 (by decide))
    (H.mul_mem (m780 H hv hs) (H.mul_mem (m197 H hv hs) (H.mul_mem (H.inv_mem (m588 H hv hs)) (H.mul_mem (H.inv_mem (m77 H hv hs)) (H.mul_mem (H.inv_mem (m288 H hv hs)) (H.mul_mem (m1083 H hv hs) (H.mul_mem (H.inv_mem (m1451 H hv hs)) (H.mul_mem (H.inv_mem (m189 H hv hs)) (H.mul_mem (H.inv_mem (m863 H hv hs)) H.one_mem)))))))))

private theorem m1662 : g 1662 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "107,-348,-475,-3,-688,675")) (hv 19060 (by decide))
    (H.mul_mem (m107 H hv hs) (H.mul_mem (H.inv_mem (m348 H hs)) (H.mul_mem (H.inv_mem (m475 H hv hs)) (H.mul_mem (H.inv_mem (m3 H hs)) (H.mul_mem (H.inv_mem (m688 H hs)) (H.mul_mem (m675 H hv hs) H.one_mem))))))

private theorem m581 : g 581 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-755,522,906,-119,422,1450,-12,533,161,-514,-2,-1772")) (hv 31043 (by decide))
    (H.mul_mem (H.inv_mem (m755 H hv hs)) (H.mul_mem (m522 H hv hs) (H.mul_mem (m906 H hs) (H.mul_mem (H.inv_mem (m119 H hv hs)) (H.mul_mem (m422 H hs) (H.mul_mem (m1450 H hv hs) (H.mul_mem (H.inv_mem (m12 H hv hs)) (H.mul_mem (m533 H hv hs) (H.mul_mem (m161 H hv hs) (H.mul_mem (H.inv_mem (m514 H hv hs)) (H.mul_mem (H.inv_mem (m2 H hs)) (H.mul_mem (H.inv_mem (m1772 H hs)) H.one_mem))))))))))))

private theorem m738 : g 738 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "688,-1432,-2037,189,-688,-1053,348")) (hv 19233 (by decide))
    (H.mul_mem (m688 H hs) (H.mul_mem (H.inv_mem (m1432 H hv hs)) (H.mul_mem (H.inv_mem (m2037 H hv hs)) (H.mul_mem (m189 H hv hs) (H.mul_mem (H.inv_mem (m688 H hs)) (H.mul_mem (H.inv_mem (m1053 H hv hs)) (H.mul_mem (m348 H hs) H.one_mem)))))))

private theorem m122 : g 122 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1053,890,1405,-533,12,-1450,-422,-77,1405,-1106")) (hv 19244 (by decide))
    (H.mul_mem (H.inv_mem (m1053 H hv hs)) (H.mul_mem (m890 H hv hs) (H.mul_mem (m1405 H hv hs) (H.mul_mem (H.inv_mem (m533 H hv hs)) (H.mul_mem (m12 H hv hs) (H.mul_mem (H.inv_mem (m1450 H hv hs)) (H.mul_mem (H.inv_mem (m422 H hs)) (H.mul_mem (H.inv_mem (m77 H hv hs)) (H.mul_mem (m1405 H hv hs) (H.mul_mem (H.inv_mem (m1106 H hs)) H.one_mem))))))))))

private theorem m2018 : g 2018 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-480,729,348,906,480,19,3,-161")) (hv 20216 (by decide))
    (H.mul_mem (H.inv_mem (m480 H hs)) (H.mul_mem (m729 H hv hs) (H.mul_mem (m348 H hs) (H.mul_mem (m906 H hs) (H.mul_mem (m480 H hs) (H.mul_mem (m19 H hv hs) (H.mul_mem (m3 H hs) (H.mul_mem (H.inv_mem (m161 H hv hs)) H.one_mem))))))))

private theorem m558 : g 558 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-735,197,-1824,1168,1405")) (hv 20240 (by decide))
    (H.mul_mem (H.inv_mem (m735 H hv hs)) (H.mul_mem (m197 H hv hs) (H.mul_mem (H.inv_mem (m1824 H hv hs)) (H.mul_mem (m1168 H hv hs) (H.mul_mem (m1405 H hv hs) H.one_mem)))))

private theorem m449 : g 449 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1083,-189,906,-3")) (hv 20259 (by decide))
    (H.mul_mem (H.inv_mem (m1083 H hv hs)) (H.mul_mem (H.inv_mem (m189 H hv hs)) (H.mul_mem (m906 H hs) (H.mul_mem (H.inv_mem (m3 H hs)) H.one_mem))))

private theorem m1258 : g 1258 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-109,1620,208,-1,-208,-37,-1,1018")) (hv 20476 (by decide))
    (H.mul_mem (H.inv_mem (m109 H hv hs)) (H.mul_mem (m1620 H hv hs) (H.mul_mem (m208 H hv hs) (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (H.inv_mem (m208 H hv hs)) (H.mul_mem (H.inv_mem (m37 H hv hs)) (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (m1018 H hv hs) H.one_mem))))))))

private theorem m459 : g 459 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1235,1115,23,348,1432,148,-189,906,729")) (hv 20509 (by decide))
    (H.mul_mem (m1235 H hv hs) (H.mul_mem (m1115 H hs) (H.mul_mem (m23 H hs) (H.mul_mem (m348 H hs) (H.mul_mem (m1432 H hv hs) (H.mul_mem (m148 H hv hs) (H.mul_mem (H.inv_mem (m189 H hv hs)) (H.mul_mem (m906 H hs) (H.mul_mem (m729 H hv hs) H.one_mem)))))))))

private theorem m1321 : g 1321 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-197,-780,-1,-1083,-189,906,-3,780,197,-1")) (hv 20514 (by decide))
    (H.mul_mem (H.inv_mem (m197 H hv hs)) (H.mul_mem (H.inv_mem (m780 H hv hs)) (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (H.inv_mem (m1083 H hv hs)) (H.mul_mem (H.inv_mem (m189 H hv hs)) (H.mul_mem (m906 H hs) (H.mul_mem (H.inv_mem (m3 H hs)) (H.mul_mem (m780 H hv hs) (H.mul_mem (m197 H hv hs) (H.mul_mem (H.inv_mem (m1 H hs)) H.one_mem))))))))))

private theorem m1814 : g 1814 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-903")) (hv 5610 (by decide))
    (H.mul_mem (H.inv_mem (m903 H hv hs)) H.one_mem)

private theorem m1327 : g 1327 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-10")) (hv 5002 (by decide))
    (H.mul_mem (H.inv_mem (m10 H hv hs)) H.one_mem)

private theorem m1779 : g 1779 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1166")) (hv 4957 (by decide))
    (H.mul_mem (H.inv_mem (m1166 H hv hs)) H.one_mem)

private theorem m534 : g 534 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-42")) (hv 5368 (by decide))
    (H.mul_mem (H.inv_mem (m42 H hv hs)) H.one_mem)

private theorem m145 : g 145 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-74")) (hv 5557 (by decide))
    (H.mul_mem (H.inv_mem (m74 H hv hs)) H.one_mem)

private theorem m1014 : g 1014 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-449")) (hv 5125 (by decide))
    (H.mul_mem (H.inv_mem (m449 H hv hs)) H.one_mem)

private theorem m1434 : g 1434 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-591")) (hv 31044 (by decide))
    (H.mul_mem (H.inv_mem (m591 H hv hs)) H.one_mem)

private theorem m404 : g 404 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-122")) (hv 5076 (by decide))
    (H.mul_mem (H.inv_mem (m122 H hv hs)) H.one_mem)

private theorem m542 : g 542 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-153")) (hv 5090 (by decide))
    (H.mul_mem (H.inv_mem (m153 H hv hs)) H.one_mem)

private theorem m929 : g 929 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-185")) (hv 5218 (by decide))
    (H.mul_mem (H.inv_mem (m185 H hv hs)) H.one_mem)

private theorem m1639 : g 1639 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1159")) (hv 4653 (by decide))
    (H.mul_mem (H.inv_mem (m1159 H hv hs)) H.one_mem)

private theorem m690 : g 690 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-195")) (hv 5265 (by decide))
    (H.mul_mem (H.inv_mem (m195 H hv hs)) H.one_mem)

private theorem m1918 : g 1918 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-782")) (hv 5494 (by decide))
    (H.mul_mem (H.inv_mem (m782 H hv hs)) H.one_mem)

private theorem m1372 : g 1372 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1002")) (hv 5331 (by decide))
    (H.mul_mem (H.inv_mem (m1002 H hv hs)) H.one_mem)

private theorem m2055 : g 2055 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-244")) (hv 4781 (by decide))
    (H.mul_mem (H.inv_mem (m244 H hv hs)) H.one_mem)

private theorem m1196 : g 1196 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-249")) (hv 4913 (by decide))
    (H.mul_mem (H.inv_mem (m249 H hv hs)) H.one_mem)

private theorem m576 : g 576 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-462")) (hv 5046 (by decide))
    (H.mul_mem (H.inv_mem (m462 H hv hs)) H.one_mem)

private theorem m1863 : g 1863 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-264")) (hv 5361 (by decide))
    (H.mul_mem (H.inv_mem (m264 H hv hs)) H.one_mem)

private theorem m1707 : g 1707 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-271")) (hv 5150 (by decide))
    (H.mul_mem (H.inv_mem (m271 H hv hs)) H.one_mem)

private theorem m1783 : g 1783 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-497")) (hv 5006 (by decide))
    (H.mul_mem (H.inv_mem (m497 H hv hs)) H.one_mem)

private theorem m1391 : g 1391 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-292")) (hv 5431 (by decide))
    (H.mul_mem (H.inv_mem (m292 H hv hs)) H.one_mem)

private theorem m1647 : g 1647 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-295")) (hv 5206 (by decide))
    (H.mul_mem (H.inv_mem (m295 H hv hs)) H.one_mem)

private theorem m1287 : g 1287 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-303")) (hv 5414 (by decide))
    (H.mul_mem (H.inv_mem (m303 H hv hs)) H.one_mem)

private theorem m862 : g 862 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-310")) (hv 5398 (by decide))
    (H.mul_mem (H.inv_mem (m310 H hv hs)) H.one_mem)

private theorem m1000 : g 1000 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-459")) (hv 5680 (by decide))
    (H.mul_mem (H.inv_mem (m459 H hv hs)) H.one_mem)

private theorem m1511 : g 1511 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-745")) (hv 5122 (by decide))
    (H.mul_mem (H.inv_mem (m745 H hv hs)) H.one_mem)

private theorem m1421 : g 1421 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-513")) (hv 5407 (by decide))
    (H.mul_mem (H.inv_mem (m513 H hv hs)) H.one_mem)

private theorem m2000 : g 2000 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1816")) (hv 5508 (by decide))
    (H.mul_mem (H.inv_mem (m1816 H hv hs)) H.one_mem)

private theorem m1558 : g 1558 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-557")) (hv 5515 (by decide))
    (H.mul_mem (H.inv_mem (m557 H hv hs)) H.one_mem)

private theorem m1632 : g 1632 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-558")) (hv 4827 (by decide))
    (H.mul_mem (H.inv_mem (m558 H hv hs)) H.one_mem)

private theorem m989 : g 989 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-581")) (hv 5107 (by decide))
    (H.mul_mem (H.inv_mem (m581 H hv hs)) H.one_mem)

private theorem m1219 : g 1219 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-587")) (hv 4929 (by decide))
    (H.mul_mem (H.inv_mem (m587 H hv hs)) H.one_mem)

private theorem m1689 : g 1689 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1252")) (hv 4905 (by decide))
    (H.mul_mem (H.inv_mem (m1252 H hv hs)) H.one_mem)

private theorem m1033 : g 1033 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-630")) (hv 4685 (by decide))
    (H.mul_mem (H.inv_mem (m630 H hv hs)) H.one_mem)

private theorem m1386 : g 1386 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-634")) (hv 5463 (by decide))
    (H.mul_mem (H.inv_mem (m634 H hv hs)) H.one_mem)

private theorem m1762 : g 1762 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-639")) (hv 5709 (by decide))
    (H.mul_mem (H.inv_mem (m639 H hv hs)) H.one_mem)

private theorem m1474 : g 1474 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-738")) (hv 5147 (by decide))
    (H.mul_mem (H.inv_mem (m738 H hv hs)) H.one_mem)

private theorem m1973 : g 1973 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-847")) (hv 5678 (by decide))
    (H.mul_mem (H.inv_mem (m847 H hv hs)) H.one_mem)

private theorem m1284 : g 1284 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-887")) (hv 4603 (by decide))
    (H.mul_mem (H.inv_mem (m887 H hv hs)) H.one_mem)

private theorem m1910 : g 1910 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-949")) (hv 5070 (by decide))
    (H.mul_mem (H.inv_mem (m949 H hv hs)) H.one_mem)

private theorem m1107 : g 1107 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-957")) (hv 4956 (by decide))
    (H.mul_mem (H.inv_mem (m957 H hv hs)) H.one_mem)

private theorem m1058 : g 1058 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1030")) (hv 5211 (by decide))
    (H.mul_mem (H.inv_mem (m1030 H hv hs)) H.one_mem)

private theorem m2011 : g 2011 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1035")) (hv 31045 (by decide))
    (H.mul_mem (H.inv_mem (m1035 H hv hs)) H.one_mem)

private theorem m1692 : g 1692 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1147")) (hv 5491 (by decide))
    (H.mul_mem (H.inv_mem (m1147 H hv hs)) H.one_mem)

private theorem m1336 : g 1336 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1198")) (hv 5269 (by decide))
    (H.mul_mem (H.inv_mem (m1198 H hv hs)) H.one_mem)

private theorem m1776 : g 1776 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1265")) (hv 5058 (by decide))
    (H.mul_mem (H.inv_mem (m1265 H hv hs)) H.one_mem)

private theorem m1545 : g 1545 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1273")) (hv 5347 (by decide))
    (H.mul_mem (H.inv_mem (m1273 H hv hs)) H.one_mem)

private theorem m1865 : g 1865 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1338")) (hv 5432 (by decide))
    (H.mul_mem (H.inv_mem (m1338 H hv hs)) H.one_mem)

private theorem m2019 : g 2019 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1374")) (hv 31046 (by decide))
    (H.mul_mem (H.inv_mem (m1374 H hv hs)) H.one_mem)

private theorem m1846 : g 1846 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1412")) (hv 5094 (by decide))
    (H.mul_mem (H.inv_mem (m1412 H hv hs)) H.one_mem)

private theorem m1546 : g 1546 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1488")) (hv 5748 (by decide))
    (H.mul_mem (H.inv_mem (m1488 H hv hs)) H.one_mem)

private theorem m1581 : g 1581 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1574")) (hv 5535 (by decide))
    (H.mul_mem (H.inv_mem (m1574 H hv hs)) H.one_mem)

private theorem m1996 : g 1996 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1908")) (hv 31047 (by decide))
    (H.mul_mem (H.inv_mem (m1908 H hv hs)) H.one_mem)

private theorem m661 : g 661 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-558")) (hv 6292 (by decide))
    (H.mul_mem (H.inv_mem (m558 H hv hs)) H.one_mem)

private theorem m1578 : g 1578 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "473")) (hv 7601 (by decide))
    (H.mul_mem (m473 H hv hs) H.one_mem)

private theorem m336 : g 336 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-431,735")) (hv 10074 (by decide))
    (H.mul_mem (H.inv_mem (m431 H hv hs)) (H.mul_mem (m735 H hv hs) H.one_mem))

private theorem m2009 : g 2009 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-88,-533")) (hv 10079 (by decide))
    (H.mul_mem (H.inv_mem (m88 H hv hs)) (H.mul_mem (H.inv_mem (m533 H hv hs)) H.one_mem))

private theorem m1080 : g 1080 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1083,449")) (hv 10086 (by decide))
    (H.mul_mem (m1083 H hv hs) (H.mul_mem (m449 H hv hs) H.one_mem))

private theorem m1413 : g 1413 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1412,-692")) (hv 10092 (by decide))
    (H.mul_mem (m1412 H hv hs) (H.mul_mem (H.inv_mem (m692 H hv hs)) H.one_mem))

private theorem m351 : g 351 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-263,-1093")) (hv 10105 (by decide))
    (H.mul_mem (H.inv_mem (m263 H hv hs)) (H.mul_mem (H.inv_mem (m1093 H hv hs)) H.one_mem))

private theorem m1943 : g 1943 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-412,-1701")) (hv 10107 (by decide))
    (H.mul_mem (H.inv_mem (m412 H hv hs)) (H.mul_mem (H.inv_mem (m1701 H hv hs)) H.one_mem))

private theorem m411 : g 411 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "853,1958")) (hv 10115 (by decide))
    (H.mul_mem (m853 H hv hs) (H.mul_mem (m1958 H hs) H.one_mem))

private theorem m365 : g 365 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1041,-847")) (hv 10122 (by decide))
    (H.mul_mem (H.inv_mem (m1041 H hs)) (H.mul_mem (H.inv_mem (m847 H hv hs)) H.one_mem))

private theorem m916 : g 916 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "408,1972")) (hv 10142 (by decide))
    (H.mul_mem (m408 H hv hs) (H.mul_mem (m1972 H hs) H.one_mem))

private theorem m1969 : g 1969 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1035,-345")) (hv 10155 (by decide))
    (H.mul_mem (H.inv_mem (m1035 H hv hs)) (H.mul_mem (H.inv_mem (m345 H hv hs)) H.one_mem))

private theorem m659 : g 659 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-898,1087")) (hv 10172 (by decide))
    (H.mul_mem (H.inv_mem (m898 H hv hs)) (H.mul_mem (m1087 H hv hs) H.one_mem))

private theorem m656 : g 656 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-677,-131")) (hv 10175 (by decide))
    (H.mul_mem (H.inv_mem (m677 H hv hs)) (H.mul_mem (H.inv_mem (m131 H hv hs)) H.one_mem))

private theorem m596 : g 596 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1688,-220")) (hv 10176 (by decide))
    (H.mul_mem (H.inv_mem (m1688 H hv hs)) (H.mul_mem (H.inv_mem (m220 H hv hs)) H.one_mem))

private theorem m154 : g 154 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "153,-533")) (hv 10180 (by decide))
    (H.mul_mem (m153 H hv hs) (H.mul_mem (H.inv_mem (m533 H hv hs)) H.one_mem))

private theorem m1553 : g 1553 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-374,-3,374")) (hv 10229 (by decide))
    (H.mul_mem (H.inv_mem (m374 H hv hs)) (H.mul_mem (H.inv_mem (m3 H hs)) (H.mul_mem (m374 H hv hs) H.one_mem)))

private theorem m1489 : g 1489 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-414,-855")) (hv 10232 (by decide))
    (H.mul_mem (H.inv_mem (m414 H hv hs)) (H.mul_mem (H.inv_mem (m855 H hv hs)) H.one_mem))

private theorem m240 : g 240 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-847,1451,-1319")) (hv 10246 (by decide))
    (H.mul_mem (H.inv_mem (m847 H hv hs)) (H.mul_mem (m1451 H hv hs) (H.mul_mem (H.inv_mem (m1319 H hv hs)) H.one_mem)))

private theorem m1968 : g 1968 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "3,-449")) (hv 10248 (by decide))
    (H.mul_mem (m3 H hs) (H.mul_mem (H.inv_mem (m449 H hv hs)) H.one_mem))

private theorem m1870 : g 1870 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "755,122")) (hv 31048 (by decide))
    (H.mul_mem (m755 H hv hs) (H.mul_mem (m122 H hv hs) H.one_mem))

private theorem m1845 : g 1845 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "122,-735")) (hv 10254 (by decide))
    (H.mul_mem (m122 H hv hs) (H.mul_mem (H.inv_mem (m735 H hv hs)) H.one_mem))

private theorem m595 : g 595 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "898,-1087")) (hv 10268 (by decide))
    (H.mul_mem (m898 H hv hs) (H.mul_mem (H.inv_mem (m1087 H hv hs)) H.one_mem))

private theorem m349 : g 349 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-412,-1450")) (hv 10276 (by decide))
    (H.mul_mem (H.inv_mem (m412 H hv hs)) (H.mul_mem (H.inv_mem (m1450 H hv hs)) H.one_mem))

private theorem m294 : g 294 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "295,-359,-295")) (hv 10284 (by decide))
    (H.mul_mem (m295 H hv hs) (H.mul_mem (H.inv_mem (m359 H hv hs)) (H.mul_mem (H.inv_mem (m295 H hv hs)) H.one_mem)))

private theorem m2002 : g 2002 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1018,-1093")) (hv 10981 (by decide))
    (H.mul_mem (H.inv_mem (m1018 H hv hs)) (H.mul_mem (H.inv_mem (m1093 H hv hs)) H.one_mem))

private theorem m1022 : g 1022 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "462,-836")) (hv 10982 (by decide))
    (H.mul_mem (m462 H hv hs) (H.mul_mem (H.inv_mem (m836 H hv hs)) H.one_mem))

private theorem m1760 : g 1760 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-249,-688")) (hv 10983 (by decide))
    (H.mul_mem (H.inv_mem (m249 H hv hs)) (H.mul_mem (H.inv_mem (m688 H hs)) H.one_mem))

private theorem m427 : g 427 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-831,-1298")) (hv 10987 (by decide))
    (H.mul_mem (H.inv_mem (m831 H hv hs)) (H.mul_mem (H.inv_mem (m1298 H hv hs)) H.one_mem))

private theorem m469 : g 469 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-314,14")) (hv 10997 (by decide))
    (H.mul_mem (H.inv_mem (m314 H hv hs)) (H.mul_mem (m14 H hv hs) H.one_mem))

private theorem m201 : g 201 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "764,449")) (hv 11000 (by decide))
    (H.mul_mem (m764 H hv hs) (H.mul_mem (m449 H hv hs) H.one_mem))

private theorem m880 : g 880 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1258,-526")) (hv 11008 (by decide))
    (H.mul_mem (H.inv_mem (m1258 H hv hs)) (H.mul_mem (H.inv_mem (m526 H hv hs)) H.one_mem))

private theorem m1164 : g 1164 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-992,-1321")) (hv 31049 (by decide))
    (H.mul_mem (H.inv_mem (m992 H hv hs)) (H.mul_mem (H.inv_mem (m1321 H hv hs)) H.one_mem))

private theorem m820 : g 820 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1908,-588")) (hv 11061 (by decide))
    (H.mul_mem (H.inv_mem (m1908 H hv hs)) (H.mul_mem (H.inv_mem (m588 H hv hs)) H.one_mem))

private theorem m383 : g 383 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "37,957")) (hv 11070 (by decide))
    (H.mul_mem (m37 H hv hs) (H.mul_mem (m957 H hv hs) H.one_mem))

private theorem m496 : g 496 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-957,-1520,-255")) (hv 11072 (by decide))
    (H.mul_mem (H.inv_mem (m957 H hv hs)) (H.mul_mem (H.inv_mem (m1520 H hv hs)) (H.mul_mem (H.inv_mem (m255 H hv hs)) H.one_mem)))

private theorem m713 : g 713 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1273,-855")) (hv 11091 (by decide))
    (H.mul_mem (m1273 H hv hs) (H.mul_mem (H.inv_mem (m855 H hv hs)) H.one_mem))

private theorem m1144 : g 1144 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1030,-243,-268")) (hv 11107 (by decide))
    (H.mul_mem (H.inv_mem (m1030 H hv hs)) (H.mul_mem (H.inv_mem (m243 H hv hs)) (H.mul_mem (H.inv_mem (m268 H hv hs)) H.one_mem)))

private theorem m1137 : g 1137 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-514,1265")) (hv 11109 (by decide))
    (H.mul_mem (H.inv_mem (m514 H hv hs)) (H.mul_mem (m1265 H hv hs) H.one_mem))

private theorem m543 : g 543 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1298,-37")) (hv 11111 (by decide))
    (H.mul_mem (m1298 H hv hs) (H.mul_mem (H.inv_mem (m37 H hv hs)) H.one_mem))

private theorem m495 : g 495 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "494,1265,1703")) (hv 11113 (by decide))
    (H.mul_mem (m494 H hv hs) (H.mul_mem (m1265 H hv hs) (H.mul_mem (m1703 H hv hs) H.one_mem)))

private theorem m287 : g 287 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "2,1378,3")) (hv 11114 (by decide))
    (H.mul_mem (m2 H hs) (H.mul_mem (m1378 H hv hs) (H.mul_mem (m3 H hs) H.one_mem)))

private theorem m356 : g 356 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1,172,-12,-1785")) (hv 31050 (by decide))
    (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (m172 H hv hs) (H.mul_mem (H.inv_mem (m12 H hv hs)) (H.mul_mem (H.inv_mem (m1785 H hv hs)) H.one_mem))))

private theorem m1576 : g 1576 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-490,408,-1701")) (hv 11139 (by decide))
    (H.mul_mem (H.inv_mem (m490 H hv hs)) (H.mul_mem (m408 H hv hs) (H.mul_mem (H.inv_mem (m1701 H hv hs)) H.one_mem)))

private theorem m1442 : g 1442 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1869,-1972,827")) (hv 11140 (by decide))
    (H.mul_mem (H.inv_mem (m1869 H hv hs)) (H.mul_mem (H.inv_mem (m1972 H hs)) (H.mul_mem (m827 H hv hs) H.one_mem)))

private theorem m159 : g 159 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1574,1095,12")) (hv 11143 (by decide))
    (H.mul_mem (m1574 H hv hs) (H.mul_mem (m1095 H hv hs) (H.mul_mem (m12 H hv hs) H.one_mem)))

private theorem m223 : g 223 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "147,738")) (hv 11169 (by decide))
    (H.mul_mem (m147 H hv hs) (H.mul_mem (m738 H hv hs) H.one_mem))

private theorem m1653 : g 1653 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "415,-235,-1785")) (hv 11173 (by decide))
    (H.mul_mem (m415 H hv hs) (H.mul_mem (H.inv_mem (m235 H hs)) (H.mul_mem (H.inv_mem (m1785 H hv hs)) H.one_mem)))

private theorem m809 : g 809 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1273,-116,799")) (hv 11179 (by decide))
    (H.mul_mem (m1273 H hv hs) (H.mul_mem (H.inv_mem (m116 H hv hs)) (H.mul_mem (m799 H hv hs) H.one_mem)))

private theorem m357 : g 357 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-634,-216")) (hv 11184 (by decide))
    (H.mul_mem (H.inv_mem (m634 H hv hs)) (H.mul_mem (H.inv_mem (m216 H hv hs)) H.one_mem))

private theorem m203 : g 203 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "271,-625,769")) (hv 11188 (by decide))
    (H.mul_mem (m271 H hv hs) (H.mul_mem (H.inv_mem (m625 H hv hs)) (H.mul_mem (m769 H hv hs) H.one_mem)))

private theorem m2032 : g 2032 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1083,-1455")) (hv 11834 (by decide))
    (H.mul_mem (H.inv_mem (m1083 H hv hs)) (H.mul_mem (H.inv_mem (m1455 H hv hs)) H.one_mem))

private theorem m1708 : g 1708 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-271,1053,674")) (hv 11843 (by decide))
    (H.mul_mem (H.inv_mem (m271 H hv hs)) (H.mul_mem (m1053 H hv hs) (H.mul_mem (m674 H hv hs) H.one_mem)))

private theorem m226 : g 226 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1265,-524")) (hv 11853 (by decide))
    (H.mul_mem (H.inv_mem (m1265 H hv hs)) (H.mul_mem (H.inv_mem (m524 H hv hs)) H.one_mem))

private theorem m1739 : g 1739 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1177,1147,176")) (hv 11862 (by decide))
    (H.mul_mem (m1177 H hv hs) (H.mul_mem (m1147 H hv hs) (H.mul_mem (m176 H hv hs) H.one_mem)))

private theorem m87 : g 87 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "88,216,-313")) (hv 11867 (by decide))
    (H.mul_mem (m88 H hv hs) (H.mul_mem (m216 H hv hs) (H.mul_mem (H.inv_mem (m313 H hv hs)) H.one_mem)))

private theorem m425 : g 425 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-291,1030")) (hv 11868 (by decide))
    (H.mul_mem (H.inv_mem (m291 H hv hs)) (H.mul_mem (m1030 H hv hs) H.one_mem))

private theorem m173 : g 173 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "379,-1030")) (hv 11917 (by decide))
    (H.mul_mem (m379 H hv hs) (H.mul_mem (H.inv_mem (m1030 H hv hs)) H.one_mem))

private theorem m170 : g 170 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-77,408")) (hv 11918 (by decide))
    (H.mul_mem (H.inv_mem (m77 H hv hs)) (H.mul_mem (m408 H hv hs) H.one_mem))

private theorem m1673 : g 1673 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "459,243")) (hv 11948 (by decide))
    (H.mul_mem (m459 H hv hs) (H.mul_mem (m243 H hv hs) H.one_mem))

private theorem m430 : g 430 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1273,-185,1394")) (hv 11969 (by decide))
    (H.mul_mem (H.inv_mem (m1273 H hv hs)) (H.mul_mem (H.inv_mem (m185 H hv hs)) (H.mul_mem (m1394 H hv hs) H.one_mem)))

private theorem m24 : g 24 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "23,-827")) (hv 11994 (by decide))
    (H.mul_mem (m23 H hs) (H.mul_mem (H.inv_mem (m827 H hv hs)) H.one_mem))

private theorem m1929 : g 1929 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "630,-30,-630")) (hv 11996 (by decide))
    (H.mul_mem (m630 H hv hs) (H.mul_mem (H.inv_mem (m30 H hv hs)) (H.mul_mem (H.inv_mem (m630 H hv hs)) H.one_mem)))

private theorem m1724 : g 1724 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1,-649")) (hv 12034 (by decide))
    (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (H.inv_mem (m649 H hv hs)) H.one_mem))

private theorem m76 : g 76 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "10,-1424,1778,-979")) (hv 12050 (by decide))
    (H.mul_mem (m10 H hv hs) (H.mul_mem (H.inv_mem (m1424 H hv hs)) (H.mul_mem (m1778 H hv hs) (H.mul_mem (H.inv_mem (m979 H hv hs)) H.one_mem))))

private theorem m27 : g 27 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "216,-1166")) (hv 12708 (by decide))
    (H.mul_mem (m216 H hv hs) (H.mul_mem (H.inv_mem (m1166 H hv hs)) H.one_mem))

private theorem m1903 : g 1903 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "735,558")) (hv 12723 (by decide))
    (H.mul_mem (m735 H hv hs) (H.mul_mem (m558 H hv hs) H.one_mem))

private theorem m816 : g 816 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "526,-855")) (hv 12735 (by decide))
    (H.mul_mem (m526 H hv hs) (H.mul_mem (H.inv_mem (m855 H hv hs)) H.one_mem))

private theorem m62 : g 62 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1930,-122")) (hv 12742 (by decide))
    (H.mul_mem (H.inv_mem (m1930 H hv hs)) (H.mul_mem (H.inv_mem (m122 H hv hs)) H.one_mem))

private theorem m387 : g 387 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "408,1972,1")) (hv 12803 (by decide))
    (H.mul_mem (m408 H hv hs) (H.mul_mem (m1972 H hs) (H.mul_mem (m1 H hs) H.one_mem)))

private theorem m207 : g 207 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "729,-147")) (hv 12819 (by decide))
    (H.mul_mem (m729 H hv hs) (H.mul_mem (H.inv_mem (m147 H hv hs)) H.one_mem))

private theorem m1118 : g 1118 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1,359,715")) (hv 12825 (by decide))
    (H.mul_mem (m1 H hs) (H.mul_mem (m359 H hv hs) (H.mul_mem (m715 H hv hs) H.one_mem)))

private theorem m130 : g 130 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "131,-216,348")) (hv 12845 (by decide))
    (H.mul_mem (m131 H hv hs) (H.mul_mem (H.inv_mem (m216 H hv hs)) (H.mul_mem (m348 H hs) H.one_mem)))

private theorem m120 : g 120 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1030,291,-736,-376")) (hv 31051 (by decide))
    (H.mul_mem (H.inv_mem (m1030 H hv hs)) (H.mul_mem (m291 H hv hs) (H.mul_mem (H.inv_mem (m736 H hv hs)) (H.mul_mem (H.inv_mem (m376 H hv hs)) H.one_mem))))

private theorem m169 : g 169 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1662,-675")) (hv 12849 (by decide))
    (H.mul_mem (m1662 H hv hs) (H.mul_mem (H.inv_mem (m675 H hv hs)) H.one_mem))

private theorem m1100 : g 1100 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1,-644,1378")) (hv 12863 (by decide))
    (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (H.inv_mem (m644 H hv hs)) (H.mul_mem (m1378 H hv hs) H.one_mem)))

private theorem m2013 : g 2013 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-2,-1041,-514,-629")) (hv 12871 (by decide))
    (H.mul_mem (H.inv_mem (m2 H hs)) (H.mul_mem (H.inv_mem (m1041 H hs)) (H.mul_mem (H.inv_mem (m514 H hv hs)) (H.mul_mem (H.inv_mem (m629 H hv hs)) H.one_mem))))

private theorem m1012 : g 1012 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-688,-736,855,431")) (hv 12895 (by decide))
    (H.mul_mem (H.inv_mem (m688 H hs)) (H.mul_mem (H.inv_mem (m736 H hv hs)) (H.mul_mem (m855 H hv hs) (H.mul_mem (m431 H hv hs) H.one_mem))))

private theorem m606 : g 606 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-459,189,1772,701,-526")) (hv 31052 (by decide))
    (H.mul_mem (H.inv_mem (m459 H hv hs)) (H.mul_mem (m189 H hv hs) (H.mul_mem (m1772 H hs) (H.mul_mem (m701 H hv hs) (H.mul_mem (H.inv_mem (m526 H hv hs)) H.one_mem)))))

private theorem m561 : g 561 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "903,-712,19")) (hv 12915 (by decide))
    (H.mul_mem (m903 H hv hs) (H.mul_mem (H.inv_mem (m712 H hv hs)) (H.mul_mem (m19 H hv hs) H.one_mem)))

private theorem m90 : g 90 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "2037,798,-431")) (hv 12922 (by decide))
    (H.mul_mem (m2037 H hv hs) (H.mul_mem (m798 H hv hs) (H.mul_mem (H.inv_mem (m431 H hv hs)) H.one_mem)))

private theorem m1745 : g 1745 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1408,-831")) (hv 12924 (by decide))
    (H.mul_mem (m1408 H hv hs) (H.mul_mem (H.inv_mem (m831 H hv hs)) H.one_mem))

private theorem m611 : g 611 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "10,-1424,-1")) (hv 13659 (by decide))
    (H.mul_mem (m10 H hv hs) (H.mul_mem (H.inv_mem (m1424 H hv hs)) (H.mul_mem (H.inv_mem (m1 H hs)) H.one_mem)))

private theorem m11 : g 11 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-302,-581,-755")) (hv 13667 (by decide))
    (H.mul_mem (H.inv_mem (m302 H hv hs)) (H.mul_mem (H.inv_mem (m581 H hv hs)) (H.mul_mem (H.inv_mem (m755 H hv hs)) H.one_mem)))

private theorem m1005 : g 1005 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1030,-379,-863,36")) (hv 31053 (by decide))
    (H.mul_mem (m1030 H hv hs) (H.mul_mem (H.inv_mem (m379 H hv hs)) (H.mul_mem (H.inv_mem (m863 H hv hs)) (H.mul_mem (m36 H hv hs) H.one_mem))))

private theorem m239 : g 239 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1908,-189")) (hv 13704 (by decide))
    (H.mul_mem (m1908 H hv hs) (H.mul_mem (H.inv_mem (m189 H hv hs)) H.one_mem))

private theorem m948 : g 948 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-282,422,514,-1701,1,-172")) (hv 13714 (by decide))
    (H.mul_mem (H.inv_mem (m282 H hv hs)) (H.mul_mem (m422 H hs) (H.mul_mem (m514 H hv hs) (H.mul_mem (H.inv_mem (m1701 H hv hs)) (H.mul_mem (m1 H hs) (H.mul_mem (H.inv_mem (m172 H hv hs)) H.one_mem))))))

private theorem m968 : g 968 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "558,-1106,1420,-1778")) (hv 13720 (by decide))
    (H.mul_mem (m558 H hv hs) (H.mul_mem (H.inv_mem (m1106 H hs)) (H.mul_mem (m1420 H hv hs) (H.mul_mem (H.inv_mem (m1778 H hv hs)) H.one_mem))))

private theorem m878 : g 878 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-741,216,-1166,-741")) (hv 31054 (by decide))
    (H.mul_mem (H.inv_mem (m741 H hv hs)) (H.mul_mem (m216 H hv hs) (H.mul_mem (H.inv_mem (m1166 H hv hs)) (H.mul_mem (H.inv_mem (m741 H hv hs)) H.one_mem))))

private theorem m697 : g 697 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-558,-1649")) (hv 13722 (by decide))
    (H.mul_mem (H.inv_mem (m558 H hv hs)) (H.mul_mem (H.inv_mem (m1649 H hv hs)) H.one_mem))

private theorem m1757 : g 1757 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-630,-1208,-738")) (hv 13743 (by decide))
    (H.mul_mem (H.inv_mem (m630 H hv hs)) (H.mul_mem (H.inv_mem (m1208 H hv hs)) (H.mul_mem (H.inv_mem (m738 H hv hs)) H.one_mem)))

private theorem m1506 : g 1506 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1701,-84,522")) (hv 13745 (by decide))
    (H.mul_mem (H.inv_mem (m1701 H hv hs)) (H.mul_mem (H.inv_mem (m84 H hv hs)) (H.mul_mem (m522 H hv hs) H.one_mem)))

private theorem m1286 : g 1286 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "10,-1424,-148,-74")) (hv 13749 (by decide))
    (H.mul_mem (m10 H hv hs) (H.mul_mem (H.inv_mem (m1424 H hv hs)) (H.mul_mem (H.inv_mem (m148 H hv hs)) (H.mul_mem (H.inv_mem (m74 H hv hs)) H.one_mem))))

private theorem m1233 : g 1233 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "649,-1424,-1235")) (hv 13751 (by decide))
    (H.mul_mem (m649 H hv hs) (H.mul_mem (H.inv_mem (m1424 H hv hs)) (H.mul_mem (H.inv_mem (m1235 H hv hs)) H.one_mem)))

private theorem m683 : g 683 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-255,-195,-3")) (hv 13757 (by decide))
    (H.mul_mem (H.inv_mem (m255 H hv hs)) (H.mul_mem (H.inv_mem (m195 H hv hs)) (H.mul_mem (H.inv_mem (m3 H hs)) H.one_mem)))

private theorem m1899 : g 1899 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1772,1321,-1703")) (hv 13768 (by decide))
    (H.mul_mem (m1772 H hs) (H.mul_mem (m1321 H hv hs) (H.mul_mem (H.inv_mem (m1703 H hv hs)) H.one_mem)))

private theorem m950 : g 950 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-23,459,-869,-422")) (hv 13782 (by decide))
    (H.mul_mem (H.inv_mem (m23 H hs)) (H.mul_mem (m459 H hv hs) (H.mul_mem (H.inv_mem (m869 H hv hs)) (H.mul_mem (H.inv_mem (m422 H hs)) H.one_mem))))

private theorem m309 : g 309 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-449,-1451,1686")) (hv 13799 (by decide))
    (H.mul_mem (H.inv_mem (m449 H hv hs)) (H.mul_mem (H.inv_mem (m1451 H hv hs)) (H.mul_mem (m1686 H hv hs) H.one_mem)))

private theorem m858 : g 858 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1321,-1703,-689")) (hv 13802 (by decide))
    (H.mul_mem (m1321 H hv hs) (H.mul_mem (H.inv_mem (m1703 H hv hs)) (H.mul_mem (H.inv_mem (m689 H hv hs)) H.one_mem)))

private theorem m1924 : g 1924 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "629,-514,510,-208")) (hv 13824 (by decide))
    (H.mul_mem (m629 H hv hs) (H.mul_mem (H.inv_mem (m514 H hv hs)) (H.mul_mem (m510 H hv hs) (H.mul_mem (H.inv_mem (m208 H hv hs)) H.one_mem))))

private theorem m959 : g 959 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-77,-288,-1908")) (hv 13834 (by decide))
    (H.mul_mem (H.inv_mem (m77 H hv hs)) (H.mul_mem (H.inv_mem (m288 H hv hs)) (H.mul_mem (H.inv_mem (m1908 H hv hs)) H.one_mem)))

private theorem m256 : g 256 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-258,161,-1265")) (hv 13864 (by decide))
    (H.mul_mem (H.inv_mem (m258 H hv hs)) (H.mul_mem (m161 H hv hs) (H.mul_mem (H.inv_mem (m1265 H hv hs)) H.one_mem)))

private theorem m1108 : g 1108 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-801,1208,630,-634")) (hv 13919 (by decide))
    (H.mul_mem (H.inv_mem (m801 H hv hs)) (H.mul_mem (m1208 H hv hs) (H.mul_mem (m630 H hv hs) (H.mul_mem (H.inv_mem (m634 H hv hs)) H.one_mem))))

private theorem m1837 : g 1837 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1765,-799,1408,180,992")) (hv 31055 (by decide))
    (H.mul_mem (m1765 H hv hs) (H.mul_mem (H.inv_mem (m799 H hv hs)) (H.mul_mem (m1408 H hv hs) (H.mul_mem (m180 H hv hs) (H.mul_mem (m992 H hv hs) H.one_mem)))))

private theorem m919 : g 919 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1,-282,-587,-1,282")) (hv 13925 (by decide))
    (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (H.inv_mem (m282 H hv hs)) (H.mul_mem (H.inv_mem (m587 H hv hs)) (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (m282 H hv hs) H.one_mem)))))

private theorem m61 : g 61 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-2018,-189,1208,630")) (hv 14707 (by decide))
    (H.mul_mem (H.inv_mem (m2018 H hv hs)) (H.mul_mem (H.inv_mem (m189 H hv hs)) (H.mul_mem (m1208 H hv hs) (H.mul_mem (m630 H hv hs) H.one_mem))))

private theorem m1801 : g 1801 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1087,634")) (hv 14709 (by decide))
    (H.mul_mem (H.inv_mem (m1087 H hv hs)) (H.mul_mem (m634 H hv hs) H.one_mem))

private theorem m31 : g 31 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-30,313,-957")) (hv 14717 (by decide))
    (H.mul_mem (H.inv_mem (m30 H hv hs)) (H.mul_mem (m313 H hv hs) (H.mul_mem (H.inv_mem (m957 H hv hs)) H.one_mem)))

private theorem m2049 : g 2049 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1273,675,1450,237")) (hv 14726 (by decide))
    (H.mul_mem (H.inv_mem (m1273 H hv hs)) (H.mul_mem (m675 H hv hs) (H.mul_mem (m1450 H hv hs) (H.mul_mem (m237 H hv hs) H.one_mem))))

private theorem m652 : g 652 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-957,741,-906,514")) (hv 14727 (by decide))
    (H.mul_mem (H.inv_mem (m957 H hv hs)) (H.mul_mem (m741 H hv hs) (H.mul_mem (H.inv_mem (m906 H hs)) (H.mul_mem (m514 H hv hs) H.one_mem))))

private theorem m355 : g 355 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-736,688,273,-782")) (hv 14739 (by decide))
    (H.mul_mem (H.inv_mem (m736 H hv hs)) (H.mul_mem (m688 H hs) (H.mul_mem (m273 H hs) (H.mul_mem (H.inv_mem (m782 H hv hs)) H.one_mem))))

private theorem m65 : g 65 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-688,-480,-325,-1338")) (hv 14775 (by decide))
    (H.mul_mem (H.inv_mem (m688 H hs)) (H.mul_mem (H.inv_mem (m480 H hs)) (H.mul_mem (H.inv_mem (m325 H hv hs)) (H.mul_mem (H.inv_mem (m1338 H hv hs)) H.one_mem))))

private theorem m874 : g 874 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "250,-268,-1030")) (hv 14792 (by decide))
    (H.mul_mem (m250 H hv hs) (H.mul_mem (H.inv_mem (m268 H hv hs)) (H.mul_mem (H.inv_mem (m1030 H hv hs)) H.one_mem)))

private theorem m134 : g 134 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "255,745,645,1428,449")) (hv 14800 (by decide))
    (H.mul_mem (m255 H hv hs) (H.mul_mem (m745 H hv hs) (H.mul_mem (m645 H hv hs) (H.mul_mem (m1428 H hv hs) (H.mul_mem (m449 H hv hs) H.one_mem)))))

private theorem m910 : g 910 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-957,831,360,1203")) (hv 14811 (by decide))
    (H.mul_mem (H.inv_mem (m957 H hv hs)) (H.mul_mem (m831 H hv hs) (H.mul_mem (m360 H hv hs) (H.mul_mem (m1203 H hv hs) H.one_mem))))

private theorem m1114 : g 1114 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-216,274,-634,1087")) (hv 14895 (by decide))
    (H.mul_mem (H.inv_mem (m216 H hv hs)) (H.mul_mem (m274 H hv hs) (H.mul_mem (H.inv_mem (m634 H hv hs)) (H.mul_mem (m1087 H hv hs) H.one_mem))))

private theorem m1504 : g 1504 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-42,1824,645")) (hv 14942 (by decide))
    (H.mul_mem (H.inv_mem (m42 H hv hs)) (H.mul_mem (m1824 H hv hs) (H.mul_mem (m645 H hv hs) H.one_mem)))

private theorem m983 : g 983 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "863,764,855,-526,-3,-480")) (hv 14946 (by decide))
    (H.mul_mem (m863 H hv hs) (H.mul_mem (m764 H hv hs) (H.mul_mem (m855 H hv hs) (H.mul_mem (H.inv_mem (m526 H hv hs)) (H.mul_mem (H.inv_mem (m3 H hs)) (H.mul_mem (H.inv_mem (m480 H hs)) H.one_mem))))))

private theorem m530 : g 530 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1338,-1,1824,293,-533")) (hv 14954 (by decide))
    (H.mul_mem (H.inv_mem (m1338 H hv hs)) (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (m1824 H hv hs) (H.mul_mem (m293 H hv hs) (H.mul_mem (H.inv_mem (m533 H hv hs)) H.one_mem)))))

private theorem m622 : g 622 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "42,-928,-1208,-1,-197")) (hv 31056 (by decide))
    (H.mul_mem (m42 H hv hs) (H.mul_mem (H.inv_mem (m928 H hv hs)) (H.mul_mem (H.inv_mem (m1208 H hv hs)) (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (H.inv_mem (m197 H hv hs)) H.one_mem)))))

private theorem m424 : g 424 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1701,84,-107,1")) (hv 14999 (by decide))
    (H.mul_mem (H.inv_mem (m1701 H hv hs)) (H.mul_mem (m84 H hv hs) (H.mul_mem (H.inv_mem (m107 H hv hs)) (H.mul_mem (m1 H hs) H.one_mem))))

private theorem m1231 : g 1231 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-755,863,-36,-1206,-1405")) (hv 15030 (by decide))
    (H.mul_mem (H.inv_mem (m755 H hv hs)) (H.mul_mem (m863 H hv hs) (H.mul_mem (H.inv_mem (m36 H hv hs)) (H.mul_mem (H.inv_mem (m1206 H hv hs)) (H.mul_mem (H.inv_mem (m1405 H hv hs)) H.one_mem)))))

private theorem m1799 : g 1799 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "831,-736,688,524")) (hv 15031 (by decide))
    (H.mul_mem (m831 H hv hs) (H.mul_mem (H.inv_mem (m736 H hv hs)) (H.mul_mem (m688 H hs) (H.mul_mem (m524 H hv hs) H.one_mem))))

private theorem m609 : g 609 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "235,1428,-1,-1424,-688,735,-122,590")) (hv 15961 (by decide))
    (H.mul_mem (m235 H hs) (H.mul_mem (m1428 H hv hs) (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (H.inv_mem (m1424 H hv hs)) (H.mul_mem (H.inv_mem (m688 H hs)) (H.mul_mem (m735 H hv hs) (H.mul_mem (H.inv_mem (m122 H hv hs)) (H.mul_mem (m590 H hv hs) H.one_mem))))))))

private theorem m190 : g 190 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "798,-431,2,1972")) (hv 15975 (by decide))
    (H.mul_mem (m798 H hv hs) (H.mul_mem (H.inv_mem (m431 H hv hs)) (H.mul_mem (m2 H hs) (H.mul_mem (m1972 H hs) H.one_mem))))

private theorem m732 : g 732 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1686,449,-322,-255,863")) (hv 15996 (by decide))
    (H.mul_mem (H.inv_mem (m1686 H hv hs)) (H.mul_mem (m449 H hv hs) (H.mul_mem (H.inv_mem (m322 H hv hs)) (H.mul_mem (H.inv_mem (m255 H hv hs)) (H.mul_mem (m863 H hv hs) H.one_mem)))))

private theorem m1645 : g 1645 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "780,1772,1321,-675,688")) (hv 16024 (by decide))
    (H.mul_mem (m780 H hv hs) (H.mul_mem (m1772 H hs) (H.mul_mem (m1321 H hv hs) (H.mul_mem (H.inv_mem (m675 H hv hs)) (H.mul_mem (m688 H hs) H.one_mem)))))

private theorem m835 : g 835 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1030,359,-1115,-688,736,273")) (hv 16037 (by decide))
    (H.mul_mem (m1030 H hv hs) (H.mul_mem (m359 H hv hs) (H.mul_mem (H.inv_mem (m1115 H hs)) (H.mul_mem (H.inv_mem (m688 H hs)) (H.mul_mem (m736 H hv hs) (H.mul_mem (m273 H hs) H.one_mem))))))

private theorem m267 : g 267 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-10,-161,-107,712")) (hv 16072 (by decide))
    (H.mul_mem (H.inv_mem (m10 H hv hs)) (H.mul_mem (H.inv_mem (m161 H hv hs)) (H.mul_mem (H.inv_mem (m107 H hv hs)) (H.mul_mem (m712 H hv hs) H.one_mem))))

private theorem m1184 : g 1184 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "480,-738,675,-1662,-1451")) (hv 31057 (by decide))
    (H.mul_mem (m480 H hs) (H.mul_mem (H.inv_mem (m738 H hv hs)) (H.mul_mem (m675 H hv hs) (H.mul_mem (H.inv_mem (m1662 H hv hs)) (H.mul_mem (H.inv_mem (m1451 H hv hs)) H.one_mem)))))

private theorem m956 : g 956 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "780,890,1405,-558")) (hv 16090 (by decide))
    (H.mul_mem (m780 H hv hs) (H.mul_mem (m890 H hv hs) (H.mul_mem (m1405 H hv hs) (H.mul_mem (H.inv_mem (m558 H hv hs)) H.one_mem))))

private theorem m59 : g 59 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1208,-729,480,2018,258")) (hv 16205 (by decide))
    (H.mul_mem (m1208 H hv hs) (H.mul_mem (H.inv_mem (m729 H hv hs)) (H.mul_mem (m480 H hs) (H.mul_mem (m2018 H hv hs) (H.mul_mem (m258 H hv hs) H.one_mem)))))

private theorem m182 : g 182 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-10,-161,-533")) (hv 16269 (by decide))
    (H.mul_mem (H.inv_mem (m10 H hv hs)) (H.mul_mem (H.inv_mem (m161 H hv hs)) (H.mul_mem (H.inv_mem (m533 H hv hs)) H.one_mem)))

private theorem m1403 : g 1403 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "3,785,-1686,449")) (hv 16361 (by decide))
    (H.mul_mem (m3 H hs) (H.mul_mem (m785 H hv hs) (H.mul_mem (H.inv_mem (m1686 H hv hs)) (H.mul_mem (m449 H hv hs) H.one_mem))))

private theorem m1843 : g 1843 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-147,855,431,-3,-475")) (hv 16391 (by decide))
    (H.mul_mem (H.inv_mem (m147 H hv hs)) (H.mul_mem (m855 H hv hs) (H.mul_mem (m431 H hv hs) (H.mul_mem (H.inv_mem (m3 H hs)) (H.mul_mem (H.inv_mem (m475 H hv hs)) H.one_mem)))))

private theorem m1864 : g 1864 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-431,735,-398,906,37")) (hv 17597 (by decide))
    (H.mul_mem (H.inv_mem (m431 H hv hs)) (H.mul_mem (m735 H hv hs) (H.mul_mem (H.inv_mem (m398 H hv hs)) (H.mul_mem (m906 H hs) (H.mul_mem (m37 H hv hs) H.one_mem)))))

private theorem m1076 : g 1076 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1662,-1451,1115,-107,1030")) (hv 31058 (by decide))
    (H.mul_mem (H.inv_mem (m1662 H hv hs)) (H.mul_mem (H.inv_mem (m1451 H hv hs)) (H.mul_mem (m1115 H hs) (H.mul_mem (H.inv_mem (m107 H hv hs)) (H.mul_mem (m1030 H hv hs) H.one_mem)))))

private theorem m312 : g 312 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-77,-189,-738,-729,480")) (hv 17639 (by decide))
    (H.mul_mem (H.inv_mem (m77 H hv hs)) (H.mul_mem (H.inv_mem (m189 H hv hs)) (H.mul_mem (H.inv_mem (m738 H hv hs)) (H.mul_mem (H.inv_mem (m729 H hv hs)) (H.mul_mem (m480 H hs) H.one_mem)))))

private theorem m601 : g 601 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-581,-755,863,764,449,250,-1083,-890")) (hv 31059 (by decide))
    (H.mul_mem (H.inv_mem (m581 H hv hs)) (H.mul_mem (H.inv_mem (m755 H hv hs)) (H.mul_mem (m863 H hv hs) (H.mul_mem (m764 H hv hs) (H.mul_mem (m449 H hv hs) (H.mul_mem (m250 H hv hs) (H.mul_mem (H.inv_mem (m1083 H hv hs)) (H.mul_mem (H.inv_mem (m890 H hv hs)) H.one_mem))))))))

private theorem m1735 : g 1735 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "282,2,-12,480,-738,675")) (hv 17688 (by decide))
    (H.mul_mem (m282 H hv hs) (H.mul_mem (m2 H hs) (H.mul_mem (H.inv_mem (m12 H hv hs)) (H.mul_mem (m480 H hs) (H.mul_mem (H.inv_mem (m738 H hv hs)) (H.mul_mem (m675 H hv hs) H.one_mem))))))

private theorem m867 : g 867 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-459,23,227,-1018,-764")) (hv 17709 (by decide))
    (H.mul_mem (H.inv_mem (m459 H hv hs)) (H.mul_mem (m23 H hs) (H.mul_mem (m227 H hv hs) (H.mul_mem (H.inv_mem (m1018 H hv hs)) (H.mul_mem (H.inv_mem (m764 H hv hs)) H.one_mem)))))

private theorem m241 : g 241 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1083,449,780,1772")) (hv 17721 (by decide))
    (H.mul_mem (m1083 H hv hs) (H.mul_mem (m449 H hv hs) (H.mul_mem (m780 H hv hs) (H.mul_mem (m1772 H hs) H.one_mem))))

private theorem m125 : g 125 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1824,1168,77,-449,-1083")) (hv 17781 (by decide))
    (H.mul_mem (H.inv_mem (m1824 H hv hs)) (H.mul_mem (m1168 H hv hs) (H.mul_mem (m77 H hv hs) (H.mul_mem (H.inv_mem (m449 H hv hs)) (H.mul_mem (H.inv_mem (m1083 H hv hs)) H.one_mem)))))

private theorem m8 : g 8 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "735,558,284,-645")) (hv 17854 (by decide))
    (H.mul_mem (m735 H hv hs) (H.mul_mem (m558 H hv hs) (H.mul_mem (m284 H hv hs) (H.mul_mem (H.inv_mem (m645 H hv hs)) H.one_mem))))

private theorem m352 : g 352 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "180,-1321,-1772,-189")) (hv 18919 (by decide))
    (H.mul_mem (m180 H hv hs) (H.mul_mem (H.inv_mem (m1321 H hv hs)) (H.mul_mem (H.inv_mem (m1772 H hs)) (H.mul_mem (H.inv_mem (m189 H hv hs)) H.one_mem))))

private theorem m860 : g 860 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1,459,-729,-906,398,-735,-459")) (hv 18921 (by decide))
    (H.mul_mem (m1 H hs) (H.mul_mem (m459 H hv hs) (H.mul_mem (H.inv_mem (m729 H hv hs)) (H.mul_mem (H.inv_mem (m906 H hs)) (H.mul_mem (m398 H hv hs) (H.mul_mem (H.inv_mem (m735 H hv hs)) (H.mul_mem (H.inv_mem (m459 H hv hs)) H.one_mem)))))))

private theorem m748 : g 748 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-522,322,422,1450,-12,-1451,2018")) (hv 18923 (by decide))
    (H.mul_mem (H.inv_mem (m522 H hv hs)) (H.mul_mem (m322 H hv hs) (H.mul_mem (m422 H hs) (H.mul_mem (m1450 H hv hs) (H.mul_mem (H.inv_mem (m12 H hv hs)) (H.mul_mem (H.inv_mem (m1451 H hv hs)) (H.mul_mem (m2018 H hv hs) H.one_mem)))))))

private theorem m550 : g 550 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1258,243,-109,-250,-449,-1083")) (hv 18993 (by decide))
    (H.mul_mem (H.inv_mem (m1258 H hv hs)) (H.mul_mem (m243 H hv hs) (H.mul_mem (H.inv_mem (m109 H hv hs)) (H.mul_mem (H.inv_mem (m250 H hv hs)) (H.mul_mem (H.inv_mem (m449 H hv hs)) (H.mul_mem (H.inv_mem (m1083 H hv hs)) H.one_mem))))))

private theorem m1057 : g 1057 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1321,-675,1053,688,1772,-588")) (hv 19049 (by decide))
    (H.mul_mem (m1321 H hv hs) (H.mul_mem (H.inv_mem (m675 H hv hs)) (H.mul_mem (m1053 H hv hs) (H.mul_mem (m688 H hs) (H.mul_mem (m1772 H hs) (H.mul_mem (H.inv_mem (m588 H hv hs)) H.one_mem))))))

private theorem m1621 : g 1621 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "558,-348,1053,688")) (hv 19159 (by decide))
    (H.mul_mem (m558 H hv hs) (H.mul_mem (H.inv_mem (m348 H hs)) (H.mul_mem (m1053 H hv hs) (H.mul_mem (m688 H hs) H.one_mem))))

private theorem m1157 : g 1157 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-8")) (hv 4616 (by decide))
    (H.mul_mem (H.inv_mem (m8 H hv hs)) H.one_mem)

private theorem m389 : g 389 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-387")) (hv 5567 (by decide))
    (H.mul_mem (H.inv_mem (m387 H hv hs)) H.one_mem)

private theorem m1292 : g 1292 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-24")) (hv 4746 (by decide))
    (H.mul_mem (H.inv_mem (m24 H hv hs)) H.one_mem)

private theorem m1835 : g 1835 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-31")) (hv 5392 (by decide))
    (H.mul_mem (H.inv_mem (m31 H hv hs)) H.one_mem)

private theorem m1630 : g 1630 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-59")) (hv 5312 (by decide))
    (H.mul_mem (H.inv_mem (m59 H hv hs)) H.one_mem)

private theorem m986 : g 986 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-62")) (hv 4874 (by decide))
    (H.mul_mem (H.inv_mem (m62 H hv hs)) H.one_mem)

private theorem m402 : g 402 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-87")) (hv 5268 (by decide))
    (H.mul_mem (H.inv_mem (m87 H hv hs)) H.one_mem)

private theorem m2048 : g 2048 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-90")) (hv 5569 (by decide))
    (H.mul_mem (H.inv_mem (m90 H hv hs)) H.one_mem)

private theorem m1961 : g 1961 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-858")) (hv 5486 (by decide))
    (H.mul_mem (H.inv_mem (m858 H hv hs)) H.one_mem)

private theorem m1991 : g 1991 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1899")) (hv 5304 (by decide))
    (H.mul_mem (H.inv_mem (m1899 H hv hs)) H.one_mem)

private theorem m1470 : g 1470 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-120")) (hv 5506 (by decide))
    (H.mul_mem (H.inv_mem (m120 H hv hs)) H.one_mem)

private theorem m1109 : g 1109 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-125")) (hv 4614 (by decide))
    (H.mul_mem (H.inv_mem (m125 H hv hs)) H.one_mem)

private theorem m1896 : g 1896 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1735")) (hv 5010 (by decide))
    (H.mul_mem (H.inv_mem (m1735 H hv hs)) H.one_mem)

private theorem m773 : g 773 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-130")) (hv 5113 (by decide))
    (H.mul_mem (H.inv_mem (m130 H hv hs)) H.one_mem)

private theorem m421 : g 421 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-169")) (hv 5196 (by decide))
    (H.mul_mem (H.inv_mem (m169 H hv hs)) H.one_mem)

private theorem m194 : g 194 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-170")) (hv 5198 (by decide))
    (H.mul_mem (H.inv_mem (m170 H hv hs)) H.one_mem)

private theorem m217 : g 217 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-173")) (hv 5066 (by decide))
    (H.mul_mem (H.inv_mem (m173 H hv hs)) H.one_mem)

private theorem m1679 : g 1679 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-867")) (hv 5690 (by decide))
    (H.mul_mem (H.inv_mem (m867 H hv hs)) H.one_mem)

private theorem m922 : g 922 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-182")) (hv 4925 (by decide))
    (H.mul_mem (H.inv_mem (m182 H hv hs)) H.one_mem)

private theorem m1790 : g 1790 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-190")) (hv 5715 (by decide))
    (H.mul_mem (H.inv_mem (m190 H hv hs)) H.one_mem)

private theorem m565 : g 565 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-201")) (hv 5025 (by decide))
    (H.mul_mem (H.inv_mem (m201 H hv hs)) H.one_mem)

private theorem m753 : g 753 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-203")) (hv 5224 (by decide))
    (H.mul_mem (H.inv_mem (m203 H hv hs)) H.one_mem)

private theorem m366 : g 366 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-241")) (hv 5336 (by decide))
    (H.mul_mem (H.inv_mem (m241 H hv hs)) H.one_mem)

private theorem m1787 : g 1787 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-223")) (hv 5267 (by decide))
    (H.mul_mem (H.inv_mem (m223 H hv hs)) H.one_mem)

private theorem m544 : g 544 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-239")) (hv 5485 (by decide))
    (H.mul_mem (H.inv_mem (m239 H hv hs)) H.one_mem)

private theorem m1323 : g 1323 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-240")) (hv 5677 (by decide))
    (H.mul_mem (H.inv_mem (m240 H hv hs)) H.one_mem)

private theorem m1024 : g 1024 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-256")) (hv 5355 (by decide))
    (H.mul_mem (H.inv_mem (m256 H hv hs)) H.one_mem)

private theorem m894 : g 894 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-267")) (hv 5140 (by decide))
    (H.mul_mem (H.inv_mem (m267 H hv hs)) H.one_mem)

private theorem m703 : g 703 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-309")) (hv 5418 (by decide))
    (H.mul_mem (H.inv_mem (m309 H hv hs)) H.one_mem)

private theorem m901 : g 901 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-530")) (hv 5157 (by decide))
    (H.mul_mem (H.inv_mem (m530 H hv hs)) H.one_mem)

private theorem m1676 : g 1676 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-312")) (hv 5424 (by decide))
    (H.mul_mem (H.inv_mem (m312 H hv hs)) H.one_mem)

private theorem m2045 : g 2045 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-349")) (hv 31060 (by decide))
    (H.mul_mem (H.inv_mem (m349 H hv hs)) H.one_mem)

private theorem m1999 : g 1999 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-352")) (hv 5430 (by decide))
    (H.mul_mem (H.inv_mem (m352 H hv hs)) H.one_mem)

private theorem m1702 : g 1702 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-355")) (hv 4805 (by decide))
    (H.mul_mem (H.inv_mem (m355 H hv hs)) H.one_mem)

private theorem m686 : g 686 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-357")) (hv 5462 (by decide))
    (H.mul_mem (H.inv_mem (m357 H hv hs)) H.one_mem)

private theorem m823 : g 823 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-365")) (hv 5335 (by decide))
    (H.mul_mem (H.inv_mem (m365 H hv hs)) H.one_mem)

private theorem m1905 : g 1905 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1621")) (hv 5448 (by decide))
    (H.mul_mem (H.inv_mem (m1621 H hv hs)) H.one_mem)

private theorem m406 : g 406 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-383")) (hv 5792 (by decide))
    (H.mul_mem (H.inv_mem (m383 H hv hs)) H.one_mem)

private theorem m772 : g 772 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-543")) (hv 5483 (by decide))
    (H.mul_mem (H.inv_mem (m543 H hv hs)) H.one_mem)

private theorem m1010 : g 1010 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-425")) (hv 5210 (by decide))
    (H.mul_mem (H.inv_mem (m425 H hv hs)) H.one_mem)

private theorem m993 : g 993 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-430")) (hv 5351 (by decide))
    (H.mul_mem (H.inv_mem (m430 H hv hs)) H.one_mem)

private theorem m1711 : g 1711 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1578")) (hv 5354 (by decide))
    (H.mul_mem (H.inv_mem (m1578 H hv hs)) H.one_mem)

private theorem m1274 : g 1274 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-713")) (hv 5240 (by decide))
    (H.mul_mem (H.inv_mem (m713 H hv hs)) H.one_mem)

private theorem m865 : g 865 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-496")) (hv 4933 (by decide))
    (H.mul_mem (H.inv_mem (m496 H hv hs)) H.one_mem)

private theorem m1341 : g 1341 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-561")) (hv 5217 (by decide))
    (H.mul_mem (H.inv_mem (m561 H hv hs)) H.one_mem)

private theorem m1399 : g 1399 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-609")) (hv 4924 (by decide))
    (H.mul_mem (H.inv_mem (m609 H hv hs)) H.one_mem)

private theorem m610 : g 610 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-606")) (hv 5741 (by decide))
    (H.mul_mem (H.inv_mem (m606 H hv hs)) H.one_mem)

private theorem m1255 : g 1255 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-611")) (hv 4829 (by decide))
    (H.mul_mem (H.inv_mem (m611 H hv hs)) H.one_mem)

private theorem m1249 : g 1249 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-622")) (hv 5554 (by decide))
    (H.mul_mem (H.inv_mem (m622 H hv hs)) H.one_mem)

private theorem m1478 : g 1478 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-697")) (hv 5634 (by decide))
    (H.mul_mem (H.inv_mem (m697 H hv hs)) H.one_mem)

private theorem m1935 : g 1935 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-748")) (hv 5586 (by decide))
    (H.mul_mem (H.inv_mem (m748 H hv hs)) H.one_mem)

private theorem m996 : g 996 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-820")) (hv 5293 (by decide))
    (H.mul_mem (H.inv_mem (m820 H hv hs)) H.one_mem)

private theorem m1793 : g 1793 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-860")) (hv 31061 (by decide))
    (H.mul_mem (H.inv_mem (m860 H hv hs)) H.one_mem)

private theorem m1267 : g 1267 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-874")) (hv 4612 (by decide))
    (H.mul_mem (H.inv_mem (m874 H hv hs)) H.one_mem)

private theorem m1867 : g 1867 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-910")) (hv 5601 (by decide))
    (H.mul_mem (H.inv_mem (m910 H hv hs)) H.one_mem)

private theorem m2057 : g 2057 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-916")) (hv 5817 (by decide))
    (H.mul_mem (H.inv_mem (m916 H hv hs)) H.one_mem)

private theorem m1134 : g 1134 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-919")) (hv 4974 (by decide))
    (H.mul_mem (H.inv_mem (m919 H hv hs)) H.one_mem)

private theorem m1381 : g 1381 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-948")) (hv 5704 (by decide))
    (H.mul_mem (H.inv_mem (m948 H hv hs)) H.one_mem)

private theorem m1913 : g 1913 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-956")) (hv 5422 (by decide))
    (H.mul_mem (H.inv_mem (m956 H hv hs)) H.one_mem)

private theorem m2047 : g 2047 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1114")) (hv 31062 (by decide))
    (H.mul_mem (H.inv_mem (m1114 H hv hs)) H.one_mem)

private theorem m1650 : g 1650 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1403")) (hv 5390 (by decide))
    (H.mul_mem (H.inv_mem (m1403 H hv hs)) H.one_mem)

private theorem m1830 : g 1830 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1506")) (hv 31063 (by decide))
    (H.mul_mem (H.inv_mem (m1506 H hv hs)) H.one_mem)

private theorem m1700 : g 1700 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1576")) (hv 5488 (by decide))
    (H.mul_mem (H.inv_mem (m1576 H hv hs)) H.one_mem)

private theorem m1749 : g 1749 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1745")) (hv 5836 (by decide))
    (H.mul_mem (H.inv_mem (m1745 H hv hs)) H.one_mem)

private theorem m1851 : g 1851 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1799")) (hv 5155 (by decide))
    (H.mul_mem (H.inv_mem (m1799 H hv hs)) H.one_mem)

private theorem m1818 : g 1818 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1801")) (hv 31064 (by decide))
    (H.mul_mem (H.inv_mem (m1801 H hv hs)) H.one_mem)

private theorem m875 : g 875 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "874")) (hv 7627 (by decide))
    (H.mul_mem (m874 H hv hs) H.one_mem)

private theorem m1388 : g 1388 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "550")) (hv 7610 (by decide))
    (H.mul_mem (m550 H hv hs) H.one_mem)

private theorem m1440 : g 1440 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-867")) (hv 7599 (by decide))
    (H.mul_mem (H.inv_mem (m867 H hv hs)) H.one_mem)

private theorem m808 : g 808 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-713")) (hv 7573 (by decide))
    (H.mul_mem (H.inv_mem (m713 H hv hs)) H.one_mem)

private theorem m468 : g 468 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "182")) (hv 8482 (by decide))
    (H.mul_mem (m182 H hv hs) H.one_mem)

private theorem m380 : g 380 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-853,-170,182")) (hv 10073 (by decide))
    (H.mul_mem (H.inv_mem (m853 H hv hs)) (H.mul_mem (H.inv_mem (m170 H hv hs)) (H.mul_mem (m182 H hv hs) H.one_mem)))

private theorem m723 : g 723 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-979,-76")) (hv 10089 (by decide))
    (H.mul_mem (H.inv_mem (m979 H hv hs)) (H.mul_mem (H.inv_mem (m76 H hv hs)) H.one_mem))

private theorem m828 : g 828 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-436,530")) (hv 10097 (by decide))
    (H.mul_mem (H.inv_mem (m436 H hv hs)) (H.mul_mem (m530 H hv hs) H.one_mem))

private theorem m2028 : g 2028 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-601,-581")) (hv 10127 (by decide))
    (H.mul_mem (H.inv_mem (m601 H hv hs)) (H.mul_mem (H.inv_mem (m581 H hv hs)) H.one_mem))

private theorem m1237 : g 1237 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1286,-843")) (hv 10139 (by decide))
    (H.mul_mem (H.inv_mem (m1286 H hv hs)) (H.mul_mem (H.inv_mem (m843 H hv hs)) H.one_mem))

private theorem m994 : g 994 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-430,-90")) (hv 10140 (by decide))
    (H.mul_mem (H.inv_mem (m430 H hv hs)) (H.mul_mem (H.inv_mem (m90 H hv hs)) H.one_mem))

private theorem m793 : g 793 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "11,-933")) (hv 31065 (by decide))
    (H.mul_mem (m11 H hv hs) (H.mul_mem (H.inv_mem (m933 H hv hs)) H.one_mem))

private theorem m115 : g 115 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "799,-697")) (hv 10154 (by decide))
    (H.mul_mem (m799 H hv hs) (H.mul_mem (H.inv_mem (m697 H hv hs)) H.one_mem))

private theorem m1868 : g 1868 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-910,816")) (hv 10156 (by decide))
    (H.mul_mem (H.inv_mem (m910 H hv hs)) (H.mul_mem (m816 H hv hs) H.one_mem))

private theorem m1222 : g 1222 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "959,-692")) (hv 10164 (by decide))
    (H.mul_mem (m959 H hv hs) (H.mul_mem (H.inv_mem (m692 H hv hs)) H.one_mem))

private theorem m262 : g 262 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "169,688")) (hv 10221 (by decide))
    (H.mul_mem (m169 H hv hs) (H.mul_mem (m688 H hs) H.one_mem))

private theorem m673 : g 673 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1168,-697,-1405")) (hv 10239 (by decide))
    (H.mul_mem (H.inv_mem (m1168 H hv hs)) (H.mul_mem (H.inv_mem (m697 H hv hs)) (H.mul_mem (H.inv_mem (m1405 H hv hs)) H.one_mem)))

private theorem m1933 : g 1933 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "867,-1662")) (hv 10251 (by decide))
    (H.mul_mem (m867 H hv hs) (H.mul_mem (H.inv_mem (m1662 H hv hs)) H.one_mem))

private theorem m1575 : g 1575 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1574,125")) (hv 10262 (by decide))
    (H.mul_mem (m1574 H hv hs) (H.mul_mem (m125 H hv hs) H.one_mem))

private theorem m482 : g 482 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1724,-803")) (hv 10273 (by decide))
    (H.mul_mem (m1724 H hv hs) (H.mul_mem (H.inv_mem (m803 H hv hs)) H.one_mem))

private theorem m643 : g 643 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "644,1100,-1378")) (hv 10281 (by decide))
    (H.mul_mem (m644 H hv hs) (H.mul_mem (m1100 H hv hs) (H.mul_mem (H.inv_mem (m1378 H hv hs)) H.one_mem)))

private theorem m1582 : g 1582 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "125,-1455")) (hv 10980 (by decide))
    (H.mul_mem (m125 H hv hs) (H.mul_mem (H.inv_mem (m1455 H hv hs)) H.one_mem))

private theorem m788 : g 788 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-860,-1")) (hv 10993 (by decide))
    (H.mul_mem (H.inv_mem (m860 H hv hs)) (H.mul_mem (H.inv_mem (m1 H hs)) H.one_mem))

private theorem m711 : g 711 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "8,-1")) (hv 11021 (by decide))
    (H.mul_mem (m8 H hv hs) (H.mul_mem (H.inv_mem (m1 H hs)) H.one_mem))

private theorem m386 : g 386 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1311,-841,-387")) (hv 31066 (by decide))
    (H.mul_mem (m1311 H hv hs) (H.mul_mem (H.inv_mem (m841 H hv hs)) (H.mul_mem (H.inv_mem (m387 H hv hs)) H.one_mem)))

private theorem m2029 : g 2029 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-755,-11")) (hv 11047 (by decide))
    (H.mul_mem (H.inv_mem (m755 H hv hs)) (H.mul_mem (H.inv_mem (m11 H hv hs)) H.one_mem))

private theorem m1946 : g 1946 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1392,-816")) (hv 11050 (by decide))
    (H.mul_mem (H.inv_mem (m1392 H hv hs)) (H.mul_mem (H.inv_mem (m816 H hv hs)) H.one_mem))

private theorem m536 : g 536 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-835,-246,-1233")) (hv 31067 (by decide))
    (H.mul_mem (H.inv_mem (m835 H hv hs)) (H.mul_mem (H.inv_mem (m246 H hv hs)) (H.mul_mem (H.inv_mem (m1233 H hv hs)) H.one_mem)))

private theorem m1436 : g 1436 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1757,-61")) (hv 11088 (by decide))
    (H.mul_mem (H.inv_mem (m1757 H hv hs)) (H.mul_mem (H.inv_mem (m61 H hv hs)) H.one_mem))

private theorem m1569 : g 1569 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-550,-379")) (hv 11101 (by decide))
    (H.mul_mem (H.inv_mem (m550 H hv hs)) (H.mul_mem (H.inv_mem (m379 H hv hs)) H.one_mem))

private theorem m1472 : g 1472 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "182,1958")) (hv 11102 (by decide))
    (H.mul_mem (m182 H hv hs) (H.mul_mem (m1958 H hs) H.one_mem))

private theorem m1125 : g 1125 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1506,-510,-313")) (hv 31068 (by decide))
    (H.mul_mem (H.inv_mem (m1506 H hv hs)) (H.mul_mem (H.inv_mem (m510 H hv hs)) (H.mul_mem (H.inv_mem (m313 H hv hs)) H.one_mem)))

private theorem m200 : g 200 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-645,-8")) (hv 11118 (by decide))
    (H.mul_mem (H.inv_mem (m645 H hv hs)) (H.mul_mem (H.inv_mem (m8 H hv hs)) H.one_mem))

private theorem m121 : g 121 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1899,216")) (hv 11120 (by decide))
    (H.mul_mem (H.inv_mem (m1899 H hv hs)) (H.mul_mem (m216 H hv hs) H.one_mem))

private theorem m68 : g 68 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "182,1686")) (hv 11129 (by decide))
    (H.mul_mem (m182 H hv hs) (H.mul_mem (m1686 H hv hs) H.one_mem))

private theorem m943 : g 943 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-685,-950")) (hv 11153 (by decide))
    (H.mul_mem (H.inv_mem (m685 H hv hs)) (H.mul_mem (H.inv_mem (m950 H hv hs)) H.one_mem))

private theorem m6 : g 6 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1506,906")) (hv 11217 (by decide))
    (H.mul_mem (m1506 H hv hs) (H.mul_mem (m906 H hs) H.one_mem))

private theorem m410 : g 410 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "950,-782,1772,701")) (hv 11848 (by decide))
    (H.mul_mem (m950 H hv hs) (H.mul_mem (H.inv_mem (m782 H hv hs)) (H.mul_mem (m1772 H hs) (H.mul_mem (m701 H hv hs) H.one_mem))))

private theorem m1945 : g 1945 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1,-214,-84,-190")) (hv 11871 (by decide))
    (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (H.inv_mem (m214 H hv hs)) (H.mul_mem (H.inv_mem (m84 H hv hs)) (H.mul_mem (H.inv_mem (m190 H hv hs)) H.one_mem))))

private theorem m89 : g 89 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "8,-1824")) (hv 31069 (by decide))
    (H.mul_mem (m8 H hv hs) (H.mul_mem (H.inv_mem (m1824 H hv hs)) H.one_mem))

private theorem m728 : g 728 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "77,182,3")) (hv 11901 (by decide))
    (H.mul_mem (m77 H hv hs) (H.mul_mem (m182 H hv hs) (H.mul_mem (m3 H hs) H.one_mem)))

private theorem m1780 : g 1780 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1864,-431,-869")) (hv 11906 (by decide))
    (H.mul_mem (H.inv_mem (m1864 H hv hs)) (H.mul_mem (H.inv_mem (m431 H hv hs)) (H.mul_mem (H.inv_mem (m869 H hv hs)) H.one_mem)))

private theorem m1135 : g 1135 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-919,494,1265")) (hv 11929 (by decide))
    (H.mul_mem (H.inv_mem (m919 H hv hs)) (H.mul_mem (m494 H hv hs) (H.mul_mem (m1265 H hv hs) H.one_mem)))

private theorem m1543 : g 1543 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-208,-104,-1403")) (hv 11949 (by decide))
    (H.mul_mem (H.inv_mem (m208 H hv hs)) (H.mul_mem (H.inv_mem (m104 H hv hs)) (H.mul_mem (H.inv_mem (m1403 H hv hs)) H.one_mem)))

private theorem m1283 : g 1283 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1076,1210")) (hv 11960 (by decide))
    (H.mul_mem (m1076 H hv hs) (H.mul_mem (m1210 H hv hs) H.one_mem))

private theorem m762 : g 762 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-701,-1772,1899")) (hv 11965 (by decide))
    (H.mul_mem (H.inv_mem (m701 H hv hs)) (H.mul_mem (H.inv_mem (m1772 H hs)) (H.mul_mem (m1899 H hv hs) H.one_mem)))

private theorem m598 : g 598 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "355,-189,798")) (hv 11966 (by decide))
    (H.mul_mem (m355 H hv hs) (H.mul_mem (H.inv_mem (m189 H hv hs)) (H.mul_mem (m798 H hv hs) H.one_mem)))

private theorem m1447 : g 1447 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "874,291,-736")) (hv 12018 (by decide))
    (H.mul_mem (m874 H hv hs) (H.mul_mem (m291 H hv hs) (H.mul_mem (H.inv_mem (m736 H hv hs)) H.one_mem)))

private theorem m229 : g 229 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "59,-258,-59")) (hv 31070 (by decide))
    (H.mul_mem (m59 H hv hs) (H.mul_mem (H.inv_mem (m258 H hv hs)) (H.mul_mem (H.inv_mem (m59 H hv hs)) H.one_mem)))

private theorem m976 : g 976 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "530,1620,-84,-530")) (hv 12041 (by decide))
    (H.mul_mem (m530 H hv hs) (H.mul_mem (m1620 H hv hs) (H.mul_mem (H.inv_mem (m84 H hv hs)) (H.mul_mem (H.inv_mem (m530 H hv hs)) H.one_mem))))

private theorem m737 : g 737 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-801,398,801,-1108")) (hv 12045 (by decide))
    (H.mul_mem (H.inv_mem (m801 H hv hs)) (H.mul_mem (m398 H hv hs) (H.mul_mem (m801 H hv hs) (H.mul_mem (H.inv_mem (m1108 H hv hs)) H.one_mem))))

private theorem m977 : g 977 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-2049,1258,-1030")) (hv 12669 (by decide))
    (H.mul_mem (H.inv_mem (m2049 H hv hs)) (H.mul_mem (m1258 H hv hs) (H.mul_mem (H.inv_mem (m1030 H hv hs)) H.one_mem)))

private theorem m1698 : g 1698 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1076,-1258,-526")) (hv 12689 (by decide))
    (H.mul_mem (H.inv_mem (m1076 H hv hs)) (H.mul_mem (H.inv_mem (m1258 H hv hs)) (H.mul_mem (H.inv_mem (m526 H hv hs)) H.one_mem)))

private theorem m504 : g 504 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "732,-863,255")) (hv 12717 (by decide))
    (H.mul_mem (m732 H hv hs) (H.mul_mem (H.inv_mem (m863 H hv hs)) (H.mul_mem (m255 H hv hs) H.one_mem)))

private theorem m1941 : g 1941 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-77,-42,622,-1208")) (hv 12722 (by decide))
    (H.mul_mem (H.inv_mem (m77 H hv hs)) (H.mul_mem (H.inv_mem (m42 H hv hs)) (H.mul_mem (m622 H hv hs) (H.mul_mem (H.inv_mem (m1208 H hv hs)) H.one_mem))))

private theorem m1507 : g 1507 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-309,-449,1686")) (hv 12729 (by decide))
    (H.mul_mem (H.inv_mem (m309 H hv hs)) (H.mul_mem (H.inv_mem (m449 H hv hs)) (H.mul_mem (m1686 H hv hs) H.one_mem)))

private theorem m531 : g 531 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "798,981,-312")) (hv 12732 (by decide))
    (H.mul_mem (m798 H hv hs) (H.mul_mem (m981 H hv hs) (H.mul_mem (H.inv_mem (m312 H hv hs)) H.one_mem)))

private theorem m320 : g 320 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1924,208,-172")) (hv 12753 (by decide))
    (H.mul_mem (m1924 H hv hs) (H.mul_mem (m208 H hv hs) (H.mul_mem (H.inv_mem (m172 H hv hs)) H.one_mem)))

private theorem m2058 : g 2058 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-424,-232,-1213")) (hv 12768 (by decide))
    (H.mul_mem (H.inv_mem (m424 H hv hs)) (H.mul_mem (H.inv_mem (m232 H hv hs)) (H.mul_mem (H.inv_mem (m1213 H hv hs)) H.one_mem)))

private theorem m438 : g 438 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1703,-798,-1233")) (hv 12780 (by decide))
    (H.mul_mem (H.inv_mem (m1703 H hv hs)) (H.mul_mem (H.inv_mem (m798 H hv hs)) (H.mul_mem (H.inv_mem (m1233 H hv hs)) H.one_mem)))

private theorem m1332 : g 1332 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-8,736")) (hv 12783 (by decide))
    (H.mul_mem (H.inv_mem (m8 H hv hs)) (H.mul_mem (m736 H hv hs) H.one_mem))

private theorem m215 : g 215 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1735,-1662")) (hv 12788 (by decide))
    (H.mul_mem (m1735 H hv hs) (H.mul_mem (H.inv_mem (m1662 H hv hs)) H.one_mem))

private theorem m162 : g 162 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "530,533,-293,1338")) (hv 12791 (by decide))
    (H.mul_mem (m530 H hv hs) (H.mul_mem (m533 H hv hs) (H.mul_mem (H.inv_mem (m293 H hv hs)) (H.mul_mem (m1338 H hv hs) H.one_mem))))

private theorem m369 : g 369 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1265,1114,-634")) (hv 12808 (by decide))
    (H.mul_mem (H.inv_mem (m1265 H hv hs)) (H.mul_mem (m1114 H hv hs) (H.mul_mem (H.inv_mem (m634 H hv hs)) H.one_mem)))

private theorem m765 : g 765 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "588,-241,-312")) (hv 12829 (by decide))
    (H.mul_mem (m588 H hv hs) (H.mul_mem (H.inv_mem (m241 H hv hs)) (H.mul_mem (H.inv_mem (m312 H hv hs)) H.one_mem)))

private theorem m498 : g 498 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-274,-683,522")) (hv 12830 (by decide))
    (H.mul_mem (H.inv_mem (m274 H hv hs)) (H.mul_mem (H.inv_mem (m683 H hv hs)) (H.mul_mem (m522 H hv hs) H.one_mem)))

private theorem m1775 : g 1775 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-273,355,782")) (hv 12854 (by decide))
    (H.mul_mem (H.inv_mem (m273 H hs)) (H.mul_mem (m355 H hv hs) (H.mul_mem (m782 H hv hs) H.one_mem)))

private theorem m1348 : g 1348 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1184,1451,1018")) (hv 12862 (by decide))
    (H.mul_mem (m1184 H hv hs) (H.mul_mem (m1451 H hv hs) (H.mul_mem (m1018 H hv hs) H.one_mem)))

private theorem m1148 : g 1148 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1321,1057,1645,-968")) (hv 12876 (by decide))
    (H.mul_mem (H.inv_mem (m1321 H hv hs)) (H.mul_mem (m1057 H hv hs) (H.mul_mem (m1645 H hv hs) (H.mul_mem (H.inv_mem (m968 H hv hs)) H.one_mem))))

private theorem m358 : g 358 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-959,-10,-629,-412")) (hv 12900 (by decide))
    (H.mul_mem (H.inv_mem (m959 H hv hs)) (H.mul_mem (H.inv_mem (m10 H hv hs)) (H.mul_mem (H.inv_mem (m629 H hv hs)) (H.mul_mem (H.inv_mem (m412 H hv hs)) H.one_mem))))

private theorem m311 : g 311 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "109,-243,352,-1816")) (hv 12930 (by decide))
    (H.mul_mem (m109 H hv hs) (H.mul_mem (H.inv_mem (m243 H hv hs)) (H.mul_mem (m352 H hv hs) (H.mul_mem (H.inv_mem (m1816 H hv hs)) H.one_mem))))

private theorem m73 : g 73 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-309,-77,-928")) (hv 13636 (by decide))
    (H.mul_mem (H.inv_mem (m309 H hv hs)) (H.mul_mem (H.inv_mem (m77 H hv hs)) (H.mul_mem (H.inv_mem (m928 H hv hs)) H.one_mem)))

private theorem m1228 : g 1228 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "119,-712,1662,-1735")) (hv 13637 (by decide))
    (H.mul_mem (m119 H hv hs) (H.mul_mem (H.inv_mem (m712 H hv hs)) (H.mul_mem (m1662 H hv hs) (H.mul_mem (H.inv_mem (m1735 H hv hs)) H.one_mem))))

private theorem m962 : g 962 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-983,863,379,-1258")) (hv 13641 (by decide))
    (H.mul_mem (H.inv_mem (m983 H hv hs)) (H.mul_mem (m863 H hv hs) (H.mul_mem (m379 H hv hs) (H.mul_mem (H.inv_mem (m1258 H hv hs)) H.one_mem))))

private theorem m230 : g 230 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "345,956,-558")) (hv 31071 (by decide))
    (H.mul_mem (m345 H hv hs) (H.mul_mem (m956 H hv hs) (H.mul_mem (H.inv_mem (m558 H hv hs)) H.one_mem)))

private theorem m1133 : g 1133 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1686,-957,-267")) (hv 13654 (by decide))
    (H.mul_mem (m1686 H hv hs) (H.mul_mem (H.inv_mem (m957 H hv hs)) (H.mul_mem (H.inv_mem (m267 H hv hs)) H.one_mem)))

private theorem m80 : g 80 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-208,780,1843")) (hv 13661 (by decide))
    (H.mul_mem (H.inv_mem (m208 H hv hs)) (H.mul_mem (m780 H hv hs) (H.mul_mem (m1843 H hv hs) H.one_mem)))

private theorem m796 : g 796 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1139,2,803,-629,-424")) (hv 13665 (by decide))
    (H.mul_mem (m1139 H hv hs) (H.mul_mem (m2 H hs) (H.mul_mem (m803 H hv hs) (H.mul_mem (H.inv_mem (m629 H hv hs)) (H.mul_mem (H.inv_mem (m424 H hv hs)) H.one_mem)))))

private theorem m479 : g 479 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "649,267,28,-3")) (hv 13668 (by decide))
    (H.mul_mem (m649 H hv hs) (H.mul_mem (m267 H hv hs) (H.mul_mem (m28 H hv hs) (H.mul_mem (H.inv_mem (m3 H hs)) H.one_mem))))

private theorem m509 : g 509 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "652,-1930,284,758")) (hv 13683 (by decide))
    (H.mul_mem (m652 H hv hs) (H.mul_mem (H.inv_mem (m1930 H hv hs)) (H.mul_mem (m284 H hv hs) (H.mul_mem (m758 H hv hs) H.one_mem))))

private theorem m1613 : g 1613 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-634,216,1114")) (hv 13686 (by decide))
    (H.mul_mem (H.inv_mem (m634 H hv hs)) (H.mul_mem (m216 H hv hs) (H.mul_mem (m1114 H hv hs) H.one_mem)))

private theorem m429 : g 429 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-182,-322")) (hv 13700 (by decide))
    (H.mul_mem (H.inv_mem (m182 H hv hs)) (H.mul_mem (H.inv_mem (m322 H hv hs)) H.one_mem))

private theorem m164 : g 164 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-560,-758,-182,-104")) (hv 13786 (by decide))
    (H.mul_mem (H.inv_mem (m560 H hv hs)) (H.mul_mem (H.inv_mem (m758 H hv hs)) (H.mul_mem (H.inv_mem (m182 H hv hs)) (H.mul_mem (H.inv_mem (m104 H hv hs)) H.one_mem))))

private theorem m142 : g 142 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1799,-161,863,-867")) (hv 13788 (by decide))
    (H.mul_mem (H.inv_mem (m1799 H hv hs)) (H.mul_mem (H.inv_mem (m161 H hv hs)) (H.mul_mem (m863 H hv hs) (H.mul_mem (H.inv_mem (m867 H hv hs)) H.one_mem))))

private theorem m1091 : g 1091 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-180,1765,-352")) (hv 13793 (by decide))
    (H.mul_mem (H.inv_mem (m180 H hv hs)) (H.mul_mem (m1765 H hv hs) (H.mul_mem (H.inv_mem (m352 H hv hs)) H.one_mem)))

private theorem m224 : g 224 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "147,-1208,59")) (hv 13808 (by decide))
    (H.mul_mem (m147 H hv hs) (H.mul_mem (H.inv_mem (m1208 H hv hs)) (H.mul_mem (m59 H hv hs) H.one_mem)))

private theorem m305 : g 305 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-312,1,107")) (hv 13853 (by decide))
    (H.mul_mem (H.inv_mem (m312 H hv hs)) (H.mul_mem (m1 H hs) (H.mul_mem (m107 H hv hs) H.one_mem)))

private theorem m886 : g 886 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "56,1403")) (hv 13866 (by decide))
    (H.mul_mem (m56 H hv hs) (H.mul_mem (m1403 H hv hs) H.one_mem))

private theorem m1925 : g 1925 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-475,-56,-1864")) (hv 13875 (by decide))
    (H.mul_mem (H.inv_mem (m475 H hv hs)) (H.mul_mem (H.inv_mem (m56 H hv hs)) (H.mul_mem (H.inv_mem (m1864 H hv hs)) H.one_mem)))

private theorem m2043 : g 2043 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-227,-235,-190,-1,-752,874,1030")) (hv 13892 (by decide))
    (H.mul_mem (H.inv_mem (m227 H hv hs)) (H.mul_mem (H.inv_mem (m235 H hs)) (H.mul_mem (H.inv_mem (m190 H hv hs)) (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (H.inv_mem (m752 H hv hs)) (H.mul_mem (m874 H hv hs) (H.mul_mem (m1030 H hv hs) H.one_mem)))))))

private theorem m953 : g 953 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-190,1168,-1,1235")) (hv 13920 (by decide))
    (H.mul_mem (H.inv_mem (m190 H hv hs)) (H.mul_mem (m1168 H hv hs) (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (m1235 H hv hs) H.one_mem))))

private theorem m453 : g 453 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-291,-1451,-1184,-835,291")) (hv 13926 (by decide))
    (H.mul_mem (H.inv_mem (m291 H hv hs)) (H.mul_mem (H.inv_mem (m1451 H hv hs)) (H.mul_mem (H.inv_mem (m1184 H hv hs)) (H.mul_mem (H.inv_mem (m835 H hv hs)) (H.mul_mem (m291 H hv hs) H.one_mem)))))

private theorem m2006 : g 2006 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-801,398,1203,-841,-182")) (hv 31072 (by decide))
    (H.mul_mem (H.inv_mem (m801 H hv hs)) (H.mul_mem (m398 H hv hs) (H.mul_mem (m1203 H hv hs) (H.mul_mem (H.inv_mem (m841 H hv hs)) (H.mul_mem (H.inv_mem (m182 H hv hs)) H.one_mem)))))

private theorem m1247 : g 1247 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1,2037,798,1864")) (hv 14737 (by decide))
    (H.mul_mem (m1 H hs) (H.mul_mem (m2037 H hv hs) (H.mul_mem (m798 H hv hs) (H.mul_mem (m1864 H hv hs) H.one_mem))))

private theorem m99 : g 99 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-135,-197,1843")) (hv 14747 (by decide))
    (H.mul_mem (H.inv_mem (m135 H hv hs)) (H.mul_mem (H.inv_mem (m197 H hv hs)) (H.mul_mem (m1843 H hv hs) H.one_mem)))

private theorem m1027 : g 1027 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1,629,1403,208")) (hv 14778 (by decide))
    (H.mul_mem (m1 H hs) (H.mul_mem (m629 H hv hs) (H.mul_mem (m1403 H hv hs) (H.mul_mem (m208 H hv hs) H.one_mem))))

private theorem m4 : g 4 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "514,462,-836,267")) (hv 14791 (by decide))
    (H.mul_mem (m514 H hv hs) (H.mul_mem (m462 H hv hs) (H.mul_mem (H.inv_mem (m836 H hv hs)) (H.mul_mem (m267 H hv hs) H.one_mem))))

private theorem m990 : g 990 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "122,558,-956,588,1057,-449")) (hv 14810 (by decide))
    (H.mul_mem (m122 H hv hs) (H.mul_mem (m558 H hv hs) (H.mul_mem (H.inv_mem (m956 H hv hs)) (H.mul_mem (m588 H hv hs) (H.mul_mem (m1057 H hv hs) (H.mul_mem (H.inv_mem (m449 H hv hs)) H.one_mem))))))

private theorem m845 : g 845 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "560,116,8,-1824")) (hv 14829 (by decide))
    (H.mul_mem (m560 H hv hs) (H.mul_mem (m116 H hv hs) (H.mul_mem (m8 H hv hs) (H.mul_mem (H.inv_mem (m1824 H hv hs)) H.one_mem))))

private theorem m552 : g 552 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-28,-267,-1403")) (hv 14845 (by decide))
    (H.mul_mem (H.inv_mem (m28 H hv hs)) (H.mul_mem (H.inv_mem (m267 H hv hs)) (H.mul_mem (H.inv_mem (m1403 H hv hs)) H.one_mem)))

private theorem m319 : g 319 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-125,-590,-1621")) (hv 14847 (by decide))
    (H.mul_mem (H.inv_mem (m125 H hv hs)) (H.mul_mem (H.inv_mem (m590 H hv hs)) (H.mul_mem (H.inv_mem (m1621 H hv hs)) H.one_mem)))

private theorem m307 : g 307 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1,-1041,510,-1843,-147,-30")) (hv 14855 (by decide))
    (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (H.inv_mem (m1041 H hs)) (H.mul_mem (m510 H hv hs) (H.mul_mem (H.inv_mem (m1843 H hv hs)) (H.mul_mem (H.inv_mem (m147 H hv hs)) (H.mul_mem (H.inv_mem (m30 H hv hs)) H.one_mem))))))

private theorem m650 : g 650 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "745,1083,-764,1076")) (hv 31073 (by decide))
    (H.mul_mem (m745 H hv hs) (H.mul_mem (m1083 H hv hs) (H.mul_mem (H.inv_mem (m764 H hv hs)) (H.mul_mem (m1076 H hv hs) H.one_mem))))

private theorem m1671 : g 1671 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1451,1735,1450")) (hv 14857 (by decide))
    (H.mul_mem (m1451 H hv hs) (H.mul_mem (m1735 H hv hs) (H.mul_mem (m1450 H hv hs) H.one_mem)))

private theorem m2033 : g 2033 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1930,-1843,-147,855,735")) (hv 14875 (by decide))
    (H.mul_mem (m1930 H hv hs) (H.mul_mem (H.inv_mem (m1843 H hv hs)) (H.mul_mem (H.inv_mem (m147 H hv hs)) (H.mul_mem (m855 H hv hs) (H.mul_mem (m735 H hv hs) H.one_mem)))))

private theorem m179 : g 179 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "352,189,1772,701,-634,1087")) (hv 31074 (by decide))
    (H.mul_mem (m352 H hv hs) (H.mul_mem (m189 H hv hs) (H.mul_mem (m1772 H hs) (H.mul_mem (m701 H hv hs) (H.mul_mem (H.inv_mem (m634 H hv hs)) (H.mul_mem (m1087 H hv hs) H.one_mem))))))

private theorem m457 : g 457 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1,480,-3,-674,348,190")) (hv 14903 (by decide))
    (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (m480 H hs) (H.mul_mem (H.inv_mem (m3 H hs)) (H.mul_mem (H.inv_mem (m674 H hv hs)) (H.mul_mem (m348 H hs) (H.mul_mem (m190 H hv hs) H.one_mem))))))

private theorem m1047 : g 1047 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-302,601,581,302,10")) (hv 14953 (by decide))
    (H.mul_mem (H.inv_mem (m302 H hv hs)) (H.mul_mem (m601 H hv hs) (H.mul_mem (m581 H hv hs) (H.mul_mem (m302 H hv hs) (H.mul_mem (m10 H hv hs) H.one_mem)))))

private theorem m1979 : g 1979 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1106,1824,125,-42")) (hv 14960 (by decide))
    (H.mul_mem (H.inv_mem (m1106 H hs)) (H.mul_mem (m1824 H hv hs) (H.mul_mem (m125 H hv hs) (H.mul_mem (H.inv_mem (m42 H hv hs)) H.one_mem))))

private theorem m804 : g 804 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-12,-182,836")) (hv 14982 (by decide))
    (H.mul_mem (H.inv_mem (m12 H hv hs)) (H.mul_mem (H.inv_mem (m182 H hv hs)) (H.mul_mem (m836 H hv hs) H.one_mem)))

private theorem m602 : g 602 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-30,736,431,1864,56")) (hv 14989 (by decide))
    (H.mul_mem (H.inv_mem (m30 H hv hs)) (H.mul_mem (m736 H hv hs) (H.mul_mem (m431 H hv hs) (H.mul_mem (m1864 H hv hs) (H.mul_mem (m56 H hv hs) H.one_mem)))))

private theorem m1809 : g 1809 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "867,-863,161,831,352,-1765")) (hv 31075 (by decide))
    (H.mul_mem (m867 H hv hs) (H.mul_mem (H.inv_mem (m863 H hv hs)) (H.mul_mem (m161 H hv hs) (H.mul_mem (m831 H hv hs) (H.mul_mem (m352 H hv hs) (H.mul_mem (H.inv_mem (m1765 H hv hs)) H.one_mem))))))

private theorem m1704 : g 1704 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "268,533,550,1083,-268")) (hv 15962 (by decide))
    (H.mul_mem (m268 H hv hs) (H.mul_mem (m533 H hv hs) (H.mul_mem (m550 H hv hs) (H.mul_mem (m1083 H hv hs) (H.mul_mem (H.inv_mem (m268 H hv hs)) H.one_mem)))))

private theorem m1190 : g 1190 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "195,-748,1087,-890,-755")) (hv 15964 (by decide))
    (H.mul_mem (m195 H hv hs) (H.mul_mem (H.inv_mem (m748 H hv hs)) (H.mul_mem (m1087 H hv hs) (H.mul_mem (H.inv_mem (m890 H hv hs)) (H.mul_mem (H.inv_mem (m755 H hv hs)) H.one_mem)))))

private theorem m1828 : g 1828 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1,-8,-30,-701")) (hv 15970 (by decide))
    (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (H.inv_mem (m8 H hv hs)) (H.mul_mem (H.inv_mem (m30 H hv hs)) (H.mul_mem (H.inv_mem (m701 H hv hs)) H.one_mem))))

private theorem m1516 : g 1516 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "860,459,243,1662,-867,1451")) (hv 15991 (by decide))
    (H.mul_mem (m860 H hv hs) (H.mul_mem (m459 H hv hs) (H.mul_mem (m243 H hv hs) (H.mul_mem (m1662 H hv hs) (H.mul_mem (H.inv_mem (m867 H hv hs)) (H.mul_mem (m1451 H hv hs) H.one_mem))))))

private theorem m51 : g 51 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "480,2018,-258,-748")) (hv 16040 (by decide))
    (H.mul_mem (m480 H hs) (H.mul_mem (m2018 H hv hs) (H.mul_mem (H.inv_mem (m258 H hv hs)) (H.mul_mem (H.inv_mem (m748 H hv hs)) H.one_mem))))

private theorem m416 : g 416 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "415,524,-1864,785,1265,1703")) (hv 16089 (by decide))
    (H.mul_mem (m415 H hv hs) (H.mul_mem (m524 H hv hs) (H.mul_mem (H.inv_mem (m1864 H hv hs)) (H.mul_mem (m785 H hv hs) (H.mul_mem (m1265 H hv hs) (H.mul_mem (m1703 H hv hs) H.one_mem))))))

private theorem m1096 : g 1096 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-8,197,1")) (hv 16095 (by decide))
    (H.mul_mem (H.inv_mem (m8 H hv hs)) (H.mul_mem (m197 H hv hs) (H.mul_mem (m1 H hs) H.one_mem)))

private theorem m1631 : g 1631 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-258,-2018,241,701,688")) (hv 16105 (by decide))
    (H.mul_mem (H.inv_mem (m258 H hv hs)) (H.mul_mem (H.inv_mem (m2018 H hv hs)) (H.mul_mem (m241 H hv hs) (H.mul_mem (m701 H hv hs) (H.mul_mem (m688 H hs) H.one_mem)))))

private theorem m521 : g 521 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "312,77,588,-241")) (hv 16107 (by decide))
    (H.mul_mem (m312 H hv hs) (H.mul_mem (m77 H hv hs) (H.mul_mem (m588 H hv hs) (H.mul_mem (H.inv_mem (m241 H hv hs)) H.one_mem))))

private theorem m192 : g 192 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1076,1210,-189,-574,148,-1235,459")) (hv 31076 (by decide))
    (H.mul_mem (m1076 H hv hs) (H.mul_mem (m1210 H hv hs) (H.mul_mem (H.inv_mem (m189 H hv hs)) (H.mul_mem (H.inv_mem (m574 H hv hs)) (H.mul_mem (m148 H hv hs) (H.mul_mem (H.inv_mem (m1235 H hv hs)) (H.mul_mem (m459 H hv hs) H.one_mem)))))))

private theorem m1345 : g 1345 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-322,-1106,-558,345,-1057,1321,-1703")) (hv 31077 (by decide))
    (H.mul_mem (H.inv_mem (m322 H hv hs)) (H.mul_mem (H.inv_mem (m1106 H hs)) (H.mul_mem (H.inv_mem (m558 H hv hs)) (H.mul_mem (m345 H hv hs) (H.mul_mem (H.inv_mem (m1057 H hv hs)) (H.mul_mem (m1321 H hv hs) (H.mul_mem (H.inv_mem (m1703 H hv hs)) H.one_mem)))))))

private theorem m1060 : g 1060 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1930,-122,-1621,-893,19,-161,863")) (hv 16360 (by decide))
    (H.mul_mem (H.inv_mem (m1930 H hv hs)) (H.mul_mem (H.inv_mem (m122 H hv hs)) (H.mul_mem (H.inv_mem (m1621 H hv hs)) (H.mul_mem (H.inv_mem (m893 H hv hs)) (H.mul_mem (m19 H hv hs) (H.mul_mem (H.inv_mem (m161 H hv hs)) (H.mul_mem (m863 H hv hs) H.one_mem)))))))

private theorem m1052 : g 1052 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-125,1053,348,1208")) (hv 16402 (by decide))
    (H.mul_mem (H.inv_mem (m125 H hv hs)) (H.mul_mem (m1053 H hv hs) (H.mul_mem (m348 H hs) (H.mul_mem (m1208 H hv hs) H.one_mem))))

private theorem m371 : g 371 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "352,-1765,1258,-1018,-1451,-243")) (hv 17598 (by decide))
    (H.mul_mem (m352 H hv hs) (H.mul_mem (H.inv_mem (m1765 H hv hs)) (H.mul_mem (m1258 H hv hs) (H.mul_mem (H.inv_mem (m1018 H hv hs)) (H.mul_mem (H.inv_mem (m1451 H hv hs)) (H.mul_mem (H.inv_mem (m243 H hv hs)) H.one_mem))))))

private theorem m1026 : g 1026 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "863,-360,-688,736,352,1824,-550")) (hv 31078 (by decide))
    (H.mul_mem (m863 H hv hs) (H.mul_mem (H.inv_mem (m360 H hv hs)) (H.mul_mem (H.inv_mem (m688 H hs)) (H.mul_mem (m736 H hv hs) (H.mul_mem (m352 H hv hs) (H.mul_mem (m1824 H hv hs) (H.mul_mem (H.inv_mem (m550 H hv hs)) H.one_mem)))))))

private theorem m861 : g 861 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "860,459,758,-1106,2037,1432,-148,-1")) (hv 17640 (by decide))
    (H.mul_mem (m860 H hv hs) (H.mul_mem (m459 H hv hs) (H.mul_mem (m758 H hv hs) (H.mul_mem (H.inv_mem (m1106 H hs)) (H.mul_mem (m2037 H hv hs) (H.mul_mem (m1432 H hv hs) (H.mul_mem (H.inv_mem (m148 H hv hs)) (H.mul_mem (H.inv_mem (m1 H hs)) H.one_mem))))))))

private theorem m442 : g 442 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1168,-558,1621")) (hv 17673 (by decide))
    (H.mul_mem (H.inv_mem (m1168 H hv hs)) (H.mul_mem (H.inv_mem (m558 H hv hs)) (H.mul_mem (m1621 H hv hs) H.one_mem)))

private theorem m1294 : g 1294 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1018,-1321,1057,780,-189,-1765,-736")) (hv 17764 (by decide))
    (H.mul_mem (m1018 H hv hs) (H.mul_mem (H.inv_mem (m1321 H hv hs)) (H.mul_mem (m1057 H hv hs) (H.mul_mem (m780 H hv hs) (H.mul_mem (H.inv_mem (m189 H hv hs)) (H.mul_mem (H.inv_mem (m1765 H hv hs)) (H.mul_mem (H.inv_mem (m736 H hv hs)) H.one_mem)))))))

private theorem m1848 : g 1848 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1405,-1106,-348,890,645,-1824,189,288,288,288,-1168,-558,1621")) (hv 17883 (by decide))
    (H.mul_mem (m1405 H hv hs) (H.mul_mem (H.inv_mem (m1106 H hs)) (H.mul_mem (H.inv_mem (m348 H hs)) (H.mul_mem (m890 H hv hs) (H.mul_mem (m645 H hv hs) (H.mul_mem (H.inv_mem (m1824 H hv hs)) (H.mul_mem (m189 H hv hs) (H.mul_mem (m288 H hv hs) (H.mul_mem (m288 H hv hs) (H.mul_mem (m288 H hv hs) (H.mul_mem (H.inv_mem (m1168 H hv hs)) (H.mul_mem (H.inv_mem (m558 H hv hs)) (H.mul_mem (m1621 H hv hs) H.one_mem)))))))))))))

private theorem m1401 : g 1401 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1057,3,-906,-1405,-890,-755,1208")) (hv 18959 (by decide))
    (H.mul_mem (m1057 H hv hs) (H.mul_mem (m3 H hs) (H.mul_mem (H.inv_mem (m906 H hs)) (H.mul_mem (H.inv_mem (m1405 H hv hs)) (H.mul_mem (H.inv_mem (m890 H hv hs)) (H.mul_mem (H.inv_mem (m755 H hv hs)) (H.mul_mem (m1208 H hv hs) H.one_mem)))))))

private theorem m1675 : g 1675 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "780,197,-588,3,729,288,-1168,-558,1621")) (hv 18967 (by decide))
    (H.mul_mem (m780 H hv hs) (H.mul_mem (m197 H hv hs) (H.mul_mem (H.inv_mem (m588 H hv hs)) (H.mul_mem (m3 H hs) (H.mul_mem (m729 H hv hs) (H.mul_mem (m288 H hv hs) (H.mul_mem (H.inv_mem (m1168 H hv hs)) (H.mul_mem (H.inv_mem (m558 H hv hs)) (H.mul_mem (m1621 H hv hs) H.one_mem)))))))))

private theorem m364 : g 364 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-4")) (hv 4594 (by decide))
    (H.mul_mem (H.inv_mem (m4 H hv hs)) H.one_mem)

private theorem m709 : g 709 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-6")) (hv 4598 (by decide))
    (H.mul_mem (H.inv_mem (m6 H hv hs)) H.one_mem)

private theorem m1200 : g 1200 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-429")) (hv 4992 (by decide))
    (H.mul_mem (H.inv_mem (m429 H hv hs)) H.one_mem)

private theorem m1479 : g 1479 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1096")) (hv 4790 (by decide))
    (H.mul_mem (H.inv_mem (m1096 H hv hs)) H.one_mem)

private theorem m405 : g 405 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-230")) (hv 5584 (by decide))
    (H.mul_mem (H.inv_mem (m230 H hv hs)) H.one_mem)

private theorem m1373 : g 1373 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-68")) (hv 5639 (by decide))
    (H.mul_mem (H.inv_mem (m68 H hv hs)) H.one_mem)

private theorem m1573 : g 1573 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-73")) (hv 4792 (by decide))
    (H.mul_mem (H.inv_mem (m73 H hv hs)) H.one_mem)

private theorem m155 : g 155 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-89")) (hv 4860 (by decide))
    (H.mul_mem (H.inv_mem (m89 H hv hs)) H.one_mem)

private theorem m749 : g 749 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-99")) (hv 4994 (by decide))
    (H.mul_mem (H.inv_mem (m99 H hv hs)) H.one_mem)

private theorem m921 : g 921 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-115")) (hv 5469 (by decide))
    (H.mul_mem (H.inv_mem (m115 H hv hs)) H.one_mem)

private theorem m1289 : g 1289 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-142")) (hv 5141 (by decide))
    (H.mul_mem (H.inv_mem (m142 H hv hs)) H.one_mem)

private theorem m954 : g 954 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-164")) (hv 5642 (by decide))
    (H.mul_mem (H.inv_mem (m164 H hv hs)) H.one_mem)

private theorem m1191 : g 1191 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-179")) (hv 5467 (by decide))
    (H.mul_mem (H.inv_mem (m179 H hv hs)) H.one_mem)

private theorem m1492 : g 1492 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-875")) (hv 4657 (by decide))
    (H.mul_mem (H.inv_mem (m875 H hv hs)) H.one_mem)

private theorem m1353 : g 1353 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-215")) (hv 4778 (by decide))
    (H.mul_mem (H.inv_mem (m215 H hv hs)) H.one_mem)

private theorem m1603 : g 1603 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-262")) (hv 5461 (by decide))
    (H.mul_mem (H.inv_mem (m262 H hv hs)) H.one_mem)

private theorem m1612 : g 1612 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1060")) (hv 5119 (by decide))
    (H.mul_mem (H.inv_mem (m1060 H hv hs)) H.one_mem)

private theorem m1045 : g 1045 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-305")) (hv 5416 (by decide))
    (H.mul_mem (H.inv_mem (m305 H hv hs)) H.one_mem)

private theorem m734 : g 734 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-311")) (hv 5123 (by decide))
    (H.mul_mem (H.inv_mem (m311 H hv hs)) H.one_mem)

private theorem m363 : g 363 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-320")) (hv 5566 (by decide))
    (H.mul_mem (H.inv_mem (m320 H hv hs)) H.one_mem)

private theorem m1854 : g 1854 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-990")) (hv 5487 (by decide))
    (H.mul_mem (H.inv_mem (m990 H hv hs)) H.one_mem)

private theorem m676 : g 676 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-369")) (hv 5464 (by decide))
    (H.mul_mem (H.inv_mem (m369 H hv hs)) H.one_mem)

private theorem m1804 : g 1804 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1247")) (hv 5345 (by decide))
    (H.mul_mem (H.inv_mem (m1247 H hv hs)) H.one_mem)

private theorem m1993 : g 1993 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-380")) (hv 5477 (by decide))
    (H.mul_mem (H.inv_mem (m380 H hv hs)) H.one_mem)

private theorem m1926 : g 1926 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-416")) (hv 5484 (by decide))
    (H.mul_mem (H.inv_mem (m416 H hv hs)) H.one_mem)

private theorem m1241 : g 1241 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-552")) (hv 5306 (by decide))
    (H.mul_mem (H.inv_mem (m552 H hv hs)) H.one_mem)

private theorem m1483 : g 1483 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-457")) (hv 5547 (by decide))
    (H.mul_mem (H.inv_mem (m457 H hv hs)) H.one_mem)

private theorem m1855 : g 1855 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-468")) (hv 5524 (by decide))
    (H.mul_mem (H.inv_mem (m468 H hv hs)) H.one_mem)

private theorem m1948 : g 1948 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-482")) (hv 31079 (by decide))
    (H.mul_mem (H.inv_mem (m482 H hv hs)) H.one_mem)

private theorem m658 : g 658 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-498")) (hv 5378 (by decide))
    (H.mul_mem (H.inv_mem (m498 H hv hs)) H.one_mem)

private theorem m566 : g 566 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-509")) (hv 5000 (by decide))
    (H.mul_mem (H.inv_mem (m509 H hv hs)) H.one_mem)

private theorem m579 : g 579 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-531")) (hv 4921 (by decide))
    (H.mul_mem (H.inv_mem (m531 H hv hs)) H.one_mem)

private theorem m1567 : g 1567 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-602")) (hv 5283 (by decide))
    (H.mul_mem (H.inv_mem (m602 H hv hs)) H.one_mem)

private theorem m1163 : g 1163 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-650")) (hv 5775 (by decide))
    (H.mul_mem (H.inv_mem (m650 H hv hs)) H.one_mem)

private theorem m1829 : g 1829 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-728")) (hv 5625 (by decide))
    (H.mul_mem (H.inv_mem (m728 H hv hs)) H.one_mem)

private theorem m1141 : g 1141 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-765")) (hv 5128 (by decide))
    (H.mul_mem (H.inv_mem (m765 H hv hs)) H.one_mem)

private theorem m1193 : g 1193 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-796")) (hv 5238 (by decide))
    (H.mul_mem (H.inv_mem (m796 H hv hs)) H.one_mem)

private theorem m941 : g 941 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-804")) (hv 5442 (by decide))
    (H.mul_mem (H.inv_mem (m804 H hv hs)) H.one_mem)

private theorem m1361 : g 1361 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-886")) (hv 5656 (by decide))
    (H.mul_mem (H.inv_mem (m886 H hv hs)) H.one_mem)

private theorem m1712 : g 1712 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-953")) (hv 5648 (by decide))
    (H.mul_mem (H.inv_mem (m953 H hv hs)) H.one_mem)

private theorem m2001 : g 2001 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1047")) (hv 31080 (by decide))
    (H.mul_mem (H.inv_mem (m1047 H hv hs)) H.one_mem)

private theorem m1452 : g 1452 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1091")) (hv 5307 (by decide))
    (H.mul_mem (H.inv_mem (m1091 H hv hs)) H.one_mem)

private theorem m1593 : g 1593 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1332")) (hv 4615 (by decide))
    (H.mul_mem (H.inv_mem (m1332 H hv hs)) H.one_mem)

private theorem m1646 : g 1646 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1472")) (hv 5322 (by decide))
    (H.mul_mem (H.inv_mem (m1472 H hv hs)) H.one_mem)

private theorem m1756 : g 1756 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1698")) (hv 5742 (by decide))
    (H.mul_mem (H.inv_mem (m1698 H hv hs)) H.one_mem)

private theorem m1819 : g 1819 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1809")) (hv 31081 (by decide))
    (H.mul_mem (H.inv_mem (m1809 H hv hs)) H.one_mem)

private theorem m1568 : g 1568 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1332")) (hv 7794 (by decide))
    (H.mul_mem (m1332 H hv hs) H.one_mem)

private theorem m124 : g 124 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-886,-804")) (hv 10068 (by decide))
    (H.mul_mem (H.inv_mem (m886 H hv hs)) (H.mul_mem (H.inv_mem (m804 H hv hs)) H.one_mem))

private theorem m335 : g 335 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1925,-3")) (hv 10075 (by decide))
    (H.mul_mem (H.inv_mem (m1925 H hv hs)) (H.mul_mem (H.inv_mem (m3 H hs)) H.one_mem))

private theorem m2046 : g 2046 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1018,-1125")) (hv 10078 (by decide))
    (H.mul_mem (H.inv_mem (m1018 H hv hs)) (H.mul_mem (H.inv_mem (m1125 H hv hs)) H.one_mem))

private theorem m1796 : g 1796 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1208,-1941")) (hv 10091 (by decide))
    (H.mul_mem (H.inv_mem (m1208 H hv hs)) (H.mul_mem (H.inv_mem (m1941 H hv hs)) H.one_mem))

private theorem m1158 : g 1158 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1824,-845")) (hv 10094 (by decide))
    (H.mul_mem (H.inv_mem (m1824 H hv hs)) (H.mul_mem (H.inv_mem (m845 H hv hs)) H.one_mem))

private theorem m541 : g 541 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-977,-2049")) (hv 10100 (by decide))
    (H.mul_mem (H.inv_mem (m977 H hv hs)) (H.mul_mem (H.inv_mem (m2049 H hv hs)) H.one_mem))

private theorem m1886 : g 1886 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-968,-1148")) (hv 10109 (by decide))
    (H.mul_mem (H.inv_mem (m968 H hv hs)) (H.mul_mem (H.inv_mem (m1148 H hv hs)) H.one_mem))

private theorem m750 : g 750 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1843,99")) (hv 10149 (by decide))
    (H.mul_mem (H.inv_mem (m1843 H hv hs)) (H.mul_mem (m99 H hv hs) H.one_mem))

private theorem m719 : g 719 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-434,-2058")) (hv 10150 (by decide))
    (H.mul_mem (H.inv_mem (m434 H hv hs)) (H.mul_mem (H.inv_mem (m2058 H hv hs)) H.one_mem))

private theorem m175 : g 175 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1972,-1775")) (hv 10152 (by decide))
    (H.mul_mem (m1972 H hs) (H.mul_mem (H.inv_mem (m1775 H hv hs)) H.one_mem))

private theorem m455 : g 455 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1869,-1775")) (hv 10177 (by decide))
    (H.mul_mem (H.inv_mem (m1869 H hv hs)) (H.mul_mem (H.inv_mem (m1775 H hv hs)) H.one_mem))

private theorem m1458 : g 1458 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-311,1686,74")) (hv 10182 (by decide))
    (H.mul_mem (H.inv_mem (m311 H hv hs)) (H.mul_mem (m1686 H hv hs) (H.mul_mem (m74 H hv hs) H.one_mem)))

private theorem m385 : g 385 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1332,-263")) (hv 10213 (by decide))
    (H.mul_mem (m1332 H hv hs) (H.mul_mem (H.inv_mem (m263 H hv hs)) H.one_mem))

private theorem m486 : g 486 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "369,1087")) (hv 10242 (by decide))
    (H.mul_mem (m369 H hv hs) (H.mul_mem (m1087 H hv hs) H.one_mem))

private theorem m41 : g 41 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-89,-200,-937")) (hv 10247 (by decide))
    (H.mul_mem (H.inv_mem (m89 H hv hs)) (H.mul_mem (H.inv_mem (m200 H hv hs)) (H.mul_mem (H.inv_mem (m937 H hv hs)) H.one_mem)))

private theorem m1871 : g 1871 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "558,-319")) (hv 10252 (by decide))
    (H.mul_mem (m558 H hv hs) (H.mul_mem (H.inv_mem (m319 H hv hs)) H.one_mem))

private theorem m1853 : g 1853 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "533,-1026")) (hv 10253 (by decide))
    (H.mul_mem (m533 H hv hs) (H.mul_mem (H.inv_mem (m1026 H hv hs)) H.one_mem))

private theorem m547 : g 547 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-320,-424,-1958")) (hv 10283 (by decide))
    (H.mul_mem (H.inv_mem (m320 H hv hs)) (H.mul_mem (H.inv_mem (m424 H hv hs)) (H.mul_mem (H.inv_mem (m1958 H hs)) H.one_mem)))

private theorem m212 : g 212 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-886,-1253,886")) (hv 10287 (by decide))
    (H.mul_mem (H.inv_mem (m886 H hv hs)) (H.mul_mem (H.inv_mem (m1253 H hv hs)) (H.mul_mem (m886 H hv hs) H.one_mem)))

private theorem m1067 : g 1067 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1828,-101")) (hv 10990 (by decide))
    (H.mul_mem (H.inv_mem (m1828 H hv hs)) (H.mul_mem (H.inv_mem (m101 H hv hs)) H.one_mem))

private theorem m2025 : g 2025 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-861,-1876")) (hv 11005 (by decide))
    (H.mul_mem (H.inv_mem (m861 H hv hs)) (H.mul_mem (H.inv_mem (m1876 H hv hs)) H.one_mem))

private theorem m1985 : g 1985 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-231,-305")) (hv 11024 (by decide))
    (H.mul_mem (H.inv_mem (m231 H hv hs)) (H.mul_mem (H.inv_mem (m305 H hv hs)) H.one_mem))

private theorem m1744 : g 1744 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1027,-1018")) (hv 11028 (by decide))
    (H.mul_mem (m1027 H hv hs) (H.mul_mem (H.inv_mem (m1018 H hv hs)) H.one_mem))

private theorem m582 : g 582 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1208,-1190")) (hv 11034 (by decide))
    (H.mul_mem (H.inv_mem (m1208 H hv hs)) (H.mul_mem (H.inv_mem (m1190 H hv hs)) H.one_mem))

private theorem m78 : g 78 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "442,-1675,-1047")) (hv 31082 (by decide))
    (H.mul_mem (m442 H hv hs) (H.mul_mem (H.inv_mem (m1675 H hv hs)) (H.mul_mem (H.inv_mem (m1047 H hv hs)) H.one_mem)))

private theorem m1465 : g 1465 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-893,-1848,-928")) (hv 31083 (by decide))
    (H.mul_mem (H.inv_mem (m893 H hv hs)) (H.mul_mem (H.inv_mem (m1848 H hv hs)) (H.mul_mem (H.inv_mem (m928 H hv hs)) H.one_mem)))

private theorem m1236 : g 1236 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1286,-56,-1507")) (hv 31084 (by decide))
    (H.mul_mem (H.inv_mem (m1286 H hv hs)) (H.mul_mem (H.inv_mem (m56 H hv hs)) (H.mul_mem (H.inv_mem (m1507 H hv hs)) H.one_mem)))

private theorem m925 : g 925 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1613,736,-1801")) (hv 11071 (by decide))
    (H.mul_mem (H.inv_mem (m1613 H hv hs)) (H.mul_mem (m736 H hv hs) (H.mul_mem (H.inv_mem (m1801 H hv hs)) H.one_mem)))

private theorem m2021 : g 2021 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1294,736,1809")) (hv 11100 (by decide))
    (H.mul_mem (m1294 H hv hs) (H.mul_mem (m736 H hv hs) (H.mul_mem (m1809 H hv hs) H.one_mem)))

private theorem m1307 : g 1307 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "804,-1594,-804")) (hv 31085 (by decide))
    (H.mul_mem (m804 H hv hs) (H.mul_mem (H.inv_mem (m1594 H hv hs)) (H.mul_mem (H.inv_mem (m804 H hv hs)) H.one_mem)))

private theorem m49 : g 49 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1520,-224")) (hv 11122 (by decide))
    (H.mul_mem (H.inv_mem (m1520 H hv hs)) (H.mul_mem (H.inv_mem (m224 H hv hs)) H.one_mem))

private theorem m213 : g 213 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-886,-1253,56,-514")) (hv 11126 (by decide))
    (H.mul_mem (H.inv_mem (m886 H hv hs)) (H.mul_mem (H.inv_mem (m1253 H hv hs)) (H.mul_mem (m56 H hv hs) (H.mul_mem (H.inv_mem (m514 H hv hs)) H.one_mem))))

private theorem m259 : g 259 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1052,97")) (hv 11162 (by decide))
    (H.mul_mem (H.inv_mem (m1052 H hv hs)) (H.mul_mem (m97 H hv hs) H.one_mem))

private theorem m1902 : g 1902 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-313,-1613,313")) (hv 11171 (by decide))
    (H.mul_mem (H.inv_mem (m313 H hv hs)) (H.mul_mem (H.inv_mem (m1613 H hv hs)) (H.mul_mem (m313 H hv hs) H.one_mem)))

private theorem m1459 : g 1459 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-376,-192,-36")) (hv 31086 (by decide))
    (H.mul_mem (H.inv_mem (m376 H hv hs)) (H.mul_mem (H.inv_mem (m192 H hv hs)) (H.mul_mem (H.inv_mem (m36 H hv hs)) H.one_mem)))

private theorem m1178 : g 1178 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "585,-1,457")) (hv 11176 (by decide))
    (H.mul_mem (m585 H hv hs) (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (m457 H hv hs) H.one_mem)))

private theorem m834 : g 834 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "291,-453,-291")) (hv 11178 (by decide))
    (H.mul_mem (m291 H hv hs) (H.mul_mem (H.inv_mem (m453 H hv hs)) (H.mul_mem (H.inv_mem (m291 H hv hs)) H.one_mem)))

private theorem m2041 : g 2041 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-886,-616,886")) (hv 11222 (by decide))
    (H.mul_mem (H.inv_mem (m886 H hv hs)) (H.mul_mem (H.inv_mem (m616 H hv hs)) (H.mul_mem (m886 H hv hs) H.one_mem)))

private theorem m1331 : g 1331 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "953,-1235,190")) (hv 11838 (by decide))
    (H.mul_mem (m953 H hv hs) (H.mul_mem (H.inv_mem (m1235 H hv hs)) (H.mul_mem (m190 H hv hs) H.one_mem)))

private theorem m306 : g 306 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-893,-1675")) (hv 11850 (by decide))
    (H.mul_mem (H.inv_mem (m893 H hv hs)) (H.mul_mem (H.inv_mem (m1675 H hv hs)) H.one_mem))

private theorem m1240 : g 1240 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-552,-28,-4")) (hv 11898 (by decide))
    (H.mul_mem (H.inv_mem (m552 H hv hs)) (H.mul_mem (H.inv_mem (m28 H hv hs)) (H.mul_mem (H.inv_mem (m4 H hv hs)) H.one_mem)))

private theorem m484 : g 484 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "836,-804")) (hv 11902 (by decide))
    (H.mul_mem (m836 H hv hs) (H.mul_mem (H.inv_mem (m804 H hv hs)) H.one_mem))

private theorem m1531 : g 1531 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1027,-1319,-893")) (hv 11908 (by decide))
    (H.mul_mem (H.inv_mem (m1027 H hv hs)) (H.mul_mem (H.inv_mem (m1319 H hv hs)) (H.mul_mem (H.inv_mem (m893 H hv hs)) H.one_mem)))

private theorem m1226 : g 1226 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "874,-1516,-752")) (hv 11910 (by decide))
    (H.mul_mem (m874 H hv hs) (H.mul_mem (H.inv_mem (m1516 H hv hs)) (H.mul_mem (H.inv_mem (m752 H hv hs)) H.one_mem)))

private theorem m338 : g 338 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "804,-616,785")) (hv 11916 (by decide))
    (H.mul_mem (m804 H hv hs) (H.mul_mem (H.inv_mem (m616 H hv hs)) (H.mul_mem (m785 H hv hs) H.one_mem)))

private theorem m672 : g 672 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-475,-575,-1925,-475,-1925")) (hv 31087 (by decide))
    (H.mul_mem (H.inv_mem (m475 H hv hs)) (H.mul_mem (H.inv_mem (m575 H hv hs)) (H.mul_mem (H.inv_mem (m1925 H hv hs)) (H.mul_mem (H.inv_mem (m475 H hv hs)) (H.mul_mem (H.inv_mem (m1925 H hv hs)) H.one_mem)))))

private theorem m757 : g 757 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "379,-1704,-379")) (hv 31088 (by decide))
    (H.mul_mem (m379 H hv hs) (H.mul_mem (H.inv_mem (m1704 H hv hs)) (H.mul_mem (H.inv_mem (m379 H hv hs)) H.one_mem)))

private theorem m512 : g 512 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1052,735,906")) (hv 11933 (by decide))
    (H.mul_mem (m1052 H hv hs) (H.mul_mem (m735 H hv hs) (H.mul_mem (m906 H hs) H.one_mem)))

private theorem m1920 : g 1920 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1093,1018,-1348")) (hv 11946 (by decide))
    (H.mul_mem (m1093 H hv hs) (H.mul_mem (m1018 H hv hs) (H.mul_mem (H.inv_mem (m1348 H hv hs)) H.one_mem)))

private theorem m1534 : g 1534 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1091,-533")) (hv 11952 (by decide))
    (H.mul_mem (H.inv_mem (m1091 H hv hs)) (H.mul_mem (H.inv_mem (m533 H hv hs)) H.one_mem))

private theorem m1220 : g 1220 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "28,1594,886")) (hv 11962 (by decide))
    (H.mul_mem (m28 H hv hs) (H.mul_mem (m1594 H hv hs) (H.mul_mem (m886 H hv hs) H.one_mem)))

private theorem m503 : g 503 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "62,-442,-135")) (hv 11968 (by decide))
    (H.mul_mem (m62 H hv hs) (H.mul_mem (H.inv_mem (m442 H hv hs)) (H.mul_mem (H.inv_mem (m135 H hv hs)) H.one_mem)))

private theorem m1259 : g 1259 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-689,475,1925")) (hv 11988 (by decide))
    (H.mul_mem (H.inv_mem (m689 H hv hs)) (H.mul_mem (m475 H hv hs) (H.mul_mem (m1925 H hv hs) H.one_mem)))

private theorem m501 : g 501 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "804,-56")) (hv 11990 (by decide))
    (H.mul_mem (m804 H hv hs) (H.mul_mem (H.inv_mem (m56 H hv hs)) H.one_mem))

private theorem m1611 : g 1611 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1060,-712,-764")) (hv 12012 (by decide))
    (H.mul_mem (H.inv_mem (m1060 H hv hs)) (H.mul_mem (H.inv_mem (m712 H hv hs)) (H.mul_mem (H.inv_mem (m764 H hv hs)) H.one_mem)))

private theorem m985 : g 985 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1824,99,185")) (hv 12028 (by decide))
    (H.mul_mem (m1824 H hv hs) (H.mul_mem (m99 H hv hs) (H.mul_mem (m185 H hv hs) H.one_mem)))

private theorem m792 : g 792 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-195,521,2018")) (hv 12031 (by decide))
    (H.mul_mem (H.inv_mem (m195 H hv hs)) (H.mul_mem (m521 H hv hs) (H.mul_mem (m2018 H hv hs) H.one_mem)))

private theorem m1699 : g 1699 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-320,-1924,-424,853")) (hv 12037 (by decide))
    (H.mul_mem (H.inv_mem (m320 H hv hs)) (H.mul_mem (H.inv_mem (m1924 H hv hs)) (H.mul_mem (H.inv_mem (m424 H hv hs)) (H.mul_mem (m853 H hv hs) H.one_mem))))

private theorem m1013 : g 1013 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-345,1208,602,-1345")) (hv 31089 (by decide))
    (H.mul_mem (H.inv_mem (m345 H hv hs)) (H.mul_mem (m1208 H hv hs) (H.mul_mem (m602 H hv hs) (H.mul_mem (H.inv_mem (m1345 H hv hs)) H.one_mem))))

private theorem m539 : g 539 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1420,1930,-804")) (hv 31090 (by decide))
    (H.mul_mem (H.inv_mem (m1420 H hv hs)) (H.mul_mem (m1930 H hv hs) (H.mul_mem (H.inv_mem (m804 H hv hs)) H.one_mem)))

private theorem m70 : g 70 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-2043,-1030,-874,752")) (hv 12672 (by decide))
    (H.mul_mem (H.inv_mem (m2043 H hv hs)) (H.mul_mem (H.inv_mem (m1030 H hv hs)) (H.mul_mem (H.inv_mem (m874 H hv hs)) (H.mul_mem (m752 H hv hs) H.one_mem))))

private theorem m614 : g 614 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1076,-1026,36")) (hv 31091 (by decide))
    (H.mul_mem (H.inv_mem (m1076 H hv hs)) (H.mul_mem (H.inv_mem (m1026 H hv hs)) (H.mul_mem (m36 H hv hs) H.one_mem)))

private theorem m1615 : g 1615 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "521,241,-1958")) (hv 12690 (by decide))
    (H.mul_mem (m521 H hv hs) (H.mul_mem (m241 H hv hs) (H.mul_mem (H.inv_mem (m1958 H hs)) H.one_mem)))

private theorem m117 : g 117 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-56,-3,-479,-3,56")) (hv 12712 (by decide))
    (H.mul_mem (H.inv_mem (m56 H hv hs)) (H.mul_mem (H.inv_mem (m3 H hs)) (H.mul_mem (H.inv_mem (m479 H hv hs)) (H.mul_mem (H.inv_mem (m3 H hs)) (H.mul_mem (m56 H hv hs) H.one_mem)))))

private theorem m1132 : g 1132 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "429,116,-855")) (hv 12750 (by decide))
    (H.mul_mem (m429 H hv hs) (H.mul_mem (m116 H hv hs) (H.mul_mem (H.inv_mem (m855 H hv hs)) H.one_mem)))

private theorem m1070 : g 1070 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1294,1258,1159,-1093")) (hv 12751 (by decide))
    (H.mul_mem (H.inv_mem (m1294 H hv hs)) (H.mul_mem (m1258 H hv hs) (H.mul_mem (m1159 H hv hs) (H.mul_mem (H.inv_mem (m1093 H hv hs)) H.one_mem))))

private theorem m114 : g 114 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "886,-1620,323")) (hv 12758 (by decide))
    (H.mul_mem (m886 H hv hs) (H.mul_mem (H.inv_mem (m1620 H hv hs)) (H.mul_mem (m323 H hv hs) H.one_mem)))

private theorem m961 : g 961 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1828,-1772,-1147")) (hv 12773 (by decide))
    (H.mul_mem (m1828 H hv hs) (H.mul_mem (H.inv_mem (m1772 H hs)) (H.mul_mem (H.inv_mem (m1147 H hv hs)) H.one_mem)))

private theorem m896 : g 896 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-243,1294,-376")) (hv 12775 (by decide))
    (H.mul_mem (H.inv_mem (m243 H hv hs)) (H.mul_mem (m1294 H hv hs) (H.mul_mem (H.inv_mem (m376 H hv hs)) H.one_mem)))

private theorem m681 : g 681 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-118,-1403,-552")) (hv 12778 (by decide))
    (H.mul_mem (H.inv_mem (m118 H hv hs)) (H.mul_mem (H.inv_mem (m1403 H hv hs)) (H.mul_mem (H.inv_mem (m552 H hv hs)) H.one_mem)))

private theorem m157 : g 157 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-84,-841,429,-323,1620")) (hv 12782 (by decide))
    (H.mul_mem (H.inv_mem (m84 H hv hs)) (H.mul_mem (H.inv_mem (m841 H hv hs)) (H.mul_mem (m429 H hv hs) (H.mul_mem (H.inv_mem (m323 H hv hs)) (H.mul_mem (m1620 H hv hs) H.one_mem)))))

private theorem m553 : g 553 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "23,227,1091")) (hv 12801 (by decide))
    (H.mul_mem (m23 H hs) (H.mul_mem (m227 H hv hs) (H.mul_mem (m1091 H hv hs) H.one_mem)))

private theorem m1197 : g 1197 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "302,1047,312,-981")) (hv 12836 (by decide))
    (H.mul_mem (m302 H hv hs) (H.mul_mem (m1047 H hv hs) (H.mul_mem (m312 H hv hs) (H.mul_mem (H.inv_mem (m981 H hv hs)) H.one_mem))))

private theorem m938 : g 938 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "937,125,1052,735")) (hv 12839 (by decide))
    (H.mul_mem (m937 H hv hs) (H.mul_mem (m125 H hv hs) (H.mul_mem (m1052 H hv hs) (H.mul_mem (m735 H hv hs) H.one_mem))))

private theorem m830 : g 830 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1095,1096,-352,-831")) (hv 12841 (by decide))
    (H.mul_mem (H.inv_mem (m1095 H hv hs)) (H.mul_mem (m1096 H hv hs) (H.mul_mem (H.inv_mem (m352 H hv hs)) (H.mul_mem (H.inv_mem (m831 H hv hs)) H.one_mem))))

private theorem m1509 : g 1509 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-99,1843,-80")) (hv 12860 (by decide))
    (H.mul_mem (H.inv_mem (m99 H hv hs)) (H.mul_mem (m1843 H hv hs) (H.mul_mem (H.inv_mem (m80 H hv hs)) H.one_mem)))

private theorem m771 : g 771 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "112,-147,841,416")) (hv 12877 (by decide))
    (H.mul_mem (m112 H hv hs) (H.mul_mem (H.inv_mem (m147 H hv hs)) (H.mul_mem (m841 H hv hs) (H.mul_mem (m416 H hv hs) H.one_mem))))

private theorem m578 : g 578 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-161,-1106,1319,429")) (hv 12879 (by decide))
    (H.mul_mem (H.inv_mem (m161 H hv hs)) (H.mul_mem (H.inv_mem (m1106 H hs)) (H.mul_mem (m1319 H hv hs) (H.mul_mem (m429 H hv hs) H.one_mem))))

private theorem m1510 : g 1510 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1824,-1649,-1096")) (hv 12904 (by decide))
    (H.mul_mem (H.inv_mem (m1824 H hv hs)) (H.mul_mem (H.inv_mem (m1649 H hv hs)) (H.mul_mem (H.inv_mem (m1096 H hv hs)) H.one_mem)))

private theorem m1180 : g 1180 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "526,180,1091")) (hv 12906 (by decide))
    (H.mul_mem (m526 H hv hs) (H.mul_mem (m180 H hv hs) (H.mul_mem (m1091 H hv hs) H.one_mem)))

private theorem m403 : g 403 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1828,1321,-180")) (hv 13635 (by decide))
    (H.mul_mem (m1828 H hv hs) (H.mul_mem (m1321 H hv hs) (H.mul_mem (H.inv_mem (m180 H hv hs)) H.one_mem)))

private theorem m759 : g 759 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "748,-224,147,581,-729")) (hv 13644 (by decide))
    (H.mul_mem (m748 H hv hs) (H.mul_mem (H.inv_mem (m224 H hv hs)) (H.mul_mem (m147 H hv hs) (H.mul_mem (m581 H hv hs) (H.mul_mem (H.inv_mem (m729 H hv hs)) H.one_mem)))))

private theorem m704 : g 704 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1686,732,-1060")) (hv 13647 (by decide))
    (H.mul_mem (m1686 H hv hs) (H.mul_mem (m732 H hv hs) (H.mul_mem (H.inv_mem (m1060 H hv hs)) H.one_mem)))

private theorem m133 : g 133 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-255,745,-1574,1294")) (hv 13649 (by decide))
    (H.mul_mem (H.inv_mem (m255 H hv hs)) (H.mul_mem (m745 H hv hs) (H.mul_mem (H.inv_mem (m1574 H hv hs)) (H.mul_mem (m1294 H hv hs) H.one_mem))))

private theorem m1211 : g 1211 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-197,738,-1096,-8")) (hv 13681 (by decide))
    (H.mul_mem (H.inv_mem (m197 H hv hs)) (H.mul_mem (m738 H hv hs) (H.mul_mem (H.inv_mem (m1096 H hv hs)) (H.mul_mem (H.inv_mem (m8 H hv hs)) H.one_mem))))

private theorem m790 : g 790 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "841,-231,-1378,-416")) (hv 31092 (by decide))
    (H.mul_mem (m841 H hv hs) (H.mul_mem (H.inv_mem (m231 H hv hs)) (H.mul_mem (H.inv_mem (m1378 H hv hs)) (H.mul_mem (H.inv_mem (m416 H hv hs)) H.one_mem))))

private theorem m160 : g 160 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1621,-1675,354,-1367")) (hv 31093 (by decide))
    (H.mul_mem (m1621 H hv hs) (H.mul_mem (H.inv_mem (m1675 H hv hs)) (H.mul_mem (m354 H hv hs) (H.mul_mem (H.inv_mem (m1367 H hv hs)) H.one_mem))))

private theorem m627 : g 627 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1972,-1671,-1083,-1455")) (hv 13712 (by decide))
    (H.mul_mem (H.inv_mem (m1972 H hs)) (H.mul_mem (H.inv_mem (m1671 H hv hs)) (H.mul_mem (H.inv_mem (m1083 H hv hs)) (H.mul_mem (H.inv_mem (m1455 H hv hs)) H.one_mem))))

private theorem m126 : g 126 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "125,319,-893,-1675")) (hv 31094 (by decide))
    (H.mul_mem (m125 H hv hs) (H.mul_mem (m319 H hv hs) (H.mul_mem (H.inv_mem (m893 H hv hs)) (H.mul_mem (H.inv_mem (m1675 H hv hs)) H.one_mem))))

private theorem m613 : g 613 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "352,-1765,1258,-1026")) (hv 13725 (by decide))
    (H.mul_mem (m352 H hv hs) (H.mul_mem (H.inv_mem (m1765 H hv hs)) (H.mul_mem (m1258 H hv hs) (H.mul_mem (H.inv_mem (m1026 H hv hs)) H.one_mem))))

private theorem m1764 : g 1764 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1809,867,1112,-422")) (hv 13740 (by decide))
    (H.mul_mem (H.inv_mem (m1809 H hv hs)) (H.mul_mem (m867 H hv hs) (H.mul_mem (m1112 H hv hs) (H.mul_mem (H.inv_mem (m422 H hs)) H.one_mem))))

private theorem m851 : g 851 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-442,-1645,780,-1824")) (hv 13756 (by decide))
    (H.mul_mem (H.inv_mem (m442 H hv hs)) (H.mul_mem (H.inv_mem (m1645 H hv hs)) (H.mul_mem (m780 H hv hs) (H.mul_mem (H.inv_mem (m1824 H hv hs)) H.one_mem))))

private theorem m1359 : g 1359 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1741,526,-736,-30,602")) (hv 13809 (by decide))
    (H.mul_mem (m1741 H hv hs) (H.mul_mem (m526 H hv hs) (H.mul_mem (H.inv_mem (m736 H hv hs)) (H.mul_mem (H.inv_mem (m30 H hv hs)) (H.mul_mem (m602 H hv hs) H.one_mem)))))

private theorem m483 : g 483 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-764,-863,-2018,-521")) (hv 13837 (by decide))
    (H.mul_mem (H.inv_mem (m764 H hv hs)) (H.mul_mem (H.inv_mem (m863 H hv hs)) (H.mul_mem (H.inv_mem (m2018 H hv hs)) (H.mul_mem (H.inv_mem (m521 H hv hs)) H.one_mem))))

private theorem m5 : g 5 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-804,-237,1972,-273")) (hv 13894 (by decide))
    (H.mul_mem (H.inv_mem (m804 H hv hs)) (H.mul_mem (H.inv_mem (m237 H hv hs)) (H.mul_mem (m1972 H hs) (H.mul_mem (H.inv_mem (m273 H hs)) H.one_mem))))

private theorem m1334 : g 1334 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-107,-1,-1394,-1772,-1848,-42")) (hv 31095 (by decide))
    (H.mul_mem (H.inv_mem (m107 H hv hs)) (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (H.inv_mem (m1394 H hv hs)) (H.mul_mem (H.inv_mem (m1772 H hs)) (H.mul_mem (H.inv_mem (m1848 H hv hs)) (H.mul_mem (H.inv_mem (m42 H hv hs)) H.one_mem))))))

private theorem m1011 : g 1011 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-688,348,-1,861,-1,688")) (hv 14779 (by decide))
    (H.mul_mem (H.inv_mem (m688 H hs)) (H.mul_mem (m348 H hs) (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (m861 H hv hs) (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (m688 H hs) H.one_mem))))))

private theorem m456 : g 456 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-348,-1053,-442")) (hv 14790 (by decide))
    (H.mul_mem (H.inv_mem (m348 H hs)) (H.mul_mem (H.inv_mem (m1053 H hv hs)) (H.mul_mem (H.inv_mem (m442 H hv hs)) H.one_mem)))

private theorem m1729 : g 1729 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1848,19,743,416,1649")) (hv 31096 (by decide))
    (H.mul_mem (m1848 H hv hs) (H.mul_mem (m19 H hv hs) (H.mul_mem (m743 H hv hs) (H.mul_mem (m416 H hv hs) (H.mul_mem (m1649 H hv hs) H.one_mem)))))

private theorem m1964 : g 1964 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1096,-799,1208,581,216")) (hv 31097 (by decide))
    (H.mul_mem (m1096 H hv hs) (H.mul_mem (H.inv_mem (m799 H hv hs)) (H.mul_mem (m1208 H hv hs) (H.mul_mem (m581 H hv hs) (H.mul_mem (m216 H hv hs) H.one_mem)))))

private theorem m1398 : g 1398 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-688,1499,-20,1621,-1848,77")) (hv 14852 (by decide))
    (H.mul_mem (H.inv_mem (m688 H hs)) (H.mul_mem (m1499 H hv hs) (H.mul_mem (H.inv_mem (m20 H hv hs)) (H.mul_mem (m1621 H hv hs) (H.mul_mem (H.inv_mem (m1848 H hv hs)) (H.mul_mem (m77 H hv hs) H.one_mem))))))

private theorem m866 : g 866 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "109,243,-109,-459,-860,861")) (hv 14854 (by decide))
    (H.mul_mem (m109 H hv hs) (H.mul_mem (m243 H hv hs) (H.mul_mem (H.inv_mem (m109 H hv hs)) (H.mul_mem (H.inv_mem (m459 H hv hs)) (H.mul_mem (H.inv_mem (m860 H hv hs)) (H.mul_mem (m861 H hv hs) H.one_mem))))))

private theorem m1874 : g 1874 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "743,-268,1704,268,758,-738,20")) (hv 14862 (by decide))
    (H.mul_mem (m743 H hv hs) (H.mul_mem (H.inv_mem (m268 H hv hs)) (H.mul_mem (m1704 H hv hs) (H.mul_mem (m268 H hv hs) (H.mul_mem (m758 H hv hs) (H.mul_mem (H.inv_mem (m738 H hv hs)) (H.mul_mem (m20 H hv hs) H.one_mem)))))))

private theorem m1335 : g 1335 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-107,-1,312,-189,-1190,1675,893")) (hv 31098 (by decide))
    (H.mul_mem (H.inv_mem (m107 H hv hs)) (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (m312 H hv hs) (H.mul_mem (H.inv_mem (m189 H hv hs)) (H.mul_mem (H.inv_mem (m1190 H hv hs)) (H.mul_mem (m1675 H hv hs) (H.mul_mem (m893 H hv hs) H.one_mem)))))))

private theorem m1693 : g 1693 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-189,-1765,-855,712,-1345,-1057")) (hv 31099 (by decide))
    (H.mul_mem (H.inv_mem (m189 H hv hs)) (H.mul_mem (H.inv_mem (m1765 H hv hs)) (H.mul_mem (H.inv_mem (m855 H hv hs)) (H.mul_mem (m712 H hv hs) (H.mul_mem (H.inv_mem (m1345 H hv hs)) (H.mul_mem (H.inv_mem (m1057 H hv hs)) H.one_mem))))))

private theorem m1565 : g 1565 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "442,1053,890,125,-1")) (hv 14863 (by decide))
    (H.mul_mem (m442 H hv hs) (H.mul_mem (m1053 H hv hs) (H.mul_mem (m890 H hv hs) (H.mul_mem (m125 H hv hs) (H.mul_mem (H.inv_mem (m1 H hs)) H.one_mem)))))

private theorem m1556 : g 1556 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "195,-255,-863,-2018,-521")) (hv 14880 (by decide))
    (H.mul_mem (m195 H hv hs) (H.mul_mem (H.inv_mem (m255 H hv hs)) (H.mul_mem (H.inv_mem (m863 H hv hs)) (H.mul_mem (H.inv_mem (m2018 H hv hs)) (H.mul_mem (H.inv_mem (m521 H hv hs)) H.one_mem)))))

private theorem m1062 : g 1062 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-803,-1649,-1096,-1574")) (hv 14961 (by decide))
    (H.mul_mem (H.inv_mem (m803 H hv hs)) (H.mul_mem (H.inv_mem (m1649 H hv hs)) (H.mul_mem (H.inv_mem (m1096 H hv hs)) (H.mul_mem (H.inv_mem (m1574 H hv hs)) H.one_mem))))

private theorem m837 : g 837 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "422,-416,415,533,161")) (hv 14968 (by decide))
    (H.mul_mem (m422 H hs) (H.mul_mem (H.inv_mem (m416 H hv hs)) (H.mul_mem (m415 H hv hs) (H.mul_mem (m533 H hv hs) (H.mul_mem (m161 H hv hs) H.one_mem)))))

private theorem m786 : g 786 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1,-348,1,-861,1516,1451")) (hv 31100 (by decide))
    (H.mul_mem (m1 H hs) (H.mul_mem (H.inv_mem (m348 H hs)) (H.mul_mem (m1 H hs) (H.mul_mem (H.inv_mem (m861 H hv hs)) (H.mul_mem (m1516 H hv hs) (H.mul_mem (m1451 H hv hs) H.one_mem))))))

private theorem m129 : g 129 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1703,-1321,1401")) (hv 15960 (by decide))
    (H.mul_mem (m1703 H hv hs) (H.mul_mem (H.inv_mem (m1321 H hv hs)) (H.mul_mem (m1401 H hv hs) H.one_mem)))

private theorem m573 : g 573 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "148,-1235,459,-243,1294,-376,-459,-574")) (hv 31101 (by decide))
    (H.mul_mem (m148 H hv hs) (H.mul_mem (H.inv_mem (m1235 H hv hs)) (H.mul_mem (m459 H hv hs) (H.mul_mem (H.inv_mem (m243 H hv hs)) (H.mul_mem (m1294 H hv hs) (H.mul_mem (H.inv_mem (m376 H hv hs)) (H.mul_mem (H.inv_mem (m459 H hv hs)) (H.mul_mem (H.inv_mem (m574 H hv hs)) H.one_mem))))))))

private theorem m47 : g 47 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-442,-1168,-1405")) (hv 16016 (by decide))
    (H.mul_mem (H.inv_mem (m442 H hv hs)) (H.mul_mem (H.inv_mem (m1168 H hv hs)) (H.mul_mem (H.inv_mem (m1405 H hv hs)) H.one_mem)))

private theorem m1357 : g 1357 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-192,-1258,-1273,675,-1076,-1258,-243")) (hv 31102 (by decide))
    (H.mul_mem (H.inv_mem (m192 H hv hs)) (H.mul_mem (H.inv_mem (m1258 H hv hs)) (H.mul_mem (H.inv_mem (m1273 H hv hs)) (H.mul_mem (m675 H hv hs) (H.mul_mem (H.inv_mem (m1076 H hv hs)) (H.mul_mem (H.inv_mem (m1258 H hv hs)) (H.mul_mem (H.inv_mem (m243 H hv hs)) H.one_mem)))))))

private theorem m1015 : g 1015 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-77,-1168,-1,861,-1,348,-758")) (hv 16034 (by decide))
    (H.mul_mem (H.inv_mem (m77 H hv hs)) (H.mul_mem (H.inv_mem (m1168 H hv hs)) (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (m861 H hv hs) (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (m348 H hs) (H.mul_mem (H.inv_mem (m758 H hv hs)) H.one_mem)))))))

private theorem m987 : g 987 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-442,-288,-288,-288")) (hv 16081 (by decide))
    (H.mul_mem (H.inv_mem (m442 H hv hs)) (H.mul_mem (H.inv_mem (m288 H hv hs)) (H.mul_mem (H.inv_mem (m288 H hv hs)) (H.mul_mem (H.inv_mem (m288 H hv hs)) H.one_mem))))

private theorem m978 : g 978 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "675,-1662,-109,-250,-449,-1428,1053,-1848")) (hv 31103 (by decide))
    (H.mul_mem (m675 H hv hs) (H.mul_mem (H.inv_mem (m1662 H hv hs)) (H.mul_mem (H.inv_mem (m109 H hv hs)) (H.mul_mem (H.inv_mem (m250 H hv hs)) (H.mul_mem (H.inv_mem (m449 H hv hs)) (H.mul_mem (H.inv_mem (m1428 H hv hs)) (H.mul_mem (m1053 H hv hs) (H.mul_mem (H.inv_mem (m1848 H hv hs)) H.one_mem))))))))

private theorem m1032 : g 1032 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1401,1057,-345,1208,581,-729")) (hv 17576 (by decide))
    (H.mul_mem (H.inv_mem (m1401 H hv hs)) (H.mul_mem (m1057 H hv hs) (H.mul_mem (H.inv_mem (m345 H hv hs)) (H.mul_mem (m1208 H hv hs) (H.mul_mem (m581 H hv hs) (H.mul_mem (H.inv_mem (m729 H hv hs)) H.one_mem))))))

private theorem m64 : g 64 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-2,1041,-1,1106,-195,1675")) (hv 17624 (by decide))
    (H.mul_mem (H.inv_mem (m2 H hs)) (H.mul_mem (m1041 H hs) (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (m1106 H hs) (H.mul_mem (H.inv_mem (m195 H hv hs)) (H.mul_mem (m1675 H hv hs) H.one_mem))))))

private theorem m1555 : g 1555 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-284,1,-208,3,729,-780,588,1401")) (hv 31104 (by decide))
    (H.mul_mem (H.inv_mem (m284 H hv hs)) (H.mul_mem (m1 H hs) (H.mul_mem (H.inv_mem (m208 H hv hs)) (H.mul_mem (m3 H hs) (H.mul_mem (m729 H hv hs) (H.mul_mem (H.inv_mem (m780 H hv hs)) (H.mul_mem (m588 H hv hs) (H.mul_mem (m1401 H hv hs) H.one_mem))))))))

private theorem m1841 : g 1841 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-5")) (hv 5059 (by decide))
    (H.mul_mem (H.inv_mem (m5 H hv hs)) H.one_mem)

private theorem m1725 : g 1725 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1555")) (hv 5799 (by decide))
    (H.mul_mem (H.inv_mem (m1555 H hv hs)) H.one_mem)

private theorem m693 : g 693 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-70")) (hv 4901 (by decide))
    (H.mul_mem (H.inv_mem (m70 H hv hs)) H.one_mem)

private theorem m1444 : g 1444 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-126")) (hv 4870 (by decide))
    (H.mul_mem (H.inv_mem (m126 H hv hs)) H.one_mem)

private theorem m1069 : g 1069 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-133")) (hv 5126 (by decide))
    (H.mul_mem (H.inv_mem (m133 H hv hs)) H.one_mem)

private theorem m1477 : g 1477 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-306")) (hv 4684 (by decide))
    (H.mul_mem (H.inv_mem (m306 H hv hs)) H.one_mem)

private theorem m1696 : g 1696 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-403")) (hv 4766 (by decide))
    (H.mul_mem (H.inv_mem (m403 H hv hs)) H.one_mem)

private theorem m1595 : g 1595 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-456")) (hv 5519 (by decide))
    (H.mul_mem (H.inv_mem (m456 H hv hs)) H.one_mem)

private theorem m1635 : g 1635 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-484")) (hv 31105 (by decide))
    (H.mul_mem (H.inv_mem (m484 H hv hs)) H.one_mem)

private theorem m1840 : g 1840 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-486")) (hv 5528 (by decide))
    (H.mul_mem (H.inv_mem (m486 H hv hs)) H.one_mem)

private theorem m1077 : g 1077 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-501")) (hv 5255 (by decide))
    (H.mul_mem (H.inv_mem (m501 H hv hs)) H.one_mem)

private theorem m1303 : g 1303 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-503")) (hv 4872 (by decide))
    (H.mul_mem (H.inv_mem (m503 H hv hs)) H.one_mem)

private theorem m1084 : g 1084 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-512")) (hv 5609 (by decide))
    (H.mul_mem (H.inv_mem (m512 H hv hs)) H.one_mem)

private theorem m1110 : g 1110 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-553")) (hv 4731 (by decide))
    (H.mul_mem (H.inv_mem (m553 H hv hs)) H.one_mem)

private theorem m1199 : g 1199 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-578")) (hv 4880 (by decide))
    (H.mul_mem (H.inv_mem (m578 H hv hs)) H.one_mem)

private theorem m777 : g 777 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-681")) (hv 5131 (by decide))
    (H.mul_mem (H.inv_mem (m681 H hv hs)) H.one_mem)

private theorem m1873 : g 1873 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-704")) (hv 5117 (by decide))
    (H.mul_mem (H.inv_mem (m704 H hv hs)) H.one_mem)

private theorem m1500 : g 1500 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-771")) (hv 5689 (by decide))
    (H.mul_mem (H.inv_mem (m771 H hv hs)) H.one_mem)

private theorem m1932 : g 1932 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-786")) (hv 5264 (by decide))
    (H.mul_mem (H.inv_mem (m786 H hv hs)) H.one_mem)

private theorem m1752 : g 1752 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-866")) (hv 31106 (by decide))
    (H.mul_mem (H.inv_mem (m866 H hv hs)) H.one_mem)

private theorem m991 : g 991 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-961")) (hv 4660 (by decide))
    (H.mul_mem (H.inv_mem (m961 H hv hs)) H.one_mem)

private theorem m1728 : g 1728 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-978")) (hv 5490 (by decide))
    (H.mul_mem (H.inv_mem (m978 H hv hs)) H.one_mem)

private theorem m1071 : g 1071 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1015")) (hv 5587 (by decide))
    (H.mul_mem (H.inv_mem (m1015 H hv hs)) H.one_mem)

private theorem m1487 : g 1487 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1132")) (hv 5205 (by decide))
    (H.mul_mem (H.inv_mem (m1132 H hv hs)) H.one_mem)

private theorem m1636 : g 1636 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1197")) (hv 5410 (by decide))
    (H.mul_mem (H.inv_mem (m1197 H hv hs)) H.one_mem)

private theorem m1795 : g 1795 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1211")) (hv 5421 (by decide))
    (H.mul_mem (H.inv_mem (m1211 H hv hs)) H.one_mem)

private theorem m1820 : g 1820 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1334")) (hv 5423 (by decide))
    (H.mul_mem (H.inv_mem (m1334 H hv hs)) H.one_mem)

private theorem m1663 : g 1663 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1398")) (hv 5582 (by decide))
    (H.mul_mem (H.inv_mem (m1398 H hv hs)) H.one_mem)

private theorem m1885 : g 1885 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1458")) (hv 31107 (by decide))
    (H.mul_mem (H.inv_mem (m1458 H hv hs)) H.one_mem)

private theorem m1681 : g 1681 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1568")) (hv 5762 (by decide))
    (H.mul_mem (H.inv_mem (m1568 H hv hs)) H.one_mem)

private theorem m1718 : g 1718 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1611")) (hv 5843 (by decide))
    (H.mul_mem (H.inv_mem (m1611 H hv hs)) H.one_mem)

private theorem m1769 : g 1769 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1764")) (hv 31108 (by decide))
    (H.mul_mem (H.inv_mem (m1764 H hv hs)) H.one_mem)

private theorem m1893 : g 1893 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1853")) (hv 31109 (by decide))
    (H.mul_mem (H.inv_mem (m1853 H hv hs)) H.one_mem)

private theorem m1073 : g 1073 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1729,-1985")) (hv 10072 (by decide))
    (H.mul_mem (H.inv_mem (m1729 H hv hs)) (H.mul_mem (H.inv_mem (m1985 H hv hs)) H.one_mem))

private theorem m1808 : g 1808 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-539,-37,-501")) (hv 10081 (by decide))
    (H.mul_mem (H.inv_mem (m539 H hv hs)) (H.mul_mem (H.inv_mem (m37 H hv hs)) (H.mul_mem (H.inv_mem (m501 H hv hs)) H.one_mem)))

private theorem m1495 : g 1495 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1335,-254")) (hv 10084 (by decide))
    (H.mul_mem (H.inv_mem (m1335 H hv hs)) (H.mul_mem (H.inv_mem (m254 H hv hs)) H.one_mem))

private theorem m1904 : g 1904 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "890,-47")) (hv 10130 (by decide))
    (H.mul_mem (m890 H hv hs) (H.mul_mem (H.inv_mem (m47 H hv hs)) H.one_mem))

private theorem m1657 : g 1657 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "573,1")) (hv 10193 (by decide))
    (H.mul_mem (m573 H hv hs) (H.mul_mem (m1 H hs) H.one_mem))

private theorem m951 : g 951 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1062,-243")) (hv 10201 (by decide))
    (H.mul_mem (m1062 H hv hs) (H.mul_mem (H.inv_mem (m243 H hv hs)) H.one_mem))

private theorem m912 : g 912 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-627,-1020")) (hv 10265 (by decide))
    (H.mul_mem (H.inv_mem (m627 H hv hs)) (H.mul_mem (H.inv_mem (m1020 H hv hs)) H.one_mem))

private theorem m516 : g 516 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1565,-1118")) (hv 10271 (by decide))
    (H.mul_mem (H.inv_mem (m1565 H hv hs)) (H.mul_mem (H.inv_mem (m1118 H hv hs)) H.one_mem))

private theorem m824 : g 824 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-987,-1675")) (hv 11014 (by decide))
    (H.mul_mem (H.inv_mem (m987 H hv hs)) (H.mul_mem (H.inv_mem (m1675 H hv hs)) H.one_mem))

private theorem m806 : g 806 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1070,-1294,-1062")) (hv 11045 (by decide))
    (H.mul_mem (H.inv_mem (m1070 H hv hs)) (H.mul_mem (H.inv_mem (m1294 H hv hs)) (H.mul_mem (H.inv_mem (m1062 H hv hs)) H.one_mem)))

private theorem m1173 : g 1173 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-189,985")) (hv 11053 (by decide))
    (H.mul_mem (H.inv_mem (m189 H hv hs)) (H.mul_mem (m985 H hv hs) H.one_mem))

private theorem m813 : g 813 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-352,1534")) (hv 11067 (by decide))
    (H.mul_mem (H.inv_mem (m352 H hv hs)) (H.mul_mem (m1534 H hv hs) H.one_mem))

private theorem m477 : g 477 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1874,-1264,-715")) (hv 11076 (by decide))
    (H.mul_mem (H.inv_mem (m1874 H hv hs)) (H.mul_mem (H.inv_mem (m1264 H hv hs)) (H.mul_mem (H.inv_mem (m715 H hv hs)) H.one_mem)))

private theorem m261 : g 261 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "578,-255,-195")) (hv 11185 (by decide))
    (H.mul_mem (m578 H hv hs) (H.mul_mem (H.inv_mem (m255 H hv hs)) (H.mul_mem (H.inv_mem (m195 H hv hs)) H.one_mem)))

private theorem m219 : g 219 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-27,-683,-114")) (hv 11186 (by decide))
    (H.mul_mem (H.inv_mem (m27 H hv hs)) (H.mul_mem (H.inv_mem (m683 H hv hs)) (H.mul_mem (H.inv_mem (m114 H hv hs)) H.one_mem)))

private theorem m1914 : g 1914 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1168,442,-64")) (hv 31110 (by decide))
    (H.mul_mem (m1168 H hv hs) (H.mul_mem (m442 H hv hs) (H.mul_mem (H.inv_mem (m64 H hv hs)) H.one_mem)))

private theorem m791 : g 791 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-77,1729,-956")) (hv 11839 (by decide))
    (H.mul_mem (H.inv_mem (m77 H hv hs)) (H.mul_mem (m1729 H hv hs) (H.mul_mem (H.inv_mem (m956 H hv hs)) H.one_mem)))

private theorem m1982 : g 1982 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1401,858,129")) (hv 11869 (by decide))
    (H.mul_mem (H.inv_mem (m1401 H hv hs)) (H.mul_mem (m858 H hv hs) (H.mul_mem (m129 H hv hs) H.one_mem)))

private theorem m1515 : g 1515 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "786,-1451,-1516")) (hv 11877 (by decide))
    (H.mul_mem (m786 H hv hs) (H.mul_mem (H.inv_mem (m1451 H hv hs)) (H.mul_mem (H.inv_mem (m1516 H hv hs)) H.one_mem)))

private theorem m626 : g 626 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "627,1455,-639")) (hv 11884 (by decide))
    (H.mul_mem (m627 H hv hs) (H.mul_mem (m1455 H hv hs) (H.mul_mem (H.inv_mem (m639 H hv hs)) H.one_mem)))

private theorem m767 : g 767 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-588,208,-1509")) (hv 11900 (by decide))
    (H.mul_mem (H.inv_mem (m588 H hv hs)) (H.mul_mem (m208 H hv hs) (H.mul_mem (H.inv_mem (m1509 H hv hs)) H.one_mem)))

private theorem m1016 : g 1016 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1015,-84,72")) (hv 11930 (by decide))
    (H.mul_mem (m1015 H hv hs) (H.mul_mem (H.inv_mem (m84 H hv hs)) (H.mul_mem (m72 H hv hs) H.one_mem)))

private theorem m1385 : g 1385 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1408,161,-837")) (hv 11955 (by decide))
    (H.mul_mem (H.inv_mem (m1408 H hv hs)) (H.mul_mem (m161 H hv hs) (H.mul_mem (H.inv_mem (m837 H hv hs)) H.one_mem)))

private theorem m1116 : g 1116 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1319,-1451,-987,893")) (hv 11963 (by decide))
    (H.mul_mem (m1319 H hv hs) (H.mul_mem (H.inv_mem (m1451 H hv hs)) (H.mul_mem (H.inv_mem (m987 H hv hs)) (H.mul_mem (m893 H hv hs) H.one_mem))))

private theorem m999 : g 999 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-459,1432,-1011,-1432,459")) (hv 31111 (by decide))
    (H.mul_mem (H.inv_mem (m459 H hv hs)) (H.mul_mem (m1432 H hv hs) (H.mul_mem (H.inv_mem (m1011 H hv hs)) (H.mul_mem (H.inv_mem (m1432 H hv hs)) (H.mul_mem (m459 H hv hs) H.one_mem)))))

private theorem m205 : g 205 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1615,521,-312")) (hv 11989 (by decide))
    (H.mul_mem (H.inv_mem (m1615 H hv hs)) (H.mul_mem (m521 H hv hs) (H.mul_mem (H.inv_mem (m312 H hv hs)) H.one_mem)))

private theorem m420 : g 420 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1359,-983,-1206,-1649")) (hv 11993 (by decide))
    (H.mul_mem (H.inv_mem (m1359 H hv hs)) (H.mul_mem (H.inv_mem (m983 H hv hs)) (H.mul_mem (H.inv_mem (m1206 H hv hs)) (H.mul_mem (H.inv_mem (m1649 H hv hs)) H.one_mem))))

private theorem m460 : g 460 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1703,-704,1686")) (hv 12033 (by decide))
    (H.mul_mem (H.inv_mem (m1703 H hv hs)) (H.mul_mem (H.inv_mem (m704 H hv hs)) (H.mul_mem (m1686 H hv hs) H.one_mem)))

private theorem m163 : g 163 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1112,1062,-874")) (hv 12677 (by decide))
    (H.mul_mem (m1112 H hv hs) (H.mul_mem (m1062 H hv hs) (H.mul_mem (H.inv_mem (m874 H hv hs)) H.one_mem)))

private theorem m435 : g 435 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-12,101,1359")) (hv 12688 (by decide))
    (H.mul_mem (H.inv_mem (m12 H hv hs)) (H.mul_mem (m101 H hv hs) (H.mul_mem (m1359 H hv hs) H.one_mem)))

private theorem m91 : g 91 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1401,-1555,590")) (hv 31112 (by decide))
    (H.mul_mem (m1401 H hv hs) (H.mul_mem (H.inv_mem (m1555 H hv hs)) (H.mul_mem (m590 H hv hs) H.one_mem)))

private theorem m717 : g 717 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-745,863,-1060,-704")) (hv 12786 (by decide))
    (H.mul_mem (H.inv_mem (m745 H hv hs)) (H.mul_mem (m863 H hv hs) (H.mul_mem (H.inv_mem (m1060 H hv hs)) (H.mul_mem (H.inv_mem (m704 H hv hs)) H.one_mem))))

private theorem m760 : g 760 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1032,-129,-1345")) (hv 12800 (by decide))
    (H.mul_mem (H.inv_mem (m1032 H hv hs)) (H.mul_mem (H.inv_mem (m129 H hv hs)) (H.mul_mem (H.inv_mem (m1345 H hv hs)) H.one_mem)))

private theorem m81 : g 81 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1015,449,-1057,-588")) (hv 12823 (by decide))
    (H.mul_mem (m1015 H hv hs) (H.mul_mem (m449 H hv hs) (H.mul_mem (H.inv_mem (m1057 H hv hs)) (H.mul_mem (H.inv_mem (m588 H hv hs)) H.one_mem))))

private theorem m908 : g 908 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "933,-1190,-1556,1190,-933")) (hv 12848 (by decide))
    (H.mul_mem (m933 H hv hs) (H.mul_mem (H.inv_mem (m1190 H hv hs)) (H.mul_mem (H.inv_mem (m1556 H hv hs)) (H.mul_mem (m1190 H hv hs) (H.mul_mem (H.inv_mem (m933 H hv hs)) H.one_mem)))))

private theorem m1544 : g 1544 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-893,987,241,-1958")) (hv 12875 (by decide))
    (H.mul_mem (H.inv_mem (m893 H hv hs)) (H.mul_mem (m987 H hv hs) (H.mul_mem (m241 H hv hs) (H.mul_mem (H.inv_mem (m1958 H hs)) H.one_mem))))

private theorem m952 : g 952 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1062,-243,970")) (hv 12880 (by decide))
    (H.mul_mem (m1062 H hv hs) (H.mul_mem (H.inv_mem (m243 H hv hs)) (H.mul_mem (m970 H hv hs) H.one_mem)))

private theorem m40 : g 40 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "214,1764,-93,1735")) (hv 12902 (by decide))
    (H.mul_mem (m214 H hv hs) (H.mul_mem (m1764 H hv hs) (H.mul_mem (H.inv_mem (m93 H hv hs)) (H.mul_mem (m1735 H hv hs) H.one_mem))))

private theorem m787 : g 787 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-149,-1,-866,970,148")) (hv 31113 (by decide))
    (H.mul_mem (H.inv_mem (m149 H hv hs)) (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (H.inv_mem (m866 H hv hs)) (H.mul_mem (m970 H hv hs) (H.mul_mem (m148 H hv hs) H.one_mem)))))

private theorem m394 : g 394 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-893,-64,135")) (hv 12919 (by decide))
    (H.mul_mem (H.inv_mem (m893 H hv hs)) (H.mul_mem (H.inv_mem (m64 H hv hs)) (H.mul_mem (m135 H hv hs) H.one_mem)))

private theorem m1580 : g 1580 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1401,1032,-51,-1032,-1401")) (hv 31114 (by decide))
    (H.mul_mem (m1401 H hv hs) (H.mul_mem (m1032 H hv hs) (H.mul_mem (H.inv_mem (m51 H hv hs)) (H.mul_mem (H.inv_mem (m1032 H hv hs)) (H.mul_mem (H.inv_mem (m1401 H hv hs)) H.one_mem)))))

private theorem m1165 : g 1165 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "697,-799,1208,-129")) (hv 12927 (by decide))
    (H.mul_mem (m697 H hv hs) (H.mul_mem (H.inv_mem (m799 H hv hs)) (H.mul_mem (m1208 H hv hs) (H.mul_mem (H.inv_mem (m129 H hv hs)) H.one_mem))))

private theorem m754 : g 754 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "56,-302,850,-456,-933")) (hv 13645 (by decide))
    (H.mul_mem (m56 H hv hs) (H.mul_mem (H.inv_mem (m302 H hv hs)) (H.mul_mem (m850 H hv hs) (H.mul_mem (H.inv_mem (m456 H hv hs)) (H.mul_mem (H.inv_mem (m933 H hv hs)) H.one_mem)))))

private theorem m1485 : g 1485 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-978,-937,-513,1504")) (hv 13719 (by decide))
    (H.mul_mem (H.inv_mem (m978 H hv hs)) (H.mul_mem (H.inv_mem (m937 H hv hs)) (H.mul_mem (H.inv_mem (m513 H hv hs)) (H.mul_mem (m1504 H hv hs) H.one_mem))))

private theorem m973 : g 973 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-64,135,-780,208")) (hv 13754 (by decide))
    (H.mul_mem (H.inv_mem (m64 H hv hs)) (H.mul_mem (m135 H hv hs) (H.mul_mem (H.inv_mem (m780 H hv hs)) (H.mul_mem (m208 H hv hs) H.one_mem))))

private theorem m1617 : g 1617 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1516,786,-1184,-835,291,-786,1516")) (hv 13791 (by decide))
    (H.mul_mem (H.inv_mem (m1516 H hv hs)) (H.mul_mem (m786 H hv hs) (H.mul_mem (H.inv_mem (m1184 H hv hs)) (H.mul_mem (H.inv_mem (m835 H hv hs)) (H.mul_mem (m291 H hv hs) (H.mul_mem (H.inv_mem (m786 H hv hs)) (H.mul_mem (m1516 H hv hs) H.one_mem)))))))

private theorem m839 : g 839 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "735,558,-1335,1979,-513")) (hv 13815 (by decide))
    (H.mul_mem (m735 H hv hs) (H.mul_mem (m558 H hv hs) (H.mul_mem (H.inv_mem (m1335 H hv hs)) (H.mul_mem (m1979 H hv hs) (H.mul_mem (H.inv_mem (m513 H hv hs)) H.one_mem)))))

private theorem m915 : g 915 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "869,1357,-192,-36,650")) (hv 31115 (by decide))
    (H.mul_mem (m869 H hv hs) (H.mul_mem (m1357 H hv hs) (H.mul_mem (H.inv_mem (m192 H hv hs)) (H.mul_mem (H.inv_mem (m36 H hv hs)) (H.mul_mem (m650 H hv hs) H.one_mem)))))

private theorem m947 : g 947 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1,-987,-1675,-1244")) (hv 13883 (by decide))
    (H.mul_mem (m1 H hs) (H.mul_mem (H.inv_mem (m987 H hv hs)) (H.mul_mem (H.inv_mem (m1675 H hv hs)) (H.mul_mem (H.inv_mem (m1244 H hv hs)) H.one_mem))))

private theorem m333 : g 333 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1188,64,-1675,195")) (hv 13927 (by decide))
    (H.mul_mem (m1188 H hv hs) (H.mul_mem (m64 H hv hs) (H.mul_mem (H.inv_mem (m1675 H hv hs)) (H.mul_mem (m195 H hv hs) H.one_mem))))

private theorem m884 : g 884 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "937,125,-47")) (hv 14756 (by decide))
    (H.mul_mem (m937 H hv hs) (H.mul_mem (m125 H hv hs) (H.mul_mem (H.inv_mem (m47 H hv hs)) H.one_mem)))

private theorem m346 : g 346 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1190,799,-1096,-129")) (hv 14774 (by decide))
    (H.mul_mem (m1190 H hv hs) (H.mul_mem (m799 H hv hs) (H.mul_mem (H.inv_mem (m1096 H hv hs)) (H.mul_mem (H.inv_mem (m129 H hv hs)) H.one_mem))))

private theorem m608 : g 608 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "609,47,-125,-645,122,-735")) (hv 14843 (by decide))
    (H.mul_mem (m609 H hv hs) (H.mul_mem (m47 H hv hs) (H.mul_mem (H.inv_mem (m125 H hv hs)) (H.mul_mem (H.inv_mem (m645 H hv hs)) (H.mul_mem (m122 H hv hs) (H.mul_mem (H.inv_mem (m735 H hv hs)) H.one_mem))))))

private theorem m1085 : g 1085 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1032,-1208,-398,801")) (hv 31116 (by decide))
    (H.mul_mem (H.inv_mem (m1032 H hv hs)) (H.mul_mem (H.inv_mem (m1208 H hv hs)) (H.mul_mem (H.inv_mem (m398 H hv hs)) (H.mul_mem (m801 H hv hs) H.one_mem))))

private theorem m997 : g 997 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-449,-1428,-645,-1574,-109,-1015")) (hv 14898 (by decide))
    (H.mul_mem (H.inv_mem (m449 H hv hs)) (H.mul_mem (H.inv_mem (m1428 H hv hs)) (H.mul_mem (H.inv_mem (m645 H hv hs)) (H.mul_mem (H.inv_mem (m1574 H hv hs)) (H.mul_mem (H.inv_mem (m109 H hv hs)) (H.mul_mem (H.inv_mem (m1015 H hv hs)) H.one_mem))))))

private theorem m776 : g 776 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "214,-1408,214,64,893,1621")) (hv 14899 (by decide))
    (H.mul_mem (m214 H hv hs) (H.mul_mem (H.inv_mem (m1408 H hv hs)) (H.mul_mem (m214 H hv hs) (H.mul_mem (m64 H hv hs) (H.mul_mem (m893 H hv hs) (H.mul_mem (m1621 H hv hs) H.one_mem))))))

private theorem m82 : g 82 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1015,109,352,-1816,736,-1087,634")) (hv 14904 (by decide))
    (H.mul_mem (m1015 H hv hs) (H.mul_mem (m109 H hv hs) (H.mul_mem (m352 H hv hs) (H.mul_mem (H.inv_mem (m1816 H hv hs)) (H.mul_mem (m736 H hv hs) (H.mul_mem (H.inv_mem (m1087 H hv hs)) (H.mul_mem (m634 H hv hs) H.one_mem)))))))

private theorem m926 : g 926 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "688,19,1675,-64")) (hv 15028 (by decide))
    (H.mul_mem (m688 H hs) (H.mul_mem (m19 H hv hs) (H.mul_mem (m1675 H hv hs) (H.mul_mem (H.inv_mem (m64 H hv hs)) H.one_mem))))

private theorem m612 : g 612 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-371,-736,-630,-1555,-581,-1052,-8")) (hv 31117 (by decide))
    (H.mul_mem (H.inv_mem (m371 H hv hs)) (H.mul_mem (H.inv_mem (m736 H hv hs)) (H.mul_mem (H.inv_mem (m630 H hv hs)) (H.mul_mem (H.inv_mem (m1555 H hv hs)) (H.mul_mem (H.inv_mem (m581 H hv hs)) (H.mul_mem (H.inv_mem (m1052 H hv hs)) (H.mul_mem (H.inv_mem (m8 H hv hs)) H.one_mem)))))))

private theorem m1448 : g 1448 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1085")) (hv 5412 (by decide))
    (H.mul_mem (H.inv_mem (m1085 H hv hs)) H.one_mem)

private theorem m934 : g 934 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-91")) (hv 4871 (by decide))
    (H.mul_mem (H.inv_mem (m91 H hv hs)) H.one_mem)

private theorem m1090 : g 1090 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-261")) (hv 5078 (by decide))
    (H.mul_mem (H.inv_mem (m261 H hv hs)) H.one_mem)

private theorem m1706 : g 1706 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-926")) (hv 5222 (by decide))
    (H.mul_mem (H.inv_mem (m926 H hv hs)) H.one_mem)

private theorem m940 : g 940 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-163")) (hv 4658 (by decide))
    (H.mul_mem (H.inv_mem (m163 H hv hs)) H.one_mem)

private theorem m492 : g 492 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-219")) (hv 4753 (by decide))
    (H.mul_mem (H.inv_mem (m219 H hv hs)) H.one_mem)

private theorem m909 : g 909 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-754")) (hv 5344 (by decide))
    (H.mul_mem (H.inv_mem (m754 H hv hs)) H.one_mem)

private theorem m1473 : g 1473 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-346")) (hv 5449 (by decide))
    (H.mul_mem (H.inv_mem (m346 H hv hs)) H.one_mem)

private theorem m849 : g 849 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-435")) (hv 5019 (by decide))
    (H.mul_mem (H.inv_mem (m435 H hv hs)) H.one_mem)

private theorem m1770 : g 1770 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-460")) (hv 5179 (by decide))
    (H.mul_mem (H.inv_mem (m460 H hv hs)) H.one_mem)

private theorem m2040 : g 2040 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-608")) (hv 31118 (by decide))
    (H.mul_mem (H.inv_mem (m608 H hv hs)) H.one_mem)

private theorem m1766 : g 1766 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-612")) (hv 31119 (by decide))
    (H.mul_mem (H.inv_mem (m612 H hv hs)) H.one_mem)

private theorem m1627 : g 1627 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-626")) (hv 5289 (by decide))
    (H.mul_mem (H.inv_mem (m626 H hv hs)) H.one_mem)

private theorem m1160 : g 1160 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-717")) (hv 5288 (by decide))
    (H.mul_mem (H.inv_mem (m717 H hv hs)) H.one_mem)

private theorem m1909 : g 1909 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-767")) (hv 5580 (by decide))
    (H.mul_mem (H.inv_mem (m767 H hv hs)) H.one_mem)

private theorem m1433 : g 1433 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-884")) (hv 5596 (by decide))
    (H.mul_mem (H.inv_mem (m884 H hv hs)) H.one_mem)

private theorem m1476 : g 1476 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-915")) (hv 4961 (by decide))
    (H.mul_mem (H.inv_mem (m915 H hv hs)) H.one_mem)

private theorem m2050 : g 2050 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-951")) (hv 31120 (by decide))
    (H.mul_mem (H.inv_mem (m951 H hv hs)) H.one_mem)

private theorem m1802 : g 1802 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-973")) (hv 31121 (by decide))
    (H.mul_mem (H.inv_mem (m973 H hv hs)) H.one_mem)

private theorem m1584 : g 1584 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1165")) (hv 31122 (by decide))
    (H.mul_mem (H.inv_mem (m1165 H hv hs)) H.one_mem)

private theorem m1822 : g 1822 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1173")) (hv 5841 (by decide))
    (H.mul_mem (H.inv_mem (m1173 H hv hs)) H.one_mem)

private theorem m1490 : g 1490 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1485")) (hv 5489 (by decide))
    (H.mul_mem (H.inv_mem (m1485 H hv hs)) H.one_mem)

private theorem m1927 : g 1927 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1544")) (hv 4677 (by decide))
    (H.mul_mem (H.inv_mem (m1544 H hv hs)) H.one_mem)

private theorem m1464 : g 1464 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1621,-442,-394")) (hv 10106 (by decide))
    (H.mul_mem (m1621 H hv hs) (H.mul_mem (H.inv_mem (m442 H hv hs)) (H.mul_mem (H.inv_mem (m394 H hv hs)) H.one_mem)))

private theorem m1142 : g 1142 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-205,-1615")) (hv 10113 (by decide))
    (H.mul_mem (H.inv_mem (m205 H hv hs)) (H.mul_mem (H.inv_mem (m1615 H hv hs)) H.one_mem))

private theorem m1588 : g 1588 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "27,219")) (hv 10133 (by decide))
    (H.mul_mem (m27 H hv hs) (H.mul_mem (m219 H hv hs) H.one_mem))

private theorem m1454 : g 1454 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1455,1504,-1173")) (hv 10185 (by decide))
    (H.mul_mem (m1455 H hv hs) (H.mul_mem (m1504 H hv hs) (H.mul_mem (H.inv_mem (m1173 H hv hs)) H.one_mem)))

private theorem m636 : g 636 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-293,-952")) (hv 10208 (by decide))
    (H.mul_mem (H.inv_mem (m293 H hv hs)) (H.mul_mem (H.inv_mem (m952 H hv hs)) H.one_mem))

private theorem m1038 : g 1038 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-947,-483")) (hv 10237 (by decide))
    (H.mul_mem (H.inv_mem (m947 H hv hs)) (H.mul_mem (H.inv_mem (m483 H hv hs)) H.one_mem))

private theorem m260 : g 260 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "261,354,-110")) (hv 10243 (by decide))
    (H.mul_mem (m261 H hv hs) (H.mul_mem (m354 H hv hs) (H.mul_mem (H.inv_mem (m110 H hv hs)) H.one_mem)))

private theorem m1121 : g 1121 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-78,-394")) (hv 10263 (by decide))
    (H.mul_mem (H.inv_mem (m78 H hv hs)) (H.mul_mem (H.inv_mem (m394 H hv hs)) H.one_mem))

private theorem m33 : g 33 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-82,-134")) (hv 10280 (by decide))
    (H.mul_mem (H.inv_mem (m82 H hv hs)) (H.mul_mem (H.inv_mem (m134 H hv hs)) H.one_mem))

private theorem m857 : g 857 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1394,-791,-1394")) (hv 11023 (by decide))
    (H.mul_mem (m1394 H hv hs) (H.mul_mem (H.inv_mem (m791 H hv hs)) (H.mul_mem (H.inv_mem (m1394 H hv hs)) H.one_mem)))

private theorem m1664 : g 1664 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1398,-947,588")) (hv 31123 (by decide))
    (H.mul_mem (H.inv_mem (m1398 H hv hs)) (H.mul_mem (H.inv_mem (m947 H hv hs)) (H.mul_mem (m588 H hv hs) H.one_mem)))

private theorem m1001 : g 1001 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1002,-926,1801")) (hv 11177 (by decide))
    (H.mul_mem (m1002 H hv hs) (H.mul_mem (H.inv_mem (m926 H hv hs)) (H.mul_mem (m1801 H hv hs) H.one_mem)))

private theorem m139 : g 139 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-284,-1,-80,-973")) (hv 11905 (by decide))
    (H.mul_mem (H.inv_mem (m284 H hv hs)) (H.mul_mem (H.inv_mem (m1 H hs)) (H.mul_mem (H.inv_mem (m80 H hv hs)) (H.mul_mem (H.inv_mem (m973 H hv hs)) H.one_mem))))

private theorem m1186 : g 1186 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-776,1499,207")) (hv 11912 (by decide))
    (H.mul_mem (H.inv_mem (m776 H hv hs)) (H.mul_mem (m1499 H hv hs) (H.mul_mem (m207 H hv hs) H.one_mem)))

private theorem m1589 : g 1589 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-47,-884")) (hv 11922 (by decide))
    (H.mul_mem (H.inv_mem (m47 H hv hs)) (H.mul_mem (H.inv_mem (m884 H hv hs)) H.one_mem))

private theorem m270 : g 270 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-442,-394,1621")) (hv 11934 (by decide))
    (H.mul_mem (H.inv_mem (m442 H hv hs)) (H.mul_mem (H.inv_mem (m394 H hv hs)) (H.mul_mem (m1621 H hv hs) H.one_mem)))

private theorem m60 : g 60 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1335,-2052,-926,-61")) (hv 12052 (by decide))
    (H.mul_mem (m1335 H hv hs) (H.mul_mem (H.inv_mem (m2052 H hv hs)) (H.mul_mem (H.inv_mem (m926 H hv hs)) (H.mul_mem (H.inv_mem (m61 H hv hs)) H.one_mem))))

private theorem m946 : g 946 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1244,-947,-1556")) (hv 12695 (by decide))
    (H.mul_mem (H.inv_mem (m1244 H hv hs)) (H.mul_mem (H.inv_mem (m947 H hv hs)) (H.mul_mem (H.inv_mem (m1556 H hv hs)) H.one_mem)))

private theorem m620 : g 620 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "1828,-1772,-97,-839")) (hv 12818 (by decide))
    (H.mul_mem (m1828 H hv hs) (H.mul_mem (H.inv_mem (m1772 H hs)) (H.mul_mem (H.inv_mem (m97 H hv hs)) (H.mul_mem (H.inv_mem (m839 H hv hs)) H.one_mem))))

private theorem m545 : g 545 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-260")) (hv 5257 (by decide))
    (H.mul_mem (H.inv_mem (m260 H hv hs)) H.one_mem)

private theorem m1383 : g 1383 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1001")) (hv 4973 (by decide))
    (H.mul_mem (H.inv_mem (m1001 H hv hs)) H.one_mem)

private theorem m1898 : g 1898 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1454")) (hv 4922 (by decide))
    (H.mul_mem (H.inv_mem (m1454 H hv hs)) H.one_mem)

private theorem m1740 : g 1740 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1589")) (hv 5665 (by decide))
    (H.mul_mem (H.inv_mem (m1589 H hv hs)) H.one_mem)

private theorem m1272 : g 1272 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "-1589,1405,-657")) (hv 10188 (by decide))
    (H.mul_mem (H.inv_mem (m1589 H hv hs)) (H.mul_mem (m1405 H hv hs) (H.mul_mem (H.inv_mem (m657 H hv hs)) H.one_mem)))

private theorem m619 : g 619 ∈ H :=
  generator_mem_from_fact H (w := (held_word% "403,-736,-30,-620")) (hv 11927 (by decide))
    (H.mul_mem (m403 H hv hs) (H.mul_mem (H.inv_mem (m736 H hv hs)) (H.mul_mem (H.inv_mem (m30 H hv hs)) (H.mul_mem (H.inv_mem (m620 H hv hs)) H.one_mem))))

private theorem range1 : ∀ n, 1 ≤ n → n < 33 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 1 (m1 H hs)) (range_singleton 2 (m2 H hs))) (range_join (range_singleton 3 (m3 H hs)) (range_singleton 4 (m4 H hv hs)))) (range_join (range_join (range_singleton 5 (m5 H hv hs)) (range_singleton 6 (m6 H hv hs))) (range_join (range_singleton 7 (m7 H hv)) (range_singleton 8 (m8 H hv hs))))) (range_join (range_join (range_join (range_singleton 9 (m9 H hv)) (range_singleton 10 (m10 H hv hs))) (range_join (range_singleton 11 (m11 H hv hs)) (range_singleton 12 (m12 H hv hs)))) (range_join (range_join (range_singleton 13 (m13 H hv)) (range_singleton 14 (m14 H hv hs))) (range_join (range_singleton 15 (m15 H hv)) (range_singleton 16 (m16 H hv)))))) (range_join (range_join (range_join (range_join (range_singleton 17 (m17 H hv)) (range_singleton 18 (m18 H hv))) (range_join (range_singleton 19 (m19 H hv hs)) (range_singleton 20 (m20 H hv hs)))) (range_join (range_join (range_singleton 21 (m21 H hv)) (range_singleton 22 (m22 H hv hs))) (range_join (range_singleton 23 (m23 H hs)) (range_singleton 24 (m24 H hv hs))))) (range_join (range_join (range_join (range_singleton 25 (m25 H hv)) (range_singleton 26 (m26 H hv))) (range_join (range_singleton 27 (m27 H hv hs)) (range_singleton 28 (m28 H hv hs)))) (range_join (range_join (range_singleton 29 (m29 H hv)) (range_singleton 30 (m30 H hv hs))) (range_join (range_singleton 31 (m31 H hv hs)) (range_singleton 32 (m32 H hv)))))))

private theorem range33 : ∀ n, 33 ≤ n → n < 65 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 33 (m33 H hv hs)) (range_singleton 34 (m34 H hv))) (range_join (range_singleton 35 (m35 H hv)) (range_singleton 36 (m36 H hv hs)))) (range_join (range_join (range_singleton 37 (m37 H hv hs)) (range_singleton 38 (m38 H hv hs))) (range_join (range_singleton 39 (m39 H hv hs)) (range_singleton 40 (m40 H hv hs))))) (range_join (range_join (range_join (range_singleton 41 (m41 H hv hs)) (range_singleton 42 (m42 H hv hs))) (range_join (range_singleton 43 (m43 H hv)) (range_singleton 44 (m44 H hv)))) (range_join (range_join (range_singleton 45 (m45 H hv)) (range_singleton 46 (m46 H hv))) (range_join (range_singleton 47 (m47 H hv hs)) (range_singleton 48 (m48 H hv)))))) (range_join (range_join (range_join (range_join (range_singleton 49 (m49 H hv hs)) (range_singleton 50 (m50 H hv))) (range_join (range_singleton 51 (m51 H hv hs)) (range_singleton 52 (m52 H hv)))) (range_join (range_join (range_singleton 53 (m53 H hv hs)) (range_singleton 54 (m54 H hv))) (range_join (range_singleton 55 (m55 H hv)) (range_singleton 56 (m56 H hv hs))))) (range_join (range_join (range_join (range_singleton 57 (m57 H hv)) (range_singleton 58 (m58 H hv))) (range_join (range_singleton 59 (m59 H hv hs)) (range_singleton 60 (m60 H hv hs)))) (range_join (range_join (range_singleton 61 (m61 H hv hs)) (range_singleton 62 (m62 H hv hs))) (range_join (range_singleton 63 (m63 H hv)) (range_singleton 64 (m64 H hv hs)))))))

private theorem range65 : ∀ n, 65 ≤ n → n < 97 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 65 (m65 H hv hs)) (range_singleton 66 (m66 H hv hs))) (range_join (range_singleton 67 (m67 H hv)) (range_singleton 68 (m68 H hv hs)))) (range_join (range_join (range_singleton 69 (m69 H hv)) (range_singleton 70 (m70 H hv hs))) (range_join (range_singleton 71 (m71 H hv)) (range_singleton 72 (m72 H hv hs))))) (range_join (range_join (range_join (range_singleton 73 (m73 H hv hs)) (range_singleton 74 (m74 H hv hs))) (range_join (range_singleton 75 (m75 H hv)) (range_singleton 76 (m76 H hv hs)))) (range_join (range_join (range_singleton 77 (m77 H hv hs)) (range_singleton 78 (m78 H hv hs))) (range_join (range_singleton 79 (m79 H hv)) (range_singleton 80 (m80 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 81 (m81 H hv hs)) (range_singleton 82 (m82 H hv hs))) (range_join (range_singleton 83 (m83 H hv)) (range_singleton 84 (m84 H hv hs)))) (range_join (range_join (range_singleton 85 (m85 H hv)) (range_singleton 86 (m86 H hv))) (range_join (range_singleton 87 (m87 H hv hs)) (range_singleton 88 (m88 H hv hs))))) (range_join (range_join (range_join (range_singleton 89 (m89 H hv hs)) (range_singleton 90 (m90 H hv hs))) (range_join (range_singleton 91 (m91 H hv hs)) (range_singleton 92 (m92 H hv)))) (range_join (range_join (range_singleton 93 (m93 H hv hs)) (range_singleton 94 (m94 H hv))) (range_join (range_singleton 95 (m95 H hv hs)) (range_singleton 96 (m96 H hv)))))))

private theorem range97 : ∀ n, 97 ≤ n → n < 129 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 97 (m97 H hv hs)) (range_singleton 98 (m98 H hv hs))) (range_join (range_singleton 99 (m99 H hv hs)) (range_singleton 100 (m100 H hv)))) (range_join (range_join (range_singleton 101 (m101 H hv hs)) (range_singleton 102 (m102 H hv))) (range_join (range_singleton 103 (m103 H hv)) (range_singleton 104 (m104 H hv hs))))) (range_join (range_join (range_join (range_singleton 105 (m105 H hv)) (range_singleton 106 (m106 H hv hs))) (range_join (range_singleton 107 (m107 H hv hs)) (range_singleton 108 (m108 H hv)))) (range_join (range_join (range_singleton 109 (m109 H hv hs)) (range_singleton 110 (m110 H hv hs))) (range_join (range_singleton 111 (m111 H hv)) (range_singleton 112 (m112 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 113 (m113 H hv hs)) (range_singleton 114 (m114 H hv hs))) (range_join (range_singleton 115 (m115 H hv hs)) (range_singleton 116 (m116 H hv hs)))) (range_join (range_join (range_singleton 117 (m117 H hv hs)) (range_singleton 118 (m118 H hv hs))) (range_join (range_singleton 119 (m119 H hv hs)) (range_singleton 120 (m120 H hv hs))))) (range_join (range_join (range_join (range_singleton 121 (m121 H hv hs)) (range_singleton 122 (m122 H hv hs))) (range_join (range_singleton 123 (m123 H hv)) (range_singleton 124 (m124 H hv hs)))) (range_join (range_join (range_singleton 125 (m125 H hv hs)) (range_singleton 126 (m126 H hv hs))) (range_join (range_singleton 127 (m127 H hv hs)) (range_singleton 128 (m128 H hv)))))))

private theorem range129 : ∀ n, 129 ≤ n → n < 161 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 129 (m129 H hv hs)) (range_singleton 130 (m130 H hv hs))) (range_join (range_singleton 131 (m131 H hv hs)) (range_singleton 132 (m132 H hv)))) (range_join (range_join (range_singleton 133 (m133 H hv hs)) (range_singleton 134 (m134 H hv hs))) (range_join (range_singleton 135 (m135 H hv hs)) (range_singleton 136 (m136 H hv))))) (range_join (range_join (range_join (range_singleton 137 (m137 H hv hs)) (range_singleton 138 (m138 H hv hs))) (range_join (range_singleton 139 (m139 H hv hs)) (range_singleton 140 (m140 H hv)))) (range_join (range_join (range_singleton 141 (m141 H hv)) (range_singleton 142 (m142 H hv hs))) (range_join (range_singleton 143 (m143 H hv)) (range_singleton 144 (m144 H hv)))))) (range_join (range_join (range_join (range_join (range_singleton 145 (m145 H hv hs)) (range_singleton 146 (m146 H hv))) (range_join (range_singleton 147 (m147 H hv hs)) (range_singleton 148 (m148 H hv hs)))) (range_join (range_join (range_singleton 149 (m149 H hv hs)) (range_singleton 150 (m150 H hv))) (range_join (range_singleton 151 (m151 H hv)) (range_singleton 152 (m152 H hv))))) (range_join (range_join (range_join (range_singleton 153 (m153 H hv hs)) (range_singleton 154 (m154 H hv hs))) (range_join (range_singleton 155 (m155 H hv hs)) (range_singleton 156 (m156 H hv hs)))) (range_join (range_join (range_singleton 157 (m157 H hv hs)) (range_singleton 158 (m158 H hv))) (range_join (range_singleton 159 (m159 H hv hs)) (range_singleton 160 (m160 H hv hs)))))))

private theorem range161 : ∀ n, 161 ≤ n → n < 193 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 161 (m161 H hv hs)) (range_singleton 162 (m162 H hv hs))) (range_join (range_singleton 163 (m163 H hv hs)) (range_singleton 164 (m164 H hv hs)))) (range_join (range_join (range_singleton 165 (m165 H hv)) (range_singleton 166 (m166 H hv))) (range_join (range_singleton 167 (m167 H hv hs)) (range_singleton 168 (m168 H hv))))) (range_join (range_join (range_join (range_singleton 169 (m169 H hv hs)) (range_singleton 170 (m170 H hv hs))) (range_join (range_singleton 171 (m171 H hv hs)) (range_singleton 172 (m172 H hv hs)))) (range_join (range_join (range_singleton 173 (m173 H hv hs)) (range_singleton 174 (m174 H hv))) (range_join (range_singleton 175 (m175 H hv hs)) (range_singleton 176 (m176 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 177 (m177 H hv hs)) (range_singleton 178 (m178 H hv))) (range_join (range_singleton 179 (m179 H hv hs)) (range_singleton 180 (m180 H hv hs)))) (range_join (range_join (range_singleton 181 (m181 H hv)) (range_singleton 182 (m182 H hv hs))) (range_join (range_singleton 183 (m183 H hv)) (range_singleton 184 (m184 H hv))))) (range_join (range_join (range_join (range_singleton 185 (m185 H hv hs)) (range_singleton 186 (m186 H hv))) (range_join (range_singleton 187 (m187 H hv hs)) (range_singleton 188 (m188 H hv)))) (range_join (range_join (range_singleton 189 (m189 H hv hs)) (range_singleton 190 (m190 H hv hs))) (range_join (range_singleton 191 (m191 H hv)) (range_singleton 192 (m192 H hv hs)))))))

private theorem range193 : ∀ n, 193 ≤ n → n < 225 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 193 (m193 H hv)) (range_singleton 194 (m194 H hv hs))) (range_join (range_singleton 195 (m195 H hv hs)) (range_singleton 196 (m196 H hv)))) (range_join (range_join (range_singleton 197 (m197 H hv hs)) (range_singleton 198 (m198 H hv))) (range_join (range_singleton 199 (m199 H hv)) (range_singleton 200 (m200 H hv hs))))) (range_join (range_join (range_join (range_singleton 201 (m201 H hv hs)) (range_singleton 202 (m202 H hv))) (range_join (range_singleton 203 (m203 H hv hs)) (range_singleton 204 (m204 H hv)))) (range_join (range_join (range_singleton 205 (m205 H hv hs)) (range_singleton 206 (m206 H hv))) (range_join (range_singleton 207 (m207 H hv hs)) (range_singleton 208 (m208 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 209 (m209 H hv)) (range_singleton 210 (m210 H hv))) (range_join (range_singleton 211 (m211 H hv)) (range_singleton 212 (m212 H hv hs)))) (range_join (range_join (range_singleton 213 (m213 H hv hs)) (range_singleton 214 (m214 H hv hs))) (range_join (range_singleton 215 (m215 H hv hs)) (range_singleton 216 (m216 H hv hs))))) (range_join (range_join (range_join (range_singleton 217 (m217 H hv hs)) (range_singleton 218 (m218 H hv))) (range_join (range_singleton 219 (m219 H hv hs)) (range_singleton 220 (m220 H hv hs)))) (range_join (range_join (range_singleton 221 (m221 H hv)) (range_singleton 222 (m222 H hv))) (range_join (range_singleton 223 (m223 H hv hs)) (range_singleton 224 (m224 H hv hs)))))))

private theorem range225 : ∀ n, 225 ≤ n → n < 257 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 225 (m225 H hv)) (range_singleton 226 (m226 H hv hs))) (range_join (range_singleton 227 (m227 H hv hs)) (range_singleton 228 (m228 H hv hs)))) (range_join (range_join (range_singleton 229 (m229 H hv hs)) (range_singleton 230 (m230 H hv hs))) (range_join (range_singleton 231 (m231 H hv hs)) (range_singleton 232 (m232 H hv hs))))) (range_join (range_join (range_join (range_singleton 233 (m233 H hv hs)) (range_singleton 234 (m234 H hv))) (range_join (range_singleton 235 (m235 H hs)) (range_singleton 236 (m236 H hv hs)))) (range_join (range_join (range_singleton 237 (m237 H hv hs)) (range_singleton 238 (m238 H hv))) (range_join (range_singleton 239 (m239 H hv hs)) (range_singleton 240 (m240 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 241 (m241 H hv hs)) (range_singleton 242 (m242 H hv hs))) (range_join (range_singleton 243 (m243 H hv hs)) (range_singleton 244 (m244 H hv hs)))) (range_join (range_join (range_singleton 245 (m245 H hv)) (range_singleton 246 (m246 H hv hs))) (range_join (range_singleton 247 (m247 H hv hs)) (range_singleton 248 (m248 H hv))))) (range_join (range_join (range_join (range_singleton 249 (m249 H hv hs)) (range_singleton 250 (m250 H hv hs))) (range_join (range_singleton 251 (m251 H hv hs)) (range_singleton 252 (m252 H hv)))) (range_join (range_join (range_singleton 253 (m253 H hv)) (range_singleton 254 (m254 H hv hs))) (range_join (range_singleton 255 (m255 H hv hs)) (range_singleton 256 (m256 H hv hs)))))))

private theorem range257 : ∀ n, 257 ≤ n → n < 289 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 257 (m257 H hv)) (range_singleton 258 (m258 H hv hs))) (range_join (range_singleton 259 (m259 H hv hs)) (range_singleton 260 (m260 H hv hs)))) (range_join (range_join (range_singleton 261 (m261 H hv hs)) (range_singleton 262 (m262 H hv hs))) (range_join (range_singleton 263 (m263 H hv hs)) (range_singleton 264 (m264 H hv hs))))) (range_join (range_join (range_join (range_singleton 265 (m265 H hv)) (range_singleton 266 (m266 H hv))) (range_join (range_singleton 267 (m267 H hv hs)) (range_singleton 268 (m268 H hv hs)))) (range_join (range_join (range_singleton 269 (m269 H hv)) (range_singleton 270 (m270 H hv hs))) (range_join (range_singleton 271 (m271 H hv hs)) (range_singleton 272 (m272 H hv)))))) (range_join (range_join (range_join (range_join (range_singleton 273 (m273 H hs)) (range_singleton 274 (m274 H hv hs))) (range_join (range_singleton 275 (m275 H hv)) (range_singleton 276 (m276 H hv hs)))) (range_join (range_join (range_singleton 277 (m277 H hv hs)) (range_singleton 278 (m278 H hv))) (range_join (range_singleton 279 (m279 H hv)) (range_singleton 280 (m280 H hv))))) (range_join (range_join (range_join (range_singleton 281 (m281 H hv hs)) (range_singleton 282 (m282 H hv hs))) (range_join (range_singleton 283 (m283 H hv)) (range_singleton 284 (m284 H hv hs)))) (range_join (range_join (range_singleton 285 (m285 H hv)) (range_singleton 286 (m286 H hv))) (range_join (range_singleton 287 (m287 H hv hs)) (range_singleton 288 (m288 H hv hs)))))))

private theorem range289 : ∀ n, 289 ≤ n → n < 321 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 289 (m289 H hv hs)) (range_singleton 290 (m290 H hv))) (range_join (range_singleton 291 (m291 H hv hs)) (range_singleton 292 (m292 H hv hs)))) (range_join (range_join (range_singleton 293 (m293 H hv hs)) (range_singleton 294 (m294 H hv hs))) (range_join (range_singleton 295 (m295 H hv hs)) (range_singleton 296 (m296 H hv))))) (range_join (range_join (range_join (range_singleton 297 (m297 H hv)) (range_singleton 298 (m298 H hv))) (range_join (range_singleton 299 (m299 H hv)) (range_singleton 300 (m300 H hv)))) (range_join (range_join (range_singleton 301 (m301 H hv)) (range_singleton 302 (m302 H hv hs))) (range_join (range_singleton 303 (m303 H hv hs)) (range_singleton 304 (m304 H hv)))))) (range_join (range_join (range_join (range_join (range_singleton 305 (m305 H hv hs)) (range_singleton 306 (m306 H hv hs))) (range_join (range_singleton 307 (m307 H hv hs)) (range_singleton 308 (m308 H hv)))) (range_join (range_join (range_singleton 309 (m309 H hv hs)) (range_singleton 310 (m310 H hv hs))) (range_join (range_singleton 311 (m311 H hv hs)) (range_singleton 312 (m312 H hv hs))))) (range_join (range_join (range_join (range_singleton 313 (m313 H hv hs)) (range_singleton 314 (m314 H hv hs))) (range_join (range_singleton 315 (m315 H hv)) (range_singleton 316 (m316 H hv hs)))) (range_join (range_join (range_singleton 317 (m317 H hv)) (range_singleton 318 (m318 H hv))) (range_join (range_singleton 319 (m319 H hv hs)) (range_singleton 320 (m320 H hv hs)))))))

private theorem range321 : ∀ n, 321 ≤ n → n < 353 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 321 (m321 H hv)) (range_singleton 322 (m322 H hv hs))) (range_join (range_singleton 323 (m323 H hv hs)) (range_singleton 324 (m324 H hv)))) (range_join (range_join (range_singleton 325 (m325 H hv hs)) (range_singleton 326 (m326 H hv))) (range_join (range_singleton 327 (m327 H hv)) (range_singleton 328 (m328 H hv))))) (range_join (range_join (range_join (range_singleton 329 (m329 H hv)) (range_singleton 330 (m330 H hv))) (range_join (range_singleton 331 (m331 H hv hs)) (range_singleton 332 (m332 H hv)))) (range_join (range_join (range_singleton 333 (m333 H hv hs)) (range_singleton 334 (m334 H hv))) (range_join (range_singleton 335 (m335 H hv hs)) (range_singleton 336 (m336 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 337 (m337 H hv)) (range_singleton 338 (m338 H hv hs))) (range_join (range_singleton 339 (m339 H hv)) (range_singleton 340 (m340 H hv)))) (range_join (range_join (range_singleton 341 (m341 H hv hs)) (range_singleton 342 (m342 H hv hs))) (range_join (range_singleton 343 (m343 H hv hs)) (range_singleton 344 (m344 H hv))))) (range_join (range_join (range_join (range_singleton 345 (m345 H hv hs)) (range_singleton 346 (m346 H hv hs))) (range_join (range_singleton 347 (m347 H hv)) (range_singleton 348 (m348 H hs)))) (range_join (range_join (range_singleton 349 (m349 H hv hs)) (range_singleton 350 (m350 H hv))) (range_join (range_singleton 351 (m351 H hv hs)) (range_singleton 352 (m352 H hv hs)))))))

private theorem range353 : ∀ n, 353 ≤ n → n < 385 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 353 (m353 H hv)) (range_singleton 354 (m354 H hv hs))) (range_join (range_singleton 355 (m355 H hv hs)) (range_singleton 356 (m356 H hv hs)))) (range_join (range_join (range_singleton 357 (m357 H hv hs)) (range_singleton 358 (m358 H hv hs))) (range_join (range_singleton 359 (m359 H hv hs)) (range_singleton 360 (m360 H hv hs))))) (range_join (range_join (range_join (range_singleton 361 (m361 H hv)) (range_singleton 362 (m362 H hv hs))) (range_join (range_singleton 363 (m363 H hv hs)) (range_singleton 364 (m364 H hv hs)))) (range_join (range_join (range_singleton 365 (m365 H hv hs)) (range_singleton 366 (m366 H hv hs))) (range_join (range_singleton 367 (m367 H hv)) (range_singleton 368 (m368 H hv)))))) (range_join (range_join (range_join (range_join (range_singleton 369 (m369 H hv hs)) (range_singleton 370 (m370 H hv))) (range_join (range_singleton 371 (m371 H hv hs)) (range_singleton 372 (m372 H hv)))) (range_join (range_join (range_singleton 373 (m373 H hv)) (range_singleton 374 (m374 H hv hs))) (range_join (range_singleton 375 (m375 H hv)) (range_singleton 376 (m376 H hv hs))))) (range_join (range_join (range_join (range_singleton 377 (m377 H hv)) (range_singleton 378 (m378 H hv))) (range_join (range_singleton 379 (m379 H hv hs)) (range_singleton 380 (m380 H hv hs)))) (range_join (range_join (range_singleton 381 (m381 H hv hs)) (range_singleton 382 (m382 H hv))) (range_join (range_singleton 383 (m383 H hv hs)) (range_singleton 384 (m384 H hv hs)))))))

private theorem range385 : ∀ n, 385 ≤ n → n < 417 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 385 (m385 H hv hs)) (range_singleton 386 (m386 H hv hs))) (range_join (range_singleton 387 (m387 H hv hs)) (range_singleton 388 (m388 H hv)))) (range_join (range_join (range_singleton 389 (m389 H hv hs)) (range_singleton 390 (m390 H hv))) (range_join (range_singleton 391 (m391 H hv hs)) (range_singleton 392 (m392 H hv hs))))) (range_join (range_join (range_join (range_singleton 393 (m393 H hv hs)) (range_singleton 394 (m394 H hv hs))) (range_join (range_singleton 395 (m395 H hv hs)) (range_singleton 396 (m396 H hv)))) (range_join (range_join (range_singleton 397 (m397 H hv)) (range_singleton 398 (m398 H hv hs))) (range_join (range_singleton 399 (m399 H hv)) (range_singleton 400 (m400 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 401 (m401 H hv hs)) (range_singleton 402 (m402 H hv hs))) (range_join (range_singleton 403 (m403 H hv hs)) (range_singleton 404 (m404 H hv hs)))) (range_join (range_join (range_singleton 405 (m405 H hv hs)) (range_singleton 406 (m406 H hv hs))) (range_join (range_singleton 407 (m407 H hv)) (range_singleton 408 (m408 H hv hs))))) (range_join (range_join (range_join (range_singleton 409 (m409 H hv)) (range_singleton 410 (m410 H hv hs))) (range_join (range_singleton 411 (m411 H hv hs)) (range_singleton 412 (m412 H hv hs)))) (range_join (range_join (range_singleton 413 (m413 H hv)) (range_singleton 414 (m414 H hv hs))) (range_join (range_singleton 415 (m415 H hv hs)) (range_singleton 416 (m416 H hv hs)))))))

private theorem range417 : ∀ n, 417 ≤ n → n < 449 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 417 (m417 H hv)) (range_singleton 418 (m418 H hv))) (range_join (range_singleton 419 (m419 H hv)) (range_singleton 420 (m420 H hv hs)))) (range_join (range_join (range_singleton 421 (m421 H hv hs)) (range_singleton 422 (m422 H hs))) (range_join (range_singleton 423 (m423 H hv)) (range_singleton 424 (m424 H hv hs))))) (range_join (range_join (range_join (range_singleton 425 (m425 H hv hs)) (range_singleton 426 (m426 H hv))) (range_join (range_singleton 427 (m427 H hv hs)) (range_singleton 428 (m428 H hv)))) (range_join (range_join (range_singleton 429 (m429 H hv hs)) (range_singleton 430 (m430 H hv hs))) (range_join (range_singleton 431 (m431 H hv hs)) (range_singleton 432 (m432 H hv)))))) (range_join (range_join (range_join (range_join (range_singleton 433 (m433 H hv hs)) (range_singleton 434 (m434 H hv hs))) (range_join (range_singleton 435 (m435 H hv hs)) (range_singleton 436 (m436 H hv hs)))) (range_join (range_join (range_singleton 437 (m437 H hv)) (range_singleton 438 (m438 H hv hs))) (range_join (range_singleton 439 (m439 H hv)) (range_singleton 440 (m440 H hv hs))))) (range_join (range_join (range_join (range_singleton 441 (m441 H hv)) (range_singleton 442 (m442 H hv hs))) (range_join (range_singleton 443 (m443 H hv)) (range_singleton 444 (m444 H hv hs)))) (range_join (range_join (range_singleton 445 (m445 H hv)) (range_singleton 446 (m446 H hv))) (range_join (range_singleton 447 (m447 H hv hs)) (range_singleton 448 (m448 H hv)))))))

private theorem range449 : ∀ n, 449 ≤ n → n < 481 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 449 (m449 H hv hs)) (range_singleton 450 (m450 H hv))) (range_join (range_singleton 451 (m451 H hv)) (range_singleton 452 (m452 H hv)))) (range_join (range_join (range_singleton 453 (m453 H hv hs)) (range_singleton 454 (m454 H hv))) (range_join (range_singleton 455 (m455 H hv hs)) (range_singleton 456 (m456 H hv hs))))) (range_join (range_join (range_join (range_singleton 457 (m457 H hv hs)) (range_singleton 458 (m458 H hv))) (range_join (range_singleton 459 (m459 H hv hs)) (range_singleton 460 (m460 H hv hs)))) (range_join (range_join (range_singleton 461 (m461 H hv)) (range_singleton 462 (m462 H hv hs))) (range_join (range_singleton 463 (m463 H hv hs)) (range_singleton 464 (m464 H hv)))))) (range_join (range_join (range_join (range_join (range_singleton 465 (m465 H hv)) (range_singleton 466 (m466 H hv))) (range_join (range_singleton 467 (m467 H hv)) (range_singleton 468 (m468 H hv hs)))) (range_join (range_join (range_singleton 469 (m469 H hv hs)) (range_singleton 470 (m470 H hv))) (range_join (range_singleton 471 (m471 H hv)) (range_singleton 472 (m472 H hv hs))))) (range_join (range_join (range_join (range_singleton 473 (m473 H hv hs)) (range_singleton 474 (m474 H hv))) (range_join (range_singleton 475 (m475 H hv hs)) (range_singleton 476 (m476 H hv)))) (range_join (range_join (range_singleton 477 (m477 H hv hs)) (range_singleton 478 (m478 H hv hs))) (range_join (range_singleton 479 (m479 H hv hs)) (range_singleton 480 (m480 H hs)))))))

private theorem range481 : ∀ n, 481 ≤ n → n < 513 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 481 (m481 H hv hs)) (range_singleton 482 (m482 H hv hs))) (range_join (range_singleton 483 (m483 H hv hs)) (range_singleton 484 (m484 H hv hs)))) (range_join (range_join (range_singleton 485 (m485 H hv)) (range_singleton 486 (m486 H hv hs))) (range_join (range_singleton 487 (m487 H hv)) (range_singleton 488 (m488 H hv))))) (range_join (range_join (range_join (range_singleton 489 (m489 H hv hs)) (range_singleton 490 (m490 H hv hs))) (range_join (range_singleton 491 (m491 H hv hs)) (range_singleton 492 (m492 H hv hs)))) (range_join (range_join (range_singleton 493 (m493 H hv)) (range_singleton 494 (m494 H hv hs))) (range_join (range_singleton 495 (m495 H hv hs)) (range_singleton 496 (m496 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 497 (m497 H hv hs)) (range_singleton 498 (m498 H hv hs))) (range_join (range_singleton 499 (m499 H hv hs)) (range_singleton 500 (m500 H hv)))) (range_join (range_join (range_singleton 501 (m501 H hv hs)) (range_singleton 502 (m502 H hv))) (range_join (range_singleton 503 (m503 H hv hs)) (range_singleton 504 (m504 H hv hs))))) (range_join (range_join (range_join (range_singleton 505 (m505 H hv)) (range_singleton 506 (m506 H hv hs))) (range_join (range_singleton 507 (m507 H hv hs)) (range_singleton 508 (m508 H hv)))) (range_join (range_join (range_singleton 509 (m509 H hv hs)) (range_singleton 510 (m510 H hv hs))) (range_join (range_singleton 511 (m511 H hv hs)) (range_singleton 512 (m512 H hv hs)))))))

private theorem range513 : ∀ n, 513 ≤ n → n < 545 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 513 (m513 H hv hs)) (range_singleton 514 (m514 H hv hs))) (range_join (range_singleton 515 (m515 H hv)) (range_singleton 516 (m516 H hv hs)))) (range_join (range_join (range_singleton 517 (m517 H hv hs)) (range_singleton 518 (m518 H hv))) (range_join (range_singleton 519 (m519 H hv)) (range_singleton 520 (m520 H hv))))) (range_join (range_join (range_join (range_singleton 521 (m521 H hv hs)) (range_singleton 522 (m522 H hv hs))) (range_join (range_singleton 523 (m523 H hv hs)) (range_singleton 524 (m524 H hv hs)))) (range_join (range_join (range_singleton 525 (m525 H hv)) (range_singleton 526 (m526 H hv hs))) (range_join (range_singleton 527 (m527 H hv)) (range_singleton 528 (m528 H hv)))))) (range_join (range_join (range_join (range_join (range_singleton 529 (m529 H hv)) (range_singleton 530 (m530 H hv hs))) (range_join (range_singleton 531 (m531 H hv hs)) (range_singleton 532 (m532 H hv)))) (range_join (range_join (range_singleton 533 (m533 H hv hs)) (range_singleton 534 (m534 H hv hs))) (range_join (range_singleton 535 (m535 H hv)) (range_singleton 536 (m536 H hv hs))))) (range_join (range_join (range_join (range_singleton 537 (m537 H hv)) (range_singleton 538 (m538 H hv))) (range_join (range_singleton 539 (m539 H hv hs)) (range_singleton 540 (m540 H hv)))) (range_join (range_join (range_singleton 541 (m541 H hv hs)) (range_singleton 542 (m542 H hv hs))) (range_join (range_singleton 543 (m543 H hv hs)) (range_singleton 544 (m544 H hv hs)))))))

private theorem range545 : ∀ n, 545 ≤ n → n < 577 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 545 (m545 H hv hs)) (range_singleton 546 (m546 H hv))) (range_join (range_singleton 547 (m547 H hv hs)) (range_singleton 548 (m548 H hv)))) (range_join (range_join (range_singleton 549 (m549 H hv)) (range_singleton 550 (m550 H hv hs))) (range_join (range_singleton 551 (m551 H hv hs)) (range_singleton 552 (m552 H hv hs))))) (range_join (range_join (range_join (range_singleton 553 (m553 H hv hs)) (range_singleton 554 (m554 H hv))) (range_join (range_singleton 555 (m555 H hv hs)) (range_singleton 556 (m556 H hv)))) (range_join (range_join (range_singleton 557 (m557 H hv hs)) (range_singleton 558 (m558 H hv hs))) (range_join (range_singleton 559 (m559 H hv hs)) (range_singleton 560 (m560 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 561 (m561 H hv hs)) (range_singleton 562 (m562 H hv))) (range_join (range_singleton 563 (m563 H hv)) (range_singleton 564 (m564 H hv)))) (range_join (range_join (range_singleton 565 (m565 H hv hs)) (range_singleton 566 (m566 H hv hs))) (range_join (range_singleton 567 (m567 H hv)) (range_singleton 568 (m568 H hv))))) (range_join (range_join (range_join (range_singleton 569 (m569 H hv)) (range_singleton 570 (m570 H hv))) (range_join (range_singleton 571 (m571 H hv hs)) (range_singleton 572 (m572 H hv hs)))) (range_join (range_join (range_singleton 573 (m573 H hv hs)) (range_singleton 574 (m574 H hv hs))) (range_join (range_singleton 575 (m575 H hv hs)) (range_singleton 576 (m576 H hv hs)))))))

private theorem range577 : ∀ n, 577 ≤ n → n < 609 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 577 (m577 H hv)) (range_singleton 578 (m578 H hv hs))) (range_join (range_singleton 579 (m579 H hv hs)) (range_singleton 580 (m580 H hv)))) (range_join (range_join (range_singleton 581 (m581 H hv hs)) (range_singleton 582 (m582 H hv hs))) (range_join (range_singleton 583 (m583 H hv)) (range_singleton 584 (m584 H hv))))) (range_join (range_join (range_join (range_singleton 585 (m585 H hv hs)) (range_singleton 586 (m586 H hv))) (range_join (range_singleton 587 (m587 H hv hs)) (range_singleton 588 (m588 H hv hs)))) (range_join (range_join (range_singleton 589 (m589 H hv)) (range_singleton 590 (m590 H hv hs))) (range_join (range_singleton 591 (m591 H hv hs)) (range_singleton 592 (m592 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 593 (m593 H hv)) (range_singleton 594 (m594 H hv))) (range_join (range_singleton 595 (m595 H hv hs)) (range_singleton 596 (m596 H hv hs)))) (range_join (range_join (range_singleton 597 (m597 H hv)) (range_singleton 598 (m598 H hv hs))) (range_join (range_singleton 599 (m599 H hv hs)) (range_singleton 600 (m600 H hv))))) (range_join (range_join (range_join (range_singleton 601 (m601 H hv hs)) (range_singleton 602 (m602 H hv hs))) (range_join (range_singleton 603 (m603 H hv)) (range_singleton 604 (m604 H hv hs)))) (range_join (range_join (range_singleton 605 (m605 H hv)) (range_singleton 606 (m606 H hv hs))) (range_join (range_singleton 607 (m607 H hv)) (range_singleton 608 (m608 H hv hs)))))))

private theorem range609 : ∀ n, 609 ≤ n → n < 641 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 609 (m609 H hv hs)) (range_singleton 610 (m610 H hv hs))) (range_join (range_singleton 611 (m611 H hv hs)) (range_singleton 612 (m612 H hv hs)))) (range_join (range_join (range_singleton 613 (m613 H hv hs)) (range_singleton 614 (m614 H hv hs))) (range_join (range_singleton 615 (m615 H hv hs)) (range_singleton 616 (m616 H hv hs))))) (range_join (range_join (range_join (range_singleton 617 (m617 H hv hs)) (range_singleton 618 (m618 H hv))) (range_join (range_singleton 619 (m619 H hv hs)) (range_singleton 620 (m620 H hv hs)))) (range_join (range_join (range_singleton 621 (m621 H hv)) (range_singleton 622 (m622 H hv hs))) (range_join (range_singleton 623 (m623 H hv)) (range_singleton 624 (m624 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 625 (m625 H hv hs)) (range_singleton 626 (m626 H hv hs))) (range_join (range_singleton 627 (m627 H hv hs)) (range_singleton 628 (m628 H hv hs)))) (range_join (range_join (range_singleton 629 (m629 H hv hs)) (range_singleton 630 (m630 H hv hs))) (range_join (range_singleton 631 (m631 H hv)) (range_singleton 632 (m632 H hv))))) (range_join (range_join (range_join (range_singleton 633 (m633 H hv)) (range_singleton 634 (m634 H hv hs))) (range_join (range_singleton 635 (m635 H hv)) (range_singleton 636 (m636 H hv hs)))) (range_join (range_join (range_singleton 637 (m637 H hv hs)) (range_singleton 638 (m638 H hv))) (range_join (range_singleton 639 (m639 H hv hs)) (range_singleton 640 (m640 H hv hs)))))))

private theorem range641 : ∀ n, 641 ≤ n → n < 673 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 641 (m641 H hv)) (range_singleton 642 (m642 H hv))) (range_join (range_singleton 643 (m643 H hv hs)) (range_singleton 644 (m644 H hv hs)))) (range_join (range_join (range_singleton 645 (m645 H hv hs)) (range_singleton 646 (m646 H hv))) (range_join (range_singleton 647 (m647 H hv hs)) (range_singleton 648 (m648 H hv))))) (range_join (range_join (range_join (range_singleton 649 (m649 H hv hs)) (range_singleton 650 (m650 H hv hs))) (range_join (range_singleton 651 (m651 H hv hs)) (range_singleton 652 (m652 H hv hs)))) (range_join (range_join (range_singleton 653 (m653 H hv)) (range_singleton 654 (m654 H hv))) (range_join (range_singleton 655 (m655 H hv)) (range_singleton 656 (m656 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 657 (m657 H hv hs)) (range_singleton 658 (m658 H hv hs))) (range_join (range_singleton 659 (m659 H hv hs)) (range_singleton 660 (m660 H hv)))) (range_join (range_join (range_singleton 661 (m661 H hv hs)) (range_singleton 662 (m662 H hv))) (range_join (range_singleton 663 (m663 H hv)) (range_singleton 664 (m664 H hv))))) (range_join (range_join (range_join (range_singleton 665 (m665 H hv hs)) (range_singleton 666 (m666 H hv))) (range_join (range_singleton 667 (m667 H hv hs)) (range_singleton 668 (m668 H hv)))) (range_join (range_join (range_singleton 669 (m669 H hv)) (range_singleton 670 (m670 H hv))) (range_join (range_singleton 671 (m671 H hv hs)) (range_singleton 672 (m672 H hv hs)))))))

private theorem range673 : ∀ n, 673 ≤ n → n < 705 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 673 (m673 H hv hs)) (range_singleton 674 (m674 H hv hs))) (range_join (range_singleton 675 (m675 H hv hs)) (range_singleton 676 (m676 H hv hs)))) (range_join (range_join (range_singleton 677 (m677 H hv hs)) (range_singleton 678 (m678 H hv))) (range_join (range_singleton 679 (m679 H hv)) (range_singleton 680 (m680 H hv hs))))) (range_join (range_join (range_join (range_singleton 681 (m681 H hv hs)) (range_singleton 682 (m682 H hv))) (range_join (range_singleton 683 (m683 H hv hs)) (range_singleton 684 (m684 H hv)))) (range_join (range_join (range_singleton 685 (m685 H hv hs)) (range_singleton 686 (m686 H hv hs))) (range_join (range_singleton 687 (m687 H hv)) (range_singleton 688 (m688 H hs)))))) (range_join (range_join (range_join (range_join (range_singleton 689 (m689 H hv hs)) (range_singleton 690 (m690 H hv hs))) (range_join (range_singleton 691 (m691 H hv hs)) (range_singleton 692 (m692 H hv hs)))) (range_join (range_join (range_singleton 693 (m693 H hv hs)) (range_singleton 694 (m694 H hv hs))) (range_join (range_singleton 695 (m695 H hv)) (range_singleton 696 (m696 H hv))))) (range_join (range_join (range_join (range_singleton 697 (m697 H hv hs)) (range_singleton 698 (m698 H hv))) (range_join (range_singleton 699 (m699 H hv hs)) (range_singleton 700 (m700 H hv)))) (range_join (range_join (range_singleton 701 (m701 H hv hs)) (range_singleton 702 (m702 H hv))) (range_join (range_singleton 703 (m703 H hv hs)) (range_singleton 704 (m704 H hv hs)))))))

private theorem range705 : ∀ n, 705 ≤ n → n < 737 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 705 (m705 H hv hs)) (range_singleton 706 (m706 H hv))) (range_join (range_singleton 707 (m707 H hv hs)) (range_singleton 708 (m708 H hv hs)))) (range_join (range_join (range_singleton 709 (m709 H hv hs)) (range_singleton 710 (m710 H hv))) (range_join (range_singleton 711 (m711 H hv hs)) (range_singleton 712 (m712 H hv hs))))) (range_join (range_join (range_join (range_singleton 713 (m713 H hv hs)) (range_singleton 714 (m714 H hv))) (range_join (range_singleton 715 (m715 H hv hs)) (range_singleton 716 (m716 H hv)))) (range_join (range_join (range_singleton 717 (m717 H hv hs)) (range_singleton 718 (m718 H hv))) (range_join (range_singleton 719 (m719 H hv hs)) (range_singleton 720 (m720 H hv)))))) (range_join (range_join (range_join (range_join (range_singleton 721 (m721 H hv)) (range_singleton 722 (m722 H hv))) (range_join (range_singleton 723 (m723 H hv hs)) (range_singleton 724 (m724 H hv hs)))) (range_join (range_join (range_singleton 725 (m725 H hv)) (range_singleton 726 (m726 H hv))) (range_join (range_singleton 727 (m727 H hv hs)) (range_singleton 728 (m728 H hv hs))))) (range_join (range_join (range_join (range_singleton 729 (m729 H hv hs)) (range_singleton 730 (m730 H hv hs))) (range_join (range_singleton 731 (m731 H hv)) (range_singleton 732 (m732 H hv hs)))) (range_join (range_join (range_singleton 733 (m733 H hv)) (range_singleton 734 (m734 H hv hs))) (range_join (range_singleton 735 (m735 H hv hs)) (range_singleton 736 (m736 H hv hs)))))))

private theorem range737 : ∀ n, 737 ≤ n → n < 769 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 737 (m737 H hv hs)) (range_singleton 738 (m738 H hv hs))) (range_join (range_singleton 739 (m739 H hv)) (range_singleton 740 (m740 H hv hs)))) (range_join (range_join (range_singleton 741 (m741 H hv hs)) (range_singleton 742 (m742 H hv))) (range_join (range_singleton 743 (m743 H hv hs)) (range_singleton 744 (m744 H hv))))) (range_join (range_join (range_join (range_singleton 745 (m745 H hv hs)) (range_singleton 746 (m746 H hv))) (range_join (range_singleton 747 (m747 H hv)) (range_singleton 748 (m748 H hv hs)))) (range_join (range_join (range_singleton 749 (m749 H hv hs)) (range_singleton 750 (m750 H hv hs))) (range_join (range_singleton 751 (m751 H hv)) (range_singleton 752 (m752 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 753 (m753 H hv hs)) (range_singleton 754 (m754 H hv hs))) (range_join (range_singleton 755 (m755 H hv hs)) (range_singleton 756 (m756 H hv)))) (range_join (range_join (range_singleton 757 (m757 H hv hs)) (range_singleton 758 (m758 H hv hs))) (range_join (range_singleton 759 (m759 H hv hs)) (range_singleton 760 (m760 H hv hs))))) (range_join (range_join (range_join (range_singleton 761 (m761 H hv)) (range_singleton 762 (m762 H hv hs))) (range_join (range_singleton 763 (m763 H hv)) (range_singleton 764 (m764 H hv hs)))) (range_join (range_join (range_singleton 765 (m765 H hv hs)) (range_singleton 766 (m766 H hv))) (range_join (range_singleton 767 (m767 H hv hs)) (range_singleton 768 (m768 H hv hs)))))))

private theorem range769 : ∀ n, 769 ≤ n → n < 801 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 769 (m769 H hv hs)) (range_singleton 770 (m770 H hv))) (range_join (range_singleton 771 (m771 H hv hs)) (range_singleton 772 (m772 H hv hs)))) (range_join (range_join (range_singleton 773 (m773 H hv hs)) (range_singleton 774 (m774 H hv))) (range_join (range_singleton 775 (m775 H hv)) (range_singleton 776 (m776 H hv hs))))) (range_join (range_join (range_join (range_singleton 777 (m777 H hv hs)) (range_singleton 778 (m778 H hv hs))) (range_join (range_singleton 779 (m779 H hv)) (range_singleton 780 (m780 H hv hs)))) (range_join (range_join (range_singleton 781 (m781 H hv)) (range_singleton 782 (m782 H hv hs))) (range_join (range_singleton 783 (m783 H hv)) (range_singleton 784 (m784 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 785 (m785 H hv hs)) (range_singleton 786 (m786 H hv hs))) (range_join (range_singleton 787 (m787 H hv hs)) (range_singleton 788 (m788 H hv hs)))) (range_join (range_join (range_singleton 789 (m789 H hv)) (range_singleton 790 (m790 H hv hs))) (range_join (range_singleton 791 (m791 H hv hs)) (range_singleton 792 (m792 H hv hs))))) (range_join (range_join (range_join (range_singleton 793 (m793 H hv hs)) (range_singleton 794 (m794 H hv))) (range_join (range_singleton 795 (m795 H hv)) (range_singleton 796 (m796 H hv hs)))) (range_join (range_join (range_singleton 797 (m797 H hv)) (range_singleton 798 (m798 H hv hs))) (range_join (range_singleton 799 (m799 H hv hs)) (range_singleton 800 (m800 H hv)))))))

private theorem range801 : ∀ n, 801 ≤ n → n < 833 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 801 (m801 H hv hs)) (range_singleton 802 (m802 H hv))) (range_join (range_singleton 803 (m803 H hv hs)) (range_singleton 804 (m804 H hv hs)))) (range_join (range_join (range_singleton 805 (m805 H hv)) (range_singleton 806 (m806 H hv hs))) (range_join (range_singleton 807 (m807 H hv hs)) (range_singleton 808 (m808 H hv hs))))) (range_join (range_join (range_join (range_singleton 809 (m809 H hv hs)) (range_singleton 810 (m810 H hv hs))) (range_join (range_singleton 811 (m811 H hv)) (range_singleton 812 (m812 H hv hs)))) (range_join (range_join (range_singleton 813 (m813 H hv hs)) (range_singleton 814 (m814 H hv hs))) (range_join (range_singleton 815 (m815 H hv)) (range_singleton 816 (m816 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 817 (m817 H hv)) (range_singleton 818 (m818 H hv hs))) (range_join (range_singleton 819 (m819 H hv)) (range_singleton 820 (m820 H hv hs)))) (range_join (range_join (range_singleton 821 (m821 H hv hs)) (range_singleton 822 (m822 H hv hs))) (range_join (range_singleton 823 (m823 H hv hs)) (range_singleton 824 (m824 H hv hs))))) (range_join (range_join (range_join (range_singleton 825 (m825 H hv)) (range_singleton 826 (m826 H hv))) (range_join (range_singleton 827 (m827 H hv hs)) (range_singleton 828 (m828 H hv hs)))) (range_join (range_join (range_singleton 829 (m829 H hv hs)) (range_singleton 830 (m830 H hv hs))) (range_join (range_singleton 831 (m831 H hv hs)) (range_singleton 832 (m832 H hv)))))))

private theorem range833 : ∀ n, 833 ≤ n → n < 865 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 833 (m833 H hv)) (range_singleton 834 (m834 H hv hs))) (range_join (range_singleton 835 (m835 H hv hs)) (range_singleton 836 (m836 H hv hs)))) (range_join (range_join (range_singleton 837 (m837 H hv hs)) (range_singleton 838 (m838 H hv))) (range_join (range_singleton 839 (m839 H hv hs)) (range_singleton 840 (m840 H hv))))) (range_join (range_join (range_join (range_singleton 841 (m841 H hv hs)) (range_singleton 842 (m842 H hv))) (range_join (range_singleton 843 (m843 H hv hs)) (range_singleton 844 (m844 H hv)))) (range_join (range_join (range_singleton 845 (m845 H hv hs)) (range_singleton 846 (m846 H hv hs))) (range_join (range_singleton 847 (m847 H hv hs)) (range_singleton 848 (m848 H hv)))))) (range_join (range_join (range_join (range_join (range_singleton 849 (m849 H hv hs)) (range_singleton 850 (m850 H hv hs))) (range_join (range_singleton 851 (m851 H hv hs)) (range_singleton 852 (m852 H hv)))) (range_join (range_join (range_singleton 853 (m853 H hv hs)) (range_singleton 854 (m854 H hv))) (range_join (range_singleton 855 (m855 H hv hs)) (range_singleton 856 (m856 H hv hs))))) (range_join (range_join (range_join (range_singleton 857 (m857 H hv hs)) (range_singleton 858 (m858 H hv hs))) (range_join (range_singleton 859 (m859 H hv hs)) (range_singleton 860 (m860 H hv hs)))) (range_join (range_join (range_singleton 861 (m861 H hv hs)) (range_singleton 862 (m862 H hv hs))) (range_join (range_singleton 863 (m863 H hv hs)) (range_singleton 864 (m864 H hv hs)))))))

private theorem range865 : ∀ n, 865 ≤ n → n < 897 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 865 (m865 H hv hs)) (range_singleton 866 (m866 H hv hs))) (range_join (range_singleton 867 (m867 H hv hs)) (range_singleton 868 (m868 H hv)))) (range_join (range_join (range_singleton 869 (m869 H hv hs)) (range_singleton 870 (m870 H hv))) (range_join (range_singleton 871 (m871 H hv hs)) (range_singleton 872 (m872 H hv))))) (range_join (range_join (range_join (range_singleton 873 (m873 H hv)) (range_singleton 874 (m874 H hv hs))) (range_join (range_singleton 875 (m875 H hv hs)) (range_singleton 876 (m876 H hv)))) (range_join (range_join (range_singleton 877 (m877 H hv hs)) (range_singleton 878 (m878 H hv hs))) (range_join (range_singleton 879 (m879 H hv)) (range_singleton 880 (m880 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 881 (m881 H hv)) (range_singleton 882 (m882 H hv))) (range_join (range_singleton 883 (m883 H hv)) (range_singleton 884 (m884 H hv hs)))) (range_join (range_join (range_singleton 885 (m885 H hv)) (range_singleton 886 (m886 H hv hs))) (range_join (range_singleton 887 (m887 H hv hs)) (range_singleton 888 (m888 H hv hs))))) (range_join (range_join (range_join (range_singleton 889 (m889 H hv)) (range_singleton 890 (m890 H hv hs))) (range_join (range_singleton 891 (m891 H hv)) (range_singleton 892 (m892 H hv)))) (range_join (range_join (range_singleton 893 (m893 H hv hs)) (range_singleton 894 (m894 H hv hs))) (range_join (range_singleton 895 (m895 H hv)) (range_singleton 896 (m896 H hv hs)))))))

private theorem range897 : ∀ n, 897 ≤ n → n < 929 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 897 (m897 H hv)) (range_singleton 898 (m898 H hv hs))) (range_join (range_singleton 899 (m899 H hv)) (range_singleton 900 (m900 H hv)))) (range_join (range_join (range_singleton 901 (m901 H hv hs)) (range_singleton 902 (m902 H hv))) (range_join (range_singleton 903 (m903 H hv hs)) (range_singleton 904 (m904 H hv))))) (range_join (range_join (range_join (range_singleton 905 (m905 H hv)) (range_singleton 906 (m906 H hs))) (range_join (range_singleton 907 (m907 H hv)) (range_singleton 908 (m908 H hv hs)))) (range_join (range_join (range_singleton 909 (m909 H hv hs)) (range_singleton 910 (m910 H hv hs))) (range_join (range_singleton 911 (m911 H hv)) (range_singleton 912 (m912 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 913 (m913 H hv hs)) (range_singleton 914 (m914 H hv hs))) (range_join (range_singleton 915 (m915 H hv hs)) (range_singleton 916 (m916 H hv hs)))) (range_join (range_join (range_singleton 917 (m917 H hv)) (range_singleton 918 (m918 H hv hs))) (range_join (range_singleton 919 (m919 H hv hs)) (range_singleton 920 (m920 H hv))))) (range_join (range_join (range_join (range_singleton 921 (m921 H hv hs)) (range_singleton 922 (m922 H hv hs))) (range_join (range_singleton 923 (m923 H hv hs)) (range_singleton 924 (m924 H hv)))) (range_join (range_join (range_singleton 925 (m925 H hv hs)) (range_singleton 926 (m926 H hv hs))) (range_join (range_singleton 927 (m927 H hv)) (range_singleton 928 (m928 H hv hs)))))))

private theorem range929 : ∀ n, 929 ≤ n → n < 961 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 929 (m929 H hv hs)) (range_singleton 930 (m930 H hv))) (range_join (range_singleton 931 (m931 H hv)) (range_singleton 932 (m932 H hv hs)))) (range_join (range_join (range_singleton 933 (m933 H hv hs)) (range_singleton 934 (m934 H hv hs))) (range_join (range_singleton 935 (m935 H hv)) (range_singleton 936 (m936 H hv))))) (range_join (range_join (range_join (range_singleton 937 (m937 H hv hs)) (range_singleton 938 (m938 H hv hs))) (range_join (range_singleton 939 (m939 H hv)) (range_singleton 940 (m940 H hv hs)))) (range_join (range_join (range_singleton 941 (m941 H hv hs)) (range_singleton 942 (m942 H hv))) (range_join (range_singleton 943 (m943 H hv hs)) (range_singleton 944 (m944 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 945 (m945 H hv hs)) (range_singleton 946 (m946 H hv hs))) (range_join (range_singleton 947 (m947 H hv hs)) (range_singleton 948 (m948 H hv hs)))) (range_join (range_join (range_singleton 949 (m949 H hv hs)) (range_singleton 950 (m950 H hv hs))) (range_join (range_singleton 951 (m951 H hv hs)) (range_singleton 952 (m952 H hv hs))))) (range_join (range_join (range_join (range_singleton 953 (m953 H hv hs)) (range_singleton 954 (m954 H hv hs))) (range_join (range_singleton 955 (m955 H hv)) (range_singleton 956 (m956 H hv hs)))) (range_join (range_join (range_singleton 957 (m957 H hv hs)) (range_singleton 958 (m958 H hv))) (range_join (range_singleton 959 (m959 H hv hs)) (range_singleton 960 (m960 H hv)))))))

private theorem range961 : ∀ n, 961 ≤ n → n < 993 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 961 (m961 H hv hs)) (range_singleton 962 (m962 H hv hs))) (range_join (range_singleton 963 (m963 H hv hs)) (range_singleton 964 (m964 H hv)))) (range_join (range_join (range_singleton 965 (m965 H hv hs)) (range_singleton 966 (m966 H hv))) (range_join (range_singleton 967 (m967 H hv)) (range_singleton 968 (m968 H hv hs))))) (range_join (range_join (range_join (range_singleton 969 (m969 H hv)) (range_singleton 970 (m970 H hv hs))) (range_join (range_singleton 971 (m971 H hv)) (range_singleton 972 (m972 H hv)))) (range_join (range_join (range_singleton 973 (m973 H hv hs)) (range_singleton 974 (m974 H hv))) (range_join (range_singleton 975 (m975 H hv hs)) (range_singleton 976 (m976 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 977 (m977 H hv hs)) (range_singleton 978 (m978 H hv hs))) (range_join (range_singleton 979 (m979 H hv hs)) (range_singleton 980 (m980 H hv)))) (range_join (range_join (range_singleton 981 (m981 H hv hs)) (range_singleton 982 (m982 H hv))) (range_join (range_singleton 983 (m983 H hv hs)) (range_singleton 984 (m984 H hv))))) (range_join (range_join (range_join (range_singleton 985 (m985 H hv hs)) (range_singleton 986 (m986 H hv hs))) (range_join (range_singleton 987 (m987 H hv hs)) (range_singleton 988 (m988 H hv)))) (range_join (range_join (range_singleton 989 (m989 H hv hs)) (range_singleton 990 (m990 H hv hs))) (range_join (range_singleton 991 (m991 H hv hs)) (range_singleton 992 (m992 H hv hs)))))))

private theorem range993 : ∀ n, 993 ≤ n → n < 1025 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 993 (m993 H hv hs)) (range_singleton 994 (m994 H hv hs))) (range_join (range_singleton 995 (m995 H hv)) (range_singleton 996 (m996 H hv hs)))) (range_join (range_join (range_singleton 997 (m997 H hv hs)) (range_singleton 998 (m998 H hv hs))) (range_join (range_singleton 999 (m999 H hv hs)) (range_singleton 1000 (m1000 H hv hs))))) (range_join (range_join (range_join (range_singleton 1001 (m1001 H hv hs)) (range_singleton 1002 (m1002 H hv hs))) (range_join (range_singleton 1003 (m1003 H hv)) (range_singleton 1004 (m1004 H hv)))) (range_join (range_join (range_singleton 1005 (m1005 H hv hs)) (range_singleton 1006 (m1006 H hv))) (range_join (range_singleton 1007 (m1007 H hv)) (range_singleton 1008 (m1008 H hv)))))) (range_join (range_join (range_join (range_join (range_singleton 1009 (m1009 H hv hs)) (range_singleton 1010 (m1010 H hv hs))) (range_join (range_singleton 1011 (m1011 H hv hs)) (range_singleton 1012 (m1012 H hv hs)))) (range_join (range_join (range_singleton 1013 (m1013 H hv hs)) (range_singleton 1014 (m1014 H hv hs))) (range_join (range_singleton 1015 (m1015 H hv hs)) (range_singleton 1016 (m1016 H hv hs))))) (range_join (range_join (range_join (range_singleton 1017 (m1017 H hv hs)) (range_singleton 1018 (m1018 H hv hs))) (range_join (range_singleton 1019 (m1019 H hv)) (range_singleton 1020 (m1020 H hv hs)))) (range_join (range_join (range_singleton 1021 (m1021 H hv)) (range_singleton 1022 (m1022 H hv hs))) (range_join (range_singleton 1023 (m1023 H hv hs)) (range_singleton 1024 (m1024 H hv hs)))))))

private theorem range1025 : ∀ n, 1025 ≤ n → n < 1057 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 1025 (m1025 H hv)) (range_singleton 1026 (m1026 H hv hs))) (range_join (range_singleton 1027 (m1027 H hv hs)) (range_singleton 1028 (m1028 H hv hs)))) (range_join (range_join (range_singleton 1029 (m1029 H hv hs)) (range_singleton 1030 (m1030 H hv hs))) (range_join (range_singleton 1031 (m1031 H hv)) (range_singleton 1032 (m1032 H hv hs))))) (range_join (range_join (range_join (range_singleton 1033 (m1033 H hv hs)) (range_singleton 1034 (m1034 H hv))) (range_join (range_singleton 1035 (m1035 H hv hs)) (range_singleton 1036 (m1036 H hv)))) (range_join (range_join (range_singleton 1037 (m1037 H hv)) (range_singleton 1038 (m1038 H hv hs))) (range_join (range_singleton 1039 (m1039 H hv)) (range_singleton 1040 (m1040 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 1041 (m1041 H hs)) (range_singleton 1042 (m1042 H hv hs))) (range_join (range_singleton 1043 (m1043 H hv hs)) (range_singleton 1044 (m1044 H hv)))) (range_join (range_join (range_singleton 1045 (m1045 H hv hs)) (range_singleton 1046 (m1046 H hv))) (range_join (range_singleton 1047 (m1047 H hv hs)) (range_singleton 1048 (m1048 H hv hs))))) (range_join (range_join (range_join (range_singleton 1049 (m1049 H hv)) (range_singleton 1050 (m1050 H hv hs))) (range_join (range_singleton 1051 (m1051 H hv)) (range_singleton 1052 (m1052 H hv hs)))) (range_join (range_join (range_singleton 1053 (m1053 H hv hs)) (range_singleton 1054 (m1054 H hv hs))) (range_join (range_singleton 1055 (m1055 H hv)) (range_singleton 1056 (m1056 H hv)))))))

private theorem range1057 : ∀ n, 1057 ≤ n → n < 1089 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 1057 (m1057 H hv hs)) (range_singleton 1058 (m1058 H hv hs))) (range_join (range_singleton 1059 (m1059 H hv)) (range_singleton 1060 (m1060 H hv hs)))) (range_join (range_join (range_singleton 1061 (m1061 H hv)) (range_singleton 1062 (m1062 H hv hs))) (range_join (range_singleton 1063 (m1063 H hv hs)) (range_singleton 1064 (m1064 H hv))))) (range_join (range_join (range_join (range_singleton 1065 (m1065 H hv hs)) (range_singleton 1066 (m1066 H hv))) (range_join (range_singleton 1067 (m1067 H hv hs)) (range_singleton 1068 (m1068 H hv)))) (range_join (range_join (range_singleton 1069 (m1069 H hv hs)) (range_singleton 1070 (m1070 H hv hs))) (range_join (range_singleton 1071 (m1071 H hv hs)) (range_singleton 1072 (m1072 H hv)))))) (range_join (range_join (range_join (range_join (range_singleton 1073 (m1073 H hv hs)) (range_singleton 1074 (m1074 H hv))) (range_join (range_singleton 1075 (m1075 H hv hs)) (range_singleton 1076 (m1076 H hv hs)))) (range_join (range_join (range_singleton 1077 (m1077 H hv hs)) (range_singleton 1078 (m1078 H hv))) (range_join (range_singleton 1079 (m1079 H hv)) (range_singleton 1080 (m1080 H hv hs))))) (range_join (range_join (range_join (range_singleton 1081 (m1081 H hv)) (range_singleton 1082 (m1082 H hv))) (range_join (range_singleton 1083 (m1083 H hv hs)) (range_singleton 1084 (m1084 H hv hs)))) (range_join (range_join (range_singleton 1085 (m1085 H hv hs)) (range_singleton 1086 (m1086 H hv))) (range_join (range_singleton 1087 (m1087 H hv hs)) (range_singleton 1088 (m1088 H hv)))))))

private theorem range1089 : ∀ n, 1089 ≤ n → n < 1121 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 1089 (m1089 H hv)) (range_singleton 1090 (m1090 H hv hs))) (range_join (range_singleton 1091 (m1091 H hv hs)) (range_singleton 1092 (m1092 H hv)))) (range_join (range_join (range_singleton 1093 (m1093 H hv hs)) (range_singleton 1094 (m1094 H hv))) (range_join (range_singleton 1095 (m1095 H hv hs)) (range_singleton 1096 (m1096 H hv hs))))) (range_join (range_join (range_join (range_singleton 1097 (m1097 H hv)) (range_singleton 1098 (m1098 H hv hs))) (range_join (range_singleton 1099 (m1099 H hv)) (range_singleton 1100 (m1100 H hv hs)))) (range_join (range_join (range_singleton 1101 (m1101 H hv)) (range_singleton 1102 (m1102 H hv))) (range_join (range_singleton 1103 (m1103 H hv)) (range_singleton 1104 (m1104 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 1105 (m1105 H hv)) (range_singleton 1106 (m1106 H hs))) (range_join (range_singleton 1107 (m1107 H hv hs)) (range_singleton 1108 (m1108 H hv hs)))) (range_join (range_join (range_singleton 1109 (m1109 H hv hs)) (range_singleton 1110 (m1110 H hv hs))) (range_join (range_singleton 1111 (m1111 H hv)) (range_singleton 1112 (m1112 H hv hs))))) (range_join (range_join (range_join (range_singleton 1113 (m1113 H hv hs)) (range_singleton 1114 (m1114 H hv hs))) (range_join (range_singleton 1115 (m1115 H hs)) (range_singleton 1116 (m1116 H hv hs)))) (range_join (range_join (range_singleton 1117 (m1117 H hv)) (range_singleton 1118 (m1118 H hv hs))) (range_join (range_singleton 1119 (m1119 H hv)) (range_singleton 1120 (m1120 H hv)))))))

private theorem range1121 : ∀ n, 1121 ≤ n → n < 1153 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 1121 (m1121 H hv hs)) (range_singleton 1122 (m1122 H hv hs))) (range_join (range_singleton 1123 (m1123 H hv)) (range_singleton 1124 (m1124 H hv)))) (range_join (range_join (range_singleton 1125 (m1125 H hv hs)) (range_singleton 1126 (m1126 H hv))) (range_join (range_singleton 1127 (m1127 H hv hs)) (range_singleton 1128 (m1128 H hv hs))))) (range_join (range_join (range_join (range_singleton 1129 (m1129 H hv)) (range_singleton 1130 (m1130 H hv))) (range_join (range_singleton 1131 (m1131 H hv hs)) (range_singleton 1132 (m1132 H hv hs)))) (range_join (range_join (range_singleton 1133 (m1133 H hv hs)) (range_singleton 1134 (m1134 H hv hs))) (range_join (range_singleton 1135 (m1135 H hv hs)) (range_singleton 1136 (m1136 H hv)))))) (range_join (range_join (range_join (range_join (range_singleton 1137 (m1137 H hv hs)) (range_singleton 1138 (m1138 H hv))) (range_join (range_singleton 1139 (m1139 H hv hs)) (range_singleton 1140 (m1140 H hv)))) (range_join (range_join (range_singleton 1141 (m1141 H hv hs)) (range_singleton 1142 (m1142 H hv hs))) (range_join (range_singleton 1143 (m1143 H hv)) (range_singleton 1144 (m1144 H hv hs))))) (range_join (range_join (range_join (range_singleton 1145 (m1145 H hv hs)) (range_singleton 1146 (m1146 H hv))) (range_join (range_singleton 1147 (m1147 H hv hs)) (range_singleton 1148 (m1148 H hv hs)))) (range_join (range_join (range_singleton 1149 (m1149 H hv)) (range_singleton 1150 (m1150 H hv))) (range_join (range_singleton 1151 (m1151 H hv)) (range_singleton 1152 (m1152 H hv hs)))))))

private theorem range1153 : ∀ n, 1153 ≤ n → n < 1185 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 1153 (m1153 H hv)) (range_singleton 1154 (m1154 H hv hs))) (range_join (range_singleton 1155 (m1155 H hv)) (range_singleton 1156 (m1156 H hv hs)))) (range_join (range_join (range_singleton 1157 (m1157 H hv hs)) (range_singleton 1158 (m1158 H hv hs))) (range_join (range_singleton 1159 (m1159 H hv hs)) (range_singleton 1160 (m1160 H hv hs))))) (range_join (range_join (range_join (range_singleton 1161 (m1161 H hv hs)) (range_singleton 1162 (m1162 H hv))) (range_join (range_singleton 1163 (m1163 H hv hs)) (range_singleton 1164 (m1164 H hv hs)))) (range_join (range_join (range_singleton 1165 (m1165 H hv hs)) (range_singleton 1166 (m1166 H hv hs))) (range_join (range_singleton 1167 (m1167 H hv)) (range_singleton 1168 (m1168 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 1169 (m1169 H hv)) (range_singleton 1170 (m1170 H hv))) (range_join (range_singleton 1171 (m1171 H hv)) (range_singleton 1172 (m1172 H hv hs)))) (range_join (range_join (range_singleton 1173 (m1173 H hv hs)) (range_singleton 1174 (m1174 H hv))) (range_join (range_singleton 1175 (m1175 H hv hs)) (range_singleton 1176 (m1176 H hv))))) (range_join (range_join (range_join (range_singleton 1177 (m1177 H hv hs)) (range_singleton 1178 (m1178 H hv hs))) (range_join (range_singleton 1179 (m1179 H hv)) (range_singleton 1180 (m1180 H hv hs)))) (range_join (range_join (range_singleton 1181 (m1181 H hv)) (range_singleton 1182 (m1182 H hv))) (range_join (range_singleton 1183 (m1183 H hv)) (range_singleton 1184 (m1184 H hv hs)))))))

private theorem range1185 : ∀ n, 1185 ≤ n → n < 1217 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 1185 (m1185 H hv hs)) (range_singleton 1186 (m1186 H hv hs))) (range_join (range_singleton 1187 (m1187 H hv)) (range_singleton 1188 (m1188 H hv hs)))) (range_join (range_join (range_singleton 1189 (m1189 H hv)) (range_singleton 1190 (m1190 H hv hs))) (range_join (range_singleton 1191 (m1191 H hv hs)) (range_singleton 1192 (m1192 H hv hs))))) (range_join (range_join (range_join (range_singleton 1193 (m1193 H hv hs)) (range_singleton 1194 (m1194 H hv))) (range_join (range_singleton 1195 (m1195 H hv)) (range_singleton 1196 (m1196 H hv hs)))) (range_join (range_join (range_singleton 1197 (m1197 H hv hs)) (range_singleton 1198 (m1198 H hv hs))) (range_join (range_singleton 1199 (m1199 H hv hs)) (range_singleton 1200 (m1200 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 1201 (m1201 H hv hs)) (range_singleton 1202 (m1202 H hv hs))) (range_join (range_singleton 1203 (m1203 H hv hs)) (range_singleton 1204 (m1204 H hv hs)))) (range_join (range_join (range_singleton 1205 (m1205 H hv)) (range_singleton 1206 (m1206 H hv hs))) (range_join (range_singleton 1207 (m1207 H hv)) (range_singleton 1208 (m1208 H hv hs))))) (range_join (range_join (range_join (range_singleton 1209 (m1209 H hv)) (range_singleton 1210 (m1210 H hv hs))) (range_join (range_singleton 1211 (m1211 H hv hs)) (range_singleton 1212 (m1212 H hv)))) (range_join (range_join (range_singleton 1213 (m1213 H hv hs)) (range_singleton 1214 (m1214 H hv hs))) (range_join (range_singleton 1215 (m1215 H hv hs)) (range_singleton 1216 (m1216 H hv hs)))))))

private theorem range1217 : ∀ n, 1217 ≤ n → n < 1249 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 1217 (m1217 H hv)) (range_singleton 1218 (m1218 H hv))) (range_join (range_singleton 1219 (m1219 H hv hs)) (range_singleton 1220 (m1220 H hv hs)))) (range_join (range_join (range_singleton 1221 (m1221 H hv hs)) (range_singleton 1222 (m1222 H hv hs))) (range_join (range_singleton 1223 (m1223 H hv hs)) (range_singleton 1224 (m1224 H hv))))) (range_join (range_join (range_join (range_singleton 1225 (m1225 H hv)) (range_singleton 1226 (m1226 H hv hs))) (range_join (range_singleton 1227 (m1227 H hv)) (range_singleton 1228 (m1228 H hv hs)))) (range_join (range_join (range_singleton 1229 (m1229 H hv hs)) (range_singleton 1230 (m1230 H hv))) (range_join (range_singleton 1231 (m1231 H hv hs)) (range_singleton 1232 (m1232 H hv)))))) (range_join (range_join (range_join (range_join (range_singleton 1233 (m1233 H hv hs)) (range_singleton 1234 (m1234 H hv))) (range_join (range_singleton 1235 (m1235 H hv hs)) (range_singleton 1236 (m1236 H hv hs)))) (range_join (range_join (range_singleton 1237 (m1237 H hv hs)) (range_singleton 1238 (m1238 H hv))) (range_join (range_singleton 1239 (m1239 H hv hs)) (range_singleton 1240 (m1240 H hv hs))))) (range_join (range_join (range_join (range_singleton 1241 (m1241 H hv hs)) (range_singleton 1242 (m1242 H hv))) (range_join (range_singleton 1243 (m1243 H hv)) (range_singleton 1244 (m1244 H hv hs)))) (range_join (range_join (range_singleton 1245 (m1245 H hv hs)) (range_singleton 1246 (m1246 H hv))) (range_join (range_singleton 1247 (m1247 H hv hs)) (range_singleton 1248 (m1248 H hv)))))))

private theorem range1249 : ∀ n, 1249 ≤ n → n < 1281 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 1249 (m1249 H hv hs)) (range_singleton 1250 (m1250 H hv hs))) (range_join (range_singleton 1251 (m1251 H hv)) (range_singleton 1252 (m1252 H hv hs)))) (range_join (range_join (range_singleton 1253 (m1253 H hv hs)) (range_singleton 1254 (m1254 H hv))) (range_join (range_singleton 1255 (m1255 H hv hs)) (range_singleton 1256 (m1256 H hv))))) (range_join (range_join (range_join (range_singleton 1257 (m1257 H hv)) (range_singleton 1258 (m1258 H hv hs))) (range_join (range_singleton 1259 (m1259 H hv hs)) (range_singleton 1260 (m1260 H hv)))) (range_join (range_join (range_singleton 1261 (m1261 H hv hs)) (range_singleton 1262 (m1262 H hv hs))) (range_join (range_singleton 1263 (m1263 H hv)) (range_singleton 1264 (m1264 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 1265 (m1265 H hv hs)) (range_singleton 1266 (m1266 H hv hs))) (range_join (range_singleton 1267 (m1267 H hv hs)) (range_singleton 1268 (m1268 H hv hs)))) (range_join (range_join (range_singleton 1269 (m1269 H hv hs)) (range_singleton 1270 (m1270 H hv hs))) (range_join (range_singleton 1271 (m1271 H hv)) (range_singleton 1272 (m1272 H hv hs))))) (range_join (range_join (range_join (range_singleton 1273 (m1273 H hv hs)) (range_singleton 1274 (m1274 H hv hs))) (range_join (range_singleton 1275 (m1275 H hv)) (range_singleton 1276 (m1276 H hv)))) (range_join (range_join (range_singleton 1277 (m1277 H hv hs)) (range_singleton 1278 (m1278 H hv))) (range_join (range_singleton 1279 (m1279 H hv hs)) (range_singleton 1280 (m1280 H hv)))))))

private theorem range1281 : ∀ n, 1281 ≤ n → n < 1313 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 1281 (m1281 H hv hs)) (range_singleton 1282 (m1282 H hv))) (range_join (range_singleton 1283 (m1283 H hv hs)) (range_singleton 1284 (m1284 H hv hs)))) (range_join (range_join (range_singleton 1285 (m1285 H hv)) (range_singleton 1286 (m1286 H hv hs))) (range_join (range_singleton 1287 (m1287 H hv hs)) (range_singleton 1288 (m1288 H hv hs))))) (range_join (range_join (range_join (range_singleton 1289 (m1289 H hv hs)) (range_singleton 1290 (m1290 H hv))) (range_join (range_singleton 1291 (m1291 H hv hs)) (range_singleton 1292 (m1292 H hv hs)))) (range_join (range_join (range_singleton 1293 (m1293 H hv)) (range_singleton 1294 (m1294 H hv hs))) (range_join (range_singleton 1295 (m1295 H hv)) (range_singleton 1296 (m1296 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 1297 (m1297 H hv)) (range_singleton 1298 (m1298 H hv hs))) (range_join (range_singleton 1299 (m1299 H hv hs)) (range_singleton 1300 (m1300 H hv)))) (range_join (range_join (range_singleton 1301 (m1301 H hv)) (range_singleton 1302 (m1302 H hv))) (range_join (range_singleton 1303 (m1303 H hv hs)) (range_singleton 1304 (m1304 H hv hs))))) (range_join (range_join (range_join (range_singleton 1305 (m1305 H hv)) (range_singleton 1306 (m1306 H hv hs))) (range_join (range_singleton 1307 (m1307 H hv hs)) (range_singleton 1308 (m1308 H hv)))) (range_join (range_join (range_singleton 1309 (m1309 H hv)) (range_singleton 1310 (m1310 H hv))) (range_join (range_singleton 1311 (m1311 H hv hs)) (range_singleton 1312 (m1312 H hv)))))))

private theorem range1313 : ∀ n, 1313 ≤ n → n < 1345 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 1313 (m1313 H hv hs)) (range_singleton 1314 (m1314 H hv hs))) (range_join (range_singleton 1315 (m1315 H hv)) (range_singleton 1316 (m1316 H hv hs)))) (range_join (range_join (range_singleton 1317 (m1317 H hv)) (range_singleton 1318 (m1318 H hv hs))) (range_join (range_singleton 1319 (m1319 H hv hs)) (range_singleton 1320 (m1320 H hv))))) (range_join (range_join (range_join (range_singleton 1321 (m1321 H hv hs)) (range_singleton 1322 (m1322 H hv))) (range_join (range_singleton 1323 (m1323 H hv hs)) (range_singleton 1324 (m1324 H hv)))) (range_join (range_join (range_singleton 1325 (m1325 H hv)) (range_singleton 1326 (m1326 H hv hs))) (range_join (range_singleton 1327 (m1327 H hv hs)) (range_singleton 1328 (m1328 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 1329 (m1329 H hv hs)) (range_singleton 1330 (m1330 H hv))) (range_join (range_singleton 1331 (m1331 H hv hs)) (range_singleton 1332 (m1332 H hv hs)))) (range_join (range_join (range_singleton 1333 (m1333 H hv)) (range_singleton 1334 (m1334 H hv hs))) (range_join (range_singleton 1335 (m1335 H hv hs)) (range_singleton 1336 (m1336 H hv hs))))) (range_join (range_join (range_join (range_singleton 1337 (m1337 H hv)) (range_singleton 1338 (m1338 H hv hs))) (range_join (range_singleton 1339 (m1339 H hv)) (range_singleton 1340 (m1340 H hv hs)))) (range_join (range_join (range_singleton 1341 (m1341 H hv hs)) (range_singleton 1342 (m1342 H hv hs))) (range_join (range_singleton 1343 (m1343 H hv hs)) (range_singleton 1344 (m1344 H hv)))))))

private theorem range1345 : ∀ n, 1345 ≤ n → n < 1377 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 1345 (m1345 H hv hs)) (range_singleton 1346 (m1346 H hv))) (range_join (range_singleton 1347 (m1347 H hv hs)) (range_singleton 1348 (m1348 H hv hs)))) (range_join (range_join (range_singleton 1349 (m1349 H hv)) (range_singleton 1350 (m1350 H hv))) (range_join (range_singleton 1351 (m1351 H hv hs)) (range_singleton 1352 (m1352 H hv))))) (range_join (range_join (range_join (range_singleton 1353 (m1353 H hv hs)) (range_singleton 1354 (m1354 H hv))) (range_join (range_singleton 1355 (m1355 H hv)) (range_singleton 1356 (m1356 H hv hs)))) (range_join (range_join (range_singleton 1357 (m1357 H hv hs)) (range_singleton 1358 (m1358 H hv))) (range_join (range_singleton 1359 (m1359 H hv hs)) (range_singleton 1360 (m1360 H hv)))))) (range_join (range_join (range_join (range_join (range_singleton 1361 (m1361 H hv hs)) (range_singleton 1362 (m1362 H hv))) (range_join (range_singleton 1363 (m1363 H hv hs)) (range_singleton 1364 (m1364 H hv hs)))) (range_join (range_join (range_singleton 1365 (m1365 H hv hs)) (range_singleton 1366 (m1366 H hv))) (range_join (range_singleton 1367 (m1367 H hv hs)) (range_singleton 1368 (m1368 H hv hs))))) (range_join (range_join (range_join (range_singleton 1369 (m1369 H hv)) (range_singleton 1370 (m1370 H hv))) (range_join (range_singleton 1371 (m1371 H hv)) (range_singleton 1372 (m1372 H hv hs)))) (range_join (range_join (range_singleton 1373 (m1373 H hv hs)) (range_singleton 1374 (m1374 H hv hs))) (range_join (range_singleton 1375 (m1375 H hv)) (range_singleton 1376 (m1376 H hv hs)))))))

private theorem range1377 : ∀ n, 1377 ≤ n → n < 1409 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 1377 (m1377 H hv)) (range_singleton 1378 (m1378 H hv hs))) (range_join (range_singleton 1379 (m1379 H hv)) (range_singleton 1380 (m1380 H hv)))) (range_join (range_join (range_singleton 1381 (m1381 H hv hs)) (range_singleton 1382 (m1382 H hv hs))) (range_join (range_singleton 1383 (m1383 H hv hs)) (range_singleton 1384 (m1384 H hv hs))))) (range_join (range_join (range_join (range_singleton 1385 (m1385 H hv hs)) (range_singleton 1386 (m1386 H hv hs))) (range_join (range_singleton 1387 (m1387 H hv)) (range_singleton 1388 (m1388 H hv hs)))) (range_join (range_join (range_singleton 1389 (m1389 H hv)) (range_singleton 1390 (m1390 H hv hs))) (range_join (range_singleton 1391 (m1391 H hv hs)) (range_singleton 1392 (m1392 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 1393 (m1393 H hv hs)) (range_singleton 1394 (m1394 H hv hs))) (range_join (range_singleton 1395 (m1395 H hv hs)) (range_singleton 1396 (m1396 H hv hs)))) (range_join (range_join (range_singleton 1397 (m1397 H hv)) (range_singleton 1398 (m1398 H hv hs))) (range_join (range_singleton 1399 (m1399 H hv hs)) (range_singleton 1400 (m1400 H hv))))) (range_join (range_join (range_join (range_singleton 1401 (m1401 H hv hs)) (range_singleton 1402 (m1402 H hv hs))) (range_join (range_singleton 1403 (m1403 H hv hs)) (range_singleton 1404 (m1404 H hv)))) (range_join (range_join (range_singleton 1405 (m1405 H hv hs)) (range_singleton 1406 (m1406 H hv hs))) (range_join (range_singleton 1407 (m1407 H hv)) (range_singleton 1408 (m1408 H hv hs)))))))

private theorem range1409 : ∀ n, 1409 ≤ n → n < 1441 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 1409 (m1409 H hv hs)) (range_singleton 1410 (m1410 H hv))) (range_join (range_singleton 1411 (m1411 H hv)) (range_singleton 1412 (m1412 H hv hs)))) (range_join (range_join (range_singleton 1413 (m1413 H hv hs)) (range_singleton 1414 (m1414 H hv hs))) (range_join (range_singleton 1415 (m1415 H hv hs)) (range_singleton 1416 (m1416 H hv hs))))) (range_join (range_join (range_join (range_singleton 1417 (m1417 H hv hs)) (range_singleton 1418 (m1418 H hv hs))) (range_join (range_singleton 1419 (m1419 H hv)) (range_singleton 1420 (m1420 H hv hs)))) (range_join (range_join (range_singleton 1421 (m1421 H hv hs)) (range_singleton 1422 (m1422 H hv))) (range_join (range_singleton 1423 (m1423 H hv)) (range_singleton 1424 (m1424 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 1425 (m1425 H hv hs)) (range_singleton 1426 (m1426 H hv))) (range_join (range_singleton 1427 (m1427 H hv)) (range_singleton 1428 (m1428 H hv hs)))) (range_join (range_join (range_singleton 1429 (m1429 H hv)) (range_singleton 1430 (m1430 H hv))) (range_join (range_singleton 1431 (m1431 H hv)) (range_singleton 1432 (m1432 H hv hs))))) (range_join (range_join (range_join (range_singleton 1433 (m1433 H hv hs)) (range_singleton 1434 (m1434 H hv hs))) (range_join (range_singleton 1435 (m1435 H hv)) (range_singleton 1436 (m1436 H hv hs)))) (range_join (range_join (range_singleton 1437 (m1437 H hv hs)) (range_singleton 1438 (m1438 H hv))) (range_join (range_singleton 1439 (m1439 H hv)) (range_singleton 1440 (m1440 H hv hs)))))))

private theorem range1441 : ∀ n, 1441 ≤ n → n < 1473 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 1441 (m1441 H hv)) (range_singleton 1442 (m1442 H hv hs))) (range_join (range_singleton 1443 (m1443 H hv)) (range_singleton 1444 (m1444 H hv hs)))) (range_join (range_join (range_singleton 1445 (m1445 H hv hs)) (range_singleton 1446 (m1446 H hv))) (range_join (range_singleton 1447 (m1447 H hv hs)) (range_singleton 1448 (m1448 H hv hs))))) (range_join (range_join (range_join (range_singleton 1449 (m1449 H hv hs)) (range_singleton 1450 (m1450 H hv hs))) (range_join (range_singleton 1451 (m1451 H hv hs)) (range_singleton 1452 (m1452 H hv hs)))) (range_join (range_join (range_singleton 1453 (m1453 H hv)) (range_singleton 1454 (m1454 H hv hs))) (range_join (range_singleton 1455 (m1455 H hv hs)) (range_singleton 1456 (m1456 H hv)))))) (range_join (range_join (range_join (range_join (range_singleton 1457 (m1457 H hv)) (range_singleton 1458 (m1458 H hv hs))) (range_join (range_singleton 1459 (m1459 H hv hs)) (range_singleton 1460 (m1460 H hv hs)))) (range_join (range_join (range_singleton 1461 (m1461 H hv)) (range_singleton 1462 (m1462 H hv hs))) (range_join (range_singleton 1463 (m1463 H hv)) (range_singleton 1464 (m1464 H hv hs))))) (range_join (range_join (range_join (range_singleton 1465 (m1465 H hv hs)) (range_singleton 1466 (m1466 H hv hs))) (range_join (range_singleton 1467 (m1467 H hv)) (range_singleton 1468 (m1468 H hv hs)))) (range_join (range_join (range_singleton 1469 (m1469 H hv)) (range_singleton 1470 (m1470 H hv hs))) (range_join (range_singleton 1471 (m1471 H hv)) (range_singleton 1472 (m1472 H hv hs)))))))

private theorem range1473 : ∀ n, 1473 ≤ n → n < 1505 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 1473 (m1473 H hv hs)) (range_singleton 1474 (m1474 H hv hs))) (range_join (range_singleton 1475 (m1475 H hv hs)) (range_singleton 1476 (m1476 H hv hs)))) (range_join (range_join (range_singleton 1477 (m1477 H hv hs)) (range_singleton 1478 (m1478 H hv hs))) (range_join (range_singleton 1479 (m1479 H hv hs)) (range_singleton 1480 (m1480 H hv))))) (range_join (range_join (range_join (range_singleton 1481 (m1481 H hv)) (range_singleton 1482 (m1482 H hv hs))) (range_join (range_singleton 1483 (m1483 H hv hs)) (range_singleton 1484 (m1484 H hv hs)))) (range_join (range_join (range_singleton 1485 (m1485 H hv hs)) (range_singleton 1486 (m1486 H hv hs))) (range_join (range_singleton 1487 (m1487 H hv hs)) (range_singleton 1488 (m1488 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 1489 (m1489 H hv hs)) (range_singleton 1490 (m1490 H hv hs))) (range_join (range_singleton 1491 (m1491 H hv)) (range_singleton 1492 (m1492 H hv hs)))) (range_join (range_join (range_singleton 1493 (m1493 H hv)) (range_singleton 1494 (m1494 H hv))) (range_join (range_singleton 1495 (m1495 H hv hs)) (range_singleton 1496 (m1496 H hv hs))))) (range_join (range_join (range_join (range_singleton 1497 (m1497 H hv)) (range_singleton 1498 (m1498 H hv))) (range_join (range_singleton 1499 (m1499 H hv hs)) (range_singleton 1500 (m1500 H hv hs)))) (range_join (range_join (range_singleton 1501 (m1501 H hv)) (range_singleton 1502 (m1502 H hv))) (range_join (range_singleton 1503 (m1503 H hv)) (range_singleton 1504 (m1504 H hv hs)))))))

private theorem range1505 : ∀ n, 1505 ≤ n → n < 1537 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 1505 (m1505 H hv hs)) (range_singleton 1506 (m1506 H hv hs))) (range_join (range_singleton 1507 (m1507 H hv hs)) (range_singleton 1508 (m1508 H hv)))) (range_join (range_join (range_singleton 1509 (m1509 H hv hs)) (range_singleton 1510 (m1510 H hv hs))) (range_join (range_singleton 1511 (m1511 H hv hs)) (range_singleton 1512 (m1512 H hv))))) (range_join (range_join (range_join (range_singleton 1513 (m1513 H hv)) (range_singleton 1514 (m1514 H hv hs))) (range_join (range_singleton 1515 (m1515 H hv hs)) (range_singleton 1516 (m1516 H hv hs)))) (range_join (range_join (range_singleton 1517 (m1517 H hv)) (range_singleton 1518 (m1518 H hv))) (range_join (range_singleton 1519 (m1519 H hv)) (range_singleton 1520 (m1520 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 1521 (m1521 H hv)) (range_singleton 1522 (m1522 H hv))) (range_join (range_singleton 1523 (m1523 H hv)) (range_singleton 1524 (m1524 H hv)))) (range_join (range_join (range_singleton 1525 (m1525 H hv)) (range_singleton 1526 (m1526 H hv hs))) (range_join (range_singleton 1527 (m1527 H hv)) (range_singleton 1528 (m1528 H hv))))) (range_join (range_join (range_join (range_singleton 1529 (m1529 H hv)) (range_singleton 1530 (m1530 H hv hs))) (range_join (range_singleton 1531 (m1531 H hv hs)) (range_singleton 1532 (m1532 H hv hs)))) (range_join (range_join (range_singleton 1533 (m1533 H hv)) (range_singleton 1534 (m1534 H hv hs))) (range_join (range_singleton 1535 (m1535 H hv)) (range_singleton 1536 (m1536 H hv hs)))))))

private theorem range1537 : ∀ n, 1537 ≤ n → n < 1569 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 1537 (m1537 H hv)) (range_singleton 1538 (m1538 H hv hs))) (range_join (range_singleton 1539 (m1539 H hv)) (range_singleton 1540 (m1540 H hv)))) (range_join (range_join (range_singleton 1541 (m1541 H hv)) (range_singleton 1542 (m1542 H hv))) (range_join (range_singleton 1543 (m1543 H hv hs)) (range_singleton 1544 (m1544 H hv hs))))) (range_join (range_join (range_join (range_singleton 1545 (m1545 H hv hs)) (range_singleton 1546 (m1546 H hv hs))) (range_join (range_singleton 1547 (m1547 H hv)) (range_singleton 1548 (m1548 H hv)))) (range_join (range_join (range_singleton 1549 (m1549 H hv hs)) (range_singleton 1550 (m1550 H hv))) (range_join (range_singleton 1551 (m1551 H hv)) (range_singleton 1552 (m1552 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 1553 (m1553 H hv hs)) (range_singleton 1554 (m1554 H hv))) (range_join (range_singleton 1555 (m1555 H hv hs)) (range_singleton 1556 (m1556 H hv hs)))) (range_join (range_join (range_singleton 1557 (m1557 H hv)) (range_singleton 1558 (m1558 H hv hs))) (range_join (range_singleton 1559 (m1559 H hv hs)) (range_singleton 1560 (m1560 H hv))))) (range_join (range_join (range_join (range_singleton 1561 (m1561 H hv)) (range_singleton 1562 (m1562 H hv hs))) (range_join (range_singleton 1563 (m1563 H hv)) (range_singleton 1564 (m1564 H hv hs)))) (range_join (range_join (range_singleton 1565 (m1565 H hv hs)) (range_singleton 1566 (m1566 H hv))) (range_join (range_singleton 1567 (m1567 H hv hs)) (range_singleton 1568 (m1568 H hv hs)))))))

private theorem range1569 : ∀ n, 1569 ≤ n → n < 1601 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 1569 (m1569 H hv hs)) (range_singleton 1570 (m1570 H hv hs))) (range_join (range_singleton 1571 (m1571 H hv)) (range_singleton 1572 (m1572 H hv hs)))) (range_join (range_join (range_singleton 1573 (m1573 H hv hs)) (range_singleton 1574 (m1574 H hv hs))) (range_join (range_singleton 1575 (m1575 H hv hs)) (range_singleton 1576 (m1576 H hv hs))))) (range_join (range_join (range_join (range_singleton 1577 (m1577 H hv hs)) (range_singleton 1578 (m1578 H hv hs))) (range_join (range_singleton 1579 (m1579 H hv)) (range_singleton 1580 (m1580 H hv hs)))) (range_join (range_join (range_singleton 1581 (m1581 H hv hs)) (range_singleton 1582 (m1582 H hv hs))) (range_join (range_singleton 1583 (m1583 H hv)) (range_singleton 1584 (m1584 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 1585 (m1585 H hv hs)) (range_singleton 1586 (m1586 H hv hs))) (range_join (range_singleton 1587 (m1587 H hv)) (range_singleton 1588 (m1588 H hv hs)))) (range_join (range_join (range_singleton 1589 (m1589 H hv hs)) (range_singleton 1590 (m1590 H hv))) (range_join (range_singleton 1591 (m1591 H hv hs)) (range_singleton 1592 (m1592 H hv))))) (range_join (range_join (range_join (range_singleton 1593 (m1593 H hv hs)) (range_singleton 1594 (m1594 H hv hs))) (range_join (range_singleton 1595 (m1595 H hv hs)) (range_singleton 1596 (m1596 H hv hs)))) (range_join (range_join (range_singleton 1597 (m1597 H hv hs)) (range_singleton 1598 (m1598 H hv))) (range_join (range_singleton 1599 (m1599 H hv hs)) (range_singleton 1600 (m1600 H hv hs)))))))

private theorem range1601 : ∀ n, 1601 ≤ n → n < 1633 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 1601 (m1601 H hv)) (range_singleton 1602 (m1602 H hv hs))) (range_join (range_singleton 1603 (m1603 H hv hs)) (range_singleton 1604 (m1604 H hv hs)))) (range_join (range_join (range_singleton 1605 (m1605 H hv)) (range_singleton 1606 (m1606 H hv))) (range_join (range_singleton 1607 (m1607 H hv)) (range_singleton 1608 (m1608 H hv))))) (range_join (range_join (range_join (range_singleton 1609 (m1609 H hv hs)) (range_singleton 1610 (m1610 H hv))) (range_join (range_singleton 1611 (m1611 H hv hs)) (range_singleton 1612 (m1612 H hv hs)))) (range_join (range_join (range_singleton 1613 (m1613 H hv hs)) (range_singleton 1614 (m1614 H hv))) (range_join (range_singleton 1615 (m1615 H hv hs)) (range_singleton 1616 (m1616 H hv)))))) (range_join (range_join (range_join (range_join (range_singleton 1617 (m1617 H hv hs)) (range_singleton 1618 (m1618 H hv))) (range_join (range_singleton 1619 (m1619 H hv)) (range_singleton 1620 (m1620 H hv hs)))) (range_join (range_join (range_singleton 1621 (m1621 H hv hs)) (range_singleton 1622 (m1622 H hv hs))) (range_join (range_singleton 1623 (m1623 H hv)) (range_singleton 1624 (m1624 H hv))))) (range_join (range_join (range_join (range_singleton 1625 (m1625 H hv)) (range_singleton 1626 (m1626 H hv hs))) (range_join (range_singleton 1627 (m1627 H hv hs)) (range_singleton 1628 (m1628 H hv)))) (range_join (range_join (range_singleton 1629 (m1629 H hv hs)) (range_singleton 1630 (m1630 H hv hs))) (range_join (range_singleton 1631 (m1631 H hv hs)) (range_singleton 1632 (m1632 H hv hs)))))))

private theorem range1633 : ∀ n, 1633 ≤ n → n < 1665 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 1633 (m1633 H hv)) (range_singleton 1634 (m1634 H hv))) (range_join (range_singleton 1635 (m1635 H hv hs)) (range_singleton 1636 (m1636 H hv hs)))) (range_join (range_join (range_singleton 1637 (m1637 H hv)) (range_singleton 1638 (m1638 H hv hs))) (range_join (range_singleton 1639 (m1639 H hv hs)) (range_singleton 1640 (m1640 H hv))))) (range_join (range_join (range_join (range_singleton 1641 (m1641 H hv hs)) (range_singleton 1642 (m1642 H hv hs))) (range_join (range_singleton 1643 (m1643 H hv)) (range_singleton 1644 (m1644 H hv)))) (range_join (range_join (range_singleton 1645 (m1645 H hv hs)) (range_singleton 1646 (m1646 H hv hs))) (range_join (range_singleton 1647 (m1647 H hv hs)) (range_singleton 1648 (m1648 H hv)))))) (range_join (range_join (range_join (range_join (range_singleton 1649 (m1649 H hv hs)) (range_singleton 1650 (m1650 H hv hs))) (range_join (range_singleton 1651 (m1651 H hv)) (range_singleton 1652 (m1652 H hv)))) (range_join (range_join (range_singleton 1653 (m1653 H hv hs)) (range_singleton 1654 (m1654 H hv))) (range_join (range_singleton 1655 (m1655 H hv)) (range_singleton 1656 (m1656 H hv))))) (range_join (range_join (range_join (range_singleton 1657 (m1657 H hv hs)) (range_singleton 1658 (m1658 H hv hs))) (range_join (range_singleton 1659 (m1659 H hv)) (range_singleton 1660 (m1660 H hv hs)))) (range_join (range_join (range_singleton 1661 (m1661 H hv)) (range_singleton 1662 (m1662 H hv hs))) (range_join (range_singleton 1663 (m1663 H hv hs)) (range_singleton 1664 (m1664 H hv hs)))))))

private theorem range1665 : ∀ n, 1665 ≤ n → n < 1697 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 1665 (m1665 H hv)) (range_singleton 1666 (m1666 H hv hs))) (range_join (range_singleton 1667 (m1667 H hv)) (range_singleton 1668 (m1668 H hv hs)))) (range_join (range_join (range_singleton 1669 (m1669 H hv hs)) (range_singleton 1670 (m1670 H hv hs))) (range_join (range_singleton 1671 (m1671 H hv hs)) (range_singleton 1672 (m1672 H hv))))) (range_join (range_join (range_join (range_singleton 1673 (m1673 H hv hs)) (range_singleton 1674 (m1674 H hv))) (range_join (range_singleton 1675 (m1675 H hv hs)) (range_singleton 1676 (m1676 H hv hs)))) (range_join (range_join (range_singleton 1677 (m1677 H hv)) (range_singleton 1678 (m1678 H hv))) (range_join (range_singleton 1679 (m1679 H hv hs)) (range_singleton 1680 (m1680 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 1681 (m1681 H hv hs)) (range_singleton 1682 (m1682 H hv hs))) (range_join (range_singleton 1683 (m1683 H hv hs)) (range_singleton 1684 (m1684 H hv)))) (range_join (range_join (range_singleton 1685 (m1685 H hv)) (range_singleton 1686 (m1686 H hv hs))) (range_join (range_singleton 1687 (m1687 H hv)) (range_singleton 1688 (m1688 H hv hs))))) (range_join (range_join (range_join (range_singleton 1689 (m1689 H hv hs)) (range_singleton 1690 (m1690 H hv hs))) (range_join (range_singleton 1691 (m1691 H hv hs)) (range_singleton 1692 (m1692 H hv hs)))) (range_join (range_join (range_singleton 1693 (m1693 H hv hs)) (range_singleton 1694 (m1694 H hv))) (range_join (range_singleton 1695 (m1695 H hv)) (range_singleton 1696 (m1696 H hv hs)))))))

private theorem range1697 : ∀ n, 1697 ≤ n → n < 1729 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 1697 (m1697 H hv)) (range_singleton 1698 (m1698 H hv hs))) (range_join (range_singleton 1699 (m1699 H hv hs)) (range_singleton 1700 (m1700 H hv hs)))) (range_join (range_join (range_singleton 1701 (m1701 H hv hs)) (range_singleton 1702 (m1702 H hv hs))) (range_join (range_singleton 1703 (m1703 H hv hs)) (range_singleton 1704 (m1704 H hv hs))))) (range_join (range_join (range_join (range_singleton 1705 (m1705 H hv)) (range_singleton 1706 (m1706 H hv hs))) (range_join (range_singleton 1707 (m1707 H hv hs)) (range_singleton 1708 (m1708 H hv hs)))) (range_join (range_join (range_singleton 1709 (m1709 H hv)) (range_singleton 1710 (m1710 H hv))) (range_join (range_singleton 1711 (m1711 H hv hs)) (range_singleton 1712 (m1712 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 1713 (m1713 H hv)) (range_singleton 1714 (m1714 H hv))) (range_join (range_singleton 1715 (m1715 H hv hs)) (range_singleton 1716 (m1716 H hv)))) (range_join (range_join (range_singleton 1717 (m1717 H hv)) (range_singleton 1718 (m1718 H hv hs))) (range_join (range_singleton 1719 (m1719 H hv hs)) (range_singleton 1720 (m1720 H hv hs))))) (range_join (range_join (range_join (range_singleton 1721 (m1721 H hv hs)) (range_singleton 1722 (m1722 H hv))) (range_join (range_singleton 1723 (m1723 H hv)) (range_singleton 1724 (m1724 H hv hs)))) (range_join (range_join (range_singleton 1725 (m1725 H hv hs)) (range_singleton 1726 (m1726 H hv))) (range_join (range_singleton 1727 (m1727 H hv hs)) (range_singleton 1728 (m1728 H hv hs)))))))

private theorem range1729 : ∀ n, 1729 ≤ n → n < 1761 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 1729 (m1729 H hv hs)) (range_singleton 1730 (m1730 H hv))) (range_join (range_singleton 1731 (m1731 H hv)) (range_singleton 1732 (m1732 H hv)))) (range_join (range_join (range_singleton 1733 (m1733 H hv hs)) (range_singleton 1734 (m1734 H hv))) (range_join (range_singleton 1735 (m1735 H hv hs)) (range_singleton 1736 (m1736 H hv))))) (range_join (range_join (range_join (range_singleton 1737 (m1737 H hv)) (range_singleton 1738 (m1738 H hv hs))) (range_join (range_singleton 1739 (m1739 H hv hs)) (range_singleton 1740 (m1740 H hv hs)))) (range_join (range_join (range_singleton 1741 (m1741 H hv hs)) (range_singleton 1742 (m1742 H hv))) (range_join (range_singleton 1743 (m1743 H hv)) (range_singleton 1744 (m1744 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 1745 (m1745 H hv hs)) (range_singleton 1746 (m1746 H hv hs))) (range_join (range_singleton 1747 (m1747 H hv)) (range_singleton 1748 (m1748 H hv hs)))) (range_join (range_join (range_singleton 1749 (m1749 H hv hs)) (range_singleton 1750 (m1750 H hv))) (range_join (range_singleton 1751 (m1751 H hv hs)) (range_singleton 1752 (m1752 H hv hs))))) (range_join (range_join (range_join (range_singleton 1753 (m1753 H hv hs)) (range_singleton 1754 (m1754 H hv))) (range_join (range_singleton 1755 (m1755 H hv hs)) (range_singleton 1756 (m1756 H hv hs)))) (range_join (range_join (range_singleton 1757 (m1757 H hv hs)) (range_singleton 1758 (m1758 H hv))) (range_join (range_singleton 1759 (m1759 H hv)) (range_singleton 1760 (m1760 H hv hs)))))))

private theorem range1761 : ∀ n, 1761 ≤ n → n < 1793 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 1761 (m1761 H hv)) (range_singleton 1762 (m1762 H hv hs))) (range_join (range_singleton 1763 (m1763 H hv)) (range_singleton 1764 (m1764 H hv hs)))) (range_join (range_join (range_singleton 1765 (m1765 H hv hs)) (range_singleton 1766 (m1766 H hv hs))) (range_join (range_singleton 1767 (m1767 H hv)) (range_singleton 1768 (m1768 H hv))))) (range_join (range_join (range_join (range_singleton 1769 (m1769 H hv hs)) (range_singleton 1770 (m1770 H hv hs))) (range_join (range_singleton 1771 (m1771 H hv)) (range_singleton 1772 (m1772 H hs)))) (range_join (range_join (range_singleton 1773 (m1773 H hv)) (range_singleton 1774 (m1774 H hv))) (range_join (range_singleton 1775 (m1775 H hv hs)) (range_singleton 1776 (m1776 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 1777 (m1777 H hv)) (range_singleton 1778 (m1778 H hv hs))) (range_join (range_singleton 1779 (m1779 H hv hs)) (range_singleton 1780 (m1780 H hv hs)))) (range_join (range_join (range_singleton 1781 (m1781 H hv)) (range_singleton 1782 (m1782 H hv))) (range_join (range_singleton 1783 (m1783 H hv hs)) (range_singleton 1784 (m1784 H hv))))) (range_join (range_join (range_join (range_singleton 1785 (m1785 H hv hs)) (range_singleton 1786 (m1786 H hv))) (range_join (range_singleton 1787 (m1787 H hv hs)) (range_singleton 1788 (m1788 H hv hs)))) (range_join (range_join (range_singleton 1789 (m1789 H hv)) (range_singleton 1790 (m1790 H hv hs))) (range_join (range_singleton 1791 (m1791 H hv)) (range_singleton 1792 (m1792 H hv hs)))))))

private theorem range1793 : ∀ n, 1793 ≤ n → n < 1825 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 1793 (m1793 H hv hs)) (range_singleton 1794 (m1794 H hv))) (range_join (range_singleton 1795 (m1795 H hv hs)) (range_singleton 1796 (m1796 H hv hs)))) (range_join (range_join (range_singleton 1797 (m1797 H hv)) (range_singleton 1798 (m1798 H hv))) (range_join (range_singleton 1799 (m1799 H hv hs)) (range_singleton 1800 (m1800 H hv hs))))) (range_join (range_join (range_join (range_singleton 1801 (m1801 H hv hs)) (range_singleton 1802 (m1802 H hv hs))) (range_join (range_singleton 1803 (m1803 H hv)) (range_singleton 1804 (m1804 H hv hs)))) (range_join (range_join (range_singleton 1805 (m1805 H hv)) (range_singleton 1806 (m1806 H hv))) (range_join (range_singleton 1807 (m1807 H hv hs)) (range_singleton 1808 (m1808 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 1809 (m1809 H hv hs)) (range_singleton 1810 (m1810 H hv hs))) (range_join (range_singleton 1811 (m1811 H hv)) (range_singleton 1812 (m1812 H hv)))) (range_join (range_join (range_singleton 1813 (m1813 H hv hs)) (range_singleton 1814 (m1814 H hv hs))) (range_join (range_singleton 1815 (m1815 H hv)) (range_singleton 1816 (m1816 H hv hs))))) (range_join (range_join (range_join (range_singleton 1817 (m1817 H hv)) (range_singleton 1818 (m1818 H hv hs))) (range_join (range_singleton 1819 (m1819 H hv hs)) (range_singleton 1820 (m1820 H hv hs)))) (range_join (range_join (range_singleton 1821 (m1821 H hv)) (range_singleton 1822 (m1822 H hv hs))) (range_join (range_singleton 1823 (m1823 H hv)) (range_singleton 1824 (m1824 H hv hs)))))))

private theorem range1825 : ∀ n, 1825 ≤ n → n < 1857 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 1825 (m1825 H hv)) (range_singleton 1826 (m1826 H hv))) (range_join (range_singleton 1827 (m1827 H hv)) (range_singleton 1828 (m1828 H hv hs)))) (range_join (range_join (range_singleton 1829 (m1829 H hv hs)) (range_singleton 1830 (m1830 H hv hs))) (range_join (range_singleton 1831 (m1831 H hv hs)) (range_singleton 1832 (m1832 H hv))))) (range_join (range_join (range_join (range_singleton 1833 (m1833 H hv)) (range_singleton 1834 (m1834 H hv))) (range_join (range_singleton 1835 (m1835 H hv hs)) (range_singleton 1836 (m1836 H hv)))) (range_join (range_join (range_singleton 1837 (m1837 H hv hs)) (range_singleton 1838 (m1838 H hv))) (range_join (range_singleton 1839 (m1839 H hv hs)) (range_singleton 1840 (m1840 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 1841 (m1841 H hv hs)) (range_singleton 1842 (m1842 H hv))) (range_join (range_singleton 1843 (m1843 H hv hs)) (range_singleton 1844 (m1844 H hv)))) (range_join (range_join (range_singleton 1845 (m1845 H hv hs)) (range_singleton 1846 (m1846 H hv hs))) (range_join (range_singleton 1847 (m1847 H hv)) (range_singleton 1848 (m1848 H hv hs))))) (range_join (range_join (range_join (range_singleton 1849 (m1849 H hv)) (range_singleton 1850 (m1850 H hv hs))) (range_join (range_singleton 1851 (m1851 H hv hs)) (range_singleton 1852 (m1852 H hv)))) (range_join (range_join (range_singleton 1853 (m1853 H hv hs)) (range_singleton 1854 (m1854 H hv hs))) (range_join (range_singleton 1855 (m1855 H hv hs)) (range_singleton 1856 (m1856 H hv)))))))

private theorem range1857 : ∀ n, 1857 ≤ n → n < 1889 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 1857 (m1857 H hv)) (range_singleton 1858 (m1858 H hv hs))) (range_join (range_singleton 1859 (m1859 H hv)) (range_singleton 1860 (m1860 H hv)))) (range_join (range_join (range_singleton 1861 (m1861 H hv hs)) (range_singleton 1862 (m1862 H hv))) (range_join (range_singleton 1863 (m1863 H hv hs)) (range_singleton 1864 (m1864 H hv hs))))) (range_join (range_join (range_join (range_singleton 1865 (m1865 H hv hs)) (range_singleton 1866 (m1866 H hv hs))) (range_join (range_singleton 1867 (m1867 H hv hs)) (range_singleton 1868 (m1868 H hv hs)))) (range_join (range_join (range_singleton 1869 (m1869 H hv hs)) (range_singleton 1870 (m1870 H hv hs))) (range_join (range_singleton 1871 (m1871 H hv hs)) (range_singleton 1872 (m1872 H hv)))))) (range_join (range_join (range_join (range_join (range_singleton 1873 (m1873 H hv hs)) (range_singleton 1874 (m1874 H hv hs))) (range_join (range_singleton 1875 (m1875 H hv hs)) (range_singleton 1876 (m1876 H hv hs)))) (range_join (range_join (range_singleton 1877 (m1877 H hv)) (range_singleton 1878 (m1878 H hv))) (range_join (range_singleton 1879 (m1879 H hv hs)) (range_singleton 1880 (m1880 H hv))))) (range_join (range_join (range_join (range_singleton 1881 (m1881 H hv hs)) (range_singleton 1882 (m1882 H hv))) (range_join (range_singleton 1883 (m1883 H hv)) (range_singleton 1884 (m1884 H hv hs)))) (range_join (range_join (range_singleton 1885 (m1885 H hv hs)) (range_singleton 1886 (m1886 H hv hs))) (range_join (range_singleton 1887 (m1887 H hv)) (range_singleton 1888 (m1888 H hv)))))))

private theorem range1889 : ∀ n, 1889 ≤ n → n < 1921 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 1889 (m1889 H hv)) (range_singleton 1890 (m1890 H hv))) (range_join (range_singleton 1891 (m1891 H hv hs)) (range_singleton 1892 (m1892 H hv)))) (range_join (range_join (range_singleton 1893 (m1893 H hv hs)) (range_singleton 1894 (m1894 H hv))) (range_join (range_singleton 1895 (m1895 H hv)) (range_singleton 1896 (m1896 H hv hs))))) (range_join (range_join (range_join (range_singleton 1897 (m1897 H hv)) (range_singleton 1898 (m1898 H hv hs))) (range_join (range_singleton 1899 (m1899 H hv hs)) (range_singleton 1900 (m1900 H hv)))) (range_join (range_join (range_singleton 1901 (m1901 H hv)) (range_singleton 1902 (m1902 H hv hs))) (range_join (range_singleton 1903 (m1903 H hv hs)) (range_singleton 1904 (m1904 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 1905 (m1905 H hv hs)) (range_singleton 1906 (m1906 H hv hs))) (range_join (range_singleton 1907 (m1907 H hv)) (range_singleton 1908 (m1908 H hv hs)))) (range_join (range_join (range_singleton 1909 (m1909 H hv hs)) (range_singleton 1910 (m1910 H hv hs))) (range_join (range_singleton 1911 (m1911 H hv hs)) (range_singleton 1912 (m1912 H hv))))) (range_join (range_join (range_join (range_singleton 1913 (m1913 H hv hs)) (range_singleton 1914 (m1914 H hv hs))) (range_join (range_singleton 1915 (m1915 H hv)) (range_singleton 1916 (m1916 H hv hs)))) (range_join (range_join (range_singleton 1917 (m1917 H hv hs)) (range_singleton 1918 (m1918 H hv hs))) (range_join (range_singleton 1919 (m1919 H hv)) (range_singleton 1920 (m1920 H hv hs)))))))

private theorem range1921 : ∀ n, 1921 ≤ n → n < 1953 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 1921 (m1921 H hv)) (range_singleton 1922 (m1922 H hv))) (range_join (range_singleton 1923 (m1923 H hv hs)) (range_singleton 1924 (m1924 H hv hs)))) (range_join (range_join (range_singleton 1925 (m1925 H hv hs)) (range_singleton 1926 (m1926 H hv hs))) (range_join (range_singleton 1927 (m1927 H hv hs)) (range_singleton 1928 (m1928 H hv))))) (range_join (range_join (range_join (range_singleton 1929 (m1929 H hv hs)) (range_singleton 1930 (m1930 H hv hs))) (range_join (range_singleton 1931 (m1931 H hv)) (range_singleton 1932 (m1932 H hv hs)))) (range_join (range_join (range_singleton 1933 (m1933 H hv hs)) (range_singleton 1934 (m1934 H hv))) (range_join (range_singleton 1935 (m1935 H hv hs)) (range_singleton 1936 (m1936 H hv)))))) (range_join (range_join (range_join (range_join (range_singleton 1937 (m1937 H hv hs)) (range_singleton 1938 (m1938 H hv))) (range_join (range_singleton 1939 (m1939 H hv)) (range_singleton 1940 (m1940 H hv)))) (range_join (range_join (range_singleton 1941 (m1941 H hv hs)) (range_singleton 1942 (m1942 H hv))) (range_join (range_singleton 1943 (m1943 H hv hs)) (range_singleton 1944 (m1944 H hv))))) (range_join (range_join (range_join (range_singleton 1945 (m1945 H hv hs)) (range_singleton 1946 (m1946 H hv hs))) (range_join (range_singleton 1947 (m1947 H hv hs)) (range_singleton 1948 (m1948 H hv hs)))) (range_join (range_join (range_singleton 1949 (m1949 H hv)) (range_singleton 1950 (m1950 H hv))) (range_join (range_singleton 1951 (m1951 H hv)) (range_singleton 1952 (m1952 H hv)))))))

private theorem range1953 : ∀ n, 1953 ≤ n → n < 1985 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 1953 (m1953 H hv hs)) (range_singleton 1954 (m1954 H hv hs))) (range_join (range_singleton 1955 (m1955 H hv)) (range_singleton 1956 (m1956 H hv)))) (range_join (range_join (range_singleton 1957 (m1957 H hv)) (range_singleton 1958 (m1958 H hs))) (range_join (range_singleton 1959 (m1959 H hv hs)) (range_singleton 1960 (m1960 H hv))))) (range_join (range_join (range_join (range_singleton 1961 (m1961 H hv hs)) (range_singleton 1962 (m1962 H hv))) (range_join (range_singleton 1963 (m1963 H hv)) (range_singleton 1964 (m1964 H hv hs)))) (range_join (range_join (range_singleton 1965 (m1965 H hv)) (range_singleton 1966 (m1966 H hv hs))) (range_join (range_singleton 1967 (m1967 H hv)) (range_singleton 1968 (m1968 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 1969 (m1969 H hv hs)) (range_singleton 1970 (m1970 H hv))) (range_join (range_singleton 1971 (m1971 H hv)) (range_singleton 1972 (m1972 H hs)))) (range_join (range_join (range_singleton 1973 (m1973 H hv hs)) (range_singleton 1974 (m1974 H hv hs))) (range_join (range_singleton 1975 (m1975 H hv)) (range_singleton 1976 (m1976 H hv hs))))) (range_join (range_join (range_join (range_singleton 1977 (m1977 H hv)) (range_singleton 1978 (m1978 H hv))) (range_join (range_singleton 1979 (m1979 H hv hs)) (range_singleton 1980 (m1980 H hv)))) (range_join (range_join (range_singleton 1981 (m1981 H hv hs)) (range_singleton 1982 (m1982 H hv hs))) (range_join (range_singleton 1983 (m1983 H hv)) (range_singleton 1984 (m1984 H hv)))))))

private theorem range1985 : ∀ n, 1985 ≤ n → n < 2017 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 1985 (m1985 H hv hs)) (range_singleton 1986 (m1986 H hv hs))) (range_join (range_singleton 1987 (m1987 H hv)) (range_singleton 1988 (m1988 H hv hs)))) (range_join (range_join (range_singleton 1989 (m1989 H hv)) (range_singleton 1990 (m1990 H hv))) (range_join (range_singleton 1991 (m1991 H hv hs)) (range_singleton 1992 (m1992 H hv hs))))) (range_join (range_join (range_join (range_singleton 1993 (m1993 H hv hs)) (range_singleton 1994 (m1994 H hv))) (range_join (range_singleton 1995 (m1995 H hv)) (range_singleton 1996 (m1996 H hv hs)))) (range_join (range_join (range_singleton 1997 (m1997 H hv)) (range_singleton 1998 (m1998 H hv))) (range_join (range_singleton 1999 (m1999 H hv hs)) (range_singleton 2000 (m2000 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 2001 (m2001 H hv hs)) (range_singleton 2002 (m2002 H hv hs))) (range_join (range_singleton 2003 (m2003 H hv)) (range_singleton 2004 (m2004 H hv)))) (range_join (range_join (range_singleton 2005 (m2005 H hv)) (range_singleton 2006 (m2006 H hv hs))) (range_join (range_singleton 2007 (m2007 H hv hs)) (range_singleton 2008 (m2008 H hv))))) (range_join (range_join (range_join (range_singleton 2009 (m2009 H hv hs)) (range_singleton 2010 (m2010 H hv))) (range_join (range_singleton 2011 (m2011 H hv hs)) (range_singleton 2012 (m2012 H hv)))) (range_join (range_join (range_singleton 2013 (m2013 H hv hs)) (range_singleton 2014 (m2014 H hv))) (range_join (range_singleton 2015 (m2015 H hv)) (range_singleton 2016 (m2016 H hv)))))))

private theorem range2017 : ∀ n, 2017 ≤ n → n < 2049 → g n ∈ H :=
  (range_join (range_join (range_join (range_join (range_join (range_singleton 2017 (m2017 H hv)) (range_singleton 2018 (m2018 H hv hs))) (range_join (range_singleton 2019 (m2019 H hv hs)) (range_singleton 2020 (m2020 H hv)))) (range_join (range_join (range_singleton 2021 (m2021 H hv hs)) (range_singleton 2022 (m2022 H hv hs))) (range_join (range_singleton 2023 (m2023 H hv)) (range_singleton 2024 (m2024 H hv))))) (range_join (range_join (range_join (range_singleton 2025 (m2025 H hv hs)) (range_singleton 2026 (m2026 H hv hs))) (range_join (range_singleton 2027 (m2027 H hv)) (range_singleton 2028 (m2028 H hv hs)))) (range_join (range_join (range_singleton 2029 (m2029 H hv hs)) (range_singleton 2030 (m2030 H hv))) (range_join (range_singleton 2031 (m2031 H hv)) (range_singleton 2032 (m2032 H hv hs)))))) (range_join (range_join (range_join (range_join (range_singleton 2033 (m2033 H hv hs)) (range_singleton 2034 (m2034 H hv hs))) (range_join (range_singleton 2035 (m2035 H hv)) (range_singleton 2036 (m2036 H hv)))) (range_join (range_join (range_singleton 2037 (m2037 H hv hs)) (range_singleton 2038 (m2038 H hv hs))) (range_join (range_singleton 2039 (m2039 H hv hs)) (range_singleton 2040 (m2040 H hv hs))))) (range_join (range_join (range_join (range_singleton 2041 (m2041 H hv hs)) (range_singleton 2042 (m2042 H hv))) (range_join (range_singleton 2043 (m2043 H hv hs)) (range_singleton 2044 (m2044 H hv)))) (range_join (range_join (range_singleton 2045 (m2045 H hv hs)) (range_singleton 2046 (m2046 H hv hs))) (range_join (range_singleton 2047 (m2047 H hv hs)) (range_singleton 2048 (m2048 H hv hs)))))))

private theorem range2049 : ∀ n, 2049 ≤ n → n < 2063 → g n ∈ H :=
  (range_join (range_join (range_join (range_singleton 2049 (m2049 H hv hs)) (range_join (range_singleton 2050 (m2050 H hv hs)) (range_singleton 2051 (m2051 H hv)))) (range_join (range_join (range_singleton 2052 (m2052 H hv hs)) (range_singleton 2053 (m2053 H hv hs))) (range_join (range_singleton 2054 (m2054 H hv hs)) (range_singleton 2055 (m2055 H hv hs))))) (range_join (range_join (range_singleton 2056 (m2056 H hv hs)) (range_join (range_singleton 2057 (m2057 H hv hs)) (range_singleton 2058 (m2058 H hv hs)))) (range_join (range_join (range_singleton 2059 (m2059 H hv)) (range_singleton 2060 (m2060 H hv))) (range_join (range_singleton 2061 (m2061 H hv)) (range_singleton 2062 (m2062 H hv hs))))))

theorem all_mem : ∀ n : Fin 2062, g (n.val + 1) ∈ H := by
  have hall : ∀ n, 1 ≤ n → n < 2063 → g n ∈ H := (range_join (range_join (range_join (range_join (range_join (range_join (range1 H hv hs) (range33 H hv hs)) (range_join (range65 H hv hs) (range97 H hv hs))) (range_join (range_join (range129 H hv hs) (range161 H hv hs)) (range_join (range193 H hv hs) (range225 H hv hs)))) (range_join (range_join (range_join (range257 H hv hs) (range289 H hv hs)) (range_join (range321 H hv hs) (range353 H hv hs))) (range_join (range_join (range385 H hv hs) (range417 H hv hs)) (range_join (range449 H hv hs) (range481 H hv hs))))) (range_join (range_join (range_join (range_join (range513 H hv hs) (range545 H hv hs)) (range_join (range577 H hv hs) (range609 H hv hs))) (range_join (range_join (range641 H hv hs) (range673 H hv hs)) (range_join (range705 H hv hs) (range737 H hv hs)))) (range_join (range_join (range_join (range769 H hv hs) (range801 H hv hs)) (range_join (range833 H hv hs) (range865 H hv hs))) (range_join (range_join (range897 H hv hs) (range929 H hv hs)) (range_join (range961 H hv hs) (range993 H hv hs)))))) (range_join (range_join (range_join (range_join (range_join (range1025 H hv hs) (range1057 H hv hs)) (range_join (range1089 H hv hs) (range1121 H hv hs))) (range_join (range_join (range1153 H hv hs) (range1185 H hv hs)) (range_join (range1217 H hv hs) (range1249 H hv hs)))) (range_join (range_join (range_join (range1281 H hv hs) (range1313 H hv hs)) (range_join (range1345 H hv hs) (range1377 H hv hs))) (range_join (range_join (range1409 H hv hs) (range1441 H hv hs)) (range_join (range1473 H hv hs) (range1505 H hv hs))))) (range_join (range_join (range_join (range_join (range1537 H hv hs) (range1569 H hv hs)) (range_join (range1601 H hv hs) (range1633 H hv hs))) (range_join (range_join (range1665 H hv hs) (range1697 H hv hs)) (range_join (range1729 H hv hs) (range1761 H hv hs)))) (range_join (range_join (range_join (range1793 H hv hs) (range1825 H hv hs)) (range_join (range1857 H hv hs) (range1889 H hv hs))) (range_join (range_join (range1921 H hv hs) (range1953 H hv hs)) (range_join (range1985 H hv hs) (range_join (range2017 H hv hs) (range2049 H hv hs))))))))
  intro n
  exact hall (n.val + 1) (Nat.succ_pos _) (by have := n.isLt; omega)

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Membership
