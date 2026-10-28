module

public import Theory.SpecificGroups.Rudvalis.Model.TwoRankSix.Data
public import Mathlib.Tactic.FinCases

/-!
# Four elementary sixty-four rows in the Rudvalis Sylow coordinates

The existing 64-label involution certificate forces label one to be 6144.
Label 36 has four possibilities. Commutation with these two elements forces
label four, and commutation with the resulting three seeds determines every
other label. These kernel checks use the original degree-4060 point maps.

Source: the even-index E64.G2(2) local in GLS3 Table 5.3r, printed p.279,
used in Aschbacher--Smith 4.4.3, printed pp.622--623. The checks establish only
this elementary-subgroup coverage, not a normalizer classification.
-/

namespace Rudvalis.BinaryThreeModules.ElementarySixtyFour

open Rudvalis.TwoRankSix
open Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate.LocalOrder

set_option Elab.async false
set_option maxRecDepth 30000

@[expose] public def pointCommute (m n : Fin 16384) : Prop :=
  normalMap m (normalMap n 0) = normalMap n (normalMap m 0) ∧
  normalMap m (normalMap n 1) = normalMap n (normalMap m 1)

public instance (m n : Fin 16384) : Decidable (pointCommute m n) :=
  inferInstanceAs (Decidable (_ ∧ _))


@[expose] public def rowIndex : Fin 4 → Fin 64 → Fin 16384 :=
  ![![0,6144,10240,12288,76,2380,4428,6220,8524,2304,4352,10316,8448,12364,14668,14592,64,12,2316,2368,4364,4416,6208,6156,8460,8512,10304,10252,12352,12300,14604,14656,4,8,68,72,2308,2312,2372,2376,4356,4360,4420,4424,6148,6152,6212,6216,8452,8456,8516,8520,10244,10248,10308,10312,12292,12296,12356,12360,14596,14600,14660,14664],
    ![0,6144,10240,12288,2696,3016,4744,5064,8840,2304,4352,1156,8448,3268,9160,14592,5316,320,2112,14984,4160,15304,7300,6464,8256,712,9412,10560,11396,12608,14400,904,13444,15556,1476,3460,5508,6856,7048,7620,9604,10952,11144,11716,13000,13192,13764,15748,1548,1868,3660,3852,5708,5900,7692,8012,9804,9996,11788,12108,13836,14156,15948,16140],
    ![0,6144,10240,12288,48,304,6192,6448,256,10288,10544,6400,12336,10496,12544,12592,64,320,32,96,288,352,6208,6464,6176,6240,10304,10560,12352,12608,6432,6496,10528,10272,10592,10336,12320,12576,12384,12640,112,368,6256,6512,10352,10608,12400,12656,16,80,272,336,6160,6224,6416,6480,10256,10320,10512,10576,12304,12368,12560,12624],
    ![0,6144,10240,12288,1648,1904,7792,8048,256,11888,12144,6400,13936,10496,12544,14192,720,976,2112,2368,4160,4416,2704,2960,8256,8512,4752,5008,6864,7120,14400,14656,8848,11216,9104,10960,13008,15248,13264,14992,3632,3888,5680,5936,9776,10032,15920,16176,1248,1504,3232,3488,5280,5536,7392,7648,9376,9632,11488,11744,13536,13792,15520,15776]]

@[expose] public def branchSeed : Fin 4 → Fin 16384 := ![2308,5508,12320,13008]

@[expose] public def supportSeed : Fin 4 → Fin 16384 := ![76,2696,48,1648]

public theorem forced_first (s : Fin 21) : entry 1 s = 6144 := by
  revert s
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

public theorem branch_entry (s : Fin 21) : ∃ j : Fin 4, entry 36 s = branchSeed j := by
  revert s
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

public theorem forced_fourth (j : Fin 4) (s : Fin 21) :
    entry 4 s = supportSeed j ∨
      ¬ pointCommute (entry 4 s) 6144 ∨ ¬ pointCommute (entry 4 s) (branchSeed j) := by
  revert j s
  apply Rudvalis.OrderCertificate.allFin₂
  decide +kernel

private theorem row_restriction_0 (c : Fin 64) (s : Fin 21) :
    entry c s = rowIndex 0 c ∨ ¬ pointCommute (entry c s) 6144 ∨
      ¬ pointCommute (entry c s) (branchSeed 0) ∨
      ¬ pointCommute (entry c s) (supportSeed 0) := by
  revert c s
  apply Rudvalis.OrderCertificate.allFin₂
  decide +kernel

private theorem row_restriction_1 (c : Fin 64) (s : Fin 21) :
    entry c s = rowIndex 1 c ∨ ¬ pointCommute (entry c s) 6144 ∨
      ¬ pointCommute (entry c s) (branchSeed 1) ∨
      ¬ pointCommute (entry c s) (supportSeed 1) := by
  revert c s
  apply Rudvalis.OrderCertificate.allFin₂
  decide +kernel

private theorem row_restriction_2 (c : Fin 64) (s : Fin 21) :
    entry c s = rowIndex 2 c ∨ ¬ pointCommute (entry c s) 6144 ∨
      ¬ pointCommute (entry c s) (branchSeed 2) ∨
      ¬ pointCommute (entry c s) (supportSeed 2) := by
  revert c s
  apply Rudvalis.OrderCertificate.allFin₂
  decide +kernel

private theorem row_restriction_3 (c : Fin 64) (s : Fin 21) :
    entry c s = rowIndex 3 c ∨ ¬ pointCommute (entry c s) 6144 ∨
      ¬ pointCommute (entry c s) (branchSeed 3) ∨
      ¬ pointCommute (entry c s) (supportSeed 3) := by
  revert c s
  apply Rudvalis.OrderCertificate.allFin₂
  decide +kernel

public theorem row_restriction (j : Fin 4) (c : Fin 64) (s : Fin 21) :
    entry c s = rowIndex j c ∨ ¬ pointCommute (entry c s) 6144 ∨
      ¬ pointCommute (entry c s) (branchSeed j) ∨
      ¬ pointCommute (entry c s) (supportSeed j) := by
  fin_cases j
  · exact row_restriction_0 c s
  · exact row_restriction_1 c s
  · exact row_restriction_2 c s
  · exact row_restriction_3 c s

end Rudvalis.BinaryThreeModules.ElementarySixtyFour
