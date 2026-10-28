module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.Data
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.Check

/-!
# Short source-map relations for Fi23 Schreier edges

The two packed maps satisfy A² = B³ = 1 on every original coordinate.
Balanced kernel checks certify these statements in blocks of 1024 points.
`Tree` transfers them to the literal generators using the source-map agreements;
`Reduction` uses them to omit one edge from each nontrivial generator cycle.
No assertion about the witness group is made by these numerical relations.

Source: retained ATLAS F23G1-p31671B0 permutations; GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.Exhaustion.Edges
open Fi24Prime.Fi23Lift.Certificate

def relationCheck (n : Nat) : Bool :=
  let x := Fin.ofNat 31671 n
  decide (sourceA (sourceA x) = x ∧ sourceB (sourceB (sourceB x)) = x)

private theorem relationBlock0 : checkPow relationCheck 0 10 = true := by
  decide +kernel

private theorem relationBlock1 : checkPow relationCheck 1024 10 = true := by
  decide +kernel

private theorem relationBlock2 : checkPow relationCheck 2048 10 = true := by
  decide +kernel

private theorem relationBlock3 : checkPow relationCheck 3072 10 = true := by
  decide +kernel

private theorem relationBlock4 : checkPow relationCheck 4096 10 = true := by
  decide +kernel

private theorem relationBlock5 : checkPow relationCheck 5120 10 = true := by
  decide +kernel

private theorem relationBlock6 : checkPow relationCheck 6144 10 = true := by
  decide +kernel

private theorem relationBlock7 : checkPow relationCheck 7168 10 = true := by
  decide +kernel

private theorem relationBlock8 : checkPow relationCheck 8192 10 = true := by
  decide +kernel

private theorem relationBlock9 : checkPow relationCheck 9216 10 = true := by
  decide +kernel

private theorem relationBlock10 : checkPow relationCheck 10240 10 = true := by
  decide +kernel

private theorem relationBlock11 : checkPow relationCheck 11264 10 = true := by
  decide +kernel

private theorem relationBlock12 : checkPow relationCheck 12288 10 = true := by
  decide +kernel

private theorem relationBlock13 : checkPow relationCheck 13312 10 = true := by
  decide +kernel

private theorem relationBlock14 : checkPow relationCheck 14336 10 = true := by
  decide +kernel

private theorem relationBlock15 : checkPow relationCheck 15360 10 = true := by
  decide +kernel

private theorem relationBlock16 : checkPow relationCheck 16384 10 = true := by
  decide +kernel

private theorem relationBlock17 : checkPow relationCheck 17408 10 = true := by
  decide +kernel

private theorem relationBlock18 : checkPow relationCheck 18432 10 = true := by
  decide +kernel

private theorem relationBlock19 : checkPow relationCheck 19456 10 = true := by
  decide +kernel

private theorem relationBlock20 : checkPow relationCheck 20480 10 = true := by
  decide +kernel

private theorem relationBlock21 : checkPow relationCheck 21504 10 = true := by
  decide +kernel

private theorem relationBlock22 : checkPow relationCheck 22528 10 = true := by
  decide +kernel

private theorem relationBlock23 : checkPow relationCheck 23552 10 = true := by
  decide +kernel

private theorem relationBlock24 : checkPow relationCheck 24576 10 = true := by
  decide +kernel

private theorem relationBlock25 : checkPow relationCheck 25600 10 = true := by
  decide +kernel

private theorem relationBlock26 : checkPow relationCheck 26624 10 = true := by
  decide +kernel

private theorem relationBlock27 : checkPow relationCheck 27648 10 = true := by
  decide +kernel

private theorem relationBlock28 : checkPow relationCheck 28672 10 = true := by
  decide +kernel

private theorem relationBlock29 : checkPow relationCheck 29696 10 = true := by
  decide +kernel

private theorem relationBlock30 : checkPow relationCheck 30720 10 = true := by
  decide +kernel

private theorem relationBlock31 : checkPow relationCheck 31744 10 = true := by
  decide +kernel

private theorem relationCheck_all : checkPow relationCheck 0 15 = true :=
  (checkPow_join relationCheck 14 0
  (checkPow_join relationCheck 13 0
  (checkPow_join relationCheck 12 0
  (checkPow_join relationCheck 11 0
  (checkPow_join relationCheck 10 0
  relationBlock0
  relationBlock1)
  (checkPow_join relationCheck 10 2048
  relationBlock2
  relationBlock3))
  (checkPow_join relationCheck 11 4096
  (checkPow_join relationCheck 10 4096
  relationBlock4
  relationBlock5)
  (checkPow_join relationCheck 10 6144
  relationBlock6
  relationBlock7)))
  (checkPow_join relationCheck 12 8192
  (checkPow_join relationCheck 11 8192
  (checkPow_join relationCheck 10 8192
  relationBlock8
  relationBlock9)
  (checkPow_join relationCheck 10 10240
  relationBlock10
  relationBlock11))
  (checkPow_join relationCheck 11 12288
  (checkPow_join relationCheck 10 12288
  relationBlock12
  relationBlock13)
  (checkPow_join relationCheck 10 14336
  relationBlock14
  relationBlock15))))
  (checkPow_join relationCheck 13 16384
  (checkPow_join relationCheck 12 16384
  (checkPow_join relationCheck 11 16384
  (checkPow_join relationCheck 10 16384
  relationBlock16
  relationBlock17)
  (checkPow_join relationCheck 10 18432
  relationBlock18
  relationBlock19))
  (checkPow_join relationCheck 11 20480
  (checkPow_join relationCheck 10 20480
  relationBlock20
  relationBlock21)
  (checkPow_join relationCheck 10 22528
  relationBlock22
  relationBlock23)))
  (checkPow_join relationCheck 12 24576
  (checkPow_join relationCheck 11 24576
  (checkPow_join relationCheck 10 24576
  relationBlock24
  relationBlock25)
  (checkPow_join relationCheck 10 26624
  relationBlock26
  relationBlock27))
  (checkPow_join relationCheck 11 28672
  (checkPow_join relationCheck 10 28672
  relationBlock28
  relationBlock29)
  (checkPow_join relationCheck 10 30720
  relationBlock30
  relationBlock31)))))

private theorem source_relations (x : Fin 31671) :
    sourceA (sourceA x) = x ∧ sourceB (sourceB (sourceB x)) = x := by
  have h := checkPow_sound relationCheck 15 0 relationCheck_all x.val
    (Nat.zero_le _) (Nat.lt_trans x.isLt (by decide))
  simpa only [relationCheck, Fin.ofNat_eq_cast, Fin.cast_val_eq_self,
    decide_eq_true_eq] using h

theorem sourceA_square (x : Fin 31671) : sourceA (sourceA x) = x :=
  (source_relations x).1

theorem sourceB_cube (x : Fin 31671) : sourceB (sourceB (sourceB x)) = x :=
  (source_relations x).2

end Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.Exhaustion.Edges
