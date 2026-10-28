module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.CertificateData
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.Check

/-!
# Checked injectivity and spanning tree for the Fi₂₃ relabeling

For each source label, the kernel verifies a left-inverse identity and a tree
edge to a label of strictly smaller depth (apart from root 27192). The 32
blocks have 1024 points each; padding above 31670 wraps harmlessly modulo
31671. Balanced checking and packed lookup keep individual reductions bounded.

The edge checks concern the numerical `sourceA` and `sourceB` maps only.
They assert no equality with the ATLAS carrier generators. `Comparison`
uses their actual comparisons to prove membership in the orbit of 508.
Source: the retained F23G1-p31671B0 and F24G1-p306936B0 witnesses; GLS3 Table 5.3v.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate

private def pointTest (n : Nat) : Bool :=
  let i := Fin.ofNat 31671 n
  decide (labelInverse (labelMap i) = i.val ∧
    (i = 27192 ∨ (depth (parent i) < depth i ∧
      (sourceA (parent i) = i ∨ sourceA i = parent i ∨
        sourceB (parent i) = i ∨ sourceB i = parent i))))

private theorem block0 : checkPow pointTest 0 10 = true := by decide +kernel

private theorem block1 : checkPow pointTest 1024 10 = true := by decide +kernel

private theorem block2 : checkPow pointTest 2048 10 = true := by decide +kernel

private theorem block3 : checkPow pointTest 3072 10 = true := by decide +kernel

private theorem block4 : checkPow pointTest 4096 10 = true := by decide +kernel

private theorem block5 : checkPow pointTest 5120 10 = true := by decide +kernel

private theorem block6 : checkPow pointTest 6144 10 = true := by decide +kernel

private theorem block7 : checkPow pointTest 7168 10 = true := by decide +kernel

private theorem block8 : checkPow pointTest 8192 10 = true := by decide +kernel

private theorem block9 : checkPow pointTest 9216 10 = true := by decide +kernel

private theorem block10 : checkPow pointTest 10240 10 = true := by decide +kernel

private theorem block11 : checkPow pointTest 11264 10 = true := by decide +kernel

private theorem block12 : checkPow pointTest 12288 10 = true := by decide +kernel

private theorem block13 : checkPow pointTest 13312 10 = true := by decide +kernel

private theorem block14 : checkPow pointTest 14336 10 = true := by decide +kernel

private theorem block15 : checkPow pointTest 15360 10 = true := by decide +kernel

private theorem block16 : checkPow pointTest 16384 10 = true := by decide +kernel

private theorem block17 : checkPow pointTest 17408 10 = true := by decide +kernel

private theorem block18 : checkPow pointTest 18432 10 = true := by decide +kernel

private theorem block19 : checkPow pointTest 19456 10 = true := by decide +kernel

private theorem block20 : checkPow pointTest 20480 10 = true := by decide +kernel

private theorem block21 : checkPow pointTest 21504 10 = true := by decide +kernel

private theorem block22 : checkPow pointTest 22528 10 = true := by decide +kernel

private theorem block23 : checkPow pointTest 23552 10 = true := by decide +kernel

private theorem block24 : checkPow pointTest 24576 10 = true := by decide +kernel

private theorem block25 : checkPow pointTest 25600 10 = true := by decide +kernel

private theorem block26 : checkPow pointTest 26624 10 = true := by decide +kernel

private theorem block27 : checkPow pointTest 27648 10 = true := by decide +kernel

private theorem block28 : checkPow pointTest 28672 10 = true := by decide +kernel

private theorem block29 : checkPow pointTest 29696 10 = true := by decide +kernel

private theorem block30 : checkPow pointTest 30720 10 = true := by decide +kernel

private theorem block31 : checkPow pointTest 31744 10 = true := by decide +kernel

private theorem all_checked : checkPow pointTest 0 15 = true :=
  (checkPow_join pointTest 14 0 (checkPow_join pointTest 13 0 (checkPow_join pointTest 12 0 (checkPow_join pointTest 11 0 (checkPow_join pointTest 10 0 block0 block1) (checkPow_join pointTest 10 2048 block2 block3)) (checkPow_join pointTest 11 4096 (checkPow_join pointTest 10 4096 block4 block5) (checkPow_join pointTest 10 6144 block6 block7))) (checkPow_join pointTest 12 8192 (checkPow_join pointTest 11 8192 (checkPow_join pointTest 10 8192 block8 block9) (checkPow_join pointTest 10 10240 block10 block11)) (checkPow_join pointTest 11 12288 (checkPow_join pointTest 10 12288 block12 block13) (checkPow_join pointTest 10 14336 block14 block15)))) (checkPow_join pointTest 13 16384 (checkPow_join pointTest 12 16384 (checkPow_join pointTest 11 16384 (checkPow_join pointTest 10 16384 block16 block17) (checkPow_join pointTest 10 18432 block18 block19)) (checkPow_join pointTest 11 20480 (checkPow_join pointTest 10 20480 block20 block21) (checkPow_join pointTest 10 22528 block22 block23))) (checkPow_join pointTest 12 24576 (checkPow_join pointTest 11 24576 (checkPow_join pointTest 10 24576 block24 block25) (checkPow_join pointTest 10 26624 block26 block27)) (checkPow_join pointTest 11 28672 (checkPow_join pointTest 10 28672 block28 block29) (checkPow_join pointTest 10 30720 block30 block31)))))

private theorem point_properties (i : Fin 31671) :
    labelInverse (labelMap i) = i.val ∧
    (i = 27192 ∨ (depth (parent i) < depth i ∧
      (sourceA (parent i) = i ∨ sourceA i = parent i ∨
        sourceB (parent i) = i ∨ sourceB i = parent i))) := by
  have h := checkPow_sound pointTest 15 0 all_checked i.val
    (Nat.zero_le _) (Nat.lt_trans i.isLt (by decide))
  have hi : Fin.ofNat 31671 i.val = i := by simp
  simpa only [pointTest, hi, decide_eq_true_eq] using h

/-- The saved relabeling has no collisions. -/
theorem labelMap_injective : Function.Injective labelMap := by
  intro i j h
  apply Fin.ext
  calc
    i.val = labelInverse (labelMap i) := (point_properties i).1.symm
    _ = labelInverse (labelMap j) := congrArg labelInverse h
    _ = j.val := (point_properties j).1

/-- The source label of the selected ambient root. -/
theorem labelMap_root : labelMap 27192 = 508 := by decide +kernel

/-- The first source label, recording the labeling convention. -/
theorem labelMap_zero : labelMap 0 = 117971 := by decide +kernel

/-- Every non-root label has a generator edge to a smaller-depth label. -/
theorem tree_step (i : Fin 31671) :
    i = 27192 ∨ (depth (parent i) < depth i ∧
      (sourceA (parent i) = i ∨ sourceA i = parent i ∨
        sourceB (parent i) = i ∨ sourceB i = parent i)) :=
  (point_properties i).2

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate
