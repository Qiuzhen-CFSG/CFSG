module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Suz.CentralizerSection.TwoKernel.ThreeTables

/-!
# Kernel-checked cubic and commutation certificates

Each block verifies 64 letters of the fixed degree-1782 action. The balanced
checker combines those blocks without expanding the original cycle expressions.
These certificates establish concrete word identities, not a group-order claim.
-/

public section
namespace Sporadic.LeechRelated.Suz.CentralizerSection.ThreeWitness
open Tables Checks
set_option Elab.async false

private theorem range6_0 : checkRange ThreeWitness.pointCheck 6 0 = true := by decide +kernel
private theorem range6_1 : checkRange ThreeWitness.pointCheck 6 64 = true := by decide +kernel
private theorem range6_2 : checkRange ThreeWitness.pointCheck 6 128 = true := by decide +kernel
private theorem range6_3 : checkRange ThreeWitness.pointCheck 6 192 = true := by decide +kernel
private theorem range6_4 : checkRange ThreeWitness.pointCheck 6 256 = true := by decide +kernel
private theorem range6_5 : checkRange ThreeWitness.pointCheck 6 320 = true := by decide +kernel
private theorem range6_6 : checkRange ThreeWitness.pointCheck 6 384 = true := by decide +kernel
private theorem range6_7 : checkRange ThreeWitness.pointCheck 6 448 = true := by decide +kernel
private theorem range6_8 : checkRange ThreeWitness.pointCheck 6 512 = true := by decide +kernel
private theorem range6_9 : checkRange ThreeWitness.pointCheck 6 576 = true := by decide +kernel
private theorem range6_10 : checkRange ThreeWitness.pointCheck 6 640 = true := by decide +kernel
private theorem range6_11 : checkRange ThreeWitness.pointCheck 6 704 = true := by decide +kernel
private theorem range6_12 : checkRange ThreeWitness.pointCheck 6 768 = true := by decide +kernel
private theorem range6_13 : checkRange ThreeWitness.pointCheck 6 832 = true := by decide +kernel
private theorem range6_14 : checkRange ThreeWitness.pointCheck 6 896 = true := by decide +kernel
private theorem range6_15 : checkRange ThreeWitness.pointCheck 6 960 = true := by decide +kernel
private theorem range6_16 : checkRange ThreeWitness.pointCheck 6 1024 = true := by decide +kernel
private theorem range6_17 : checkRange ThreeWitness.pointCheck 6 1088 = true := by decide +kernel
private theorem range6_18 : checkRange ThreeWitness.pointCheck 6 1152 = true := by decide +kernel
private theorem range6_19 : checkRange ThreeWitness.pointCheck 6 1216 = true := by decide +kernel
private theorem range6_20 : checkRange ThreeWitness.pointCheck 6 1280 = true := by decide +kernel
private theorem range6_21 : checkRange ThreeWitness.pointCheck 6 1344 = true := by decide +kernel
private theorem range6_22 : checkRange ThreeWitness.pointCheck 6 1408 = true := by decide +kernel
private theorem range6_23 : checkRange ThreeWitness.pointCheck 6 1472 = true := by decide +kernel
private theorem range6_24 : checkRange ThreeWitness.pointCheck 6 1536 = true := by decide +kernel
private theorem range6_25 : checkRange ThreeWitness.pointCheck 6 1600 = true := by decide +kernel
private theorem range6_26 : checkRange ThreeWitness.pointCheck 6 1664 = true := by decide +kernel
private theorem range6_27 : checkRange ThreeWitness.pointCheck 6 1728 = true := by decide +kernel
private theorem range6_28 : checkRange ThreeWitness.pointCheck 6 1792 = true := by decide +kernel
private theorem range6_29 : checkRange ThreeWitness.pointCheck 6 1856 = true := by decide +kernel
private theorem range6_30 : checkRange ThreeWitness.pointCheck 6 1920 = true := by decide +kernel
private theorem range6_31 : checkRange ThreeWitness.pointCheck 6 1984 = true := by decide +kernel
private theorem range7_0 : checkRange ThreeWitness.pointCheck 7 0 = true := by
  change (checkRange ThreeWitness.pointCheck 6 0 &&
    checkRange ThreeWitness.pointCheck 6 64) = true
  rw [range6_0, range6_1]
  rfl
private theorem range7_1 : checkRange ThreeWitness.pointCheck 7 128 = true := by
  change (checkRange ThreeWitness.pointCheck 6 128 &&
    checkRange ThreeWitness.pointCheck 6 192) = true
  rw [range6_2, range6_3]
  rfl
private theorem range7_2 : checkRange ThreeWitness.pointCheck 7 256 = true := by
  change (checkRange ThreeWitness.pointCheck 6 256 &&
    checkRange ThreeWitness.pointCheck 6 320) = true
  rw [range6_4, range6_5]
  rfl
private theorem range7_3 : checkRange ThreeWitness.pointCheck 7 384 = true := by
  change (checkRange ThreeWitness.pointCheck 6 384 &&
    checkRange ThreeWitness.pointCheck 6 448) = true
  rw [range6_6, range6_7]
  rfl
private theorem range7_4 : checkRange ThreeWitness.pointCheck 7 512 = true := by
  change (checkRange ThreeWitness.pointCheck 6 512 &&
    checkRange ThreeWitness.pointCheck 6 576) = true
  rw [range6_8, range6_9]
  rfl
private theorem range7_5 : checkRange ThreeWitness.pointCheck 7 640 = true := by
  change (checkRange ThreeWitness.pointCheck 6 640 &&
    checkRange ThreeWitness.pointCheck 6 704) = true
  rw [range6_10, range6_11]
  rfl
private theorem range7_6 : checkRange ThreeWitness.pointCheck 7 768 = true := by
  change (checkRange ThreeWitness.pointCheck 6 768 &&
    checkRange ThreeWitness.pointCheck 6 832) = true
  rw [range6_12, range6_13]
  rfl
private theorem range7_7 : checkRange ThreeWitness.pointCheck 7 896 = true := by
  change (checkRange ThreeWitness.pointCheck 6 896 &&
    checkRange ThreeWitness.pointCheck 6 960) = true
  rw [range6_14, range6_15]
  rfl
private theorem range7_8 : checkRange ThreeWitness.pointCheck 7 1024 = true := by
  change (checkRange ThreeWitness.pointCheck 6 1024 &&
    checkRange ThreeWitness.pointCheck 6 1088) = true
  rw [range6_16, range6_17]
  rfl
private theorem range7_9 : checkRange ThreeWitness.pointCheck 7 1152 = true := by
  change (checkRange ThreeWitness.pointCheck 6 1152 &&
    checkRange ThreeWitness.pointCheck 6 1216) = true
  rw [range6_18, range6_19]
  rfl
private theorem range7_10 : checkRange ThreeWitness.pointCheck 7 1280 = true := by
  change (checkRange ThreeWitness.pointCheck 6 1280 &&
    checkRange ThreeWitness.pointCheck 6 1344) = true
  rw [range6_20, range6_21]
  rfl
private theorem range7_11 : checkRange ThreeWitness.pointCheck 7 1408 = true := by
  change (checkRange ThreeWitness.pointCheck 6 1408 &&
    checkRange ThreeWitness.pointCheck 6 1472) = true
  rw [range6_22, range6_23]
  rfl
private theorem range7_12 : checkRange ThreeWitness.pointCheck 7 1536 = true := by
  change (checkRange ThreeWitness.pointCheck 6 1536 &&
    checkRange ThreeWitness.pointCheck 6 1600) = true
  rw [range6_24, range6_25]
  rfl
private theorem range7_13 : checkRange ThreeWitness.pointCheck 7 1664 = true := by
  change (checkRange ThreeWitness.pointCheck 6 1664 &&
    checkRange ThreeWitness.pointCheck 6 1728) = true
  rw [range6_26, range6_27]
  rfl
private theorem range7_14 : checkRange ThreeWitness.pointCheck 7 1792 = true := by
  change (checkRange ThreeWitness.pointCheck 6 1792 &&
    checkRange ThreeWitness.pointCheck 6 1856) = true
  rw [range6_28, range6_29]
  rfl
private theorem range7_15 : checkRange ThreeWitness.pointCheck 7 1920 = true := by
  change (checkRange ThreeWitness.pointCheck 6 1920 &&
    checkRange ThreeWitness.pointCheck 6 1984) = true
  rw [range6_30, range6_31]
  rfl
private theorem range8_0 : checkRange ThreeWitness.pointCheck 8 0 = true := by
  change (checkRange ThreeWitness.pointCheck 7 0 &&
    checkRange ThreeWitness.pointCheck 7 128) = true
  rw [range7_0, range7_1]
  rfl
private theorem range8_1 : checkRange ThreeWitness.pointCheck 8 256 = true := by
  change (checkRange ThreeWitness.pointCheck 7 256 &&
    checkRange ThreeWitness.pointCheck 7 384) = true
  rw [range7_2, range7_3]
  rfl
private theorem range8_2 : checkRange ThreeWitness.pointCheck 8 512 = true := by
  change (checkRange ThreeWitness.pointCheck 7 512 &&
    checkRange ThreeWitness.pointCheck 7 640) = true
  rw [range7_4, range7_5]
  rfl
private theorem range8_3 : checkRange ThreeWitness.pointCheck 8 768 = true := by
  change (checkRange ThreeWitness.pointCheck 7 768 &&
    checkRange ThreeWitness.pointCheck 7 896) = true
  rw [range7_6, range7_7]
  rfl
private theorem range8_4 : checkRange ThreeWitness.pointCheck 8 1024 = true := by
  change (checkRange ThreeWitness.pointCheck 7 1024 &&
    checkRange ThreeWitness.pointCheck 7 1152) = true
  rw [range7_8, range7_9]
  rfl
private theorem range8_5 : checkRange ThreeWitness.pointCheck 8 1280 = true := by
  change (checkRange ThreeWitness.pointCheck 7 1280 &&
    checkRange ThreeWitness.pointCheck 7 1408) = true
  rw [range7_10, range7_11]
  rfl
private theorem range8_6 : checkRange ThreeWitness.pointCheck 8 1536 = true := by
  change (checkRange ThreeWitness.pointCheck 7 1536 &&
    checkRange ThreeWitness.pointCheck 7 1664) = true
  rw [range7_12, range7_13]
  rfl
private theorem range8_7 : checkRange ThreeWitness.pointCheck 8 1792 = true := by
  change (checkRange ThreeWitness.pointCheck 7 1792 &&
    checkRange ThreeWitness.pointCheck 7 1920) = true
  rw [range7_14, range7_15]
  rfl
private theorem range9_0 : checkRange ThreeWitness.pointCheck 9 0 = true := by
  change (checkRange ThreeWitness.pointCheck 8 0 &&
    checkRange ThreeWitness.pointCheck 8 256) = true
  rw [range8_0, range8_1]
  rfl
private theorem range9_1 : checkRange ThreeWitness.pointCheck 9 512 = true := by
  change (checkRange ThreeWitness.pointCheck 8 512 &&
    checkRange ThreeWitness.pointCheck 8 768) = true
  rw [range8_2, range8_3]
  rfl
private theorem range9_2 : checkRange ThreeWitness.pointCheck 9 1024 = true := by
  change (checkRange ThreeWitness.pointCheck 8 1024 &&
    checkRange ThreeWitness.pointCheck 8 1280) = true
  rw [range8_4, range8_5]
  rfl
private theorem range9_3 : checkRange ThreeWitness.pointCheck 9 1536 = true := by
  change (checkRange ThreeWitness.pointCheck 8 1536 &&
    checkRange ThreeWitness.pointCheck 8 1792) = true
  rw [range8_6, range8_7]
  rfl
private theorem range10_0 : checkRange ThreeWitness.pointCheck 10 0 = true := by
  change (checkRange ThreeWitness.pointCheck 9 0 &&
    checkRange ThreeWitness.pointCheck 9 512) = true
  rw [range9_0, range9_1]
  rfl
private theorem range10_1 : checkRange ThreeWitness.pointCheck 10 1024 = true := by
  change (checkRange ThreeWitness.pointCheck 9 1024 &&
    checkRange ThreeWitness.pointCheck 9 1536) = true
  rw [range9_2, range9_3]
  rfl
private theorem range11_0 : checkRange ThreeWitness.pointCheck 11 0 = true := by
  change (checkRange ThreeWitness.pointCheck 10 0 &&
    checkRange ThreeWitness.pointCheck 10 1024) = true
  rw [range10_0, range10_1]
  rfl

private theorem all_points (a : Fin 1782) : ThreeWitness.pointCheck a.val = true :=
  checkRange_sound ThreeWitness.pointCheck 11 0 range11_0 a.val (Nat.zero_le _) (by omega)

/-- All checked word, inverse, cube and commutation identities, pointwise. -/
theorem pointFacts (a : Fin 1782) :
    cMap (ciMap a) = a ∧
    hMap a = ciMap (dMap (cMap (dMap (cMap (cMap a))))) ∧
    kMap a = cMap (dMap (dMap (dMap (ciMap a)))) ∧
    hMap (hiMap a) = a ∧ kMap (kiMap a) = a ∧
    xMap a = dMap (dMap (dMap (dMap a))) ∧
    yMap a = hMap (xMap (hiMap a)) ∧
    tMap a = kMap (xMap (kiMap a)) ∧
    xMap (xMap (xMap a)) = a ∧
    yMap (yMap (yMap a)) = a ∧
    tMap (tMap (tMap a)) = a ∧
    xMap (yMap a) = yMap (xMap a) ∧
    xMap (tMap a) = tMap (xMap a) ∧
    yMap (tMap a) = tMap (yMap a) := by
  have h := all_points a
  have ha : Fin.ofNat 1782 a.val = a := by simp
  simpa only [ThreeWitness.pointCheck, if_pos a.isLt, ha,
    Bool.and_eq_true, beq_iff_eq, and_assoc] using h

end Sporadic.LeechRelated.Suz.CentralizerSection.ThreeWitness
