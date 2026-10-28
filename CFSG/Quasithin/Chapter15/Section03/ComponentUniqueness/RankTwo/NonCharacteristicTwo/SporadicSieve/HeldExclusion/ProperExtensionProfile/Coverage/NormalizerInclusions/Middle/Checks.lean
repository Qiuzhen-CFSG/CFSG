module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Coverage.NormalizerInclusions.Middle.Data

/-!
# Checked signatures of the two middle outer Held rows

Common fixed-point counts distinguish the row-zero involution in both literal
rows: it fixes 42 points and has no common fixed-point count 10 with a row
element. Every other element either has a different fixed-point count or has
a displayed partner with common count 10. Only these entries of the count
tables are checked; the calculations use existing certified permutation tables.

Source: ATLAS HeG1-p2058B0, GLS3 Table 5.3p, and Aschbacher--Smith 15.3.41--42,
printed p.1138. The diagnostic GAP output is not a premise.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.NormalizerInclusions.Middle

def badIndex (k : Fin 2) (n : Fin (2 ^ dim k)) : Fin (2 ^ dim k) :=
  ⟨if n.val % 2 = 1 then 2 else 1, by fin_cases k <;> split_ifs <;> decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem central_count_check : ∀ k : Fin 2,
    tableCount (permForm k (centralIndex k)) (permForm k (centralIndex k)) = 42 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem central_avoid_check : ∀ k : Fin 2, ∀ n : Fin (2 ^ dim k),
    tableCount (permForm k (centralIndex k)) (permForm k n) ≠ 10 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem eliminate_check : ∀ k : Fin 2, ∀ n : Fin (2 ^ dim k),
    n = centralIndex k ∨ tableCount (permForm k n) (permForm k n) ≠ 42 ∨
      tableCount (permForm k n) (permForm k (badIndex k n)) = 10 := by
  decide +kernel

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.NormalizerInclusions.Middle
