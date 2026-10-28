module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Rows
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.FixedCoordinates

/-!
# Fixed kernel coordinates of the four literal quotient rows

The tables are the action of the printed generators on the eleven certified
kernel coordinates, computed from the native pair labels. Kernel checking
certifies the tables and their common fixed sets. These are coordinates of
the original Mathieu kernel, not a separately chosen representation.
Source: Kleidman--Wilson (1988), Figures 1/2 and Propositions 2.3.4--2.3.5.
-/

set_option Elab.async false
@[expose] public section
namespace Janko4.LocalStructure.ElementaryEightGeometry
open Cardinality.QuotientCount.Image SylowCore

def actionRows : Fin 4 → Fin 3 → Fin 11 → ℕ :=
  ![![![1, 2, 4, 1125, 1151, 1099, 64, 946, 1385, 1645, 1030], ![1, 2, 822, 1248, 1994, 1099, 1064, 128, 1625, 1768, 235], ![1, 2, 1133, 1838, 863, 787, 883, 131, 1385, 1557, 806]], ![![1, 2, 4, 1125, 1151, 1099, 64, 946, 1385, 1645, 1030], ![1, 816, 4, 831, 1478, 1732, 1064, 946, 261, 517, 1467], ![1, 1131, 4, 1874, 1615, 534, 883, 2015, 256, 512, 607]], ![![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024], ![1, 2, 822, 1248, 1994, 1099, 1064, 128, 1625, 1768, 235], ![1, 2, 1133, 1838, 863, 787, 883, 131, 1385, 1557, 806]], ![![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024], ![1, 816, 4, 831, 1478, 1732, 1064, 946, 261, 517, 1467], ![1, 1131, 4, 1874, 1615, 534, 883, 2015, 256, 512, 607]]]

private theorem actionRows_eq : ∀ r j i,
    actionRows r j i = pairLabel
      ((rowGenerator r j).val (basisPair i).1)
      ((rowGenerator r j).val (basisPair i).2) := by decide +kernel

theorem rowGenerator_mask (r : Fin 4) (j : Fin 3) (m : ℕ) :
    starMask (rowGenerator r j) m = maskImage (actionRows r j) m := by
  unfold starMask
  congr 1
  exact (funext (actionRows_eq r j)).symm

/-- Bounded masks fixed by all the selected image generators. -/
def fixedTest (r : Fin 4) (m : Fin 2048) : Prop :=
  ∀ j : Fin 3, maskImage (actionRows r j) m.val = m.val

instance (r : Fin 4) (m : Fin 2048) : Decidable (fixedTest r m) :=
  inferInstanceAs (Decidable (∀ _j : Fin 3, _))

/-- The common fixed space, in the literal eleven-bit kernel coordinates. -/
def fixedMasks (r : Fin 4) : Type := {m : Fin 2048 // fixedTest r m}

instance (r : Fin 4) : Fintype (fixedMasks r) :=
  inferInstanceAs (Fintype {m : Fin 2048 // fixedTest r m})

def fixedList0 : Finset (Fin 2048) := {0, 1, 2, 3, 816, 817, 818, 819, 1128, 1129, 1130, 1131, 1880, 1881, 1882, 1883}

theorem fixedTest0 : ∀ m, fixedTest 0 m ↔ m ∈ fixedList0 := by decide +kernel

theorem fixedMasks0_card : Nat.card (fixedMasks 0) = 16 := by
  rw [Nat.card_eq_fintype_card]
  change Fintype.card {m : Fin 2048 // fixedTest 0 m} = _
  simp_rw [fixedTest0]
  rw [Fintype.card_coe]
  decide +kernel

def fixedList1 : Finset (Fin 2048) := {0, 1, 4, 5, 818, 819, 822, 823, 1128, 1129, 1132, 1133, 1882, 1883, 1886, 1887}

theorem fixedTest1 : ∀ m, fixedTest 1 m ↔ m ∈ fixedList1 := by decide +kernel

theorem fixedMasks1_card : Nat.card (fixedMasks 1) = 16 := by
  rw [Nat.card_eq_fintype_card]
  change Fintype.card {m : Fin 2048 // fixedTest 1 m} = _
  simp_rw [fixedTest1]
  rw [Fintype.card_coe]
  decide +kernel

def fixedList2 : Finset (Fin 2048) := {0, 1, 2, 3, 28, 29, 30, 31, 812, 813, 814, 815, 816, 817, 818, 819, 1128, 1129, 1130, 1131, 1140, 1141, 1142, 1143, 1860, 1861, 1862, 1863, 1880, 1881, 1882, 1883}

theorem fixedTest2 : ∀ m, fixedTest 2 m ↔ m ∈ fixedList2 := by decide +kernel

theorem fixedMasks2_card : Nat.card (fixedMasks 2) = 32 := by
  rw [Nat.card_eq_fintype_card]
  change Fintype.card {m : Fin 2048 // fixedTest 2 m} = _
  simp_rw [fixedTest2]
  rw [Fintype.card_coe]
  decide +kernel

def fixedList3 : Finset (Fin 2048) := {0, 1, 4, 5, 50, 51, 54, 55, 768, 769, 772, 773, 818, 819, 822, 823, 1114, 1115, 1118, 1119, 1128, 1129, 1132, 1133, 1882, 1883, 1886, 1887, 1896, 1897, 1900, 1901}

theorem fixedTest3 : ∀ m, fixedTest 3 m ↔ m ∈ fixedList3 := by decide +kernel

theorem fixedMasks3_card : Nat.card (fixedMasks 3) = 32 := by
  rw [Nat.card_eq_fintype_card]
  change Fintype.card {m : Fin 2048 // fixedTest 3 m} = _
  simp_rw [fixedTest3]
  rw [Fintype.card_coe]
  decide +kernel

end Janko4.LocalStructure.ElementaryEightGeometry
