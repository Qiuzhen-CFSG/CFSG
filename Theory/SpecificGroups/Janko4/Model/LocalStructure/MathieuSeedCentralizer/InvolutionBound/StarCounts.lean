module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.InvolutionBound.StarDefs
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.InvolutionBound.StarCounts.Incidence
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.InvolutionBound.StarCounts.CentralizerFalse
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.InvolutionBound.StarCounts.CentralizerTrue
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarOrder

/-!
# Bounds for the two star classes stabilizing the marked pair

Explicit centralizer subgroups of orders at least 7680 and 21504 bound the
full conjugacy classes by 31878 and 11385. Transitivity on ordered distinct
pairs and double counting give marked-pair bounds of 1386 and 1485. Thus
each actual star class has at most 1600 elements stabilizing {0,1}.

All permutation witnesses are checked by the kernel, with the carriers and
left-conjugation convention from `StarDefs`. See `StarCounts/source/` for
the centralizer witnesses and their provenance in the ATLAS J4 max1 action.
No assertion about the full ambient J4 centralizer is needed here.
-/

set_option maxRecDepth 10000

public section
namespace Janko4.LocalStructure.MathieuSeedCentralizer.InvolutionBound
open Cardinality.QuotientCount.Image StarCountsCertificate
attribute [local irreducible] StarGroup starBase

private theorem class_mul_centralizer (b : Bool) :
    Nat.card {g : StarGroup // IsConj (starBase b) g} *
      Nat.card (Subgroup.centralizer ({starBase b} : Set StarGroup)) = 244823040 := by
  have he : (ConjClasses.mk (starBase b)).carrier = {g : StarGroup | IsConj (starBase b) g} := by
    ext g
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
    exact isConj_comm
  have h := ConjClasses.nat_card_carrier_mul_card_centralizer (starBase b)
  rw [he, starGroup_order] at h
  exact h

private theorem false_arithmetic (s n c : ℕ) (hg : n * c = 244823040)
    (hc : 7680 ≤ c) (hi : 552 * s = n * 24) : s ≤ 1600 := by
  have hm := Nat.mul_le_mul_left n hc
  rw [hg] at hm
  omega

private theorem true_arithmetic (s n c : ℕ) (hg : n * c = 244823040)
    (hc : 21504 ≤ c) (hi : 552 * s = n * 72) : s ≤ 1600 := by
  have hm := Nat.mul_le_mul_left n hc
  rw [hg] at hm
  omega

/-- The first literal star conjugacy class has at most 1600 elements fixing
 the seed's unordered pair. The incidence argument gives at most 1386. -/
theorem starClass_false_card_le : Nat.card (StarClass false) ≤ 1600 := by
  exact false_arithmetic _ _ _ (class_mul_centralizer false) centralizer_false_card_ge
    (by simpa only [Bool.false_eq_true, ↓reduceIte] using starClass_incidence false)

/-- The second literal star conjugacy class has at most 1600 elements fixing
 the seed's unordered pair. The incidence argument gives at most 1485. -/
theorem starClass_true_card_le : Nat.card (StarClass true) ≤ 1600 := by
  exact true_arithmetic _ _ _ (class_mul_centralizer true) centralizer_true_card_ge
    (by simpa only [↓reduceIte] using starClass_incidence true)

end Janko4.LocalStructure.MathieuSeedCentralizer.InvolutionBound
