module

public import CFSG.Quasithin.MainConverse.OddClassicalLocal.UnitaryThreeFour.DimensionFour
public import Theory.GroupTheory.ElementaryNormalizerThreeRank

/-!
# PSU₄(3): reduction of the three-rank calculation to centralizers

For elementary two-subgroups of order at most sixteen, the normalizer order
is controlled by the centralizer and the actual conjugation image in the
automorphism group. The only geometric inputs needed here are the elementary
size bound, the absence of 27 and 9 in centralizers in orders two and four,
and the absence of 3 in centralizers in order sixteen. Order eight follows
from the four-subgroup calculation. All subgroups are inside the actual
projective SU image over `FiniteField.Nine`, with its scalar kernel retained.

The theorems below are conditional reductions: the model centralizer and
size premises remain to be proved. Once discharged, the existing elementary
normalizer reduction gives the QT clause of Aschbacher–Smith, Theorem
0.1.2(4), printed p.4, repeated as Theorem 0.1.1(4), printed p.482.
-/

open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree

namespace CFSG.Quasithin.MainConverse.UnitaryFourThree

/-- Conditional defining-prime bound in the actual elementary normalizer.
The Sylow containment restricts all geometric calculations to one Sylow group. -/
public theorem elementary_normalizer_three_rank_of_centralizer_bounds
    (S : Sylow 2 (Carrier 4))
    (hsize : ∀ A : Subgroup (Carrier 4), A ≤ (S : Subgroup (Carrier 4)) →
      IsElementaryAbelian 2 A → Nat.card A ≤ 16)
    (htwo : ∀ A : Subgroup (Carrier 4), A ≤ (S : Subgroup (Carrier 4)) →
      IsElementaryAbelian 2 A → Nat.card A = 2 →
        ¬ 3 ^ 3 ∣ Nat.card (Subgroup.centralizer (A : Set (Carrier 4))))
    (hfour : ∀ A : Subgroup (Carrier 4), A ≤ (S : Subgroup (Carrier 4)) →
      IsElementaryAbelian 2 A → Nat.card A = 4 →
        ¬ 3 ^ 2 ∣ Nat.card (Subgroup.centralizer (A : Set (Carrier 4))))
    (hsixteen : ∀ A : Subgroup (Carrier 4), A ≤ (S : Subgroup (Carrier 4)) →
      IsElementaryAbelian 2 A → Nat.card A = 16 →
        ¬ 3 ∣ Nat.card (Subgroup.centralizer (A : Set (Carrier 4))))
    (A : Subgroup (Carrier 4)) (hAS : A ≤ (S : Subgroup (Carrier 4)))
    (hA : A ≠ ⊥) (hEA : IsElementaryAbelian 2 A) :
    primeRank 3 (Subgroup.normalizer (A : Set (Carrier 4))) ≤ 2 := by
  apply A.primeRank_three_normalizer_le_two_of_elementary_centralizers
    hA hEA (hsize A hAS hEA) (htwo A hAS hEA) ?_ (hsixteen A hAS hEA)
  intro B hBA hEB hB
  exact hfour B (hBA.trans hAS) hEB hB

/-- Conditional QT assembly using the existing elementary-normalizer theorem.
The centralizer and size inputs are precisely the remaining model obligations. -/
public theorem model_quasithin_of_elementary_centralizer_bounds
    (S : Sylow 2 (Carrier 4))
    (hsize : ∀ A : Subgroup (Carrier 4), A ≤ (S : Subgroup (Carrier 4)) →
      IsElementaryAbelian 2 A → Nat.card A ≤ 16)
    (htwo : ∀ A : Subgroup (Carrier 4), A ≤ (S : Subgroup (Carrier 4)) →
      IsElementaryAbelian 2 A → Nat.card A = 2 →
        ¬ 3 ^ 3 ∣ Nat.card (Subgroup.centralizer (A : Set (Carrier 4))))
    (hfour : ∀ A : Subgroup (Carrier 4), A ≤ (S : Subgroup (Carrier 4)) →
      IsElementaryAbelian 2 A → Nat.card A = 4 →
        ¬ 3 ^ 2 ∣ Nat.card (Subgroup.centralizer (A : Set (Carrier 4))))
    (hsixteen : ∀ A : Subgroup (Carrier 4), A ≤ (S : Subgroup (Carrier 4)) →
      IsElementaryAbelian 2 A → Nat.card A = 16 →
        ¬ 3 ∣ Nat.card (Subgroup.centralizer (A : Set (Carrier 4)))) :
    IsQuasithin (Carrier 4) :=
  model_quasithin_of_elementary_normalizer_rank S
    (elementary_normalizer_three_rank_of_centralizer_bounds S hsize htwo hfour hsixteen)

end CFSG.Quasithin.MainConverse.UnitaryFourThree
