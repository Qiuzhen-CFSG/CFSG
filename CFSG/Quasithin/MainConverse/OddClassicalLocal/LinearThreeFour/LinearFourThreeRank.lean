module

public import Theory.SpecificGroups.PSL4Three.LocalThree.ElementaryBound
public import Theory.SpecificGroups.PSL4Three.LocalThree.FourCentralizer
public import Theory.SpecificGroups.PSL4Three.LocalThree.InvolutionCentralizer
public import Theory.GroupTheory.ElementaryNormalizerThreeRank
public import Theory.GroupTheory.MaximalTwoLocalElementary

/-!
# PSL₄(3): local three-rank from involution and four-group centralizers

Every two-local lies in a maximal two-local, which is the full normalizer of
a nonidentity elementary two-subgroup. The trace-pairing calculation bounds
that subgroup's order by sixteen and excludes three from its centralizer at
equality. The actual matrix centralizer calculations exclude 27 from involution
centralizers and 9 from four-group centralizers, including projectively
centralizing lifts that anticommute. The eight-element case follows from
containment in a four-group centralizer. The conjugation action on the
elementary subgroup then excludes 27 from the normalizer order and bounds
the three-rank of every two-local by two.

The conditional reductions are retained, and the final theorems discharge
both centralizer premises. No simplicity or noncommutativity hypothesis is
needed for this intrinsic local calculation.
Source: Aschbacher–Smith, Theorem 0.1.2(4), printed p.4, repeated as
Theorem 0.1.1(4) on printed p.482 of `refs/quasithin.pdf`.
-/

open Subgroup Matrix.PSL4Three.LocalThree

namespace CFSG.Quasithin.MainConverse

/-- Reduction to the centralizers in elementary orders two and four.
The model's size bound and order-sixteen centralizer bound are discharged. -/
public theorem psl4_three_twoLocal_cube_not_dvd_of_centralizer_bounds
    (htwo : ∀ A : Subgroup P, IsElementaryAbelian 2 A → Nat.card A = 2 →
      ¬ 3 ^ 3 ∣ Nat.card (centralizer (A : Set P)))
    (hfour : ∀ A : Subgroup P, IsElementaryAbelian 2 A → Nat.card A = 4 →
      ¬ 3 ^ 2 ∣ Nat.card (centralizer (A : Set P)))
    (M : Subgroup P) (hM : IsTwoLocal M) : ¬ 3 ^ 3 ∣ Nat.card M := by
  obtain ⟨L, hML, hL⟩ := Finite.exists_le_maximal hM
  obtain ⟨A, hA, hEA, rfl⟩ :=
    Theory.GroupTheory.exists_elementary_normalizer_of_isMaximalTwoLocal hL
  have hN := A.three_cube_not_dvd_card_normalizer_of_elementary_centralizers
    hA hEA (elementary_card_le_sixteen A hEA) (htwo A hEA)
    (fun B _ hB hcard => hfour B hB hcard)
    (centralizer_not_three_dvd_of_card_eq_sixteen A hEA)
  exact fun hdiv => hN (hdiv.trans (card_dvd_of_le hML))

/-- Conditional assembly of the local three-rank bound from the two
centralizer bounds. The unconditional theorem below supplies both inputs. -/
public theorem psl4_three_twoLocal_three_rank_of_centralizer_bounds
    (htwo : ∀ A : Subgroup P, IsElementaryAbelian 2 A → Nat.card A = 2 →
      ¬ 3 ^ 3 ∣ Nat.card (centralizer (A : Set P)))
    (hfour : ∀ A : Subgroup P, IsElementaryAbelian 2 A → Nat.card A = 4 →
      ¬ 3 ^ 2 ∣ Nat.card (centralizer (A : Set P)))
    (M : Subgroup P) (hM : IsTwoLocal M) : primeRank 3 M ≤ 2 :=
  primeRank_le_two_of_cube_not_dvd
    (psl4_three_twoLocal_cube_not_dvd_of_centralizer_bounds htwo hfour M hM)

/-- Every two-local in the actual PSL₄(3) model has order indivisible by 27. -/
public theorem psl4_three_twoLocal_cube_not_dvd
    (M : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 3)))
    (hM : IsTwoLocal M) : ¬ 3 ^ 3 ∣ Nat.card M :=
  psl4_three_twoLocal_cube_not_dvd_of_centralizer_bounds
    (fun A _ => centralizer_three_part_of_card_eq_two A)
    four_centralizer_not_nine_dvd M hM

/-- Every normalizer of a nonidentity two-subgroup in PSL₄(3) has three-rank
at most two, as required by its quasithin converse. -/
public theorem psl4_three_twoLocal_three_rank
    (M : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 3)))
    (hM : IsTwoLocal M) : primeRank 3 M ≤ 2 :=
  primeRank_le_two_of_cube_not_dvd (psl4_three_twoLocal_cube_not_dvd M hM)

end CFSG.Quasithin.MainConverse
