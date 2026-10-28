module

public import Theory.SpecificGroups.PSL3.StandardCubicFixedNine
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# The odd-rank obstruction to a cubic field actor

For a binary PSL₃ model, a non-inner-diagonal standard automorphism of order
three fixes an inner elementary abelian nine-group.  If the ambient actor
subgroup contains the full inner action, this nine-group and the actor give an
elementary abelian group of order 27.  Thus an ambient odd-prime-rank bound of
two forces every cubic standard actor to be inner-diagonal.

This is the fixed-subfield step in the A.3.18 reduction.  The surrounding
component argument still has to provide the actual actor subgroup, its standard
embedding and containment of the inner action.
-/

public section

open scoped MatrixGroups
open Subgroup Theory.GroupTheory
open Matrix.PSL3.OuterSolvable

namespace Matrix.PSL3.StandardCubicFixedNine

variable {F : Type*} [Field F] [Finite F] [IsSimpleGroup PSL(3, F)]

/-- A cubic non-inner-diagonal standard actor is impossible in a subgroup of
odd three-rank at most two which contains all inner automorphisms. -/
theorem innerDiagonal_of_primeRank_three_le_two
    (hns : ¬ Group.IsSolvable PSL(3, F)) {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : Even n)
    (A : Subgroup (MulAut PSL(3, F)))
    (hinner : MulAut.innerSubgroup PSL(3, F) ≤ A)
    (hrank : primeRank 3 A ≤ 2)
    (a : MulAut PSL(3, F)) (ha : a ∈ A)
    (hstandard : a ∈ standard F) (ha3 : orderOf a = 3) :
    a ∈ innerDiagonal F := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hdiag
  obtain ⟨E, hE, hEin, hEcard, hfix⟩ :=
    exists_fixed_inner_nine hns hF hn a hstandard ha3 hdiag
  let : IsElementaryAbelian 3 E := hE
  have hEA : E ≤ A := hEin.trans hinner
  let D := E.subgroupOf A
  let : IsElementaryAbelian 3 D := IsElementaryAbelian.subgroupOf hEA
  let x : A := ⟨a, ha⟩
  have hx : orderOf x = 3 := (Subgroup.orderOf_coe x).symm.trans ha3
  have hxD : x ∉ D := fun hx => hdiag (inner_le_innerDiagonal F (hEin hx))
  have hfD : D ≤ centralizer ({x} : Set A) := by
    intro y hy
    apply mem_centralizer_singleton_iff.mpr
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hfix hy))
  have hcD : Nat.card D = 3 ^ 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEA).toEquiv).trans hEcard
  have hbound := IsElementaryAbelian.primeRank_ge_of_fixed_join D x hx hxD hfD hcD
  omega

/-- Literal standard-actor consumer: when the standard automorphism image is
itself the ambient actor subgroup and has three-rank at most two, every cubic
actor is inner-diagonal. -/
theorem standard_cubic_innerDiagonal_of_primeRank_three_le_two
    (hns : ¬ Group.IsSolvable PSL(3, F)) {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : Even n)
    (hrank : primeRank 3 (standard F) ≤ 2)
    (a : MulAut PSL(3, F)) (ha : a ∈ standard F)
    (ha3 : orderOf a = 3) :
    a ∈ innerDiagonal F := by
  exact innerDiagonal_of_primeRank_three_le_two hns hF hn (standard F)
    (inner_le_standard F) hrank a ha ha ha3

end Matrix.PSL3.StandardCubicFixedNine
