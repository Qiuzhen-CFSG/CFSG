module

public import Stellmacher.Recognition.NormalFourAbelianSylow
public import Stellmacher.Recognition.NormalFourCentralOmegaFour
public import Stellmacher.Recognition.NormalFourCentralOmegaTwo

/-!
# The normal-four branch of the rank-two Sylow classification

For a finite nonsolvable simple N₂ group with every elementary binary subgroup
of order less than eight, a Sylow two-subgroup containing a normal elementary
four-group is dihedral, isomorphic to C₄ ≀ C₂, or has the intrinsic Lyons
structure. In particular it satisfies the existing four-way Sylow alternative.

Following Janko–Thompson, Math. Z. 113 (1970), §6, pp.394–395, we first handle
the abelian case by Brauer's reduction. For a nonabelian Sylow the central
first omega subgroup has order two or four. The order-four case uses the
MacWilliams calculation and the order-two case uses §§3–4 and the odd-core
quotient split. Those three arguments are proved in the imported modules.
The dihedral alternative is essential, even when the supplied four is normal.

The final theorem joins this branch to the independent no-normal-four
classification. The full Lyons omega equality remains available through
`IsLyonsSylow.sylowStructure_of_elementary_card_lt_eight` under the same
ambient rank bound.
-/

namespace Stellmacher.Recognition

/-- The source-faithful normal-four branch, retaining the dihedral case and
using an actual wreath equivalence and the intrinsic Lyons predicate. -/
public theorem dihedral_or_wreath_or_lyons_of_normal_four
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : Stellmacher.IsNTwoGroup G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4) :
    IsDihedralGroup S ∨ Nonempty (S ≃* C4WreathC2) ∨ IsLyonsSylow S := by
  by_cases hab : IsMulCommutative S
  · let : IsMulCommutative S := hab
    obtain ⟨hcard, helem⟩ :=
      NormalFourAbelianSylow.card_eq_four_and_elementary hns hrank S E hE
    let : IsElementaryAbelian 2 S := helem
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let : Nontrivial S := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    let : IsKleinFour S := ⟨hcard, IsElementaryAbelian.exponent_eq_prime⟩
    exact Or.inl ⟨2, IsKleinFour.nonempty_mulEquiv⟩
  · have hle : Nat.card E ≤ Nat.card S := Subgroup.card_le_card_group E
    let : Nontrivial S := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    rcases S.isPGroup'.card_omega_one_center_eq_two_or_four
      (Subgroup.elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G)) with htwo | hfour
    · rcases NormalFourCentralOmegaTwo.dihedral_or_c4WreathC2_of_normal_four
        hns hN hrank S hab htwo E hE with hd | hw
      · exact Or.inl hd
      · exact Or.inr (Or.inl hw)
    · exact Or.inr (Or.inr
        (NormalFourCentralOmegaFour.isLyonsSylow hns S hrank hab hfour))

/-- A supplied normal elementary four-group gives the existing four-way
rank-two Sylow alternative. -/
public theorem rank_two_sylow_alternative_of_normal_four
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : Stellmacher.IsNTwoGroup G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4) : RankTwoSylowAlternative S := by
  apply (rankTwoSylowAlternative_iff S).mpr
  rcases dihedral_or_wreath_or_lyons_of_normal_four hns hN hrank S E hE with hd | hw | hl
  · exact Or.inl hd
  · exact Or.inr (Or.inr (Or.inl hw))
  · exact Or.inr (Or.inr (Or.inr hl))

/-- With an elementary four-group supplied, the normal-four and no-normal-four
branches together give the rank-two Sylow alternative. -/
public theorem rank_two_sylow_alternative_of_elementary_four
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : Stellmacher.IsNTwoGroup G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (E : Subgroup S) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4) : RankTwoSylowAlternative S := by
  by_cases hnormal : ∃ U : Subgroup S,
      U.Normal ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 4
  · obtain ⟨U, hn, he, hc⟩ := hnormal
    let : U.Normal := hn
    let : IsElementaryAbelian 2 U := he
    exact rank_two_sylow_alternative_of_normal_four hns hN hrank S U hc
  · exact rank_two_sylow_alternative_of_no_normal_four S S.isPGroup' hnormal E hE

end Stellmacher.Recognition
