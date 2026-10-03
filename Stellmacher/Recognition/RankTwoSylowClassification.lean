module

public import Stellmacher.Recognition.NormalFourSylowClassification
public import Stellmacher.Recognition.SimpleInvolutionFusion
public import Theory.GroupTheory.PGroup.RankOneInvolution

/-!
# The complete low-rank Sylow reduction

A Sylow two-subgroup of a finite nonsolvable simple N₂ group of elementary
binary rank at most two is dihedral, semidihedral, isomorphic to C₄ ≀ C₂,
or has the intrinsic order-64 Lyons structure.

First, every Sylow two-subgroup of a finite nonsolvable simple group contains
an elementary four: odd order is excluded by Feit–Thompson, and absence of a
four would give a unique involution, contradicting the distinct Sylow conjugate
supplied by Glauberman's Z-star theorem. The normal-four and no-normal-four
classifications then apply. In the Lyons case the ambient rank bound supplies
the first omega equality as well as the other intrinsic equalities.

The classification is Janko–Thompson, Math. Z. 113 (1970), §§3–6,
pp.394–396; the full intrinsic structure is Lyons, Trans. AMS 164 (1972),
Theorem 2, p.372. See the source audit in
`refs/original/n-group-global/odd-core-rank-two-source/README.md`.
This extension preserves the original four-way interface without introducing
an import cycle through the normal-four classification.
-/

namespace Stellmacher.Recognition
/-- Every Sylow two-subgroup of a finite nonsolvable simple group contains
an elementary abelian subgroup of order four. -/
public theorem exists_elementary_four_in_sylow_of_simple_nonsolvable
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G) :
    ∃ E : Subgroup S, IsElementaryAbelian 2 E ∧ Nat.card E = 4 := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdiv : 2 ∣ Nat.card S :=
    S.dvd_card_of_dvd_card (simple_nonsolvable_inputs hns).1.two_dvd
  let : Nontrivial S := Finite.one_lt_card_iff_nontrivial.mp
    (lt_of_lt_of_le (by decide : 1 < 2) (Nat.le_of_dvd Nat.card_pos hdiv))
  by_contra hnone
  have hfour (E : Subgroup S) (he : IsElementaryAbelian 2 E) : Nat.card E ≠ 4 :=
    fun hc => hnone ⟨E, he, hc⟩
  obtain ⟨z, hz, _, huniq⟩ :=
    S.isPGroup'.exists_central_involution_of_no_elementary_four hfour
  obtain ⟨t, htz, hconj⟩ := exists_distinct_isConj_in_sylow hns S z hz
  have ht : orderOf t = 2 := by
    obtain ⟨g, hg⟩ := hconj
    have heq := SemiconjBy.orderOf_eq (g : G) hg
    simpa only [Subgroup.orderOf_coe, hz] using heq.symm
  rcases huniq t (by simpa only [ht] using pow_orderOf_eq_one t) with hone | heq
  · simp [hone] at ht
  · exact htz heq

/-- The complete four-way reduction with the original public alternatives. -/
public theorem rank_two_sylow_alternative
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) : RankTwoSylowAlternative S := by
  obtain ⟨E, he, hcard⟩ := exists_elementary_four_in_sylow_of_simple_nonsolvable hns S
  let : IsElementaryAbelian 2 E := he
  exact rank_two_sylow_alternative_of_elementary_four hns hN hrank S E hcard

/-- The four-way reduction with all of Lyons's intrinsic equalities, including
`Z(S) = Ω₁(S)`, in the last alternative. -/
public theorem rank_two_sylow_structure_alternative
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) :
    IsDihedralGroup S ∨ IsSemidihedralGroup S ∨
      Nonempty (S ≃* C4WreathC2) ∨ LyonsU3Four.SylowStructure S := by
  rcases (rankTwoSylowAlternative_iff S).mp
    (rank_two_sylow_alternative hns hN hrank S) with hd | hs | hw | hl
  · exact Or.inl hd
  · exact Or.inr (Or.inl hs)
  · exact Or.inr (Or.inr (Or.inl hw))
  · exact Or.inr (Or.inr (Or.inr
      (hl.sylowStructure_of_elementary_card_lt_eight S hrank)))

end Stellmacher.Recognition
