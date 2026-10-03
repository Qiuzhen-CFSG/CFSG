module
public import Theory.GroupTheory.InvolutionTransfer
public import Theory.GroupTheory.SylowElementConjugacy
public import Theory.GroupTheory.NormalFourCentralizer
public import Theory.GroupTheory.PGroup.NormalFour

/-!
# Placing simple-group involutions in elementary eights

Suppose a Sylow two-subgroup contains a normal four-group and has elementary
rank at least three. If the ambient finite group has no normal subgroup of
index two, every involution belongs to an elementary abelian subgroup of
order at least eight.

The normal four-group's centralizer has index at most two in the Sylow
subgroup. Thompson transfer puts a conjugate of each involution into that
centralizer, where elementary joins give the required overgroup. Conjugate
it back to obtain an overgroup of the original involution.

This is the transfer step in the paragraph following GLS, volume 1,
Theorem 31.1 (`refs/KGroup/GLS1/Chapter002.tex`), using GLS, volume 2,
Lemmas 10.11 and 10.20 and Kurzweil--Stellmacher, Lemma 12.1.1. The final
theorem obtains the normal four-group from elementary rank at least three
using `IsPGroup.exists_normal_four_of_elementary_rank_three`. Thus in a
finite simple group the existence of one elementary subgroup of order at
least eight places every involution in such a subgroup.
-/

namespace Sylow

private theorem involution_order_of_isConj
    {G : Type*} [Group G] {x y : G} (hx : orderOf x = 2) (hxy : IsConj x y) :
    orderOf y = 2 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  have heq : (MulAut.conj g) x = y := hg
  rw [← heq, MulEquiv.orderOf_eq, hx]

/-- A normal four-group in a Sylow subgroup of elementary rank at least three,
together with Thompson transfer, places every ambient involution in an elementary eight. -/
public theorem exists_elementary_eight_of_normal_four
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hno : ∀ K : Subgroup G, K.Normal → K.index ≠ 2)
    (U : Subgroup S) [U.Normal] [IsElementaryAbelian 2 U] (hU : Nat.card U = 4)
    (E : Subgroup S) [IsElementaryAbelian 2 E] (hE : 8 ≤ Nat.card E)
    (t : G) (ht : orderOf t = 2) :
    ∃ A : Subgroup G, IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A ∧ t ∈ A := by
  obtain ⟨y, hty⟩ := S.exists_isConj_of_orderOf_eq_prime_pow
    (n := 1) (by simpa using ht)
  have hy : orderOf y = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact involution_order_of_isConj ht hty
  let C := Subgroup.centralizer (U : Set S)
  have hCbound : C.index ≤ 2 :=
    Subgroup.centralizer_index_le_two_of_normal_four S.isPGroup' U hU
  obtain ⟨z, htz, hzC⟩ : ∃ z : S, IsConj t (z : G) ∧ z ∈ C := by
    by_cases hC : C.index = 1
    · exact ⟨y, hty, by rw [Subgroup.index_eq_one.mp hC]; trivial⟩
    have hCtwo : C.index = 2 := by
      have hzero := C.index_ne_zero_of_finite
      omega
    obtain ⟨z, hyz, hz⟩ := S.exists_isConj_mem_of_index_two hno C hCtwo y hy
    exact ⟨z, hty.trans hyz, hz⟩
  have hz : orderOf z = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact involution_order_of_isConj ht htz
  obtain ⟨V, hV, hcard, hzV⟩ :=
    Subgroup.exists_elementary_eight_of_mem_centralizer_normal_four
      S.isPGroup' U hU E hE z (by simpa only [hz] using pow_orderOf_eq_one z) hzC
  let : IsElementaryAbelian 2 V := hV
  obtain ⟨g, hg⟩ := isConj_iff.mp htz.symm
  let f : S →* G := (MulAut.conj g).toMonoidHom.comp (S : Subgroup G).subtype
  have hf : Function.Injective f := (MulAut.conj g).injective.comp Subtype.coe_injective
  refine ⟨V.map f, IsElementaryAbelian.map f, ?_, ?_⟩
  · simpa only [Subgroup.card_map_of_injective hf] using hcard
  · exact Subgroup.mem_map.mpr ⟨z, hzV, hg⟩

/-- In a simple group the same placement follows from the local Sylow hypotheses.
The elementary eight already excludes a simple group of order two. -/
public theorem exists_elementary_eight_of_normal_four_of_simple
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] (S : Sylow 2 G)
    (U : Subgroup S) [U.Normal] [IsElementaryAbelian 2 U] (hU : Nat.card U = 4)
    (E : Subgroup S) [IsElementaryAbelian 2 E] (hE : 8 ≤ Nat.card E)
    (t : G) (ht : orderOf t = 2) :
    ∃ A : Subgroup G, IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A ∧ t ∈ A := by
  apply S.exists_elementary_eight_of_normal_four _ U hU E hE t ht
  intro K hK hindex
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K hK with hbot | htop
  · have hG : 8 ≤ Nat.card G := hE.trans
      (E.card_le_card_group.trans (S : Subgroup G).card_le_card_group)
    rw [hbot, Subgroup.index_bot] at hindex
    omega
  · simp [htop] at hindex

/-- Every involution of a finite simple group lies in an elementary eight as
soon as the group has one elementary subgroup of rank at least three. -/
public theorem exists_elementary_eight_of_simple
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hE : 8 ≤ Nat.card E)
    (t : G) (ht : orderOf t = 2) :
    ∃ A : Subgroup G, IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A ∧ t ∈ A := by
  obtain ⟨S, hES⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_le_sylow
  let ES : Subgroup S := E.subgroupOf (S : Subgroup G)
  let : IsElementaryAbelian 2 ES := IsElementaryAbelian.subgroupOf hES
  have hEScard : Nat.card ES = Nat.card E := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hES).toEquiv
  have hES8 : 8 ≤ Nat.card ES := by simpa [hEScard] using hE
  obtain ⟨U, hUN, hUelem, hUcard⟩ :=
    IsPGroup.exists_normal_four_of_elementary_rank_three S.isPGroup' ES hES8
  let : U.Normal := hUN
  let : IsElementaryAbelian 2 U := hUelem
  exact S.exists_elementary_eight_of_normal_four_of_simple U hUcard ES hES8 t ht

end Sylow
