module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Constructions
public import Theory.GroupTheory.InvolutionTransfer

/-!
# The transfer contradiction at the end of 15.3.50

In a finite simple group with a four-subgroup, there is no normal
subgroup of index two. Thompson transfer therefore takes every Sylow
involution into each index-two subgroup of that Sylow group. If the
involutions of `K = O²(C_G(Z))` lie in two ambient classes, an involution
outside both classes contradicts `|T:T ∩ K| = 2`.

The final lemma is the deduction on printed p.1151, with the index from
15.3.59(3) and the fusion assertions from 15.3.60–61 explicitly supplied.
Those local assertions still require proof before Theorem 15.3.50 can be
assembled. Transfer itself is proved by the imported theorem.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), p.1151.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian
open Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem no_normal_index_two_of_four [IsSimpleGroup G]
    (A : Subgroup G) (hA : 2 < Nat.card A) :
    ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
  intro N hN hi
  rcases hN.eq_bot_or_eq_top with hbot | htop
  · have hc : Nat.card G = 2 := by simpa only [hbot, index_bot] using hi
    have hle := Nat.card_le_card_of_injective A.subtype A.subtype_injective
    omega
  · norm_num only [htop, index_top] at hi

/-- Transfer contradicts an index-two subgroup covered by two classes avoiding an involution. -/
theorem false_of_two_class_cover
    (T : Sylow 2 G) (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (K : Subgroup G) (hindex : (K.subgroupOf (T : Subgroup G)).index = 2)
    (z v : G) (t : T) (ht : orderOf t = 2)
    (hntz : ¬ IsConj (t : G) z) (hntv : ¬ IsConj (t : G) v)
    (hcover : ∀ x ∈ K, orderOf x = 2 → IsConj x z ∨ IsConj x v) : False := by
  obtain ⟨u, htu, huK⟩ := T.exists_isConj_mem_of_index_two hno _ hindex t ht
  have hu : orderOf (u : G) = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp htu
    have he : MulAut.conj g (t : G) = u := hg
    rw [← he, MulEquiv.orderOf_eq, Subgroup.orderOf_coe, ht]
  rcases hcover u huK hu with huz | huv
  · exact hntz (htu.trans huz)
  · exact hntv (htu.trans huv)

/-- The final source contradiction, retaining the index and fusion inputs for assembly. -/
theorem false_of_residual_fusion [IsSimpleGroup G]
    (T : Sylow 2 G) (Z ZS : Subgroup G) (hZS : Nat.card ZS = 4)
    (hindex : ((residualSylow T Z).subgroupOf (T : Subgroup G)).index = 2)
    (z v : G) (t : T) (ht : orderOf t = 2)
    (hntz : ¬ IsConj (t : G) z) (hntv : ¬ IsConj (t : G) v)
    (hcover : ∀ x ∈ residualK Z, orderOf x = 2 → IsConj x z ∨ IsConj x v) : False := by
  apply false_of_two_class_cover T (no_normal_index_two_of_four ZS (by omega))
    (residualSylow T Z) hindex z v t ht hntz hntv
  intro x hx ho
  exact hcover x hx.2 ho

end CFSG.Quasithin.Chapter15.Section03.Nonabelian
