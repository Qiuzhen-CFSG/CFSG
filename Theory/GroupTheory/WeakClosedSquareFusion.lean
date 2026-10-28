module
public import Theory.GroupTheory.OrderFourSquareTransfer
public import Theory.GroupTheory.OrderFourWeakClosure
/-!
# An involution obtained by square transfer

If the square z of an order-four element is weakly closed in P, and a
subgroup F containing S is normalized by C_G(z), the order-four class
avoids S whenever its chosen representative lies outside F. Transfer from
an index-two subgroup S of a Sylow two-subgroup then produces an involution
outside S conjugate to z.

Source: Aschbacher--Smith A.1.37 and 2.4.29, printed p.546.
-/
public section
open Subgroup
namespace Sylow

/-- Weak closure of a square, together with a normal separation subgroup,
forces its class into the complement of an index-two Sylow subgroup. -/
theorem exists_isConj_involution_outside_of_weak_closed_square
    {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G)
    (hno : ∀K:Subgroup G, K.Normal → K.index≠2)
    (S P F : Subgroup G) (hST:S≤(T:Subgroup G))
    (hi:S.relIndex (T:Subgroup G)=2) (hSF:S≤F)
    (hphi:(frattini S).map S.subtype≤P)
    (j z:G) (hjT:j∈(T:Subgroup G)) (hj4:orderOf j=4)
    (hjsq:j^2=z) (hjF:j∉F) (hz2:orderOf z=2)
    (hn:centralizer ({z}:Set G)≤normalizer (F:Set G))
    (hweak:∀x∈P, IsConj z x→x=z) :
    ∃i∈(T:Subgroup G), i∉S ∧ orderOf i=2 ∧ IsConj z i := by
  have havoid := Subgroup.order_four_class_avoids_of_square_weak_closed
    S P F (T.isPGroup'.to_le hST) hSF hphi j z hjsq hjF hn hweak
  let Q := S.subgroupOf (T:Subgroup G)
  let jj : T := ⟨j,hjT⟩
  have hQ : Q.index=2 := hi
  have hjj : orderOf jj=4 :=
    (orderOf_injective (T:Subgroup G).subtype (T:Subgroup G).subtype_injective jj).symm.trans hj4
  obtain ⟨other,hconj,hout⟩ := T.exists_isConj_square_outside_of_order_four
    hno Q hQ jj hjj (fun other hh ho=>havoid other ho hh)
  have hzi : IsConj z (other:G) := by
    change IsConj (j^2) (other:G) at hconj
    rwa [hjsq] at hconj
  have ho : orderOf (other:G)=2 := by
    obtain ⟨c,hc⟩ := hzi
    exact (SemiconjBy.orderOf_eq (c:G) hc).symm.trans hz2
  exact ⟨other,other.property,hout,ho,hzi⟩
end Sylow

