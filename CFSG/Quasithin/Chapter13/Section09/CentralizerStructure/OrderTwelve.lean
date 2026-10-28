module
public import CFSG.Quasithin.Chapter13.Section09.CentralizerStructure.QuotientWreath
public import Theory.GroupTheory.QuaternionCentralProductNineOrbit
/-!
# Excluding the order-36 centralizer quotient by original marked fusion

The faithful square-action quotient has order 12 or 36. In the latter case
C_G(z) has order 1152 and an actual Sylow three-subgroup of order nine. The
intrinsic quaternion-product orbit theorem fuses all noncentral involutions
of Q. The original marked t and the noncentral Q-involution fused to z would
then be conjugate, contradicting the earlier source nonfusion.

The proof retains the original groups, central quotient, and ambient fusion;
it does not replace the order-36 action by an assumed transitivity certificate.
Source: Aschbacher–Smith 13.9.8, printed p.972.
-/
public section
namespace CFSG.Quasithin.Chapter13.Section09.CentralizerStructure
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {d : Configuration G} {m : PairData d}
namespace CoreData
variable (q : CoreData m)

private theorem not_mem_center_in_C {x : G} (hxQ : x ∈ q.Q) (hxZ : x ∉ m.Z) :
    (⟨⟨x,q.le_C hxQ⟩,hxQ⟩ : q.Q.subgroupOf m.C) ∉ center (q.Q.subgroupOf m.C) := by
  intro hc
  apply hxZ
  rw [← q.center_eq]
  refine ⟨⟨x,hxQ⟩,mem_center_iff.mpr ?_,rfl⟩
  intro y
  have hh := mem_center_iff.mp hc (⟨⟨y,q.le_C y.property⟩,y.property⟩ : q.Q.subgroupOf m.C)
  exact Subtype.ext (congrArg (fun a : q.Q.subgroupOf m.C => ((a : m.C) : G)) hh)

theorem quotient_card_twelve_of_marked_nonfusion (h : m.ClosureData)
    (hE : IsEvenCharacteristicAt d.T)
    (hfix : ∀ E : Subgroup m.Tilde, E ≤ m.tilde q.Q → Nat.card E = 8 →
      m.tilde d.T ⊓ centralizer (E : Set m.Tilde) ≤
        centralizer (m.tilde q.Q : Set m.Tilde))
    (hself : m.tilde d.T ⊓ centralizer (m.tilde q.Q : Set m.Tilde) ≤ m.tilde q.Q)
    (hgrowth : (d.T : Subgroup G) < m.C)
    (htz : ¬ IsConj m.t m.z)
    (a : G) (haQ : a ∈ q.Q) (haZ : a ∉ m.Z) (haz : IsConj a m.z) :
    letI : (q.Q.subgroupOf m.C).Normal := q.normal_of_hyperplane_fixers h hE hfix
    Nat.card (m.C ⧸ q.Q.subgroupOf m.C) = 12 := by
  let : (q.Q.subgroupOf m.C).Normal := q.normal_of_hyperplane_fixers h hE hfix
  rcases q.quotient_card_twelve_or_thirty_six h hE hfix hself hgrowth with hc | hc
  · exact hc
  have htZ : m.t ∉ m.Z := by
    intro ht
    have hV : m.V = m.Z := sup_eq_right.mpr (zpowers_le.mpr ht)
    have hh := h.card_four
    rw [hV,Nat.card_zpowers,m.z_order] at hh
    omega
  exfalso
  apply htz
  let N := q.Q.subgroupOf m.C
  let e := q.centralProductInC
  have hN : Nat.card N = 32 :=
    (Nat.card_congr (subgroupOfEquivOfLe q.le_C).toEquiv).trans q.card
  have hC : Nat.card m.C = 1152 := by
    have hh := card_eq_card_quotient_mul_card_subgroup N
    rw [hc,hN] at hh
    exact hh
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Sylow 3 m.C := Classical.choice inferInstance
  have hP : Nat.card P = 9 := by
    rw [P.card_eq_multiplicity,hC]
    decide +kernel
  let x : N := ⟨⟨m.t,m.t_mem_C⟩,q.t_mem⟩
  let y : N := ⟨⟨a,q.le_C haQ⟩,haQ⟩
  let j : N →* G := m.C.subtype.comp N.subtype
  have hj : Function.Injective j := m.C.subtype_injective.comp N.subtype_injective
  have hx : orderOf x = 2 := (orderOf_injective j hj x).symm.trans m.t_order
  have haOrder : orderOf a = 2 := by
    obtain ⟨g,hg⟩ := isConj_iff.mp haz
    have he : (MulAut.conj g) a = m.z := hg
    exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective a).symm.trans
      (he ▸ m.z_order)
  have hy : orderOf y = 2 := (orderOf_injective j hj y).symm.trans haOrder
  have hconj := isConj_noncentral_involutions_of_order_nine N
    (q.centralizer_le_of_tilde_self_centralizing h hE hfix hself)
    e.left e.right e.left_model e.right_model e.span e.intersection_card e.commute
    P hP x y hx (q.not_mem_center_in_C q.t_mem htZ) hy
    (q.not_mem_center_in_C haQ haZ)
  exact (m.C.subtype.map_isConj hconj).trans haz

end CoreData
end CFSG.Quasithin.Chapter13.Section09.CentralizerStructure
