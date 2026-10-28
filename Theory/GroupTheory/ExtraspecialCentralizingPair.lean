module
public import Theory.GroupTheory.ExtraspecialIntersection

/-!
# Centralizing commutator pairs in extraspecial two-groups

In an extraspecial group of order greater than eight, every element centralizer
is nonabelian: its index is at most two, whereas an abelian subgroup has square
order at most twice the group order. Any noncommuting pair in that centralizer
has commutator equal to the unique nonidentity central element.

This supplies the mutual-core witness for arbitrary returning central
involutions in the triality application, without a chosen root representative.
Source: Aschbacher--Smith F.4.35, printed p.292.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Theory.GroupTheory.ExtraspecialIntersection
variable {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P]

/-- The order-eight bound is sharp: reflection centralizers in D₈ are abelian. -/
theorem centralizer_noncommutative_of_card_gt_eight (hcard : 8 < Nat.card P) (q : P) :
    ¬ IsMulCommutative (centralizer ({q} : Set P)) := by
  intro hc
  let := hc
  let C := centralizer ({q} : Set P)
  have hb := extraspecial_prime_abelian_card_sq_le_any (p := 2) C
  by_cases hq : q ∈ center P
  · have he : C = ⊤ := by
      apply top_unique
      intro x _
      exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hq x)
    rw [he, Nat.card_congr (topEquiv : (⊤ : Subgroup P) ≃* P).toEquiv] at hb
    nlinarith
  · have hi := centralizer_index_two q hq
    have he := C.card_mul_index
    change Nat.card C * (centralizer ({q} : Set P)).index = Nat.card P at he
    rw [hi] at he
    nlinarith

/-- Every element centralizes a pair whose commutator is the prescribed nontrivial center element. -/
theorem centralizing_pair_of_card_gt_eight (hcard : 8 < Nat.card P)
    (q z : P) (hz : z ∈ center P) (hz1 : z ≠ 1) :
    ∃ x y : P, Commute x q ∧ Commute y q ∧ ⁅x,y⁆ = z := by
  have hn := centralizer_noncommutative_of_card_gt_eight hcard q
  obtain ⟨x,y,hxy⟩ : ∃ x y : centralizer ({q} : Set P), x*y ≠ y*x := by
    by_contra! he
    exact hn ⟨⟨he⟩⟩
  have hc : ⁅x.val,y.val⁆ ∈ center P :=
    (IsExtraspecial.quotient_elementary_abelian 2 P).commutator_le_center_of_central_quotient
      (commutator_mem_commutator (mem_top _) (mem_top _))
  have hn1 : ⁅x.val,y.val⁆ ≠ 1 := by
    intro he
    exact hxy (Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mp he))
  have he : ⁅x.val,y.val⁆ = z := congrArg Subtype.val
    (((Nat.card_eq_two_iff' (1 : center P)).mp (IsExtraspecial.center_order_p 2 P)).unique
      (show (⟨⁅x.val,y.val⁆,hc⟩ : center P) ≠ 1 from fun h => hn1 (congrArg Subtype.val h))
      (show (⟨z,hz⟩ : center P) ≠ 1 from fun h => hz1 (congrArg Subtype.val h)))
  exact ⟨x,y,mem_centralizer_singleton_iff.mp x.property,
    mem_centralizer_singleton_iff.mp y.property,he⟩
end Theory.GroupTheory.ExtraspecialIntersection
