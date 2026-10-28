module
public import Theory.GroupAction.Quotient
public import Theory.GroupAction.QuotientFixedIndex


/-!
# Fixed-index budgets on nonabelian normal sections

For an arbitrary automorphism action on a finite group, the product of the
fixed indices on an invariant normal subgroup and its quotient is bounded
by the fixed index of the group. The group need not be abelian and the
actor need not have coprime order. Fixed elements map into quotient fixed
elements; counting the kernel and image gives the bound.

This is the group-level movement budget used before radius centrality in
Meierfrankenfeld--Stellmacher (1993), (5.2)(i), printed p.914. Individual chief
factors can then be linearized without assuming the entire radius quotient
is elementary abelian.
-/

@[expose] public section
namespace FixedPoints
open Subgroup
variable {A P : Type*} [Group A] [Group P] [Finite P]
  [MulDistribMulAction A P]

theorem card_le_quotient_mul_kernel (N : Subgroup P) [N.Normal]
    (hN : IsInvariant A P N) :
    letI : MulDistribMulAction A (P ⧸ N) := quotientMulDistribMulAction N hN
    Nat.card (subgroup A P) ≤
      Nat.card (subgroup A (P ⧸ N)) * Nat.card ↥(N ⊓ subgroup A P) := by
  let : MulDistribMulAction A (P ⧸ N) := quotientMulDistribMulAction N hN
  let C := subgroup A P
  let f := (QuotientGroup.mk' N).comp C.subtype
  have hrange : f.range ≤ subgroup A (P ⧸ N) := by
    rintro x ⟨c,rfl⟩ a
    change QuotientGroup.mk' N (a • (c : P)) = QuotientGroup.mk' N c
    rw [c.property a]
  let e : f.ker ≃ ↥(N ⊓ C) := {
    toFun := fun x => ⟨x.val.val,
      (QuotientGroup.eq_one_iff x.val.val).mp x.property,x.val.property⟩
    invFun := fun x => ⟨⟨x.val,x.property.2⟩,
      (QuotientGroup.eq_one_iff x.val).mpr x.property.1⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  calc
    Nat.card C = Nat.card f.range * Nat.card f.ker := by
      rw [← index_ker,index_mul_card]
    _ ≤ Nat.card (subgroup A (P ⧸ N)) * Nat.card f.ker :=
      Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective
        (inclusion hrange) (inclusion_injective hrange))
    _ = _ := by rw [Nat.card_congr e]

theorem quotient_index_mul_kernel_index_le (N : Subgroup P) [N.Normal]
    (hN : IsInvariant A P N) :
    letI := hN
    letI : MulDistribMulAction A (P ⧸ N) := quotientMulDistribMulAction N hN
    (subgroup A (P ⧸ N)).index * (subgroup A N).index ≤
      (subgroup A P).index := by
  let := hN
  let : MulDistribMulAction A (P ⧸ N) := quotientMulDistribMulAction N hN
  have hker : (N ⊓ subgroup A P).subgroupOf N = subgroup A N := by
    ext n
    constructor
    · intro hn a
      exact Subtype.ext (hn.2 a)
    · intro hn
      exact ⟨n.property,fun a => congrArg Subtype.val (hn a)⟩
  have hc : Nat.card ↥(N ⊓ subgroup A P) = Nat.card (subgroup A N) := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe
      (show N ⊓ subgroup A P ≤ N from inf_le_left)).toEquiv,hker]
  have hcard := card_le_quotient_mul_kernel N hN
  rw [hc] at hcard
  apply Nat.le_of_mul_le_mul_right (c := Nat.card (subgroup A P)) _ Nat.card_pos
  calc
    ((subgroup A (P ⧸ N)).index * (subgroup A N).index) *
        Nat.card (subgroup A P) ≤
      ((subgroup A (P ⧸ N)).index * (subgroup A N).index) *
        (Nat.card (subgroup A (P ⧸ N)) * Nat.card (subgroup A N)) :=
      Nat.mul_le_mul_left _ hcard
    _ = Nat.card (P ⧸ N) * Nat.card N := by
      rw [show ((subgroup A (P ⧸ N)).index * (subgroup A N).index) *
          (Nat.card (subgroup A (P ⧸ N)) * Nat.card (subgroup A N)) =
          ((subgroup A (P ⧸ N)).index * Nat.card (subgroup A (P ⧸ N))) *
            ((subgroup A N).index * Nat.card (subgroup A N)) by ring]
      rw [index_mul_card,index_mul_card]
    _ = Nat.card P := (card_eq_card_quotient_mul_card_subgroup N).symm
    _ = (subgroup A P).index * Nat.card (subgroup A P) :=
      (index_mul_card _).symm

end FixedPoints
