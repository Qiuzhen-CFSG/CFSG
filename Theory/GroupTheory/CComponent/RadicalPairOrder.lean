module

public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.CComponent.RadicalFreeProduct
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# The orders of two distinct C-component quotients

Modulo the ambient solvable radical, distinct C-components are disjoint
commuting simple groups. Their product therefore embeds in that quotient.
The restricted quotient maps identify the factors with the original
components modulo their intrinsic solvable radicals. Consequently the
product of those two orders divides the ambient order.

This is the order obstruction used in the embedding restriction of
Aschbacher--Smith, A.3.12 and 1.2.8(1), printed pp.47--48 and 506.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {B C : Subgroup G}

private theorem radical_quotient_card_eq_image (hB : B.IsCComponent) :
    Nat.card (B ⧸ solvableRadical B) =
      Nat.card (B.map (QuotientGroup.mk' (solvableRadical G))) := by
  let q := QuotientGroup.mk' (solvableRadical G)
  let f := q.subgroupMap B
  let : Group.IsSolvable f.ker := by
    rw [show f = q.subgroupMap B from rfl, ker_subgroupMap, QuotientGroup.ker_mk']
    exact Group.isSolvable_of_isSolvable_injective
      (f := B.subtype.subgroupComap (solvableRadical G))
      (fun a b he => Subtype.ext (Subtype.ext
        (congrArg (fun x : solvableRadical G => (x : G)) he)))
  have hr := solvableRadical_eq_bot_of_isSubnormal
    (solvableRadical_quotient_solvableRadical (G := G)) (hB.map_quotient _).subnormal
  let e := (solvableRadicalQuotientEquiv f (q.subgroupMap_surjective B)).trans
    ((QuotientGroup.quotientMulEquivOfEq hr).trans QuotientGroup.quotientBot)
  exact Nat.card_congr e.toEquiv

/-- Distinct C-components contribute independent simple factors to the order. -/
theorem IsCComponent.radical_quotient_card_mul_dvd
    (hB : B.IsCComponent) (hC : C.IsCComponent) (hne : B ≠ C) :
    Nat.card (B ⧸ solvableRadical B) * Nat.card (C ⧸ solvableRadical C) ∣ Nat.card G := by
  let q := QuotientGroup.mk' (solvableRadical G)
  have hA := hB.map_quotient (solvableRadical G)
  have hD := hC.map_quotient (solvableRadical G)
  have hr := solvableRadical_quotient_solvableRadical (G := G)
  have hne' : B.map q ≠ C.map q := fun he => hne (hB.eq_of_map_quotient_eq hC _ he)
  obtain ⟨e, _⟩ := hA.exists_mulEquiv_prod_sup_of_solvableRadical_eq_bot hr
    (hA.commutator_eq_bot_of_ne_of_solvableRadical_eq_bot hr hD hne')
  rw [radical_quotient_card_eq_image hB, radical_quotient_card_eq_image hC,
    ← Nat.card_prod, Nat.card_congr e.toEquiv]
  exact (card_subgroup_dvd_card _).trans (card_quotient_dvd_card _)

end Subgroup
