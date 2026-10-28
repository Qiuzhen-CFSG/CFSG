module

public import Theory.GroupTheory.CComponent.SylowOvergroupUnique
public import Theory.GroupTheory.CComponent.RadicalFreeProduct
public import Theory.GroupTheory.SimpleTwoRank
public import Theory.GroupTheory.PrimeRankProduct

/-!
# Two-rank obstructions to distinct C-components

Distinct C-components remain distinct modulo the solvable radical. Their
images are commuting nonabelian simple groups with trivial intersection.
Each has two-rank at least two, so their product forces two-rank at least
four in the radical quotient, and sixteen divides the original group order.
This proves uniqueness whenever subgroup radical quotients have two-rank
at most three, or the ambient order is not divisible by sixteen.

These are the no-two-components calculations used in Aschbacher--Smith,
A.3.12, printed pp.47--48, and 1.2.8(1), printed p.506.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Distinct components force two independent simple factors in the radical quotient. -/
theorem four_le_twoRank_radicalQuotient_of_distinct_cComponents
    {B C : Subgroup G} (hB : B.IsCComponent)
    (hC : C.IsCComponent) (hne : B ≠ C) :
    4 ≤ primeRank 2 (G ⧸ solvableRadical G) := by
  let q := QuotientGroup.mk' (solvableRadical G)
  let A := B.map q
  let D := C.map q
  have hA : A.IsCComponent := hB.map_quotient _
  have hD : D.IsCComponent := hC.map_quotient _
  have hR : solvableRadical (G ⧸ solvableRadical G) = ⊥ :=
    solvableRadical_quotient_solvableRadical
  have hne' : A ≠ D := fun he => hne (hB.eq_of_map_quotient_eq hC _ he)
  let : IsSimpleGroup A := hA.isSimpleGroup_of_solvableRadical_eq_bot hR
  let : IsSimpleGroup D := hD.isSimpleGroup_of_solvableRadical_eq_bot hR
  have hAr := two_le_twoRank_of_nonabelian_simple
    (hA.not_isMulCommutative_of_solvableRadical_eq_bot hR)
  have hDr := two_le_twoRank_of_nonabelian_simple
    (hD.not_isMulCommutative_of_solvableRadical_eq_bot hR)
  obtain ⟨e,_⟩ := hA.exists_mulEquiv_prod_sup_of_solvableRadical_eq_bot hR
    (hA.commutator_eq_bot_of_ne_of_solvableRadical_eq_bot hR hD hne')
  have hr := primeRank_le_of_injective 2 (A ⊔ D).subtype (A ⊔ D).subtype_injective
  rw [← primeRank_equiv 2 e, primeRank_prod_eq_add] at hr
  omega

/-- The order consequence requires no lifting of elementary subgroups through the radical. -/
theorem sixteen_dvd_card_of_distinct_cComponents
    {B C : Subgroup G} (hB : B.IsCComponent)
    (hC : C.IsCComponent) (hne : B ≠ C) : 16 ∣ Nat.card G := by
  have hr := four_le_twoRank_radicalQuotient_of_distinct_cComponents hB hC hne
  obtain ⟨E,_,hE⟩ := exists_elementaryAbelian_card_primeRank
    (G := G ⧸ solvableRadical G) (p := 2)
  have hd : 16 ∣ Nat.card E := by
    rw [hE]
    exact Nat.pow_dvd_pow 2 hr
  exact hd.trans (E.card_subgroup_dvd_card.trans
    (card_dvd_of_surjective (QuotientGroup.mk' (solvableRadical G))
      (QuotientGroup.mk'_surjective _)))

/-- Two-rank at most three in the radical quotient permits at most one component. -/
theorem cComponents_eq_of_radicalQuotient_twoRank_le_three
    (hr : primeRank 2 (G ⧸ solvableRadical G) ≤ 3)
    {B C : Subgroup G} (hB : B.IsCComponent) (hC : C.IsCComponent) : B = C := by
  by_contra hne
  have := four_le_twoRank_radicalQuotient_of_distinct_cComponents hB hC hne
  omega

namespace SylowOvergroupComponentUnique

/-- In particular, Sylow overgroups have unique components if sixteen does not divide the order. -/
theorem of_not_sixteen_dvd_card (hc : ¬ 16 ∣ Nat.card G) :
    SylowOvergroupComponentUnique G := by
  intro _ P _ B C hB hC
  by_contra hne
  exact hc ((sixteen_dvd_card_of_distinct_cComponents hB hC hne).trans
    P.card_subgroup_dvd_card)

/-- A bound on subgroup radical quotients supplies the actual Sylow-overgroup property. -/
theorem of_subgroup_radicalQuotient_twoRank_le_three
    (hr : ∀ P : Subgroup G, primeRank 2 (P ⧸ solvableRadical P) ≤ 3) :
    SylowOvergroupComponentUnique G := by
  intro _ P _ _ _ hB hC
  exact cComponents_eq_of_radicalQuotient_twoRank_le_three (hr P) hB hC

end SylowOvergroupComponentUnique
end Theory.GroupTheory
