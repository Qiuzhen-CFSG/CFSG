module
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.IndexNormal

/-!
# Intersection order for two subgroups of index two

Two subgroups of order sixteen whose join has order thirty-two intersect
in order eight. Restrict to their join; index two gives normality, and
the normalized product order formula gives the intersection order.

Source application: the elementary pair in Aschbacher--Smith F.5.5, p.302.
-/

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
/-- Two sixteen-subgroups generating order thirty-two intersect in order eight. -/
public theorem inf_card_eight_of_card_sixteen_sup_thirtytwo (B0 B1 : Subgroup G)
    (hc0 : Nat.card B0 = 16) (hc1 : Nat.card B1 = 16)
    (hs : Nat.card (B0 ⊔ B1 : Subgroup G) = 32) :
    Nat.card (B0 ⊓ B1 : Subgroup G) = 8 := by
  let S := B0 ⊔ B1
  let A0 := B0.subgroupOf S
  let A1 := B1.subgroupOf S
  have h0 : Nat.card A0=16 := (Nat.card_congr (subgroupOfEquivOfLe le_sup_left).toEquiv).trans hc0
  have h1 : Nat.card A1=16 := (Nat.card_congr (subgroupOfEquivOfLe le_sup_right).toEquiv).trans hc1
  have hi : A0.index=2 := by
    have hh := A0.card_mul_index
    rw [h0,show Nat.card S=32 from hs] at hh
    omega
  let := A0.normal_of_index_eq_two hi
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes A0 A1 le_normalizer_of_normal
  have hinf : Nat.card (A0 ⊓ A1 : Subgroup S)=Nat.card (B0 ⊓ B1 : Subgroup G) := by
    change Nat.card ((B0 ⊓ B1).subgroupOf S)=_
    exact Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans le_sup_left)).toEquiv
  have hsup : Nat.card (A0 ⊔ A1 : Subgroup S)=32 := by
    rw [←subgroupOf_sup le_sup_left le_sup_right]
    change Nat.card (S.subgroupOf S)=32
    rw [subgroupOf_self,card_top]
    exact hs
  rw [h0,h1,hinf,hsup] at hh
  omega
end Subgroup
