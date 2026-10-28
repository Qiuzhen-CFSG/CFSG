module
public import Theory.GroupTheory.CoprimeIndexMarking
public import Theory.GroupTheory.SylowSubnormalIntersection

/-!
# Prime divisors of subnormal intersections at prime-to-p index

A Sylow p-subgroup of a subgroup H of index prime to p stays Sylow in
the ambient group. Its intersection with a subnormal K is Sylow in K.
Thus every factor p in the order of K also occurs in K ∩ H. The statement
uses relative subnormality and the literal intersection.
Source application: Aschbacher--Smith 14.6.15, printed pp.1033--1034.
-/
public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem prime_dvd_intersection_of_subnormal_of_primeTo_index
    (H K : Subgroup G) (hH : ¬p ∣ H.index) (hK : K.IsSubnormal)
    (hd : p ∣ Nat.card K) : p ∣ Nat.card (K ⊓ H : Subgroup G) := by
  let P : Sylow p H := Classical.choice inferInstance
  let S : Sylow p G := P.mapSubtypeOfIndexPrimeTo hH
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_subnormal K hK
  have hRH : (R : Subgroup K).map K.subtype ≤ K ⊓ H := by
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨x.property,?_⟩
    rw [hR] at hx
    exact (map_subtype_le (P : Subgroup H)) hx
  have hdR := R.dvd_card_of_dvd_card hd
  have hc : Nat.card ((R : Subgroup K).map K.subtype) = Nat.card R :=
    card_map_of_injective K.subtype_injective
  exact (hc ▸ hdR).trans (card_dvd_of_le hRH)

end Subgroup
