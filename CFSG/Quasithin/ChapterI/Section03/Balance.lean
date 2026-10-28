module

public import Theory.GroupTheory.CComponent.TwoComponent.OddQuotient
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent
public import FeitThompson.FinalTheorem

/-!
# The odd-core reductions for two-component balance

The odd order theorem discharges the solvability premises of the lower-layer
component correspondence. Thus every ordinary component is a two-component,
two-components correspond bijectively across odd normal quotients, and the
image of the two-layer modulo the odd core is the ordinary layer.

These results supply the odd-core reductions in Aschbacher--Smith I.3.1,
printed p.414 (combined manuscript of 1 March 2004), and GLS II,
Propositions 4.7 and 4.10. The final two lemmas isolate the ordinary-input
use of GLS 5.17 and 5.22: a layer bound puts an ordinary local component in
the ambient layer, and a two-component orbit witness is ordinary when the
ambient odd core is trivial. Neither assertion uses the B₂ property.

The universal layer bound, its orbit construction, and the general B₂
projection assertion remain to be proved. This module does not yet assert
I.3.1 or the universal OrdinaryBalance13 consumed in Chapter 2.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Balance
variable {G : Type*} [Group G] [Finite G]

/-- Discharge the lower-layer solvability premise by the odd order theorem. -/
theorem ordinary_isTwoComponent {L : Subgroup G} (hL : IsComponent G L) :
    L.IsTwoComponent := by
  let : Group.IsSolvable (pPrimeCore 2 L) := odd_order_theorem _
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  exact hL.isTwoComponent_of_solvable_oddCore

/-- The ordinary and two-component notions coincide when the ambient odd core is trivial. -/
theorem isTwoComponent_iff_isComponent (ho : pPrimeCore 2 G = ⊥) (L : Subgroup G) :
    L.IsTwoComponent ↔ IsComponent G L :=
  ⟨fun h => h.isComponent_of_oddCore_eq_bot ho, ordinary_isTwoComponent⟩

/-- The quotient correspondence has no unproved solvability premise in finite groups. -/
theorem twoComponent_odd_quotient_bijection (N : Subgroup G) [N.Normal]
    (hn : Odd (Nat.card N)) :
    Set.BijOn (map (QuotientGroup.mk' N)) {L : Subgroup G | L.IsTwoComponent}
      {K : Subgroup (G ⧸ N) | K.IsTwoComponent} := by
  let : Group.IsSolvable N := odd_order_theorem _ hn
  exact bijOn_isTwoComponent_map_odd_quotient N hn

/-- A two-component's image modulo the ambient odd core is an ordinary component. -/
theorem twoComponent_oddCore_image {L : Subgroup G} (hL : L.IsTwoComponent) :
    IsComponent (G ⧸ pPrimeCore 2 G) (L.map (QuotientGroup.mk' (pPrimeCore 2 G))) := by
  let : Group.IsSolvable (pPrimeCore 2 G) := odd_order_theorem _
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  exact hL.map_oddCore_isComponent

/-- Every ordinary component modulo the odd core lifts to a unique source two-component. -/
theorem existsUnique_twoComponent_of_oddCore_component
    {K : Subgroup (G ⧸ pPrimeCore 2 G)} (hK : IsComponent (G ⧸ pPrimeCore 2 G) K) :
    ∃! L : Subgroup G, L.IsTwoComponent ∧ L.map (QuotientGroup.mk' (pPrimeCore 2 G)) = K := by
  let : Group.IsSolvable (pPrimeCore 2 G) := odd_order_theorem _
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  obtain ⟨L, hL, he⟩ := (ordinary_isTwoComponent hK).exists_map_odd_quotient_eq
    (pPrimeCore 2 G) (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  refine ⟨L, ⟨hL, he⟩, ?_⟩
  intro J hJ
  exact hJ.1.1.eq_of_map_quotient_eq hL.1 (pPrimeCore 2 G) (hJ.2.trans he.symm)

/-- With trivial odd core the source two-layer is the ordinary layer. -/
theorem twoComponentLayer_eq_componentLayer (ho : pPrimeCore 2 G = ⊥) :
    twoComponentLayer G = componentLayer G := by
  apply congrArg sSup
  ext L
  exact isTwoComponent_iff_isComponent ho L

/-- The source two-layer maps onto the ordinary layer of the odd-core quotient. -/
theorem map_twoComponentLayer_oddCore :
    (twoComponentLayer G).map (QuotientGroup.mk' (pPrimeCore 2 G)) =
      componentLayer (G ⧸ pPrimeCore 2 G) := by
  let : Group.IsSolvable (pPrimeCore 2 G) := odd_order_theorem _
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  rw [map_twoComponentLayer_odd_quotient (pPrimeCore 2 G)
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card)]
  exact twoComponentLayer_eq_componentLayer (pPrimeCore_quotient_pPrimeCore_eq_bot (p := 2))

/-- O_{2',E}(G) is precisely the inverse image of the quotient's ordinary layer. -/
theorem oddELayer_eq_comap_componentLayer :
    oddELayer G = (componentLayer (G ⧸ pPrimeCore 2 G)).comap
      (QuotientGroup.mk' (pPrimeCore 2 G)) := by
  rw [← map_twoComponentLayer_oddCore, comap_map_eq, QuotientGroup.ker_mk',
    oddELayer, sup_comm]

/-- The ordinary-input reduction of GLS 5.17. The missing layer bound is
explicit; it is not claimed as a consequence of the component definition. -/
theorem ordinary_local_component_le_layer_of_twoLayer_bound
    (ho : pPrimeCore 2 G = ⊥) (P : Subgroup G) {D : Subgroup G}
    (hD : IsComponentIn D (centralizer (P : Set G)))
    (hbalance : (twoComponentLayer (centralizer (P : Set G))).map
      (centralizer (P : Set G)).subtype ≤ twoComponentLayer G) :
    D ≤ componentLayer G := by
  have h := map_mono (f := (centralizer (P : Set G)).subtype)
    (ordinary_isTwoComponent hD.2).le_twoComponentLayer
  rw [map_subgroupOf_eq_of_le hD.1] at h
  exact (h.trans hbalance).trans (twoComponentLayer_eq_componentLayer ho).le

/-- The pumpup part of I.3.1(2), once its orbit has been constructed.
Centralization of the odd core passes from the seed to its normal closure. -/
theorem pumpup_component_of_centralizes_oddCore
    (P D J : Subgroup G) (hJ : J.IsTwoComponent)
    (he : componentOrbit D (oddELayer G) = componentOrbit J P)
    (hD : D ≤ centralizer (pPrimeCore 2 G : Set G)) : IsComponent G J := by
  have hs : componentOrbit D (oddELayer G) ≤ centralizer (pPrimeCore 2 G : Set G) :=
    iSup_conjugates_le_of_le_normalizer D (oddELayer G) _ hD
      (by rw [normalizer_eq_top]; exact le_top)
  exact hJ.isComponent_of_centralizes_oddCore
    ((le_componentOrbit J P).trans (he.symm.le.trans hs))

/-- The ordinary-output reduction of GLS 5.22. For an ordinary local input,
only the orbit witness is needed; B₂ is absent from this deduction. -/
theorem ordinary_pumpup_of_orbit_eq (ho : pPrimeCore 2 G = ⊥)
    (P D J : Subgroup G) (hJ : J.IsTwoComponent)
    (he : componentOrbit D (oddELayer G) = componentOrbit J P) :
    IsComponent G J ∧ D ≤ componentOrbit J P :=
  ⟨hJ.isComponent_of_oddCore_eq_bot ho, he ▸ le_componentOrbit D (oddELayer G)⟩

end CFSG.Quasithin.ChapterI.Balance
