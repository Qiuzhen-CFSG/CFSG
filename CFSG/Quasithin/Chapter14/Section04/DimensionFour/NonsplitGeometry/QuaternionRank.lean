module

public import Theory.GroupTheory.QuaternionCentralProductC2Action

/-!
# The c₂ quaternion-extension rank in 14.4.4(6)

The local group P = UWᵍ has its actual index-two quaternion central product U
and an embedded elementary eight V. The outside action is conjugation on U,
with Suzuki type c₂ interpreted on U/Z(U) using its intrinsic square form.
The chosen outside representative need not be an involution.

The c₂ calculation proves outer restriction on both quaternion factors.
Inner twists preserve these restrictions; an outside elementary subgroup
therefore intersects U in at most the fixed four of one of its own outside
involutions. The inside bound and the index-two intersection formula give
rank at most three, while V gives equality. The order is 64.

The final theorem transports these results along the actual equality
P = T ∩ L. Its rank and elementary-cardinality conclusions discharge exactly
the `hrank` and the derived `hbound` used by
`NonsplitGeometry.elementary_extension_transfer_of_fixed_spaces`; its order
conclusion supplies the regular-action calculation. That later theorem's
fixed-space, lifting, and global hypotheses remain with its assembly owner.

Source: Aschbacher–Smith, Lemma 14.4.4(2),(5),(6) and the proof of 14.4.5,
printed pp.1007–1008. This is the conditional local-model calculation, not
the source proof excluding the split block.
-/

open Subgroup

namespace CFSG.Quasithin.Chapter14.Section04.DimensionFour.NonsplitGeometry

/-- The actual c₂ extension has order 64, rank three, and no elementary sixteen. -/
public theorem quaternion_c2_rank_and_order
    {P : Type*} [Group P] [Finite P] (U : Subgroup P) [U.Normal]
    (d : QuaternionCentralProductData U) (hindex : U.index = 2)
    (a : P) (ha : a ∉ U) (hc2 : d.IsC2 (MulAut.conjNormal a))
    (V : Subgroup U) (hV : IsElementaryAbelian 2 V) (hVcard : Nat.card V = 8) :
    Nat.card P = 64 ∧ primeRank 2 P = 3 ∧
      ∀ E : Subgroup P, IsElementaryAbelian 2 E → Nat.card E ≤ 8 := by
  have hout := QuaternionCentralProductData.IsC2.bothOuter d hc2
  obtain ⟨hcard,hrank⟩ := quaternion_index_two_rank U d hindex a ha hout V hV hVcard
  exact ⟨hcard,hrank,quaternion_index_two_elementary_card_le U d hindex a ha hout⟩

/-- Transport through P = T ∩ L, retaining the literal ambient elementary subgroups.
The three conclusions supply the order, `hrank`, and elementary-cardinality
premises of the nonsplit elementary-extension transfer argument. -/
public theorem quaternion_c2_transfer_bounds
    {G : Type*} [Group G] [Finite G]
    (T L P : Subgroup G) (hP : P = T ⊓ L)
    (U : Subgroup P) [U.Normal] (d : QuaternionCentralProductData U)
    (hindex : U.index = 2) (a : P) (ha : a ∉ U)
    (hc2 : d.IsC2 (MulAut.conjNormal a))
    (V : Subgroup U) (hV : IsElementaryAbelian 2 V) (hVcard : Nat.card V = 8) :
    Nat.card (T ⊓ L : Subgroup G) = 64 ∧
    primeRank 2 (T ⊓ L : Subgroup G) ≤ 3 ∧
    ∀ E : Subgroup G, E ≤ T → E ≤ L → IsElementaryAbelian 2 E → Nat.card E ≤ 8 := by
  subst P
  obtain ⟨hcard,hrank,hbound⟩ := quaternion_c2_rank_and_order U d hindex a ha hc2 V hV hVcard
  refine ⟨hcard,hrank.le,?_⟩
  intro E hET hEL hE
  let _ := hE
  have hEP : E ≤ T ⊓ L := le_inf hET hEL
  have hh := hbound (E.subgroupOf (T ⊓ L)) (IsElementaryAbelian.subgroupOf hEP)
  rwa [Nat.card_congr (subgroupOfEquivOfLe hEP).toEquiv] at hh

end CFSG.Quasithin.Chapter14.Section04.DimensionFour.NonsplitGeometry
