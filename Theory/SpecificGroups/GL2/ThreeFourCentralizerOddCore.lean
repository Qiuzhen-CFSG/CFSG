module
public import Theory.PPrimeCore
public import Theory.SpecificGroups.GL2.ThreeFourCentralizer
public import Theory.GroupTheory.SelfCentralizingImage
public import Theory.GroupTheory.CoprimeQuotientSubgroups
/-!
# Four-group centralizers with a GL₂(3) odd-core quotient

Let T be a four-group containing x, and put N = C_G(x). If N/O₂′(N) is
GL₂(3), then |C_G(T)| = 4 |C_G(T) ∩ O₂′(N)|. Inject T through the odd
kernel; its image is self-centralizing by the explicit GL₂(3) calculation.
The kernel–image formula counts exactly the centralizing part of the kernel.
No centralization assumption on the whole odd core is needed.

Source: the local count in Alperin–Brauer–Gorenstein, III.2 Proposition 6
and III.8 Proposition 5, article pp.68 and 117.
-/

namespace Subgroup
open Subgroup Matrix
/-- A four-group centralizer has order four times its intersection with the
odd core of an involution centralizer whose odd-core quotient is GL₂(3). -/
public theorem fourCentralizer_card_intersection_of_oddCoreQuotient
    {G : Type*} [Group G] [Finite G]
    (x : G)
    (T : Subgroup G) [IsElementaryAbelian 2 T] (hT : Nat.card T = 4) (hxT : x ∈ T)
    (ee : (Subgroup.centralizer ({x} : Set G) ⧸
      pPrimeCore 2 (Subgroup.centralizer ({x} : Set G))) ≃* GL (Fin 2) (ZMod 3)) :
    Nat.card (centralizer (T : Set G)) =
      4 * Nat.card ((centralizer (T : Set G)).subgroupOf
        ((pPrimeCore 2 (centralizer ({x} : Set G))).map
          (centralizer ({x} : Set G)).subtype)) := by
  let N := centralizer ({x} : Set G)
  let O := pPrimeCore 2 N
  let A := T.subgroupOf N
  have hCN : centralizer (T : Set G) ≤ N :=
    centralizer_le (Set.singleton_subset_iff.mpr hxT)
  have hTN : T ≤ N := T.le_centralizer.trans hCN
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hTN
  have hA : Nat.card A = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hTN).toEquiv).trans hT
  let f : N →* GL (Fin 2) (ZMod 3) :=
    ee.toMonoidHom.comp (QuotientGroup.mk' O)
  have hfker : f.ker = O := by
    ext a
    change ee (QuotientGroup.mk' O a) = 1 ↔ a ∈ O
    rw [← ee.map_one, ee.injective.eq_iff]
    exact QuotientGroup.eq_one_iff a
  have hfodd : Nat.Coprime 2 (Nat.card f.ker) := by
    rw [hfker]
    exact pPrimeCore_coprime_card
  have hinj : Function.Injective (f.comp A.subtype) :=
    injective_comp_subtype_of_coprime_ker f hfodd A (IsElementaryAbelian.isPGroup 2 A)
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  have hAf : Nat.card (A.map f) = 4 := by
    rw [← hA]
    apply Nat.card_image_of_injOn
    intro a ha b hb hab
    exact congrArg Subtype.val (hinj (show f.comp A.subtype ⟨a, ha⟩ =
      f.comp A.subtype ⟨b, hb⟩ from hab))
  have hc := card_centralizer_of_selfCentralizing_image_intersection f A hinj
    (Matrix.GeneralLinearGroup.three_four_centralizer (A.map f) hAf)
  rw [hA, hfker] at hc
  have heq : centralizer (A : Set N) = (centralizer (T : Set G)).subgroupOf N := by
    ext a
    constructor
    · intro ha b hb
      exact congrArg Subtype.val (ha ⟨b, hTN hb⟩ hb)
    · intro ha b hb
      exact Subtype.ext (ha b hb)
  let K := O.map N.subtype
  have hmem (a : N) : (a : G) ∈ K ↔ a ∈ O := by
    exact mem_map_iff_mem (f := N.subtype) N.subtype_injective
  have hcard : Nat.card (O.subgroupOf (centralizer (A : Set N))) =
      Nat.card ((centralizer (T : Set G)).subgroupOf K) := by
    apply Nat.card_congr
    exact {
      toFun := fun a => ⟨⟨a.val.val.val, (hmem a.val.val).mpr a.property⟩,
        heq.le a.val.property⟩
      invFun := fun a => ⟨⟨⟨a.val.val, hCN a.property⟩, by
        rw [heq]
        exact a.property⟩, (hmem _).mp a.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [hcard, heq, Nat.card_congr (subgroupOfEquivOfLe hCN).toEquiv] at hc
  exact hc

end Subgroup
