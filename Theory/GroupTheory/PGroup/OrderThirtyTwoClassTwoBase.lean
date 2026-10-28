module

public import Theory.GroupTheory.PGroup.OrderThirtyTwoCharacteristicBounds
public import Theory.GroupTheory.Commutator.CentralFourSurjectivity
public import Theory.GroupTheory.PGroup.ExtraspecialAbelianIndexTwo
public import Theory.GroupTheory.IndexTwoIntersection

/-!
# The characteristic abelian base in the class-two order-thirty-two case

A group of order thirty-two with central commutators and elementary center
of order four has a characteristic abelian subgroup of order sixteen.

If no noncentral element has centralizer of order sixteen, every noncentral
commutator homomorphism surjects onto the center. Quotienting by a central
involution then gives an extraspecial group of order sixteen. This is
impossible by the elementary commutator-kernel bound for abelian subgroups
of index two: a noncentral element of that quotient would have an abelian
centralizer of order eight. No classification of small groups is used.

A centralizer of order sixteen is abelian because its own center is larger
than the ambient center. Finally, two distinct abelian subgroups of order
sixteen would have a central intersection of order eight. Thus the abelian
base is unique and consequently characteristic.

The final wrapper obtains the center conditions from the characteristic
subgroup bounds. Its exponent-four hypothesis is retained for the intended
interface; the stronger structural theorem does not require it.

Source context: Janko–Thompson, Math. Z. 113 (1970), results 1.3–1.4,
printed p.386. The proof uses the project's central commutator homomorphism
and extraspecial index-two commutator-kernel estimate.
-/

open Subgroup
open scoped commutatorElement IsMulCommutative

namespace OrderThirtyTwoClassTwoBase

private theorem commutative_of_large_center
    {H : Type*} [Group H] [Finite H]
    (h : Nat.card H < 4 * Nat.card (center H)) : IsMulCommutative H := by
  have hp := (center H).index_ne_zero_of_finite
  have hm := (center H).card_mul_index
  have hc := Nat.card_pos (α := center H)
  have hi : (center H).index < 4 := by nlinarith
  have hh : (center H).index = 1 ∨ (center H).index = 2 ∨ (center H).index = 3 := by omega
  rcases hh with hh | hh | hh
  · exact center_eq_top_iff.mp (index_eq_one.mp hh)
  · let : IsCyclic (H ⧸ center H) := isCyclic_of_prime_card (p := 2) hh
    exact isMulCommutative_of_isCyclic_quotient_center_self H
  · let : Fact (Nat.Prime 3) := ⟨by decide⟩
    let : IsCyclic (H ⧸ center H) := isCyclic_of_prime_card (p := 3) hh
    exact isMulCommutative_of_isCyclic_quotient_center_self H

private theorem center_centralizer_card_gt
    {H : Type*} [Group H] [Finite H] (x : H) (hx : x ∉ center H) :
    Nat.card (center H) < Nat.card (center (centralizer ({x} : Set H))) := by
  let C := centralizer ({x} : Set H)
  have hZ : center H ≤ C := center_le_centralizer _
  have hle : (center H).subgroupOf C ≤ center C := by
    intro z hz
    apply mem_center_iff.mpr
    intro c
    apply Subtype.ext
    exact mem_center_iff.mp hz c
  have hc : Nat.card ((center H).subgroupOf C) = Nat.card (center H) :=
    Nat.card_congr (subgroupOfEquivOfLe hZ).toEquiv
  by_contra! hn
  change Nat.card (center C) ≤ Nat.card (center H) at hn
  have he := eq_of_le_of_card_ge hle (by omega)
  have hxc : (⟨x, mem_centralizer_singleton_iff.mpr rfl⟩ : C) ∈ center C := by
    apply mem_center_iff.mpr
    intro c
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp c.property
  rw [← he] at hxc
  exact hx hxc

private theorem centralizer_ne_top
    {H : Type*} [Group H] {x : H} (hx : x ∉ center H) :
    centralizer ({x} : Set H) ≠ ⊤ := by
  intro he
  exact hx (centralizer_eq_top_iff_subset.mp he (Set.mem_singleton x))

private theorem extraspecial_card_ne_sixteen
    {H : Type*} [Group H] [Finite H] [IsExtraspecial 2 H] : Nat.card H ≠ 16 := by
  intro hcard
  have hZ := IsExtraspecial.center_order_p 2 H
  have hclass := (IsExtraspecial.quotient_elementary_abelian 2 H).commutator_le_center_of_central_quotient
  obtain ⟨x, hx⟩ : ∃ x : H, x ∉ center H := by
    by_contra! hn
    have ht : center H = ⊤ := top_unique (fun x _ => hn x)
    rw [ht, card_top, hcard] at hZ
    omega
  let C := centralizer ({x} : Set H)
  let f := centerCommutatorHom hclass x
  have hfker : f.ker = C := centerCommutatorHom_ker hclass x
  have hrle : Nat.card f.range ≤ 2 := by
    simpa only [hZ] using Nat.card_le_card_of_injective f.range.subtype f.range.subtype_injective
  have hri : C.index ≤ 2 := by
    rw [← hfker, index_ker]
    exact hrle
  have hip : 1 < C.index := one_lt_index_of_ne_top (centralizer_ne_top hx)
  have hi : C.index = 2 := by omega
  have hC : Nat.card C = 8 := by
    have hh := C.card_mul_index
    rw [hi, hcard] at hh
    omega
  have hc := center_centralizer_card_gt x hx
  change Nat.card (center H) < Nat.card (center C) at hc
  have hab : IsMulCommutative C := commutative_of_large_center (by rw [hC]; omega)
  exact IsExtraspecial.not_isMulCommutative_of_index_two (by omega) C hi
    (center_le_centralizer _) hab

private theorem square_mem_center
    {G : Type*} [Group G] (hclass : commutator G ≤ center G)
    [IsElementaryAbelian 2 (center G)] (x : G) : x ^ 2 ∈ center G := by
  apply mem_center_iff.mpr
  intro y
  apply Eq.symm
  apply commutatorElement_eq_one_iff_mul_comm.mp
  have hc : ⁅x,y⁆ ∈ center G :=
    hclass (commutator_mem_commutator (mem_top x) (mem_top y))
  rw [pow_two, commutatorElement_mul_left_eq_conj_mul,
    mem_center_iff.mp hc x, mul_inv_cancel_right, ← pow_two,
    elemPow_eq_one_of_isElementaryAbelian _ hc]

private theorem exists_centralizer_sixteen
    {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 32) (hZ : Nat.card (center G) = 4)
    (hclass : commutator G ≤ center G) [IsElementaryAbelian 2 (center G)] :
    ∃ x : G, x ∉ center G ∧ Nat.card (centralizer ({x} : Set G)) = 16 := by
  classical
  by_contra! hn
  have hsurj (x : G) (hx : x ∉ center G) :
      Function.Surjective (centerCommutatorHom hclass x) := by
    let f := centerCommutatorHom hclass x
    have hp := f.ker.card_mul_index
    rw [index_ker, centerCommutatorHom_ker, hcard] at hp
    change Nat.card (centralizer ({x} : Set G)) * Nat.card f.range = 32 at hp
    have hd : Nat.card f.range ∣ 2 ^ 2 := by
      simpa [hZ] using f.range.card_subgroup_dvd_card
    obtain ⟨n, hnle, hneq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    have hr : Nat.card f.range = Nat.card (center G) := by
      interval_cases n
      · norm_num only [pow_zero, pow_one] at hneq
        rw [hneq] at hp
        have hC : Nat.card (centralizer ({x} : Set G)) = Nat.card G := by omega
        exact (centralizer_ne_top hx (eq_top_of_card_eq _ hC)).elim
      · norm_num only [pow_zero, pow_one] at hneq
        rw [hneq] at hp
        exact (hn x hx (by omega)).elim
      · simpa [hZ] using hneq
    exact f.range_eq_top.mp (f.range.eq_top_of_card_eq hr)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center G) 2
    (show 2 ∣ Nat.card (center G) by rw [hZ]; decide)
  let N := zpowers (z : G)
  have hNZ : N ≤ center G := zpowers_le.mpr z.property
  let : N.Normal := ⟨fun n hn g => by
    rw [mem_center_iff.mp (hNZ hn) g, mul_inv_cancel_right]
    exact hn⟩
  have hNcard : Nat.card N = 2 := by
    rw [Nat.card_zpowers, orderOf_coe, hz]
  let q := QuotientGroup.mk' N
  have hquot : Nat.card (G ⧸ N) = 16 := by
    have hh := N.index_mul_card
    rw [hNcard, hcard] at hh
    change Nat.card (G ⧸ N) * 2 = 32 at hh
    omega
  have hZmap : center (G ⧸ N) = (center G).map q := by
    apply le_antisymm
    · intro a ha
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N a
      have hx : x ∈ center G := by
        by_contra hx
        have hle : center G ≤ N := by
          intro c hc
          obtain ⟨y, hy⟩ := hsurj x hx ⟨c, hc⟩
          have hcomm : q ⁅x,y⁆ = 1 := by
            rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
            exact (mem_center_iff.mp ha (q y)).symm
          have hmem : ⁅x,y⁆ ∈ N := (QuotientGroup.eq_one_iff _).mp hcomm
          have heq : ⁅x,y⁆ = c := congrArg Subtype.val hy
          exact heq ▸ hmem
        have hb := card_le_of_le hle
        omega
      exact mem_map_of_mem q hx
    · rintro _ ⟨x, hx, rfl⟩
      apply mem_center_iff.mpr
      intro y
      obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective N y
      simpa only [map_mul] using congrArg q (mem_center_iff.mp hx t)
  have hZquot : Nat.card (center (G ⧸ N)) = 2 := by
    have hk : Nat.card (N.subgroupOf (center G)) = 2 :=
      (Nat.card_congr (subgroupOfEquivOfLe hNZ).toEquiv).trans hNcard
    have hh := (N.subgroupOf (center G)).index_mul_card
    change N.relIndex (center G) * Nat.card (N.subgroupOf (center G)) = _ at hh
    have hr : N.relIndex (center G) = Nat.card ((center G).map q) := by
      simpa only [q, QuotientGroup.ker_mk'] using relIndex_ker (center G) q
    rw [hk, hr, hZ, ← hZmap] at hh
    omega
  have hquotel : IsElementaryAbelian 2 ((G ⧸ N) ⧸ center (G ⧸ N)) := by
    refine {
      toIsMulCommutative := Normal.quotient_commutative_iff_commutator_le.mpr ?_
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one ?_ }
    · have hmap : (commutator G).map q = commutator (G ⧸ N) := by
        rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)]
        rfl
      rw [← hmap, hZmap]
      exact map_mono hclass
    · intro a
      induction a using QuotientGroup.induction_on with
      | H a =>
        induction a using QuotientGroup.induction_on with
        | H x =>
          apply (QuotientGroup.eq_one_iff _).mpr
          rw [hZmap]
          exact mem_map_of_mem q (square_mem_center hclass x)
  let : IsExtraspecial 2 (G ⧸ N) := {
    center_order_p := hZquot
    quotient_elementary_abelian := hquotel
    quotient_nontrivial := QuotientGroup.nontrivial_iff.mpr (by
      intro heq
      have hh : Nat.card (center (G ⧸ N)) = Nat.card (G ⧸ N) := by rw [heq, card_top]
      omega) }
  exact extraspecial_card_ne_sixteen hquot

private theorem abelian_sixteen_unique
    {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 32) (hZ : Nat.card (center G) = 4)
    (A B : Subgroup G) [IsMulCommutative A] [IsMulCommutative B]
    (hA : Nat.card A = 16) (hB : Nat.card B = 16) : B = A := by
  have hi : A.index = 2 := by
    have hh := A.card_mul_index
    rw [hA, hcard] at hh
    omega
  apply eq_of_le_of_card_ge _ (by omega)
  by_contra hn
  obtain ⟨b, hbB, hbA⟩ := SetLike.not_le_iff_exists.mp hn
  have hc : Nat.card (A.subgroupOf B) = 8 := by
    have hh := (A.subgroupOf B).card_mul_index
    rw [subgroupOf_index_eq_two A B hi hn, hB] at hh
    omega
  have hle : (A.subgroupOf B).map B.subtype ≤ center G := by
    rintro _ ⟨z, hz, rfl⟩
    apply mem_center_iff.mpr
    intro g
    have hcommA (a : G) (ha : a ∈ A) : a * z = z * a :=
      congrArg Subtype.val (mul_comm (⟨a, ha⟩ : A) ⟨z, hz⟩)
    have hcommB : b * z = z * b :=
      congrArg Subtype.val (mul_comm (⟨b, hbB⟩ : B) z)
    by_cases hg : g ∈ A
    · exact hcommA g hg
    · have hgb : g * b⁻¹ ∈ A := (A.mul_mem_iff_of_index_two hi).mpr (by
        simpa only [A.inv_mem_iff] using (iff_of_false hg hbA))
      calc
        g * z = (g * b⁻¹) * (b * z) := by group
        _ = (g * b⁻¹) * (z * b) := by rw [hcommB]
        _ = z * ((g * b⁻¹) * b) := by rw [← mul_assoc, hcommA _ hgb, mul_assoc]
        _ = z * g := by group
  have hh := card_le_of_le hle
  rw [card_map_of_injective B.subtype_injective, hc, hZ] at hh
  omega

/-- A class-two group of order thirty-two with elementary center of order four
has a characteristic abelian subgroup of order sixteen. -/
public theorem exists_characteristic_abelian_of_center_four
    {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 32) (hZ : Nat.card (center G) = 4)
    (hclass : commutator G ≤ center G) [IsElementaryAbelian 2 (center G)] :
    ∃ A : Subgroup G, A.Characteristic ∧ IsMulCommutative A ∧ Nat.card A = 16 := by
  obtain ⟨x, hx, hC⟩ := exists_centralizer_sixteen hcard hZ hclass
  let C := centralizer ({x} : Set G)
  have hzC := center_centralizer_card_gt x hx
  change Nat.card (center G) < Nat.card (center C) at hzC
  change Nat.card C = 16 at hC
  let : IsMulCommutative C := commutative_of_large_center (by rw [hC]; omega)
  refine ⟨C, ?_, inferInstance, hC⟩
  apply characteristic_iff_map_eq.mpr
  intro φ
  apply abelian_sixteen_unique hcard hZ C (C.map φ.toMonoidHom) hC
  rw [card_map_of_injective φ.injective, hC]

/-- The characteristic bounds provide the elementary center needed for the
class-two construction. -/
public theorem exists_characteristic_abelian_sixteen
    {G : Type*} [Group G] [Finite G] (hcard : Nat.card G = 32)
    (hcenter : 4 ≤ Nat.card (center G))
    (hchar : ∀ K : Subgroup G, K.Characteristic → Nat.card K ≠ 2)
    (helem : ∀ K : Subgroup G, K.Characteristic → IsElementaryAbelian 2 K → Nat.card K < 8)
    (hclass : commutator G ≤ center G) (_hexp : ∀ x : G, x ^ 4 = 1) :
    ∃ A : Subgroup G, A.Characteristic ∧ IsMulCommutative A ∧ Nat.card A = 16 := by
  let : IsElementaryAbelian 2 (center G) :=
    OrderThirtyTwoCharacteristicBounds.center_elementary hcard hcenter hchar helem
  exact exists_characteristic_abelian_of_center_four hcard
    (OrderThirtyTwoCharacteristicBounds.center_card hcard hcenter hchar helem) hclass

end OrderThirtyTwoClassTwoBase
