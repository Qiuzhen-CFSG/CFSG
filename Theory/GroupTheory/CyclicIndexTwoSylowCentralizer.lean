module
public import Theory.GroupTheory.CyclicIndexTwoElementary
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# Odd centralizers under cyclic-index-two Sylow geometry

Let a finite group have a Sylow two-subgroup with a cyclic subgroup of
index two. Any centerless subgroup containing a Klein four subgroup has
odd-order centralizer. No normality of the centerless subgroup is needed.

A centralizing involution supplies an order-two subgroup disjoint from the
centerless subgroup. Its commuting product with the actual Klein four
subgroup is an injective image of a product of order eight and exponent
two. Inclusion in a Sylow subgroup contradicts the elementary order bound
for cyclic-index-two groups. The proof uses the actual product and Sylow
maps, rather than assuming a rank bound.

This is the local faithfulness argument for the prescribed normal PSL2
core in Alperin--Brauer--Gorenstein II.3, Proposition 4, article page 29.
-/

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

public theorem centralizer_card_coprime_two_of_centerless_of_cyclic_sylow_index_two
    (S : Sylow 2 G) (A : Subgroup S) [IsCyclic A] (hA : A.index = 2)
    (H : Subgroup G) (hZ : Subgroup.center H = ⊥)
    (V : Subgroup H) (hV : IsKleinFour V) :
    Nat.Coprime 2 (Nat.card (centralizer (H : Set G))) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsKleinFour V := hV
  rw [Nat.prime_two.coprime_iff_not_dvd]
  intro hd
  let C := centralizer (H : Set G)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 hd
  let T := zpowers (t : G)
  have hTle : T ≤ C := zpowers_le.mpr t.property
  have hTc : Nat.card T = 2 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe t, ht]
  have hTp : ∀ x : T, x ^ 2 = 1 := by
    intro x
    apply Subtype.ext
    have hx := orderOf_dvd_of_mem_zpowers x.property
    rw [Subgroup.orderOf_coe t, ht] at hx
    exact orderOf_dvd_iff_pow_eq_one.mp hx
  let i : V →* G := H.subtype.comp V.subtype
  have hic : ∀ v : V, (i v) ∈ H := fun v => v.val.property
  have hcomm : ∀ (v : V) (x : T), Commute (i v) (x : G) := by
    intro v x
    exact mem_centralizer_iff.mp (hTle x.property) (i v) (hic v)
  let f : V × T →* G := i.noncommCoprod T.subtype hcomm
  have hdisj : Disjoint i.range T.subtype.range := by
    rw [disjoint_iff_inf_le]
    rintro g ⟨⟨v, rfl⟩, x, hx⟩
    have hcent : (⟨i v, hic v⟩ : H) ∈ Subgroup.center H := by
      rw [mem_center_iff]
      intro h
      apply Subtype.ext
      have hv : i v ∈ C := hx ▸ hTle x.property
      exact mem_centralizer_iff.mp hv h h.property
    rw [hZ] at hcent
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hcent)
  have hf : Function.Injective f :=
    (MonoidHom.noncommCoprod_injective i T.subtype hcomm).mpr
      ⟨H.subtype_injective.comp V.subtype_injective, T.subtype_injective, hdisj⟩
  let eR : V × T ≃* f.range := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun _ _ h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  have hRc : Nat.card f.range = 8 := by
    rw [← Nat.card_congr eR.toEquiv, Nat.card_prod, hV.card_four, hTc]
  have hRp : ∀ x : f.range, x ^ 2 = 1 := by
    intro x
    obtain ⟨y, rfl⟩ := eR.surjective x
    rw [← map_pow]
    have hy : y ^ 2 = 1 := by
      apply Prod.ext
      · change y.1 ^ 2 = 1
        simpa only [pow_two] using IsKleinFour.mul_self y.1
      · exact hTp y.2
    rw [hy, map_one]
  have hRtwo : IsPGroup 2 f.range := IsPGroup.of_card (by simpa using hRc : Nat.card f.range = 2 ^ 3)
  obtain ⟨Q, hRQ⟩ := IsPGroup.exists_le_sylow hRtwo
  let eS : S ≃* Q := Sylow.equiv S Q
  let B : Subgroup Q := A.map eS.toMonoidHom
  let : IsCyclic B := (eS.subgroupMap A).isCyclic.mp inferInstance
  have hBi : B.index = 2 := by
    rw [Subgroup.index_map_of_bijective eS.bijective]
    exact hA
  let E : Subgroup Q := f.range.subgroupOf Q
  let eE : E ≃* f.range := subgroupOfEquivOfLe hRQ
  have hEp : ∀ x : E, x ^ 2 = 1 := by
    intro x
    apply eE.injective
    simpa only [map_pow, map_one] using hRp (eE x)
  have hbound := card_le_four_of_pow_two_of_cyclic_index_two B hBi E hEp
  rw [Nat.card_congr eE.toEquiv, hRc] at hbound
  omega

end Subgroup
