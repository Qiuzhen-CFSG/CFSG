module

public import Theory.GroupTheory.PGroup.OrderThirtyTwoCharacteristicBounds
public import Theory.GroupTheory.CharacteristicInvertedIndexTwo
public import Theory.GroupTheory.AbelianIndexTwoSurjectiveNorm
public import Theory.GroupTheory.C4SquareInvolutionBound

/-!
# An inverting involution for the characteristic order-sixteen base

For a characteristic abelian base of order sixteen, the elementary ambient
center is exactly the square-one subgroup of the base. In particular all
base squares are central. The outside norm has characteristic image in this
center, hence order one, two, or four. Order two is forbidden, while order
four would make all involutions form a characteristic elementary eight.
The norm is therefore trivial, which gives inversion. The common outside
square then generates a characteristic subgroup of order at most two, so
the hypotheses force every outside element to be an involution.

These are intrinsic reductions for Janko–Thompson, Math. Z. 113 (1970),
results 1.3–1.4, printed p.386. No bound on arbitrary elementary subgroups
and no classification of the possible automorphisms is used.
-/

open Subgroup

namespace OrderThirtyTwoCharacteristicInverter

private theorem center_le_base
    {G : Type*} [Group G] (A : Subgroup G) [IsMulCommutative A]
    (hi : A.index = 2) (hn : ¬ IsMulCommutative G) : center G ≤ A := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  have hcomm (a : G) (ha : a ∈ A) (b : G) (hb : b ∈ A) : Commute a b :=
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : A) ⟨b, hb⟩)
  intro t ht
  by_contra htA
  have hAZ : A ≤ center G := by
    intro a ha
    exact mem_center_of_commute_index_two A hi t htA a (hcomm a ha)
      (mem_center_iff.mp ht a)
  apply hn
  apply center_eq_top_iff.mp
  apply top_unique
  intro g _
  by_cases hg : g ∈ A
  · exact hAZ hg
  · have hgt : g * t⁻¹ ∈ A := (A.mul_mem_iff_of_index_two hi).mpr (by
      simp only [A.inv_mem_iff, hg, htA])
    simpa only [inv_mul_cancel_right] using (center G).mul_mem (hAZ hgt) ht

/-- The base has index two. -/
public theorem base_index {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 32) (A : Subgroup G) (hA : Nat.card A = 16) :
    A.index = 2 := by
  have h := A.card_mul_index
  rw [hcard, hA] at h
  omega

/-- The ambient center is exactly the square-one part of the characteristic base. -/
public theorem mem_center_iff_mem_base_and_sq_eq_one
    {G : Type*} [Group G] [Finite G] (hcard : Nat.card G = 32)
    (hcenter : 4 ≤ Nat.card (center G))
    (hchar : ∀ K : Subgroup G, K.Characteristic → Nat.card K ≠ 2)
    (helem : ∀ K : Subgroup G, K.Characteristic → IsElementaryAbelian 2 K → Nat.card K < 8)
    (A : Subgroup G) [A.Characteristic] [IsMulCommutative A]
    (hA : Nat.card A = 16) (x : G) :
    x ∈ center G ↔ x ∈ A ∧ x ^ 2 = 1 := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  have hZA := center_le_base A (base_index hcard A hA)
    (OrderThirtyTwoCharacteristicBounds.not_isMulCommutative hcard hchar helem)
  let : IsElementaryAbelian 2 (center G) :=
    OrderThirtyTwoCharacteristicBounds.center_elementary hcard hcenter hchar helem
  let f : A →* A := powMonoidHom 2
  have hle : (center G).subgroupOf A ≤ f.ker := by
    intro a ha
    exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (A := center G) (a : G) ha)
  have hcardZ : Nat.card ((center G).subgroupOf A) = 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZA).toEquiv]
    exact OrderThirtyTwoCharacteristicBounds.center_card hcard hcenter hchar helem
  have hker : Nat.card f.ker ≤ 4 :=
    card_le_four_of_c4_square_square_one
      (OrderThirtyTwoCharacteristicRecognition.base_recognition hchar helem A hA)
      f.ker (fun _ h => h)
  have heq : (center G).subgroupOf A = f.ker :=
    eq_of_le_of_card_ge hle (by omega)
  constructor
  · intro hx
    exact ⟨hZA hx, elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx⟩
  · rintro ⟨hxA, hx⟩
    have hk : (⟨x, hxA⟩ : A) ∈ f.ker := Subtype.ext hx
    rwa [← heq] at hk

/-- Every element of the base has fourth power one. -/
public theorem base_pow_four
    {G : Type*} [Group G] [Finite G]
    (hchar : ∀ K : Subgroup G, K.Characteristic → Nat.card K ≠ 2)
    (helem : ∀ K : Subgroup G, K.Characteristic → IsElementaryAbelian 2 K → Nat.card K < 8)
    (A : Subgroup G) [A.Characteristic] [IsMulCommutative A]
    (hA : Nat.card A = 16) (a : G) (ha : a ∈ A) : a ^ 4 = 1 := by
  obtain ⟨e⟩ := OrderThirtyTwoCharacteristicRecognition.base_recognition hchar helem A hA
  have hp : ∀ b : C4SquareSignSwap.Base, b ^ 4 = 1 := by decide
  have hh : (⟨a, ha⟩ : A) ^ 4 = 1 := e.injective (by
    rw [map_pow, map_one]
    exact hp _)
  exact congrArg Subtype.val hh

/-- Squares of base elements lie in the ambient center. -/
public theorem base_sq_mem_center
    {G : Type*} [Group G] [Finite G] (hcard : Nat.card G = 32)
    (hcenter : 4 ≤ Nat.card (center G))
    (hchar : ∀ K : Subgroup G, K.Characteristic → Nat.card K ≠ 2)
    (helem : ∀ K : Subgroup G, K.Characteristic → IsElementaryAbelian 2 K → Nat.card K < 8)
    (A : Subgroup G) [A.Characteristic] [IsMulCommutative A]
    (hA : Nat.card A = 16) (a : G) (ha : a ∈ A) : a ^ 2 ∈ center G := by
  apply (mem_center_iff_mem_base_and_sq_eq_one hcard hcenter hchar helem A hA _).mpr
  refine ⟨A.pow_mem ha 2, ?_⟩
  simpa only [← pow_mul] using base_pow_four hchar helem A hA a ha

/-- Once the outside action is inversion, the extension splits. -/
public theorem inverter_is_involution
    {G : Type*} [Group G] [Finite G] (hcard : Nat.card G = 32)
    (hchar : ∀ K : Subgroup G, K.Characteristic → Nat.card K ≠ 2)
    (A : Subgroup G) [A.Characteristic] (hA : Nat.card A = 16)
    (t : G) (ht : t ∉ A) (hinv : ∀ a ∈ A, t * a * t⁻¹ = a⁻¹) :
    t ^ 2 = 1 :=
  sq_eq_one_of_characteristic_inverted_index_two hchar A (base_index hcard A hA) t ht hinv

private theorem norm_range_le_center
    {G : Type*} [Group G] [Finite G] (hcard : Nat.card G = 32)
    (hcenter : 4 ≤ Nat.card (center G))
    (hchar : ∀ K : Subgroup G, K.Characteristic → Nat.card K ≠ 2)
    (helem : ∀ K : Subgroup G, K.Characteristic → IsElementaryAbelian 2 K → Nat.card K < 8)
    (A : Subgroup G) [A.Characteristic] [IsMulCommutative A]
    (hA : Nat.card A = 16) (t : G) : (abelianConjNorm A t).range ≤ center G := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  rintro _ ⟨a, rfl⟩
  have hconj : t * (a : G) * t⁻¹ ∈ A :=
    (inferInstance : A.Normal).conj_mem a a.property t
  apply (mem_center_iff_mem_base_and_sq_eq_one hcard hcenter hchar helem A hA _).mpr
  refine ⟨A.mul_mem a.property hconj, ?_⟩
  have hcomm : Commute (a : G) (t * a * t⁻¹) :=
    congrArg Subtype.val (mul_comm a (⟨t * a * t⁻¹, hconj⟩ : A))
  have hsquare : (t * (a : G) * t⁻¹) ^ 2 = (a : G) ^ 2 := by
    calc
      _ = t * (a : G) ^ 2 * t⁻¹ := (map_pow (MulAut.conj t) (a : G) 2).symm
      _ = (a : G) ^ 2 := (show Commute t ((a : G) ^ 2) from
        mem_center_iff.mp (base_sq_mem_center hcard hcenter hchar helem A hA a a.property) t
        ).mul_inv_cancel
  rw [abelianConjNorm_apply, hcomm.mul_pow, hsquare, ← pow_two, ← pow_mul]
  exact base_pow_four hchar helem A hA a a.property

/-- Every element outside the characteristic order-sixteen base acts by inversion. -/
public theorem outside_inverts
    {G : Type*} [Group G] [Finite G] (hcard : Nat.card G = 32)
    (hcenter : 4 ≤ Nat.card (center G))
    (hchar : ∀ K : Subgroup G, K.Characteristic → Nat.card K ≠ 2)
    (helem : ∀ K : Subgroup G, K.Characteristic → IsElementaryAbelian 2 K → Nat.card K < 8)
    (A : Subgroup G) [A.Characteristic] [IsMulCommutative A]
    (hA : Nat.card A = 16) (t : G) (ht : t ∉ A) :
    ∀ a ∈ A, t * a * t⁻¹ = a⁻¹ := by
  let n := abelianConjNorm A t
  have hnchar : n.range.Characteristic :=
    abelianConjNorm_range_characteristic A (base_index hcard A hA) t ht
  have hle : n.range ≤ center G := norm_range_le_center hcard hcenter hchar helem A hA t
  have hZ := OrderThirtyTwoCharacteristicBounds.center_card hcard hcenter hchar helem
  have hdiv : Nat.card n.range ∣ 2 ^ 2 := by
    simpa only [hZ, Nat.reducePow] using card_dvd_of_le hle
  have hnotfour : Nat.card n.range ≠ 4 := by
    intro hfour
    have heq : n.range = center G := eq_of_le_of_card_ge hle (by omega)
    obtain ⟨K, hKchar, hKelem, hKcard⟩ :=
      exists_characteristic_elementary_of_surjective_abelian_norm A
        (base_index hcard A hA) hA hZ
        (mem_center_iff_mem_base_and_sq_eq_one hcard hcenter hchar helem A hA) t ht heq
    have := helem K hKchar hKelem
    omega
  have hone : Nat.card n.range = 1 := by
    obtain ⟨k, hk, heq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
    have hnotTwo := hchar n.range hnchar
    interval_cases k
    · simpa only [pow_zero] using heq
    · exact (hnotTwo (by simpa only [pow_one] using heq)).elim
    · exact (hnotfour (by simpa only [Nat.reducePow] using heq)).elim
  have hbot : n.range = ⊥ := n.range.eq_bot_of_card_eq hone
  intro a ha
  have hmem : n ⟨a, ha⟩ ∈ n.range := ⟨⟨a, ha⟩, rfl⟩
  rw [hbot, mem_bot] at hmem
  exact eq_inv_of_mul_eq_one_right hmem

/-- The characteristic abelian order-sixteen base admits an outside inverting involution. -/
public theorem exists_inverting_involution
    {G : Type*} [Group G] [Finite G] (hcard : Nat.card G = 32)
    (hcenter : 4 ≤ Nat.card (center G))
    (hchar : ∀ K : Subgroup G, K.Characteristic → Nat.card K ≠ 2)
    (helem : ∀ K : Subgroup G, K.Characteristic → IsElementaryAbelian 2 K → Nat.card K < 8)
    (A : Subgroup G) [A.Characteristic] [IsMulCommutative A]
    (hA : Nat.card A = 16) :
    ∃ t : G, t ∉ A ∧ t ^ 2 = 1 ∧ ∀ a ∈ A, t * a * t⁻¹ = a⁻¹ := by
  obtain ⟨t, ht, _⟩ := A.index_eq_two_iff_exists_notMem_and.mp (base_index hcard A hA)
  have hinv := outside_inverts hcard hcenter hchar helem A hA t ht
  exact ⟨t, ht, inverter_is_involution hcard hchar A hA t ht hinv, hinv⟩

end OrderThirtyTwoCharacteristicInverter
