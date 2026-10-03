module

public import Theory.SpecificGroups.C4SquareInverterRecognition
public import Theory.GroupTheory.NormalSixteenC4SquareRecognition
public import Theory.ElementaryAbelian.Basic

/-!
# Characteristic-subgroup reductions for order-thirty-two recognition

A characteristic abelian subgroup of order sixteen in a group with no
characteristic subgroup of order two and no characteristic elementary eight
is C₄ × C₄. Characteristic subgroups of this base remain characteristic in
the ambient group. The elementary bound forces an element of order four,
and the order-sixteen recognition theorem determines the base.

An outside involution inverting this base then gives the explicit inverter
core. The existence of the characteristic abelian base and of that involution
are separate structural inputs to the assembly below.

Source context: Janko–Thompson, Math. Z. 113 (1970), results 1.3–1.4,
printed p.386. No small-group classification is assumed here.
-/

namespace OrderThirtyTwoCharacteristicRecognition

open C4SquareSignSwap


/-- The characteristic abelian order-sixteen base is C₄ × C₄. -/
public theorem base_recognition {G : Type*} [Group G] [Finite G]
    (hchar : ∀ K : Subgroup G, K.Characteristic → Nat.card K ≠ 2)
    (helem : ∀ K : Subgroup G, K.Characteristic → IsElementaryAbelian 2 K → Nat.card K < 8)
    (A : Subgroup G) [A.Characteristic] [IsMulCommutative A]
    (hA : Nat.card A = 16) : Nonempty (A ≃* Base) := by
  apply NormalSixteenC4Square.recognition_of_no_characteristic_two hA
  · intro K hK
    let : K.Characteristic := hK
    have h := hchar (K.map A.subtype) inferInstance
    rwa [Subgroup.card_map_of_injective A.subtype_injective] at h
  · by_contra hn
    have hp (x : A) : x ^ 2 = 1 := by
      have hd : orderOf x ∣ 2 ^ 4 := by
        simpa [hA] using orderOf_dvd_natCard x
      obtain ⟨k, hk, heq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
      have hsmall : k < 2 := by
        by_contra hnsmall
        have hd4 : 4 ∣ orderOf x := by
          rw [heq]
          exact Nat.pow_dvd_pow 2 (by omega : 2 ≤ k)
        exact hn ⟨x ^ (orderOf x / 4), orderOf_pow_orderOf_div (orderOf_pos x).ne' hd4⟩
      apply orderOf_dvd_iff_pow_eq_one.mp
      rw [heq]
      interval_cases k <;> norm_num
    let : IsElementaryAbelian 2 A := ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp⟩
    have := helem A inferInstance inferInstance
    omega

/-- Recognition once the characteristic abelian base and its involutive
inverter have been constructed. -/
public theorem recognition_of_characteristic_base_and_inverter
    {G : Type*} [Group G] [Finite G] (hcard : Nat.card G = 32)
    (hchar : ∀ K : Subgroup G, K.Characteristic → Nat.card K ≠ 2)
    (helem : ∀ K : Subgroup G, K.Characteristic → IsElementaryAbelian 2 K → Nat.card K < 8)
    (A : Subgroup G) [A.Characteristic] [IsMulCommutative A]
    (hA : Nat.card A = 16) (t : G) (htA : t ∉ A) (ht : t ^ 2 = 1)
    (hinv : ∀ a ∈ A, t * a * t⁻¹ = a⁻¹) :
    Nonempty (G ≃* inverterCore) := by
  obtain ⟨e⟩ := base_recognition hchar helem A hA
  have hi : A.index = 2 := by
    have h := A.card_mul_index
    rw [hcard, hA] at h
    omega
  exact recognition_of_inverted_base hcard A hi e t htA ht hinv

end OrderThirtyTwoCharacteristicRecognition
