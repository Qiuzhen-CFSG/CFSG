module

public import Theory.GroupTheory.PGroup.OrderThirtyTwoClassTwoBase
public import Theory.GroupTheory.PGroup.OrderThirtyTwoCharacteristicInverter

/-!
# Characteristic base and inverter in a group of order thirty-two

A group of order thirty-two with center of order at least four, no
characteristic subgroup of order two, and no characteristic elementary
abelian 2-subgroup of order at least eight has a characteristic abelian
subgroup of order sixteen and an outside involution acting on it by inversion.
Consequently it is isomorphic to the explicit C₄ × C₄ inverter core.

The characteristic-subgroup bounds reduce base existence to the class-two
case, where the centralizer construction supplies the base. The characteristic
norm argument then supplies the inverter, and the base recognition theorem
identifies the resulting extension. Every structural input is discharged here.

Source context: Janko–Thompson, Math. Z. 113 (1970), results 1.3–1.4,
printed p.386. The proof uses intrinsic finite-group arguments.
-/

namespace OrderThirtyTwoCharacteristicExtraction

/-- The characteristic subgroup constraints force an abelian base of order sixteen. -/
public theorem exists_characteristic_abelian_sixteen
    {G : Type*} [Group G] [Finite G] (hcard : Nat.card G = 32)
    (hcenter : 4 ≤ Nat.card (Subgroup.center G))
    (hchar : ∀ K : Subgroup G, K.Characteristic → Nat.card K ≠ 2)
    (helem : ∀ K : Subgroup G, K.Characteristic → IsElementaryAbelian 2 K → Nat.card K < 8) :
    ∃ A : Subgroup G, A.Characteristic ∧ IsMulCommutative A ∧ Nat.card A = 16 := by
  rcases OrderThirtyTwoCharacteristicBounds.base_or_class_two hcard hcenter hchar helem with
    hbase | ⟨hclass, hexp⟩
  · exact hbase
  · exact OrderThirtyTwoClassTwoBase.exists_characteristic_abelian_sixteen
      hcard hcenter hchar helem hclass hexp

/-- The characteristic abelian base admits an outside involution acting by inversion. -/
public theorem exists_characteristic_base_and_inverter
    {G : Type*} [Group G] [Finite G] (hcard : Nat.card G = 32)
    (hcenter : 4 ≤ Nat.card (Subgroup.center G))
    (hchar : ∀ K : Subgroup G, K.Characteristic → Nat.card K ≠ 2)
    (helem : ∀ K : Subgroup G, K.Characteristic → IsElementaryAbelian 2 K → Nat.card K < 8) :
    ∃ A : Subgroup G, A.Characteristic ∧ IsMulCommutative A ∧ Nat.card A = 16 ∧
      ∃ t : G, t ∉ A ∧ t ^ 2 = 1 ∧ ∀ a ∈ A, t * a * t⁻¹ = a⁻¹ := by
  obtain ⟨A, hAchar, hAcomm, hA⟩ :=
    exists_characteristic_abelian_sixteen hcard hcenter hchar helem
  let : A.Characteristic := hAchar
  let : IsMulCommutative A := hAcomm
  exact ⟨A, hAchar, hAcomm, hA,
    OrderThirtyTwoCharacteristicInverter.exists_inverting_involution
      hcard hcenter hchar helem A hA⟩

/-- Recognition from the original characteristic subgroup constraints alone. -/
public theorem recognition
    {G : Type*} [Group G] [Finite G] (hcard : Nat.card G = 32)
    (hcenter : 4 ≤ Nat.card (Subgroup.center G))
    (hchar : ∀ K : Subgroup G, K.Characteristic → Nat.card K ≠ 2)
    (helem : ∀ K : Subgroup G, K.Characteristic → IsElementaryAbelian 2 K → Nat.card K < 8) :
    Nonempty (G ≃* C4SquareSignSwap.inverterCore) := by
  obtain ⟨A, hAchar, hAcomm, hA, t, htA, ht, hinv⟩ :=
    exists_characteristic_base_and_inverter hcard hcenter hchar helem
  let : A.Characteristic := hAchar
  let : IsMulCommutative A := hAcomm
  exact OrderThirtyTwoCharacteristicRecognition.recognition_of_characteristic_base_and_inverter
    hcard hchar helem A hA t htA ht hinv

end OrderThirtyTwoCharacteristicExtraction
