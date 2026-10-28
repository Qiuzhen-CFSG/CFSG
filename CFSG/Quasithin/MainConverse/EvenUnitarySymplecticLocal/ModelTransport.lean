module

public import CFSG.Quasithin.MainConverse.AlternatingLocal
public import CFSG.Quasithin.MainConverse.EvenUnitarySymplecticLocal.SymplecticFour
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived

/-!
# The symplectic model witnesses in the converse

The even-field calculation proves QT and E on the actual projective symplectic
carrier. Unpacking an `IsPSp` witness and transporting both conditions gives
the corresponding branch of the classification list. At the binary endpoint,
the proved equivalence from the actual derived carrier to A₆ supplies E.

Source: Aschbacher–Smith, Theorem 0.1.2(1–2), printed p.4, repeated on p.482.
The proper-K hypothesis belongs to final assembly and is not required for
these local conditions.
-/

namespace CFSG.Quasithin.MainConverse

open Theory.SpecificGroups.SymplecticFour.Binary

/-- QT and E for the exact even-field symplectic witness in the model list. -/
public theorem psp4_two_pow_quasithin_and_evenCharacteristic
    {G : Type*} [Group G] [Finite G] {f : ℕ}
    (hf : 2 ≤ f) (hG : ClassicalGroup.IsPSp G 2 (2 ^ f)) :
    IsQuasithin G ∧ IsEvenCharacteristic G := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hG
  exact ⟨quasithin_of_model_equiv e (SymplecticFour.projective_quasithin hcard hf),
    evenCharacteristic_of_model_equiv e
      (SymplecticFour.projective_evenCharacteristic hcard hf)⟩

/-- The actual binary derived symplectic carrier satisfies condition E. -/
public theorem symplectic_derived_evenCharacteristic :
    IsEvenCharacteristic (commutator (ClassicalGroup.PSp 2 (ZMod 2))) :=
  alternating_evenCharacteristic_of_degree_le_six_of_iso (by decide)
    projectiveDerivedEquivAlternatingSix

/-- Condition E for the actual isomorphism witness of the binary endpoint. -/
public theorem symplectic_derived_evenCharacteristic_of_iso
    {G : Type*} [Group G] [Finite G]
    (e : G ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) :
    IsEvenCharacteristic G :=
  evenCharacteristic_of_model_equiv e symplectic_derived_evenCharacteristic

end CFSG.Quasithin.MainConverse
