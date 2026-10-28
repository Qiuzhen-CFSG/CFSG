module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SourceContext
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.Binary
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder

/-!
# The exact remaining component list after the field and cover exclusions

Apply the exclusions to the actual 13.8.17 catalogue. The binary endpoint
Sp₄(2)' is identified with A₆; the G₂ endpoint is transported through the
actual coefficient-field equivalence to G₂(2)'. The parameter restrictions
exclude special SL₃(2) and the nonsimple unitary endpoint. The surviving
PSL₃(2) component is retained, as required by the statement of 13.8.21(2).

The higher-field and three small-cover exclusions are independent source
obligations, not conclusions of this sieve.
Source: Aschbacher–Smith, 13.8.17 and 13.8.21(2), printed pp.953,955–956.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents
open Chapter1.Section02.LocalModels Components.Models

/-- All higher-field rows of the literal component catalogue. Unitary
parameters are fixed-field orders; symplectic and G₂ rows retain the derived
subgroup convention, rather than silently replacing it by the whole group. -/
def HigherFieldAlternative (A : Type*) [Group A] : Prop :=
  ∃ n : ℕ, 1 < n ∧
    (ClassicalGroup.IsPSL A 2 (2 ^ n) ∨
      (∃ unitary : Bool, IsPSLSign A unitary 3 (2 ^ n) ∨ IsSLSign A unitary 3 (2 ^ n)) ∨
      IsSp4DerivedAt A (2 ^ n) ∨ IsG2DerivedAt A (2 ^ n))

/-- The exact remaining quotient list in 13.8.21(2). -/
def RemainingQuotient (A : Type*) [Group A] : Prop :=
  (∃ n : ℕ, 3 ≤ n ∧ n ≤ 5 ∧ ClassicalGroup.IsPSL A n 2) ∨
    Nonempty (A ≃* alternatingGroup (Fin 6)) ∨
    Nonempty (A ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (A ≃* commutator (Atlas.G2.Model (ZMod 2)))

/-- Normalize the binary endpoints of the source catalogue after the
independent higher-field and covered/Mathieu exclusions. -/
theorem remainingQuotient_of_exclusions {A : Type*} [Group A]
    (models : ComponentModel A) (hfield : ¬ HigherFieldAlternative A)
    (hsix : ¬ Nonempty (A ≃* A6Triple))
    (hmathieu : ¬ Nonempty (A ≃* Sporadic.Mathieu.M22))
    (hcover : ¬ Nonempty (A ≃* M22Triple)) : RemainingQuotient A := by
  cases models with
  | linear_two n hn iso =>
      exact (hfield ⟨n, by omega, Or.inl iso⟩).elim
  | projective_three unitary n hn iso =>
      have hn1 : n ≤ 1 := by
        by_contra hgt
        exact hfield ⟨n, by omega, Or.inr (Or.inl ⟨unitary, Or.inl iso⟩)⟩
      cases unitary with
      | false =>
          have hn : n = 1 := by simpa [ThreeParameter] using le_antisymm hn1 hn
          subst n
          exact Or.inl ⟨3, le_rfl, by decide, by simpa [IsPSLSign] using iso⟩
      | true => simp [ThreeParameter] at hn; omega
  | special_three unitary n hn hmod iso =>
      have hn1 : n ≤ 1 := by
        by_contra hgt
        exact hfield ⟨n, by omega, Or.inr (Or.inl ⟨unitary, Or.inr iso⟩)⟩
      cases unitary with
      | false =>
          have hn : n = 1 := by simpa [ThreeParameter] using le_antisymm hn1 hn
          subst n
          norm_num at hmod
      | true => simp [ThreeParameter] at hn; omega
  | symplectic n hn iso =>
      have hn1 : n ≤ 1 := by
        by_contra hgt
        exact hfield ⟨n, by omega, Or.inr (Or.inr (Or.inl iso))⟩
      have he : n = 1 := by omega
      subst n
      obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := iso
      let := hF
      let := hfin
      exact Or.inr (Or.inl ⟨e.trans
        (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (by simpa using hcard))⟩)
  | g2 n hn iso =>
      have hn1 : n ≤ 1 := by
        by_contra hgt
        exact hfield ⟨n, by omega, Or.inr (Or.inr (Or.inr iso))⟩
      have he : n = 1 := by omega
      subst n
      obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := iso
      let := hF
      let := hfin
      exact Or.inr (Or.inr (Or.inr ⟨e.trans
        (Atlas.G2.DerivedEvenOrder.derivedFieldEquiv (Atlas.G2.binaryFieldEquiv (by simpa using hcard)))⟩))
  | linear_four iso => exact Or.inl ⟨4, by decide, by decide, iso⟩
  | linear_five iso => exact Or.inl ⟨5, by decide, le_rfl, iso⟩
  | alternating_seven iso => exact Or.inr (Or.inr (Or.inl iso))
  | alternating_six_cover iso => exact (hsix iso).elim
  | mathieu iso => exact (hmathieu iso).elim
  | mathieu_cover iso => exact (hcover iso).elim

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents
