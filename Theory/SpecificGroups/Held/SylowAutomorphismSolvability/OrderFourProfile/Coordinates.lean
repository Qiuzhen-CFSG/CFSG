module

public import Theory.SpecificGroups.Held.SylowAutomorphismSolvability.FrattiniCoordinates
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.WordCoverage
public import Theory.SpecificGroups.Held.SylowAutomorphismSolvability.OrderFourProfile.FiniteData

/-!
# Literal coordinates and power tests for the Held normal form

The original normal form reverses the ascending PC generators used by the
Frattini homomorphism. Transport that map through the literal words, giving
masks `[1,2,4,4,8,8,8,8,8,0]`. Surjectivity and the existing order lower bound
make this normal form a bijection. The four-point base then relates each
Boolean order test to actual powers in the representative.

Source: the ATLAS words in `IntrinsicEnumeration.Words`, the proved collection
in `WordCoverage`, and the actual graph quotient in `FrattiniCoordinates`.
-/

namespace Held.SylowAutomorphismSolvability.OrderFourProfile
open FrattiniCoordinates
open Held.TwoLocalCandidates.MaximalNormalizerCatalogue
open IntrinsicEnumeration IntrinsicEnumeration.ExtensionChecks
open Held.LocalPairs.SylowGeometry.Calculations
open Held.LocalPairs.SylowGeometry.Calculations.TwoGroup

@[expose] public def vector (n : Nat) : Coordinate := Multiplicative.ofAdd (fun j => (n / 2 ^ j.val % 2 : Nat))
@[expose] public def vectorCode (v : Coordinate) : Nat :=
  (v.toAdd 0).val + 2 * (v.toAdd 1).val + 4 * (v.toAdd 2).val + 8 * (v.toAdd 3).val

private theorem literalWord_pcElement (i : Fin 10) :
    word (pcWord i) = pcElement ⟨9 - i.val, by omega⟩ := by
  apply Subtype.ext
  fin_cases i <;> simp [word, letter, pcWord, pcElement, pcGenerator, mul_assoc] <;> rfl

public theorem normalForm_coordinate (f : Representative →* Coordinate)
    (hf : ∀ i, f (pcElement i) = coordinateGenerator i) (n : Fin 1024) :
    f (normalForm n) = ((List.finRange 10).map (fun i =>
      coordinateGenerator ⟨9 - i.val, by omega⟩ ^ (n.val / 2 ^ i.val % 2))).prod := by
  simp only [normalForm, map_list_prod, List.map_map, Function.comp_def, map_pow,
    literalWord_pcElement, hf]

private theorem coordinate_calculation : ∀ n : Fin 1024,
    ((List.finRange 10).map (fun i =>
      coordinateGenerator ⟨9 - i.val, by omega⟩ ^ (n.val / 2 ^ i.val % 2))).prod =
        vector (indexCode n) := by decide +kernel

private theorem vectorCode_vector : ∀ n : Fin 1024,
    vectorCode (vector (indexCode n)) = indexCode n := by decide +kernel

private theorem vector_vectorCode : ∀ v : Coordinate, vector (vectorCode v) = v := by
  decide +kernel

public theorem normalForm_coordinate_eq_iff (f : Representative →* Coordinate)
    (hf : ∀ i, f (pcElement i) = coordinateGenerator i) (n : Fin 1024) (v : Coordinate) :
    f (normalForm n) = v ↔ indexCode n = vectorCode v := by
  rw [normalForm_coordinate f hf n, coordinate_calculation]
  constructor
  · intro h
    simpa only [vectorCode_vector] using congrArg vectorCode h
  · intro h
    rw [h, vector_vectorCode]

public theorem normalForm_bijective : Function.Bijective normalForm :=
  normalForm_surjective.bijective_of_nat_card_le (by
    simpa only [Nat.card_fin] using
      InnerNormalizer.representative_card_ge_of_orbit_labels InnerNormalizer.orbitSizeLabel_eq_card_orbit)

private theorem sameAction_power (n : Fin 1024) (k : Nat) :
    sameAction (normalFormAction n ^ k) 1 = true ↔ normalForm n ^ k = 1 := by
  have h : sameAction (normalFormAction n ^ k) 1 = same (normalForm n ^ k) 1 := by
    simp only [sameAction, same, normalFormAction_eq, Subgroup.coe_pow,
      Subgroup.coe_one, map_pow, map_one]
  rw [h, same_eq_true]

public theorem hasOrderFour_iff (n : Fin 1024) :
    hasOrderFour n = true ↔ normalForm n ^ 4 = 1 ∧ normalForm n ^ 2 ≠ 1 := by
  simp only [hasOrderFour, Bool.and_eq_true, Bool.not_eq_true']
  rw [sameAction_power, ← Bool.not_eq_true, sameAction_power]
end Held.SylowAutomorphismSolvability.OrderFourProfile
