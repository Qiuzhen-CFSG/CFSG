module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.GeneralizedRows.PowerData
public import Theory.Character.ConstantOffIdentity

/-!
# Realization of the ordinary rows on elementary two-subgroups

All nonidentity elements of an exponent-two subgroup belong to the unique
involution class. In each of the fifteen rows the difference between the degree
and the involution value is divisible by eight. If the subgroup order divides
eight, its restricted row is therefore an integer multiple of its regular
character plus an integer multiple of its principal character.

This is the two-primary local test for the Brauer restriction construction.
The two columns used here are from the literal table in `OrdinaryData.lean`;
that numerical material has its GPL-3.0-or-later attribution in `../../Source.md`.
Source: Janko (1966), ordinary-character calculation; Gorenstein, §16.6, p.482.
-/

noncomputable section
attribute [local instance] Fintype.ofFinite

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters

private def involutionValue : Fin 15 → ℤ :=
  ![1, 0, 0, 4, -4, 5, -3, -3, 0, 0, 0, 5, -3, -3, 1]

private def regularMultiple : Fin 15 → ℤ :=
  ![0, 7, 7, 9, 10, 9, 10, 10, 15, 15, 15, 16, 17, 17, 26]

/-- Every row restricts to a genuine generalized character on any exponent-two
subgroup whose order divides eight. No root or power-map calculation is needed
for this branch. -/
public theorem OrdinaryPowerLabels.row_two_restriction
    {G : Type*} [Group G] [Finite G] {c : OrdinaryClassData G}
    (p : OrdinaryPowerLabels c) (ζ₅ ζ₁₉ : ℂ) (i : Fin 15)
    (H : Subgroup G) (hsquare : ∀ x : H, x ^ 2 = 1) (hcard : Nat.card H ∣ 8) :
    IsGeneralizedCharacter (fun x : H => p.row ζ₅ ζ₁₉ i (x : G)) := by
  obtain ⟨k, hk⟩ := hcard
  apply isGeneralizedCharacter_of_constant_off_one _ (involutionValue i)
    (regularMultiple i * (k : ℤ))
  · have hc : (8 : ℂ) = (k : ℂ) * (Nat.card H : ℂ) := by
      exact_mod_cast hk.trans (Nat.mul_comm _ _)
    have hi : ordinaryValue ζ₅ ζ₁₉ i 0 =
        (involutionValue i : ℂ) + (regularMultiple i : ℂ) * 8 := by
      fin_cases i <;> norm_num [ordinaryValue, involutionValue, regularMultiple]
    change p.row ζ₅ ζ₁₉ i 1 = _
    rw [OrdinaryPowerLabels.row, p.classIndex_one, hi]
    push_cast
    rw [mul_assoc, ← hc]
  · intro x hx
    have ho : orderOf (x : G) = 2 := by
      apply orderOf_eq_prime_iff.mpr
      exact ⟨congrArg Subtype.val (hsquare x), fun he => hx (Subtype.ext he)⟩
    change ordinaryValue ζ₅ ζ₁₉ i (p.classIndex (x : G)) = _
    rw [p.classIndex_involution _ ho]
    fin_cases i <;> norm_num [ordinaryValue, involutionValue]

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters
