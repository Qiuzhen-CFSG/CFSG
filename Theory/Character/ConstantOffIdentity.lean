module

public import Theory.Character.Generalized
public import Theory.Character.NilpotentBrauerIdeal

/-!
# Generalized characters constant away from the identity

Induction of the trivial character of the trivial subgroup gives the regular
character. An integer multiple of it, plus an integer multiple of the principal
character, realizes every function having the corresponding two values.
This supplies the elementary abelian restriction test in Brauer's criterion.

Source: the regular representation and the elementary character-ring identities;
Serre, *Linear Representations of Finite Groups*, Chapters 2 and 10.
-/

public section
noncomputable section
attribute [local instance] Classical.propDecidable

variable {G : Type*} [Group G] [Fintype G]

/-- The usual regular-character values are afforded by an actual representation. -/
theorem isCharacter_regular :
    IsCharacter (fun g : G => if g = 1 then (Nat.card G : ℂ) else 0) := by
  classical
  have he : inducedClassFunction (⊥ : Subgroup G) (1 : ClassFunction (⊥ : Subgroup G)) =
      (fun g : G => if g = 1 then (Nat.card G : ℂ) else 0) := by
    ext g
    have hx (x : G) : x⁻¹ * g * x = 1 ↔ g = 1 := by
      constructor
      · intro h
        have hh := congrArg (fun y => x * y * x⁻¹) h
        simpa [mul_assoc] using hh
      · rintro rfl
        simp
    simp [inducedClassFunction, Subgroup.mem_bot, hx, Nat.card_eq_fintype_card]
  rw [← he]
  exact BrauerInduction.inducedClassFunction_isCharacter _ isCharacter_one

/-- An integral regular multiple and an integral constant are a difference of
actual representation characters, including negative coefficients. -/
theorem isGeneralizedCharacter_of_constant_off_one (f : ClassFunction G) (a b : ℤ)
    (hone : f 1 = (a : ℂ) + (b : ℂ) * (Nat.card G : ℂ))
    (hother : ∀ g : G, g ≠ 1 → f g = (a : ℂ)) : IsGeneralizedCharacter f := by
  classical
  let r : ClassFunction G := fun g => if g = 1 then (Nat.card G : ℂ) else 0
  have he : f = a • (1 : ClassFunction G) + b • r := by
    ext g
    by_cases hg : g = 1
    · subst g
      simpa [r] using hone
    · simp [r, hg, hother g hg]
  rw [he]
  exact (isCharacter_one.isGeneralized.zsmul a).add (isCharacter_regular.isGeneralized.zsmul b)

end
