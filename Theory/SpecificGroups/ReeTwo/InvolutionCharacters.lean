module

public import Theory.SpecificGroups.ReeTwo.CoreCharacterKernel

/-!
# Ree two characters on involutions

Both alternative binary characters kill every involution in the Sylow model.
The cyclic-four coordinate of an involution is either zero or two. The zero
case is the involution calculation in `CoreCharacterKernel`; the other case
reduces to the twisted square `x * a²(x)`, checked on all 1024 core elements by
kernel reduction. Parity also kills involutions, so the mixed character follows.

Source: Shinoda (1975), (2.3), pp. 81–82, for the verified multiplication and
root-1 action. The finite checks use that model, not an external computation.
-/

namespace ReeTwo.SylowModel

private theorem binaryCharacter_eq_one_of_twisted_square_eq_one : ∀ x : Core,
    x * (Core.a ^ 2) x = 1 → Core.binaryCharacter x = 1 := by
  set_option maxHeartbeats 0 in
    set_option maxRecDepth 131072 in
      decide +kernel

/-- The core-coordinate character kills every involution of the full Sylow
model, including those outside the canonical core. -/
public theorem coreCharacter_eq_one_of_square_eq_one (g : SylowModel) (hg : g ^ 2 = 1) :
    coreCharacter g = 1 := by
  have ht : g.right ^ 2 = 1 := by
    simpa only [map_pow, map_one, SemidirectProduct.rightHom_eq_right] using congrArg
      (SemidirectProduct.rightHom : SylowModel →* FiveFour.Cyclic 4) hg
  have hl : g.left * Core.complementAction (SemidirectProduct.inr g.right) g.left = 1 :=
    congrArg SemidirectProduct.left (show g * g = 1 by simpa only [pow_two] using hg)
  change Core.binaryCharacter g.left = 1
  rcases (by decide +kernel : ∀ t : FiveFour.Cyclic 4, t ^ 2 = 1 →
      t = 1 ∨ t = FiveFour.generator 4 ^ 2) g.right ht with h | h
  · rw [h, map_one, map_one, MulAut.one_apply] at hl
    exact Core.binaryCharacter_eq_one_of_square_eq_one _ (by simpa only [pow_two] using hl)
  · rw [h, map_pow, map_pow] at hl
    change g.left * (Core.complementAction FiveFour.a ^ 2) g.left = 1 at hl
    rw [Core.complementAction_a] at hl
    exact binaryCharacter_eq_one_of_twisted_square_eq_one _ hl

/-- Both alternative characters kill involutions. -/
public theorem alternativeCharacter_eq_one_of_square_eq_one
    (χ : SylowModel →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter)
    (g : SylowModel) (hg : g ^ 2 = 1) : χ g = 1 := by
  rcases hχ with rfl | rfl
  · exact coreCharacter_eq_one_of_square_eq_one g hg
  · change coreCharacter g * character g = 1
    rw [coreCharacter_eq_one_of_square_eq_one g hg,
      character_eq_one_of_square_eq_one g hg, mul_one]

/-- The first omega subgroup is killed by either alternative character. -/
public theorem omega_le_alternativeCharacter_ker
    (χ : SylowModel →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) :
    omega₁ SylowModel (p := 2) ≤ χ.ker := by
  apply (Subgroup.closure_le _).mpr
  intro x hx
  exact alternativeCharacter_eq_one_of_square_eq_one χ hχ x
    (by simpa only [Set.mem_ofPred_eq, pow_one] using hx)

end ReeTwo.SylowModel
