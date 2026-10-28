module
public import Theory.SpecificGroups.SymplecticFour.NativeTriality
public import Theory.SpecificGroups.SymplecticFour.NativeTits

/-!
# Excluding the remaining exceptional carriers from symplectic four-space

The genuine binary triality and Tits carriers contain two-elements with
nontrivial fourth powers. Every two-element in dimension four in characteristic
two has fourth power one, so no faithful symplectic representation exists.
The actual Tits embedding gives the same obstruction for every Ree F₄ model.
These results discharge the last exceptional rows in the native carrier
inspection for Aschbacher--Smith G.4.1, printed p.342.
-/

@[expose] public noncomputable section
open Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section04.NativeTransvectionRecognition
open Theory.SpecificGroups.SymplecticFour
variable {H F : Type*} [Group H] [Field F] [CharP F 2]

/-- A faithful characteristic-two symplectic four-space excludes binary triality. -/
theorem not_binary_triality_model {n : ℕ} (hn : 0 < n)
    (j : H →* Sp F) (hj : Function.Injective j) :
    ¬Triality.Standard.IsTrialityGroupAt (2 ^ n) H := by
  intro h
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff H n hn).mp h
  exact NativeTriality.model_not_injective n hn (j.comp e.symm.toMonoidHom)
    (hj.comp e.symm.injective)

/-- The embedded Tits group excludes every actual Ree F₄ carrier. -/
theorem not_ree_model (m : ℕ) (j : H →* Sp F) (hj : Function.Injective j) :
    ¬Nonempty (H ≃* ReeF4.Model m) := by
  rintro ⟨e⟩
  exact NativeTits.ree_model_not_injective m (j.comp e.symm.toMonoidHom)
    (hj.comp e.symm.injective)

/-- The actual Parrott Tits carrier has no faithful characteristic-two Sp₄ action. -/
theorem not_tits_model (j : H →* Sp F) (hj : Function.Injective j) :
    ¬Nonempty (H ≃* Tits.ParrottGroup) := by
  rintro ⟨e⟩
  exact NativeTits.model_not_injective (j.comp e.symm.toMonoidHom)
    (hj.comp e.symm.injective)

end CFSG.Quasithin.ChapterG.Section04.NativeTransvectionRecognition
