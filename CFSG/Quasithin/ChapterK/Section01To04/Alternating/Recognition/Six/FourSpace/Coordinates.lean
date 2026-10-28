module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.Extension
public import Theory.LinearAlgebra.BinaryFourAlternatingEight

/-!
# Linear coordinates on the literal natural A₆ module

The natural six-letter quotient has binary dimension four. The general
binary four-space comparison identifies its actual linear automorphism
group with A₈. The alternating restriction retains the faithfulness of
the symmetric action proved in `Six.Extension`.

These interfaces use exactly the quotient and action specified in
`Six.Inputs`, for Aschbacher–Smith, K.1–K.1.1, printed p.452.
-/

@[expose] public section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterK.Alternating.RecognitionInputs.Six
open BinaryFourAlternatingEight

/-- Dimension of the literal natural six-letter quotient. -/
theorem natural_finrank : Module.finrank (ZMod 2) (BinaryPermutation.natural (Fin 6)) = 4 := by
  rw [BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]
  rfl

/-- The actual linear group of the specified natural quotient, compared with A₈. -/
noncomputable def naturalLinearEquivAlternatingEight :
    (BinaryPermutation.natural (Fin 6) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6)) ≃*
      alternatingGroup (Fin 8) :=
  linearEquivAlternatingEight natural_finrank

/-- Faithfulness for the literal alternating inclusion in the natural action. -/
theorem natural_alternating_action_injective :
    Function.Injective (naturalLinearAction.comp (alternatingGroup (Fin 6)).subtype) :=
  six_naturalLinearAction_injective.comp (alternatingGroup (Fin 6)).subtype_injective

end CFSG.Quasithin.ChapterK.Alternating.RecognitionInputs.Six
