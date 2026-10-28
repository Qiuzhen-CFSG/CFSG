module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryOdd.SeventhModel
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryOdd.Twist
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryOdd.Splitting

/-!
# The seventh marked relation in a perfect central double cover

The checked model identity places the seventh word in the central kernel,
whose order two makes it an involution. Twisting all three marked lifts by
this word satisfies all twelve local relators. The local section and the
Schreier parity obstruction then force the twist to be one. This proves the
original mapped equation under precisely the four allowed even equations.

Source: John Bray's ATLAS `Held/Model/Source/HeG1-P1.M` and the literal marked
words of `M1Restriction/Data.lean`. No faithfulness of the source presentation
or multiplier assertion is used.
-/

public section
namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryOdd
open Subgroup.CosetWordCertificate PerfectCentralCovering

/-- The seventh equation follows from the even image equations in every
finite perfect central double cover with the literal marked triangle. -/
theorem image_seven_of_even {E : Type*} [Group E] [Finite E]
    (f : Cover E He) (hcard : Nat.card f.toMonoidHom.ker = 2)
    (h : Presentation →* E) (ht : f.toMonoidHom.comp h = presentationMap)
    (heven : EvenImageRelations h) :
    h (eval liftedGenerator (relationLetters 7)) = 1 := by
  let z := h (eval liftedGenerator (relationLetters 7))
  have hk : z ∈ f.toMonoidHom.ker := by
    change (f.toMonoidHom.comp h) (eval liftedGenerator (relationLetters 7)) = 1
    rw [ht]
    exact seventh_model
  have hs : z ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨z, hk⟩ : f.toMonoidHom.ker))
    rw [hcard] at hh
    exact congrArg Subtype.val hh
  exact common_twist_eq_one f hcard h ht z hk
    (twisted_image_relations f h ht heven z (f.ker_le_center hk) hs rfl)

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryOdd
