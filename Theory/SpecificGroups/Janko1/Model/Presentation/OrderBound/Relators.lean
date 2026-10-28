module
public import Theory.SpecificGroups.Janko1.Model.Presentation.OrderBound.Core
public import Theory.SpecificGroups.Janko1.Model.Presentation.OrderBound.Certificate.Context

/-!
# Realization of the J₁ coset certificate

The six literal words are the five ATLAS relators and the definition `c = ab`.
The other loops are only inverse or cyclic rotations of these words. This
module realizes the certificate in the abstract presentation, rather than
in the matrix quotient.

Source: ATLAS `J1G1-P1`; see `Source/README.md`.
-/

public section
namespace Janko1.PresentationBound
open Subgroup.CosetWordCertificate
open Certificate

private theorem original_eval (i : Fin 6) : eval generator (originals i) = 1 := by
  fin_cases i
  · change eval generator [(0, true), (0, true)] = 1
    simpa [eval, FreeGroup.lift_mk, generator, atlasWord, pow_succ, mul_assoc]
      using relator_eval 0
  · change eval generator [(1, true), (1, true), (1, true)] = 1
    simpa [eval, FreeGroup.lift_mk, generator, atlasWord, pow_succ, mul_assoc]
      using relator_eval 1
  · change eval generator [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true)] = 1
    simpa [eval, FreeGroup.lift_mk, generator, atlasWord, pow_succ, mul_assoc]
      using relator_eval 2
  · change eval generator [(0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false)] = 1
    simpa [eval, FreeGroup.lift_mk, generator, atlasWord, pow_succ, mul_assoc]
      using relator_eval 3
  · change eval generator [(0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false)] = 1
    simpa [eval, FreeGroup.lift_mk, generator, atlasWord, pow_succ, mul_assoc]
      using relator_eval 4
  · change eval generator [(0, true), (1, true), (2, false)] = 1
    simp [eval, FreeGroup.lift_mk, generator]

set_option maxRecDepth 10000 in
private theorem variants_exact : ∀ i : Fin 110,
    relatorTable i.val = variant (originals (variantTable i.val).1)
      (variantTable i.val).2.1 (variantTable i.val).2.2 := by decide +kernel

private theorem relator_ok (r : Nat) : eval generator (relatorWords r) = 1 := by
  let i : Fin 110 := ⟨min r 109, by omega⟩
  rw [relatorWords, variants_exact i]
  exact eval_variant _ (original_eval _) _ _

/-- Every certificate rule is interpreted in the literal abstract presentation. -/
theorem certificate_valid : Valid context cyclic generator (definitions.repr generator) := by
  apply definitions.valid
  · intro a ha
    have he : a = (2,true) := beq_iff_eq.mp ha
    subst a
    simpa only [eval_letter, if_true, cyclic] using Subgroup.mem_zpowers (generator 2)
  · exact relator_ok

end Janko1.PresentationBound
