module

public import Theory.Mathieu.M22.Properties.ConjugateGeneration.Data

/-!
# Checked identities for conjugate generation in M₂₂

Kernel reduction checks the fusion words and both standard generators as words
in the designated conjugates. The alternatives for all 256 Sylow rows discard
only the identity and elements with nonidentity square. Thus the coverage does
not rely on encoded conjugacy-class counts.

Source: Guralnick–Malle, Classification of 2F-modules I, Proposition 5.1,
manuscript pp.15–16.
-/

public section
namespace Sporadic.Mathieu.M22ConjugateGeneration
open M22CubicInverters M22ValueBound.Concrete
set_option maxRecDepth 100000

theorem representative_apply (k : Fin 3) (x : Fin 22) :
    (representative k).val x = representativeTable k x := by
  fin_cases k
  · exact letter_apply 0 x
  · revert x; decide +kernel
  · exact rowElement_apply 24 x

theorem conjugator_apply (k : Fin 3) (j : Fin 4) (x : Fin 22) :
    (conjugator k j).val x = conjugatorTable k j x := by
  rw [conjugator, innerWord_apply]
  revert k j x
  decide +kernel

theorem conjugate_table_relation (k : Fin 3) (j : Fin 4) (x : Fin 22) :
    conjugateTable k j (conjugatorTable k j x) =
      conjugatorTable k j (representativeTable k x) := by
  revert k j x
  decide +kernel

theorem conjugate_apply (k : Fin 3) (j : Fin 4) (x : Fin 22) :
    (conjugate k j).val x = conjugateTable k j x := by
  obtain ⟨y, rfl⟩ := (conjugator k j).val.surjective x
  change (conjugator k j).val ((representative k).val
    ((conjugator k j).val.symm ((conjugator k j).val y))) = _
  rw [Equiv.symm_apply_apply, representative_apply, conjugator_apply,
    conjugator_apply, conjugate_table_relation]

theorem fusion_apply (i : Fin 256) (x : Fin 22) :
    (fusionElement i).val x = fusionTable i x := by
  rw [fusionElement, innerWord_apply]
  revert i x
  decide +kernel

theorem row_fusion_cases (i : Fin 256) :
    (∀ x, rowTable i x = x) ∨
    (∃ x, rowTable i (rowTable i x) ≠ x) ∨
    (∀ x, rowTable i (fusionTable i x) =
      fusionTable i (representativeTable (fusionClass i) x)) := by
  revert i
  decide +kernel

theorem generation_word_table (k : Fin 3) (j : Fin 2) (x : Fin 22) :
    wordAction (conjugateTable k) (generationWord k j) x = letterTable j.castSucc x := by
  revert k j x
  decide +kernel

theorem inner_generation_word_table (j : Fin 2) (x : Fin 22) :
    wordAction (fun i : Fin 3 => conjugateTable 0 i.castSucc)
      (innerGenerationWord j) x = letterTable j.castSucc x := by
  revert j x
  decide +kernel

end Sporadic.Mathieu.M22ConjugateGeneration
