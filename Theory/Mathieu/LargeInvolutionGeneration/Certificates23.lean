module

public import Theory.Mathieu.LargeInvolutionGeneration.Data

/-!
# Checked three-involution generation words in M23

The kernel verifies the point tables of the conjugators and their conjugates,
then verifies that words in the three conjugates recover the two generators
of the full M22 stabilizer and the native 23-cycle. No group order is inferred
from the untrusted witness search.

Source: Guralnick--Malle, *Classification of 2F-modules I*, Proposition 5.1,
manuscript p.16.
-/

public section
namespace Sporadic.Mathieu.LargeInvolutionGeneration
set_option maxRecDepth 10000

 theorem letter23_apply (i : Fin 6) (x : Fin 23) :
    (letter23 i).val x = letterPoint23 i x := by
  revert i x
  decide +kernel

 theorem target23_apply (i : Fin 3) (x : Fin 23) :
    (target23 i).val x = targetPoint23 i x := by
  revert i x
  decide +kernel

 theorem conjugator23_apply (i : Fin 3) (x : Fin 23) :
    (conjugator23 i).val x = conjugatorPoint23 i x := by
  rw [conjugator23, evalWord_apply _ _ letter23_apply]
  revert i x
  decide +kernel

private theorem conjugate23_relation (i : Fin 3) (x : Fin 23) :
    conjugatePoint23 i (conjugatorPoint23 i x) =
      conjugatorPoint23 i (targetPoint23 0 x) := by
  revert i x
  decide +kernel

 theorem conjugate23_apply (i : Fin 3) (x : Fin 23) :
    (conjugate23 i).val x = conjugatePoint23 i x := by
  obtain ⟨y, rfl⟩ := (conjugator23 i).val.surjective x
  change (conjugator23 i).val (a23.val
    ((conjugator23 i).val.symm ((conjugator23 i).val y))) = _
  rw [Equiv.symm_apply_apply, show a23 = target23 0 from rfl,
    target23_apply, conjugator23_apply, conjugator23_apply, conjugate23_relation]

private theorem generationPoint23 (i : Fin 3) (x : Fin 23) :
    wordPoint conjugatePoint23 (generationWord23 i) x = targetPoint23 i x := by
  revert i x
  decide +kernel

/-- The three recovered elements generate the full native M23. -/
theorem generation23 (i : Fin 3) :
    evalWord conjugate23 (generationWord23 i) = target23 i := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  rw [evalWord_apply _ _ conjugate23_apply, generationPoint23, target23_apply]

end Sporadic.Mathieu.LargeInvolutionGeneration
