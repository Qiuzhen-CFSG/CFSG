module

public import Theory.SpecificGroups.Held.Automorphisms.Realization.IndexBound.Evaluation

/-!
# The source relators for the Held coset certificate

The first seven words are exactly the seven uncommented relations of John
Bray's `Model/Source/HeG1-P1.M`, already checked for the concrete generators.
The remaining four equations expand the two marked conjugates and their squares.
-/

public section
namespace Held.Realization.IndexCertificate
open Subgroup.CosetWordCertificate

theorem relator_0 : eval generator (relatorFin 0) = 1 := by
  have h := Held.relations 0
  simpa [relatorFin, generator, eval_cons, relationWord, pow_succ,
    mul_inv_rev, mul_assoc] using h

theorem relator_1 : eval generator (relatorFin 1) = 1 := by
  have h := Held.relations 1
  simpa [relatorFin, generator, eval_cons, relationWord, pow_succ,
    mul_inv_rev, mul_assoc] using h

theorem relator_2 : eval generator (relatorFin 2) = 1 := by
  have h := Held.relations 2
  simpa [relatorFin, generator, eval_cons, relationWord, pow_succ,
    mul_inv_rev, mul_assoc] using h

theorem relator_3 : eval generator (relatorFin 3) = 1 := by
  have h := Held.relations 3
  simpa [relatorFin, generator, eval_cons, relationWord, pow_succ,
    mul_inv_rev, mul_assoc] using h

theorem relator_4 : eval generator (relatorFin 4) = 1 := by
  have h := Held.relations 4
  simpa [relatorFin, generator, eval_cons, relationWord, pow_succ,
    mul_inv_rev, mul_assoc] using h

theorem relator_5 : eval generator (relatorFin 5) = 1 := by
  have h := Held.relations 5
  simpa [relatorFin, generator, eval_cons, relationWord, pow_succ,
    mul_inv_rev, mul_assoc] using h

theorem relator_6 : eval generator (relatorFin 6) = 1 := by
  have h := Held.relations 6
  simpa [relatorFin, generator, eval_cons, relationWord, pow_succ,
    mul_inv_rev, mul_assoc] using h

theorem relator_7 : eval generator (relatorFin 7) = 1 := by
  simp [relatorFin, generator, eval_cons, markedGenerator, pow_succ,
    mul_inv_rev, mul_assoc]

theorem relator_8 : eval generator (relatorFin 8) = 1 := by
  simp [relatorFin, generator, eval_cons, markedGenerator, pow_succ,
    mul_inv_rev, mul_assoc]

theorem relator_9 : eval generator (relatorFin 9) = 1 := by
  have ha (x : He) : a * (a * x) = x := by
    rw [← mul_assoc, ← pow_two, Held.a_sq, one_mul]
  simp [relatorFin, generator, eval_cons, markedGenerator, pow_succ,
    mul_inv_rev, mul_assoc, ha]

theorem relator_10 : eval generator (relatorFin 10) = 1 := by
  have ha (x : He) : a * (a * x) = x := by
    rw [← mul_assoc, ← pow_two, Held.a_sq, one_mul]
  simp [relatorFin, generator, eval_cons, markedGenerator, pow_succ,
    mul_inv_rev, mul_assoc, ha]

end Held.Realization.IndexCertificate
