module

public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.ProjectiveIndices

/-!
# Order comparison in the projective-general branch of A.3.18

The signed comparison is applied to the original image of L in H/O_{3'}(H)
and the literal prime-to-three residual of that quotient. It supplies the
factor-three order comparison once the PGL/PGU alternative has been selected.
Establishing that alternative remains part of the source-theorem assembly.

Source: Aschbacher--Smith, Lemma A.3.18(2), printed pp.51--52.
-/

public section
open Subgroup Theory.GroupTheory CFSG.Quasithin.Chapter1.Section02.LocalModels

namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels

/-- The exact residual/component order comparison for the first model in A.3.18(2). -/
theorem card_projective_residual_eq_three_mul_starComponent
    {H : Type*} [Group H] (L : Subgroup H) (unitary : Bool) (q : ℕ)
    (hL : IsPSLSign (starComponent 3 L) unitary 3 q)
    (hR : IsPGLSign (primeToResidual 3 (Star 3 H)) unitary q)
    (hsign : SignedCongruence unitary q) :
    Nat.card (primeToResidual 3 (Star 3 H)) = 3 * Nat.card (starComponent 3 L) :=
  card_pgl_sign_eq_three_mul_psl_sign unitary q hL hR hsign

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels
