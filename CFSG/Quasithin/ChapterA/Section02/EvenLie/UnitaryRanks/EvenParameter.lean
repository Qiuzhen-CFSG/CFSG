module

public import CFSG.Quasithin.ChapterA.Section02.EvenLie.UnitaryRanks
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicTorus.Cover.EvenParameter

/-!
# The actual special-unitary covering branch of A.2.18

An isomorphism with SU5(q), for even q, transports quasithinness to the
original special unitary group. Its coordinate-swap involution centralizer
has odd-prime rank at least three, so this covering branch is impossible.
All field parameters and the actual model equivalence are retained.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
A.2.18, printed p.40, case (ii). Cover recognition and the source induction
remain separate inputs to the full A.2.18 theorem.
-/

public section

open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section02.EvenLie

/-- Every actual SU5 cover in even characteristic is excluded from a quasithin source group. -/
theorem unitary_five_cover_not_quasithin
    {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
    (J : HermitianForm 5 F) {q : ℕ}
    (hcard : Nat.card F = q ^ 2) (heven : Even q) (hq : 2 ≤ q)
    (hconj : ∀ x, J.conj x = x ^ q) (e : G ≃* J.specialSubgroup) :
    ¬ IsQuasithin G := by
  let : Finite (Matrix.GeneralLinearGroup (Fin 5) F) :=
    Finite.of_injective Units.val Units.val_injective
  intro hqt
  exact Theory.SpecificGroups.UnitaryFive.not_quasithin_special_even_of_form
    J hcard heven hq hconj (Theory.GroupTheory.isQuasithin_of_equiv e hqt)

end CFSG.Quasithin.ChapterA.Section02.EvenLie
