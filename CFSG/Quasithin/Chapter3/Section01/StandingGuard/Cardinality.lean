module
public import CFSG.Quasithin.Chapter3.Section01.StandingGuard
public import Theory.GroupTheory.MaximalTwoLocalOvergroups

/-!
# The multiple-overgroup branch supplies the standing guard

Two distinct maximal two-local overgroups of the original Sylow subgroup
cannot both be the selected maximal local. The other one supplies the
literal outside witness used by the numerical source theorems.

Source: Aschbacher--Smith, the standing assumption after 2.1.1, printed p.518;
the forward Main Theorem reduction retains precisely this cardinality premise.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter3
variable {G : Type*} [Group G]

/-- The actual multiple-overgroup branch gives an outside maximal local for
every selected maximal two-local containing the same Sylow subgroup. -/
theorem hasMaximalOutside_of_many (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (M : Subgroup G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M) :
    HasMaximalOutside T M := by
  obtain ⟨A,hA,B,hB,hne⟩ := (Set.one_lt_ncard_iff_nontrivial_and_finite.mp hmany).1
  by_cases hAM : A = M
  · exact hasMaximalOutside_of_two_distinct hM hB.1 hTM hB.2
      (fun he => hne (hAM.trans he.symm))
  · exact hasMaximalOutside_of_two_distinct hM hA.1 hTM hA.2 hAM

end CFSG.Quasithin.Chapter3
