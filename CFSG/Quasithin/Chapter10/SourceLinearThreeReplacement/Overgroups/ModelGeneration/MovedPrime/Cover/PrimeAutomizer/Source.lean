module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.MovedPrime.Cover.PrimeAutomizer.Inner

/-!
# The prime-field automizer dichotomy

A faithful normal PSL₂(p) component, supplemented by the prescribed full
Sylow two-subgroup, has either a genuine unique-maximal-overgroup
structure or a generating family of solvable Sylow-invariant subgroups.
The proper extension uses the PGL₂ obstruction to normalized A₅; the
inner case uses maximal involution centralizers, with p = 7 separate.
No generation conclusion is assumed in either branch.

Source application: Aschbacher--Smith E.1.12 and 10.3.3, pp.214 and 756.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Cover
universe u

/-- The complete prime-field automizer dichotomy, with the prescribed full Sylow subgroup. -/
theorem primeAutomizerCoverDichotomy : PrimeAutomizerCoverDichotomy.{u} := by
  intro G _ _ L hLn hC R hgen p hp ho hp7 hm
  let := hLn
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : IsSimpleGroup (PSL(2,F)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : IsSimpleGroup L := e.isSimpleGroup
  let : Group.IsPerfect (PSL(2,F)) :=
    GorensteinWalter.psl2_isPerfect_of_card_gt_three F (by omega)
  let : Group.IsPerfect L :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hn := PrimeAutomizer.sylow_not_normal_of_faithful_simple L hC R
  by_cases hL : L = ⊤
  · subst L
    let d : G ≃* PSL(2,F) := (topEquiv (G := G)).symm.trans e
    by_cases hseven : p = 7
    · exact PrimeAutomizer.inner_seven_dichotomy R hn (hF.trans hseven) d
    · have hnine : p ≠ 9 := by
        intro h
        exact (by decide : ¬ Nat.Prime 9) (h ▸ hp)
      have hlarge : 9 < p := by obtain ⟨k, hk⟩ := ho; omega
      exact PrimeAutomizer.inner_large_prime_dichotomy R hn ho hlarge hF d
  · apply PrimeAutomizer.dichotomy_of_solvable_intersections L R hgen hn
    intro M hM hRM
    exact PrimeAutomizer.proper_extension_solvable_intersection
      L hC hL R hgen F ho hp7 hF e M hM.1 hRM

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Cover
