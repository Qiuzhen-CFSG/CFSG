module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Lie.FieldClassical.Inputs
public import Theory.SpecificGroups.PSL2.OuterSolvable.Models

/-!
# The smallest linear field endpoint

PSL₂(2) is solvable, as is its actual derived subgroup. A component has a
nontrivial perfect quotient by its center, so that quotient cannot be
PSL₂(2)′. Consequently the linear-two field row automatically has n > 1.
This excludes the endpoint without replacing the derived subgroup by PSL₂(2).

Source: Aschbacher–Smith, 16.1.4(4) and 16.1.7(3a), printed pp.1171–1173.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.FieldClassical
open Subgroup Theory.GroupTheory
open CounterexampleGeometry.CoveredPersistence

private theorem not_linearTwo_derived_two {P : Type*} [Group P]
    [Nontrivial P] [Group.IsPerfect P]
    (hsmall : FieldFamily.linearTwo.DerivedAt P 2) : False := by
  obtain ⟨M, hM, hfin, hmodel, ⟨d⟩⟩ := hsmall
  obtain ⟨F, hF, hfinF, hcard, ⟨e⟩⟩ := hmodel
  let : Group.IsSolvable (Theory.PSL2.Group F) :=
    Theory.PSL2.OuterSolvable.isSolvable_of_card_two hcard
  let : Group.IsSolvable M := Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : Group.IsSolvable P := Group.isSolvable_of_surjective (f := d.symm.toMonoidHom) d.symm.surjective
  exact Group.IsPerfect.not_isSolvable P inferInstance

/-- A component cannot have the solvable derived PSL₂(2) central quotient. -/
theorem linearTwo_parameter_gt_one {P : Type*} [Group P] [IsQuasisimple P]
    {n : ℕ} (hn : 1 ≤ n)
    (hsmall : FieldFamily.linearTwo.DerivedAt (P ⧸ center P) (2 ^ n)) : 1 < n := by
  by_contra h
  have he : n = 1 := by omega
  subst n
  let : IsSimpleGroup (P ⧸ center P) := IsQuasisimple.simple
  exact not_linearTwo_derived_two (by simpa using hsmall)

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.FieldClassical
