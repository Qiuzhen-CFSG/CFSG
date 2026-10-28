module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveSourceAudit.MonomialWitness.Solvability
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveSourceAudit.Escape

/-!
# Applying the solvability of the five-prime monomial graph subgroup

The solvability input of `monomial_escape_of_simultaneous_sylow` is discharged
on its literal carrier. Simultaneous placement of the two actors in an ambient
Sylow subgroup remains the independent input. Weak-closure movement comes from
the actual three-cycle in `Preparation`, and the solvable E-generation theorem
then gives an escaping E1-member for the original full conjugacy family.

Source: Aschbacher--Smith E.1.8, E.1.13 and E.1.14(7), printed pp.210--214;
`FiveSourceAudit/source/README.md` for the matrices. Final unconditional witness
assembly remains with `MonomialWitness`.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveSourceAudit

/-- The concrete escape conclusion now requires only simultaneous Sylow placement;
the solvability premise of the original consumer has been proved. -/
theorem monomial_escape_of_sylow_placement
    (hplace : ∃ T : Sylow 2 Model, actor ≤ (T : Subgroup Model) ∧
      (T : Subgroup Model) ≤ monomialOvergroup ∧ movedActor ≤ (T : Subgroup Model)) :
    ∃ T : Sylow 2 Model, actor ≤ (T : Subgroup Model) ∧
      ∃ g : Model, actor.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup Model) ∧
        ∃ K : Subgroup Model,
          IsEMemberAt 1 (T : Subgroup Model) (actor.map (MulAut.conj g).toMonoidHom) K ∧
          ¬ K ≤ normalizer (weakClosure (T : Subgroup Model) family : Set Model) := by
  let : Group.IsSolvable monomialOvergroup := monomialOvergroup_solvable
  obtain ⟨T, hAT, hTK, hBT⟩ := hplace
  obtain ⟨B, ⟨g, rfl⟩, hBT, K, hK, hKM⟩ :=
    exists_escape_of_solvable_overgroup T family family_elementary monomialOvergroup hTK
      (monomial_motion_of_movedActor_le T hBT)
  exact ⟨T, hAT, g, hBT, K, hK, hKM⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveSourceAudit
