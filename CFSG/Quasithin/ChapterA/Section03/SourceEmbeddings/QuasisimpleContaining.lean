module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryContaining
/-!
# The complete carrier catalogue for a quasisimple containing component

The original A.3.6 theorem over known simple groups classifies the actual
component. Quasisimplicity excludes its two solvable-Fitting alternatives;
the remaining alternatives retain the actual simple carrier or central
three-cover. This is used when C.5 supplies quasisimplicity independently
for the full conjugate span, including the smaller SL2(5) row.
Source: Aschbacher–Smith A.3.6 and C.5.12, printed pp.43–44,163.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
theorem quasisimple_containing_component_models_knownSimple
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G = ⊥)
    {L : Subgroup G} (hL : L.IsCComponent) [IsQuasisimple L] :
    (IsSimpleGroup L ∧ TheoremCModel L) ∨
      (Nonempty (center L ≃* Multiplicative (ZMod 3)) ∧ ThreeCoverModel L) := by
  have hfit : generalizedFitting L ≠ fittingSubgroup L := by
    intro he
    have hf : fittingSubgroup L = ⊤ := he.symm.trans generalizedFitting_eq_top_of_quasisimple
    let : Group.IsSolvable (⊤ : Subgroup L) := hf ▸
      (inferInstance : Group.IsSolvable (fittingSubgroup L))
    exact hL.not_isSolvable
      (Group.isSolvable_of_surjective (f := (topEquiv (G := L)).toMonoidHom)
        (topEquiv (G := L)).surjective)
  have hsource := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    G hG hO L hL

  cases hsource.1 with
  | simple _ hs hm => exact .inl ⟨hs, hm⟩
  | cover _ hc hm => exact .inr ⟨hc, hm⟩
  | natural h => exact (hfit h.1).elim
  | nilpotent h => exact (hfit h.1).elim

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
