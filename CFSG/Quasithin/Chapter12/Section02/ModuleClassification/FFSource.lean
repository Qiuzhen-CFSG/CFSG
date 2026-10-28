module

public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Actions
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.FFQuasisimple

/-!
# Complete B.5.1 on the original chosen seed actor

Irr⁺ forces the two-core of the faithful seed actor to act trivially.
The component image is quasisimple and the quotient is a two-group, so
an FF witness places this component inside the actual best-offender subgroup.
The complete known-simple B.5.1 theorem then supplies all six source clauses
on the same chosen space and its literal moved and fixed-space quotients.
No fixed-free or splitting hypothesis is imposed.

The FF condition here concerns the original seed actor. Passing from a
full-linear-normalizer FF witness remains a separate comparison step.
Source: Aschbacher--Smith B.5.1 and 12.2.2, printed pp.99--103 and 795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal faithful seed actor has no nontrivial normal two-subgroup. -/
theorem seed_twoCore_eq_bot (hq : IsQuasisimple (L ⧸ pCore 2 L)) :
    pCore 2 D.seedActor = ⊥ := by
  let := D.componentImage_quasisimple hq
  have hs : componentLayer D.componentImage = ⊤ := by
    apply top_unique
    exact le_sSup (show IsComponent D.componentImage ⊤ from
      ⟨Subgroup.IsSubnormal.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩)
  have hi : IsIrrPlus D.seedRepresentation D.componentImage ⊤ := by
    simpa only [Submodule.comap_subtype_self] using
      D.irrPlus.isIrrPlus.restricted (reducedRepresentation (L ⊔ (T : Subgroup G)))
        D.irrPlus.invariant le_rfl
  have hfix := IsIrrPlus.le_fixedSpace_of_twoGroup_centralizes D.seedRepresentation hi
    pCore_isPGroup (twoCore_centralizes_of_normal_layer_or_odd D.componentImage (Or.inl hs))
    (le_subspaceStabilizer D.seedRepresentation ⊤ (fun _ _ _ _ => Submodule.mem_top))
  apply bot_unique
  intro g hg
  apply mem_bot.mpr
  apply subspaceImageRepresentation_injective (reducedRepresentation (L ⊔ (T : Subgroup G))) D.space
  apply LinearMap.ext
  intro v
  simpa only [map_one, Module.End.one_apply, MonoidHom.comp_apply,
    Subgroup.subtype_apply] using hfix Submodule.mem_top ⟨g,hg⟩

/-- All six corrected B.5.1 conclusions on the actual chosen space and
actual best-offender subgroup; every universal earlier input is discharged. -/
theorem seed_quasisimple_source_conclusion
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hff : IsFFModule D.seedRepresentation) :
    D.componentImage ≤ offenderSubgroup D.seedRepresentation ∧
    Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (D.seedRepresentation.comp (offenderSubgroup D.seedRepresentation).subtype)
      (D.componentImage.subgroupOf (offenderSubgroup D.seedRepresentation))) := by
  let := D.componentImage_quasisimple h.quasisimple
  exact ChapterB.QuasisimpleSource.SourceCompletion.ff_quasisimple_source_conclusion
    D.seedRepresentation D.componentImage D.seed_quotient_isTwoGroup
    (D.seed_twoCore_eq_bot h.quasisimple)
    ((D.seed_sqtk h (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)).subgroup D.componentImage)
    (subspaceImageRepresentation_injective _ _) hff

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
