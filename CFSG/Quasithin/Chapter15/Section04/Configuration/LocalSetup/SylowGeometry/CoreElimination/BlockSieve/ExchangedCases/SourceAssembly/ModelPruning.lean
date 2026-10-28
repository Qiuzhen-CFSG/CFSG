module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.ModelPruning.Rows
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.FFClassification
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.Selection

/-!
# Source B.5 pruning on the selected exchanged component

Apply the proved known-simple B.5 classification to the original star action
of LR on its literal omega-core module. The original selected component has
the intrinsic swapped PSL₂ model. Its canonical quotient identification with
the component inside the offender subgroup supplies the model comparison.

The conclusion retains the same complete B.5 witness and all of its section,
central quotient, extension, offender and ratio data. Its only possible rows
are natural SL₂, marked natural A₅, binary natural SL₃, and doubled binary
natural SL₃. There is no earlier C.2.7/C.1.34 classification premise.

Source: Aschbacher--Smith C.2.7(3), pp.145--147, and 15.4.20, p.1164.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly
open SL3Geometry.SourceCases
universe u
variable {G : Type u} [Group G] [Finite G]
variable {d : Source.Geometry G} {i j : Bool} {H U K K₁ : Subgroup G} {r : G}

/-- Refine a chosen full B.5 source conclusion without changing its section. -/
theorem source_selected_ff_cases
    (h : Input d i j H U K) (s : Selected H U K K₁ r)
    (hc : ComponentHypotheses KnownSimple.IsKnownSimple H ((sourceRadical d U).subgroupOf H)
      (d.M₁.subgroupOf H) (K₁.subgroupOf H))
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((starRepresentation (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H)).comp
        (offenderSubgroup (starRepresentation (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H))).subtype)
      ((starComponent (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H)).subgroupOf
        (offenderSubgroup (starRepresentation (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H))))) :
    ModelPruning.Cases _ _ c.sectionData := by
  have hCJ := (source_selected_ff_classification h s hc).1
  let e := SL3Geometry.source_componentStarEquiv h s hc.normalized
    (source_local_radical h s hc.normalized)
  have hs := swappedModel_of_mulEquiv (e.trans (subgroupOfEquivOfLe hCJ).symm) s.model
  exact ModelPruning.quasisimple_cases hs c.clause_one

/-- The original selected source configuration produces both the full B.5
conclusion and its refined action alternatives, with no classifier input. -/
theorem source_selected_ff_pruned_classification
    (h : Input d i j H U K) (s : Selected H U K K₁ r)
    (hc : ComponentHypotheses KnownSimple.IsKnownSimple H ((sourceRadical d U).subgroupOf H)
      (d.M₁.subgroupOf H) (K₁.subgroupOf H)) :
    let L := K₁.subgroupOf H
    let R := (sourceRadical d U).subgroupOf H
    let J := offenderSubgroup (starRepresentation L R)
    starComponent L R ≤ J ∧
    ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((starRepresentation L R).comp J.subtype) ((starComponent L R).subgroupOf J),
      ModelPruning.Cases _ _ c.sectionData := by
  have hCJ := (source_selected_ff_classification h s hc).1
  obtain ⟨hCJ,⟨c⟩⟩ := source_selected_ff_classification h s hc
  exact ⟨hCJ,c,source_selected_ff_cases h s hc c⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly
