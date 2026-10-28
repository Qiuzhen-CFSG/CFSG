module

public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.QuasisimpleAction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.C27Source.LocalClauses

/-!
# B.5.1 on D's literal fixed-centralizer star action

The original Case supplies the genuine C.2.7 input and relative component
normality. Its original star action, restricted to its offender-generated
subgroup, therefore has the full moved-section conclusion of B.5.1.
There is no representation model, classifier or kernel premise.

Source: Aschbacher--Smith 14.7.68(2), pp.1071–1072, via C.2.7(!), p.146.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

theorem fixedComponent_C27_quasisimple_action
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu) :
    let R := d.fixedCore u
    let ρ := starRepresentation Lu R
    let J := offenderSubgroup ρ
    starImage Lu R Lu ≤ J ∧
    Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp J.subtype) ((starImage Lu R Lu).subgroupOf J)) := by
  let : (Lu.subgroupOf (d.fixedCentralizer u)).Normal := h.normal
  exact ChapterC.C27Source.star_moved_section_conclusion
    (d.fixedComponent_C27_input Nonquasisimple.earlier1211_source u h
      d.point_mem_U_commutator_K)

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
