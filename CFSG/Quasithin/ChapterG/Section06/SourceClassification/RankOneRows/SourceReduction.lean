module

public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.RankOneRows.Quasisimple
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.CentralSylow

/-!
# Remaining original G.6.4 source obligations after rank-one row selection

Complete B.5 source induction supplies the original normal-closure data.
Rank-one row selection now proves all repeated binary linear branches and
excludes the doubled and natural-plus-dual branches without a cubic premise.
The residual quasisimple branch retains its full B.5 source conclusion and
the literal faithful irreducible quotient action for kernel reconstruction.
On the actual two-central domain the two-factor branch is also discharged.

Source: Aschbacher–Smith G.6.4, printed pp.345–346.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterG.Section06
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
open HighThreeRank.CoverCentralizer.SourceConstruction
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {a : G}
  {Cover : Type u} [Group Cover] {q : Cover →* G}

/-- The genuine remaining quasisimple action, including its original full
source data for reconstructing the central extension. -/
@[expose] def IrreducibleQuasisimpleRemainder (ρ : Representation (ZMod 2) G V) (a : G) : Prop :=
  IsQuasisimple (generalizedFitting (normalClosure ({a} : Set G))) ∧
  ∃ d : ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (normalClosure ({a} : Set G)).subtype)
      (generalizedFitting (normalClosure ({a} : Set G))),
    d.sectionData.space.toSubmodule = ⊤ ∧
    IsIrrPlus (ρ.comp (normalClosure ({a} : Set G)).subtype)
      (generalizedFitting (normalClosure ({a} : Set G))) d.sectionData.space.toSubmodule ∧
    Function.Injective d.sectionData.action ∧
    IsIrreducible (d.sectionData.action.comp
      (generalizedFitting (normalClosure ({a} : Set G))).subtype) ∧
    ProjectiveLine.IrreducibleActionCase d.sectionData.action
      (generalizedFitting (normalClosure ({a} : Set G))) ⊤

theorem Hypotheses.rank_one_irreducible_source_reduction
    (hA : SemisimpleInput.{u} KnownSimple.IsKnownSimple)
    (h36 : Chapter1.Section02.A36Input.{u} KnownSimple.IsKnownSimple)
    (h4 : ProjectiveLine.IrreducibleClassificationInput.{u,v} KnownSimple.IsKnownSimple)
    (h : Hypotheses KnownSimple.IsKnownSimple ρ a q)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1) :
    Conclusion ρ a ∨ IrreducibleQuasisimpleRemainder ρ a ∨
      Nonempty (SourceTwoFactorCase (ρ.comp (normalClosure ({a} : Set G)).subtype)) := by
  rcases h.rank_one_source_reduction hA h36 h4 ht with hc | hh
  · exact Or.inl hc
  · rcases hh with ⟨hq,⟨d⟩⟩ | hd
    · rcases h.quasisimple_rank_one_rows ht hq d with hc | hi
      · exact Or.inl hc
      · exact Or.inr (Or.inl ⟨hq,d,hi⟩)
    · exact Or.inr (Or.inr hd)

/-- Actual two-central inputs now leave only the irreducible central-extension
reconstruction; no original B.5 factor or reducible action row remains. -/
theorem Hypotheses.rank_one_twoCentral_irreducible_source_reduction
    (hA : SemisimpleInput.{u} KnownSimple.IsKnownSimple)
    (h36 : Chapter1.Section02.A36Input.{u} KnownSimple.IsKnownSimple)
    (h4 : ProjectiveLine.IrreducibleClassificationInput.{u,v} KnownSimple.IsKnownSimple)
    (h : Hypotheses KnownSimple.IsKnownSimple ρ a q)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (S : Sylow 2 G) (hz : a ∈ (center S).map (S : Subgroup G).subtype) :
    Conclusion ρ a ∨ IrreducibleQuasisimpleRemainder ρ a := by
  rcases h.rank_one_irreducible_source_reduction hA h36 h4 ht with hc | hh
  · exact Or.inl hc
  · rcases hh with hi | hd
    · exact Or.inr hi
    · obtain ⟨d⟩ := hd
      exact (h.not_two_factors_of_twoCentral ht d S hz).elim
end CFSG.Quasithin.ChapterG.Section06
