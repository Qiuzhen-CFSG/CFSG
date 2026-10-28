module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.FullLinearExclusion
public import CFSG.Quasithin.ChapterG.Section11.LargeActorExchangedExclusion

/-!
# The earlier HS action after eliminating exchanged constituents

The original nonextraspecial flag supplies all G.11 inputs and the
half-degree actor bound, before any centerlessness assumption. Its seed
plane excludes the exceptional whole S₈ action. The large-actor theorem
excludes all remaining exchanged natural constituents, and the same bound
excludes the solvable degree-six remainder.

The literal action therefore satisfies the printed catalogue or the
whole-component G.9 recognition hypothesis. The latter recognition and
the marked catalogue exclusions remain obligations of qt-d-hs-action-source;
this is not yet the full 14.3.24 alternative or the later natural action.
Source: Aschbacher--Smith 14.3.12--14 and 14.3.23--24,
printed pp.993--994,999--1000, with the corrected G.11 reduction.
-/

public section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open ChapterG.Section11 ChapterG.Section11.ExchangedRecognition
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original nonextraspecial flag reaches the printed G.11 catalogue or
its whole-component recognition problem. Every exchanged constituent and
the exceptional whole S₈ action are excluded using the actual source data.
No centerlessness or later natural-action conclusion is used. -/
theorem source_earlier_whole_component_reduction (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ heU : IsElementaryAbelian 2 F.Uhat, letI := heU
    ∃ heX : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := heX
    ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) ∧
      LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      (Conclusion F.terminalRepresentation B (F.terminalDot (F.X g)) ∨
        (IsIrreducible F.terminalRepresentation ∧
          6 ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
          ¬ Group.IsSolvable F.TerminalHdot ∧
          ∃ J : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot J ∧
            ⁅J,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
            ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B J ∧
            ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
              F.terminalRepresentation (F.terminalDot (F.X g)) J (componentOrbit J ⊤)
              (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))))) := by
  obtain ⟨heU,heX,B,v,hyp,hline,hcover,hn,_⟩ :=
    source_earlier_classification_input d earlier hq chosen structural alternatives F hne g hgP hgH
  let := heU
  let := heX
  have hw := source_earlier_lowRank d earlier hq chosen structural alternatives F hne hZ g hgP hgH v hline
  have hlarge := source_earlier_dimension_le_twice_actor d earlier hq chosen structural alternatives
    F g hne hZ hgP hgH
  refine ⟨heU,heX,B,v,hyp,hline,hw,hn,?_⟩
  rcases corrected_conclusion_or_remaining hyp hcover hw hn with (hc | hex) | ⟨hi,hd,hs | ⟨hnon,hrem⟩⟩
  · exact Or.inl hc
  · exact (source_no_full_linear_alternative d earlier hq chosen structural alternatives F hne
      B v _ _ _ hex).elim
  · obtain ⟨_,hr,hd⟩ := hs
    omega
  · exact Or.inr ⟨hi,hd,hnon,whole_of_remaining_of_large hyp hcover hw hn hnon hlarge hrem⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
