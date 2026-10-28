module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.ExchangedNatural
public import CFSG.Quasithin.ChapterG.Section11.LargeActorCatalogue
public import CFSG.Quasithin.ChapterG.Section11.WholeComponentCandidates

/-!
# The original HS action after the numerical catalogue exclusions

The source half-degree bound excludes the solvable six-dimensional row and
all printed rows (7)--(13), using their literal model actions. Together with
the original seed dimension and the already checked exchanged-constituent
exclusions, this leaves rows (2), (4), (5), (6) or whole-component recognition. On a single whole component the genuine G.9
carrier catalogue and its proved exclusions leave the literal carrier list;
the two-component branch retains distinct components and its action intertwiners.
All marking, Sylow normality and component hypotheses concern the original
rank-three flag. Centerlessness is not used in this earlier reduction.

The remaining recognition and source exclusions belong to this task;
no complete G.11 classifier or strict-D conclusion is assumed.
Source: Aschbacher--Smith 14.3.23--24, pp.999--1000, and G.11.2, p.364.
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

/-- Apply the literal catalogue sieve to the original HS flag, retaining the
whole-component recognition obligation with all its original hypotheses. -/
theorem source_earlier_remaining_action (d : Counterexample T L)
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
      ((CaseTwo F.terminalRepresentation B ∨ CaseFour F.terminalRepresentation ∨
          CaseFive F.terminalRepresentation B ∨ CaseSix F.terminalRepresentation) ∨
        (IsIrreducible F.terminalRepresentation ∧
          6 ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
          ¬ Group.IsSolvable F.TerminalHdot ∧
          ∃ J : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot J ∧
            ⁅J,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
            ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B J ∧
            ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
              F.terminalRepresentation (F.terminalDot (F.X g)) J (componentOrbit J ⊤)
              (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∧
            WholeComponentCandidates.Alternatives F.terminalRepresentation J
              (componentOrbit J ⊤))) := by
  obtain ⟨heU,heX,B,v,hyp,hline,hw,hn,hcases⟩ :=
    source_earlier_whole_component_reduction d earlier hq chosen structural alternatives
      F hne hZ g hgP hgH
  let := heU
  let := heX
  refine ⟨heU,heX,B,v,hyp,hline,hw,hn,?_⟩
  rcases hcases with hc | hwhole
  · left
    let := chosen.elementary
    obtain ⟨htwo,hphi,hvc⟩ := source_closure d earlier hq chosen structural alternatives F hne
    exact LargeActorCatalogue.remaining_rows
      (source_earlier_dimension_le_twice_actor d earlier hq chosen structural alternatives
        F g hne hZ hgP hgH) hyp (CaseOneLarge.source_terminal_cover F d chosen) hw
      (quotient_dimension F htwo hphi hvc).1 hc
  · obtain ⟨hi,hd,hnon,J,hJ,hm,horth,h9⟩ := hwhole
    exact .inr ⟨hi,hd,hnon,J,hJ,hm,horth,h9,
      WholeComponentCandidates.component_candidates hyp h9 hw hd
        (source_earlier_dimension_le_twice_actor d earlier hq chosen structural alternatives
          F g hne hZ hgP hgH)⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
