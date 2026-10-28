module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.NaturalOrder
public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.Order120
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction

/-!
# Completing the four-dimensional branch of the original HS action

The literal normal residual acts naturally and the whole dotted group has
order 120. Its entire faithful action therefore has equivariant coordinates
in the specified SL₂(4)-by-field-automorphism model. The existing kernel
bridge transports these coordinates to H/O₂(H). The checked source assembly
then constructs the cyclic-four center, the original component and its
movement and indecomposability, and applies the literal LocalStructure
consumer.

The final reduction retains only the higher-dimensional whole-component
branch. Its recognition remains with this task; the preceding centerlessness
premise remains with qt-d-hs-local-structure.
Source: Aschbacher--Smith 14.3.23(2)(ii), 14.3.24 and 14.3.32,
printed pp.1000,1003--1004.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
include d earlier hq chosen structural alternatives hne hZ hI

/-- The full original dotted action is the specified natural semilinear model. -/
theorem source_four_dotted_natural
    (hd : finrank (ZMod 2) (Additive F.Uhat)=4) : DottedNaturalCoordinates F := by
  obtain ⟨e,c,he⟩ := source_four_residual_concrete_coordinates d earlier hq chosen structural alternatives
    F hne hZ hI hd
  obtain ⟨E,C,hE⟩ := SL2FourNatural.SemilinearNormalizer.coordinates_of_order_oneTwenty
    F.terminalRepresentation F.terminalRepresentation_injective
    (source_four_card_oneTwenty d earlier hq chosen structural alternatives F hne hZ hI hd)
    (solvableResidual F.TerminalHdot) e c he
  refine ⟨E,C.toAddEquiv.toMultiplicativeRight,?_⟩
  intro a w
  exact hE (QuotientGroup.mk' F.terminalHatAction.ker a) (Additive.ofMul w)

/-- The complete ActionStructure contract in the original four-dimensional branch. -/
theorem source_four_actionStructure
    (hd : finrank (ZMod 2) (Additive F.Uhat)=4) : ActionStructure F :=
  actionStructure_of_dotted_natural d earlier hq chosen structural alternatives F hne hZ hI
    (source_four_dotted_natural d earlier hq chosen structural alternatives F hne hZ hI hd)

/-- Apply the four-dimensional action to the literal local-structure consumer. -/
theorem source_four_localStructure
    (hd : finrank (ZMod 2) (Additive F.Uhat)=4) : LocalStructure L F :=
  localStructure_of_centerless_action d earlier hq chosen structural alternatives F hne hI
    (source_four_actionStructure d earlier hq chosen structural alternatives F hne hZ hI hd)

omit [IsElementaryAbelian 2 F.Uhat] in
/-- Only the whole-component recognition branch remains before ActionStructure. -/
theorem source_action_or_whole_recognition_of_centerless
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ActionStructure F ∨
    ∃ heU : IsElementaryAbelian 2 F.Uhat, letI := heU
    ∃ heX : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := heX
    ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) ∧
      ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      ChapterG.Section11.NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      IsIrreducible F.terminalRepresentation ∧
      6 ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
      ¬ Group.IsSolvable F.TerminalHdot ∧
      ∃ J : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot J ∧
        ⁅J,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
        ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B J ∧
        ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
          F.terminalRepresentation (F.terminalDot (F.X g)) J (componentOrbit J ⊤)
          (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∧
        ChapterG.Section11.WholeComponentCandidates.Alternatives F.terminalRepresentation J
          (componentOrbit J ⊤) := by
  obtain ⟨heU,heX,B,v,hyp,hline,hw,hn,hi,hs,hcases⟩ :=
    source_nonsolvable_four_or_whole_recognition_of_centerless d earlier hq chosen structural
      alternatives F hne hZ hI g hgP hgH
  let := heU
  let := heX
  rcases hcases with ⟨hfour,_,_⟩ | hwhole
  · exact .inl (source_four_actionStructure d earlier hq chosen structural alternatives
      F hne hZ hI hfour.1)
  · exact .inr ⟨heU,heX,B,v,hyp,hline,hw,hn,hwhole⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
