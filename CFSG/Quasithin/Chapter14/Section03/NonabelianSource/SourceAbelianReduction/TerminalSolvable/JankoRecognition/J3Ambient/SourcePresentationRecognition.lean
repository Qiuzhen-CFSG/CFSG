module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.SourcePresentationEvaluation
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.SourceSmallCoverRecognition
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Order

/-!
# Recognition of the original terminal source from the certified amalgam

The original geometry supplies a six-tuple satisfying all twenty-two literal
relations and a surjective evaluation. The independent universal certificate
bounds its carrier by three times the order of J₃. The two actual evaluations
therefore identify the original group with the concrete J₃ model, with no
remaining cover, generator, relation, or local comparison hypothesis.
-/

public noncomputable section
open Subgroup
open Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Janko23.J3Recognition.LocalSixteen Janko23.J3Recognition.Ambient
open Janko23.J3Recognition.Ambient.Seventeen
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics

variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (hnot : ¬ ClassificationModels.IsTheoremEModel G) (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    {K : Subgroup G} (hK : ComponentLift F g K)
include hG hempty hM hu hmany hcard e hne hnot hgP hgH hyp hK

open Sporadic.Janko3.AmalgamPresentation

/-- The original six-tuple and both certified evaluations identify the
original group with the concrete model, retaining the commuting diagram. -/
theorem source_single_a5_j3_marked_equiv_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) :
    ∃ (gs : Fin 6 → G) (hs : Satisfies gs) (ι : Sporadic.Janko3.Model ≃* G),
      Function.Surjective (evaluation hs) ∧
      ι.toMonoidHom.comp ModelCoordinates.modelEvaluation = evaluation hs := by
  let : Finite Carrier := finite_card.1
  obtain ⟨gs,hs,honto⟩ := source_single_a5_j3_presentation_evaluation_of_four
    hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  obtain ⟨ι,hι⟩ := source_single_a5_j3_equiv_of_small_cover_of_four
    hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
      ModelCoordinates.modelEvaluation ModelCoordinates.modelEvaluation_surjective
      (evaluation hs) honto finite_card.2
  exact ⟨gs,hs,ι,honto,hι⟩

/-- The complete original terminal prefix forces the concrete J₃ model. -/
theorem source_single_a5_j3_equiv_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) :
    Nonempty (Sporadic.Janko3.Model ≃* G) := by
  obtain ⟨_gs,_hs,ι,_⟩ := source_single_a5_j3_marked_equiv_of_four
    hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  exact ⟨ι⟩

/-- The dimension-four single-A₅ terminal branch contradicts the original
assumption that the ambient group is outside the Theorem E model list. -/
theorem source_single_a5_j3_excluded_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) : False := by
  obtain ⟨ι⟩ := source_single_a5_j3_equiv_of_four
    hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  exact hnot (.janko_three ⟨ι.symm⟩)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
