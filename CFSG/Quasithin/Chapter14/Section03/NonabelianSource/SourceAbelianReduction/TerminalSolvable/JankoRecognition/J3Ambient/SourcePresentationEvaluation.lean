module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.SourceThreePairModels
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.PresentationEvaluation

/-!
# The original terminal source evaluates the literal amalgam presentation

The complete original source prefix constructs its actual local models and
all pointwise overlap identifications. Evaluating through those models gives
an actual six-tuple satisfying the twenty-two relations and a surjection onto
the original group. No global finite certificate is required for this map.
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

/-- The complete original terminal source hypotheses construct an actual
six-tuple satisfying all twenty-two literal amalgam relations, with
surjective evaluation. No maps or relations are additional hypotheses. -/
theorem source_single_a5_j3_presentation_evaluation_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) :
    ∃ (g : Fin 6 → G) (hs : Sporadic.Janko3.AmalgamPresentation.Satisfies g),
      Function.Surjective (Sporadic.Janko3.AmalgamPresentation.evaluation hs) := by
  obtain ⟨hc,D,P,eR,_hHK,_hHz,_hcore,_hneP,_hsup,_hinf,hfields⟩ :=
    source_single_a5_j3_three_pair_models_of_four
      hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  obtain ⟨_hAE,_hAc,C,l,a,hC,ha,j,hj,_⟩ :=
    hfields (P.A₁ eR) (Or.inl rfl)
  exact J3Ambient.literal_presentation_evaluation P hc (P.A₁ eR) C l a hC ha j hj

/-- The original terminal source therefore receives a surjective
homomorphism from the actual literal twenty-two-relator carrier. -/
theorem source_single_a5_j3_presentation_surjection_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) :
    ∃ φ : Sporadic.Janko3.AmalgamPresentation.Carrier →* G, Function.Surjective φ := by
  obtain ⟨g,hs,honto⟩ := source_single_a5_j3_presentation_evaluation_of_four
    hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  exact ⟨Sporadic.Janko3.AmalgamPresentation.evaluation hs,honto⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
