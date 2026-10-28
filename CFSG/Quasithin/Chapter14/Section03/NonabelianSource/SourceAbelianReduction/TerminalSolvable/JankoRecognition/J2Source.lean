module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueSourceSingleFourJanko

/-!
# The original J₂ branch of terminal solvability

Original `IsSimpleQTKE` supplies the simplicity needed by the genuine I.4.7(1)
specialization. Its conclusion is an equivalence to the actual ATLAS J₂ carrier,
so the J₂ alternative contradicts the original non-model hypothesis. The literal
terminal-solvability application below removes exactly its J₂ recognition input;
J₃ recognition and the independent exact L₂(8) exclusion remain explicit.

Source: Aschbacher–Smith I.4.7(1), p.418, and 14.3.15, p.994; Aschbacher,
*Sporadic Groups* (1994), §§37 and 47.
-/

public section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

namespace JankoRecognition
/-- The original simple-source J₂ type recognizes the concrete carrier. -/
theorem source_j2_equiv {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : Janko23.J2Type G) :
    Nonempty (G ≃* Sporadic.LeechRelated.J2.Carrier) := by
  let := hG.simple
  exact Janko23.J2Recognition.recognition h

/-- The literal theorem-E model consequence in the original terminal context. -/
theorem source_j2_isTheoremEModel {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : Janko23.J2Type G) :
    ClassificationModels.IsTheoremEModel G :=
  .janko_two (source_j2_equiv hG h)
end JankoRecognition

/-- Apply the J₂ producer to the unchanged original terminal consumer. Only
J₃ recognition and the exact eight-row exclusion remain as independent inputs. -/
theorem source_terminal_solvable_of_j3_recognition_eight_exclusion
    {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hJ3 : Janko23.J3Type G → Nonempty (G ≃* Sporadic.Janko3.Model))
    (height : ∀ K : Subgroup G, ComponentLift F g K → EightImageRow F K → False) :
    Group.IsSolvable F.TerminalHdot := by
  exact source_terminal_solvable_of_janko_recognition_eight_exclusion
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH
    (JankoRecognition.source_j2_equiv hG) hJ3 height

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
