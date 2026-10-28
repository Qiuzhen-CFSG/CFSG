module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.SourceGenerators.LinearSubgroup
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J2Source

/-!
# Explicit source contract for the original J₃ terminal row

The ATLAS presentation comparison and the linear-subgroup transport are
already kernel-checked.  This module combines them at the literal terminal
consumer.  It deliberately keeps the source obligations explicit: a finite
presentation with the 50,232,960 upper bound, an ATLAS generating pair in the
ambient group, an order-243 subgroup, and an injective copy of the genuine
`L₂(16):2` extension.  These are the precise hypotheses removed by the
Thompson--Higman--McKay source argument; `J3Type` alone does not provide them.

Source: Aschbacher--Smith I.4.7(2), printed p.418, and the retained ATLAS
J3G1-P1 presentation.
-/

public section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

namespace JankoRecognition

/-- The exact conditional J₃ recognition contract used by the terminal row.
The `L₂(16):2` embedding supplies the independent order lower bound through
its normal `L₂(16)` subgroup and an order-243 subgroup supplies the cubic
factor. -/
theorem source_j3_equiv_of_linear_extension
    {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hJ3 : Janko23.J3Type G)
    (hgen : Sporadic.Janko3.RecognitionPresentation.HasGenerators G)
    (hfinite : Finite Sporadic.Janko3.RecognitionPresentation.Presentation)
    (hbound : Nat.card Sporadic.Janko3.RecognitionPresentation.Presentation ≤ 50232960)
    (P : Subgroup G) (hP : Nat.card P = 243)
    (f : Theory.PSL2.BinaryFourFieldExtension.Model →* G)
    (hf : Function.Injective f) :
    Nonempty (G ≃* Sporadic.Janko3.Model) := by
  let := hfinite
  let := hG.simple
  have hcard : 50232960 ≤ Nat.card G :=
    Janko23.J3Recognition.LinearSubgroup.card_lower_bound_of_embedding
      hJ3 hgen P hP f hf
  exact Janko23.J3Recognition.recognition_of_generators hgen hcard hbound

/-- Literal terminal-solvability consumer with the J₃ source contract
specialized at the original `M`, `Mᶜ`, flag and marked Borel branch. -/
theorem source_terminal_solvable_of_j3_linear_extension_eight_exclusion
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
    (hgen : Sporadic.Janko3.RecognitionPresentation.HasGenerators G)
    (hfinite : Finite Sporadic.Janko3.RecognitionPresentation.Presentation)
    (hbound : Nat.card Sporadic.Janko3.RecognitionPresentation.Presentation ≤ 50232960)
    (P : Subgroup G) (hP : Nat.card P = 243)
    (f : Theory.PSL2.BinaryFourFieldExtension.Model →* G)
    (hf : Function.Injective f)
    (height : ∀ K : Subgroup G, ComponentLift F g K → EightImageRow F K → False) :
    Group.IsSolvable F.TerminalHdot := by
  exact source_terminal_solvable_of_j3_recognition_eight_exclusion
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH
    (fun hJ3 => source_j3_equiv_of_linear_extension hG hJ3 hgen hfinite hbound P hP f hf)
    height

end JankoRecognition

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
