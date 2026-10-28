module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Source
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.Complete

/-!
# Original 13.6.13 over the full known-simple catalogue

The established A.2, A.3.6, B.4.2 and B.5 theorems supply all five earlier
source implications and the adequate classifier. Thus the solvable exclusion
retains only the actual local marked setup and the contrary nonnormality of
V_v from 13.6.8. No universal classification premise remains.
Source: Aschbacher--Smith, combined manuscript, 13.6.13, printed p.929.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable
open Construction
open ChapterB.SourceInduction ChapterB.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction
universe u

/-- The complete earlier classification inputs on the genuine known-simple catalogue. -/
theorem knownSimpleEarlier : Exceptional.SourceAction.PreciseInputs.{u,u} KnownSimple.IsKnownSimple := by
  have hA : SemisimpleInput.{u} KnownSimple.IsKnownSimple :=
    fun _ _ _ => ChapterA.Section02.theoremA_knownSimple
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have h4 := ChapterB.SourceClassification.irreducibleClassification_knownSimple
  exact {
    quasisimple := ChapterB.QuasisimpleSource.SourceCompletion.knownSimple_quasisimpleClassificationInput
      hA h36 h4 nonbinaryG2RootPairInput
    cover := coverInput_of_a36 h36
    semisimple := hA
    preparation := ChapterB.PreparationSource.componentInput
      ChapterB.PreparationSource.componentNormalization hA h36 h4
    structure36 := h36 }

variable {G : Type u} [Group G] [Finite G] {L V : Subgroup G}
    (s : A5Module.Marking L V) (T : Subgroup G)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ s) (A5Module.markedV s))]
    (S : Sylow 2 (Gv (A5Module.markedV s)))
    (hS : (S : Subgroup (Gv (A5Module.markedV s))).map
      (Gv (A5Module.markedV s)).subtype = Tv T (A5Module.markedV s))
    (hfix : Tv T (A5Module.markedV s) ≤ centralizer ({A5Module.markedZ s} : Set G))
    (hT : Tv T (A5Module.markedV s) ≤ normalizer (Lv L (A5Module.markedV s) : Set G))
    (hV : IsPGroup 2 V)
    (hL : Lv L (A5Module.markedV s) ≤ normalizer (V : Set G))
    (hcubic : Nat.card (Lv L (A5Module.markedV s) ⧸ pCore 2 (Lv L (A5Module.markedV s))) = 3)
    (hsplit : Vv L (A5Module.markedZ s) (A5Module.markedV s) =
      zpowers (A5Module.markedV s) ⊔ ⁅V, Lv L (A5Module.markedV s)⁆)
    (hsmall : Nat.card ↥(⁅V, Lv L (A5Module.markedV s)⁆ : Subgroup G) = 4)
    (hnormal : ¬ ((Vv L (A5Module.markedZ s) (A5Module.markedV s)).subgroupOf
      (Gv (A5Module.markedV s))).Normal)

include S hS hfix hT hV hL hcubic hsplit hsmall hnormal

/-- Original 13.6.13 with every earlier universal source theorem discharged. -/
theorem no_solvable_member_knownSimple
    (hlocal : IsSQTK KnownSimple.IsKnownSimple (Gv (A5Module.markedV s))) :
    ∀ X ∈ XFamily L T (A5Module.markedZ s) (A5Module.markedV s), ¬ Group.IsSolvable X :=
  no_solvable_member_of_earlier_source s T S hS hfix hT hV hL hcubic hsplit hsmall hnormal
    knownSimpleEarlier adequateClassification_knownSimple hlocal

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable
