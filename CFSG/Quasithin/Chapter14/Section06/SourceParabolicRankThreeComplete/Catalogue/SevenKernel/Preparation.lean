module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.MSRestriction
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Catalogue.SevenKernel.Inputs
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Catalogue.Preparation
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.Setup

/-!
# Original action and MS preparation for A₇ block selection

The original C.2.7 input supplies the complete star-action data and the MS
conditions on the same component-radical product. All local-Sylow and escape
premises are discharged here. The first core is not asserted to be Sylow.

Source: Aschbacher--Smith C.2.7, pp.145--147, and original 14.6.10(5), p.1029.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue.SevenKernel
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

variable (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (d : SourceSecondParabolicData
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) Mc M)
    (I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({d.u} : Set G)) Mc M))

include hG hempty hM hunique hmany hcard e hab H hH d hI

/-- The full original action is classified before its cubic kernel is removed. -/
theorem generated_actionData
    (eC : star T M Mc I d.H2 ≃* alternatingGroup (Fin 7)) :
    Nonempty (Data T M Mc I d.H2) :=
  actionData (prepared hG T hempty hM hunique hmany hcard e hab H hH d I hI).1 eC

/-- Both structural MS conditions on the literal component-radical product.
No Sylow or preferred-centralizer assumption is added. -/
theorem generated_join_ms_inputs :
    let C := sourceGeneratedComponent T M Mc I d.H2
    let R := firstCore T M Mc I d.H2
    ChapterC.MSOddIndexRadical (R.subgroupOf (C ⊔ R)) ∧
      ChapterC.MSCharacteristicCondition (R.subgroupOf (C ⊔ R)) ∧
      generalizedFitting (C ⊔ R : Subgroup G) = pCore 2 (C ⊔ R : Subgroup G) := by
  have hi := (prepared hG T hempty hM hunique hmany hcard e hab H hH d I hI).1
  have hr := (Seven.generated_ms_inputs hG T hempty hM hunique hmany hcard e hab H hH d I hI).2.1
  exact ⟨msOddIndexRadical_join_from_source hi hr,
    join_msCharacteristic_from_source hi,source_join_fitting hi⟩

end CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue.SevenKernel
