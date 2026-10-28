module
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.Source
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.CoreNoncentral

/-!
# The original 15.3.7--9 source application

The original empty faithful-component family and binary central seed force
strict growth of the two-core in M ∩ Mc. Thus the same intersection core acts
nontrivially on the actual natural orthogonal module. The preceding source
assembly now supplies every residual input, both complete three-group
alternatives, and the strict-core/wreath exclusion, without any 14.1.17
callback or local noncentrality premise.

The natural action and distinct ordering maximum are exactly the preceding
15.1.3 and 14.1.12 outputs. Construction of those earlier source outputs remains
with their source producers. Source: Aschbacher--Smith, printed pp.1122--1123.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03
open ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem original_residual_inputs
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (d : NaturalOrthogonalAction M (localModule T M))
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) (hne : Mc ≠ M) :
    ResidualEarlierInputs M Mc (localModule T M) T :=
  residualEarlierInputs_from_source hG T d hM hu hne
    (intersection_core_noncentral_from_source hG T hempty d hM hu hmany hne)

theorem source_lemma_15_3_7_of_orthogonal_action
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (d : NaturalOrthogonalAction M (localModule T M))
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) (hne : Mc ≠ M) :
    ((residualY M Mc).subgroupOf M).map d.actor =
        twoResidualAmbient (⊤ : Subgroup OrthogonalActor) ∧
    M ⊓ Mc = (M ⊓ centralizer (localModule T M : Set G)) ⊔ (T : Subgroup G) ∧
    ((M ⊓ Mc : Subgroup G) : Set G) =
      ((M ⊓ centralizer (localModule T M : Set G) : Subgroup G) : Set G) * (T : Set G) ∧
    M = normalizer (residualY M Mc : Set G) ∧
    Chapter4.UniqueMaximalOvergroup (residualY M Mc ⊔ (T : Subgroup G)) M ∧
    (residualY M Mc ⊔ (T : Subgroup G)).pCoreIn 2 =
      (T : Subgroup G) ⊓ centralizer (localModule T M : Set G) ∧
    (ThreeAlternatives.ElementaryAlternative M Mc (localModule T M) ∨
      ThreeAlternatives.ExtraspecialAlternative M Mc (localModule T M) d) :=
  lemma_15_3_7_from_earlier_source M Mc (localModule T M) T d
    (original_residual_inputs hG T hempty d hM hu hmany hne)

theorem source_lemma_15_3_9_of_orthogonal_action
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (d : NaturalOrthogonalAction M (localModule T M))
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) (hne : Mc ≠ M) :
    localModule T M < (residualY M Mc).pCoreIn 2 ∧
      ¬ Nonempty (residualY M Mc ≃* (alternatingGroup (Fin 4) × alternatingGroup (Fin 4))) :=
  source_lemma_15_3_9 hG T d hM hu hne
    (intersection_core_noncentral_from_source hG T hempty d hM hu hmany hne)

end CFSG.Quasithin.Chapter15.Section03
