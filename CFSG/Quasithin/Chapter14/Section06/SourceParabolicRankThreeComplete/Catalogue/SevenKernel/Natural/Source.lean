module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Catalogue.SevenKernel.Natural.Selection
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Catalogue.SevenKernel.Natural.Coordinates
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Catalogue.SevenKernel.Natural.PairGeometry
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Catalogue.SevenKernel.Natural.Thompson

/-!
# Original natural A₇ block selection

The local maximum-elementary images generate a nonempty group of commuting
transpositions. Pair fixed-space geometry then identifies the actual Baumann
image, and the relative cubic seed propagates to the original component.
The literal action data and source saturation discharge all group, module,
radical and kernel premises. No Sylow assumption on the first core is added.

Source: Aschbacher--Smith C.1.24(a), C.2.7 and original14.6.10(5),
pp.130--131, 145--147 and 1029.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue.SevenKernel.Natural
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The literal C.2.7 consumer of the relative natural selection theorem. -/
theorem selection_from_source
    (hth : RelativeThompsonInput.{u}) (hgeom : PairGeometryInput)
    {H K R M : Subgroup G} (h : Input KnownSimple.IsKnownSimple H R M K)
    (m : Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.AlternatingModels.ActionData
      (starRepresentation K R) (starImage K R K))
    (a : Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.ActionEquiv
      m.sectionData.space.toRepresentation (BinaryPermutation.naturalRepresentation (Fin 7)))
    (ha : (starImage K R K).map a.groupEquiv.toMonoidHom = alternatingGroup (Fin 7)) :
    SelectionConclusion K R := by
  let J := K ⊔ R
  let L := K.subgroupOf J
  let R₀ := R.subgroupOf J
  let : L.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer h.normalizes)
  let eL : L ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  let : IsQuasisimple (K ⧸ pCore 2 K) := h.quasisimple
  let : IsQuasisimple (L ⧸ pCore 2 L) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ eL (pCore_map_iso 2 eL)).symm
  have hfL : generalizedFitting L = pCore 2 L := by
    apply map_injective (f := eL.toMonoidHom) eL.injective
    rw [map_generalizedFitting_equiv, pCore_map_iso, h.fitting]
  have hgen : L ⊔ R₀ = ⊤ := by
    rw [←subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  obtain ⟨hc, s, hs, he⟩ := naturalMap_module m a
  obtain ⟨⟨P,hP⟩,hcore⟩ := naturalMap_kernel_sylow h m a ha
  exact selection_of_coordinates hth hgeom L (starV K R)
    (source_join_input h).component.2 (source_join_fitting h) hfL R₀
    (source_relative_radical h).isPGroup (source_relative_radical h).1
    (relative_core_le h) hgen (naturalMap m a) (naturalMap_surjective m a)
    (naturalMap_ker m a) (naturalMap_component m a ha) hc s hs he P hP hcore

/-- Original Chapter 14 assembly. Both independent geometric inputs remain
explicit; all original source hypotheses and the actual first core are retained. -/
theorem natural_selection_of_geometry
    (hth : RelativeThompsonInput.{u}) (hgeom : PairGeometryInput)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc)) :
    NaturalSelectionInput hG T hempty hM hunique hmany hcard e hab := by
  intro H hH d I hI _ m hm
  obtain ⟨a, ha⟩ := hm
  exact selection_from_source hth hgeom
    (prepared hG T hempty hM hunique hmany hcard e hab H hH d I hI).1 m a ha

/-- Natural relative block selection under the unchanged original Chapter 14
hypotheses. The Thompson and pair-geometry premises are fully discharged. -/
theorem naturalSelectionInput
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc)) :
    NaturalSelectionInput hG T hempty hM hunique hmany hcard e hab :=
  natural_selection_of_geometry relative_thompson pair_geometry
    hG T hempty hM hunique hmany hcard e hab

end CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue.SevenKernel.Natural
