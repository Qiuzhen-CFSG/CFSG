module
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.OriginalSource
public import Theory.GroupTheory.ConjugateSpanSupplement

/-!
# The residual generates the original central seed module

The actual Y image is O² of the orthogonal actor. Its join with the
original Sylow image is therefore the full actor, so the A.5 product
factorization gives V(M)=⟨Z^(YT)⟩. Since T normalizes Y and centralizes Z,
the latter span is exactly ⟨Z^Y⟩. Both the residual image and its normalizer
are instantiated from the original 15.3.7 source assembly.

Source: Aschbacher--Smith 15.3.7 and its use in 15.3.11, pp.1122--1124.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03
open ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The exact seed-span consequence of the residual image and relative normality. -/
theorem NaturalOrthogonalAction.localSpan_eq_of_residual_image
    (T : Sylow 2 G) {M Y : Subgroup G}
    (d : NaturalOrthogonalAction M (localModule T M))
    (hTM : (T : Subgroup G) ≤ M) (hYM : Y ≤ M)
    (hNY : M ≤ normalizer (Y : Set G))
    (himage : d.image Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) :
    localSpan (centralInvolutions T) Y = localModule T M := by
  have hfull : d.image (Y ⊔ (T : Subgroup G)) = ⊤ := by
    change ((Y ⊔ (T : Subgroup G)).subgroupOf M).map d.actor = ⊤
    rw [subgroupOf_sup hYM hTM,Subgroup.map_sup]
    change d.image Y ⊔ d.image (T : Subgroup G) = ⊤
    rw [himage]
    exact twoResidualAmbient_top_sup_sylow (d.sylowImage T hTM)
  have hspan := (d.orderingLE_of_image_eq_top T hfull).span_le
  have hZ : (T : Subgroup G) ≤ normalizer (centralInvolutions T : Set G) :=
    (le_centralizer_iff.mpr (centralInvolutions_le_centralizer_sylow T)).trans
      (Subgroup.centralizer_le_normalizer _)
  rw [conjugateSpanBy_sup_of_normalizes_seed _ _ _ hZ (hTM.trans hNY)] at hspan
  exact le_antisymm (conjugateSpanBy_mono le_rfl hYM) hspan

/-- Original 15.3.7 supplies the exact residual span needed by every outside choice. -/
theorem source_residual_seed_span
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (d : NaturalOrthogonalAction M (localModule T M))
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) (hne : Mc ≠ M) :
    localSpan (centralInvolutions T) (residualY M Mc) = localModule T M := by
  obtain ⟨hi,_,_,hn,_,_,_⟩ :=
    source_lemma_15_3_7_of_orthogonal_action hG T hempty d hM hu hmany hne
  exact d.localSpan_eq_of_residual_image T hM.1.2
    (Chapter14.SourcePreliminaries.sourceResidual_le M Mc) hn.le hi

end CFSG.Quasithin.Chapter15.Section03
