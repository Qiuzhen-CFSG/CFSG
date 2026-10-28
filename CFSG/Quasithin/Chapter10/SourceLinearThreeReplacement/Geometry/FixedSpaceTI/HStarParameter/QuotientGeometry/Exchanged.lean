module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry.Pair
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry.Recognition
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry.Dihedral

/-!
# Whole-group recognition in the exchanged H-star branch

The same centralizer quotient carries the pair residual, faithful wreath
embedding, original Sylow image, and maximal-overgroup image. Its overlap
retains the S₃ wr C₂ quotient because the centralizer kernel is a two-group
in the exchanged branch. The order argument then makes the embedding onto,
giving an actual isomorphism H/C_H(U) ≃ S₅ wr C₂.

The original overlap also has the literal dihedral quotient above O₂,₃.
This supplies the quotient used by the source to exclude the normal rows.
Source: Aschbacher--Smith 10.2.3(3), printed p.745, and E.2.2(1).
-/

public noncomputable section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry
open Chapter3.Section02 ChapterB ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

theorem omegaQuotient_wreath_of_exchanged
    (hfaith : SourceNonnormalHallFaithfulAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (s : SourceLinearThreeSurvivor T D)
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T.subtype hH.1.1.2 : Subgroup H) = ⊤)
    (hc : ExchangedClauses
      (minimalParabolicMax (T.subtype hH.1.1.2) (hstar_minimal D s hH)) K (T.subtype hH.1.1.2))
    (hm : ExchangedModel
      (minimalParabolicMax (T.subtype hH.1.1.2) (hstar_minimal D s hH)) K 2) :
    Nonempty (OmegaQuotient T H ≃*
      Theory.SpecificGroups.SymmetricFive.WreathComponents.W) := by
  obtain ⟨hk,⟨e⟩⟩ := omegaQuotient_residual_of_exchanged D hfaith hmany s hfix hH K hK hgen hc hm
  obtain ⟨a,ha⟩ := omegaQuotient_embeds_wreath_of_exchanged D hfaith hmany s hfix hH K hK hgen hc hm
  let q := QuotientGroup.mk' (omegaKernel T H)
  let P := minimalParabolicMax (T.subtype hH.1.1.2) (hstar_minimal D s hH)
  let Q := P.map q
  let S := (T.subtype hH.1.1.2).mapSurjective (QuotientGroup.mk'_surjective (omegaKernel T H))
  have hP : IsPGroup 6 P := by
    rw [show P = D.maximalLocal.subgroupOf H from
      source_hstar_parabolicMax_eq_overlap D hH (hstar_minimal D s hH)]
    have hh := (overlap_isSixGroup D hfaith hmany s hH).comap_subtype (K := H)
    have he : (H ⊓ D.maximalLocal).subgroupOf H = D.maximalLocal.subgroupOf H := by
      ext x
      exact ⟨fun hx => hx.2,fun hx => ⟨x.property,hx⟩⟩
    exact he ▸ hh
  have hSQ : (S : Subgroup (OmegaQuotient T H)) ≤ Q :=
    map_mono (minimalParabolicMax_spec (T.subtype hH.1.1.2) (hstar_minimal D s hH)).2
  have hq : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk',hk]
    exact pCore_isPGroup
  have hqP : IsPGroup 2 (q.subgroupMap P).ker := by
    rw [Subgroup.ker_subgroupMap]
    exact hq.comap_subtype
  obtain ⟨b⟩ := hstar_maximal_twoCore_quotient D hfaith hmany s hH
  have hQ : Nonempty ((Q ⧸ pCore 2 Q) ≃* WreathTwoResidual.Actor) :=
    ⟨((q.subgroupMap P).pCoreQuotientEquiv (q.subgroupMap_surjective P) hqP).symm.trans b⟩
  exact wreath_of_pair_and_overlap e S Q (hP.map q) hSQ hQ a ha

/-- The source obstruction uses O₂,₃ in this order on the actual overlap. -/
theorem overlap_twoThreeCore_quotient
    (hfaith : SourceNonnormalHallFaithfulAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (s : SourceLinearThreeSurvivor T D)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    let P : Subgroup G := H ⊓ D.maximalLocal
    Nonempty ((P ⧸ (pCore 3 (P ⧸ pCore 2 P)).comap
      (QuotientGroup.mk' (pCore 2 P))) ≃* DihedralGroup 4) := by
  obtain ⟨e⟩ := overlap_twoCore_quotient D hfaith hmany s hH
  exact twoThreeCoreQuotient_of_wreath e

/-- The same obstruction on the original minimal-parabolic maximal subgroup. -/
theorem hstar_maximal_twoThreeCore_quotient
    (hfaith : SourceNonnormalHallFaithfulAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (s : SourceLinearThreeSurvivor T D)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    let P := minimalParabolicMax (T.subtype hH.1.1.2) (hstar_minimal D s hH)
    Nonempty ((P ⧸ (pCore 3 (P ⧸ pCore 2 P)).comap
      (QuotientGroup.mk' (pCore 2 P))) ≃* DihedralGroup 4) := by
  obtain ⟨e⟩ := hstar_maximal_twoCore_quotient D hfaith hmany s hH
  exact twoThreeCoreQuotient_of_wreath e

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry
