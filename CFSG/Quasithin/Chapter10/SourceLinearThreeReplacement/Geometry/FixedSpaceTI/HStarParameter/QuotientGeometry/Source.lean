module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry.Exchanged
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry.Normal
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientAction
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.Submodule

/-!
# The fixed seed in the literal H-star quotient action

The source Hall-placement and positive-kernel omega-center calculations
prove that H∩M fixes Ω₁Z(T). Consequently its actual image in H/C_H(U)
has enough fixed vectors to generate U. This discharges the fixed-seed
premise of the independent wreath-module calculation on the original
quotient and representation.

The imported parabolic theorem marks the actual O²(H∩M)(T∩L₀) and its
residual under one quotient map. The overlap theorem now identifies the
literal (H∩M)/O₂(H∩M) and the original minimal-parabolic maximal quotient
with S₃ wr C₂. The source-case theorem below identifies C_H(U) with the
parabolic core, excludes all odd rows and the unitary row, and fixes the
remaining field exponent at two. In the exchanged row it identifies the
actual two-residual with A₅ × A₅ and recognizes the whole quotient as S₅ wr C₂.
The exact quotient above the overlap's two-three core is dihedral of order
eight, which excludes the normal field-four rows by their actual outer
automorphism orders. This completes the quotient geometry without assuming
fixed-space vanishing, TI, or later centralizer data.
Source: Aschbacher--Smith 10.2.3(3), 10.2.8(1), and 10.3.1,
printed pp.744--745,749--750,755--756.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry
open Chapter3.Section02 ChapterB ChapterE Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- The literal maximal-overgroup fixed space generates the original omega module.
This is the action premise consumed by `WreathFixedSeedBound`. -/
theorem maximal_fixedSpace_generates
    (hhall : SourceNonnormalHallFaithfulAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D)
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    letI : IsElementaryAbelian 2 (omegaModule T H) := omegaModule_elementary D hH
    orbitSpan (omegaRepresentation D hH) ⊤
      (Representation.BinaryOffender.fixedSpace (omegaRepresentation D hH)
        (minimalParabolicMax
          ((T.subtype hH.1.1.2).mapSurjective (QuotientGroup.mk'_surjective (omegaKernel T H)))
          (omegaQuotient_minimal D s hfix hH))) = ⊤ := by
  let : IsElementaryAbelian 2 (omegaModule T H) := omegaModule_elementary D hH
  rw [← omegaQuotient_maximal D s hfix hH]
  have hB : (H ⊓ D.maximalLocal).subgroupOf H = D.maximalLocal.subgroupOf H := by
    ext x
    exact ⟨fun hx => hx.2,fun hx => ⟨x.property,hx⟩⟩
  rw [← hB]
  exact orbitSpan_fixedSpace_eq_top (omegaModule T H) H (omegaRepresentation D hH)
    (QuotientGroup.mk' (omegaKernel T H)) (omegaRepresentation_apply D hH)
    (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) (H ⊓ D.maximalLocal)
    (overlap_centralizes_sylow_seed D hhall hmany s hfix hH) rfl

/-- Combine quotient isomorphisms with the source seed-centralization proof. -/
theorem quotientGeometryAt_of_isomorphisms
    (hiso : SourceNonnormalHallFaithfulAt T →
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
        (_s : SourceLinearThreeSurvivor T D),
        D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥ →
        ∀ H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal,
          Nonempty (OmegaQuotient T H ≃*
            Theory.SpecificGroups.SymmetricFive.WreathComponents.W)) : QuotientGeometryAt T := by
  intro hhall hmany L D s hfix H hH
  exact ⟨hiso hhall hmany L D s hfix H hH,
    overlap_centralizes_sylow_seed D hhall hmany s hfix hH⟩

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry
open Chapter3.Section02 ChapterB ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The actual E.2.2 branch reduction for the fixed H-star quotient.
The normal field-four rows remain in this interface. The exchanged row's
whole-group isomorphism is supplied below. All component, quotient and
Sylow markings are retained. -/
theorem omegaQuotient_source_cases
    (hfaith : SourceNonnormalHallFaithfulAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (s : SourceLinearThreeSurvivor T D)
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    IsSQTK KnownSimple.IsKnownSimple (OmegaQuotient T H) ∧
    minimalParabolicCore
      ((T.subtype hH.1.1.2).mapSurjective (QuotientGroup.mk'_surjective (omegaKernel T H)))
      (omegaQuotient_minimal D s hfix hH) = ⊥ ∧
    ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      K ⊔ (T.subtype hH.1.1.2 : Subgroup H) = ⊤ ∧
      let M := minimalParabolicMax (T.subtype hH.1.1.2) (hstar_minimal D s hH)
      (K.Normal ∧ SingleClauses M K (T.subtype hH.1.1.2) ∧
        (ExchangedModel M K 2 ∨ DiagramModel M K (T.subtype hH.1.1.2) 2)) ∨
      (¬ K.Normal ∧ ExchangedClauses M K (T.subtype hH.1.1.2) ∧
        ExchangedModel M K 2 ∧ omegaKernel T H = pCore 2 H ∧
        Nonempty (pResidual 2 (OmegaQuotient T H) ≃*
          (alternatingGroup (Fin 5) × alternatingGroup (Fin 5))) ∧
        ∃ a : OmegaQuotient T H →* Theory.SpecificGroups.SymmetricFive.WreathComponents.W,
          Function.Injective a) := by
  refine ⟨omegaQuotient_sqtk D hfaith hmany s hfix hH,
    omegaQuotient_parabolicCore_eq_bot D hfaith hmany s hfix hH,?_⟩
  obtain ⟨K,hK,hqs,hgen,hn|hn⟩ := hstar_component_cases_two D hfaith hmany s hH
  · refine ⟨K,hK,hqs,hgen,Or.inl ⟨hn.1,hn.2.1,?_⟩⟩
    rcases hn.2.2 with (hm|hm)|hm
    · exact Or.inl hm
    · exact (hstar_not_unitary_two D hfaith hmany s hH K hm).elim
    · exact Or.inr hm
  · obtain ⟨hk,he⟩ := omegaQuotient_residual_of_exchanged D hfaith hmany s hfix hH K hK hgen hn.2.1 hn.2.2
    exact ⟨K,hK,hqs,hgen,Or.inr ⟨hn.1,hn.2.1,hn.2.2,hk,he,
      omegaQuotient_embeds_wreath_of_exchanged D hfaith hmany s hfix hH K hK hgen hn.2.1 hn.2.2⟩⟩

/-- Whole-group recognition is finished in the exchanged branch. The only
remaining source alternatives are normal field-four components, with the
literal dihedral overlap quotient that must exclude them. -/
theorem omegaQuotient_wreath_or_normal
    (hfaith : SourceNonnormalHallFaithfulAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (s : SourceLinearThreeSurvivor T D)
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    Nonempty (OmegaQuotient T H ≃* Theory.SpecificGroups.SymmetricFive.WreathComponents.W) ∨
    ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      K ⊔ (T.subtype hH.1.1.2 : Subgroup H) = ⊤ ∧ K.Normal ∧
      let M := minimalParabolicMax (T.subtype hH.1.1.2) (hstar_minimal D s hH)
      SingleClauses M K (T.subtype hH.1.1.2) ∧
        (ExchangedModel M K 2 ∨ DiagramModel M K (T.subtype hH.1.1.2) 2) ∧
        Nonempty ((M ⧸ (pCore 3 (M ⧸ pCore 2 M)).comap
          (QuotientGroup.mk' (pCore 2 M))) ≃* DihedralGroup 4) := by
  obtain ⟨_,_,K,hK,hqs,hgen,hn|hn⟩ := omegaQuotient_source_cases D hfaith hmany s hfix hH
  · exact Or.inr ⟨K,hK,hqs,hgen,hn.1,hn.2.1,hn.2.2,
      hstar_maximal_twoThreeCore_quotient D hfaith hmany s hH⟩
  · exact Or.inl (omegaQuotient_wreath_of_exchanged D hfaith hmany s hfix hH K hK hgen
      hn.2.1 hn.2.2.1)

/-- The original centralizer quotient, with its original Sylow and overlap
markings retained throughout the classification, is the full symmetric-five wreath group. -/
theorem omegaQuotient_wreath
    (hfaith : SourceNonnormalHallFaithfulAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (s : SourceLinearThreeSurvivor T D)
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    Nonempty (OmegaQuotient T H ≃* Theory.SpecificGroups.SymmetricFive.WreathComponents.W) := by
  rcases omegaQuotient_wreath_or_normal D hfaith hmany s hfix hH with hw | hn
  · exact hw
  · obtain ⟨K,hK,_,hgen,hKn,hc,hm,hd⟩ := hn
    let := hKn
    have hs : ¬ Group.IsSolvable H := by
      intro hs
      let := hs
      have hb : generationParameter H ≤ 1 := generationParameter_le_one_of_solvable
      rw [s.generation H hH] at hb
      omega
    have hM : IsPGroup 6 (D.maximalLocal.subgroupOf H) := by
      have hh := (overlap_isSixGroup D hfaith hmany s hH).comap_subtype (K := H)
      have he : (H ⊓ D.maximalLocal).subgroupOf H = D.maximalLocal.subgroupOf H := by
        ext x
        exact ⟨fun hx => hx.2,fun hx => ⟨x.property,hx⟩⟩
      exact he ▸ hh
    rw [← source_hstar_parabolicMax_eq_overlap D hH (hstar_minimal D s hH)] at hM
    exact (normal_fieldFour_false (T.subtype hH.1.1.2) (hstar_minimal D s hH)
      hs K hK hgen hc hM hd hm).elim

/-- The source quotient geometry in the nonzero fixed-space branch.
Hall faithfulness is the authorized earlier-source input of the contract. -/
theorem quotientGeometryAt : QuotientGeometryAt T := by
  apply quotientGeometryAt_of_isomorphisms
  intro hfaith hmany L D s hfix H hH
  exact omegaQuotient_wreath D hfaith hmany s hfix hH

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry
