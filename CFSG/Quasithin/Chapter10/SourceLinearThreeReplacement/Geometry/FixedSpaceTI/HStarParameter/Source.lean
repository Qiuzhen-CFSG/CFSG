module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.GeometryInput
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientAction
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.Submodule
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.Model.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.LocalSource

/-!
# Assembly of the moved H-star parameter from quotient geometry and the module calculation

The original weak closure has nontrivial image in H/C_H(U). The quotient's
maximal Sylow overgroup is the actual overlap image, whose fixed vectors
generate U once the source seed-centralization input is supplied. A faithful
subrepresentation of parameter at most one then gives a literal subgroup of U.
Its faithfulness preserves weak-closure movement, and full-module coordinates
transfer the bound to exactly Aut_H(I).

The source Hall-faithfulness theorem, quotient/seed geometry and independent
deleted-sum/tensor calculation discharge all inputs to `hStarLocalAAt`.
The original conditional interfaces remain available. The fixed-part consumer
then applies the actual weak-closure contradiction, retaining only the global
parameter supplied independently by `GlobalParameter.globalSAt`.
Source: Aschbacher--Smith 10.3.1, pp.755--756.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter
open Chapter3.Section02 ChapterB ChapterE Representation.BinaryOffender.Homogeneous
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- The actual H-star constituent contract follows from the two independent source inputs. -/
theorem hStarLocalA_of_geometry_and_model
    (hhall : SourceNonnormalHallFaithfulAt T)
    (hgeometry : QuotientGeometryAt T) (hmodel : WreathFixedSeedBound.{u,u}) : HStarLocalAAt T := by
  intro hmany L D s hfix H hH
  obtain ⟨he,hseed⟩ := hgeometry hhall hmany L D s hfix H hH
  let U := omegaModule T H
  let : IsElementaryAbelian 2 U := omegaModule_elementary D hH
  let ρ := omegaRepresentation D hH
  let q := QuotientGroup.mk' (omegaKernel T H)
  let P := (T.subtype hH.1.1.2).mapSurjective (QuotientGroup.mk'_surjective (omegaKernel T H))
  let hP := omegaQuotient_minimal D s hfix hH
  have hgen : orbitSpan ρ ⊤ (Representation.BinaryOffender.fixedSpace ρ (minimalParabolicMax P hP)) = ⊤ := by
    rw [← omegaQuotient_maximal D s hfix hH]
    have hB : (H ⊓ D.maximalLocal).subgroupOf H = D.maximalLocal.subgroupOf H := by
      ext x
      exact ⟨fun hx => hx.2,fun hx => ⟨x.property,hx⟩⟩
    rw [← hB]
    exact orbitSpan_fixedSpace_eq_top U H ρ q (omegaRepresentation_apply D hH)
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) (H ⊓ D.maximalLocal) hseed rfl
  obtain ⟨S,hfaith,hbound⟩ := hmodel (OmegaQuotient T H) (Additive U) ρ
    (omegaRepresentation_injective D hH) he P hP hgen
  let I := submoduleGroup U ρ S
  have hnorm : H ≤ normalizer (I : Set G) :=
    submoduleGroup_normalizes U H ρ q (omegaRepresentation_apply D hH) S
  refine ⟨I,submoduleGroup_le U ρ S,hnorm,?_,inferInstance,?_⟩
  · intro hc
    apply weakClosure_quotient_image_ne_bot D s hfix hH
    apply (Subgroup.map_eq_bot_iff _).mpr
    intro w hw
    exact (submoduleGroup_centralizes_iff U H ρ q (omegaRepresentation_apply D hH) S hfaith w).mp (hc hw)
  · exact (submoduleGroup_parameter_le U H ρ q (omegaRepresentation_apply D hH) S hfaith).trans hbound

/-- Application to the literal weak-closure contradiction. The global bound
is supplied by its independent source owner, not used to select the subgroup. -/
theorem false_of_parameter_source_inputs
    (hhall : SourceNonnormalHallFaithfulAt T)
    (hgeometry : QuotientGeometryAt T) (hmodel : WreathFixedSeedBound.{u,u})
    (hs : GlobalSAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D)
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) : False := by
  obtain ⟨I,_,hHI,hmove,hI,haI⟩ :=
    hStarLocalA_of_geometry_and_model hhall hgeometry hmodel hmany L D s hfix H hH
  let := hI
  exact false_of_moved_parameter_bounds D s hH.1.1.2 hHI hmove haI (hs hmany L D s hfix)

/-- The original H-star constituent bound, with Hall faithfulness, the literal
quotient geometry and the faithful submodule calculation all discharged. -/
theorem hStarLocalAAt : HStarLocalAAt T :=
  hStarLocalA_of_geometry_and_model source_nonnormalHallFaithful
    QuotientGeometry.quotientGeometryAt wreathFixedSeedBound

/-- The literal fixed-space consumer of the source constituent theorem.
The independent global parameter is discharged by `GlobalParameter.globalSAt`
in the parent fixed-space/TI assembly. -/
theorem fixed_part_of_global_parameter
    (hs : GlobalSAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D) :
    D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥ := by
  by_contra hfix
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  have hout : Chapter3.HasMaximalOutside T D.maximalLocal := by
    obtain ⟨A,hA,B,hB,hne⟩ := (Set.one_lt_ncard_iff_nontrivial_and_finite.mp hmany).1
    by_cases hAM : A = D.maximalLocal
    · exact Chapter3.hasMaximalOutside_of_two_distinct hu.normalizer_maximal hB.1
        (le_normalizer_componentOrbit L T) hB.2 (fun he => hne (hAM.trans he.symm))
    · exact Chapter3.hasMaximalOutside_of_two_distinct hu.normalizer_maximal hA.1
        (le_normalizer_componentOrbit L T) hA.2 hAM
  obtain ⟨H,hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside hout
  obtain ⟨I,_,hHI,hmove,hI,haI⟩ := hStarLocalAAt hmany L D s hfix H hH
  let := hI
  exact false_of_moved_parameter_bounds D s hH.1.1.2 hHI hmove haI
    (hs hmany L D s hfix)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter
