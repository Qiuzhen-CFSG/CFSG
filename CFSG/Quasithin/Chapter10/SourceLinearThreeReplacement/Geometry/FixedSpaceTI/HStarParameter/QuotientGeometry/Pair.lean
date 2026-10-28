module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry.Core
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry.Cases
public import Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms
public import Theory.GroupTheory.GeneralizedFitting.ResidualCentralizer
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The exchanged branch inside the literal centralizer quotient

The E.2.2 exchanged clauses identify the original core with O₂(H). The
field-four markings and the actual pair coordinates identify O²(H/C_H(U))
with A₅ × A₅. Its trivial center and residual self-centralization give a
faithful conjugation map from H/C_H(U) into Aut(A₅ × A₅)=S₅ wr C₂.

The core comparison uses the defining equation through the internal Structure
import. All quotient transports use genuine equivalences. Surjectivity of
the final embedding is still required for whole-group recognition.
Source: Aschbacher--Smith E.2.2(1) and 10.2.3(3), printed pp.215--216,745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry
open Chapter3.Section02 ChapterB ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels

private theorem exchanged_component_nonnormal {X : Type*} [Group X]
    {M K S : Subgroup X} (hc : ExchangedClauses M K S) : ¬ K.Normal := by
  intro hN
  obtain ⟨t,_,hne,_⟩ := hc.exchanged_product
  apply hne
  exact (normal_iff_map_conj_eq.mp hN t⁻¹).symm

private theorem star_residual_of_exchanged_two
    {X : Type*} [Group X] [Finite X]
    (hX : IsSQTK KnownSimple.IsKnownSimple X) (S : Sylow 2 X)
    (hP : IsMinimalParabolicOver S ⊤) (hs : ¬ Group.IsSolvable X)
    (K : Subgroup X) (hK : K.IsCComponent)
    (hgen : K ⊔ (S : Subgroup X) = ⊤)
    (hc : ExchangedClauses (minimalParabolicMax S hP) K S)
    (hm : ExchangedModel (minimalParabolicMax S hP) K 2) :
    Nonempty (pResidual 2 (X ⧸ minimalParabolicCore S hP) ≃*
      (alternatingGroup (Fin 5) × alternatingGroup (Fin 5))) := by
  let J := minimalParabolicCore S hP
  let q := QuotientGroup.mk' J
  let Sq := S.mapSurjective (QuotientGroup.mk'_surjective J)
  let A := K.map q
  let : Group.IsSolvable J := minimalParabolic_core_solvable S hP
  have hi := Structure.source_component_simple_image S hP hs K hK hgen
  have hAn : ¬ A.Normal := fun h => exchanged_component_nonnormal hc
    (cComponent_normal_of_quotient_normal hK J h)
  obtain ⟨eA⟩ := exchanged_two_component_equiv_alternatingFive hm
  have hsQ : ¬ Group.IsSolvable (X ⧸ J) := fun hh =>
    hs ((Group.isSolvable_iff_subgroup_quotient J).mpr ⟨inferInstance,hh⟩)
  have hsq := Structure.source_star_sqtk ChapterA.Section02.theoremA_knownSimple hX S hP hs
  obtain ⟨t,_,_,_,hr,⟨e,_⟩,_,_⟩ := Structure.source_pair_coordinates hsq.stronglyQuasithin Sq
    (Structure.source_star_minimal_core_free S hP).1 hsQ
    (Structure.source_star_minimal_core_free S hP).2 hi.2.1 (hK.map_quotient J)
    hi.2.2.2 hAn
  let B := A.map (MulAut.conj (t : X ⧸ J)).toMonoidHom
  let eB : B ≃* alternatingGroup (Fin 5) :=
    ((MulAut.conj (t : X ⧸ J)).subgroupMap A).symm.trans eA
  exact ⟨((MulEquiv.subgroupCongr hr).trans e.symm).trans (eA.prodCongr eB)⟩

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The exchanged E.2.2 branch identifies the two-residual in the actual
centralizer quotient, not just the original overlap. -/
theorem omegaQuotient_residual_of_exchanged
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
    omegaKernel T H = pCore 2 H ∧
    Nonempty (pResidual 2 (OmegaQuotient T H) ≃*
      (alternatingGroup (Fin 5) × alternatingGroup (Fin 5))) := by
  have hk := omegaKernel_eq_parabolicCore D hfaith hmany s hfix hH
  refine ⟨hk.trans hc.kernel_eq,?_⟩
  have hs : ¬ Group.IsSolvable H := by
    intro hs
    let := hs
    have hn : generationParameter H ≤ 1 := generationParameter_le_one_of_solvable
    rw [s.generation H hH] at hn
    omega
  obtain ⟨e⟩ := star_residual_of_exchanged_two
    (Chapter3.sqtk_of_mem_H D.simpleQTKE hH.1.1.1)
    (T.subtype hH.1.1.2) (hstar_minimal D s hH) hs K hK hgen hc hm
  let a := QuotientGroup.quotientMulEquivOfEq hk
  exact ⟨((a.subgroupMap (pResidual 2 (OmegaQuotient T H))).trans
    (MulEquiv.subgroupCongr (map_pResidual_of_surjective 2 a.toMonoidHom a.surjective))).trans e⟩

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry
open Chapter3.Section02 ChapterB ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels

private theorem wreath_embedding_of_pair_residual {X : Type*} [Group X] [Finite X]
    (hcore : pCore 2 X = ⊥)
    (e : pResidual 2 X ≃* (alternatingGroup (Fin 5) × alternatingGroup (Fin 5))) :
    ∃ a : X →* Theory.SpecificGroups.SymmetricFive.WreathComponents.W,
      Function.Injective a := by
  let R := pResidual 2 X
  have hpair : center (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) = ⊥ := by
    rw [Subgroup.center_prod,alternatingGroup.center_eq_bot (by simp)]
    ext x
    simp
  have hc : centralizer (R : Set X) = ⊥ := by
    apply bot_unique
    intro x hx
    have hxr : x ∈ R := centralizer_pResidual_le_of_pCore_eq_bot hcore hx
    have hec : e ⟨x,hxr⟩ ∈ center (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨z,rfl⟩ := e.surjective y
      simpa only [← map_mul] using congrArg e (show z * ⟨x,hxr⟩ = ⟨x,hxr⟩ * z from
        Subtype.ext (hx z z.property))
    have he : e ⟨x,hxr⟩ = 1 := hpair.le hec
    exact congrArg Subtype.val (e.injective (he.trans e.map_one.symm))
  let a := Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms.wreathEquiv.symm.toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : X →* MulAut R))
  exact ⟨a,Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms.wreathEquiv.symm.injective.comp
    ((MulAut.congr e).injective.comp (MulAut.conjNormal_injective_of_centralizer_eq_bot R hc))⟩

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The original centralizer quotient acts faithfully on the two A₅ factors.
Surjectivity onto the whole wreath product remains a separate obligation. -/
theorem omegaQuotient_embeds_wreath_of_exchanged
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
    ∃ a : OmegaQuotient T H →* Theory.SpecificGroups.SymmetricFive.WreathComponents.W,
      Function.Injective a := by
  obtain ⟨_,⟨e⟩⟩ := omegaQuotient_residual_of_exchanged D hfaith hmany s hfix hH K hK hgen hc hm
  exact wreath_embedding_of_pair_residual (omegaQuotient_twoCore_eq_bot D hH) e

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry
