module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.ExchangedRecognition
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.NormalSource

/-!
# Recognizing and excluding the original exchanged Suzuki section

The original F.9.18 construction supplies a quadratic edge actor and its
faithful conjugation on the literal component orbit. A.3.8 supplies the
index-two normalizer; the two-factor geometry retains the actual images in
H/O₂(H). The minimal-actor argument recognizes the central quotient of the
entire moved space as the two natural Suzuki modules. Applying the original
Borel centralization and seed-generation contradiction excludes this branch.

Only the genuine LocalSetup, maximal-local, F.9, 13.5.4 and 13.3.9 inputs
remain explicit. `Components.Source` discharges 13.3.9 and combines all
component branches; qt-d-1381-source and its earlier-source producers retain
the final construction of the original setup and earlier hypotheses.

Source: Aschbacher--Smith, F.9.18(5--7), pp.325--326, and 13.8.16(1),
printed pp.952--953 (combined manuscript of 1 March 2004).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
open BenderSuzuki.MatrixGroups
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

namespace CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections
open SourceCompletion SolvableExclusion Three.Supercritical.Offenders
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
open Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged
open Swapped.LinearTwo.ModuleAlternatives.F918Sections
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
  (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
  (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
  (hsource : Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
  (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (one L T V₁ ⊔ (T : Subgroup G)) = H)
  (hn : ¬ (K.subgroupOf H).Normal)
  {m : ℕ} (hm : 0 < m) (eK : (K ⧸ pCore 2 K) ≃* SuzukiMatrixGroup m)
  [hEA : IsElementaryAbelian 2 (Source.UH H V₃)]
  (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
  (hρ : IsSourceAction H V₃ V₁ ρ)

omit hEA in
include d h hF9all hcentral hcomm hsource hH hKH hK hn eK in
private theorem source_exchange_geometry :
    ExchangedGeometry (Source.starImage H K) (orbitActor H K T)
      (Source.starImage H T) ⊥ ⊥ := by
  let : IsQuasisimple (Source.starImage H K) :=
    (SolvableSource.component_fitting_source d h hF9all hcentral hcomm hsource hH K hK).2
  have hc := star_isComponent H K hK (inferInstance : IsQuasisimple (Source.starImage H K))
  have hZ := SectionRecognition.center_eq_bot_of_equiv_suzuki
    ((componentStarEquiv H K hKH hK).symm.trans eK)
  have hindex := (SourceModels.source_nonnormal_star_models d hH hK hn).1
  have hmove : ¬ Source.starImage H T ≤ normalizer (Source.starImage H K : Set (Source.Hstar H)) := by
    intro ht
    apply hn
    apply (SourceModels.source_orbit_eq_iff_normal d h hF9all hcentral hcomm hsource hH K hKH hK).mp
    exact le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl ht)
      (le_componentOrbit _ _)
  have he : orbitActor H K T = componentOrbit (Source.starImage H K) (Source.starImage H T) := by
    rw [orbitActor,star_conjugateSpan H K T hKH (le_sup_right.trans hH.1.2),conjugateSpanBy_eq_iSup_conj]
    rfl
  rw [he]
  exact SourceModels.exchanged_geometry_of_index_two _ _ hc hZ hindex hmove

include d h hF9all hcentral hcomm hsource hH hKH hK hgen hρ in
private theorem source_bounded_actor :
    ∃ B : Subgroup G, B ≤ ((L ⊔ (T : Subgroup G)) ⊓ H).pCoreIn 2 ∧ B ≤ T ∧
      (IsElementaryTwo (Source.starImage H B) ∧ IsQuadratic ρ (Source.starImage H B) ∧
        fixedCodim ρ (Source.starImage H B) ≤ 2 * rank (Source.starImage H B)) ∧
      Source.starImage H B ⊓ centralizer (orbitActor H K T : Set (Source.Hstar H)) = ⊥ := by
  obtain ⟨a,B,hB,hBT,hq,hfaith,_⟩ := F918.source_component_span_actors (hEA := hEA)
    d h hF9all hcentral hcomm hsource hH K hKH hK hgen
  have heρ : ρ = linearAction a := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) g
    obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf (Source.UH H V₃)) v.toMul
    have hv : v = Additive.ofMul (sourceProjection H V₃ V₁ u) := hu.symm
    rw [hv,hρ]
    exact congrArg Additive.ofMul (a.conjugation x u).symm
  rw [←heρ] at hq
  exact ⟨B,hB,hBT,hq,hfaith⟩

include d h hF9all hcentral hcomm hsource hH hKH hK hgen hn hm eK hρ

/-- The two natural factors on the literal full moved central quotient. -/
theorem source_exchanged_natural_section : HasPairedNaturalCentralSection H V₃ V₁ ρ K T m := by
  obtain ⟨B,_,hBT,hq,hfaith⟩ := source_bounded_actor
    d h hF9all hcentral hcomm hsource hH hKH hK hgen ρ hρ
  have geo := source_exchange_geometry d h hF9all hcentral hcomm hsource hH hKH hK hn eK
  have hTK : Source.starImage H T ≤ normalizer (orbitActor H K T : Set (Source.Hstar H)) := by
    rw [orbitActor,star_conjugateSpan H K T hKH (le_sup_right.trans hH.1.2)]
    exact le_normalizer_conjugateSpanBy _ _
  have hqs := (SolvableSource.component_fitting_source d h hF9all hcentral hcomm hsource hH K hK).2
  obtain ⟨a⟩ := ExchangedRecognition.exchanged_natural_pair ρ geo
    (SourceModels.source_nonnormal_star_models d hH hK hn).1 hTK
    (original_action_faithful ρ hρ (hF9all H hH)) (star_isComponent H K hK hqs)
    (CoverModels.original_star_sqtk d hH) hm ((componentStarEquiv H K hKH hK).symm.trans eK)
    (SolvableExclusion.Three.starImage_mono H hBT) hq.1 hq.2.1 hfaith hq.2.2
  exact ⟨a.groupEquiv.toMonoidHom,a.groupEquiv.surjective,a.linearEquiv,a.intertwines⟩

omit hρ ρ hEA in
/-- The exchanged Suzuki branch of original 13.8.16(1), including recognition. -/
theorem source_exchanged_suzuki_impossible : False := by
  let : IsElementaryAbelian 2 (Source.UH H V₃) := d.uh_elementary hH
  have hF9 := hF9all H hH
  have hz : H ≤ normalizer (V₁ : Set G) :=
    hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  let ρ := Swapped.LinearTwo.ModuleAlternatives.representation H V₃ V₁ hz
    hF9.commutator_UH_QH_le_point
  have hρ := Swapped.LinearTwo.ModuleAlternatives.representation_isSourceAction H V₃ V₁ hz
    hF9.commutator_UH_QH_le_point
  exact original_natural_sections_impossible d ρ hρ h hF9all hcentral hcomm hsource
    hH hKH hK hgen hm eK (Or.inr (source_exchanged_natural_section
      d h hF9all hcentral hcomm hsource hH hKH hK hgen hn hm eK ρ hρ))

end CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections
