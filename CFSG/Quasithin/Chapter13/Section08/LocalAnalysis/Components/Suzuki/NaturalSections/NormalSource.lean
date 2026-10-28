module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.SourceRecognition
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.OriginalReduction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.SourceReduction

/-!
# Excluding normal Suzuki components in the original A₆ configuration

The original F.9.18 edge actor acts quadratically on U_H/V₁, with fixed
codimension at most twice its rank, and acts faithfully by conjugation on K*
when K is normal. `SourceRecognition` constructs the natural central quotient
of the whole moved space. The proved Borel and seed argument then gives the
original Suzuki contradiction, with no section or model-recognition callback.

Apply this inside the actual generated overgroup and transport through
K/O₂(K) to exclude Suzuki for every normal source component. The F.9.18 and
cover catalogue consequently gives every concrete 13.8.17 model in that
branch. The original 13.3.9 premise is discharged by `EarlierResidual`.

Relative normality remains explicit: the exchanged Suzuki branch and final
13.8.16--17 assembly belong to qt-d-138-components-source. The original
LocalSetup, F.9 and 13.5.4 hypotheses are ultimately supplied by
qt-d-1381-source and its earlier-source producers.

Source: Aschbacher--Smith, 13.8.16(2)--17, printed p.953, and F.9.18(4,7),
pp.325--326 (combined manuscript of 1 March 2004).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections
open SourceCompletion SolvableExclusion Three.Supercritical.Offenders
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
variable {G : Type*} [Group G] [Finite G]
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
  (hn : (K.subgroupOf H).Normal)
  {m : ℕ} (hm : 0 < m) (eK : (K ⧸ pCore 2 K) ≃* SuzukiMatrixGroup m)

include d h hF9all hcentral hcomm hsource hH hKH hK hgen hn hm eK

/-- Recognize the literal full moved central section in the normal Suzuki branch. -/
theorem source_normal_natural_section [hEA : IsElementaryAbelian 2 (Source.UH H V₃)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ) : HasNaturalCentralSection H V₃ V₁ ρ K T m := by
  obtain ⟨a,B,_,_,hq,hfaith,_⟩ := F918.source_component_span_actors (hEA := hEA)
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
  have hf := original_action_faithful ρ hρ (hF9all H hH)
  let : IsQuasisimple (Source.starImage H K) :=
    (SolvableSource.component_fitting_source d h hF9all hcentral hcomm hsource hH K hK).2
  let : (Source.starImage H K).Normal := hn.map _ (QuotientGroup.mk'_surjective (pCore 2 H))
  have ho := conjugateSpan_eq_of_normal H K T hKH (le_sup_right.trans hH.1.2) hn
  rw [ho] at hfaith
  have hnact : ¬ Source.starImage H K ≤ ρ.ker := by
    intro hh
    let : IsSimpleGroup ((Source.starImage H K) ⧸ center (Source.starImage H K)) := IsQuasisimple.simple
    let : Nontrivial (Source.starImage H K) :=
      (QuotientGroup.mk'_surjective (center (Source.starImage H K))).nontrivial
    exact (nontrivial_iff_ne_bot _).mp inferInstance
      (bot_unique (hh.trans ((MonoidHom.ker_eq_bot_iff _).mpr hf).le))
  obtain ⟨b⟩ := SourceRecognition.natural_moved_of_quadratic_actor ρ
    (Source.starImage H K) (Source.starImage H B) hm
    ((componentStarEquiv H K hKH hK).symm.trans eK)
    (CoverModels.original_star_sqtk d hH) hq.1 hq.2.1 hq.2.2 hfaith hnact
  have hb : Nonempty
      (Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.ActionEquiv
        (centralQuotientRepresentation ρ (orbitActor H K T) (movedSpace H V₃ V₁ ρ K T)
          (movedSpace_stable H V₃ V₁ ρ K T)) (natural m)) := by
    change Nonempty
      (Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.ActionEquiv
        (centralQuotientRepresentation ρ (Source.starImage H (conjugateSpanBy K (T : Subgroup G)))
          (subspaceCommutator ρ ⊤ (Source.starImage H (conjugateSpanBy K (T : Subgroup G))))
          (subspaceCommutator_invariant ρ ⊤ (Source.starImage H (conjugateSpanBy K (T : Subgroup G)))))
        (natural m))
    rw [ho]
    exact ⟨b⟩
  obtain ⟨b⟩ := hb
  exact ⟨b.groupEquiv.toMonoidHom,b.groupEquiv.surjective,b.linearEquiv,b.intertwines⟩

/-- The normal Suzuki case of original 13.8.16(2), including section construction. -/
theorem source_normal_suzuki_impossible : False := by
  let : IsElementaryAbelian 2 (Source.UH H V₃) := d.uh_elementary hH
  have hF9 := hF9all H hH
  have hz : H ≤ normalizer (V₁ : Set G) :=
    hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  let ρ := Swapped.LinearTwo.ModuleAlternatives.representation H V₃ V₁ hz
    hF9.commutator_UH_QH_le_point
  have hρ := Swapped.LinearTwo.ModuleAlternatives.representation_isSourceAction H V₃ V₁ hz
    hF9.commutator_UH_QH_le_point
  exact original_natural_sections_impossible d ρ hρ h hF9all hcentral hcomm hsource
    hH hKH hK hgen hm eK (Or.inl (source_normal_natural_section
      d h hF9all hcentral hcomm hsource hH hKH hK hgen hn hm eK ρ hρ))

end CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections


namespace CFSG.Quasithin.Chapter13.Section08.Components
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
  (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
  (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
  (hsource : SolvableExclusion.Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
  (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
include d h hF9all hcentral hcomm hsource hH hKH hK

/-- The intrinsic Suzuki quotient is excluded for every normal source component. -/
theorem source_not_suzuki_of_normal (hn : (K.subgroupOf H).Normal)
    (m : ℕ) (hm : 1 ≤ m) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* SuzukiMatrixGroup m) := by
  rintro ⟨e⟩
  let J := conjugateSpanBy K (T : Subgroup G) ⊔ (one L T V₁ ⊔ (T : Subgroup G))
  obtain ⟨hJ,hJH,hKJ,hK'⟩ := source_generated_overgroup
    d h hF9all hcentral hcomm hsource hH hKH hK
  have hnJ : (K.subgroupOf J).Normal :=
    (normal_subgroupOf_iff_le_normalizer hKJ).mpr
      (hJH.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hn))
  exact Suzuki.NaturalSections.source_normal_suzuki_impossible d h hF9all hcentral hcomm hsource
    hJ hKJ hK' rfl hnJ (by omega) e

/-- The full concrete 13.8.17 catalogue, conditional only on the remaining normality branch. -/
theorem source_catalogue_of_normal (hn : (K.subgroupOf H).Normal) :
    Models.ComponentModel (Source.starImage H K) := by
  apply (source_catalogue_or_suzuki d h hF9all hcentral hcomm hsource hH hKH hK).of_no_suzuki
  intro m hm he
  apply source_not_suzuki_of_normal d h hF9all hcentral hcomm hsource hH hKH hK hn m hm
  exact he.map ((componentStarEquiv H K hKH hK).trans ·)

omit hsource in
/-- The normal Suzuki exclusion with the completed original residual producer applied. -/
theorem original_not_suzuki_of_normal (hn : (K.subgroupOf H).Normal)
    (m : ℕ) (hm : 1 ≤ m) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* SuzukiMatrixGroup m) :=
  source_not_suzuki_of_normal d h hF9all hcentral hcomm
    (EarlierResidual.original_source d h) hH hKH hK hn m hm

omit hsource in
/-- The concrete normal-component catalogue on the original source assumptions. -/
theorem original_catalogue_of_normal (hn : (K.subgroupOf H).Normal) :
    Models.ComponentModel (Source.starImage H K) :=
  source_catalogue_of_normal d h hF9all hcentral hcomm
    (EarlierResidual.original_source d h) hH hKH hK hn

end CFSG.Quasithin.Chapter13.Section08.Components

end
