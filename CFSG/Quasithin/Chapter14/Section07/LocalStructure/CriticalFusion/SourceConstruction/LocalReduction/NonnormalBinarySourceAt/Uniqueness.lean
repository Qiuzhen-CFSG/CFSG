module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ComponentCatalogueAt
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.SourceModels.SylowOvergroupUnique

/-!
# Uniqueness inside a Sylow-invariant original component

Retain the full F.9.18 catalogue from the actual reduced-local quadratic
actor, including its precise central quotients. A Sylow-invariant component
is normal in its reduced local by the source orbit bound. Its faithful
quadratic actor therefore gives a genuine F.9.18 model, whose Sylow-overgroup
component uniqueness lifts through the intrinsic two-core.

This supplies the normalized-overcomponent exclusion in the field-four
case of 14.7.32. No full-point component comparison is assumed.
Source: Aschbacher–Smith, 14.7.30,14.7.32 and A.3.12, printed
pp.1055–1056,47–48, refs/quasithin.pdf.
-/

/-! This same-G,T source replay uses only Structural1222At and Theorem12213At
at the original Sylow; it does not infer universal earlier records. -/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
open Chapter13.Section08.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The full source model catalogue for a normal component in its literal
reduced local, on the intrinsic two-core quotient. -/
theorem local_reduced_normal_component_f918_models_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (K : Subgroup I) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I = ⊤) :
    Models.F918Models (K ⧸ pCore 2 K) := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let B := K.map q
  let : B.Normal := (inferInstance : K.Normal).map q (QuotientGroup.mk'_surjective _)
  have hg : B ⊔ ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I).map q = ⊤ := by
    rw [←Subgroup.map_sup,hgen,map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  obtain ⟨hU,a,_,A,_,hA,hquad,hcod,hfaith⟩ :=
    WholeResidualAssembly.GuardedSource.local_prime_supplement_quadratic_actor h hab structural previous I hI B hg
  let := hU
  have hB := WholeResidualAssembly.GuardedSource.local_component_star_isComponent h hab structural previous faithful I hI K hK
  let : IsQuasisimple B := hB.2
  have hs := local_star_sqtk h I hI
  have hc := ChapterA.Section03.SourceEmbeddings.quasisimple_containing_component_models_knownSimple
    hs (pCore_quotient_pCore_eq_bot 2) hB.isCComponent
  have hcenter : Nat.card (center B) = 1 ∨ Nat.card (center B) = 3 := by
    rcases hc with ⟨hs,_⟩ | ⟨⟨e⟩,_⟩
    · let := hs
      exact Or.inl (Subgroup.card_eq_one.mpr CoverModels.center_eq_bot_of_simple)
    · exact Or.inr ((Nat.card_congr e.toEquiv).trans (Nat.card_zmod 3))
  exact SourceModels.f918Models_transport (cComponentTwoCoreQuotientEquiv hK)
    (SourceModels.f918Models_of_quadratic_actor a.representation B (A.map q)
      a.faithful hcenter hs hA hquad hcod hfaith)

/-- Every full-Sylow overgroup inside an original Sylow-invariant component
has at most one C-component. -/
theorem local_sylow_invariant_component_unique_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) :
    SylowOvergroupComponentUnique K := by
  let J := K ⊔ (F.Li L 1 ⊔ (T : Subgroup G))
  have he : conjugateSpanBy K (T : Subgroup G) = K :=
    le_antisymm (conjugateSpanBy_le le_rfl hTK) (le_conjugateSpanBy _ _)
  obtain ⟨hn,hJI,hJ⟩ := local_component_reduced_mem_Hz_at h structural I hI (K.subgroupOf I) hK
  rw [map_subgroupOf_eq_of_le hKI,he] at hn hJI hJ
  have hnorm : (K.subgroupOf I).Normal := hn
  have hKJle : K ≤ J := le_sup_left
  have hKJ : (K.subgroupOf J).IsCComponent := hK.subgroupOf_of_le hKJle hJI
  let : (K.subgroupOf J).Normal := (normal_subgroupOf_iff_le_normalizer hKJle).mpr
    (hJI.trans ((normal_subgroupOf_iff_le_normalizer hKI).mp hnorm))
  have hgen : K.subgroupOf J ⊔ (F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf J = ⊤ := by
    rw [←subgroupOf_sup hKJle (show F.Li L 1 ⊔ (T : Subgroup G) ≤ J from le_sup_right),
      show K ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) = J from rfl,subgroupOf_self]
  have hm := local_reduced_normal_component_f918_models_at h hab structural previous faithful
    J hJ (K.subgroupOf J) hKJ hgen
  let := WholeResidualAssembly.GuardedSource.local_component_twoCore_isQuasisimple h hab structural previous faithful J hJ
    (K.subgroupOf J) hKJ
  let : Group.IsNilpotent (pCore 2 (K.subgroupOf J)) := pCore_isPGroup.isNilpotent
  have hu : SylowOvergroupComponentUnique (K.subgroupOf J) :=
    SylowOvergroupComponentUnique.of_quotient (pCore 2 (K.subgroupOf J))
      (f918_sylow_overgroup_component_unique hm)
  exact hu.of_equiv (subgroupOfEquivOfLe hKJle).symm
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
