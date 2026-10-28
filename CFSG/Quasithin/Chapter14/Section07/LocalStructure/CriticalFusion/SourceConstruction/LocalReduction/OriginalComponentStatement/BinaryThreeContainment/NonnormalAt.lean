module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ComponentCatalogueAt
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.BinaryThreeContainment.NormalityAt

/-!
# The remaining nonnormal components at the same original G,T

Pass to the actual Sylow-orbit local and retain nonnormality there using
the normal-or-index-two alternative. The faithful quadratic actor catalogue
leaves binary PSL₂, Suzuki, and binary PSL₃. The genuine Suzuki source
exclusion and the exchanged-parabolic argument remove the latter two.
The remaining literal intrinsic two-core quotient is PSL₂(2ⁿ), n ≥ 2.

All earlier structural inputs concern the original group and Sylow.
No component-normality theorem or 14.7.47 conclusion is assumed.
Source: Aschbacher–Smith, 14.7.30 and the opening case of 14.7.32,
printed pp.1055–1056, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Every original component still failing normality has a literal binary
PSL₂ two-core quotient; all earlier structural data are at the original T. -/
theorem local_nonnormal_component_binary_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (K : Subgroup I) (hK : K.IsCComponent) (hn : ¬ K.Normal) :
    ∃ n, 2 ≤ n ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n) := by
  let N := conjugateSpanBy (K.map I.subtype) (T : Subgroup G)
  let J := N ⊔ (F.Li L 1 ⊔ (T : Subgroup G))
  let KJ := (K.map I.subtype).subgroupOf J
  obtain ⟨_,hJI,hJ⟩ := local_component_reduced_mem_Hz_at h structural I hI K hK
  have hKJle : K.map I.subtype ≤ J := (le_conjugateSpanBy _ _).trans le_sup_left
  have hKI : ((K.map I.subtype).subgroupOf I).IsCComponent := by
    simpa only [subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hK
  have hKJ : KJ.IsCComponent := hKI.subgroupOf_of_le hKJle hJI
  have hgen : conjugateSpanBy KJ ((T : Subgroup G).subgroupOf J) ⊔
      (F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf J = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_conjugateSpanBy,map_subgroupOf_eq_of_le hKJle,
      map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hJ),
      map_subgroupOf_eq_of_le (show F.Li L 1 ⊔ (T : Subgroup G) ≤ J from le_sup_right)]
    simpa only [←MonoidHom.range_eq_map] using (range_subtype J).symm
  have hnJ : ¬ KJ.Normal := by
    intro hnJ
    have hnorm := (normal_subgroupOf_iff_le_normalizer hKJle).mp hnJ
    have hTnorm : (T : Subgroup G) ≤ normalizer (K.map I.subtype : Set G) :=
      (F.sylow_le_of_mem_Hz hJ).trans hnorm
    have hrel := subgroupOf_mono I hTnorm
    rw [subgroupOf_normalizer_eq (map_subtype_le K)] at hrel
    have hS : ((T : Subgroup G).subgroupOf I) ≤ normalizer (K : Set I) := by
      simpa only [subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hrel
    have hi := ((Chapter1.Section02.proposition_1_2_1_three_index_knownSimple
      (local_star_sqtk h I hI) hK).resolve_left hn).1
    exact (T.subtype (F.sylow_le_of_mem_Hz hI)).not_dvd_index
      (by simpa only [hi, Sylow.coe_subtype] using index_dvd_of_le hS)
  let e : K ≃* KJ := (equivMapOfInjective K I.subtype I.subtype_injective).trans
    (subgroupOfEquivOfLe hKJle).symm
  let eq : (K ⧸ pCore 2 K) ≃* (KJ ⧸ pCore 2 KJ) :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  have hm := ((local_reduced_component_catalogue_at h hab structural previous faithful
    J hJ KJ hKJ hgen).2 hnJ).transport eq
  rcases hm with hm | ⟨m,hm,he⟩ | hm
  · exact hm
  · exact (local_component_not_suzuki_at d h hab structural previous faithful earlier I hI K hK m hm he).elim
  · obtain ⟨E,_,_,hE,⟨e⟩⟩ := hm
    let eQ := (e.trans (Matrix.PSL3.binaryEquivPsl2Seven E hE)).trans
      Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two
    let eK : Chapter13.Section08.Source.starImage I (K.map I.subtype) ≃* Matrix.PSL3Two.PSL := by
      change (((K.map I.subtype).comap I.subtype).map (QuotientGroup.mk' (pCore 2 I))) ≃* _
      rw [comap_map_eq_self_of_injective I.subtype_injective]
      exact (cComponentTwoCoreQuotientEquiv hK).symm.trans eQ
    have hnormal := (OriginalComponentStatement.BinaryThreeContainment.local_linearThree_normal_and_mem_Hz_at
      d h hab structural previous faithful earlier I (K.map I.subtype) hI (map_subtype_le K) hKI eK).1
    exact (hn (by simpa only [subgroupOf,comap_map_eq_self_of_injective I.subtype_injective]
      using hnormal)).elim


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
