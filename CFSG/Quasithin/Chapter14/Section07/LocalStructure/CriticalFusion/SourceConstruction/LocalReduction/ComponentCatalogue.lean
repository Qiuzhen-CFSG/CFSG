module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ComponentActors
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.SourceModels.PairedActor

/-!
# The concrete component catalogue in the original local family

Reduce an actual component to its Sylow orbit joined with L₁T. The
previously constructed quadratic actor is faithful on that whole orbit.
For a normal component, A.3.6 bounds the center and the proved small-ratio
classification gives the full F.9.18 group catalogue. For an exchanged
component, the actual index-two normalizer and A.3.8 models give the
three-family list. The exact intrinsic two-core quotient equivalences
transport these results back to every original local component.

These are group classifications, not the module alternatives or component
normality of 14.7.32. The subsequent Suzuki exclusion and larger-field
reductions still use the original point and module geometry.

Source: Aschbacher–Smith, 14.7.30, printed p.1055; F.9.18(4–5),
printed pp.325–326, refs/quasithin.pdf.
-/

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

private theorem catalogue_transport {D E : Type*} [Group D] [Group E]
    (e : D ≃* E) (h : Models.ComponentModelOrSuzuki E) : Models.ComponentModelOrSuzuki D := by
  rcases h with h | ⟨m,hm,⟨f⟩⟩
  · exact Or.inl (h.of_mulEquiv e)
  · exact Or.inr ⟨m,hm,⟨e.trans f⟩⟩

private theorem nonnormal_catalogue {D : Type*} [Group D]
    (h : SourceModels.NonnormalF918Models D) : Models.ComponentModelOrSuzuki D := by
  rcases h with ⟨n,hn,he⟩ | he | he
  · exact Or.inl (.linear_two n hn he)
  · exact Or.inr he
  · exact Or.inl (.projective_three false 1 (by simp [Models.ThreeParameter]) (by simpa [Chapter1.Section02.LocalModels.IsPSLSign] using he))

/-- The F.9.18 group catalogue on the actual reduced local, including the
sharper three-family list when the component is not normal. -/
theorem local_reduced_component_catalogue
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (K : Subgroup I) (hK : K.IsCComponent)
    (hgen : conjugateSpanBy K ((T : Subgroup G).subgroupOf I) ⊔
      (F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I = ⊤) :
    Models.ComponentModelOrSuzuki (K ⧸ pCore 2 K) ∧
      (¬ K.Normal → SourceModels.NonnormalF918Models (K ⧸ pCore 2 K)) := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let B := K.map q
  let N := conjugateSpanBy K ((T : Subgroup G).subgroupOf I)
  let X := N.map q
  let S : Sylow 2 (HStar I) :=
    (T.subtype (F.sylow_le_of_mem_Hz hI)).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 I))
  have hNI : N.Normal := local_component_sylow_span_normal h I hI K hK
  let : X.Normal := hNI.map q (QuotientGroup.mk'_surjective _)
  have hgen' : X ⊔ ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I).map q = ⊤ := by
    rw [←Subgroup.map_sup,hgen,map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  obtain ⟨hU,a,_,A,hAR,hA,hquad,hcod,hfaith⟩ :=
    local_prime_supplement_quadratic_actor h hab structural previous I hI X hgen'
  let := hU
  have hB := local_component_star_isComponent h hab structural previous faithful I hI K hK
  let : IsQuasisimple B := hB.2
  have hs := local_star_sqtk h I hI
  have horbit : X = componentOrbit B (S : Subgroup (HStar I)) := by
    rw [show X = (conjugateSpanBy K ((T : Subgroup G).subgroupOf I)).map q from rfl,
      map_conjugateSpanBy,conjugateSpanBy_eq_iSup_conj]
    rfl
  rw [horbit] at hfaith
  have hRT : F.Ri L 1 ≤ (T : Subgroup G) := by
    let E := F.Li L 1 ⊔ (T : Subgroup G)
    have hh := pCoreIn_le_sylow E (T.subtype (show (T : Subgroup G) ≤ E from le_sup_right))
    change E.pCoreIn 2 ≤ (T : Subgroup G)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ E from le_sup_right)] using hh
  have hAS : A.map q ≤ (S : Subgroup (HStar I)) :=
    map_mono (hAR.trans (subgroupOf_mono I hRT))
  by_cases hn : B.Normal
  · let := hn
    have he : componentOrbit B (S : Subgroup (HStar I)) = B :=
      le_antisymm (iSup_conjugates_le_of_le_normalizer B _ B le_rfl
        le_normalizer_of_normal) (le_componentOrbit _ _)
    rw [he] at hfaith
    have hc := ChapterA.Section03.SourceEmbeddings.quasisimple_containing_component_models_knownSimple
      hs (pCore_quotient_pCore_eq_bot 2) hB.isCComponent
    have hcenter : Nat.card (center B) = 1 ∨ Nat.card (center B) = 3 := by
      rcases hc with ⟨hs,_⟩ | ⟨⟨e⟩,_⟩
      · let := hs
        exact Or.inl (Subgroup.card_eq_one.mpr CoverModels.center_eq_bot_of_simple)
      · exact Or.inr ((Nat.card_congr e.toEquiv).trans (Nat.card_zmod 3))
    have hm := SourceModels.f918Models_of_quadratic_actor a.representation B (A.map q)
      a.faithful hcenter hs hA hquad hcod hfaith
    refine ⟨catalogue_transport (cComponentTwoCoreQuotientEquiv hK)
      (CoverModels.SourceApplication.classified_of_source hm
        (hc.elim (fun hh => Or.inl hh.1) Or.inr)),?_⟩
    intro hnon
    let : Group.IsNilpotent (pCore 2 I) := pCore_isPGroup.isNilpotent
    exact (hnon (cComponent_normal_of_quotient_normal hK (pCore 2 I) hn)).elim
  · obtain ⟨hi,hm⟩ := (ChapterA.Section03.NonnormalOrdinary.index_and_model_knownSimple
      hs (pCore_quotient_pCore_eq_bot 2) B hB.isCComponent).resolve_left hn
    have hmove : ¬ (S : Subgroup (HStar I)) ≤ normalizer (B : Set (HStar I)) := by
      intro hh
      exact S.not_dvd_index (by simpa only [hi] using index_dvd_of_le hh)
    have hc := SourceModels.nonnormal_models_of_quadratic_actor a.representation B S (A.map q)
      hB hs hm hi hmove a.faithful hAS hA hquad hcod hfaith
    have hq := hc.transport (cComponentTwoCoreQuotientEquiv hK)
    exact ⟨nonnormal_catalogue hq,fun _ => hq⟩

/-- Source 14.7.30's concrete group catalogue for every original component,
transported from its actual reduced local through the intrinsic two-core quotient. -/
theorem local_component_catalogue_or_suzuki
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (K : Subgroup I) (hK : K.IsCComponent) :
    Models.ComponentModelOrSuzuki (K ⧸ pCore 2 K) := by
  let N := conjugateSpanBy (K.map I.subtype) (T : Subgroup G)
  let J := N ⊔ (F.Li L 1 ⊔ (T : Subgroup G))
  let KJ := (K.map I.subtype).subgroupOf J
  obtain ⟨_,hJI,hJ⟩ := local_component_reduced_mem_Hz h structural I hI K hK
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
    simpa only [← MonoidHom.range_eq_map] using (range_subtype J).symm
  let e : K ≃* KJ := (equivMapOfInjective K I.subtype I.subtype_injective).trans
    (subgroupOfEquivOfLe hKJle).symm
  let eq : (K ⧸ pCore 2 K) ≃* (KJ ⧸ pCore 2 KJ) :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  exact catalogue_transport eq
    (local_reduced_component_catalogue h hab structural previous faithful J hJ KJ hKJ hgen).1

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
