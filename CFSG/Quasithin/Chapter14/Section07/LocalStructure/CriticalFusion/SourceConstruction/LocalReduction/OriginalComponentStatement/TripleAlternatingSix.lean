module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.TripleAlternatingSix.Module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource.SixResidual
public import Theory.GroupTheory.PResidual.NormalizedImageContainment

/-!
# Excluding the original triple cover of A₆

The actual component is normal and its point cubic is central. Passing to its
literal K T local retains the original structural hypotheses. Critical-module
geometry supplies a faithful hexacode actor, which preserves the two A₆
parabolic types. The original solvable-overgroup theorem puts every relevant
overgroup in the proper overlap with N_G(L). The concrete A₆ comparison forces
a Sylow actor interchanging those types, giving the contradiction.

The final theorem takes only the original same-G,T earlier hypotheses and an
actual intrinsic component quotient isomorphism. In particular 14.7.47,
component containment, a selected module, and a diagram action are not inputs.
Source: Aschbacher--Smith 14.7.47, printed p.1064, using 14.7.28--29 and
F.9.13--18; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
open Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers
open Reduction Reduction.LocalGeometry Reduction.LocalGeometry.CoverParabolics
open Theory.GroupAction.PCoreCentralModelAction
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem point_le_coverResidual_of_star_eq
    (I K A : Subgroup G) (hKI : K ≤ I) (hAI : A ≤ I)
    [(K.subgroupOf I).Normal]
    (hK : (K.subgroupOf I).IsCComponent)
    (hc : Nat.card (center (K ⧸ pCore 2 K)) = 3)
    (hAp : IsPPerfect 2 A)
    (he : Chapter13.Section08.Source.starImage I A =
      (center (Chapter13.Section08.Source.starImage I K)).map
        (Chapter13.Section08.Source.starImage I K).subtype) : A ≤ coverResidualIn K := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let Y := (coverResidualIn K).subgroupOf I
  let : Y.Normal := coverResidualIn_normal I K hKI
  have hp : IsPPerfect 2 (A.subgroupOf I) := hAp.of_surjective
    (subgroupOfEquivOfLe hAI).symm.toMonoidHom (subgroupOfEquivOfLe hAI).symm.surjective
  have hm : (A.subgroupOf I).map q ≤ Y.map q := by
    change Chapter13.Section08.Source.starImage I A ≤
      Chapter13.Section08.Source.starImage I (coverResidualIn K)
    rw [he,ModuleRecognition.residual_star_eq_center I K hKI hK hc]
  have hle : A.subgroupOf I ≤ Y := isPPerfect_le_of_map_le_of_kernel_normalizes
    q _ _ hp (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
    (by rw [normalizer_eq_top]; exact le_top) hm
  have hh := map_mono (f := I.subtype) hle
  rwa [map_subgroupOf_eq_of_le hAI,
    map_subgroupOf_eq_of_le ((coverResidualIn_le K).trans hKI)] at hh

private noncomputable def tripleSixCentralEquiv {D : Type*} [Group D]
    (e : D ≃* Atlas.Codes.HexEvenAutomorphisms) :
    (D ⧸ center D) ≃* AlternatingSix.ShadowLocal.A6 :=
  (QuotientGroup.congr _ _ e (by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact (centerCongr e ⟨y,hy⟩).property
    · intro hx
      exact ⟨e.symm x,(centerCongr e.symm ⟨x,hx⟩).property,e.apply_symm_apply x⟩)).trans
    Hexacode.even_quotient_center_equiv

/-- In the reduced original local the forced Sylow diagram actor contradicts
the faithful hexacode action on the actual section. -/
theorem reduced_triple_alternatingSix_impossible_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (K : Subgroup G) (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (e : (K ⧸ pCore 2 K) ≃* Atlas.Codes.HexEvenAutomorphisms)
    (hgen : I = K ⊔ (T : Subgroup G)) : False := by
  let C := K.subgroupOf I
  let ec := subgroupOfEquivOfLe hKI
  let eC := (QuotientGroup.congr _ _ ec (pCore_map_iso 2 ec)).trans e
  let hn := local_triple_alternatingSix_normal_at h I hI C hK eC
  have hg : C ⊔ (T : Subgroup G).subgroupOf I = ⊤ := by
    rw [←subgroupOf_sup hKI (F.sylow_le_of_mem_Hz hI),←hgen,subgroupOf_self]
  obtain ⟨_,_,_,_,_,hz⟩ := reduced_triple_alternatingSix_structure_at
    d h hab structural previous faithful earlier I hI C hK eC hg
  have hc : Nat.card (center (K ⧸ pCore 2 K)) = 3 :=
    (Nat.card_congr (centerCongr e).toEquiv).trans Hexacode.even_center_card
  have hpoint : F.Li L 1 ≤ coverResidualIn K := point_le_coverResidual_of_star_eq
    I K (F.Li L 1) hKI (F.Li_one_le_of_mem_Hz hI) hK hc
    (isPPerfect_embedded_pResidual 2 _) hz
  have hspan : solvableOvergroupSpan I (coverResidualIn K) (T : Subgroup G) ≤
      I ⊓ normalizer (L : Set G) := by
    apply sSup_le
    rintro J ⟨hbase,hJI,hs⟩
    exact le_inf hJI (WholeResidualAssembly.GuardedSource.solvable_point_overgroup_le_normalizer
      d h hab structural previous faithful earlier J (hJI.trans hI.2.1)
      ((sup_le_sup_right hpoint _).trans hbase) hs)
  have hproper : I ⊓ normalizer (L : Set G) < I := lt_of_le_of_ne inf_le_left
    (fun hh => hI.2.2 (hh.ge.trans inf_le_right))
  have ht : Chapter1.IsSylowIn 2 (T : Subgroup G) I :=
    ⟨T.subtype (F.sylow_le_of_mem_Hz hI),map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hI)⟩
  let eZ := tripleSixCentralEquiv e
  obtain ⟨t,htbad⟩ := six_source_diagram_actor I K T (I ⊓ normalizer (L : Set G)) hKI hgen
    ht ((centralPreimageQuotientEquiv (pCore 2 K)).trans eZ) hproper hspan
  obtain ⟨φ,hφ,hφK⟩ := reduced_triple_alternatingSix_actor_at
    d h hab structural previous faithful earlier I hI C hK eC hg
  apply htbad
  have hh := DynkinExclusion.sourceAction_natural_of_actor I K hKI hK eZ φ hφ hφK
    (QuotientGroup.mk' (pCore 2 I) ⟨t,(F.sylow_le_of_mem_Hz hI) t.property⟩)
  rwa [Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource.sourceAction_eq_centralModelAction]
    at hh

/-- The original local component cannot have intrinsic quotient 3.A₆.
All earlier structural assumptions remain at the same original G,T. -/
theorem local_triple_alternatingSix_component_impossible_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* Atlas.Codes.HexEvenAutomorphisms) : False := by
  let K := C.map I.subtype
  have hKI : K ≤ I := map_subtype_le _
  have hK : (K.subgroupOf I).IsCComponent := by
    simpa only [K,subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hC
  have hnC := local_triple_alternatingSix_normal_at h I hI C hC e
  have hn : (K.subgroupOf I).Normal := by
    simpa only [K,subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hnC
  have hTN : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (F.sylow_le_of_mem_Hz hI).trans ((normal_subgroupOf_iff_le_normalizer hKI).mp hn)
  have hspan : conjugateSpanBy K (T : Subgroup G) = K :=
    le_antisymm (conjugateSpanBy_le le_rfl hTN) (le_conjugateSpanBy _ _)
  have hc : Nat.card (center (C ⧸ pCore 2 C)) = 3 :=
    (Nat.card_congr (centerCongr e).toEquiv).trans Hexacode.even_center_card
  have hz : center (C ⧸ pCore 2 C) ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hc
    omega
  have hin := (local_nontrivial_component_center_at
    d h hab structural previous faithful earlier I hI C hC hz).1
  let J := K ⊔ (T : Subgroup G)
  have hJ : J ∈ F.Hz L (normalizer (L : Set G)) := by
    have hh := (local_component_reduced_mem_Hz_at h structural I hI C hC).2.2
    change conjugateSpanBy K (T : Subgroup G) ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) ∈ _ at hh
    rwa [hspan,←sup_assoc,sup_eq_left.mpr hin] at hh
  have hJI : J ≤ I := sup_le hKI (F.sylow_le_of_mem_Hz hI)
  have hKJ : (K.subgroupOf J).IsCComponent := hK.subgroupOf_of_le le_sup_left hJI
  let ec := equivMapOfInjective C I.subtype I.subtype_injective
  let eK := (QuotientGroup.congr _ _ ec (pCore_map_iso 2 ec)).symm.trans e
  exact reduced_triple_alternatingSix_impossible_at
    d h hab structural previous faithful earlier J hJ K le_sup_left hKJ eK rfl

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
