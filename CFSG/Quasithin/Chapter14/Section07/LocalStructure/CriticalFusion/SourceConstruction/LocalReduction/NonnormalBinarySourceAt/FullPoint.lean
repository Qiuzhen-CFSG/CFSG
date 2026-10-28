module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NonnormalBinarySourceAt.Uniqueness
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NonnormalBinarySourceAt.Torus
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityObstruction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.SourceModels.SylowOvergroupUnique

/-!
# Full-point comparison for the exchanged binary component

The original Sylow-overgroup theorem embeds a moved local component in a
component of the full point normalizer. If the larger component is Sylow
invariant, its actual reduced-local quadratic actor gives an F.9.18 model
and hence Sylow-overgroup uniqueness, contradicting movement of the original
component. Otherwise the field-four reduction applies to the larger
component; Bender quotient containment then identifies the two components.
The same original Sylow orbit is consequently the full point normalizer's
three-residual, with its literal embedding retained.

Source: Aschbacher–Smith, proof of 14.7.32, printed p.1056,
refs/quasithin.pdf; component containment uses 1.2.4 and 1.2.8.2.
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
open Chapter13.Section08.Components Swapped
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- A moved original local component is a component of the full point
normalizer, including the field-four case. Its original Sylow orbit is
the full point normalizer's three-residual. -/
theorem local_nonnormal_component_full_component_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal) :
    (K.subgroupOf F.H).IsCComponent ∧
      (primeToResidual 3 F.H).map F.H.subtype = conjugateSpanBy K (T : Subgroup G) := by
  have hTI := F.sylow_le_of_mem_Hz hI
  have hSyl : Chapter1.IsSylowIn 2 (T : Subgroup G) I :=
    ⟨T.subtype hTI, by rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTI]⟩
  have hKL := Chapter1.mem_L_of_cComponent hI.1.1 hSyl hKI hK
  have hKH : K ≤ F.H := hKI.trans hI.2.1
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape_at F previous)
  have hTH := F.sylow_le_of_mem_Hz hH
  let S := T.subtype hTH
  have hb : K.subgroupOf F.H ∈ Chapter1.L F.H (S : Subgroup F.H) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTH hKH).mp ⟨hKH,hKL⟩
  have hmove : ¬ (T : Subgroup G) ≤ normalizer (K : Set G) := by
    intro hh
    exact hnormal (normal_of_sylow_span_eq I K T hKI hTI
      ((Chapter1.Section02.proposition_1_2_1_three_index_knownSimple
        (local_star_sqtk h I hI) hK).imp_right And.left)
      (le_antisymm (conjugateSpanBy_le le_rfl hh) (le_conjugateSpanBy _ _)))
  obtain ⟨D,⟨hD,hKD⟩,_⟩ := Chapter1.Section02.lemma_1_2_4_containment_of_A_3_12
    (Chapter1.Section02.containment_of_theoremsAC
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)))
    (local_star_sqtk h F.H hH) S hb
  let K₁ := D.map F.H.subtype
  have hK₁H : K₁ ≤ F.H := map_subtype_le _
  have heD : K₁.subgroupOf F.H = D :=
    comap_map_eq_self_of_injective F.H.subtype_injective D
  have hK₁ : (K₁.subgroupOf F.H).IsCComponent := by
    rw [heD]
    exact hD
  have hKK₁ : K ≤ K₁ := by
    have hh := map_mono (f := F.H.subtype) hKD
    change (K.subgroupOf F.H).map F.H.subtype ≤ K₁ at hh
    rw [map_subgroupOf_eq_of_le hKH] at hh
    exact hh
  have hK₁L := Chapter1.mem_L_of_cComponent hH.1.1
    (show Chapter1.IsSylowIn 2 (T : Subgroup G) F.H from
      ⟨S,by rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]⟩) hK₁H hK₁
  have hTmove : ¬ (T : Subgroup G) ≤ normalizer (K₁ : Set G) := by
    intro hn
    have hu := local_sylow_invariant_component_unique_at h hab structural previous faithful
      F.H K₁ hH hK₁H hK₁ hn
    exact hmove (Chapter1.Section02.MovedMaximality.local_chain_normalizes_of_sylow_overgroup_unique
      T hKL hK₁L hKK₁ hn hu)
  have hnon : ¬ (K₁.subgroupOf F.H).Normal := by
    intro hn
    exact hTmove (hTH.trans ((normal_subgroupOf_iff_le_normalizer hK₁H).mp hn))
  have hm₁ := local_nonnormal_component_field_four_at d h hab structural previous faithful earlier
    F.H K₁ hH hK₁H hK₁ hnon
  have hmD : ClassicalGroup.IsPSL (D ⧸ pCore 2 D) 2 4 := by
    have hh := hm₁.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK₁)
    rw [heD] at hh
    exact hh
  have he : K.subgroupOf F.H = D :=
    Chapter1.Section02.MovedMaximality.eq_of_bender_quotient S hb.1 hD hKD
      (.linear 2 (by decide) (by simpa using hmD))
  have hfull : (K.subgroupOf F.H).IsCComponent := he ▸ hD
  have hnonF : ¬ (K.subgroupOf F.H).Normal := by
    intro hn
    exact hmove (hTH.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hn))
  have hmF := local_nonnormal_component_field_four_at d h hab structural previous faithful earlier
    F.H K hH hKH hfull hnonF
  have hmoving : conjugateSpanBy K (T : Subgroup G) ≠ K := by
    intro hh
    exact hmove (hh ▸ le_normalizer_conjugateSpanBy K (T : Subgroup G))
  exact ⟨hfull,local_binary_threeResidual_at h hab structural previous faithful F.H K hH hKH hfull
    (show 2 ≤ 2 by decide) (by simpa using hmF) hmoving⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
