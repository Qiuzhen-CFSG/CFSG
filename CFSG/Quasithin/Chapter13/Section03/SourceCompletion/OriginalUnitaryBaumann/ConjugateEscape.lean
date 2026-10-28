module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryBaumann.Characteristic
public import CFSG.Quasithin.ChapterC.Section06.General
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerFixedLine

/-!
# The original unitary block gives an escaping module conjugate

For a short component, the chosen module is exactly [O₂(L),L]. The
maximal-local uniqueness hypothesis supplies the no-common-normal-subgroup
condition in C.6.2. With the established product-core containment, C.6.3(1)
then supplies a right conjugate V^x outside O₂(L Baum(R)), with x in the
literal ambient Baumann normalizer. All normality assertions are relative
to LT. The block premise is discharged by the Frattini-small source consumer.

Source: Aschbacher--Smith C.6.2--3 and 13.3.10(2), printed pp.166--167,888.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

theorem unitary_baumann_exists_escaping_conjugate_of_short
    (h : Hypothesis1331 T L) (chosen : ChosenModule T L V)
    (hmax : L ∈ Chapter1.LStar G (T : Subgroup G))
    (eL : (L ⧸ pCore 2 L) ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (R : Subgroup G) (hRT : R ≤ (T : Subgroup G))
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hQ : (L ⊔ ChapterB.baumann R).pCoreIn 2 ≤ ChapterB.baumann R)
    (hshort : ChapterC.IsShort L)
    (hout : ¬ normalizer (ChapterB.baumann R : Set G) ≤ normalizer (L : Set G)) :
    ∃ x ∈ normalizer (ChapterB.baumann R : Set G),
      ¬ V.map (MulAut.conj x⁻¹).toMonoidHom ≤ (L ⊔ ChapterB.baumann R).pCoreIn 2 := by
  let B := ChapterB.baumann R
  let N := normalizer (B : Set G)
  have hBT : B ≤ (T : Subgroup G) := inf_le_left.trans hRT
  have hTN : (T : Subgroup G) ≤ N := hTR.trans (normalizer_le_normalizer_baumann R)
  have hBV : V = ⁅L.pCoreIn 2,L⁆ := (RecognitionSource.FusionReducibleNormalizer.chosen_eq_blockU chosen hshort).trans
    RecognitionSource.FusionReducibleNormalizer.block_module_eq_commutator
  have hres : twoResidualAmbient L = L := by
    have hi : twoResidualSubgroup L = ⊤ := by
      apply top_unique
      apply le_sInf
      rintro N ⟨hn,n,hi⟩
      let := hn
      have hp : IsPGroup 2 (L ⧸ N) := IsPGroup.iff_card.mpr
        ⟨n,by simpa only [index_eq_card] using hi⟩
      rw [hshort.twoPerfect N hn hp]
    rw [twoResidualAmbient,hi,← MonoidHom.range_eq_map,range_subtype]
  have hn (W : Subgroup G) (hne : W ≠ ⊥) (hWB : W ≤ B)
      (hW : (W.subgroupOf (L ⊔ (T : Subgroup G))).Normal) :
      ¬ N ⊓ normalizer (B : Set G) ≤ N ⊓ normalizer (W : Set G) := by
    intro hnW
    have hWX : W ≤ L ⊔ (T : Subgroup G) := hWB.trans (hBT.trans le_sup_right)
    have hnormal : L ⊔ (T : Subgroup G) ≤ normalizer (W : Set G) :=
      (normal_subgroupOf_iff_le_normalizer hWX).mp hW
    have hc := chosen.normal_subgroup_normalizer_le
      (unitary_original_hypothesis1223 h hmax eL).toHypothesis1221 hWX hne hnormal
    apply hout
    exact (show N ≤ normalizer (W : Set G) from
      (inf_idem N).ge.trans (hnW.trans inf_le_right)).trans hc
  obtain ⟨x,hx,he⟩ := ChapterC.c6_3_exists_escaping_conjugate L B
    (T : Subgroup G) N (hBT.trans chosen.sylow_normalizes_component) hres hQ
    (hBV ▸ chosen.ne_bot)
    hBT (normal_subgroupOf_of_le_normalizer hTN) hn
  refine ⟨x,?_,?_⟩
  · exact (sup_le inf_le_left hTN) hx
  · rw [hBV]
    exact he
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
