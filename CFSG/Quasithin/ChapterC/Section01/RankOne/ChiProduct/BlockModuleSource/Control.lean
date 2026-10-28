module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.BlockModuleSource.SourceTypes
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ExceptionalSevenControl
public import Theory.SpecificGroups.Alternating.SevenComponent.Normality

/-!
# Excluding the exceptional block in the original C.1.28 source

The actual A₇ core quotient forces ambient normality at three-rank at most
two. The proved C.1.23 control theorem places the exceptional block in the
characteristic-normalizer closure, contradicting containment of the original
escaping seed. Thus the original block lift gives an escaping χ-block.

Source: Aschbacher--Smith C.1.23(2), C.1.28, printed pp.129,133--134.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.BlockModuleSource
open ChapterB SourceInduction
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Strong quasithinness normalizes the exceptional block; genuine C.1.23
places it in characteristic-normalizer control. -/
theorem exceptional_block_le_control
    (hG : IsStronglyQuasithin G) (T : Sylow 2 G) (L : Subgroup G)
    (hL : IsBlock L) (hm : IsExceptionalA7Block L) :
    L ≤ (T : Subgroup G).characteristicNormalizerClosure := by
  obtain ⟨e⟩ := hm.2.1
  let : L.Normal := alternatingGroup.SevenComponent.normal_of_twoPerfect_core_quotient
    hL.subnormal hL.short.twoPerfect e (hG 3 (by decide) (by decide))
  exact ExceptionalSevenControl.exceptionalA7_le_characteristicNormalizerClosure T L hL hm
    le_normalizer_of_normal

/-- A local source χ-seed outside control lies in an actual ambient χ-block.
The exceptional A₇ possibility is excluded by the full original control proof. -/
theorem source_outside_chi_of_local_seed
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (h4 : ProjectiveLine.IrreducibleClassificationInput.{u,u} KnownSimple.IsKnownSimple)
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (M K V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hM : (T : Subgroup G).characteristicNormalizerClosure ≤ M)
    (hout : ¬ K ≤ M)
    (hV : V = normalClosure (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hK : IsChiBlock K) (hs : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal)
    (hU : (blockU K).map K.subtype ≤ V)
    (hmove : let q := QuotientGroup.mk' (centralizer (V : Set G));
      let ρ := NormalElementaryQuotient.representation V q (QuotientGroup.mk'_surjective _)
        (QuotientGroup.ker_mk' _);
      K.map q = ⁅K.map q, generatedBy {A | IsBestOffender ρ A}
        ((T.mapSurjective (QuotientGroup.mk'_surjective (centralizer (V : Set G)))) :
          Subgroup (G ⧸ centralizer (V : Set G)))⁆) :
    ∃ L : Subgroup G, K ≤ L ∧ ¬ L ≤ M ∧ IsChiBlockIn L ∧
      (blockU L).map L.subtype ≤ V := by
  obtain ⟨L,hKL,hL,hUL,htype⟩ := source_chi_or_exceptional_block
    hA hC h4 hG T hchar K V hV hK hs hU hmove
  have hn : ¬ L ≤ M := fun hh => hout (hKL.trans hh)
  rcases htype with hchi | hex
  · exact ⟨L,hKL,hn,⟨hL,hchi⟩,hUL⟩
  · exact (hn ((exceptional_block_le_control hG.stronglyQuasithin T L hL hex).trans hM)).elim

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.BlockModuleSource
