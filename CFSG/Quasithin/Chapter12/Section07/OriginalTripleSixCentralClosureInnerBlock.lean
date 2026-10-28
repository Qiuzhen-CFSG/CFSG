module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureInnerBlockCore
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.GroupTheory.ReducedNormal.SubspaceMinimality
public import Theory.Representation.HexacodeAction.CentralCharacter
public import Theory.GroupTheory.CentralizerResidualProducts

/-!
# The original exceptional triple-six block in the inner branch

The chief-displacement argument has identified the entire original block
module with U. Its genuine hexacode chart and original chosen-module data
now supply every short-group and exceptional-block clause, including the
literal action kernel and the irreducible subgroup interval.

Source: Aschbacher--Smith 12.7.16, printed p.844.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

private theorem chart_fixed_and_kernel (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) :
    U ⊓ centralizer (K : Set G) = ⊥ ∧
      (centralizer (U : Set G)).subgroupOf K = pCore 2 K := by
  let e := tripleSixPointCoordinates D a
  have hz : U ⊓ centralizer (K : Set G) = ⊥ := by
    apply bot_unique
    intro u hu
    let v : U := ⟨u,hu.1⟩
    obtain ⟨k,hk⟩ := QuotientGroup.mk'_surjective (pCore 2 K)
      (a.groupEquiv.symm Atlas.Codes.hexEvenZ)
    have hf := (tripleSixPoint_actor_fixes_iff D a v k).mpr
      (mem_centralizer_singleton_iff.mpr (hu.2 k k.property))
    rw [hk,a.groupEquiv.apply_symm_apply] at hf
    have hv : (e v).toAdd = 0 := (Hexacode.scalar_fixed_iff _).mp hf
    have he : e v = 1 := hv
    have hv1 := e.injective (he.trans e.map_one.symm)
    exact mem_bot.mpr (congrArg Subtype.val hv1)
  refine ⟨hz,le_antisymm ?_ ?_⟩
  · intro k hk
    apply (QuotientGroup.eq_one_iff k).mp
    apply a.groupEquiv.injective
    rw [a.groupEquiv.map_one]
    apply Subtype.ext
    apply Hexacode.action_injective
    apply LinearMap.ext
    intro w
    obtain ⟨v,hv⟩ := e.surjective (Multiplicative.ofAdd w)
    have hf := (tripleSixPoint_actor_fixes_iff D a v k).mpr
      (mem_centralizer_singleton_iff.mpr ((hk v v.property).symm))
    change Hexacode.evenAction (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k))
      (e v).toAdd = (e v).toAdd at hf
    rw [hv] at hf
    exact hf
  · intro k hk
    exact ((pCoreIn_mono_of_normalizes le_sup_left
      (sup_le K.le_normalizer D.sylow_normalizes_component)).trans D.core_centralizes)
        (mem_map_of_mem K.subtype hk)

/-- The original component is an exceptional Ahat6 block, retaining the
whole original U as its block module in the actual inner closure branch. -/
theorem original_tripleSix_central_closure_inner_exceptional_block
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z:G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z:G)} : Set G)).pCoreIn 2)
    (hinner : inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G)))) ≤ inducedAutomizer U K) :
    ChapterC.IsExceptionalAhat6Block K ∧ (ChapterC.blockU K).map K.subtype=U := by
  have hB := (original_tripleSix_central_closure_inner_block_core
    h structural D a z hz hzT hnot hinner).2
  let eU : ChapterC.blockU K ≃* U :=
    ((ChapterC.blockU K).equivMapOfInjective K.subtype K.subtype_injective).trans
      (MulEquiv.subgroupCongr hB)
  let := D.elementary
  let : IsElementaryAbelian 2 (ChapterC.blockU K) :=
    IsElementaryAbelian.of_injective eU.toMonoidHom eU.injective
  obtain ⟨hfix,hker⟩ := chart_fixed_and_kernel D a
  have hfixed : ChapterC.blockU K ⊓ center K = ⊥ := by
    apply bot_unique
    intro u hu
    apply mem_bot.mpr
    apply Subtype.ext
    apply mem_bot.mp
    rw [←hfix]
    refine ⟨hB ▸ mem_map_of_mem K.subtype hu.1,?_⟩
    intro k hk
    exact congrArg K.subtype (mem_center_iff.mp hu.2 ⟨k,hk⟩)
  have hs : ChapterC.IsShort K := by
    refine {
      finite := inferInstance
      twoPerfect := h.maximal_faithful.2.1.2.1
      fitting := h.maximal_faithful.2.1.2.2
      elementary := inferInstance
      central := ?_
      quotient := Or.inl h.quasisimple
      irreducible := ?_ }
    · intro u hu q hq
      apply Subtype.ext
      have hQ := (pCoreIn_mono_of_normalizes
        (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left)
        (sup_le K.le_normalizer D.sylow_normalizes_component)).trans D.core_centralizes
      exact (hQ (mem_map_of_mem K.subtype hq) u (hB ▸ mem_map_of_mem K.subtype hu)).symm
    · rw [ChapterC.BlockModuleIrreducible,hfixed]
      refine ⟨bot_lt_iff_ne_bot.mpr ?_,?_⟩
      · intro he
        apply D.ne_bot
        rw [←hB,he,Subgroup.map_bot]
      · intro N hn _ hNU
        let := hn
        have hNV : N.map K.subtype ≤ U := (map_mono hNU).trans_eq hB
        have hKN : K ≤ normalizer (N.map K.subtype : Set G) := by
          simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
            N.le_normalizer_map K.subtype
        have hh := ReducedNormal.subspaceImage_eq_or_le_centralizer
          (K ⊔ (T : Subgroup G)) K le_sup_left D.irrPlus.isIrrPlus (N.map K.subtype)
          (by change _ ≤ subspaceImage _ D.space; rwa [D.image_eq]) hKN
        change N.map K.subtype = subspaceImage _ D.space ∨ _ at hh
        rw [D.image_eq] at hh
        rcases hh with he | hc
        · right
          exact map_injective K.subtype_injective (he.trans hB.symm)
        · left
          apply map_injective K.subtype_injective
          rw [Subgroup.map_bot]
          exact bot_unique ((le_inf hNV hc).trans hfix.le)
  have hz : Nat.card (center (K ⧸ pCore 2 K)) = 3 :=
    (Nat.card_congr (centerCongr a.groupEquiv).toEquiv).trans Hexacode.even_center_card
  have hA6 : Nonempty (((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ≃*
      alternatingGroup (Fin 6)) :=
    ⟨(QuotientGroup.congr _ _ a.groupEquiv (map_center_equiv _)).trans
      Hexacode.even_quotient_center_equiv⟩
  have hcard : Nat.card (ChapterC.blockU K) = 2^6 := by
    rw [Nat.card_congr eU.toEquiv,
      Nat.card_congr (tripleSixPointCoordinates D a).toEquiv]
    exact Atlas.Codes.hexacode_card
  have hfaith : centralizer (ChapterC.blockU K : Set K) = pCore 2 K := by
    rw [←hker]
    ext k
    constructor
    · intro hk u hu
      obtain ⟨v,hv,hvu⟩ := hB.symm ▸ hu
      exact hvu ▸ congrArg K.subtype (hk v hv)
    · intro hk u hu
      apply Subtype.ext
      exact hk u (hB ▸ mem_map_of_mem K.subtype hu)
  exact ⟨⟨hs,h.quasisimple,hz,hA6,hcard,hfaith⟩,hB⟩

end CFSG.Quasithin.Chapter12.Section07
