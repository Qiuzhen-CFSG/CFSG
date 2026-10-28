module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointOrdinaryBlockCore
public import Theory.GroupTheory.Commutator.NormalClosure
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.ReducedNormal.SubspaceMinimality
public import Theory.GroupTheory.CentralizerResidualProducts

/-!
# The original exceptional triple-six block

The actual point residual normally generates K modulo its two-core.
The identified full core O2(Lt)=U therefore propagates [O2(K),Lt]≤U
to [O2(K),K]=U. The original chosen module and its equivariant hexacode
chart then give every defining clause of the exceptional Ahat6 block.

Source: Aschbacher--Smith 12.7.7, printed p.841. All groups and the
whole original U are retained; no block or commutator premise is added.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

private theorem normal_generation {X : Type*} [Group X] [Finite X]
    (hp : IsPPerfect 2 X) [IsQuasisimple (X ⧸ pCore 2 X)]
    (J : Subgroup X) [Group.IsPerfect J] (hj : ¬ J ≤ pCore 2 X) :
    normalClosure (J : Set X) = ⊤ := by
  let N := normalClosure (J : Set X)
  let q := QuotientGroup.mk' (pCore 2 X)
  let : (N.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hi : N.map q = ⊤ := by
    rcases IsQuasisimple.normal_le_center_or_eq_top (N.map q) with hc | ht
    · exact (map_not_le_of_isPerfect_of_isSolvable J q
        (by simpa only [q,QuotientGroup.ker_mk'] using hj) (center _)
        ((map_mono le_normalClosure).trans hc)).elim
    · exact ht
  have hs : N ⊔ pCore 2 X = ⊤ := by
    have hh := congrArg (comap q) hi
    simpa only [q,comap_map_eq,QuotientGroup.ker_mk',comap_top] using hh
  exact hp N inferInstance (isPGroup_quotient_of_sup_eq_top N (pCore 2 X) pCore_isPGroup hs)

/-- The full original core commutator is exactly the chosen U. -/
theorem tripleSix_ordinary_core_commutator
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T K) (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hcenter :
      let H := centralizer ({(t : G)} : Set G)
      let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
      centerIn (conjugateSpanBy Lt H) = tripleSixPoint D a t)
    (eB :
      let H := centralizer ({(t : G)} : Set G)
      let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
      let B := conjugateSpanBy Lt H
      B ⧸ center B ≃* Matrix.PSL3Four.PSL) :
    ⁅K.pCoreIn 2,K⁆ = U ∧ (ChapterC.blockU K).map K.subtype = U := by
  let H := centralizer ({(t : G)} : Set G)
  let C := K ⊓ H
  let Lt := (pResidual 2 C).map C.subtype
  have hLK : Lt ≤ K := (map_subtype_le _).trans inf_le_left
  have hc : Lt.pCoreIn 2 = U :=
    (tripleSixPointResidual_ordinary_block_core D a t ht heven hcenter eB).2.1
  have hKC : K.pCoreIn 2 ≤ C := le_inf (pCoreIn_le 2 K)
    (((pCoreIn_mono_of_normalizes le_sup_left
      (sup_le K.le_normalizer D.sylow_normalizes_component)).trans D.core_centralizes).trans
        (centralizer_le (Set.singleton_subset_iff.mpr t.property)))
  have hnL : K.pCoreIn 2 ≤ normalizer (Lt : Set G) :=
    hKC.trans (C.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image C (pResidual 2 C)))
  have hnQ : Lt ≤ normalizer (K.pCoreIn 2 : Set G) := hLK.trans
    (K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))
  have hcomm : ⁅K.pCoreIn 2,Lt⁆ ≤ U := by
    rw [←hc]
    exact (le_inf (le_normalizer_iff_commutator_le_right.mp hnL)
      (le_normalizer_iff_commutator_le_left.mp hnQ)).trans (inf_pCoreIn_le_of_le 2 hLK)
  let J := Lt.subgroupOf K
  let W := U.subgroupOf K
  let : W.Normal := normal_subgroupOf_of_le_normalizer D.normalizes
  let : Group.IsPerfect Lt := tripleSixPointCentralizerResidual_perfect D a t ht heven
  let : Group.IsPerfect J := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hLK).symm.toMonoidHom) (subgroupOfEquivOfLe hLK).symm.surjective
  let : IsQuasisimple (K ⧸ pCore 2 K) := h.quasisimple
  have hj : ¬ J ≤ pCore 2 K := by
    intro hj
    have hLQ : Lt ≤ K.pCoreIn 2 := by
      rw [←map_subgroupOf_eq_of_le hLK]
      exact map_mono hj
    have hLc : Lt ≤ Lt.pCoreIn 2 :=
      (le_inf le_rfl hLQ).trans (inf_pCoreIn_le_of_le 2 hLK)
    have hcore : pCore 2 Lt = ⊤ := by
      apply map_injective Lt.subtype_injective
      rw [←MonoidHom.range_eq_map,range_subtype]
      exact le_antisymm (pCoreIn_le 2 Lt) hLc
    have hq := Nat.card_congr (tripleSixPointResidualQuotientEquiv D a t ht heven).toEquiv
    change Nat.card (Lt ⧸ pCore 2 Lt) = Nat.card (alternatingGroup (Fin 5)) at hq
    rw [hcore,nat_card_alternatingGroup] at hq
    let : Subsingleton (Lt ⧸ (⊤ : Subgroup Lt)) := QuotientGroup.subsingleton_quotient_top
    norm_num [Nat.factorial] at hq
  have hg := normal_generation h.maximal_faithful.2.1.2.1 J hj
  have hb : ⁅pCore 2 K,J⁆ ≤ W := by
    intro x hx
    have hm := mem_map_of_mem K.subtype hx
    rw [map_commutator,map_subgroupOf_eq_of_le hLK] at hm
    exact hcomm hm
  have hb' := commutator_normalClosure_le_of_normal (pCore 2 K) J W hb
  rw [hg] at hb'
  have hblock : (ChapterC.blockU K).map K.subtype ≤ U := by
    simpa only [W,ChapterC.blockU,map_subgroupOf_eq_of_le D.le_component] using map_mono (f := K.subtype) hb'
  have he : ⁅K.pCoreIn 2,K⁆ = U := le_antisymm (by
    simpa only [ChapterC.blockU,pCoreIn,map_commutator,←MonoidHom.range_eq_map,range_subtype] using hblock)
    (by rw [D.eq_commutator]; exact commutator_mono D.le_componentCore le_rfl)
  refine ⟨he,?_⟩
  simpa only [ChapterC.blockU,pCoreIn,map_commutator,←MonoidHom.range_eq_map,range_subtype] using he

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

/-- The original component is an exceptional Ahat6 block, with its entire
block module equal to the unchanged original U. -/
theorem original_tripleSix_ordinary_exceptional_block
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T K) (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hcenter :
      let H := centralizer ({(t : G)} : Set G)
      let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
      centerIn (conjugateSpanBy Lt H) = tripleSixPoint D a t)
    (eB :
      let H := centralizer ({(t : G)} : Set G)
      let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
      let B := conjugateSpanBy Lt H
      B ⧸ center B ≃* Matrix.PSL3Four.PSL) :
    ChapterC.IsExceptionalAhat6Block K ∧ (ChapterC.blockU K).map K.subtype = U := by
  have hB := (tripleSix_ordinary_core_commutator h D a t ht heven hcenter eB).2
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
