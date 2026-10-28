module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingNontrivialCentralizerSource
public import CFSG.Quasithin.Chapter2.Section04.BlockNormality.ChiZeroEmbedding
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.CentralizingCore
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Centralizer
public import Theory.GroupTheory.PrimeRankElementary
/-!
# The actual ordinary component in the nontrivial A5 centralizer

The original centralizer has central two-core D=C_T(L). Its selected full
Sylow normalizes L, so source 1.2.4 gives a normal containing C-component.
The sixteen-element natural layer embeds faithfully through the central
core, forcing the containing component to be quasisimple. The literal local
component, Sylow normalization and centerless-block marks are retained for
the full-Sylow model exclusion; no component or model premise is added.

Source: Aschbacher–Smith 2.4.29, printed p.545, using 1.2.1(5) and 1.2.4.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource ChapterC.Section05.BlockAnalysis
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_nontrivial_centralizer_component
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hne : (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G) ≠ ⊥) :
    let L := d.block.map d.H.subtype
    let D := (T : Subgroup G) ⊓ centralizer (L : Set G)
    let C := centralizer (D : Set G)
    ∃ (S : Sylow 2 C) (K : Subgroup C),
      (S : Subgroup C).map C.subtype = (d.S : Subgroup d.H).map d.H.subtype ∧
      IsComponent C K ∧ K.Normal ∧ L.subgroupOf C ≤ K ∧
      L.subgroupOf C ∈ Chapter1.L C (S : Subgroup C) ∧
      (S : Subgroup C) ≤ normalizer (L.subgroupOf C : Set C) ∧
      Disjoint L (centralizer (L : Set G)) ∧ Nat.card (sourceModule L) = 16 := by
  let L := d.block.map d.H.subtype
  let U := sourceModule L
  let Di := centralizer (d.block : Set d.H)
  let Ui := (blockU d.block).map d.block.subtype
  let D := (T : Subgroup G) ⊓ centralizer (L : Set G)
  let C := centralizer (D : Set G)
  obtain ⟨hHC,hgam,⟨S,hS⟩,hcore⟩ :=
    d.single_alternating_nontrivial_centralizer_core hG T hM hTM hu hST hsingle hA hne
  have hLC : L ≤ C := (map_subtype_le _).trans hHC
  have hDi : Di.map d.H.subtype = D :=
    d.single_alternating_centralizer_factor_map hG T hM hTM hu hST hsingle hA
  have hUi : Ui.map d.H.subtype = U :=
    (moduleLayer_map d.H.subtype d.H.subtype_injective d.block).symm
  have hdis : Disjoint U D := by
    rw [←hUi,←hDi]
    exact disjoint_map d.H.subtype_injective
      (d.single_alternating_centralizer_factor hG T hM hTM hu hST hsingle hA).1
  have hAi : IsAlternatingBlock d.block 5 := hA.of_mulEquiv
    (d.block.equivMapOfInjective d.H.subtype d.H.subtype_injective).symm
  have hLcore : L.pCoreIn 2 = U := by
    rw [←map_pCoreIn_of_injective 2 d.block d.H.subtype d.H.subtype_injective]
    change ((pCore 2 d.block).map d.block.subtype).map d.H.subtype = U
    rw [d.single_block_core_intrinsic_source hG T hST hsingle]
    exact hUi
  have hself : Disjoint L (centralizer (L : Set G)) := by
    apply disjoint_def.mpr
    intro x hx hxc
    have hxu : x ∈ U := by
      rw [←hLcore]
      refine ⟨⟨x,hx⟩,?_,rfl⟩
      rw [←hA.2.1.centralizer_blockU]
      intro u hu
      exact Subtype.ext (hxc (u:G) (map_subtype_le _ (mem_map_of_mem L.subtype hu)))
    have hxt : x ∈ (T : Subgroup G) := by
      have hLS : L.pCoreIn 2 ≤ (d.S : Subgroup d.H).map d.H.subtype := by
        rw [←map_pCoreIn_of_injective 2 d.block d.H.subtype d.H.subtype_injective]
        exact map_mono ((pCoreIn_le_of_subnormal 2 (hsingle ▸ d.L0_normal : d.block.Normal).isSubnormal).trans
          (pCore_isPGroup.le_sylow_of_normal d.S))
      exact hST.le (hLS (hLcore ▸ hxu))
    exact disjoint_def.mp hdis hxu ⟨hxt,hxc⟩
  have hcU : Nat.card U = 16 := by
    obtain ⟨_,eU,_⟩ := d.single_alternating_marked_action hsingle hA
    rw [←hUi,card_map_of_injective d.H.subtype_injective,Nat.card_congr eU.toEquiv,
      Nat.card_congr Multiplicative.toAdd,Module.natCard_eq_pow_finrank (K:=ZMod 2),
      BinaryPermutation.finrank_core]
    norm_num
  have h3 : ¬ IsAlternatingBlock d.block 3 := by
    intro ha
    have hc := hAi.module_card_odd (by decide)
    rw [ha.module_card_odd (by decide)] at hc
    norm_num at hc
  let B := L.subgroupOf C
  have hB : B ∈ Chapter1.L C (S : Subgroup C) := by
    apply (Chapter1.mem_L_map_iff C.subtype C.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hLC,hS]
    exact d.ambient_block_mem_L_of_not_three h3
  let : d.block.Normal := hsingle ▸ d.L0_normal
  have hHL : d.H ≤ normalizer (L : Set G) := by
    have hh := d.block.le_normalizer_map d.H.subtype
    rwa [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
  have hSN : (S : Subgroup C) ≤ normalizer (B : Set C) := by
    intro s hs
    apply mem_normalizer_iff.mpr
    intro b
    have hsH : (s:G) ∈ d.H := map_subtype_le _ (hS ▸ mem_map_of_mem C.subtype hs)
    exact mem_normalizer_iff.mp (hHL hsH) (b:G)
  have hC : C ∈ Chapter1.H G :=
    (hgam.elim (fun h=>h.1.1) (fun h=>h.1)).1
  obtain ⟨K,⟨hK,hBK,hKn⟩,_⟩ := Chapter1.Section02.lemma_1_2_4_containment_normality_source
    (Chapter1.Section02.uniqueness_local_quotient_sqtk hG hC) S hB hSN
  let : K.Normal := hKn
  let q := QuotientGroup.mk' (pCore 2 C)
  change C.pCoreIn 2 = D at hcore
  have hDQ : pCore 2 C ≤ center C := by
    intro a ha
    have haD : (a:G) ∈ D := hcore ▸ mem_map_of_mem C.subtype ha
    exact mem_center_iff.mpr fun b => Subtype.ext (b.property _ haD).symm
  have hQC : pCore 2 C ≤ centralizer (K : Set C) := hDQ.trans (center_le_centralizer (K : Set C))
  have hUC : U ≤ C := (map_subtype_le _).trans hLC
  let f : U →* K.map q :=
    { toFun := fun u => ⟨q ⟨u,hUC u.property⟩,mem_map_of_mem q (hBK (show (⟨u,hUC u.property⟩ : C) ∈ L.subgroupOf C from
        (show (u:G) ∈ L from map_subtype_le _ u.property)))⟩
      map_one' := by apply Subtype.ext; exact map_one q
      map_mul' := by
        intro a b
        apply Subtype.ext
        exact map_mul q (⟨a,hUC a.property⟩ : C) (⟨b,hUC b.property⟩ : C) }
  have hfi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro u hu
    have huQ : (⟨(u:G),hUC u.property⟩:C) ∈ pCore 2 C :=
      (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hu)
    have huD : (u:G) ∈ D := hcore ▸ mem_map_of_mem C.subtype huQ
    exact Subtype.ext (disjoint_def.mp hdis u.property huD)
  let : IsElementaryAbelian 2 U := hA.2.1.elementary.map L.subtype
  have hrU : 2 ≤ primeRank 2 U := by
    by_contra hn
    have hr : primeRank 2 U ≤ 1 := by omega
    have hc := (primeRank_le_iff_elementary_card_le U).mp hr ⊤
      (IsElementaryAbelian.of_injective (⊤ : Subgroup U).subtype (⊤ : Subgroup U).subtype_injective)
    rw [card_top,hcU] at hc
    norm_num at hc
  have hquasi : IsQuasisimple K := ChapterA.Section03.NoncentralFitting.quasisimple_of_core_centralizes_and_image_rank
    (Chapter1.Section02.uniqueness_local_quotient_sqtk hG hC) K hK hQC
    (hrU.trans (_root_.primeRank_le_of_injective 2 f hfi))
  exact ⟨S,K,hS,⟨hK.subnormal,hquasi⟩,hKn,hBK,hB,hSN,hself,hcU⟩
end CFSG.Quasithin.Chapter2
