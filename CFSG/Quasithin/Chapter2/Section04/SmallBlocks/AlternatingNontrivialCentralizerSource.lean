module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingGeneratedCoreSource
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.ModuleLift
public import Theory.GroupTheory.GeneralizedFitting.ResidualOvergroups
public import Theory.GroupTheory.PCoreRestriction
/-!
# The core of the actual single-A5 block centralizer

For D=C_T(L) nontrivial, the original largest-base argument keeps S Sylow
in C_G(D). The generated orthogonal local group supplies a residual inside
C_G(D); its subnormal overgroup shows the module cannot enter O2(C_G(D)).
The short-module dichotomy then forces that core to centralize L, so it
is exactly D. This supplies the original core premise for selecting the
ordinary containing component in the single-A5 exclusion.

Source: Aschbacher–Smith 2.4.29, printed p.545, the D nontrivial paragraph.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource ChapterC.Section05.BlockAnalysis
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_nontrivial_centralizer_core
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hne : (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G) ≠ ⊥) :
    let D := (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G)
    let C := centralizer (D : Set G)
    d.H ≤ C ∧ C ∈ gammaZero (Chapter1.He G) M ∧
      (∃ R : Sylow 2 C, (R : Subgroup C).map C.subtype =
        (d.S : Subgroup d.H).map d.H.subtype) ∧ C.pCoreIn 2 = D := by
  let L := d.block.map d.H.subtype
  let R := (d.S : Subgroup d.H).map d.H.subtype
  let U := sourceModule L
  let D := (T : Subgroup G) ⊓ centralizer (L : Set G)
  let C := centralizer (D : Set G)
  let B := M ⊓ L
  let K := (pResidual 2 B).map B.subtype
  let P := K.pCoreIn 2
  let E := P ⊔ D
  let F := K ⊔ (T : Subgroup G)
  have hDR : D ≤ R := by
    rw [show D = R ⊓ centralizer (L : Set G) from
      d.single_block_sylow_centralizer T hST.le hsingle]
    exact inf_le_left
  have hDH : D ≤ d.H := hDR.trans (map_subtype_le _)
  have hHC : d.H ≤ C := le_centralizer_iff.mp
    (d.single_alternating_centralizer_source hG T hM hTM hu hST hsingle hA).1
  have hDcore : D ≤ C.pCoreIn 2 := le_pCoreIn_of_normalizes
    (T.isPGroup'.to_le inf_le_left) (hDH.trans hHC) (Subgroup.centralizer_le_normalizer _)
  have hC : C ∈ Chapter1.H G := fun hc => hne (bot_unique (hc ▸ hDcore))
  obtain ⟨hgam,⟨S,hS⟩,_⟩ := lemma_2_3_7_2 d.mem_gammaEvenZero.1 d.full_pair d.S le_rfl ⟨hC,hHC⟩
  have hQC : C.pCoreIn 2 ≤ R := by
    have hh := pCoreIn_le_sylow C S
    rwa [hS] at hh
  have hQH : C.pCoreIn 2 ≤ d.H := hQC.trans (map_subtype_le _)
  have hUR : U ≤ R := by
    have hUb : (blockU d.block).map d.block.subtype ≤ pCore 2 d.H :=
      (map_mono (blockU_le_core (L:=d.block))).trans (pCoreIn_le_of_subnormal 2
        ((hsingle ▸ d.L0_normal : d.block.Normal).isSubnormal))
    rw [show U=((blockU d.block).map d.block.subtype).map d.H.subtype from
      moduleLayer_map d.H.subtype d.H.subtype_injective d.block]
    exact map_mono (hUb.trans (pCore_isPGroup.le_sylow_of_normal d.S))
  have hUF : U ≤ F := hUR.trans (hST.le.trans le_sup_right)
  have hUC : U ≤ C := hUR.trans ((map_subtype_le _).trans hHC)
  have hnot : ¬ U ≤ C.pCoreIn 2 := by
    intro hUQ
    let J := F ⊓ C
    have hJF : J ≤ F := inf_le_left
    have hJC : J ≤ C := inf_le_right
    have hDJ : D ≤ centralizer (E : Set G) := by
      apply le_centralizer_iff.mpr
      exact sup_le
        (le_centralizer_iff.mp (inf_le_right.trans (centralizer_le
          ((pCoreIn_le 2 K).trans ((map_subtype_le _).trans inf_le_right)))))
        (le_centralizer_iff.mp (hDH.trans hHC))
    have hDcenter : D ≤ (center E).map E.subtype := by
      intro z hz
      refine ⟨⟨z,mem_sup_right hz⟩,mem_center_iff.mpr ?_,rfl⟩
      intro x
      exact Subtype.ext (hDJ hz x x.property)
    have hres : (pResidual 2 F).map F.subtype ≤ C :=
      (d.single_alternating_generated_setup hG T hM hTM hu hST hsingle hA).2.2.trans
        (centralizer_le hDcenter)
    have hsub : (J.subgroupOf F).IsSubnormal :=
      residual_overgroup_subnormal _ (fun x hx =>
        ⟨x.property,hres (mem_map_of_mem F.subtype hx)⟩)
    have hUcoreJ : U ≤ J.pCoreIn 2 :=
      (le_inf (le_inf hUF hUC) hUQ).trans (inf_pCoreIn_le_of_le 2 hJC)
    have hUcoreF : U ≤ F.pCoreIn 2 := hUcoreJ.trans
      (pCoreAmbient_mono_of_isSubnormalIn J F 2 hJF hsub)
    rw [(d.single_alternating_generated_core hG T hM hTM hu hST hsingle hA).1] at hUcoreF
    have hi := (d.single_alternating_core_relative_indices hG T hM hTM hu hST hsingle hA).1
    have hj : E.relIndex U = 1 := relIndex_eq_one.mpr hUcoreF
    change E.relIndex U = 2 at hi
    omega
  let Q := (C.pCoreIn 2).subgroupOf d.H
  let : Q.Normal := (normal_subgroupOf_iff_le_normalizer hQH).mpr
    (hHC.trans (le_normalizer_twoCore C))
  have hQp : IsPGroup 2 Q := (isPGroup_pCoreIn 2 C).comap_subtype
  have hQcore : Q ≤ pCore 2 d.H := le_sSup ⟨inferInstance,hQp⟩
  let : d.block.Normal := hsingle ▸ d.L0_normal
  have hcomm : ⁅Q,d.block⁆ ≤ (blockU d.block).map d.block.subtype := by
    intro a ha
    have hb : a ∈ d.block := commutator_le_right Q d.block ha
    have hc : a ∈ pCore 2 d.H := hQcore (commutator_le_left Q d.block ha)
    refine ⟨⟨a,hb⟩,?_,rfl⟩
    rw [←d.single_block_core_intrinsic_source hG T hST hsingle,
      ←(inferInstance : d.block.Normal).isSubnormal.pCore_subgroupOf 2]
    exact hc
  have hAi : IsAlternatingBlock d.block 5 := hA.of_mulEquiv
    (d.block.equivMapOfInjective d.H.subtype d.H.subtype_injective).symm
  have hcent : d.block ≤ centralizer (Q : Set d.H) := by
    rcases RankOne.ChiProduct.normal_two_layer_short_dichotomy d.block Q hAi.2.1 hQp hcomm with h | h
    · apply False.elim
      apply hnot
      have hm := map_mono (f:=d.H.subtype) h
      rw [map_subgroupOf_eq_of_le hQH] at hm
      change (moduleLayer d.block).map d.H.subtype ≤ C.pCoreIn 2 at hm
      rw [←moduleLayer_map d.H.subtype d.H.subtype_injective d.block] at hm
      exact hm
    · exact h
  have hQcent : C.pCoreIn 2 ≤ centralizer (L : Set G) := by
    have hm := (map_mono (f:=d.H.subtype) (le_centralizer_iff.mp hcent)).trans
      (map_centralizer_le_centralizer_image (d.block : Set d.H) d.H.subtype)
    rwa [map_subgroupOf_eq_of_le hQH] at hm
  exact ⟨hHC,hgam,⟨S,hS⟩,le_antisymm (le_inf (hQC.trans hST.le) hQcent) hDcore⟩
end CFSG.Quasithin.Chapter2
