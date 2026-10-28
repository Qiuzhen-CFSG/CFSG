module
public import CFSG.Quasithin.Chapter10.SourceBlockModulePlacement
public import CFSG.Quasithin.Chapter10.SourceA5ZeroCentralizerCore
/-!
# The original full module in the zero-centralizer branch

The original block layer lies in the local module, as does its Sylow
conjugate. When C_Z(L₀)=1, these two layers generate O₂(L₀T), so the
local module equals that core. The core calculation O₂(M)=O₂(L₀T)
then proves M-invariance and hence equality with the full M-orbit module.
In particular the normalizer of the actual local module is M.

These are the module identities used by the subsequent dihedral-factor
argument in 10.2.1. No equality between the two modules is assumed.
Source: Aschbacher–Smith, 10.2.1, printed pp.742–743.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

theorem source_a5_zero_centralizer_module_eq_core
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    D.moduleSubgroup = (localJoin T L).pCoreIn 2 := by
  let H := localJoin T L
  let A := L.subgroupOf H
  let U := D.moduleSubgroup.subgroupOf H
  let : U.Normal := (source_parabolic_module_reduced D).normal
  obtain ⟨t,ht,hne,hb,hab,hpair,hsplit,hE⟩ :=
    source_a5_zero_centralizer_pair_core D e hn hout hz
  have hLH : L ≤ H := (le_componentOrbit L T).trans le_sup_left
  let b : A ≃* L := subgroupOfEquivOfLe hLH
  have he : (blockU L).map L.subtype = ((blockU A).map A.subtype).map H.subtype := by
    rw [←RankOne.Solvable.blockU_map_equiv b,map_map,map_map]
    rfl
  have hAU : (blockU A).map A.subtype ≤ U := by
    apply (map_le_iff_le_comap).mp
    rw [←he]
    exact source_a5_original_block_module_le D e hn hout
  let c := MulAut.conj t
  let B := A.map c.toMonoidHom
  let a : A ≃* B := c.subgroupMap A
  have heB : (blockU B).map B.subtype = ((blockU A).map A.subtype).map c.toMonoidHom := by
    rw [←RankOne.Solvable.blockU_map_equiv a,map_map,map_map]
    rfl
  have hBU : (blockU B).map B.subtype ≤ U := by
    rw [heB]
    exact (map_mono hAU).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp ((show (⊤ : Subgroup H) ≤ normalizer (U : Set H) from
        le_normalizer_of_normal) (mem_top t)))
  apply le_antisymm D.module_le_core
  change (pCore 2 H).map H.subtype ≤ D.moduleSubgroup
  rw [hsplit]
  exact (map_mono (sup_le hAU hBU)).trans_eq (map_subgroupOf_eq_of_le
    (D.module_le_sylow.trans (show (T : Subgroup G) ≤ H from le_sup_right)))

theorem source_a5_zero_centralizer_fullModule_eq
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    D.fullModule = D.moduleSubgroup := by
  have hV : D.moduleSubgroup = D.maximalLocal.pCoreIn 2 :=
    (source_a5_zero_centralizer_module_eq_core D e hn hout hz).trans
      (source_a5_zero_centralizer_core_eq D e hn hout hz).2.symm
  have hMV : D.maximalLocal ≤ normalizer (D.moduleSubgroup : Set G) := by
    rw [hV]
    exact D.maximalLocal.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image D.maximalLocal (pCore 2 D.maximalLocal))
  exact le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hMV)
    (le_componentOrbit D.moduleSubgroup D.maximalLocal)

theorem source_a5_zero_centralizer_module_normalizer
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    normalizer (D.moduleSubgroup : Set G) = D.maximalLocal := by
  rw [←source_a5_zero_centralizer_fullModule_eq D e hn hout hz]
  exact source_fullModule_normalizer D
end CFSG.Quasithin.Chapter10
