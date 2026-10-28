module
public import CFSG.Quasithin.Chapter10.SourceBlockModulePlacement
public import CFSG.Quasithin.Chapter10.SourceA5OriginalPairedAxes
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.CubicSetup
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ExceptionalRestrictions.Conjugation

/-!
# The original block layer is its moved module

The source block layer lies in the original reduced module. Two-perfection
makes that layer its own commutator with the block, while the ambient
two-core commutator gives the reverse bound. Thus no zero-center assumption
is needed to identify the original layer with its moved module.

Source: Aschbacher–Smith, 10.2.1, printed p.743, using C.1.7 and E.2.3.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem source_a5_original_block_moved
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal) :
    let H := localJoin T L
    let A := L.subgroupOf H
    ⁅D.moduleSubgroup.subgroupOf H,A⁆ = (blockU A).map A.subtype := by
  let H := localJoin T L
  let A := L.subgroupOf H
  let U := D.moduleSubgroup.subgroupOf H
  have hA := (source_a5_original_block_of_baumann_not_controlled D e hn hout).1
  have hLH : L ≤ H := (le_componentOrbit L T).trans le_sup_left
  let b : A ≃* L := subgroupOfEquivOfLe hLH
  have hb : ((blockU A).map A.subtype).map H.subtype = (blockU L).map L.subtype := by
    rw [←RankOne.Solvable.blockU_map_equiv b,map_map,map_map]
    rfl
  have hAU : (blockU A).map A.subtype ≤ U := by
    intro x hx
    exact source_a5_original_block_module_le D e hn hout
      (hb ▸ mem_map_of_mem H.subtype hx)
  apply le_antisymm
  · exact (commutator_mono (source_parabolic_module_reduced D).le_pCore le_rfl).trans_eq
      hA.ambient_core_commutator
  · have he : ⁅(blockU A).map A.subtype,A⁆ = (blockU A).map A.subtype := by
      calc
        ⁅(blockU A).map A.subtype,A⁆ =
            ⁅(blockU A).map A.subtype,(⊤ : Subgroup A).map A.subtype⁆ := by
          congr 1
          exact A.range_subtype.symm.trans (MonoidHom.range_eq_map A.subtype)
        _ = (⁅blockU A,(⊤ : Subgroup A)⁆).map A.subtype := (map_commutator _ _ _).symm
        _ = (blockU A).map A.subtype :=
          congrArg (map A.subtype) (ExceptionalRestrictions.short_commutator hA.short)
    exact he ▸ commutator_mono hAU le_rfl

end CFSG.Quasithin.Chapter10
