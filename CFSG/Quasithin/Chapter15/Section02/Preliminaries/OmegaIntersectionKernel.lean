module
public import CFSG.Quasithin.Chapter15.Section01.ChosenCoreIntersection
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaStarSetup

/-!
# Faithfulness of the intersection core on the chosen module

The exact core-centralizer identity identifies the kernel of the original
intersection core action. Consequently its image in M/O₂(M) meets the
chosen-module action kernel trivially. This proves the faithfulness used
in 15.2.3 before either the cubic or the order-nine image is selected.

The source core-growth theorem is still required to show that this faithful
image is nontrivial. Source: Aschbacher--Smith 14.1.17 and 15.2.3,
printed pp.980,1104--1105.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

theorem source_chosen_intersection_action_kernel
    (T : Sylow 2 G) {M Mc V : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V) :
    ((M ⊓ Mc).pCoreIn 2).subgroupOf M ⊓ (actionHom M V hV.normalized).ker =
      pCore 2 M := by
  have he := hV.intersection_core_centralizer T hTM hu
  rw [actionHom_ker]
  ext x
  constructor
  · intro hx
    have hm : (x : G) ∈ M.pCoreIn 2 := he.le ⟨hx.1, hx.2⟩
    obtain ⟨q,hq,heq⟩ := hm
    exact (M.subtype_injective heq) ▸ hq
  · intro hx
    have hm := he.ge (mem_map_of_mem M.subtype hx)
    exact ⟨hm.1,hm.2⟩

theorem source_omega_intersection_star_disjoint_kernel
    (T : Sylow 2 G) {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized)) :
    Disjoint ((((M ⊓ Mc).pCoreIn 2).subgroupOf M).map (QuotientGroup.mk' (pCore 2 M)))
      (omegaStarActor hV.normalized ho).ker := by
  apply disjoint_iff.mpr
  apply bot_unique
  rintro x ⟨⟨r,hr,rfl⟩,hx⟩
  apply Subgroup.mem_bot.mpr
  apply (QuotientGroup.eq_one_iff r).mpr
  apply (source_chosen_intersection_action_kernel T hTM hu hV).le
  refine ⟨hr,?_⟩
  have hh : (actionHom M V hV.normalized).rangeRestrict r = 1 := hx
  exact congrArg Subtype.val hh

end CFSG.Quasithin.Chapter15.Section02
