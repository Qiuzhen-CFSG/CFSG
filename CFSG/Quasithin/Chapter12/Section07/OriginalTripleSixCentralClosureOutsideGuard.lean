module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureConfiguration
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter3.Section01.StandingGuard
public import Theory.GroupTheory.TwoLocalCoreObstruction

/-!
# The actual outside-local guard from the central-point source

If C_G(z) were contained in N_G(K), the original TI point-normalization
argument would make it normalize U. Since U≤C_G(z), U would lie in its
two-core, contrary to the original failure. The involution z supplies a
nontrivial two-core in its centralizer and hence an actual outside maximal
two-local. This constructs the standing guard used in source3.1.8.

Source: the original12.7.14 central-point branch and12.7.20, pp.843--846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The original central-point failure itself gives an outside maximal
local and an HStar witness; no separate standing-guard assumption is added. -/
theorem original_tripleSix_central_closure_outside_guard
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z:G)} : Set G)).pCoreIn 2) :
    ¬ centralizer ({(z:G)} : Set G) ≤ normalizer (K : Set G) ∧
      Chapter3.HasMaximalOutside T (normalizer (K : Set G)) ∧
      ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (K : Set G)) := by
  let C := centralizer ({(z:G)} : Set G)
  have hUC : U ≤ C := D.le_sylow.trans hzT
  have hCN : ¬ C ≤ normalizer (K : Set G) := by
    intro hh
    have hCU : C ≤ normalizer (U : Set G) := h.source_point_normalizes_chosen_at
      structural D z.property (fun he => hz (Subtype.ext he)) (le_inf hh le_rfl)
    exact hnot (le_pCoreIn_of_normalizes D.elementary.isPGroup hUC hCU)
  let Z := zpowers (z:G)
  have hZU : Z ≤ U := zpowers_le.mpr z.property
  let := D.elementary
  have hzorder : orderOf (z:G)=2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (z:G) z.property) (fun he => hz (Subtype.ext he))
  have hCZ : C ≤ normalizer (Z : Set G) := by
    rw [normalizer_zpowers_eq_centralizer_of_order_two (z:G) hzorder]
  have hZQ : Z ≤ C.pCoreIn 2 := le_pCoreIn_of_normalizes
    (D.elementary.isPGroup.to_le hZU) (hZU.trans hUC) hCZ
  have hcore : pCore 2 C ≠ ⊥ := by
    intro he
    have he' : C.pCoreIn 2=⊥ := by change (pCore 2 C).map C.subtype=⊥; rw [he,Subgroup.map_bot]
    have hz1 : (z:G)=1 := (hZQ.trans_eq he') (mem_zpowers (z:G))
    exact hz (Subtype.ext hz1)
  obtain ⟨N,hN,hCN'⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot C hcore
  have hmax := (h.source_normalizer_maximal_unique_at structural
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G:=X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G:=X))).1
  have hout : Chapter3.HasMaximalOutside T (normalizer (K : Set G)) :=
    Chapter3.hasMaximalOutside_of_two_distinct hmax hN D.sylow_normalizes_component
      (hzT.trans hCN') (fun he => hCN (hCN'.trans_eq he))
  exact ⟨hCN,hout,Chapter3.exists_HStar_of_hasMaximalOutside hout⟩

end CFSG.Quasithin.Chapter12.Section07
