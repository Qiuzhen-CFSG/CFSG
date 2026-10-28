module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingCentralizerSource
/-!
# The marked odd involution in the original alternating-five source

A moved maximum elementary subgroup has a transposition in its image on
five letters. Lifting that transposition inside the elementary subgroup
gives an actual involution for the same previously chosen quotient map.
This mark rules out central sign twists when splitting the whole group.

Source: Aschbacher–Smith C.5.4(3), used in 2.4.29, printed pp.155,545.
-/
public section
open Subgroup Stellmacher BinaryPermutation
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource ChapterC.Section05.BlockAnalysis
open ChapterC.Section05.BlockAnalysis.AlternatingSetup ChapterB.Offenders
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_odd_involution
    (d : MinimalBlockSetup M) (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (q : d.H →* Equiv.Perm (Fin 5))
    (e : (blockU d.block).map d.block.subtype ≃* Multiplicative (core (Fin 5)))
    (hker : q.ker = pCore 2 d.H)
    (hC : q.ker = centralizer ((blockU d.block).map d.block.subtype : Set d.H))
    (he : ∀ (s : d.H) (u : (blockU d.block).map d.block.subtype),
      (e.symm (Multiplicative.ofAdd
        (coreRepresentation (Fin 5) (q s) (e u).toAdd)) : d.H) = s * (u : d.H) * s⁻¹) :
    ∃ t : d.H, t ∈ (d.S : Subgroup d.H) ∧ orderOf t = 2 ∧ (q t).IsSwap := by
  let U := (blockU d.block).map d.block.subtype
  let J := elementaryAbelianMaxJ (d.S : Subgroup d.H)
  let : d.block.Normal := hsingle ▸ d.L0_normal
  let : U.Normal := inferInstanceAs (((blockU d.block).map d.block.subtype).Normal)
  have hAi : IsAlternatingBlock d.block 5 := hA.of_mulEquiv
    (d.block.equivMapOfInjective d.H.subtype d.H.subtype_injective).symm
  let : IsElementaryAbelian 2 U := by
    let := hAi.2.1.elementary
    exact IsElementaryAbelian.map d.block.subtype
  have hU : U.map d.H.subtype = sourceModule (d.block.map d.H.subtype) :=
    (moduleLayer_map d.H.subtype d.H.subtype_injective d.block).symm
  have hUS : U ≤ d.S := (le_centralizer U).trans
    ((hC.symm.trans hker).le.trans (pCore_isPGroup.le_sylow_of_normal d.S))
  have hJ : ¬ J ≤ centralizer (U : Set d.H) := by
    intro hh
    have hm := map_mono (f := d.H.subtype) hh
    rw [←elementaryAbelianMaxJ_map_injective d.H.subtype d.H.subtype_injective] at hm
    exact thompson_moves_of_commutator (d.block.map d.H.subtype) _ hA.2.1 d.moved
      (hm.trans (by rw [←hU]; exact map_centralizer_le_centralizer_image _ _))
  have hex : ∃ A ∈ elementaryAbelianMaxSubgroups (d.S : Subgroup d.H), A.map q ≠ ⊥ := by
    by_contra! hall
    apply hJ
    rw [←hC]
    exact sSup_le fun A hA => (Subgroup.map_eq_bot_iff A).mp (hall A hA)
  obtain ⟨A,hmax,hne⟩ := hex
  obtain ⟨m,hm,_,a,ha⟩ := max_image_caseA U q hC e he d.S A hUS hmax hne
  let t := (MulAut.conj a) (pairSwap 5 0)
  have ht : t.IsSwap :=
    ⟨a 0,a 1,a.injective.ne (by decide),Equiv.symm_trans_swap_trans (0 : Fin 5) 1 a⟩
  have htA : t ∈ A.map q := by
    rw [ha]
    exact mem_map_of_mem _ (pairSwap_mem 0 hm)
  obtain ⟨b,hb,hbt⟩ := htA
  let : IsElementaryAbelian 2 A := hmax.2.1
  refine ⟨b,hmax.1 hb,orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian b hb) ?_,?_⟩
  · intro h
    have hh : t=1 := hbt.symm.trans (h ▸ q.map_one)
    have ho := ht.orderOf
    rw [hh,orderOf_one] at ho
    omega
  · rwa [hbt]
end CFSG.Quasithin.Chapter2
