module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingThree
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.Orbits
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.SpecificGroups.Alternating.FourPairCore

/-!
# The normal orbit of an alternating-three block

The original three-rank bound gives at most two χ-blocks. A Sylow orbit
of an A₃ block is therefore either that block or the join of it with a
distinct conjugate. The full guarded C.1.9 theorem gives commutation;
centerlessness makes the intersection trivial. The original orbit is
thus the literal A₄ or A₄ × A₄, and its normality follows from the
proved normalizer-index bound.

Source: Aschbacher--Smith C.1.28 and 15.4.7, pp.133--134,1158.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct
variable {G : Type*} [Group G] [Finite G]
/-- The actual normal Sylow orbit is one A₄ or a direct product of two A₄ groups. -/
theorem cubic_orbit_models
    (hfit : generalizedFitting G = pCore 2 G) (hr : primeRank 3 G ≤ 2)
    (T : Sylow 2 G) (R : Subgroup G) (hb : IsBlock R) (ha : IsAlternatingBlock R 3) :
    let N := conjugateSpanBy R (T : Subgroup G)
    N.Normal ∧ (Nonempty (N ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (N ≃* AlternatingFourPair.Model)) := by
  classical
  let N := conjugateSpanBy R (T : Subgroup G)
  have hchi : IsChiBlockIn R := ⟨hb,Or.inr ⟨3,by decide,ha⟩⟩
  have hn : N.Normal := conjugateSpanBy_sylow_normal R T (normal_or_index_two hfit hr hchi)
  refine ⟨hn,?_⟩
  by_cases he : ∀ t : T, R.map (MulAut.conj (t : G)).toMonoidHom = R
  · have hNR : N = R := by
      apply le_antisymm ?_ (le_conjugateSpanBy R _)
      rw [conjugateSpanBy_eq_iSup_conj]
      exact iSup_le fun t => (he t).le
    exact Or.inl ⟨(MulEquiv.subgroupCongr hNR).trans (Classical.choice ha.equiv_alternatingFour)⟩
  · obtain ⟨t,ht⟩ := not_forall.mp he
    let S := R.map (MulAut.conj (t : G)).toMonoidHom
    have hSR : S ≠ R := ht
    have hSchi := chi_map_equiv (MulAut.conj (t : G)) hchi
    have hSa := Solvable.isAlternatingBlock_of_equiv ((MulAut.conj (t : G)).subgroupMap R) ha
    have hpair : ({R,S} : Set (Subgroup G)) = {K | IsChiBlockIn K} := by
      apply Set.eq_of_subset_of_ncard_le
      · intro K hK
        rcases Set.mem_insert_iff.mp hK with rfl | hK
        · exact hchi
        · have : K = S := Set.mem_singleton_iff.mp hK
          subst K
          exact hSchi
      · rw [Set.ncard_pair hSR.symm]
        exact card_chiBlocks_le_two hfit hr
      · exact Set.toFinite _
    have hNS : N = R ⊔ S := by
      apply le_antisymm
      · rw [show N = conjugateSpanBy R (T : Subgroup G) from rfl,conjugateSpanBy_eq_iSup_conj]
        apply iSup_le
        intro t'
        have hm : R.map (MulAut.conj (t' : G)).toMonoidHom ∈ ({R,S} : Set (Subgroup G)) := by
          rw [hpair]
          exact chi_map_equiv (MulAut.conj (t' : G)) hchi
        rcases Set.mem_insert_iff.mp hm with heq | heq
        · rw [heq]; exact le_sup_left
        · rw [Set.mem_singleton_iff.mp heq]; exact le_sup_right
      · refine sup_le (le_conjugateSpanBy R _) ?_
        rw [show N = conjugateSpanBy R (T : Subgroup G) from rfl,conjugateSpanBy_eq_iSup_conj]
        exact le_iSup (fun t' : T => R.map (MulAut.conj (t' : G)).toMonoidHom) t
    have hc : R ≤ centralizer (S : Set G) := commutator_eq_bot_iff_le_centralizer.mp
      (blocks_commute (blockCommutationHypothesis_of_fitting hfit) hb hSchi.1 hSR.symm)
    have hd : Disjoint R S := by
      apply disjoint_iff_inf_le.mpr
      intro x hx
      have hz : (⟨x,hx.1⟩ : R) ∈ center R := by
        apply mem_center_iff.mpr
        intro y
        exact Subtype.ext ((hc y.property x hx.2).symm)
      rw [ha.center_eq_bot,mem_bot] at hz
      exact mem_bot.mpr (congrArg Subtype.val hz)
    obtain ⟨a,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting R S hd hc
    obtain ⟨aR⟩ := ha.equiv_alternatingFour
    obtain ⟨aS⟩ := hSa.equiv_alternatingFour
    exact Or.inr ⟨((MulEquiv.subgroupCongr hNS).trans a.symm).trans (aR.prodCongr aS)⟩
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct
