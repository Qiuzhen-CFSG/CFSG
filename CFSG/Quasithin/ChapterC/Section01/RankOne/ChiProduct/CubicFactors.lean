module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.CubicResidual
public import Theory.SpecificGroups.Alternating.FourPairFactors
/-!
# Actual A₃ factors in a cubic residual model

A copy of A₄ is one A₃ block; a copy of A₄ × A₄ has its two literal
commuting coordinate blocks. Transport these groups and their natural
block structures through the specified isomorphism, then through a
subnormal embedding. This retains the original factors, subnormality,
and their exact join, including the empty family for a trivial residual.

Source: the residual restriction in Aschbacher--Smith 15.1.22(*),
printed pp.1098--1099. The intrinsic A₃ structure is transported from
the actual moving block, not supplied by a family label.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct
variable {G : Type*} [Group G] [Finite G]

theorem alternatingThree_factors_of_model
    (ha : IsAlternatingBlock AlternatingFourPair.A 3)
    (hm : Nonempty (G ≃* AlternatingFourPair.A) ∨
      Nonempty (G ≃* AlternatingFourPair.Model)) :
    ∃ F : Set (Subgroup G),
      (∀ B ∈ F, IsBlock B ∧ IsAlternatingBlock B 3) ∧
      F.Pairwise (fun B C => ⁅B,C⁆ = ⊥) ∧ sSup F = ⊤ := by
  classical
  rcases hm with hm | hm
  · obtain ⟨e⟩ := hm
    have hb : IsAlternatingBlock (⊤ : Subgroup G) 3 :=
      Solvable.isAlternatingBlock_of_equiv (e.symm.trans topEquiv.symm) ha
    refine ⟨{⊤},?_,?_,by simp⟩
    · intro B hB
      rw [Set.mem_singleton_iff.mp hB]
      exact ⟨⟨inferInstance,hb.2.1,IsSubnormal.top⟩,hb⟩
    · exact Set.pairwise_singleton _ _
  · obtain ⟨e⟩ := hm
    let U := AlternatingFourPair.axis0.comap e.toMonoidHom
    let W := AlternatingFourPair.axis1.comap e.toMonoidHom
    have hU : U.map e.toMonoidHom = AlternatingFourPair.axis0 :=
      map_comap_eq_self (by rw [MonoidHom.range_eq_top.mpr e.surjective]; exact le_top)
    have hW : W.map e.toMonoidHom = AlternatingFourPair.axis1 :=
      map_comap_eq_self (by rw [MonoidHom.range_eq_top.mpr e.surjective]; exact le_top)
    have hUa : IsAlternatingBlock U 3 :=
      Solvable.isAlternatingBlock_of_equiv
        (((e.subgroupMap U).trans ((MulEquiv.subgroupCongr hU).trans
          AlternatingFourPair.axis0Equiv)).symm) ha
    have hWa : IsAlternatingBlock W 3 :=
      Solvable.isAlternatingBlock_of_equiv
        (((e.subgroupMap W).trans ((MulEquiv.subgroupCongr hW).trans
          AlternatingFourPair.axis1Equiv)).symm) ha
    have hUb : IsBlock U := ⟨inferInstance,hUa.2.1,
      AlternatingFourPair.axis0_normal.isSubnormal.comap e.toMonoidHom⟩
    have hWb : IsBlock W := ⟨inferInstance,hWa.2.1,
      AlternatingFourPair.axis1_normal.isSubnormal.comap e.toMonoidHom⟩
    have hc : ⁅U,W⁆ = ⊥ := by
      apply (map_eq_bot_iff_of_injective _ (f := e.toMonoidHom) e.injective).mp
      rw [map_commutator,hU,hW]
      apply commutator_eq_bot_iff_le_centralizer.mpr
      intro x hx y hy
      apply Prod.ext
      · change y.1 * x.1 = x.1 * y.1
        rw [show y.1 = 1 from hy.1]; simp
      · change y.2 * x.2 = x.2 * y.2
        rw [show x.2 = 1 from hx.2]; simp
    have hg : U ⊔ W = ⊤ := by
      apply map_injective (f := e.toMonoidHom) e.injective
      rw [Subgroup.map_sup,hU,hW,map_top_of_surjective _ e.surjective]
      apply top_unique
      intro x _
      have hx : x = (x.1,1) * (1,x.2) := by ext <;> simp
      rw [hx]
      exact mul_mem_sup (show (x.1,1) ∈ AlternatingFourPair.axis0 from ⟨mem_top _,rfl⟩)
        (show (1,x.2) ∈ AlternatingFourPair.axis1 from ⟨rfl,mem_top _⟩)
    refine ⟨{U,W},?_,?_,?_⟩
    · intro B hB
      rcases Set.mem_insert_iff.mp hB with rfl | hB
      · exact ⟨hUb,hUa⟩
      · exact Set.mem_singleton_iff.mp hB ▸ ⟨hWb,hWa⟩
    · intro B hB C hC hne
      rcases Set.mem_insert_iff.mp hB with rfl | hB <;>
        rcases Set.mem_insert_iff.mp hC with rfl | hC
      · exact (hne rfl).elim
      · rw [Set.mem_singleton_iff.mp hC]; exact hc
      · rw [Set.mem_singleton_iff.mp hB,commutator_comm]; exact hc
      · exact (hne ((Set.mem_singleton_iff.mp hB).trans
          (Set.mem_singleton_iff.mp hC).symm)).elim
    · simpa using hg

/-- Embed the actual commuting family through a subnormal subgroup. -/
theorem alternatingThree_factors_in_subnormal
    (N : Subgroup G) (hn : N.IsSubnormal)
    (ha : IsAlternatingBlock AlternatingFourPair.A 3)
    (hm : N = ⊥ ∨ Nonempty (N ≃* AlternatingFourPair.A) ∨
      Nonempty (N ≃* AlternatingFourPair.Model)) :
    ∃ F : Set (Subgroup G),
      (∀ B ∈ F, IsBlock B ∧ IsAlternatingBlock B 3) ∧
      F.Pairwise (fun B C => ⁅B,C⁆ = ⊥) ∧ sSup F = N := by
  rcases hm with rfl | hm
  · exact ⟨∅, by simp, by simp, by simp⟩
  obtain ⟨F,hb,hc,hg⟩ := alternatingThree_factors_of_model ha hm
  refine ⟨(fun B => B.map N.subtype) '' F,?_,?_,?_⟩
  · rintro B ⟨D,hD,rfl⟩
    have hDa := Solvable.isAlternatingBlock_of_equiv
      (D.equivMapOfInjective N.subtype N.subtype_injective) (hb D hD).2
    exact ⟨⟨inferInstance,hDa.2.1,(hb D hD).1.subnormal.trans' hn⟩,hDa⟩
  · rintro B ⟨D,hD,rfl⟩ C ⟨E,hE,rfl⟩ hne
    rw [←map_commutator,hc hD hE (fun he => hne (congrArg (map N.subtype) he)),Subgroup.map_bot]
  · apply le_antisymm
    · apply sSup_le
      rintro B ⟨D,hD,rfl⟩
      exact map_subtype_le D
    · have he : N = (sSup F).map N.subtype := by
        rw [hg,←MonoidHom.range_eq_map,range_subtype]
      calc
        N = (sSup F).map N.subtype := he
        _ ≤ sSup ((fun B => B.map N.subtype) '' F) := by
          apply map_le_iff_le_comap.mpr
          apply sSup_le
          intro D hD
          apply map_le_iff_le_comap.mp
          exact le_sSup ⟨D,hD,rfl⟩
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct
