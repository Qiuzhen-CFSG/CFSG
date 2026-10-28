module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingThree
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.ElementaryAbelian.Injective

/-!
# A cubic actor on an elementary four-group

If a subgroup of order three normalizes an elementary four-group and its
commutators generate that four-group, their join is the original A₃ block.
The proof computes the order and the two-core, and retains the embedded
four-group as that core. This applies to each lifted cubic axis in the
nondegenerate-plane decomposition of Aschbacher–Smith 13.5.6, printed p.917.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

theorem alternatingThree_of_cubic_product (U P : Subgroup G)
    [IsElementaryAbelian 2 U] (hU : Nat.card U = 4) (hP : Nat.card P = 3)
    (hn : P ≤ normalizer (U : Set G)) (hcomm : ⁅U,P⁆ = U) :
    IsAlternatingBlock (U ⊔ P : Subgroup G) 3 ∧
      (pCore 2 (U ⊔ P : Subgroup G)).map (U ⊔ P).subtype = U := by
  let H := U ⊔ P
  let U' := U.subgroupOf H
  let P' := P.subgroupOf H
  let : U'.Normal := normal_subgroupOf_of_le_normalizer (sup_le U.le_normalizer hn)
  let eU : U' ≃* U := subgroupOfEquivOfLe le_sup_left
  let eP : P' ≃* P := subgroupOfEquivOfLe le_sup_right
  have hU' : Nat.card U' = 4 := (Nat.card_congr eU.toEquiv).trans hU
  have hP' : Nat.card P' = 3 := (Nat.card_congr eP.toEquiv).trans hP
  have hd : Disjoint U P := disjoint_of_coprime_natCard (by rw [hU,hP];decide)
  have hH : Nat.card H = 12 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint U P hn hd,hU,hP]
  have hgen : U' ⊔ P' = ⊤ := by
    rw [← subgroupOf_sup (show U ≤ H from le_sup_left) (show P ≤ H from le_sup_right)]
    exact subgroupOf_self H
  have hc : ⁅U',P'⁆ = U' := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le (show U≤H from le_sup_left),
      map_subgroupOf_eq_of_le (show P≤H from le_sup_right),hcomm]
  have hPR : P' ≤ pResidual 2 H := by
    intro p hp
    apply mem_pResidual_of_orderOf_coprime
    have hd : orderOf p ∣ 3 := by
      have hd := orderOf_dvd_natCard (⟨p,hp⟩ : P')
      simpa only [Subgroup.orderOf_mk,hP'] using hd
    exact (by decide : Nat.Coprime 2 3).of_dvd_right hd
  have hUR : U' ≤ pResidual 2 H := by
    rw [←hc]
    exact (commutator_mono le_top hPR).trans (commutator_le_right _ _)
  have hpH : IsPPerfect 2 H := (pResidual_eq_top_iff 2 H).mp
    (top_unique (hgen ▸ sup_le hUR hPR))
  have hUQ : U' ≤ pCore 2 H := le_sSup ⟨inferInstance,
    (IsElementaryAbelian.isPGroup 2 U).of_equiv eU.symm⟩
  have hQ : Nat.card (pCore 2 H) = 4 := by
    have hlo : 4 ≤ Nat.card (pCore 2 H) := hU' ▸ card_le_of_le hUQ
    have hd : Nat.card (pCore 2 H) ∣ 12 := hH ▸ (pCore 2 H).card_subgroup_dvd_card
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p:=2) (G:=H)).exists_card_eq
    have hcop : Nat.Coprime 3 (Nat.card (pCore 2 H)) := hn ▸
      (by decide : Nat.Coprime 3 2).pow_right n
    have arith (k : ℕ) (hk : 4 ≤ k) (hd : k ∣ 12) (hc : Nat.Coprime 3 k) : k = 4 := by
      have hl := Nat.le_of_dvd (by decide : 0 < 12) hd
      interval_cases k <;> norm_num at *
    exact arith _ hlo hd hcop
  have he : pCore 2 H = U' := (eq_of_le_of_card_ge hUQ (by rw [hU',hQ])).symm
  have hele : IsElementaryAbelian 2 (pCore 2 H) := by
    rw [he]
    exact IsElementaryAbelian.of_injective eU.toMonoidHom eU.injective
  have hquot : Nat.card (H ⧸ pCore 2 H) = 3 := by
    have hh := (pCore 2 H).card_mul_index
    rw [hQ,hH] at hh
    change (pCore 2 H).index = 3
    omega
  refine ⟨RankOne.Solvable.MinimalParabolic.alternatingThree_of_elementary_four_core
    hpH hele hQ hquot, ?_⟩
  rw [he,map_subgroupOf_eq_of_le (show U≤H from le_sup_left)]

end CFSG.Quasithin.ChapterC
