module
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.MovingResidualConstructionEndField
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport

/-!
# Applying C.1.10 in a relative overgroup

A marked linear three-block need only be normal in its join with the
acting residual. Transporting the block, its endomorphism field, and
the literal embedded core to this join avoids an ambient normality
assumption. The empty unit-prime set proves centralization from
centralization modulo the core.

Source: Aschbacher–Smith C.1.10, used in 12.4.6, printed p.814.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- C.1.10 transported to ambient subgroups which only normalize the block.
The component need not be normal in the ambient simple group. -/
theorem linearThree_centralizes_of_normalizes_coreQuotient
    (L Y : Subgroup G) (hL : IsLinearTwoBlock L 3)
    (hY : IsPPerfect 2 Y) (hn : Y ≤ normalizer (L : Set G))
    (hc : ⁅Y, L⁆ ≤ (pCore 2 L).map L.subtype) :
    Y ≤ centralizer (L : Set G) := by
  let J := L ⊔ Y
  let A := L.subgroupOf J
  let B := Y.subgroupOf J
  have hLJ : L ≤ J := le_sup_left
  have hYJ : Y ≤ J := le_sup_right
  let e := subgroupOfEquivOfLe hLJ
  let : A.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hn)
  have hA : IsLinearTwoBlock A 3 := ⟨hL.1, hL.2.1.of_mulEquiv e.symm,
    hL.2.2.1.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)),
    hL.2.2.2.of_mulEquiv e.symm⟩
  have hB : IsPPerfect 2 B := hY.of_surjective
    (subgroupOfEquivOfLe hYJ).symm.toMonoidHom (subgroupOfEquivOfLe hYJ).symm.surjective
  have hc' : ⁅B, A⁆ ≤ (pCore 2 A).map A.subtype := by
    apply (map_le_map_iff_of_injective J.subtype_injective).mp
    rw [map_commutator, map_subgroupOf_eq_of_le hYJ, map_subgroupOf_eq_of_le hLJ]
    have he : J.subtype.comp A.subtype = L.subtype.comp e.toMonoidHom := rfl
    rw [map_map, he, ← map_map, pCore_map_iso]
    exact hc
  have hcent := linearThree_centralizes_of_coreQuotient A B hA hB hc'
  have heq := congrArg (map J.subtype) (commutator_eq_bot_iff_le_centralizer.mpr hcent)
  rw [map_commutator, map_subgroupOf_eq_of_le hYJ,
    map_subgroupOf_eq_of_le hLJ, Subgroup.map_bot] at heq
  exact commutator_eq_bot_iff_le_centralizer.mp heq

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
