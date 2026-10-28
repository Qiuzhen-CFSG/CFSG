module

public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Quotient
public import Theory.SpecificGroups.PSL3Two.CentralTwoKernel

/-!
# The abelian core of a perfect binary linear-three block

The canonical map L/U(L) → L/O₂(L) has central two-group kernel.
For a perfect L with quotient SL₃(2), this kernel has order at most two.
Since U(L) centralizes O₂(L) in a short group, its cyclic quotient
forces O₂(L) to be abelian. The possible nontrivial central cover is
retained; this does not identify O₂(L) with U(L).

Source: Aschbacher--Smith C.1.7--8 and C.1.13(b), pp.123--125.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC
open Theory.GroupTheory
variable {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]

/-- The literal image of the two-core in L/U(L) has order at most two. -/
theorem linearThree_core_image_card_le_two
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    Nat.card ((pCore 2 L).map (QuotientGroup.mk' (blockU L))) ≤ 2 := by
  let f := e.toMonoidHom.comp (blockCoreProjection (L := L))
  have hk : f.ker = (pCore 2 L).map (QuotientGroup.mk' (blockU L)) := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, blockCoreProjection_ker]
  let : Group.IsPerfect (L ⧸ blockU L) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (blockU L))
  rw [← hk]
  exact BinaryLinearThree.CentralCover.kernel_card_le_two f
    (e.surjective.comp blockCoreProjection_surjective)
    (by rw [hk]; exact blockU_core_image_le_center)
    (by rw [hk]; exact pCore_isPGroup.map _)

/-- The full two-core is abelian, including the possible extra central-cover layer. -/
theorem IsShort.linearThree_core_commutative (h : IsShort L)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    IsMulCommutative (pCore 2 L) := by
  let f := (QuotientGroup.mk' (blockU L)).subgroupMap (pCore 2 L)
  have hc := linearThree_core_image_card_le_two e
  have hp : 0 < Nat.card ((pCore 2 L).map (QuotientGroup.mk' (blockU L))) :=
    Nat.card_pos
  have hd : Nat.card ((pCore 2 L).map (QuotientGroup.mk' (blockU L))) ∣ 2 := by
    have he : Nat.card ((pCore 2 L).map (QuotientGroup.mk' (blockU L))) = 1 ∨
        Nat.card ((pCore 2 L).map (QuotientGroup.mk' (blockU L))) = 2 := by omega
    rcases he with he | he
    · rw [he]; norm_num
    · rw [he]
  let : IsCyclic ((pCore 2 L).map (QuotientGroup.mk' (blockU L))) :=
    isCyclic_of_card_dvd_prime (p := 2) hd
  apply f.isMulCommutative_of_isCyclic_of_ker_le_center
  intro x hx
  have hu : (x : L) ∈ blockU L := (QuotientGroup.eq_one_iff (x : L)).mp
    (congrArg Subtype.val (show f x = 1 from hx))
  apply mem_center_iff.mpr
  intro y
  exact Subtype.ext (h.central hu y y.property)

/-- The central cover bounds the order of the full two-core. -/
theorem linearThree_core_card_le_twice_blockU
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    Nat.card (pCore 2 L) ≤ 2 * Nat.card (blockU L) := by
  let f := (QuotientGroup.mk' (blockU L)).subgroupMap (pCore 2 L)
  have hk : f.ker = (blockU L).subgroupOf (pCore 2 L) := by
    ext x
    change (QuotientGroup.mk' (blockU L)).subgroupMap (pCore 2 L) x = 1 ↔
      (x : L) ∈ blockU L
    rw [←QuotientGroup.eq_one_iff (x : L)]
    exact Subtype.ext_iff
  have hc := card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f
    ((QuotientGroup.mk' (blockU L)).subgroupMap_surjective (pCore 2 L))).toEquiv,
    hk, Nat.card_congr (subgroupOfEquivOfLe (blockU_le_core (L := L))).toEquiv] at hc
  rw [hc]
  exact Nat.mul_le_mul_right _ (linearThree_core_image_card_le_two e)

end CFSG.Quasithin.ChapterC
