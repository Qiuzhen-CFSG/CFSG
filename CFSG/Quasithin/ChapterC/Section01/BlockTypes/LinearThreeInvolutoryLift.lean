module

public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Quotient
public import Theory.SpecificGroups.PSL3Two.InvolutoryLift

/-!
# Involutory lifts in the central quotient of a binary linear-three block

For perfect L with L/O₂(L) ≃ SL₃(2), the canonical map L/U(L) → SL₃(2)
is a perfect central two-cover. An element outside O₂(L) whose square is
in U(L) supplies a noncentral involutory lift. The checked SL₂(7) cover
comparison then makes the kernel trivial, giving O₂(L) = U(L).

This is the central-cover obstruction used to close the fixed-line kernel
calculation in Aschbacher--Smith 12.4.6, p.814; the canonical central quotient
is C.1.8, p.123. The actual source application retains U(L) = V.
-/

public section
open Subgroup

namespace CFSG.Quasithin.ChapterC
variable {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]

/-- A noncore element squaring into U(L) excludes the extra central-cover layer. -/
theorem linearThree_core_eq_blockU_of_square_mem
    (e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (x : K) (hx : x ∉ pCore 2 K) (hs : x ^ 2 ∈ blockU K) :
    pCore 2 K = blockU K := by
  let f := e.toMonoidHom.comp (blockCoreProjection (L := K))
  have hk : f.ker = (pCore 2 K).map (QuotientGroup.mk' (blockU K)) := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, blockCoreProjection_ker]
  let : Group.IsPerfect (K ⧸ blockU K) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (blockU K))
  have hb := BinaryLinearThree.CentralCover.kernel_eq_bot_of_involution f
    (e.surjective.comp blockCoreProjection_surjective)
    (by rw [hk]; exact blockU_core_image_le_center)
    (by rw [hk]; exact pCore_isPGroup.map _)
    (QuotientGroup.mk' (blockU K) x)
    (by rw [← map_pow]; exact (QuotientGroup.eq_one_iff _).mpr hs)
    (by
      intro he
      apply hx
      apply (QuotientGroup.eq_one_iff x).mp
      apply e.injective
      exact he.trans e.map_one.symm)
  apply le_antisymm ?_ blockU_le_core
  intro y hy
  apply (QuotientGroup.eq_one_iff y).mp
  have hm := mem_map_of_mem (QuotientGroup.mk' (blockU K)) hy
  rw [← hk, hb, mem_bot] at hm
  exact hm
end CFSG.Quasithin.ChapterC

