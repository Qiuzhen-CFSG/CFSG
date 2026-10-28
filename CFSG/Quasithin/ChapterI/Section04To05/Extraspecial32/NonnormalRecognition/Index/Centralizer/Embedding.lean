module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Reduction

/-!
# The literal eight-point inclusion in the nine-point model

Extend even permutations of the first eight points by fixing point 8.
The sign formula for extension proves that this is a group embedding, and
small permutation equalities identify the source marks z8 and t8 with z9
and t9. Centralizer extension comparisons use this exact map on K ∩ L.

Source: Aschbacher, “A 2-local characterization of M12”, Proposition 3.3,
printed p.38, with point labels shifted from 1,…,9 to 0,…,8.
-/

@[expose] public section
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index
open Subgroup Equiv Equiv.Perm

/-- The first eight points of the nine-point set, with their original labels. -/
def firstEight : Fin 8 ≃ {x : Fin 9 // x.val < 8} where
  toFun x := ⟨x.castSucc, x.isLt⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The standard inclusion A₈ → A₉ fixing the last point. -/
def eightToNine : Eight →* Nine where
  toFun a := ⟨(a : Perm (Fin 8)).extendDomain firstEight, by
    rw [mem_alternatingGroup, sign_extendDomain]
    exact mem_alternatingGroup.mp a.property⟩
  map_one' := Subtype.ext (extendDomain_one firstEight)
  map_mul' a b := Subtype.ext (extendDomain_mul firstEight a.val b.val).symm

theorem eightToNine_injective : Function.Injective eightToNine := by
  intro a b he
  apply Subtype.ext
  exact extendDomainHom_injective firstEight (congrArg Subtype.val he)

theorem eightToNine_z8 : eightToNine z8 = z9 := by decide
theorem eightToNine_t8 : eightToNine t8 = t9 := by decide

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index
end
