module

public import Theory.Representation.BinaryTensorThree.Group
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Module

/-!
# Tensor-swap calculations for H.1–H.4

The concrete action below is the tensor-product action from subsection H.4.4.
We establish the fixed-space direct sum of H.4.8(5), the dimensions of the
fixed and moved spaces, and the resulting upper bound for the source's
minimum-involution parameter. The other involution classes, the parameter
equalities, the terminal centralizer result H.4.12, and the other module
families of H.1–H.4 remain separate obligations.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.378–385, particularly H.4.8(5) on p.383 and E.3.1 on p.231.
-/

public section

namespace CFSG.Quasithin.ChapterH.Section01To04

open BinaryTensorThree Representation.BinaryOffender

/-- H.4.8(5): the fixed space is the direct sum of the moved space and the
diagonal matrices; the moved and fixed spaces have dimensions three and six. -/
theorem tensor_swap_fixed_decomposition :
    fixedSpace action (Subgroup.zpowers swap) =
      LinearMap.range (flip.toLinearMap - LinearMap.id) ⊔ LinearMap.range diagonal ∧
    Disjoint (LinearMap.range (flip.toLinearMap - LinearMap.id)) (LinearMap.range diagonal) ∧
    Module.finrank (ZMod 2) (LinearMap.range (flip.toLinearMap - LinearMap.id)) = 3 ∧
    Module.finrank (ZMod 2) (fixedSpace action (Subgroup.zpowers swap)) = 6 := by
  refine ⟨?_, ?_, finrank_displacement, finrank_fixedSpace_swap⟩
  · rw [fixedSpace_swap, fixed_decomposition, displacement_range]
  · rw [displacement_range]
    exact displacement_disjoint_diagonal

/-- The swapping involution attains codimension three in the actual tensor group.
The reverse inequality requires the remaining involution classes of H.4.10. -/
theorem tensor_moduleM_le_three : ChapterE.moduleM action ≤ 3 :=
  (ChapterE.moduleM_le_involution action orderOf_swap).trans_eq fixedCodim_swap

end CFSG.Quasithin.ChapterH.Section01To04
