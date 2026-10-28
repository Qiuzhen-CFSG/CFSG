module

public import Theory.GroupTheory.NoncentralChiefRefinement.BinarySections
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Mathlib.Order.Atoms.Finite

/-!
# A chief factor moved by a normal two-perfect subgroup

Let Q be a normal two-group and K a normal two-perfect subgroup. If K
moves Q modulo a normal layer Z, choose a maximal proper normal subgroup
of [Q,K]Z containing Z. Coprime commutator idempotence ensures that K
moves the resulting chief interval. Both endpoints stay in the original
acting group; no module or faithfulness witness is assumed.

This is the normal-subgroup version of the construction in `MovedChief`,
used on the point residual in Aschbacher–Smith 14.7.20(2), printed p.1049.
-/

public section
open Subgroup
namespace NoncentralChiefRefinement
variable {G : Type*} [Group G] [Finite G]

/-- Nontrivial movement by a normal two-perfect subgroup occurs on an
actual chief interval in the specified two-group section. -/
theorem exists_moved_chief_of_normal_twoPerfect
    (Z Q K : NormalNode G) (hZQ : Z ≤ Q) (hQ : IsPGroup 2 Q.val)
    (hK : IsPPerfect 2 K.val) (hn : ¬ ⁅Q.val,K.val⁆ ≤ Z.val) :
    ∃ B U : NormalNode G, Z ≤ B ∧ B ⋖ U ∧ U ≤ Q ∧
      ¬ ⁅U.val,K.val⁆ ≤ B.val := by
  let C : NormalNode G := ⟨⁅Q.val,K.val⁆, inferInstanceAs (⁅Q.val,K.val⁆).Normal⟩
  have hCQ : C ≤ Q := commutator_le_left _ _
  let U : NormalNode G := C ⊔ Z
  have hZU : Z < U := lt_of_le_of_ne le_sup_right (by
    intro he
    exact hn ((show C ≤ U from le_sup_left).trans he.ge))
  obtain ⟨B,hZB,hmax⟩ := Finite.exists_le_maximal
    (p := fun B : NormalNode G => B < U) (a := Z) hZU
  have hBU : B ⋖ U := ⟨hmax.prop, by
    intro W hBW hWU
    exact (not_le_of_gt hBW) (hmax.2 hWU hBW.le)⟩
  have hid : ⁅C.val,K.val⁆ = C.val :=
    commutator_isPPerfect_idempotent K.val Q.val hK hQ le_normalizer_of_normal
  refine ⟨B,U,hZB,hBU,sup_le hCQ hZQ,?_⟩
  intro hc
  have hCB : C ≤ B := by
    change C.val ≤ B.val
    rw [←hid]
    exact (commutator_mono (show C.val ≤ U.val from le_sup_left) le_rfl).trans hc
  exact hmax.prop.not_ge (sup_le hCB hZB)

end NoncentralChiefRefinement
