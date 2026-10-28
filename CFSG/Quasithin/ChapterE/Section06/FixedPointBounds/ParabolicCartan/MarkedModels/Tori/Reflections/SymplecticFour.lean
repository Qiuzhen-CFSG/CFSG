module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Tori.SymplecticFour
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.FullGroup
/-!
# Reflection in the actual derived symplectic carrier

The symplectic form matrix interchanges the hyperbolic halves and inverts
the specified first-coordinate diagonal torus. For a finite field of
characteristic two with more than two elements, proved perfectness places
this same matrix in Sp₄′. Its lower-left block excludes it from the same
flag Borel restricted to that derived carrier. No full-group substitution
is made in the conclusion.

Source: Aschbacher--Smith E.6.27, printed p.257, with the marked Borel
models from E.2.2. These witnesses feed the same chosen cyclic subgroup
and Hall-subgroup lifting in the original parabolic consumer.
-/
public section
open Matrix Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Tori
variable {F : Type*} [Field F]

private theorem symplecticReflection_intertwine (a : Fˣ) :
    SymplecticGroup.symJ (Fin 2) F * diagonalTorus a 1 =
      diagonalTorus a⁻¹ 1 * SymplecticGroup.symJ (Fin 2) F := by
  apply Subtype.ext
  change J _ _ * diagonal _ = diagonal _ * J _ _
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_diagonal,Matrix.diagonal_mul,Matrix.J,Matrix.fromBlocks]

theorem exists_sp4DerivedTorus_reflection [Finite F] [CharP F 2]
    (hF : 2 < Nat.card F) :
    ∃ w : commutator (Sp F), w ∉ sp4DerivedBorel (F := F) ∧ ∀ a : Fˣ,
      w * (sp4DerivedTorus a : commutator (Sp F)) * w⁻¹ =
        (sp4DerivedTorus a : commutator (Sp F))⁻¹ := by
  let : Group.IsPerfect (Sp F) := perfect_of_card_gt_two hF
  let w : commutator (Sp F) := ⟨SymplecticGroup.symJ (Fin 2) F,by
    rw [Group.IsPerfect.commutator_eq_top]
    trivial⟩
  refine ⟨w,?_,?_⟩
  · intro hw
    have hh : SymplecticGroup.symJ (Fin 2) F ∈ borel := hw
    have he := ((mem_borel_iff _).mp hh).2 0 0
    simp [SymplecticGroup.symJ,Matrix.J,Matrix.fromBlocks] at he
  · intro a
    apply Subtype.ext
    change SymplecticGroup.symJ (Fin 2) F * diagonalTorus a 1 *
      (SymplecticGroup.symJ (Fin 2) F)⁻¹ = (diagonalTorus a 1)⁻¹
    have hi : diagonalTorus a⁻¹ 1 = (diagonalTorus a 1)⁻¹ :=
      congrArg Subtype.val (map_inv (sp4Torus (F := F)) a)
    rw [symplecticReflection_intertwine,mul_inv_cancel_right,hi]
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Tori
