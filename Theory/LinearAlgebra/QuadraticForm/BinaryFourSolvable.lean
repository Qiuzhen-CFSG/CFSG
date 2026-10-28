module
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus
public import Theory.LinearAlgebra.QuadraticForm.IsometryGroup.Transport
public import Theory.SpecificGroups.OrthogonalFourBinary.PlusTypeCoordinates
public import Theory.GroupTheory.SolvableResidual
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Solvable

/-!
# Solvable residual of a binary plus four-space

A totally singular plane gives a literal isometry with the standard plus
form. Transport to its S3 wreath C2 model proves solvability: the base is
S3 times S3 and the quotient is C2. Consequently the embedded solvable
residual of the original full isometry group is trivial. This uses the
solvable residual, not the two-residual used in some orthogonal conventions.

The actual exchanged-constituent consumer excludes this row by its nontrivial
component action. Source: Aschbacher--Smith G.10.15, p.363, and the orthogonal
alternative of G.12.1, p.370.
-/

public section
open Subgroup Module
namespace QuadraticForm.BinaryFour

private def modelIsometry :
    OrthogonalFourBinary.form.IsometryEquiv BinaryFourPlus.q where
  toLinearEquiv := (LinearEquiv.finTwoArrow (ZMod 2) (ZMod 2)).symm.prodCongr
    (LinearEquiv.finTwoArrow (ZMod 2) (ZMod 2)).symm
  map_app' := by decide +kernel

private theorem wreath_solvable : Group.IsSolvable BinaryFourPlus.Wreath := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) :=
    Group.isSolvable_of_comm (by decide)
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    apply Group.isSolvable_of_ker_le_range
      (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [range_subtype, ← alternatingGroup_eq_sign_ker]
  let p : BinaryFourPlus.Wreath →* BinaryFourPlus.C2 := RegularWreathProduct.rightHom
  let t : BinaryFourPlus.C2 := Multiplicative.ofAdd 1
  have hcases : ∀ i : BinaryFourPlus.C2, i = 1 ∨ i = t := by decide
  let f : p.ker →* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) := {
    toFun w := (w.val.left 1,w.val.left t)
    map_one' := rfl
    map_mul' := by
      intro a b
      have ha : a.val.right = 1 := a.property
      simp [RegularWreathProduct.mul_left,ha] }
  have hfi : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply RegularWreathProduct.ext
    · funext i
      rcases hcases i with rfl | rfl
      · exact congrArg Prod.fst hab
      · exact congrArg Prod.snd hab
    · exact (show a.val.right=1 from a.property).trans
        (show b.val.right=1 from b.property).symm
  let : Group.IsSolvable p.ker := Group.isSolvable_of_isSolvable_injective hfi
  exact Group.isSolvable_of_ker_le_range p.ker.subtype p (by rw [range_subtype])

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The full isometry group of a binary plus four-space is solvable. -/
theorem isometryGroup_solvable_of_singular_plane
    (q : QuadraticForm (ZMod 2) V) (hnd : q.polarBilin.Nondegenerate)
    (hd : finrank (ZMod 2) V = 4) (U : Submodule (ZMod 2) V)
    (hU : finrank (ZMod 2) U = 2) (hs : ∀ u ∈ U, q u = 0) :
    Group.IsSolvable q.isometrySubgroup := by
  obtain ⟨e⟩ := OrthogonalFourBinary.nonempty_isometryEquiv_of_totallySingular
    q hnd hd U hU hs
  let j := ((e.trans modelIsometry).isometrySubgroupCongr).trans
    BinaryFourPlus.isometryEquivWreath
  let : Group.IsSolvable BinaryFourPlus.Wreath := wreath_solvable
  exact Group.isSolvable_of_isSolvable_injective (f := j.toMonoidHom) j.injective

/-- Its literal embedded solvable residual is trivial. This differs from
its generally nontrivial two-residual. -/
theorem residual_eq_bot_of_singular_plane
    (q : QuadraticForm (ZMod 2) V) (hnd : q.polarBilin.Nondegenerate)
    (hd : finrank (ZMod 2) V = 4) (U : Submodule (ZMod 2) V)
    (hU : finrank (ZMod 2) U = 2) (hs : ∀ u ∈ U, q u = 0) :
    (solvableResidual q.isometrySubgroup).map q.isometrySubgroup.subtype = ⊥ := by
  let : Group.IsSolvable q.isometrySubgroup :=
    isometryGroup_solvable_of_singular_plane q hnd hd U hU hs
  rw [solvableResidual_eq_bot, Subgroup.map_bot]

end QuadraticForm.BinaryFour
