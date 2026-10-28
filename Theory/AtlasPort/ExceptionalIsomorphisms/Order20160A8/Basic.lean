module

/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Released under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.Forms
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.ClassicalPointGroups
public import Mathlib.Tactic
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
Adapted from `Atlas/LinearGroups/Orthogonal/{Basic,IsometryTransport}.lean`.
Conjugation by an isometry identifies the actual full quadratic isometry groups.
The split form and isometry subgroup are reused from CFSG.
-/

@[expose] public noncomputable section
namespace Atlas.Order20160A8
open ClassicalOrthogonal Theory.AlgebraicGroup

abbrev isometrySubgroup {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (Q : QuadraticForm F V) := quadraticIsometrySubgroup Q

abbrev O_DPlus (n : ℕ) (F : Type) [Field F] := ↥(isometrySubgroup (F := F) (formD n F))

variable {F V W : Type} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

def isometryCarrierEquiv (Q : QuadraticForm F V) :
    isometrySubgroup Q ≃ Q.IsometryEquiv Q where
  toFun g := { g.val with map_app' := (mem_quadraticIsometrySubgroup Q g.val).mp g.prop }
  invFun g := ⟨g.toLinearEquiv, (mem_quadraticIsometrySubgroup Q _).mpr g.map_app⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance finite_orthogonal_d (n : ℕ) [Finite F] : Finite (O_DPlus n F) :=
  Finite.of_injective (fun g : O_DPlus n F => (g.val : VectorD n F → VectorD n F))
    (fun _ _ h => Subtype.ext (LinearEquiv.ext (congrFun h)))

variable {Q : QuadraticForm F V} {R : QuadraticForm F W}

/-- Conjugation transports the full isometry group, preserving its multiplication. -/
def isometryGroupTransport (g : Q.IsometryEquiv R) : isometrySubgroup Q ≃* isometrySubgroup R where
  toFun k := (isometryCarrierEquiv R).symm
    ((g.symm.trans (isometryCarrierEquiv Q k)).trans g)
  invFun k := (isometryCarrierEquiv Q).symm
    ((g.trans (isometryCarrierEquiv R k)).trans g.symm)
  left_inv k := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change g.symm (g (k.val (g.symm (g x)))) = k.val x
    rw [g.symm_apply_apply, g.symm_apply_apply]
  right_inv k := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change g (g.symm (k.val (g (g.symm x)))) = k.val x
    rw [g.apply_symm_apply, g.apply_symm_apply]
  map_mul' k l := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change g (k.val (l.val (g.symm x))) = g (k.val (g.symm (g (l.val (g.symm x)))))
    rw [g.symm_apply_apply]

end Atlas.Order20160A8
