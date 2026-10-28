module

public import Theory.Representation.SpecialLinearNatural
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Faithful natural matrix representations

The natural representation of GL is obtained by identifying an invertible
matrix with its linear automorphism and forgetting invertibility. Both steps
are injective. The analogous faithful special linear representation uses
the existing `specialLinearNatural` action.

These are the faithful degree-three actions used in Aschbacher–Smith,
Lemma A.3.21(c), printed pp. 55–56.
-/

public section

namespace Representation

variable {F : Type*} [CommRing F]

/-- The natural action of invertible matrices on column vectors. -/
@[expose] noncomputable def generalLinearNatural (n : ℕ) :
    Representation F (GL (Fin n) F) (Fin n → F) :=
  (Units.coeHom _).comp Matrix.GeneralLinearGroup.toLin.toMonoidHom

/-- An invertible matrix is determined by its natural action. -/
theorem generalLinearNatural_injective (n : ℕ) :
    Function.Injective (generalLinearNatural (F := F) n) :=
  Units.val_injective.comp Matrix.GeneralLinearGroup.toLin.injective

/-- A determinant-one matrix is determined by its natural action. -/
theorem specialLinearNatural_injective (n : ℕ) :
    Function.Injective (specialLinearNatural (k := F) n) := by
  intro a b h
  apply Matrix.SpecialLinearGroup.toLin'_injective
  exact LinearEquiv.toLinearMap_injective h

end Representation
