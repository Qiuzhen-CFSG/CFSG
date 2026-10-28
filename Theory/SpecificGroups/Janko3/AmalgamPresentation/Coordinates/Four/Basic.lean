module
public import Theory.Representation.CentralCubicNaturalFour
public import Theory.SpecificGroups.GL2.FourCentralProduct
import Mathlib.Tactic.FinCases

/-!
# Literal four-field affine coordinates for the second local pair

The saved GAP coordinates use the right affine action on row vectors. The
ATLAS model uses the inverse permutation convention. Consequently these
column-action elements are the inverses of those saved affine transformations.
The two translations and two invertible matrices are given literally over
the existing computable field of four elements. Discovery data are retained
in `Scratch/J3ModelCoordinates/canonical4-coordinates.json`; their correctness
as a marking is established in subsequent modules, not assumed here.
-/

@[expose] public noncomputable section
namespace Sporadic.Janko3.AmalgamPresentation.FourCoordinates
open Representation.SL2FourNatural hiding Plane
open Representation.CentralCubicNaturalFour
open Matrix

abbrev Affine := Plane ⋊[naturalAction] LinearGroup

/-- The first inverse-of-GAP linear coordinate, with a literal inverse matrix. -/
def firstMatrix : LinearGroup where
  val := !![⟨0,1⟩,0;⟨1,1⟩,1]
  inv := !![⟨1,1⟩,0;⟨0,1⟩,1]
  val_inv := by decide +kernel
  inv_val := by decide +kernel

/-- The second inverse-of-GAP linear coordinate. -/
def secondMatrix : LinearGroup where
  val := !![⟨0,1⟩,⟨0,1⟩;0,⟨1,1⟩]
  inv := !![⟨1,1⟩,⟨0,1⟩;0,⟨0,1⟩]
  val_inv := by decide +kernel
  inv_val := by decide +kernel

def first : Affine := ⟨Multiplicative.ofAdd ![⟨0,1⟩,0],firstMatrix⟩
def second : Affine := ⟨Multiplicative.ofAdd ![⟨1,1⟩,⟨0,1⟩],secondMatrix⟩

theorem affine_card : Nat.card Affine = 2880 := by
  rw [SemidirectProduct.card, Matrix.card_GL_field, card_field]
  have hv : Nat.card Plane = 16 :=
    (Nat.card_congr (Multiplicative.toAdd : Plane ≃ V)).trans
      (Nat.card_eq_fintype_card.trans card_vector)
  rw [hv]
  decide

end Sporadic.Janko3.AmalgamPresentation.FourCoordinates
