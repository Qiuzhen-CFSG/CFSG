module
public import Theory.Representation.SL5ExteriorSquare.MarkedRecognition
public import Mathlib.RepresentationTheory.Character

/-!
# Non-self-duality of the binary exterior-square representation

A determinant-one matrix and its inverse have distinct traces on the exterior
square of the natural five-space. Self-duality would equate those traces. The
completed degree-ten recognition transports this obstruction to every
irreducible binary SL₅(2) representation of that degree.

This supplies the binary linear row in Aschbacher--Smith G.11.7.
-/

set_option maxRecDepth 4096

open scoped MatrixGroups
open Representation
public section
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

private def separator : Group := ⟨!![0,0,0,0,1;
  1,0,0,0,0; 0,1,0,0,1; 0,0,1,0,0; 0,0,0,1,0],by decide⟩
private def separatorInv : Group := ⟨!![0,1,0,0,0;
  1,0,1,0,0; 0,0,0,1,0; 0,0,0,0,1; 1,0,0,0,0],by decide⟩

private theorem separator_inv : separator⁻¹ = separatorInv := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  decide

private theorem character_square (g : Group) :
    (exteriorAction 2).character g = Matrix.trace (actionMatrix g) := by
  have he : coordinates.conj (exteriorAction 2 g) = (actionMatrix g).toLin' := by
    apply LinearMap.ext
    intro w
    change coordinates (exteriorAction 2 g (coordinates.symm w)) = (actionMatrix g).mulVec w
    rw [coordinates_action,coordinates.apply_symm_apply]
  calc
    (exteriorAction 2).character g =
        LinearMap.trace (ZMod 2) _ (coordinates.conj (exteriorAction 2 g)) :=
      (LinearMap.trace_conj' _ _).symm
    _ = Matrix.trace (actionMatrix g) := by rw [he,Matrix.trace_toLin'_eq]

private theorem separator_character : (exteriorAction 2).character separator = 0 := by
  rw [character_square]
  decide

private theorem separator_inv_character : (exteriorAction 2).character separator⁻¹ = 1 := by
  rw [separator_inv,character_square]
  decide

/-- The actual exterior square has unequal traces on an element and its inverse. -/
theorem not_selfDual_of_square_coordinates
    {D V : Type*} [_root_.Group D] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (e : D ≃* Group)
    (c : V ≃ₗ[ZMod 2] ExteriorModule 2)
    (hc : ∀ g v, c (ρ g v) = exteriorAction 2 (e g) (c v))
    (hs : Nonempty (ρ.Equiv ρ.dual)) : False := by
  have hchar (g : D) : ρ.character g = (exteriorAction 2).character (e g) := by
    have he : c.conj (ρ g) = exteriorAction 2 (e g) := by
      apply LinearMap.ext
      intro w
      change c (ρ g (c.symm w)) = exteriorAction 2 (e g) w
      rw [hc,c.apply_symm_apply]
    exact (LinearMap.trace_conj' (ρ g) c).symm.trans (congrArg _ he)
  have hh := congrFun (Representation.char_iso hs.some) (e.symm separator)
  rw [Representation.char_dual,hchar,hchar,map_inv,e.apply_symm_apply,
    separator_character,separator_inv_character] at hh
  exact zero_ne_one hh

/-- Every ten-dimensional irreducible binary SL₅(2) module is non-self-dual. -/
theorem not_selfDual_of_finrank_ten
    {D V : Type*} [_root_.Group D] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) [IsIrreducible ρ]
    (e : D ≃* Group) (hd : Module.finrank (ZMod 2) V = 10)
    (hs : Nonempty (ρ.Equiv ρ.dual)) : False := by
  obtain ⟨actor,c,_,hc⟩ := square_coordinates_of_finrank_ten ρ e hd
  exact not_selfDual_of_square_coordinates ρ actor c hc hs
end Representation.SL5ExteriorSquare
