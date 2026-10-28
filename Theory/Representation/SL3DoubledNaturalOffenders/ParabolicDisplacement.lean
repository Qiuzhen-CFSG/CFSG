module
public import Theory.Representation.SL3.ParabolicSubgroups
public import Theory.Representation.SL3DoubledNaturalOffenders.Model

/-!
# Line-local displacements on a doubled natural module

For an additive subgroup C of two natural SL₃ copies, suppose C is invariant
under the line local and contains all displacements of one nonidentity
matrix. Intersecting C with each natural copy gives a nonzero invariant
additive subgroup. The natural plane calculation then puts every line-local
displacement in C, without assuming closure under the defining field.

The original application is to Q∩Qᵗ in NonblockMSDoubledCrossing.
Source: Aschbacher--Smith C.4.7 and original 4.3.10, pp.153 and 616--617.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups
namespace Representation.SL3DoubledNaturalOffenders
open Matrix.PSL3.LinearThree
variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

private theorem action_single (g : SL F) (i : Fin 2) (v : Natural F) :
    representation F g (Pi.single i v) = Pi.single i (g.val.mulVec v) := by
  funext j
  by_cases hj : j = i <;> simp [hj,Pi.single_eq_of_ne]

/-- An additive subgroup of two natural copies preserved by the line local
and absorbing all displacements of one nonidentity matrix absorbs every
line-local displacement. No closure under field scalars is assumed. -/
theorem line_displacement_mem_of_nontrivial_actor
    (C : AddSubgroup (Space F))
    (hC : ∀ g ∈ lineLocalSL F, ∀ v ∈ C, representation F g v ∈ C)
    (a : SL F) (ha : a ≠ 1)
    (hmove : ∀ v, representation F a v - v ∈ C)
    (g : SL F) (hg : g ∈ lineLocalSL F) (v : Space F) :
    representation F g v - v ∈ C := by
  classical
  let X (i : Fin 2) : AddSubgroup (Natural F) :=
    C.comap (LinearMap.single (R := F) (φ := fun _ : Fin 2 => Natural F) i).toAddMonoidHom
  have hX (i : Fin 2) : ∀ b ∈ lineLocalSL F, ∀ w ∈ X i, b.val.mulVec w ∈ X i := by
    intro b hb w hw
    change Pi.single i (b.val.mulVec w) ∈ C
    rw [←action_single]
    exact hC b hb _ hw
  have hXne (i : Fin 2) : X i ≠ ⊥ := by
    intro hz
    apply ha
    apply Subtype.ext
    apply Matrix.mulVec_injective
    funext w
    have hc := hmove (Pi.single i w)
    rw [action_single,←Pi.single_sub] at hc
    have hx : a.val.mulVec w - w ∈ X i := hc
    rw [hz,AddSubgroup.mem_bot] at hx
    exact (sub_eq_zero.mp hx).trans (Matrix.one_mulVec w).symm
  have hi (i : Fin 2) : Pi.single i (g.val.mulVec (v i) - v i) ∈ C :=
    SL3ParabolicNatural.line_displacement_mem (X i) (hXne i) (hX i) g hg (v i)
  have he : representation F g v - v =
      Pi.single 0 (g.val.mulVec (v 0) - v 0) + Pi.single 1 (g.val.mulVec (v 1) - v 1) := by
    funext i
    fin_cases i <;> simp
  rw [he]
  exact C.add_mem (hi 0) (hi 1)
end Representation.SL3DoubledNaturalOffenders
