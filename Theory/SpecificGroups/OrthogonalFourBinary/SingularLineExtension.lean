module

public import Theory.SpecificGroups.OrthogonalFourBinary.TerminalLines.Lines
public import Mathlib.Algebra.Module.ZMod

/-!
# Extending automorphisms of a singular binary line

A totally singular four-subgroup is the graph of an isomorphism between
the two definite planes. An automorphism of that graph acts on the first
plane, and its conjugate through the graph map acts on the second. Every
linear automorphism of a definite binary plane preserves its form, so
this pair is an actual isometry extending the given line automorphism.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the
orthogonal-space description on printed pp.1121–1122 and the full-action
argument in 15.3.66, printed p.1152 (PDF p.1169).
-/

@[expose] public section

open Subgroup Theory.AlgebraicGroup
namespace OrthogonalFourBinary.TerminalLines

/-- Projection onto the first definite plane identifies the graph with that plane. -/
def graphCoordinates (i : LineCode) : Multiplicative Plane ≃* graphLine i where
  toFun x := ⟨Multiplicative.ofAdd (x.toAdd, planePermutation i x.toAdd), rfl⟩
  invFun x := Multiplicative.ofAdd x.val.toAdd.1
  left_inv _ := rfl
  right_inv x := by apply Subtype.ext; exact Prod.ext rfl x.property.symm
  map_mul' x y := by
    apply Subtype.ext
    exact Prod.ext rfl (map_add (planePermutation i) x.toAdd y.toAdd)

private def linearize (a : MulAut (Multiplicative Plane)) : Plane ≃ₗ[F] Plane := by
  let b : Plane ≃+ Plane := {
    toFun x := (a (Multiplicative.ofAdd x)).toAdd
    invFun x := (a.symm (Multiplicative.ofAdd x)).toAdd
    left_inv := a.left_inv
    right_inv := a.right_inv
    map_add' := a.map_mul' }
  exact { b with map_smul' := ZMod.map_smul b }

/-- Extend a graph automorphism by the compatible pair of plane automorphisms. -/
theorem graph_aut_extends (i : LineCode) (f : MulAut (graphLine i)) :
    ∃ g : IsometryGroup, ∀ v : graphLine i, vectorAction g (v : Multiplicative Space) = f v := by
  let c := graphCoordinates i
  let a := linearize (c.trans (f.trans c.symm))
  let b := (planePermutation i).symm.trans (a.trans (planePermutation i))
  let g : IsometryGroup := ⟨a.prodCongr b, by
    apply (mem_quadraticIsometrySubgroup form _).mpr
    intro w
    change planeForm (a w.1) + planeForm (b w.2) = planeForm w.1 + planeForm w.2
    rw [planeForm_preserved, planeForm_preserved]⟩
  refine ⟨g, ?_⟩
  intro v
  have hv : c (Multiplicative.ofAdd v.val.toAdd.1) = v := c.apply_symm_apply v
  have hfirst : a v.val.toAdd.1 = (f v).val.toAdd.1 := by
    change (f (c (Multiplicative.ofAdd v.val.toAdd.1))).val.toAdd.1 = _
    rw [hv]
  apply Prod.ext
  · exact hfirst
  · change planePermutation i (a ((planePermutation i).symm v.val.toAdd.2)) = (f v).val.toAdd.2
    rw [v.property, LinearEquiv.symm_apply_apply, hfirst]
    exact (f v).property.symm

/-- Every automorphism of a totally singular four-subgroup extends to an isometry. -/
theorem singular_line_aut_extends (E : Subgroup (Multiplicative Space))
    (hcard : Nat.card E = 4) (hs : ∀ w ∈ E, form w.toAdd = 0) (f : MulAut E) :
    ∃ g : IsometryGroup, ∀ v : E, vectorAction g (v : Multiplicative Space) = f v := by
  obtain ⟨i,rfl⟩ := singular_four_eq_graph E hcard hs
  exact graph_aut_extends i f

/-- An extension of a line automorphism really stabilizes the line setwise. -/
theorem mem_lineStabilizer_of_extends (E : Subgroup (Multiplicative Space))
    (f : MulAut E) (g : IsometryGroup)
    (hg : ∀ v : E, vectorAction g (v : Multiplicative Space) = f v) :
    g ∈ lineStabilizer E := by
  intro w
  constructor
  · intro hw
    let v := f.symm ⟨vectorAction g w, hw⟩
    have he : vectorAction g (v : Multiplicative Space) = vectorAction g w :=
      (hg v).trans (congrArg Subtype.val (f.apply_symm_apply _))
    exact (vectorAction g).injective he ▸ v.property
  · intro hw
    rw [hg ⟨w, hw⟩]
    exact (f ⟨w, hw⟩).property

end OrthogonalFourBinary.TerminalLines
