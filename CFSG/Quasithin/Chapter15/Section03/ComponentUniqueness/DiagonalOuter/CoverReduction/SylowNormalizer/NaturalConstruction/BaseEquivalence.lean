module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.SylowNormalizer.NaturalConstruction.ModelContracts
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# The plane-preserving base as a symmetric square

Restriction to the two coordinates identifies the kernel of the wreath
permutation with two copies of SL₂(2). The proved projective-line action
identifies each copy with S₃. This equivalence uses the literal matrix base
and does not assert anything about an ambient local subgroup.

Source: the S₃ × S₃ action calculation in Aschbacher--Smith, proof of
15.3.38, printed p.1136.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.SylowNormalizer.NaturalConstruction

/-- Coordinate evaluation followed by the three-point projective actions. -/
noncomputable def planeBaseEquiv :
    planeBase ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) := by
  let e : OrthogonalPlaneActor ≃* Equiv.Perm (Fin 3) :=
    Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three
  let q : planeBase ≃* (OrthogonalPlaneIndex → OrthogonalPlaneActor) :=
    { toFun := fun x => x.val.left
      invFun := fun f => ⟨⟨f, 1⟩, rfl⟩
      left_inv := fun x => by
        apply Subtype.ext
        apply RegularWreathProduct.ext
        · rfl
        · exact x.property.symm
      right_inv := fun _ => rfl
      map_mul' := fun x y => by
        funext i
        change x.val.left i * y.val.left (x.val.right⁻¹ * i) = _
        rw [show x.val.right = 1 from x.property]
        simp }
  let r : (OrthogonalPlaneIndex → OrthogonalPlaneActor) ≃*
      (OrthogonalPlaneActor × OrthogonalPlaneActor) :=
    { toFun := fun f => (f 1, f (Multiplicative.ofAdd 1))
      invFun := fun p i => if i = 1 then p.1 else p.2
      left_inv := fun f => by
        funext i
        have hi : i = 1 ∨ i = Multiplicative.ofAdd (1 : ZMod 2) := by
          have h : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
          exact h i.toAdd
        rcases hi with rfl | rfl <;> simp
      right_inv := fun p => by simp
      map_mul' := fun _ _ => rfl }
  exact q.trans (r.trans (e.prodCongr e))

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.SylowNormalizer.NaturalConstruction
