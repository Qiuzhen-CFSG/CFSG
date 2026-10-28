module

public import Theory.AlgebraicGroup.Basic

universe u

/-! The additive algebraic group from GLS, Example 1.1.7. -/

namespace Theory.AlgebraicGroup

/-- The additive group `Gₐ`, presented by the affine line. -/
public abbrev additiveGroupVariety (k : Type u) [Field k] : Variety k where
  Coordinates := PUnit.{u + 1}
  finiteCoordinates := inferInstance
  equations := (∅ : Set (MvPolynomial PUnit.{u + 1} k))

/-- The points of `Gₐ` are the elements of `k`. -/
@[expose]
public def additiveGroupPointEquiv (k : Type u) [Field k] :
    Variety.Point (additiveGroupVariety k) ≃ Multiplicative k where
  toFun := fun x => x.val PUnit.unit
  invFun := fun a => ⟨fun _ => a, by intro p hp; simp at hp⟩
  left_inv := by
    intro x
    apply Variety.Point.ext
    funext i
    rfl
  right_inv := by
    intro a
    rfl

public noncomputable instance additiveGroupAlgebraicGroup (k : Type u) [Field k] :
    AlgebraicGroup (additiveGroupVariety k) := by
  let e := additiveGroupPointEquiv k
  let hGroup : Group (Variety.Point (additiveGroupVariety k)) := e.group
  letI : Group (Variety.Point (additiveGroupVariety k)) := hGroup
  exact
    { toGroup := hGroup
      mulPolynomial := fun _ : PUnit.{u + 1} =>
        MvPolynomial.X (Sum.inl PUnit.unit) + MvPolynomial.X (Sum.inr PUnit.unit)
      invPolynomial := fun _ : PUnit.{u + 1} => -MvPolynomial.X PUnit.unit
      mul_regular := by
        intro i x y
        change (x * y).val PUnit.unit = evalPolynomial (Sum.elim x.val y.val)
          (MvPolynomial.X (Sum.inl PUnit.unit) + MvPolynomial.X (Sum.inr PUnit.unit))
        simp [evalPolynomial]
        change (e.symm (e x * e y)).val PUnit.unit = x.val PUnit.unit + y.val PUnit.unit
        have hz : ∀ z : Multiplicative k, (e.symm z).val PUnit.unit = z := by
          intro z
          rfl
        rw [hz]
        rfl
      inv_regular := by
        intro i x
        change x⁻¹.val PUnit.unit = evalPolynomial x.val (-MvPolynomial.X PUnit.unit)
        simp [evalPolynomial]
        change (e.symm (e x)⁻¹).val PUnit.unit = -x.val PUnit.unit
        have hz : ∀ z : Multiplicative k, (e.symm z).val PUnit.unit = z := by
          intro z
          rfl
        rw [hz]
        rfl }

end Theory.AlgebraicGroup
