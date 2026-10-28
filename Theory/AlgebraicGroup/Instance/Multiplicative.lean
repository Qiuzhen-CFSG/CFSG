module

public import Theory.AlgebraicGroup.Basic

universe u

/-! The multiplicative algebraic group from GLS, Example 1.1.7. -/

namespace Theory.AlgebraicGroup

/-- The multiplicative group `Gₘ`, presented by pairs `(x, x⁻¹)`. -/
public abbrev multiplicativeGroupVariety (k : Type u) [Field k] : Variety k where
  Coordinates := PUnit.{u + 1} ⊕ PUnit.{u + 1}
  finiteCoordinates := inferInstance
  equations : Set (MvPolynomial (PUnit.{u + 1} ⊕ PUnit.{u + 1}) k) :=
    {MvPolynomial.X (Sum.inl PUnit.unit) *
      MvPolynomial.X (Sum.inr PUnit.unit) - 1}

/-- The points of `Gₘ` are the units of `k`. -/
@[expose]
public def multiplicativeGroupPointEquiv (k : Type u) [Field k] :
    Variety.Point (multiplicativeGroupVariety k) ≃ kˣ where
  toFun := fun x => ⟨x.val (Sum.inl PUnit.unit), x.val (Sum.inr PUnit.unit),
    (by
      have h := x.isZero
        (MvPolynomial.X (Sum.inl PUnit.unit) *
          MvPolynomial.X (Sum.inr PUnit.unit) - 1) (by simp)
      simpa [evalPolynomial, sub_eq_zero] using h),
    (by
      have h := x.isZero
        (MvPolynomial.X (Sum.inl PUnit.unit) *
          MvPolynomial.X (Sum.inr PUnit.unit) - 1) (by simp)
      simpa [evalPolynomial, sub_eq_zero, mul_comm] using h)⟩
  invFun := fun a => ⟨Sum.elim (fun _ => a.val) (fun _ => a.inv), by
    intro p hp
    simp at hp
    subst hp
    simp [evalPolynomial]⟩
  left_inv := by
    intro x
    apply Variety.Point.ext
    funext i
    cases i <;> rfl
  right_inv := by
    intro a
    rfl

public noncomputable instance multiplicativeGroupAlgebraicGroup
    (k : Type u) [Field k] : AlgebraicGroup (multiplicativeGroupVariety k) := by
  let e := multiplicativeGroupPointEquiv k
  let hGroup : Group (Variety.Point (multiplicativeGroupVariety k)) := e.group
  letI : Group (Variety.Point (multiplicativeGroupVariety k)) := hGroup
  exact
    { toGroup := hGroup
      mulPolynomial := fun
        | Sum.inl _ => MvPolynomial.X (Sum.inl (Sum.inl PUnit.unit)) *
            MvPolynomial.X (Sum.inr (Sum.inl PUnit.unit))
        | Sum.inr _ => MvPolynomial.X (Sum.inl (Sum.inr PUnit.unit)) *
            MvPolynomial.X (Sum.inr (Sum.inr PUnit.unit))
      invPolynomial := fun
        | Sum.inl _ => MvPolynomial.X (Sum.inr PUnit.unit)
        | Sum.inr _ => MvPolynomial.X (Sum.inl PUnit.unit)
      mul_regular := by
        intro i x y
        cases i with
        | inl u =>
            change (x * y).val (Sum.inl PUnit.unit) =
              evalPolynomial (Sum.elim x.val y.val)
                (MvPolynomial.X (Sum.inl (Sum.inl PUnit.unit)) *
                  MvPolynomial.X (Sum.inr (Sum.inl PUnit.unit)))
            simp [evalPolynomial]
            change (e.symm (e x * e y)).val (Sum.inl PUnit.unit) =
              x.val (Sum.inl PUnit.unit) * y.val (Sum.inl PUnit.unit)
            have hz : ∀ z : kˣ, (e.symm z).val (Sum.inl PUnit.unit) = z.val := by
              intro z
              rfl
            rw [hz]
            rfl
        | inr u =>
            change (x * y).val (Sum.inr PUnit.unit) =
              evalPolynomial (Sum.elim x.val y.val)
                (MvPolynomial.X (Sum.inl (Sum.inr PUnit.unit)) *
                  MvPolynomial.X (Sum.inr (Sum.inr PUnit.unit)))
            simp [evalPolynomial]
            change (e.symm (e x * e y)).val (Sum.inr PUnit.unit) =
              x.val (Sum.inr PUnit.unit) * y.val (Sum.inr PUnit.unit)
            have hz : ∀ z : kˣ, (e.symm z).val (Sum.inr PUnit.unit) = z.inv := by
              intro z
              rfl
            rw [hz]
            change ((e x) * (e y))⁻¹ =
              x.val (Sum.inr PUnit.unit) * y.val (Sum.inr PUnit.unit)
            rw [mul_inv_rev]
            simp [e, multiplicativeGroupPointEquiv, mul_comm]
      inv_regular := by
        intro i x
        cases i with
        | inl u =>
            change x⁻¹.val (Sum.inl PUnit.unit) =
              evalPolynomial x.val (MvPolynomial.X (Sum.inr PUnit.unit))
            simp [evalPolynomial]
            change (e.symm (e x)⁻¹).val (Sum.inl PUnit.unit) =
              x.val (Sum.inr PUnit.unit)
            have hz : ∀ z : kˣ, (e.symm z).val (Sum.inl PUnit.unit) = z.val := by
              intro z
              rfl
            rw [hz]
            rfl
        | inr u =>
            change x⁻¹.val (Sum.inr PUnit.unit) =
              evalPolynomial x.val (MvPolynomial.X (Sum.inl PUnit.unit))
            simp [evalPolynomial]
            change (e.symm (e x)⁻¹).val (Sum.inr PUnit.unit) =
              x.val (Sum.inl PUnit.unit)
            have hz : ∀ z : kˣ, (e.symm z).val (Sum.inr PUnit.unit) = z.inv := by
              intro z
              rfl
            rw [hz]
            change ((e x)⁻¹)⁻¹ = x.val (Sum.inl PUnit.unit)
            rw [inv_inv]
            rfl }

end Theory.AlgebraicGroup

