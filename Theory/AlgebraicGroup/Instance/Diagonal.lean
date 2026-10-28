module

public import Theory.AlgebraicGroup.Product

universe u

/-!
The diagonal algebraic group `Dₙ = (kˣ)ⁿ` from GLS, Example 1.1.7.
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- The affine zero locus for `Dₙ`, with each diagonal entry times its inverse equal to one. -/
public abbrev dVariety (k : Type u) [Field k] (n : ℕ) : Variety k where
  Coordinates := ULift.{u} (Fin n) ⊕ ULift.{u} (Fin n)
  finiteCoordinates := inferInstance
  equations : Set (MvPolynomial (ULift.{u} (Fin n) ⊕ ULift.{u} (Fin n)) k) :=
    {p | ∃ i : Fin n, p = MvPolynomial.X (Sum.inl (ULift.up i)) *
        MvPolynomial.X (Sum.inr (ULift.up i)) - 1}

/-- A diagonal coordinate of a `Dₙ` point. -/
@[expose]
public def dPointEntry (n : ℕ) (x : Variety.Point (dVariety k n)) (i : Fin n) : k :=
  x.val (Sum.inl (ULift.up i))

/-- The inverse-diagonal coordinate of a `Dₙ` point. -/
@[expose]
public def dPointEntryInv (n : ℕ) (x : Variety.Point (dVariety k n)) (i : Fin n) : k :=
  x.val (Sum.inr (ULift.up i))

/-- A diagonal coordinate and its inverse coordinate multiply to one. -/
public lemma dPoint_entry_mul_inv (n : ℕ) (x : Variety.Point (dVariety k n)) (i : Fin n) :
    dPointEntry n x i * dPointEntryInv n x i = 1 := by
  have h := x.isZero (MvPolynomial.X (Sum.inl (ULift.up i)) *
      MvPolynomial.X (Sum.inr (ULift.up i)) - 1) (by
    exact Set.mem_ofPred.mpr ⟨i, rfl⟩)
  have hsum : evalPolynomial x.val (MvPolynomial.X (Sum.inl (ULift.up i))) *
      evalPolynomial x.val (MvPolynomial.X (Sum.inr (ULift.up i))) - 1 = 0 := by
    simpa [evalPolynomial, evalPolynomial_mul] using h
  simpa [dPointEntry, dPointEntryInv, evalPolynomial, evalPolynomial_X] using
    (sub_eq_zero.mp hsum)

/-- The inverse of a diagonal coordinate is the corresponding inverse coordinate. -/
public lemma dPoint_entry_inv (n : ℕ) (x : Variety.Point (dVariety k n)) (i : Fin n) :
    (dPointEntry n x i)⁻¹ = dPointEntryInv n x i :=
  (eq_inv_of_mul_eq_one_right (dPoint_entry_mul_inv n x i)).symm

/-- Every diagonal coordinate is a unit. -/
public lemma dPoint_entry_isUnit (n : ℕ) (x : Variety.Point (dVariety k n)) (i : Fin n) :
    IsUnit (dPointEntry n x i) :=
  IsUnit.of_mul_eq_one (dPointEntryInv n x i) (dPoint_entry_mul_inv n x i)

/-- The inverse coordinate of the associated unit. -/
public lemma dPoint_unit_inv (n : ℕ) (x : Variety.Point (dVariety k n)) (i : Fin n) :
    ((dPoint_entry_isUnit n x i).unit.inv : k) = dPointEntryInv n x i :=
  Units.inv_eq_of_mul_eq_one_right (u := (dPoint_entry_isUnit n x i).unit)
    (a := dPointEntryInv n x i) (dPoint_entry_mul_inv n x i)

/-- Point equivalence for `Dₙ`. -/
@[expose]
public def dPointEquiv (n : ℕ) : Variety.Point (dVariety k n) ≃ (Fin n → kˣ) where
  toFun := fun x i => ⟨dPointEntry n x i, dPointEntryInv n x i,
    dPoint_entry_mul_inv n x i, by rw [mul_comm]; exact dPoint_entry_mul_inv n x i⟩
  invFun := fun a => ⟨Sum.elim (fun p : ULift.{u} (Fin n) => (a p.down).val)
      (fun p : ULift.{u} (Fin n) => (a p.down).inv), by
    intro p hp
    rcases Set.mem_ofPred.mp hp with ⟨i, rfl⟩
    simp [evalPolynomial]⟩
  left_inv := by
    intro x
    apply Variety.Point.ext
    funext p
    cases p <;> rfl
  right_inv := by
    intro a
    ext i
    rfl

/-- Multiplication polynomials for `Dₙ`, defined pointwise. -/
public noncomputable def dMulPoly (n : ℕ) : (dVariety k n).Coordinates →
    MvPolynomial ((dVariety k n).Coordinates ⊕ (dVariety k n).Coordinates) k :=
  fun p => match p with
  | Sum.inl i => MvPolynomial.X (Sum.inl (Sum.inl i)) *
      MvPolynomial.X (Sum.inr (Sum.inl i))
  | Sum.inr i => MvPolynomial.X (Sum.inl (Sum.inr i)) *
      MvPolynomial.X (Sum.inr (Sum.inr i))

/-- Inverse polynomials for `Dₙ`, obtained by exchanging the two coordinates. -/
public noncomputable def dInvPoly (n : ℕ) : (dVariety k n).Coordinates →
    MvPolynomial (dVariety k n).Coordinates k :=
  fun p => match p with
  | Sum.inl i => MvPolynomial.X (Sum.inr i)
  | Sum.inr i => MvPolynomial.X (Sum.inl i)

/-- The algebraic-group structure on `Dₙ`. -/
public noncomputable instance dAlgebraicGroup (k : Type u) [Field k]
    (n : ℕ) : AlgebraicGroup (dVariety k n) := by
  let e := dPointEquiv (k := k) n
  let hGroup : Group (Variety.Point (dVariety k n)) := e.group
  letI : Group (Variety.Point (dVariety k n)) := hGroup
  exact
    { toGroup := hGroup
      mulPolynomial := dMulPoly n
      invPolynomial := dInvPoly n
      mul_regular := by
        intro p x y
        cases p with
        | inl i =>
            change (x * y).val (Sum.inl i) = evalPolynomial (Sum.elim x.val y.val)
              (dMulPoly n (Sum.inl i))
            simp [dMulPoly, evalPolynomial]
            change (e.symm (e x * e y)).val (Sum.inl i) =
              x.val (Sum.inl i) * y.val (Sum.inl i)
            have hz : ∀ z : Fin n → kˣ, (e.symm z).val (Sum.inl i) = (z i.down).val := by
              intro z
              rfl
            rw [hz]
            rfl
        | inr i =>
            change (x * y).val (Sum.inr i) = evalPolynomial (Sum.elim x.val y.val)
              (dMulPoly n (Sum.inr i))
            simp [dMulPoly, evalPolynomial]
            change (e.symm (e x * e y)).val (Sum.inr i) =
              x.val (Sum.inr i) * y.val (Sum.inr i)
            have hz : ∀ z : Fin n → kˣ, (e.symm z).val (Sum.inr i) = (z i.down).inv := by
              intro z
              rfl
            rw [hz]
            change ((e x) i.down * (e y) i.down)⁻¹ =
              x.val (Sum.inr i) * y.val (Sum.inr i)
            rw [mul_inv_rev, Units.val_mul]
            have hxval : (↑(e x i.down) : k) = dPointEntry n x i.down := by rfl
            have hyval : (↑(e y i.down) : k) = dPointEntry n y i.down := by rfl
            rw [show (↑((e x i.down)⁻¹ : kˣ) : k) = dPointEntryInv n x i.down by
              exact Units.inv_eq_of_mul_eq_one_right (u := e x i.down)
                (a := dPointEntryInv n x i.down)
                (by simpa [hxval] using dPoint_entry_mul_inv n x i.down)]
            rw [show (↑((e y i.down)⁻¹ : kˣ) : k) = dPointEntryInv n y i.down by
              exact Units.inv_eq_of_mul_eq_one_right (u := e y i.down)
                (a := dPointEntryInv n y i.down)
                (by simpa [hyval] using dPoint_entry_mul_inv n y i.down)]
            simp [dPointEntryInv, mul_comm]
      inv_regular := by
        intro p x
        cases p with
        | inl i =>
            change x⁻¹.val (Sum.inl i) = evalPolynomial x.val (dInvPoly n (Sum.inl i))
            simp [dInvPoly, evalPolynomial]
            change (e.symm (e x)⁻¹).val (Sum.inl i) = x.val (Sum.inr i)
            have hz : ∀ z : Fin n → kˣ, (e.symm z).val (Sum.inl i) = (z i.down).val := by
              intro z
              rfl
            rw [hz]
            rfl
        | inr i =>
            change x⁻¹.val (Sum.inr i) = evalPolynomial x.val (dInvPoly n (Sum.inr i))
            simp [dInvPoly, evalPolynomial]
            change (e.symm (e x)⁻¹).val (Sum.inr i) = x.val (Sum.inl i)
            have hz : ∀ z : Fin n → kˣ, (e.symm z).val (Sum.inr i) = (z i.down).inv := by
              intro z
              rfl
            rw [hz]
            change ((e x) i.down)⁻¹⁻¹ = x.val (Sum.inl i)
            rw [inv_inv]
            rfl }

/-- The standard product `D_n × KMult` carries the direct-product algebraic
group structure. -/
public noncomputable instance dVarietyProdKMultAlgebraicGroup (n : ℕ) :
    AlgebraicGroup (Variety.prod (dVariety k n) (dVariety k 1)) :=
  AlgebraicGroup.prod _ _

end Theory.AlgebraicGroup
