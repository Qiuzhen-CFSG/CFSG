module

public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.Torsor.Defs
public import Theory.AlgebraicGroup.Basic

universe u

/-! Constant algebraic groups attached to finite abstract groups. -/

namespace Theory.AlgebraicGroup

open scoped TensorProduct

open LinearMap Submodule

variable {k : Type u} [Field k]

public noncomputable def finiteGroupIdempotentPolynomial (X : Type u)
    (i : X) : MvPolynomial X k :=
  MvPolynomial.X i * MvPolynomial.X i - MvPolynomial.X i

public noncomputable def finiteGroupOrthogonalPolynomial (X : Type u)
    (i j : X) : MvPolynomial X k :=
  MvPolynomial.X i * MvPolynomial.X j

public noncomputable def finiteGroupSumPolynomial (X : Type u) [Finite X] :
    MvPolynomial X k := by
  letI := Fintype.ofFinite X
  exact (∑ i : X, MvPolynomial.X i) - MvPolynomial.C 1

/-- The one-hot affine zero locus representing a finite abstract group. -/
public noncomputable abbrev finiteGroupVariety (k : Type u) [Field k]
    (X : Type u) [Finite X] : Variety k := by
  letI := Fintype.ofFinite X
  exact
    { Coordinates := X
      finiteCoordinates := inferInstance
      equations :=
        (Set.range (finiteGroupIdempotentPolynomial (k := k) X) ∪
          {p | ∃ i j : X, i ≠ j ∧
            p = finiteGroupOrthogonalPolynomial (k := k) X i j}) ∪
          {finiteGroupSumPolynomial (k := k) X} }

/-- The one-hot point corresponding to an element of a finite type. -/
@[expose]
public noncomputable def finiteGroupPoint (X : Type u) [Finite X] (x : X) :
    Variety.Point (finiteGroupVariety k X) := by
  classical
  letI := Fintype.ofFinite X
  exact
    { val := fun i ↦ if i = x then 1 else 0
      isZero := by
        intro p hp
        rcases hp with (⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩) | hp
        · by_cases hi : i = x <;>
            simp [finiteGroupIdempotentPolynomial, evalPolynomial, hi]
        · by_cases hi : i = x
          · have hj : j ≠ x := by
              intro hj
              apply hij
              exact hi.trans hj.symm
            simp [finiteGroupOrthogonalPolynomial, evalPolynomial, hi, hj]
          · simp [finiteGroupOrthogonalPolynomial, evalPolynomial, hi]
        · rw [Set.mem_singleton_iff] at hp
          subst p
          simp [finiteGroupSumPolynomial, evalPolynomial] }

public lemma finiteGroupPoint_coordinate_zero_or_one
    (X : Type u) [Finite X]
    (x : Variety.Point (finiteGroupVariety k X)) (i : X) :
    x.val i = 0 ∨ x.val i = 1 := by
  have hz := x.isZero (finiteGroupIdempotentPolynomial (k := k) X i)
    (Set.mem_union_left _ (Set.mem_union_left _ ⟨i, rfl⟩))
  have hidem : x.val i * x.val i = x.val i := by
    exact sub_eq_zero.mp (by
      simpa [finiteGroupIdempotentPolynomial, evalPolynomial] using hz)
  have hprod : x.val i * (x.val i - 1) = 0 := by
    rw [mul_sub, mul_one, hidem, sub_self]
  rcases mul_eq_zero.mp hprod with hzero | hone
  · exact Or.inl hzero
  · exact Or.inr (sub_eq_zero.mp hone)

public lemma finiteGroupPoint_exists_one
    (X : Type u) [Finite X] [Nonempty X]
    (x : Variety.Point (finiteGroupVariety k X)) :
    ∃ i : X, x.val i = 1 := by
  classical
  let := Fintype.ofFinite X
  have hz := x.isZero (finiteGroupSumPolynomial (k := k) X)
    (Set.mem_union_right _ (Set.mem_singleton _))
  have hsum : ∑ i : X, x.val i = 1 := by
    exact sub_eq_zero.mp (by
      simpa [finiteGroupSumPolynomial, evalPolynomial] using hz)
  have hne : (∑ i : X, x.val i) ≠ 0 := by
    rw [hsum]
    exact one_ne_zero
  rcases Finset.exists_ne_zero_of_sum_ne_zero hne with ⟨i, hi, hne⟩
  rcases finiteGroupPoint_coordinate_zero_or_one X x i with hzero | hone
  · exact (hne hzero).elim
  · exact ⟨i, hone⟩

public lemma finiteGroupPoint_one_unique
    (X : Type u) [Finite X]
    (x : Variety.Point (finiteGroupVariety k X)) {i j : X}
    (hi : x.val i = 1) (hj : x.val j = 1) : i = j := by
  by_contra hij
  have hz := x.isZero (finiteGroupOrthogonalPolynomial (k := k) X i j)
    (Set.mem_union_left _ (Set.mem_union_right _ ⟨i, j, hij, rfl⟩))
  simp [finiteGroupOrthogonalPolynomial, evalPolynomial, hi, hj] at hz

/-- The points of the finite one-hot zero locus are exactly the elements of the
finite type. -/
@[expose]
public noncomputable def finiteGroupPointEquiv (X : Type u) [Finite X] [Nonempty X] :
    Variety.Point (finiteGroupVariety k X) ≃ X where
    toFun := fun x ↦ Classical.choose (finiteGroupPoint_exists_one (k := k) X x)
    invFun := finiteGroupPoint (k := k) X
    left_inv := by
      intro x
      apply Variety.Point.ext
      funext i
      let selected := Classical.choose (finiteGroupPoint_exists_one (k := k) X x)
      have hselected : x.val selected = 1 :=
        Classical.choose_spec (finiteGroupPoint_exists_one (k := k) X x)
      by_cases hi : i = selected
      · subst i
        rw [hselected]
        dsimp [selected]
        simp [finiteGroupPoint]
      · have hneOne : x.val i ≠ 1 := fun hone ↦
          hi (finiteGroupPoint_one_unique X x hone hselected)
        rcases finiteGroupPoint_coordinate_zero_or_one X x i with hzero | hone
        · rw [hzero]
          have hi' : i ≠ Classical.choose
              (finiteGroupPoint_exists_one (k := k) X x) := by
            simpa [selected] using hi
          simp [finiteGroupPoint, hi']
        · exact (hneOne hone).elim
    right_inv := by
      intro x
      apply finiteGroupPoint_one_unique (k := k) X (finiteGroupPoint (k := k) X x)
      · exact Classical.choose_spec
          (finiteGroupPoint_exists_one (k := k) X (finiteGroupPoint (k := k) X x))
      · simp [finiteGroupPoint]

/-- Coordinate polynomial for multiplication in a finite constant group. -/
public noncomputable def finiteGroupMulPolynomial (X : Type u) [Finite X] [Group X]
    (z : X) : MvPolynomial (X ⊕ X) k := by
  letI := Fintype.ofFinite X
  exact ∑ a : X, MvPolynomial.X (Sum.inl a) *
    MvPolynomial.X (Sum.inr (a⁻¹ * z))

/-- Coordinate polynomial for inversion in a finite constant group. -/
public noncomputable def finiteGroupInvPolynomial (X : Type u) [Group X]
    (z : X) : MvPolynomial X k :=
  MvPolynomial.X z⁻¹

/-- Every finite abstract group has a constant algebraic-group realization. -/
public noncomputable instance finiteGroup (X : Type u)
    [Finite X] [Group X] : AlgebraicGroup (finiteGroupVariety k X) := by
  classical
  letI := Fintype.ofFinite X
  let e := finiteGroupPointEquiv (k := k) X
  let hGroup : Group (Variety.Point (finiteGroupVariety k X)) := e.group
  letI : Group (Variety.Point (finiteGroupVariety k X)) := hGroup
  exact
    { toGroup := hGroup
      mulPolynomial := finiteGroupMulPolynomial (k := k) X
      invPolynomial := finiteGroupInvPolynomial (k := k) X
      mul_regular := by
        intro z x y
        let a := e x
        let b := e y
        have hx : x = finiteGroupPoint (k := k) X a :=
          (e.symm_apply_apply x).symm
        have hy : y = finiteGroupPoint (k := k) X b :=
          (e.symm_apply_apply y).symm
        rw [hx, hy]
        have hmulPoint :
            finiteGroupPoint (k := k) X a * finiteGroupPoint (k := k) X b =
              finiteGroupPoint (k := k) X (a * b) := by
          apply e.injective
          have hmapMul (u v : Variety.Point (finiteGroupVariety k X)) :
              e (u * v) = e u * e v := by
            change e (e.symm (e u * e v)) = e u * e v
            exact e.apply_symm_apply _
          rw [hmapMul]
          have ea : e (finiteGroupPoint (k := k) X a) = a := by
            change e (e.symm a) = a
            exact e.apply_symm_apply a
          have eb : e (finiteGroupPoint (k := k) X b) = b := by
            change e (e.symm b) = b
            exact e.apply_symm_apply b
          have eab : e (finiteGroupPoint (k := k) X (a * b)) = a * b := by
            change e (e.symm (a * b)) = a * b
            exact e.apply_symm_apply (a * b)
          rw [ea, eb, eab]
        rw [hmulPoint]
        change (finiteGroupPoint (k := k) X (a * b)).val z =
          evalPolynomial
            (Sum.elim (finiteGroupPoint (k := k) X a).val
              (finiteGroupPoint (k := k) X b).val)
            (finiteGroupMulPolynomial (k := k) X z)
        have hiff : a⁻¹ * z = b ↔ z = a * b := by
          constructor
          · intro h
            calc
              z = a * (a⁻¹ * z) := by simp
              _ = a * b := by rw [h]
          · intro h
            rw [h]
            simp
        simp [finiteGroupMulPolynomial, evalPolynomial, finiteGroupPoint]
        rw [Finset.sum_eq_single a]
        · simp [hiff]
        · intro c hc hca
          simp [hca]
        · simp
      inv_regular := by
        intro z x
        let a := e x
        have hx : x = finiteGroupPoint (k := k) X a :=
          (e.symm_apply_apply x).symm
        rw [hx]
        have hinvPoint :
            (finiteGroupPoint (k := k) X a)⁻¹ =
              finiteGroupPoint (k := k) X a⁻¹ := by
          apply e.injective
          have hmapInv (u : Variety.Point (finiteGroupVariety k X)) :
              e u⁻¹ = (e u)⁻¹ := by
            change e (e.symm (e u)⁻¹) = (e u)⁻¹
            exact e.apply_symm_apply _
          rw [hmapInv]
          have ea : e (finiteGroupPoint (k := k) X a) = a := by
            change e (e.symm a) = a
            exact e.apply_symm_apply a
          have eainv : e (finiteGroupPoint (k := k) X a⁻¹) = a⁻¹ := by
            change e (e.symm a⁻¹) = a⁻¹
            exact e.apply_symm_apply a⁻¹
          rw [ea, eainv]
        rw [hinvPoint]
        change (finiteGroupPoint (k := k) X a⁻¹).val z =
          evalPolynomial (finiteGroupPoint (k := k) X a).val
            (finiteGroupInvPolynomial (k := k) X z)
        have hiff : z⁻¹ = a ↔ z = a⁻¹ := by
          constructor
          · intro h
            calc
              z = (z⁻¹)⁻¹ := by simp
              _ = a⁻¹ := congrArg Inv.inv h
          · intro h
            rw [h]
            simp
        simp [finiteGroupInvPolynomial, evalPolynomial, finiteGroupPoint]
        by_cases hz : z = a⁻¹
        · rw [if_pos hz, if_pos (hiff.mpr hz)]
        · rw [if_neg hz, if_neg (fun h ↦ hz (hiff.mp h))] }

/-- The one-hot realization respects multiplication in the finite group. -/
public lemma finiteGroupPoint_mul (X : Type u) [Finite X] [Group X]
    (a b : X) :
    finiteGroupPoint (k := k) X a * finiteGroupPoint (k := k) X b =
      finiteGroupPoint (k := k) X (a * b) := by
  let e := finiteGroupPointEquiv (k := k) X
  apply e.injective
  have hmapMul (u v : Variety.Point (finiteGroupVariety k X)) :
      e (u * v) = e u * e v := by
    change e (e.symm (e u * e v)) = e u * e v
    exact e.apply_symm_apply _
  rw [hmapMul]
  change e (e.symm a) * e (e.symm b) = e (e.symm (a * b))
  simp

/-- The one-hot realization sends the abstract identity to the algebraic-group
identity. -/
public lemma finiteGroupPoint_one (X : Type u) [Finite X] [Group X] :
    finiteGroupPoint (k := k) X 1 = 1 := by
  let e := finiteGroupPointEquiv (k := k) X
  apply e.injective
  have hmapOne : e (1 : Variety.Point (finiteGroupVariety k X)) = 1 := by
    change e (e.symm 1) = 1
    exact e.apply_symm_apply 1
  calc
    e (finiteGroupPoint (k := k) X 1) = 1 := e.apply_symm_apply 1
    _ = e (1 : Variety.Point (finiteGroupVariety k X)) := hmapOne.symm

/-- The one-hot realization respects inversion in the finite group. -/
public lemma finiteGroupPoint_inv (X : Type u) [Finite X] [Group X]
    (a : X) :
    (finiteGroupPoint (k := k) X a)⁻¹ =
      finiteGroupPoint (k := k) X a⁻¹ := by
  let e := finiteGroupPointEquiv (k := k) X
  apply e.injective
  have hmapInv (u : Variety.Point (finiteGroupVariety k X)) :
      e u⁻¹ = (e u)⁻¹ := by
    change e (e.symm (e u)⁻¹) = (e u)⁻¹
    exact e.apply_symm_apply _
  rw [hmapInv]
  change (e (e.symm a))⁻¹ = e (e.symm a⁻¹)
  simp

end Theory.AlgebraicGroup
