module

public import Theory.AlgebraicGroup.Instance.SL
public import Theory.AlgebraicGroup.Morphism.ClosedEmbedding
public import Theory.AlgebraicGroup.RootSystems.Classical
public import Theory.AlgebraicGroup.RootSubgroups.Defs

universe u

/-!
Elementary root subgroups for the standard type-A special-linear model.

For an ordered unequal pair `(i, j)` in `Fin (m + 1)`, the polynomial map
`t ↦ I + t Eᵢⱼ` defines an injective algebraic-group morphism from `KPlus k`
to `SL_(m+1)`.  Its closed image is identified with `KPlus k` by recovering
the parameter from the `(i, j)` matrix coordinate, so it is a concrete
one-parameter closed subgroup.

The inverse-conjugation convention in `RootWeightEquation` gives the exact
diagonal weight `zᵢ⁻¹ zⱼ`.  The final lemmas prove this formula without using a
classification theorem and record the elementary-matrix identities for
opposition, addition of composable roots, and coordinate reflection.  These
are the local matrix ingredients used to assemble the standard type-A
`RootGroupData`.

The construction is the usual elementary-transvection realization of the
roots of `SL_(m+1)` (GLS, Part I, Chapter A, Sections 1.9-1.10).
-/

namespace Theory.AlgebraicGroup

open StandardRootSystem

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public def typeASLRootPoint (m : ℕ) (r : TypeARootIndex m) (t : k) :
    Variety.Point (slVariety k (m + 1)) :=
  (slPointEquiv (k := k) (m + 1)).symm
    (Matrix.SpecialLinearGroup.transvection r.2 t)

@[simp]
public lemma typeASLRootPoint_val (m : ℕ) (r : TypeARootIndex m)
    (t : k) (a b : Fin (m + 1)) :
    (typeASLRootPoint m r t).val (ULift.up (a, b)) =
      (Matrix.transvection r.1.1 r.1.2 t) a b := by
  rfl

/-- The opposite of the type-A root indexed by the ordered pair `(i, j)`. -/
@[expose]
public def typeASLRootNeg (m : ℕ) (r : TypeARootIndex m) : TypeARootIndex m :=
  ⟨(r.1.2, r.1.1), fun h => r.2 h.symm⟩

/-- Partial addition of roots in ordered-pair coordinates.

The two nonzero cases are `(i, j) + (j, l) = (i, l)` and
`(j, l) + (i, j) = (i, l)`.  Opposite roots have zero sum and therefore return
`none`.
-/
@[expose]
public def typeASLRootAdd (m : ℕ) (r s : TypeARootIndex m) :
    Option (TypeARootIndex m) :=
  if _h : r.1.2 = s.1.1 then
    if hne : r.1.1 ≠ s.1.2 then
      some ⟨(r.1.1, s.1.2), hne⟩
    else
      none
  else if _h : s.1.2 = r.1.1 then
    if hne : s.1.1 ≠ r.1.2 then
      some ⟨(s.1.1, r.1.2), hne⟩
    else
      none
  else
    none

/-- Reflection in `(i, j)` swaps the two coordinate positions `i` and `j`. -/
@[expose]
public def typeASLRootReflect (m : ℕ) (r s : TypeARootIndex m) :
    TypeARootIndex m :=
  let e := Equiv.swap r.1.1 r.1.2
  ⟨(e s.1.1, e s.1.2), fun h => s.2 (e.injective h)⟩

@[simp]
public lemma typeASLRootAdd_forward (m : ℕ) (a b c : Fin (m + 1))
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    typeASLRootAdd m ⟨(a, b), hab⟩ ⟨(b, c), hbc⟩ =
      some ⟨(a, c), hac⟩ := by
  simp [typeASLRootAdd, hac]

/-- Passing to the opposite root transposes the elementary matrix. -/
public theorem typeASLRootPoint_neg_transpose
    (m : ℕ) (r : TypeARootIndex m) (t : k) :
    slPointMatrix (m + 1) (typeASLRootPoint m (typeASLRootNeg m r) t) =
      (slPointMatrix (m + 1) (typeASLRootPoint m r t)).transpose := by
  ext a b
  simp [slPointMatrix, typeASLRootPoint_val, typeASLRootNeg,
    Matrix.transvection, Matrix.one_apply, Matrix.single_apply,
    Matrix.transpose_apply]
  aesop

/-- Coordinate reindexing by the transposition `(i, j)` gives the reflected
root matrix exactly. -/
public theorem typeASLRootPoint_reflect_reindex
    (m : ℕ) (r s : TypeARootIndex m) (t : k) :
    slPointMatrix (m + 1) (typeASLRootPoint m (typeASLRootReflect m r s) t) =
      Matrix.reindexAlgEquiv k k (Equiv.swap r.1.1 r.1.2)
        (slPointMatrix (m + 1) (typeASLRootPoint m s t)) := by
  let e := Equiv.swap r.1.1 r.1.2
  let q : Matrix.TransvectionStruct (Fin (m + 1)) k :=
    ⟨s.1.1, s.1.2, s.2, t⟩
  change (q.reindexEquiv e).toMatrix = Matrix.reindexAlgEquiv k k e q.toMatrix
  exact Matrix.TransvectionStruct.toMatrix_reindexEquiv e q

/-- The elementary-matrix commutator realizes addition of composable type-A
roots. -/
public theorem typeASLRootPoint_addition_commutator
    (m : ℕ) (a b c : Fin (m + 1))
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (s t : k) :
    typeASLRootPoint m ⟨(a, b), hab⟩ s *
        typeASLRootPoint m ⟨(b, c), hbc⟩ t *
        (typeASLRootPoint m ⟨(a, b), hab⟩ s)⁻¹ *
        (typeASLRootPoint m ⟨(b, c), hbc⟩ t)⁻¹ =
      typeASLRootPoint m ⟨(a, c), hac⟩ (s * t) := by
  apply (slPointEquiv (k := k) (m + 1)).injective
  change (Matrix.SpecialLinearGroup.transvection hab s) *
      (Matrix.SpecialLinearGroup.transvection hbc t) *
      (Matrix.SpecialLinearGroup.transvection hab s)⁻¹ *
      (Matrix.SpecialLinearGroup.transvection hbc t)⁻¹ =
    Matrix.SpecialLinearGroup.transvection hac (s * t)
  rw [Matrix.SpecialLinearGroup.transvection_inv,
    Matrix.SpecialLinearGroup.transvection_inv]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_add,
    Matrix.add_mul, Matrix.single_mul_single_of_ne _ _ _ _ hab.symm,
    Matrix.single_mul_single_of_ne _ _ _ _ hbc.symm,
    Matrix.single_mul_single_of_ne _ _ _ _ hac.symm,
    Matrix.single_mul_single_same, ← Matrix.single_neg]
  abel

@[expose]
public def typeASLRootMorphism (m : ℕ) (r : TypeARootIndex m) :
    AlgebraicGroup.Morphism (KPlus k) (slVariety k (m + 1)) where
  toVariety :=
    { toFun := fun x => typeASLRootPoint m r (x.val PUnit.unit)
      regular := by
        rintro ⟨⟨a, b⟩⟩
        refine ⟨if a = r.1.1 ∧ b = r.1.2 then MvPolynomial.X PUnit.unit
          else if a = b then 1 else 0, ?_⟩
        intro x
        rw [typeASLRootPoint_val]
        by_cases hai : a = r.1.1
        · subst a
          by_cases hbj : b = r.1.2
          · subst b
            simp [Matrix.transvection, evalPolynomial, r.2]
          · have hbji : r.1.2 ≠ b := Ne.symm hbj
            simp [Matrix.transvection, Matrix.one_apply,
              evalPolynomial, hbj, hbji]
        · have hair : r.1.1 ≠ a := Ne.symm hai
          simp [Matrix.transvection, Matrix.one_apply,
            evalPolynomial, hai, hair] }
  map_one := by
    apply (slPointEquiv (k := k) (m + 1)).injective
    change Matrix.SpecialLinearGroup.transvection r.2
        ((1 : Variety.Point (KPlus k)).val PUnit.unit) = 1
    have hcoord : ((1 : Variety.Point (KPlus k)).val PUnit.unit) = 0 := by
      rw [← kPlusPoint_coordinate (k := k) (1 : Variety.Point (KPlus k))]
      rfl
    rw [hcoord]
    exact Matrix.SpecialLinearGroup.transvection_coeff_zero r.2
  map_mul := by
    intro x y
    apply (slPointEquiv (k := k) (m + 1)).injective
    change Matrix.SpecialLinearGroup.transvection r.2
        ((x * y).val PUnit.unit) =
      Matrix.SpecialLinearGroup.transvection r.2 (x.val PUnit.unit) *
        Matrix.SpecialLinearGroup.transvection r.2 (y.val PUnit.unit)
    rw [kPlusPoint_coordinate_mul]
    exact Matrix.SpecialLinearGroup.transvection_add r.2
      (x.val PUnit.unit) (y.val PUnit.unit)

@[simp]
public lemma typeASLRootMorphism_apply
    (m : ℕ) (r : TypeARootIndex m) (x : Variety.Point (KPlus k)) :
    (typeASLRootMorphism m r).onPoints x =
      typeASLRootPoint m r (x.val PUnit.unit) := by
  rfl

@[simp]
public lemma typeASLRootMorphism_kPlusPoint
    (m : ℕ) (r : TypeARootIndex m) (t : k) :
    (typeASLRootMorphism m r).onPoints (kPlusPoint t) =
      typeASLRootPoint m r t := by
  rfl

public theorem typeASLRootMorphism_injective
    (m : ℕ) (r : TypeARootIndex m) :
    Function.Injective (typeASLRootMorphism (k := k) m r).onPoints := by
  intro x y hxy
  apply (additiveGroupPointEquiv k).injective
  change x.val PUnit.unit = y.val PUnit.unit
  have hentry := congrArg
    (fun z : Variety.Point (slVariety k (m + 1)) =>
      (slPointEquiv (k := k) (m + 1) z).1 r.1.1 r.1.2) hxy
  change (Matrix.SpecialLinearGroup.transvection r.2 (x.val PUnit.unit)).1
      r.1.1 r.1.2 =
    (Matrix.SpecialLinearGroup.transvection r.2 (y.val PUnit.unit)).1
      r.1.1 r.1.2 at hentry
  simpa [Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.one_apply, Matrix.single_apply, r.2] using hentry

public theorem typeASLRootMorphism_coordinate_preimage
    (m : ℕ) (r : TypeARootIndex m) :
    ∀ c : (KPlus k).Coordinates,
      ∃ q : Variety.PolynomialFunction (slVariety k (m + 1)),
        Variety.PolynomialFunction.pullback (typeASLRootMorphism m r).toVariety q =
          Variety.PolynomialFunction.ofPolynomial (KPlus k) (MvPolynomial.X c) := by
  intro c
  refine ⟨Variety.PolynomialFunction.ofPolynomial (slVariety k (m + 1))
    (MvPolynomial.X (ULift.up (r.1.1, r.1.2))), ?_⟩
  apply Variety.PolynomialFunction.ext
  intro x
  simp only [Variety.PolynomialFunction.pullback,
    Variety.PolynomialFunction.ofPolynomial,
    Variety.PolynomialFunction.toFun]
  simp only [evalPolynomial_X]
  change ((typeASLRootMorphism m r).onPoints x).val
    (ULift.up (r.1.1, r.1.2)) = x.val c
  rw [typeASLRootMorphism_apply, typeASLRootPoint_val]
  simp [Matrix.transvection, r.2]

@[expose]
public noncomputable def typeASLRootSubgroup (m : ℕ) (r : TypeARootIndex m) :
    ClosedSubgroup (slVariety k (m + 1)) :=
  (typeASLRootMorphism m r).imageClosedSubgroup

public noncomputable def typeASLRootParametrization
    (m : ℕ) (r : TypeARootIndex m) :
    @OneParameterParametrization k _
      (typeASLRootSubgroup (k := k) m r).carrierVariety
      (typeASLRootSubgroup (k := k) m r).carrierAlgebraicGroup :=
  Classical.choose ((typeASLRootMorphism m r).iso_imageClosedSubgroup_of_coordinate_preimage
    (typeASLRootMorphism_injective m r)
    (typeASLRootMorphism_coordinate_preimage m r))

public theorem typeASLRootSubgroup_isOneParameter
    (m : ℕ) (r : TypeARootIndex m) :
    @IsOneParameterGroup k _
      (typeASLRootSubgroup (k := k) m r).carrierVariety
      (typeASLRootSubgroup (k := k) m r).carrierAlgebraicGroup :=
  ⟨typeASLRootParametrization m r⟩

public theorem typeASLRootParametrization_hom
    (m : ℕ) (r : TypeARootIndex m) :
    @AlgebraicGroup.Iso.hom k _ (KPlus k)
        (typeASLRootSubgroup (k := k) m r).carrierVariety
        (inferInstance : AlgebraicGroup (KPlus k))
        (typeASLRootSubgroup (k := k) m r).carrierAlgebraicGroup
        (typeASLRootParametrization (k := k) m r) =
      (typeASLRootMorphism m r).codRestrictClosedSubgroup
        (typeASLRootSubgroup (k := k) m r) (fun y => ⟨y, rfl⟩) :=
  Classical.choose_spec
    ((typeASLRootMorphism m r).iso_imageClosedSubgroup_of_coordinate_preimage
      (typeASLRootMorphism_injective m r)
      (typeASLRootMorphism_coordinate_preimage m r))

public theorem typeASLRootParametrization_include_value
    (m : ℕ) (r : TypeARootIndex m) (t : k) :
    (typeASLRootSubgroup (k := k) m r).includePoint
        (@OneParameterParametrization.value k _
          (typeASLRootSubgroup (k := k) m r).carrierVariety
          (typeASLRootSubgroup (k := k) m r).carrierAlgebraicGroup
          (typeASLRootParametrization m r) t) =
      typeASLRootPoint m r t := by
  let _ : AlgebraicGroup
      (typeASLRootSubgroup (k := k) m r).carrierVariety :=
    (typeASLRootSubgroup (k := k) m r).carrierAlgebraicGroup
  change (typeASLRootSubgroup (k := k) m r).inclusion.onPoints
      ((@AlgebraicGroup.Iso.hom k _ (KPlus k)
          (typeASLRootSubgroup (k := k) m r).carrierVariety
          (inferInstance : AlgebraicGroup (KPlus k))
          (typeASLRootSubgroup (k := k) m r).carrierAlgebraicGroup
          (typeASLRootParametrization m r)).onPoints (kPlusPoint t)) = _
  rw [typeASLRootParametrization_hom]
  exact (typeASLRootMorphism m r).codRestrictClosedSubgroup_inclusion_apply
    (typeASLRootSubgroup (k := k) m r) (fun y => ⟨y, rfl⟩) (kPlusPoint t)

public theorem typeASLRootPoint_diagonal_conjugation
    (m : ℕ) (r : TypeARootIndex m) (t : k)
    (d : Variety.Point (slVariety k (m + 1)))
    (z : Fin (m + 1) → kˣ)
    (hd : slPointMatrix (m + 1) d =
      Matrix.diagonal (fun a => (z a : k))) :
    d⁻¹ * typeASLRootPoint m r t * d =
      typeASLRootPoint m r (((z r.1.1 : k)⁻¹) * t * (z r.1.2 : k)) := by
  have hcomm : typeASLRootPoint m r t * d =
      d * typeASLRootPoint m r
        (((z r.1.1 : k)⁻¹) * t * (z r.1.2 : k)) := by
    apply (slPointEquiv (k := k) (m + 1)).injective
    change Matrix.SpecialLinearGroup.transvection r.2 t *
        slPointEquiv (k := k) (m + 1) d =
      slPointEquiv (k := k) (m + 1) d *
        Matrix.SpecialLinearGroup.transvection r.2
          (((z r.1.1 : k)⁻¹) * t * (z r.1.2 : k))
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    change Matrix.transvection r.1.1 r.1.2 t * slPointMatrix (m + 1) d =
      slPointMatrix (m + 1) d *
        Matrix.transvection r.1.1 r.1.2
          (((z r.1.1 : k)⁻¹) * t * (z r.1.2 : k))
    rw [hd]
    ext a b
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hab : a = b
    · subst b
      have hrdiag : ¬ (r.1.1 = a ∧ r.1.2 = a) := by
        rintro ⟨hi, hj⟩
        exact r.2 (hi.trans hj.symm)
      simp [Matrix.transvection, hrdiag]
    · by_cases hr : r.1.1 = a ∧ r.1.2 = b
      · rcases hr with ⟨rfl, rfl⟩
        simp [Matrix.transvection, r.2]
        field_simp
      · simp [Matrix.transvection, hab, hr]
  calc
    d⁻¹ * typeASLRootPoint m r t * d =
        d⁻¹ * (typeASLRootPoint m r t * d) := by rw [mul_assoc]
    _ = d⁻¹ * (d * typeASLRootPoint m r
        (((z r.1.1 : k)⁻¹) * t * (z r.1.2 : k))) := congrArg (d⁻¹ * ·) hcomm
    _ = typeASLRootPoint m r
        (((z r.1.1 : k)⁻¹) * t * (z r.1.2 : k)) := by simp

public theorem typeASLRootSubgroup_conjugation_mem_of_diagonal
    (m : ℕ) (r : TypeARootIndex m)
    (d : Variety.Point (slVariety k (m + 1)))
    (z : Fin (m + 1) → kˣ)
    (hd : slPointMatrix (m + 1) d =
      Matrix.diagonal (fun a => (z a : k)))
    (x : Variety.Point (slVariety k (m + 1)))
    (hx : x ∈ typeASLRootSubgroup (k := k) m r) :
    d⁻¹ * x * d ∈ typeASLRootSubgroup (k := k) m r := by
  change x ∈ (typeASLRootMorphism m r).image at hx
  rcases hx with ⟨q, rfl⟩
  rw [typeASLRootMorphism_apply,
    typeASLRootPoint_diagonal_conjugation m r (q.val PUnit.unit) d z hd]
  exact ⟨kPlusPoint (((z r.1.1 : k)⁻¹) * q.val PUnit.unit * (z r.1.2 : k)), rfl⟩

public theorem typeASLRootSubgroup_rootWeightEquation_of_diagonal
    (m : ℕ) (r : TypeARootIndex m)
    (T : ClosedSubgroup (slVariety k (m + 1)))
    (chi : TorusWeight T)
    (z : Variety.Point T.carrierVariety → Fin (m + 1) → kˣ)
    (hdiag : ∀ s, slPointMatrix (m + 1) (T.includePoint s) =
      Matrix.diagonal (fun a => (z s a : k)))
    (hchi : ∀ s,
      (@TorusCharacter.pointCharacter k _ T.carrierVariety
        T.carrierAlgebraicGroup chi) s =
      ((z s r.1.1 : k)⁻¹) * (z s r.1.2 : k)) :
    RootWeightEquation T (typeASLRootSubgroup (k := k) m r) chi := by
  intro y t s
  let _ : AlgebraicGroup T.carrierVariety := T.carrierAlgebraicGroup
  let _ : AlgebraicGroup
      (typeASLRootSubgroup (k := k) m r).carrierVariety :=
    (typeASLRootSubgroup (k := k) m r).carrierAlgebraicGroup
  let p := typeASLRootParametrization (k := k) m r
  rcases oneParameterParametrization_eq_rescale p y with ⟨c, hc, _⟩
  rw [show (typeASLRootSubgroup (k := k) m r).includePoint (y.value t) =
      typeASLRootPoint m r (c * t) by
        rw [hc.2, typeASLRootParametrization_include_value]]
  rw [show (typeASLRootSubgroup (k := k) m r).includePoint
        (y.value (chi.pointCharacter s * t)) =
      typeASLRootPoint m r (c * (chi.pointCharacter s * t)) by
        rw [hc.2, typeASLRootParametrization_include_value]]
  rw [typeASLRootPoint_diagonal_conjugation m r (c * t)
    (T.includePoint s) (z s) (hdiag s)]
  congr 1
  rw [hchi]
  ring

end Theory.AlgebraicGroup
