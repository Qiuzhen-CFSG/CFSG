module

import Mathlib.GroupTheory.Perm.Support
public import Theory.AlgebraicGroup.Bor1.RepresentationDifferentialKernelEquivalence
public import Theory.AlgebraicGroup.Representations.Algebraic.Natural
public import Theory.AlgebraicGroup.RootSubgroups.Tangent
public import Theory.AlgebraicGroup.RootSystems.EvenOrthogonalDiagonalTorus
public import Theory.AlgebraicGroup.Tori.Character.Duality

/-!
# Identity-tangent weights for split even Omega

For an algebraically closed field of arbitrary characteristic and hyperbolic rank
`n >= 4`, this module classifies the nontrivial weights in the identity tangent
of the exact split even-Omega carrier under its standard diagonal torus.  They
are precisely among the explicit characters indexed by `TypeDRootIndex n`.

The proof uses the natural representation on the hyperbolic space.  Its matrix
coefficients detect every nonzero identity tangent, and diagonal conjugation
gives each detected coefficient the quotient of its row and column characters.
Differentiating the quadratic-isometry equation on an isotropic hyperbolic basis
vector eliminates the two opposite-coordinate quotients.  This uses no division
by two and therefore also applies in characteristic two.  A direct four-case
calculation then identifies every remaining quotient with an explicit type-D
root weight.

This is the coordinate realization of the standard split type-D root system
used in GLS, Part I, Chapter A, Sections 1.9--1.10.  It is deliberately
independent of downstream classification of type-D group versions.
-/

open scoped BigOperators

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

open StandardRootSystem

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

private abbrev hyperbolicTangentIndex (n : Nat) := Fin n ⊕ Fin n

private noncomputable def hyperbolicTangentBasis (n : Nat) :
    Module.Basis (hyperbolicTangentIndex n) k (HyperbolicSpace k n) :=
  (Pi.basisFun k (Fin n)).prod (Pi.basisFun k (Fin n))

private noncomputable abbrev evenOrthogonalOmega (n : Nat) :=
  evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
    (standardHyperbolicSplit n)

private noncomputable def evenOrthogonalNaturalRepresentation (n : Nat) :
    RationalRepresentation (evenOrthogonalOmega (k := k) n).carrierVariety
      (HyperbolicSpace k n) :=
  naturalClosedLinearSubgroupRepresentation
    (Module.finBasis k (HyperbolicSpace k n)) (evenOrthogonalOmega n)
    (AlgebraicGroup.Iso.id _)

private lemma evenOrthogonalNaturalRepresentation_action (n : Nat)
    (g : Variety.Point (evenOrthogonalOmega (k := k) n).carrierVariety) :
    (evenOrthogonalNaturalRepresentation (k := k) n).action g =
      glPointEquivOf k (HyperbolicSpace k n)
        (Module.finBasis k (HyperbolicSpace k n))
        ((evenOrthogonalOmega n).inclusion.onPoints g) := by
  rfl

private noncomputable def hyperbolicDiagonalEntryExponent (n : Nat) :
    hyperbolicTangentIndex n → Fin n → ℤ
  | .inl i => Pi.single i 1
  | .inr i => Pi.single i (-1)

private noncomputable def hyperbolicDiagonalEntryCharacter (n : Nat)
    (hn : 4 ≤ n) (p : hyperbolicTangentIndex n) :
    letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
    TorusWeight (evenOrthogonalDiagonalTorus (k := k) n hn) := by
  letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
  exact evenOrthogonalDiagonalCharacter (k := k) n hn
    (hyperbolicDiagonalEntryExponent n p)

private noncomputable def evenOrthogonalDiagonalCharacterAddEquiv (n : Nat)
    (hn : 4 ≤ n) :
    letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
    (Fin n → ℤ) ≃+ Additive
      (TorusWeight (evenOrthogonalDiagonalTorus (k := k) n hn)) := by
  letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
  exact (dLaurentCharacterAddEquiv (k := k) n).trans
    (evenOrthogonalDiagonalCharacterTransport (k := k) n hn).toAdditive

private lemma evenOrthogonalDiagonalCharacterAddEquiv_apply (n : Nat)
    (hn : 4 ≤ n) (z : Fin n → ℤ) :
    letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
    evenOrthogonalDiagonalCharacterAddEquiv (k := k) n hn z =
      Additive.ofMul (evenOrthogonalDiagonalCharacter (k := k) n hn z) := by
  rfl

private noncomputable def evenOrthogonalRootMatrixCoordinate (n : Nat) :
    TypeDRootIndex n → hyperbolicTangentIndex n × hyperbolicTangentIndex n
  | ⟨⟨⟨i, j⟩, _⟩, s, t⟩ =>
      (if s.1 = 1 then Sum.inl i else Sum.inr i,
        if t.1 = 1 then Sum.inr j else Sum.inl j)

private lemma evenOrthogonalRootExponent_eq_entry_sub (n : Nat)
    (r : TypeDRootIndex n) :
    evenOrthogonalRootExponent n r =
      hyperbolicDiagonalEntryExponent n (evenOrthogonalRootMatrixCoordinate n r).2 -
        hyperbolicDiagonalEntryExponent n (evenOrthogonalRootMatrixCoordinate n r).1 := by
  funext q
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    by_cases hqi : q = i <;> by_cases hqj : q = j <;>
      norm_num [evenOrthogonalRootExponent, evenOrthogonalRootMatrixCoordinate,
        hyperbolicDiagonalEntryExponent, sub_eq_add_neg,
        Pi.single_apply, hqi, hqj, hij.ne, hij.ne', add_comm]

private lemma evenOrthogonalRootWeight_eq_entryCharacters (n : Nat)
    (hn : 4 ≤ n) (r : TypeDRootIndex n) :
    letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
    evenOrthogonalRootWeight (k := k) n hn r =
      hyperbolicDiagonalEntryCharacter (k := k) n hn
          (evenOrthogonalRootMatrixCoordinate n r).2 *
        (hyperbolicDiagonalEntryCharacter (k := k) n hn
          (evenOrthogonalRootMatrixCoordinate n r).1)⁻¹ := by
  letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
  rw [evenOrthogonalRootWeight, evenOrthogonalRootExponent_eq_entry_sub]
  apply Additive.ofMul.injective
  simp [hyperbolicDiagonalEntryCharacter,
    ← evenOrthogonalDiagonalCharacterAddEquiv_apply, sub_eq_add_neg]

private lemma hyperbolicDiagonalEntryCharacter_opposite (n : Nat)
    (hn : 4 ≤ n) (i : Fin n) :
    letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
    hyperbolicDiagonalEntryCharacter (k := k) n hn (Sum.inr i) =
      (hyperbolicDiagonalEntryCharacter (k := k) n hn (Sum.inl i))⁻¹ := by
  letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
  apply Additive.ofMul.injective
  change evenOrthogonalDiagonalCharacterAddEquiv (k := k) n hn
      (hyperbolicDiagonalEntryExponent n (Sum.inr i)) =
    -(evenOrthogonalDiagonalCharacterAddEquiv (k := k) n hn
      (hyperbolicDiagonalEntryExponent n (Sum.inl i)))
  rw [← map_neg]
  congr 1
  funext q
  by_cases hqi : q = i <;>
    simp [hyperbolicDiagonalEntryExponent, hqi]

private lemma exists_evenOrthogonalRootWeight_inv_eq_entry_quotient (n : Nat)
    (hn : 4 ≤ n) (p q : hyperbolicTangentIndex n) (hpq : p ≠ q)
    (hopposite : ∀ i : Fin n, (p, q) ≠ (Sum.inl i, Sum.inr i) ∧
      (p, q) ≠ (Sum.inr i, Sum.inl i)) :
    letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
    ∃ r : TypeDRootIndex n,
      (evenOrthogonalRootWeight (k := k) n hn r)⁻¹ =
        hyperbolicDiagonalEntryCharacter (k := k) n hn p *
          (hyperbolicDiagonalEntryCharacter (k := k) n hn q)⁻¹ := by
  letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
  let pos : ({-1, 1} : Set ℝ) := ⟨1, by simp⟩
  let neg : ({-1, 1} : Set ℝ) := ⟨-1, by simp⟩
  rcases p with i | i <;> rcases q with j | j
  · have hij : i ≠ j := fun h => hpq (congrArg Sum.inl h)
    rcases lt_or_gt_of_ne hij with hij | hji
    · refine ⟨⟨⟨⟨i, j⟩, hij⟩, pos, neg⟩, ?_⟩
      rw [evenOrthogonalRootWeight_eq_entryCharacters]
      norm_num [evenOrthogonalRootMatrixCoordinate, pos, neg]
    · refine ⟨⟨⟨⟨j, i⟩, hji⟩, neg, pos⟩, ?_⟩
      rw [evenOrthogonalRootWeight_eq_entryCharacters]
      norm_num [evenOrthogonalRootMatrixCoordinate, pos, neg]
      rw [hyperbolicDiagonalEntryCharacter_opposite,
        hyperbolicDiagonalEntryCharacter_opposite]
      simp only [inv_inv]
      ac_rfl
  · have hij : i ≠ j := by
      intro h
      subst j
      exact (hopposite i).1 rfl
    rcases lt_or_gt_of_ne hij with hij | hji
    · refine ⟨⟨⟨⟨i, j⟩, hij⟩, pos, pos⟩, ?_⟩
      rw [evenOrthogonalRootWeight_eq_entryCharacters]
      norm_num [evenOrthogonalRootMatrixCoordinate, pos]
    · refine ⟨⟨⟨⟨j, i⟩, hji⟩, pos, pos⟩, ?_⟩
      rw [evenOrthogonalRootWeight_eq_entryCharacters]
      norm_num [evenOrthogonalRootMatrixCoordinate, pos]
      rw [hyperbolicDiagonalEntryCharacter_opposite,
        hyperbolicDiagonalEntryCharacter_opposite]
      simp only [inv_inv]
      ac_rfl
  · have hij : i ≠ j := by
      intro h
      subst j
      exact (hopposite i).2 rfl
    rcases lt_or_gt_of_ne hij with hij | hji
    · refine ⟨⟨⟨⟨i, j⟩, hij⟩, neg, neg⟩, ?_⟩
      rw [evenOrthogonalRootWeight_eq_entryCharacters]
      norm_num [evenOrthogonalRootMatrixCoordinate, neg]
    · refine ⟨⟨⟨⟨j, i⟩, hji⟩, neg, neg⟩, ?_⟩
      rw [evenOrthogonalRootWeight_eq_entryCharacters]
      norm_num [evenOrthogonalRootMatrixCoordinate, neg]
      rw [hyperbolicDiagonalEntryCharacter_opposite,
        hyperbolicDiagonalEntryCharacter_opposite]
      ac_rfl
  · have hij : i ≠ j := fun h => hpq (congrArg Sum.inr h)
    rcases lt_or_gt_of_ne hij with hij | hji
    · refine ⟨⟨⟨⟨i, j⟩, hij⟩, neg, pos⟩, ?_⟩
      rw [evenOrthogonalRootWeight_eq_entryCharacters]
      norm_num [evenOrthogonalRootMatrixCoordinate, pos, neg]
    · refine ⟨⟨⟨⟨j, i⟩, hji⟩, pos, neg⟩, ?_⟩
      rw [evenOrthogonalRootWeight_eq_entryCharacters]
      norm_num [evenOrthogonalRootMatrixCoordinate, pos, neg]
      rw [hyperbolicDiagonalEntryCharacter_opposite,
        hyperbolicDiagonalEntryCharacter_opposite]
      simp only [inv_inv]
      ac_rfl

private noncomputable def hyperbolicMatrixCoordinate (n : Nat)
    (p q : hyperbolicTangentIndex n) :
    Variety.PolynomialFunction (evenOrthogonalOmega (k := k) n).carrierVariety :=
  rationalRepresentationLinearMatrixCoefficient
    (evenOrthogonalNaturalRepresentation n)
    (Module.finBasis k (HyperbolicSpace k n))
    (evenOrthogonalOmega n).inclusion
    ((hyperbolicTangentBasis n).coord p) (hyperbolicTangentBasis n q)

private lemma hyperbolicMatrixCoordinate_apply (n : Nat)
    (p q : hyperbolicTangentIndex n)
    (x : Variety.Point (evenOrthogonalOmega (k := k) n).carrierVariety) :
    hyperbolicMatrixCoordinate n p q x =
      (hyperbolicTangentBasis n).coord p
        (((evenOrthogonalNaturalRepresentation n).action x :
          Module.End k (HyperbolicSpace k n)) (hyperbolicTangentBasis n q)) := by
  rw [hyperbolicMatrixCoordinate,
    rationalRepresentationLinearMatrixCoefficient_apply
      (evenOrthogonalNaturalRepresentation n)
      (Module.finBasis k (HyperbolicSpace k n))
      (evenOrthogonalOmega n).inclusion
      (fun g => (evenOrthogonalNaturalRepresentation_action n g).symm)]

omit [IsAlgClosed k] in
private lemma hyperbolicTangentBasis_apply (n : Nat)
    (q : hyperbolicTangentIndex n) :
    hyperbolicTangentBasis (k := k) n q =
      match q with
      | .inl i => (Pi.single i 1, 0)
      | .inr i => (0, Pi.single i 1) := by
  cases q <;> simp [hyperbolicTangentBasis]

omit [IsAlgClosed k] in
private lemma hyperbolicTangentBasis_coord_inl (n : Nat)
    (v : HyperbolicSpace k n) (i : Fin n) :
    (hyperbolicTangentBasis (k := k) n).coord (Sum.inl i) v = v.1 i := by
  simp [hyperbolicTangentBasis]

omit [IsAlgClosed k] in
private lemma hyperbolicTangentBasis_coord_inr (n : Nat)
    (v : HyperbolicSpace k n) (i : Fin n) :
    (hyperbolicTangentBasis (k := k) n).coord (Sum.inr i) v = v.2 i := by
  simp [hyperbolicTangentBasis]

private lemma hyperbolicMatrixCoordinate_one (n : Nat)
    (p q : hyperbolicTangentIndex n) :
    hyperbolicMatrixCoordinate (k := k) n p q 1 =
      if p = q then 1 else 0 := by
  rw [hyperbolicMatrixCoordinate_apply, map_one]
  change (hyperbolicTangentBasis n).coord p (hyperbolicTangentBasis n q) = _
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply]
  simp [eq_comm]

private noncomputable def hyperbolicPointMatrix (n : Nat)
    (x : Variety.Point (evenOrthogonalOmega (k := k) n).carrierVariety) :
    Matrix (hyperbolicTangentIndex n) (hyperbolicTangentIndex n) k :=
  fun p q => hyperbolicMatrixCoordinate n p q x

private lemma hyperbolicPointMatrix_eq_toMatrix (n : Nat)
    (x : Variety.Point (evenOrthogonalOmega (k := k) n).carrierVariety) :
    hyperbolicPointMatrix n x =
      LinearMap.toMatrix (hyperbolicTangentBasis n) (hyperbolicTangentBasis n)
        ((evenOrthogonalNaturalRepresentation n).action x :
          Module.End k (HyperbolicSpace k n)) := by
  ext p q
  rw [hyperbolicPointMatrix, hyperbolicMatrixCoordinate_apply]
  rw [LinearMap.toMatrix_apply]
  rfl

private lemma hyperbolicPointMatrix_one (n : Nat) :
    hyperbolicPointMatrix (k := k) n 1 = 1 := by
  ext p q
  rw [hyperbolicPointMatrix, hyperbolicMatrixCoordinate_one,
    Matrix.one_apply]

private lemma hyperbolicPointMatrix_mul (n : Nat)
    (x y : Variety.Point (evenOrthogonalOmega (k := k) n).carrierVariety) :
    hyperbolicPointMatrix n (x * y) =
      hyperbolicPointMatrix n x * hyperbolicPointMatrix n y := by
  rw [hyperbolicPointMatrix_eq_toMatrix, hyperbolicPointMatrix_eq_toMatrix,
    hyperbolicPointMatrix_eq_toMatrix, map_mul]
  exact LinearMap.toMatrix_mul (hyperbolicTangentBasis n)
      ((evenOrthogonalNaturalRepresentation n).action x :
        Module.End k (HyperbolicSpace k n))
      ((evenOrthogonalNaturalRepresentation n).action y :
        Module.End k (HyperbolicSpace k n))

private lemma hyperbolicMatrixCoordinate_conjugation (n : Nat)
    (p q : hyperbolicTangentIndex n)
    (g : Variety.Point (evenOrthogonalOmega (k := k) n).carrierVariety)
    (z : hyperbolicTangentIndex n → kˣ)
    (hdiag : hyperbolicPointMatrix n g =
      Matrix.diagonal (fun i => (z i : k))) :
    (AlgebraicGroup.conjugationByMorphism
        (evenOrthogonalOmega (k := k) n).carrierVariety g).pullbackAlgHom
        (hyperbolicMatrixCoordinate (k := k) n p q) =
      ((z p : k) * (z q : k)⁻¹) • hyperbolicMatrixCoordinate n p q := by
  apply Variety.PolynomialFunction.ext
  intro x
  change (hyperbolicMatrixCoordinate n p q)
      ((AlgebraicGroup.conjugationByMorphism
        (evenOrthogonalOmega (k := k) n).carrierVariety g).toFun x) = _
  rw [AlgebraicGroup.conjugationByMorphism_apply]
  simp only [polynomialFunction_smul_apply]
  change hyperbolicPointMatrix n (g * x * g⁻¹) p q =
    ((z p : k) * (z q : k)⁻¹) * hyperbolicPointMatrix n x p q
  have hginv : hyperbolicPointMatrix n g⁻¹ =
      Matrix.diagonal (fun i => ((z i : k)⁻¹)) := by
    have hmul : hyperbolicPointMatrix n g * hyperbolicPointMatrix n g⁻¹ = 1 := by
      rw [← hyperbolicPointMatrix_mul]
      simp [hyperbolicPointMatrix_one]
    ext i j
    by_cases hij : i = j
    · subst j
      have he := congrFun (congrFun hmul i) i
      rw [hdiag, Matrix.mul_apply] at he
      have hsum : (z i : k) * hyperbolicPointMatrix n g⁻¹ i i = 1 := by
        simpa [Matrix.diagonal_apply, Matrix.one_apply] using he
      rw [Matrix.diagonal_apply_eq]
      exact eq_inv_of_mul_eq_one_right hsum
    · have he := congrFun (congrFun hmul i) j
      rw [hdiag, Matrix.mul_apply] at he
      have hzero : (z i : k) * hyperbolicPointMatrix n g⁻¹ i j = 0 := by
        simpa [Matrix.diagonal_apply, Matrix.one_apply, hij] using he
      have : hyperbolicPointMatrix n g⁻¹ i j = 0 :=
        (mul_eq_zero.mp hzero).resolve_left (Units.ne_zero _)
      simpa [Matrix.diagonal_apply_ne _ hij] using this
  rw [show hyperbolicPointMatrix n (g * x * g⁻¹) =
      hyperbolicPointMatrix n g * hyperbolicPointMatrix n x *
        hyperbolicPointMatrix n g⁻¹ by
      rw [hyperbolicPointMatrix_mul, hyperbolicPointMatrix_mul],
    hdiag, hginv]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

private noncomputable def hyperbolicDiagonalEntries (n : Nat)
    (d : Fin n → kˣ) : hyperbolicTangentIndex n → kˣ
  | .inl i => d i
  | .inr i => (d i)⁻¹

omit [IsAlgClosed k] in
private lemma hyperbolicDiagonalPoint_basis (n : Nat) (d : Fin n → kˣ)
    (q : hyperbolicTangentIndex n) :
    (hyperbolicDiagonalPoint n d).1 (hyperbolicTangentBasis n q) =
      (hyperbolicDiagonalEntries n d q : k) • hyperbolicTangentBasis n q := by
  cases q with
  | inl i =>
      ext p <;> by_cases hpi : p = i <;>
        simp [hyperbolicTangentBasis_apply, hyperbolicDiagonalEntries,
          hyperbolicDiagonalPoint, hyperbolicDiagonalIsometry,
          hyperbolicDiagonalLinearEquiv, Pi.single_apply, hpi]
  | inr i =>
      ext p <;> by_cases hpi : p = i <;>
        simp [hyperbolicTangentBasis_apply, hyperbolicDiagonalEntries,
          hyperbolicDiagonalPoint, hyperbolicDiagonalIsometry,
          hyperbolicDiagonalLinearEquiv, Pi.single_apply, hpi]

omit [IsAlgClosed k] in
private lemma pointCharacter_inv
    {T : Variety k} [AlgebraicGroup T]
    (chi : TorusCharacter T) (s : Variety.Point T) :
    (chi⁻¹).pointCharacter s = (chi.pointCharacter s)⁻¹ := by
  change ((dPointEquiv 1 ((chi.onPoints s)⁻¹) 0 : k)) =
    ((dPointEquiv 1 (chi.onPoints s) 0 : k))⁻¹
  have hmul := congrFun
    (dPointEquiv_mul 1 (chi.onPoints s)⁻¹ (chi.onPoints s)) 0
  rw [inv_mul_cancel, dPointEquiv_one] at hmul
  simp only [Pi.one_apply, Pi.mul_apply] at hmul
  have hu : dPointEquiv 1 ((chi.onPoints s)⁻¹) 0 =
      (dPointEquiv 1 (chi.onPoints s) 0)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    exact hmul.symm
  simpa using congrArg Units.val hu

omit [IsAlgClosed k] in
private lemma pointCharacter_mul
    {T : Variety k} [AlgebraicGroup T]
    (chi psi : TorusCharacter T) (s : Variety.Point T) :
    (chi * psi).pointCharacter s =
      chi.pointCharacter s * psi.pointCharacter s := by
  change (dPointEquiv 1 (chi.onPoints s * psi.onPoints s) 0 : k) = _
  rw [dPointEquiv_mul]
  rfl

private lemma hyperbolicDiagonalEntryCharacter_apply (n : Nat) (hn : 4 ≤ n)
    (p : hyperbolicTangentIndex n) (x : Variety.Point (dVariety k n)) :
    letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
    dPointEquiv 1
        ((hyperbolicDiagonalEntryCharacter (k := k) n hn p).onPoints
          ((evenOrthogonalDiagonalTorusIso (k := k) n hn).hom.onPoints x)) 0 =
      hyperbolicDiagonalEntries n (dPointEquiv n x) p := by
  letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
  rw [hyperbolicDiagonalEntryCharacter, evenOrthogonalDiagonalCharacter_apply]
  cases p with
  | inl i => simp [hyperbolicDiagonalEntryExponent,
      hyperbolicDiagonalEntries, Pi.single_apply]
  | inr i => simp [hyperbolicDiagonalEntryExponent,
      hyperbolicDiagonalEntries, Pi.single_apply]

private lemma hyperbolicDiagonalEntryCharacter_apply_point (n : Nat)
    (hn : 4 ≤ n) (p : hyperbolicTangentIndex n)
    (s : Variety.Point (evenOrthogonalDiagonalTorus (k := k) n hn).carrierVariety) :
    letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
    dPointEquiv 1
        ((hyperbolicDiagonalEntryCharacter (k := k) n hn p).onPoints s) 0 =
      hyperbolicDiagonalEntries n
        (dPointEquiv n (evenOrthogonalDiagonalTorusPointEquiv (k := k) n hn s)) p := by
  letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
  let x := evenOrthogonalDiagonalTorusPointEquiv (k := k) n hn s
  have hx : (evenOrthogonalDiagonalTorusIso (k := k) n hn).hom.onPoints x = s := by
    change (evenOrthogonalDiagonalTorusIso (k := k) n hn).hom.onPoints
        ((evenOrthogonalDiagonalTorusIso (k := k) n hn).inv.onPoints s) = s
    rw [(evenOrthogonalDiagonalTorusIso (k := k) n hn).inv_hom_id]
  simpa only [hx] using
    hyperbolicDiagonalEntryCharacter_apply (k := k) n hn p x

private lemma evenOrthogonalDiagonalTorus_includePoint_matrix_entries (n : Nat)
    (hn : 4 ≤ n)
    (s : Variety.Point (evenOrthogonalDiagonalTorus (k := k) n hn).carrierVariety) :
    letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
    hyperbolicPointMatrix n
        ((evenOrthogonalDiagonalTorus (k := k) n hn).includePoint s) =
      Matrix.diagonal (fun p =>
        ((hyperbolicDiagonalEntryCharacter (k := k) n hn p).pointCharacter s : k)) := by
  letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
  let x := evenOrthogonalDiagonalTorusPointEquiv (k := k) n hn s
  have hx : (evenOrthogonalDiagonalTorusIso (k := k) n hn).hom.onPoints x = s := by
    change (evenOrthogonalDiagonalTorusIso (k := k) n hn).hom.onPoints
        ((evenOrthogonalDiagonalTorusIso (k := k) n hn).inv.onPoints s) = s
    rw [(evenOrthogonalDiagonalTorusIso (k := k) n hn).inv_hom_id]
  have hi := evenOrthogonalDiagonalTorusIso_inclusion_hom (k := k) n hn x
  rw [hx] at hi
  have hlinear :
      LinearMap.GeneralLinearGroup.generalLinearEquiv k (HyperbolicSpace k n)
          ((evenOrthogonalNaturalRepresentation n).action
            ((evenOrthogonalDiagonalTorus (k := k) n hn).includePoint s)) =
        (hyperbolicDiagonalPoint n (dPointEquiv n x)).1 := by
    rw [evenOrthogonalNaturalRepresentation_action]
    rw [show (evenOrthogonalDiagonalTorus (k := k) n hn).includePoint s =
        (evenOrthogonalDiagonalTorus n hn).inclusion.onPoints s by rfl,
      hi]
    exact evenOrthogonalDiagonalMorphism_linear_points n hn x
  rw [hyperbolicPointMatrix_eq_toMatrix]
  ext p q
  rw [LinearMap.toMatrix_apply]
  change (hyperbolicTangentBasis n).repr
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv k (HyperbolicSpace k n)
        ((evenOrthogonalNaturalRepresentation n).action
          ((evenOrthogonalDiagonalTorus (k := k) n hn).includePoint s)))
            (hyperbolicTangentBasis n q)) p = _
  rw [hlinear, hyperbolicDiagonalPoint_basis]
  have hz (r : hyperbolicTangentIndex n) :
      ((hyperbolicDiagonalEntryCharacter (k := k) n hn r).pointCharacter s : k) =
        (hyperbolicDiagonalEntries n (dPointEquiv n x) r : k) := by
    exact congrArg Units.val
      (hyperbolicDiagonalEntryCharacter_apply_point (k := k) n hn r s)
  by_cases hpq : p = q
  · subst q
    simp [hz]
  · simp [hz, hpq]

private lemma exists_hyperbolicMatrixCoordinate_ne_zero (n : Nat)
    (D : IdentityPointDerivation (evenOrthogonalOmega (k := k) n).carrierVariety)
    (hD : D ≠ 0) :
    ∃ p q : hyperbolicTangentIndex n,
      D (hyperbolicMatrixCoordinate (k := k) n p q) ≠ 0 := by
  by_contra h
  push Not at h
  apply hD
  let rho := evenOrthogonalNaturalRepresentation (k := k) n
  let b := Module.finBasis k (HyperbolicSpace k n)
  let f := (evenOrthogonalOmega (k := k) n).inclusion
  let dRho := Bor1.rationalRepresentationDifferential rho b f D
  have hdRho_basis (q : hyperbolicTangentIndex n) :
      dRho (hyperbolicTangentBasis n q) = 0 := by
    apply (hyperbolicTangentBasis n).repr.injective
    ext p
    have hp := Bor1.rationalRepresentationDifferential_linearMatrixCoefficient
      rho b f D ((hyperbolicTangentBasis n).coord p)
        (hyperbolicTangentBasis n q)
    change (hyperbolicTangentBasis n).coord p
        (dRho (hyperbolicTangentBasis n q)) =
      D (hyperbolicMatrixCoordinate n p q) at hp
    rw [h p q] at hp
    simpa using hp
  have hdRho : dRho = 0 := by
    apply (hyperbolicTangentBasis n).ext
    exact hdRho_basis
  have hdf : identityTangentMorphismLinearMap f D = 0 :=
    (Bor1.identityTangentMorphismLinearMap_eq_zero_iff_rationalRepresentationDifferential_eq_zero
      rho b f D).2 hdRho
  apply identityTangentMorphismLinearMap_inclusion_injective (evenOrthogonalOmega n)
  simpa using hdf

private lemma evenOrthogonalNatural_preserves_hyperbolicForm (n : Nat)
    (hn : 4 ≤ n)
    (x : Variety.Point (evenOrthogonalOmega (k := k) n).carrierVariety)
    (v : HyperbolicSpace k n) :
    hyperbolicForm n
        (((evenOrthogonalNaturalRepresentation n).action x :
          Module.End k (HyperbolicSpace k n)) v) =
      hyperbolicForm n v := by
  let omegaPoints := evenSpinActionImageClosedSubgroupPoints
    (hyperbolicForm (k := k) n) (standardHyperbolicSplit n) (by simpa using hn)
  have hlinear := evenSpinActionImageClosedSubgroup_linear_points
    (hyperbolicForm (k := k) n) (standardHyperbolicSplit n)
      (by simpa using hn) x
  rw [← evenOrthogonalNaturalRepresentation_action] at hlinear
  have hv := congrArg (fun f : HyperbolicSpace k n ≃ₗ[k] HyperbolicSpace k n => f v)
    hlinear
  change hyperbolicForm n
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv k (HyperbolicSpace k n)
        ((evenOrthogonalNaturalRepresentation n).action x)) v) = _
  rw [hv]
  exact (mem_quadraticIsometrySubgroup (hyperbolicForm (k := k) n)
    (omegaPoints x).1.1).1 (omegaPoints x).1.2 v

private lemma hyperbolicIsotropicColumn_relation (n : Nat) (hn : 4 ≤ n)
    (q : hyperbolicTangentIndex n) :
    (∑ i : Fin n,
      hyperbolicMatrixCoordinate (k := k) n (Sum.inl i) q *
        hyperbolicMatrixCoordinate n (Sum.inr i) q) = 0 := by
  apply Variety.PolynomialFunction.ext
  intro x
  change polynomialFunctionEvalAddHom (evenOrthogonalOmega n).carrierVariety x
      (∑ i : Fin n,
        hyperbolicMatrixCoordinate n (Sum.inl i) q *
          hyperbolicMatrixCoordinate n (Sum.inr i) q) = 0
  rw [map_sum]
  simp only [polynomialFunctionEvalAddHom_apply, polynomialFunction_mul_apply]
  simp_rw [hyperbolicMatrixCoordinate_apply]
  simp only [hyperbolicTangentBasis_coord_inl,
    hyperbolicTangentBasis_coord_inr]
  rw [← hyperbolicForm_apply,
    evenOrthogonalNatural_preserves_hyperbolicForm n hn]
  cases q <;> simp [hyperbolicTangentBasis_apply, hyperbolicForm_apply]

private lemma hyperbolicOppositeCoordinate_upper_zero (n : Nat) (hn : 4 ≤ n)
    (D : IdentityPointDerivation (evenOrthogonalOmega (k := k) n).carrierVariety)
    (i : Fin n) :
    D (hyperbolicMatrixCoordinate n (Sum.inr i) (Sum.inl i)) = 0 := by
  have h := congrArg D (hyperbolicIsotropicColumn_relation (k := k) n hn (Sum.inl i))
  rw [map_zero, map_sum] at h
  simp only [D.leibniz] at h
  change (∑ x : Fin n, (
    hyperbolicMatrixCoordinate n (Sum.inl x) (Sum.inl i) 1 *
        D (hyperbolicMatrixCoordinate n (Sum.inr x) (Sum.inl i)) +
      hyperbolicMatrixCoordinate n (Sum.inr x) (Sum.inl i) 1 *
        D (hyperbolicMatrixCoordinate n (Sum.inl x) (Sum.inl i)))) = 0 at h
  simp only [hyperbolicMatrixCoordinate_one] at h
  simpa using h

private lemma hyperbolicOppositeCoordinate_lower_zero (n : Nat) (hn : 4 ≤ n)
    (D : IdentityPointDerivation (evenOrthogonalOmega (k := k) n).carrierVariety)
    (i : Fin n) :
    D (hyperbolicMatrixCoordinate n (Sum.inl i) (Sum.inr i)) = 0 := by
  have h := congrArg D (hyperbolicIsotropicColumn_relation (k := k) n hn (Sum.inr i))
  rw [map_zero, map_sum] at h
  simp only [D.leibniz] at h
  change (∑ x : Fin n, (
    hyperbolicMatrixCoordinate n (Sum.inl x) (Sum.inr i) 1 *
        D (hyperbolicMatrixCoordinate n (Sum.inr x) (Sum.inr i)) +
      hyperbolicMatrixCoordinate n (Sum.inr x) (Sum.inr i) 1 *
        D (hyperbolicMatrixCoordinate n (Sum.inl x) (Sum.inr i)))) = 0 at h
  simp only [hyperbolicMatrixCoordinate_one] at h
  simpa using h

/-- Every nonzero identity-tangent weight for the exact split even-Omega carrier
under its standard diagonal torus is one of the explicit type-D root weights. -/
public theorem evenOrthogonalTangentWeight_eq_rootWeight (n : Nat) (hn : 4 ≤ n)
    {chi : TorusWeight (evenOrthogonalDiagonalTorus (k := k) n hn)}
    {D : IdentityPointDerivation
      (evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
        (standardHyperbolicSplit n)).carrierVariety}
    (hchi : chi ≠ 1)
    (hD : IsWeightVector
      (identityTangentRepresentation
        (evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
          (standardHyperbolicSplit n)).carrierVariety)
      (evenOrthogonalDiagonalTorus (k := k) n hn) D chi⁻¹) :
    ∃ r : TypeDRootIndex n,
      chi = evenOrthogonalRootWeight (k := k) n hn r := by
  letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
  obtain ⟨p, q, hpqD⟩ := exists_hyperbolicMatrixCoordinate_ne_zero n D hD.1
  have hcharInv : chi⁻¹ =
      hyperbolicDiagonalEntryCharacter (k := k) n hn p *
        (hyperbolicDiagonalEntryCharacter (k := k) n hn q)⁻¹ := by
    apply TorusCharacter.pointCharacter_injective
    ext s
    let z : hyperbolicTangentIndex n → kˣ := fun i =>
      dPointEquiv 1
        ((hyperbolicDiagonalEntryCharacter (k := k) n hn i).onPoints s) 0
    have hdiag : hyperbolicPointMatrix n
        ((evenOrthogonalDiagonalTorus (k := k) n hn).includePoint s) =
        Matrix.diagonal (fun i => (z i : k)) := by
      rw [evenOrthogonalDiagonalTorus_includePoint_matrix_entries]
      congr 1
    have heig := congrArg
      (fun E : IdentityPointDerivation (evenOrthogonalOmega (k := k) n).carrierVariety =>
        E (hyperbolicMatrixCoordinate (k := k) n p q)) (hD.2 s)
    rw [identityTangentRepresentation_action_apply,
      hyperbolicMatrixCoordinate_conjugation n p q _ z hdiag] at heig
    change D.toLinearMap (((z p : k) * (z q : k)⁻¹) •
        hyperbolicMatrixCoordinate n p q) =
      (chi⁻¹).pointCharacter s * D (hyperbolicMatrixCoordinate n p q) at heig
    rw [D.toLinearMap.map_smul] at heig
    change ((z p : k) * (z q : k)⁻¹) * D (hyperbolicMatrixCoordinate n p q) =
      (chi⁻¹).pointCharacter s * D (hyperbolicMatrixCoordinate n p q) at heig
    have hpoint : (chi⁻¹).pointCharacter s = (z p : k) * (z q : k)⁻¹ := by
      apply mul_right_cancel₀ hpqD
      exact heig.symm
    rw [pointCharacter_mul,
      pointCharacter_inv (hyperbolicDiagonalEntryCharacter (k := k) n hn q) s]
    exact hpoint
  have hpq : p ≠ q := by
    intro hpq
    subst q
    have hone : chi⁻¹ = 1 := by simpa using hcharInv
    apply hchi
    simpa using congrArg Inv.inv hone
  have hopposite (i : Fin n) :
      (p, q) ≠ (Sum.inl i, Sum.inr i) ∧
        (p, q) ≠ (Sum.inr i, Sum.inl i) := by
    constructor
    · intro hpqi
      have hp : p = Sum.inl i := congrArg Prod.fst hpqi
      have hq : q = Sum.inr i := congrArg Prod.snd hpqi
      subst p
      subst q
      exact hpqD (hyperbolicOppositeCoordinate_lower_zero n hn D i)
    · intro hpqi
      have hp : p = Sum.inr i := congrArg Prod.fst hpqi
      have hq : q = Sum.inl i := congrArg Prod.snd hpqi
      subst p
      subst q
      exact hpqD (hyperbolicOppositeCoordinate_upper_zero n hn D i)
  obtain ⟨r, hr⟩ := exists_evenOrthogonalRootWeight_inv_eq_entry_quotient
    (k := k) n hn p q hpq hopposite
  refine ⟨r, ?_⟩
  apply inv_injective
  exact hcharInv.trans hr.symm

end Theory.AlgebraicGroup
