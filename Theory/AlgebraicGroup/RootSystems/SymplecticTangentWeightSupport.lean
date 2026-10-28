module

public import Mathlib.GroupTheory.Perm.Support
public import Theory.AlgebraicGroup.Bor1.DerivationDeterminant
public import Theory.AlgebraicGroup.RootSubgroups.Tangent
public import Theory.AlgebraicGroup.RootSystems.SymplecticRootSubgroups
public import Theory.AlgebraicGroup.Tori.Character.Duality

/-!
# Diagonal symplectic tangent weights

This module classifies the nonzero weights in the identity-tangent conjugation
representation of the standard symplectic carrier under its diagonal torus.
Every nontrivial weight is one of the explicit type-C characters indexed by
`TypeCRootIndex m`.

The proof detects a nonzero matrix coordinate of a nonzero tangent derivation.
The determinant-inverse relation for the general-linear carrier shows that the
matrix coordinates detect every tangent, while diagonal conjugation scales the
`(p, q)` coordinate by the quotient of its two diagonal entries.  The four
possible signed-index configurations identify every nontrivial quotient with a
short or long type-C root character.  The exported theorem is the ambient
support input for symplectic torus-root exhaustiveness via
`oneParameterTangent_isWeightVector`.

The matrix model follows the standard block-matrix realization of the
symplectic group used in GLS, Part I, Chapter A, Sections 1.9-1.10.
-/

open scoped BigOperators

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

open StandardRootSystem

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

public section

noncomputable section

private noncomputable def symplecticDiagonalEntryExponent (m : ℕ) :
    symplecticStandardIndex m → Fin m → ℤ
  | .inl i => Pi.single i 1
  | .inr i => Pi.single i (-1)

private noncomputable def symplecticDiagonalEntryCharacter (m : ℕ)
    (p : symplecticStandardIndex m) :
    letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
    TorusWeight (symplecticDiagonalTorus (k := k) m) := by
  letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
  exact symplecticDiagonalCharacter (k := k) m
    (symplecticDiagonalEntryExponent m p)

private noncomputable def symplecticDiagonalCharacterAddEquiv (m : ℕ) :
    letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
    (Fin m → ℤ) ≃+ Additive (TorusWeight (symplecticDiagonalTorus (k := k) m)) := by
  letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
  exact (dLaurentCharacterAddEquiv (k := k) m).trans
    (symplecticDiagonalCharacterTransport (k := k) m).toAdditive

private lemma symplecticDiagonalCharacterAddEquiv_apply (m : ℕ)
    (z : Fin m → ℤ) :
    letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
    symplecticDiagonalCharacterAddEquiv (k := k) m z =
      Additive.ofMul (symplecticDiagonalCharacter (k := k) m z) := by
  rfl

private lemma symplecticRootExponent_eq_entry_sub (m : ℕ)
    (r : TypeCRootIndex m) :
    symplecticRootExponent m r =
      symplecticDiagonalEntryExponent m (symplecticRootCoordinate m r).2 -
        symplecticDiagonalEntryExponent m (symplecticRootCoordinate m r).1 := by
  funext q
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩ | ⟨i, b⟩
  · rcases s with ⟨s, hs⟩
    rcases t with ⟨t, ht⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
      by_cases hqi : q = i <;> by_cases hqj : q = j <;>
        norm_num [symplecticRootExponent, symplecticRootCoordinate,
          symplecticDiagonalEntryExponent, sub_eq_add_neg,
          Pi.single_apply, hqi, hqj, hij.ne, hij.ne', add_comm]
  · cases b <;> by_cases hqi : q = i <;>
      norm_num [symplecticRootExponent, symplecticRootCoordinate,
        symplecticDiagonalEntryExponent, sub_eq_add_neg,
        Pi.single_apply, hqi]

private lemma symplecticRootWeight_eq_entryCharacters (m : ℕ)
    (r : TypeCRootIndex m) :
    letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
    symplecticRootWeight (k := k) m r =
      symplecticDiagonalEntryCharacter (k := k) m (symplecticRootCoordinate m r).2 *
        (symplecticDiagonalEntryCharacter (k := k) m
          (symplecticRootCoordinate m r).1)⁻¹ := by
  letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
  rw [symplecticRootWeight, symplecticRootExponent_eq_entry_sub]
  apply Additive.ofMul.injective
  simp [symplecticDiagonalEntryCharacter,
    ← symplecticDiagonalCharacterAddEquiv_apply, sub_eq_add_neg]

private lemma symplecticDiagonalEntryCharacter_opposite (m : ℕ) (i : Fin m) :
    letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
    symplecticDiagonalEntryCharacter (k := k) m (Sum.inr i) =
      (symplecticDiagonalEntryCharacter (k := k) m (Sum.inl i))⁻¹ := by
  letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
  apply Additive.ofMul.injective
  change symplecticDiagonalCharacterAddEquiv (k := k) m
      (symplecticDiagonalEntryExponent m (Sum.inr i)) =
    -(symplecticDiagonalCharacterAddEquiv (k := k) m
      (symplecticDiagonalEntryExponent m (Sum.inl i)))
  rw [← map_neg]
  congr 1
  funext q
  by_cases hqi : q = i <;>
    simp [symplecticDiagonalEntryExponent, hqi]

private lemma exists_rootWeight_inv_eq_entry_quotient (m : ℕ)
    (p q : symplecticStandardIndex m) (hpq : p ≠ q) :
    letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
    ∃ r : TypeCRootIndex m,
      (symplecticRootWeight (k := k) m r)⁻¹ =
        symplecticDiagonalEntryCharacter (k := k) m p *
          (symplecticDiagonalEntryCharacter (k := k) m q)⁻¹ := by
  letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
  let pos : ({-1, 1} : Set ℝ) := ⟨1, by simp⟩
  let neg : ({-1, 1} : Set ℝ) := ⟨-1, by simp⟩
  rcases p with i | i <;> rcases q with j | j
  · have hij : i ≠ j := fun h => hpq (congrArg Sum.inl h)
    rcases lt_or_gt_of_ne hij with hij | hji
    · refine ⟨Sum.inl (⟨⟨(i, j), hij⟩, pos, neg⟩), ?_⟩
      have hcoord : symplecticRootCoordinate m
          (Sum.inl (⟨⟨(i, j), hij⟩, pos, neg⟩)) = (Sum.inl i, Sum.inl j) := by
        norm_num [symplecticRootCoordinate, pos, neg]
      rw [symplecticRootWeight_eq_entryCharacters, hcoord]
      simp only [mul_inv_rev, inv_inv]
    · refine ⟨Sum.inl (⟨⟨(j, i), hji⟩, neg, pos⟩), ?_⟩
      have hcoord : symplecticRootCoordinate m
          (Sum.inl (⟨⟨(j, i), hji⟩, neg, pos⟩)) = (Sum.inl i, Sum.inl j) := by
        norm_num [symplecticRootCoordinate, pos, neg]
      rw [symplecticRootWeight_eq_entryCharacters, hcoord]
      simp only [mul_inv_rev, inv_inv]
  · by_cases hij : i = j
    · subst j
      refine ⟨Sum.inr (i, false), ?_⟩
      rw [symplecticRootWeight_eq_entryCharacters]
      simp only [symplecticRootCoordinate, mul_inv_rev, inv_inv]
    · rcases lt_or_gt_of_ne hij with hij | hji
      · refine ⟨Sum.inl (⟨⟨(i, j), hij⟩, pos, pos⟩), ?_⟩
        have hcoord : symplecticRootCoordinate m
            (Sum.inl (⟨⟨(i, j), hij⟩, pos, pos⟩)) = (Sum.inl i, Sum.inr j) := by
          norm_num [symplecticRootCoordinate, pos]
        rw [symplecticRootWeight_eq_entryCharacters, hcoord]
        simp only [mul_inv_rev, inv_inv]
      · refine ⟨Sum.inl (⟨⟨(j, i), hji⟩, pos, pos⟩), ?_⟩
        have hcoord : symplecticRootCoordinate m
            (Sum.inl (⟨⟨(j, i), hji⟩, pos, pos⟩)) = (Sum.inl j, Sum.inr i) := by
          norm_num [symplecticRootCoordinate, pos]
        rw [symplecticRootWeight_eq_entryCharacters, hcoord]
        rw [symplecticDiagonalEntryCharacter_opposite]
        rw [symplecticDiagonalEntryCharacter_opposite]
        simp only [mul_inv_rev, inv_inv]
        ac_rfl
  · by_cases hij : i = j
    · subst j
      refine ⟨Sum.inr (i, true), ?_⟩
      rw [symplecticRootWeight_eq_entryCharacters]
      simp only [symplecticRootCoordinate, mul_inv_rev, inv_inv]
    · rcases lt_or_gt_of_ne hij with hij | hji
      · refine ⟨Sum.inl (⟨⟨(i, j), hij⟩, neg, neg⟩), ?_⟩
        have hcoord : symplecticRootCoordinate m
            (Sum.inl (⟨⟨(i, j), hij⟩, neg, neg⟩)) = (Sum.inr i, Sum.inl j) := by
          norm_num [symplecticRootCoordinate, neg]
        rw [symplecticRootWeight_eq_entryCharacters, hcoord]
        simp only [mul_inv_rev, inv_inv]
      · refine ⟨Sum.inl (⟨⟨(j, i), hji⟩, neg, neg⟩), ?_⟩
        have hcoord : symplecticRootCoordinate m
            (Sum.inl (⟨⟨(j, i), hji⟩, neg, neg⟩)) = (Sum.inr j, Sum.inl i) := by
          norm_num [symplecticRootCoordinate, neg]
        rw [symplecticRootWeight_eq_entryCharacters, hcoord]
        rw [symplecticDiagonalEntryCharacter_opposite]
        rw [symplecticDiagonalEntryCharacter_opposite]
        simp only [mul_inv_rev, inv_inv]
        ac_rfl
  · have hij : i ≠ j := fun h => hpq (congrArg Sum.inr h)
    rcases lt_or_gt_of_ne hij with hij | hji
    · refine ⟨Sum.inl (⟨⟨(i, j), hij⟩, neg, pos⟩), ?_⟩
      have hcoord : symplecticRootCoordinate m
          (Sum.inl (⟨⟨(i, j), hij⟩, neg, pos⟩)) = (Sum.inl j, Sum.inl i) := by
        norm_num [symplecticRootCoordinate, pos, neg]
      rw [symplecticRootWeight_eq_entryCharacters, hcoord,
        symplecticDiagonalEntryCharacter_opposite,
        symplecticDiagonalEntryCharacter_opposite]
      simp only [mul_inv_rev, inv_inv]
      ac_rfl
    · refine ⟨Sum.inl (⟨⟨(j, i), hji⟩, pos, neg⟩), ?_⟩
      have hcoord : symplecticRootCoordinate m
          (Sum.inl (⟨⟨(j, i), hji⟩, pos, neg⟩)) = (Sum.inl j, Sum.inl i) := by
        norm_num [symplecticRootCoordinate, pos, neg]
      rw [symplecticRootWeight_eq_entryCharacters, hcoord,
        symplecticDiagonalEntryCharacter_opposite,
        symplecticDiagonalEntryCharacter_opposite]
      simp only [mul_inv_rev, inv_inv]
      ac_rfl

private def symplecticMatrixCoordinateIndex (m : ℕ)
    (p q : symplecticStandardIndex m) :
    (standardSymplecticClosedSubgroup (k := k) m).carrierVariety.Coordinates :=
  Sum.inl
    (symplecticStandardIndexEquiv (k := k) m p,
      symplecticStandardIndexEquiv (k := k) m q)

private def symplecticMatrixCoordinate (m : ℕ)
    (p q : symplecticStandardIndex m) :
    Variety.PolynomialFunction
      (standardSymplecticClosedSubgroup (k := k) m).carrierVariety :=
  Variety.PolynomialFunction.ofPolynomial _
    (MvPolynomial.X (symplecticMatrixCoordinateIndex (k := k) m p q))

private lemma symplecticMatrixCoordinate_apply_include (m : ℕ)
    (p q : symplecticStandardIndex m)
    (x : Variety.Point (standardSymplecticClosedSubgroup (k := k) m).carrierVariety) :
    symplecticMatrixCoordinate m p q x =
      glMatrixOfPoint (Module.finrank k (symplecticStandardSpace (k := k) m))
        ((standardSymplecticClosedSubgroup (k := k) m).inclusion.onPoints x)
        (symplecticStandardIndexEquiv (k := k) m p)
        (symplecticStandardIndexEquiv (k := k) m q) := by
  dsimp only [symplecticMatrixCoordinate,
    Variety.PolynomialFunction.ofPolynomial, Variety.PolynomialFunction.toFun]
  rw [evalPolynomial_X]
  rfl

private lemma symplecticMatrixCoordinate_apply (m : ℕ)
    (p q : symplecticStandardIndex m)
    (x : Variety.Point (standardSymplecticClosedSubgroup (k := k) m).carrierVariety) :
    symplecticMatrixCoordinate m p q x = symplecticClosedPointMatrix m x p q := by
  dsimp only [symplecticMatrixCoordinate,
    Variety.PolynomialFunction.ofPolynomial, Variety.PolynomialFunction.toFun]
  rw [evalPolynomial_X]
  exact (symplecticClosedPointMatrix_entry (k := k) m x p q).symm

private lemma symplecticClosedPointMatrix_one (m : ℕ) :
    symplecticClosedPointMatrix (k := k) m 1 = 1 := by
  have hpoint : symplecticDiagonalPoint m (1 : Variety.Point (dVariety k m)) = 1 :=
    (symplecticDiagonalMorphism (k := k) m).map_one
  calc
    symplecticClosedPointMatrix m 1 =
        symplecticClosedPointMatrix m (symplecticDiagonalPoint m 1) := by rw [hpoint]
    _ = symplecticDiagonalMatrix m 1 :=
      symplecticClosedPointMatrix_diagonalPoint m 1
    _ = 1 := symplecticDiagonalMatrix_one m

private lemma symplecticMatrixCoordinate_one (m : ℕ)
    (p q : symplecticStandardIndex m) :
    symplecticMatrixCoordinate (k := k) m p q 1 = if p = q then 1 else 0 := by
  rw [symplecticMatrixCoordinate_apply]
  rw [symplecticClosedPointMatrix_one, Matrix.one_apply]

private lemma symplecticMatrixCoordinate_conjugation (m : ℕ)
    (p q : symplecticStandardIndex m)
    (g : Variety.Point (standardSymplecticClosedSubgroup (k := k) m).carrierVariety)
    (z : symplecticStandardIndex m → kˣ)
    (hdiag : symplecticClosedPointMatrix m g =
      Matrix.diagonal (fun i => (z i : k))) :
    (AlgebraicGroup.conjugationByMorphism
        (standardSymplecticClosedSubgroup (k := k) m).carrierVariety g).pullbackAlgHom
        (symplecticMatrixCoordinate (k := k) m p q) =
      ((z p : k) * (z q : k)⁻¹) • symplecticMatrixCoordinate m p q := by
  apply Variety.PolynomialFunction.ext
  intro x
  change (symplecticMatrixCoordinate m p q)
      ((AlgebraicGroup.conjugationByMorphism
        (standardSymplecticClosedSubgroup (k := k) m).carrierVariety g).toFun x) = _
  rw [AlgebraicGroup.conjugationByMorphism_apply,
    symplecticMatrixCoordinate_apply]
  simp only [polynomialFunction_smul_apply, symplecticMatrixCoordinate_apply]
  have hginv : symplecticClosedPointMatrix m g⁻¹ =
      Matrix.diagonal (fun i => ((z i : k)⁻¹)) := by
    have hmul : symplecticClosedPointMatrix m g *
        symplecticClosedPointMatrix m g⁻¹ = 1 := by
      rw [← symplecticClosedPointMatrix_mul]
      simp [symplecticClosedPointMatrix_one]
    ext i j
    by_cases hij : i = j
    · subst j
      have he := congrFun (congrFun hmul i) i
      rw [hdiag, Matrix.mul_apply] at he
      have hsum : (z i : k) * symplecticClosedPointMatrix m g⁻¹ i i = 1 := by
        simpa [Matrix.diagonal_apply, Matrix.one_apply] using he
      rw [Matrix.diagonal_apply_eq]
      exact eq_inv_of_mul_eq_one_right hsum
    · have he := congrFun (congrFun hmul i) j
      rw [hdiag, Matrix.mul_apply] at he
      have hzero : (z i : k) * symplecticClosedPointMatrix m g⁻¹ i j = 0 := by
        simpa [Matrix.diagonal_apply, Matrix.one_apply, hij] using he
      have : symplecticClosedPointMatrix m g⁻¹ i j = 0 :=
        (mul_eq_zero.mp hzero).resolve_left (Units.ne_zero _)
      simpa [Matrix.diagonal_apply_ne _ hij] using this
  rw [show symplecticClosedPointMatrix m (g * x * g⁻¹) =
      symplecticClosedPointMatrix m g * symplecticClosedPointMatrix m x *
        symplecticClosedPointMatrix m g⁻¹ by
      rw [symplecticClosedPointMatrix_mul, symplecticClosedPointMatrix_mul],
    hdiag, hginv]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

private def symplecticScalarCoordinateIndex (m : ℕ) :
    (standardSymplecticClosedSubgroup (k := k) m).carrierVariety.Coordinates :=
  Sum.inr PUnit.unit

private def symplecticScalarCoordinate (m : ℕ) :
    Variety.PolynomialFunction
      (standardSymplecticClosedSubgroup (k := k) m).carrierVariety :=
  Variety.PolynomialFunction.ofPolynomial _
    (MvPolynomial.X (symplecticScalarCoordinateIndex (k := k) m))

private lemma symplecticScalarCoordinate_apply (m : ℕ)
    (x : Variety.Point (standardSymplecticClosedSubgroup (k := k) m).carrierVariety) :
    symplecticScalarCoordinate (k := k) m x =
      glScalarOfPoint (Module.finrank k (symplecticStandardSpace (k := k) m))
        ((standardSymplecticClosedSubgroup (k := k) m).inclusion.onPoints x) := by
  dsimp only [symplecticScalarCoordinate,
    Variety.PolynomialFunction.ofPolynomial, Variety.PolynomialFunction.toFun]
  rw [evalPolynomial_X]
  rfl

private lemma exists_symplecticMatrixCoordinate_ne_zero (m : ℕ)
    (D : IdentityPointDerivation
      (standardSymplecticClosedSubgroup (k := k) m).carrierVariety)
    (hD : D ≠ 0) :
    ∃ p q : symplecticStandardIndex m,
      D (symplecticMatrixCoordinate (k := k) m p q) ≠ 0 := by
  by_contra h
  push Not at h
  apply hD
  let e := symplecticStandardIndexEquiv (k := k) m
  let M : Matrix (Fin (Module.finrank k (symplecticStandardSpace (k := k) m)))
      (Fin (Module.finrank k (symplecticStandardSpace (k := k) m)))
      (Variety.PolynomialFunction
        (standardSymplecticClosedSubgroup (k := k) m).carrierVariety) :=
    fun i j => symplecticMatrixCoordinate m (e.symm i) (e.symm j)
  have hMone (i j : Fin (Module.finrank k (symplecticStandardSpace (k := k) m))) :
      M i j 1 = if i = j then 1 else 0 := by
    rw [symplecticMatrixCoordinate_one]
    by_cases hij : i = j
    · subst j
      simp
    · have heij : e.symm i ≠ e.symm j := fun he => hij (e.symm.injective he)
      simp [hij, heij]
  have hdet : D M.det = 0 := by
    rw [Theory.AlgebraicGroup.Bor1.identityPointDerivation_det_at_identity D M hMone]
    apply Finset.sum_eq_zero
    intro i hi
    exact h (e.symm i) (e.symm i)
  have hrelation : M.det * symplecticScalarCoordinate (k := k) m = 1 := by
    apply Variety.PolynomialFunction.ext
    intro x
    change M.det x * symplecticScalarCoordinate m x = 1
    let ev := polynomialFunctionPointAlgHom
      (standardSymplecticClosedSubgroup (k := k) m).carrierVariety x
    have hMx : ev.mapMatrix M =
        glMatrixOfPoint (Module.finrank k (symplecticStandardSpace (k := k) m))
          ((standardSymplecticClosedSubgroup (k := k) m).inclusion.onPoints x) := by
      ext i j
      change symplecticMatrixCoordinate m (e.symm i) (e.symm j) x = _
      rw [symplecticMatrixCoordinate_apply_include]
      simp [e]
    rw [show M.det x = (ev.mapMatrix M).det by
      change ev M.det = _
      rw [AlgHom.map_det], hMx]
    rw [symplecticScalarCoordinate_apply]
    exact glPoint_det_mul_scalar _
      ((standardSymplecticClosedSubgroup (k := k) m).inclusion.onPoints x)
  have hrel := congrArg D hrelation
  rw [D.leibniz, D.map_one_eq_zero, hdet] at hrel
  have hMdet : M.det 1 = 1 := by
    let ev := polynomialFunctionPointAlgHom
      (standardSymplecticClosedSubgroup (k := k) m).carrierVariety 1
    change ev M.det = 1
    rw [AlgHom.map_det]
    change Matrix.det (fun i j => M i j 1) = 1
    rw [show (fun i j => M i j 1) =
        (1 : Matrix (Fin (Module.finrank k (symplecticStandardSpace (k := k) m)))
          (Fin (Module.finrank k (symplecticStandardSpace (k := k) m))) k) by
      ext i j
      exact hMone i j]
    exact Matrix.det_one
  have hscalar : D (symplecticScalarCoordinate (k := k) m) = 0 := by
    change M.det 1 * D (symplecticScalarCoordinate m) +
      symplecticScalarCoordinate m 1 * 0 = 0 at hrel
    simpa [hMdet, symplecticScalarCoordinate] using hrel
  apply Derivation.ext_of_adjoin_eq_top
    (Set.range fun i :
      (standardSymplecticClosedSubgroup (k := k) m).carrierVariety.Coordinates =>
      Variety.PolynomialFunction.ofPolynomial _ (MvPolynomial.X i))
  · rw [Algebra.adjoin_range_eq_range_aeval]
    apply (AlgHom.range_eq_top _).2
    intro f
    obtain ⟨p, hp⟩ := f.representedBy
    refine ⟨p, ?_⟩
    apply Variety.PolynomialFunction.ext
    intro x
    rw [hp]
    have haeval :
        MvPolynomial.aeval (fun i :
          (standardSymplecticClosedSubgroup (k := k) m).carrierVariety.Coordinates =>
          Variety.PolynomialFunction.ofPolynomial _ (MvPolynomial.X i)) =
          evaluationAlgHom
            (standardSymplecticClosedSubgroup (k := k) m).carrierVariety := by
      apply MvPolynomial.algHom_ext
      intro i
      apply Variety.PolynomialFunction.ext
      intro y
      rw [MvPolynomial.aeval_X]
      rfl
    rw [haeval]
    rfl
  · rintro _ ⟨c, rfl⟩
    cases c with
    | inl ij =>
        rcases ij with ⟨i, j⟩
        have hc := h (e.symm i) (e.symm j)
        change D (Variety.PolynomialFunction.ofPolynomial _
          (MvPolynomial.X (symplecticMatrixCoordinateIndex m (e.symm i) (e.symm j)))) = 0 at hc
        rw [show symplecticMatrixCoordinateIndex (k := k) m (e.symm i) (e.symm j) =
            (show (standardSymplecticClosedSubgroup (k := k) m).carrierVariety.Coordinates
              from Sum.inl (i, j)) by
          change Sum.inl (e (e.symm i), e (e.symm j)) = Sum.inl (i, j)
          rw [e.apply_symm_apply, e.apply_symm_apply]] at hc
        exact hc
    | inr q =>
        obtain rfl := Subsingleton.elim q PUnit.unit
        simpa [symplecticScalarCoordinate, symplecticScalarCoordinateIndex] using hscalar

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

private lemma symplecticDiagonalEntryCharacter_apply (m : ℕ)
    (p : symplecticStandardIndex m) (x : Variety.Point (dVariety k m)) :
    letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
    dPointEquiv 1
        ((symplecticDiagonalEntryCharacter (k := k) m p).onPoints
          ((symplecticDiagonalTorusIso (k := k) m).hom.onPoints x)) 0 =
      symplecticDiagonalEntries (k := k) m x p := by
  letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
  rw [symplecticDiagonalEntryCharacter, symplecticDiagonalCharacter_apply]
  cases p with
  | inl i => simp [symplecticDiagonalEntryExponent,
      symplecticDiagonalEntries, Pi.single_apply]
  | inr i => simp [symplecticDiagonalEntryExponent,
      symplecticDiagonalEntries, Pi.single_apply]

private lemma symplecticDiagonalEntryCharacter_apply_point (m : ℕ)
    (p : symplecticStandardIndex m)
    (s : Variety.Point (symplecticDiagonalTorus (k := k) m).carrierVariety) :
    letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
    dPointEquiv 1
        ((symplecticDiagonalEntryCharacter (k := k) m p).onPoints s) 0 =
      symplecticDiagonalEntries m
        (symplecticDiagonalTorusPointEquiv (k := k) m s) p := by
  letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
  let x := symplecticDiagonalTorusPointEquiv (k := k) m s
  have hx : (symplecticDiagonalTorusIso (k := k) m).hom.onPoints x = s := by
    change (symplecticDiagonalTorusIso (k := k) m).hom.onPoints
        ((symplecticDiagonalTorusIso (k := k) m).inv.onPoints s) = s
    rw [(symplecticDiagonalTorusIso (k := k) m).inv_hom_id]
  simpa only [hx] using symplecticDiagonalEntryCharacter_apply (k := k) m p x

private lemma symplecticDiagonalTorus_includePoint_matrix (m : ℕ)
    (s : Variety.Point (symplecticDiagonalTorus (k := k) m).carrierVariety) :
    letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
    symplecticClosedPointMatrix m
        ((symplecticDiagonalTorus (k := k) m).includePoint s) =
      symplecticDiagonalMatrix m
        (symplecticDiagonalTorusPointEquiv (k := k) m s) := by
  letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
  let x := symplecticDiagonalTorusPointEquiv (k := k) m s
  have hx : (symplecticDiagonalTorusIso (k := k) m).hom.onPoints x = s := by
    change (symplecticDiagonalTorusIso (k := k) m).hom.onPoints
        ((symplecticDiagonalTorusIso (k := k) m).inv.onPoints s) = s
    rw [(symplecticDiagonalTorusIso (k := k) m).inv_hom_id]
  have hi := symplecticDiagonalTorusIso_inclusion_hom (k := k) m x
  rw [hx] at hi
  rw [show (symplecticDiagonalTorus (k := k) m).includePoint s =
      (symplecticDiagonalTorus m).inclusion.onPoints s by rfl]
  rw [hi, symplecticDiagonalMorphism_apply,
    symplecticClosedPointMatrix_diagonalPoint]

private lemma symplecticDiagonalTorus_includePoint_matrix_entries (m : ℕ)
    (s : Variety.Point (symplecticDiagonalTorus (k := k) m).carrierVariety) :
    letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
    symplecticClosedPointMatrix m
        ((symplecticDiagonalTorus (k := k) m).includePoint s) =
      Matrix.diagonal (fun p =>
        ((symplecticDiagonalEntryCharacter (k := k) m p).pointCharacter s : k)) := by
  letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
  rw [symplecticDiagonalTorus_includePoint_matrix,
    symplecticDiagonalMatrix]
  congr 1
  funext p
  rw [symplecticDiagonalValue_point]
  exact congrArg Units.val
    (symplecticDiagonalEntryCharacter_apply_point (k := k) m p s).symm

/-- A nonzero identity tangent of nontrivial inverse weight for the standard
symplectic diagonal torus has a type-C root character. -/
public theorem symplecticTangentWeight_eq_rootWeight (m : ℕ)
    {chi : TorusWeight (symplecticDiagonalTorus (k := k) m)}
    {D : IdentityPointDerivation
      (standardSymplecticClosedSubgroup (k := k) m).carrierVariety}
    (hchi : chi ≠ 1)
    (hD : IsWeightVector
      (identityTangentRepresentation
        (standardSymplecticClosedSubgroup (k := k) m).carrierVariety)
      (symplecticDiagonalTorus (k := k) m) D chi⁻¹) :
    ∃ r : TypeCRootIndex m, chi = symplecticRootWeight (k := k) m r := by
  letI := (symplecticDiagonalTorus (k := k) m).carrierAlgebraicGroup
  obtain ⟨p, q, hpqD⟩ := exists_symplecticMatrixCoordinate_ne_zero m D hD.1
  have hcharInv : chi⁻¹ =
      symplecticDiagonalEntryCharacter (k := k) m p *
        (symplecticDiagonalEntryCharacter (k := k) m q)⁻¹ := by
    apply TorusCharacter.pointCharacter_injective
    ext s
    let z : symplecticStandardIndex m → kˣ := fun i =>
      dPointEquiv 1
        ((symplecticDiagonalEntryCharacter (k := k) m i).onPoints s) 0
    have hdiag : symplecticClosedPointMatrix m
        ((symplecticDiagonalTorus (k := k) m).includePoint s) =
        Matrix.diagonal (fun i => (z i : k)) := by
      rw [symplecticDiagonalTorus_includePoint_matrix_entries]
      congr 1
    have heig := congrArg
      (fun E : IdentityPointDerivation
          (standardSymplecticClosedSubgroup (k := k) m).carrierVariety =>
        E (symplecticMatrixCoordinate (k := k) m p q)) (hD.2 s)
    rw [identityTangentRepresentation_action_apply,
      symplecticMatrixCoordinate_conjugation m p q _ z hdiag] at heig
    change D.toLinearMap (((z p : k) * (z q : k)⁻¹) •
        symplecticMatrixCoordinate m p q) =
      (chi⁻¹).pointCharacter s * D (symplecticMatrixCoordinate m p q) at heig
    rw [D.toLinearMap.map_smul] at heig
    change ((z p : k) * (z q : k)⁻¹) * D (symplecticMatrixCoordinate m p q) =
      (chi⁻¹).pointCharacter s * D (symplecticMatrixCoordinate m p q) at heig
    have hpoint : (chi⁻¹).pointCharacter s = (z p : k) * (z q : k)⁻¹ := by
      apply mul_right_cancel₀ hpqD
      exact heig.symm
    rw [pointCharacter_mul,
      pointCharacter_inv (symplecticDiagonalEntryCharacter (k := k) m q) s]
    exact hpoint
  have hpq : p ≠ q := by
    intro hpq
    subst q
    have hone : chi⁻¹ = 1 := by simpa using hcharInv
    apply hchi
    simpa using congrArg Inv.inv hone
  obtain ⟨r, hr⟩ := exists_rootWeight_inv_eq_entry_quotient
    (k := k) m p q hpq
  refine ⟨r, ?_⟩
  apply inv_injective
  exact hcharInv.trans hr.symm

end

end

end Theory.AlgebraicGroup
