module

public import Theory.Representation.FirstCohomologySymplecticFour.Quadratic
public import Theory.Representation.FirstCohomologySymplecticFour.BinaryField
public import Theory.Representation.FirstCohomologySymplecticFour.LargeField
public import Theory.Representation.FirstCohomologyCyclic

/-!
# First cohomology of the natural derived symplectic four-space

The natural module for `Sp₄(K)'` has first-cohomology dimension one over every
finite field `K` of characteristic two, including the binary field.

The quadratic-defect cocycle gives a nonzero class. The separate binary and
larger-field calculations show that every cocycle is a scalar multiple of it
plus a principal cocycle. Every finite field has at least two elements, so these
cases exhaust the fields in question and the cyclic quotient criterion gives
dimension one. The group remains the actual derived subgroup in both cases.

Reference: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma I.1.6(5), printed p.408 (PDF p.419).
-/

namespace Representation.OneCohomology.SymplecticFour

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

/-- The explicit quadratic-defect class is nonzero. -/
public lemma quadratic_class_ne_zero :
    classMap (symplecticDerivedNatural (k := K) 2) derivedQuadraticCocycle ≠ 0 := by
  intro h
  exact derivedQuadraticCocycle_not_principal
    ((classMap_eq_zero_iff _ _).mp h)

/-- First cohomology has positive dimension, including over the binary field. -/
public lemma finrank_H1_pos :
    0 < Module.finrank K (H1 (symplecticDerivedNatural (k := K) 2)) := by
  let := nontrivial_of_ne _ _ (quadratic_class_ne_zero (K := K))
  exact Module.finrank_pos

/-- A spanning calculation and explicit nonprincipality give dimension one. -/
public lemma finrank_H1_eq_one_of_normalForm
    (hspans : ∀ f : cocycles (symplecticDerivedNatural (k := K) 2),
      ∃ t : K, ∃ v : (Fin 2 ⊕ Fin 2) → K,
        f = t • derivedQuadraticCocycle + principal (symplecticDerivedNatural 2) v) :
    Module.finrank K (H1 (symplecticDerivedNatural (k := K) 2)) = 1 :=
  finrank_H1_of_cyclicNormalForm _ _ derivedQuadraticCocycle_not_principal hspans

/-- Every natural derived-symplectic cocycle is a scalar multiple of the
quadratic-defect cocycle plus a principal cocycle, including over the binary field. -/
public theorem exists_normal_form
    (f : cocycles (symplecticDerivedNatural (k := K) 2)) :
    ∃ (t : K) (v : (Fin 2 ⊕ Fin 2) → K),
      f = t • derivedQuadraticCocycle + principal (symplecticDerivedNatural 2) v := by
  have hcard : 2 ≤ Nat.card K := Finite.one_lt_card
  rcases lt_or_eq_of_le hcard with hlarge | hbinary
  · exact LargeField.exists_normal_form hlarge f
  · exact BinaryField.exists_normal_form hbinary.symm f

/-- The natural module of `Sp₄(K)'` has first-cohomology dimension one over
every finite field of characteristic two, including `K = F₂`. -/
public theorem finrank_H1_eq_one :
    Module.finrank K (H1 (symplecticDerivedNatural (k := K) 2)) = 1 :=
  finrank_H1_eq_one_of_normalForm exists_normal_form

end Representation.OneCohomology.SymplecticFour
