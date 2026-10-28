module

public import Theory.AlgebraicGroup.Bor1.RepresentationDifferentialKernelEquivalence
public import Theory.AlgebraicGroup.Representations.Algebraic.Natural
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.EvenSpinIsogeny
public import Theory.AlgebraicGroup.RootSystems.HyperbolicStandardSplitForm
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The dimension bound from the concrete orthogonal matrix equations

The natural representation of the exact split Omega carrier detects every
identity tangent. Its quadratic-isometry equations make the tangent matrix,
after interchanging the two hyperbolic halves, alternating: isotropic columns
force its diagonal to vanish, and polarization makes opposite entries sum to
zero. Thus its entries above the diagonal determine it. In dimension eight
there are 28 such entries, giving the upper bound used for Clifford Spin D4.

The argument is valid in every characteristic. In particular, it uses the
quadratic equations themselves as well as their polar equations, so it also
gives 28 in characteristic two. The matrix-coefficient and isotropic-column
proofs adapt the calculation in `EvenOrthogonalTangentWeightSupport.lean`.

Source: GLS3, Chapter 1, §§1.9–1.14, especially the type-D model in 1.10.7(d)
and the Lie-algebra dimension in 1.14.9(e).
-/

open scoped BigOperators
noncomputable section
namespace Theory.AlgebraicGroup.SpinTangentOrthogonal
open Theory.AlgebraicGroup Bor1
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


private def opposite {n : Nat} : hyperbolicTangentIndex n → hyperbolicTangentIndex n
  | .inl i => .inr i
  | .inr i => .inl i

private lemma opposite_opposite {n : Nat} (p : hyperbolicTangentIndex n) :
    opposite (opposite p) = p := by cases p <;> rfl

private lemma tangent_opposite_self (n : Nat) (hn : 4 ≤ n)
    (D : IdentityPointDerivation (evenOrthogonalOmega (k := k) n).carrierVariety)
    (p : hyperbolicTangentIndex n) :
    D (hyperbolicMatrixCoordinate n (opposite p) p) = 0 := by
  cases p with
  | inl i => exact hyperbolicOppositeCoordinate_upper_zero n hn D i
  | inr i => exact hyperbolicOppositeCoordinate_lower_zero n hn D i

private lemma hyperbolicPolarColumn_relation (n : Nat) (hn : 4 ≤ n)
    (p q : hyperbolicTangentIndex n) :
    (∑ i : Fin n,
      (hyperbolicMatrixCoordinate (k := k) n (Sum.inl i) p *
        hyperbolicMatrixCoordinate n (Sum.inr i) q +
      hyperbolicMatrixCoordinate n (Sum.inl i) q *
        hyperbolicMatrixCoordinate n (Sum.inr i) p)) =
      algebraMap k (Variety.PolynomialFunction (evenOrthogonalOmega n).carrierVariety)
        ((hyperbolicForm (k := k) n).polarBilin
          (hyperbolicTangentBasis n p) (hyperbolicTangentBasis n q)) := by
  apply Variety.PolynomialFunction.ext
  intro x
  change polynomialFunctionEvalAddHom (evenOrthogonalOmega n).carrierVariety x
      (∑ i : Fin n, _) = _
  rw [map_sum, polynomialFunction_algebraMap_apply]
  simp only [map_add, polynomialFunctionEvalAddHom_apply,
    polynomialFunction_mul_apply]
  simp_rw [hyperbolicMatrixCoordinate_apply]
  simp only [hyperbolicTangentBasis_coord_inl, hyperbolicTangentBasis_coord_inr]
  rw [← hyperbolicForm_polar]
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add]
  simp only [evenOrthogonalNatural_preserves_hyperbolicForm n hn]

private lemma tangent_columnProduct (n : Nat)
    (D : IdentityPointDerivation (evenOrthogonalOmega (k := k) n).carrierVariety)
    (p q : hyperbolicTangentIndex n) :
    D (∑ i : Fin n,
      hyperbolicMatrixCoordinate n (Sum.inl i) p *
        hyperbolicMatrixCoordinate n (Sum.inr i) q) =
      (match p with
        | .inl i => D (hyperbolicMatrixCoordinate n (.inr i) q)
        | .inr _ => 0) +
      (match q with
        | .inl _ => 0
        | .inr i => D (hyperbolicMatrixCoordinate n (.inl i) p)) := by
  rw [map_sum]
  simp only [D.leibniz]
  change (∑ i : Fin n,
    (hyperbolicMatrixCoordinate n (Sum.inl i) p 1 *
      D (hyperbolicMatrixCoordinate n (Sum.inr i) q) +
    hyperbolicMatrixCoordinate n (Sum.inr i) q 1 *
      D (hyperbolicMatrixCoordinate n (Sum.inl i) p))) = _
  simp only [hyperbolicMatrixCoordinate_one]
  cases p <;> cases q <;> simp [Finset.sum_add_distrib]

omit [IsAlgClosed k] in
private lemma opposite_sum {n : Nat} (f : hyperbolicTangentIndex n → hyperbolicTangentIndex n → k)
    (p q : hyperbolicTangentIndex n) :
    ((match p with | .inl i => f (.inr i) q | .inr _ => 0) +
      (match q with | .inl _ => 0 | .inr i => f (.inl i) p)) +
    ((match q with | .inl i => f (.inr i) p | .inr _ => 0) +
      (match p with | .inl _ => 0 | .inr i => f (.inl i) q)) =
      f (opposite p) q + f (opposite q) p := by
  cases p <;> cases q <;> simp only [opposite, zero_add, add_zero, add_comm]

private lemma tangent_opposite_add (n : Nat) (hn : 4 ≤ n)
    (D : IdentityPointDerivation (evenOrthogonalOmega (k := k) n).carrierVariety)
    (p q : hyperbolicTangentIndex n) :
    D (hyperbolicMatrixCoordinate n (opposite p) q) +
      D (hyperbolicMatrixCoordinate n (opposite q) p) = 0 := by
  have h := congrArg D (hyperbolicPolarColumn_relation (k := k) n hn p q)
  rw [Finset.sum_add_distrib, map_add, D.map_algebraMap,
    tangent_columnProduct, tangent_columnProduct] at h
  exact (opposite_sum (fun a b => D (hyperbolicMatrixCoordinate n a b)) p q).symm.trans h

private abbrev UpperIndex := {pq : Fin 8 × Fin 8 // pq.1 < pq.2}

private def indexEquiv : hyperbolicTangentIndex 4 ≃ Fin 8 := finSumFinEquiv

private def tangentUpperCoordinates :
    IdentityPointDerivation (evenOrthogonalOmega (k := k) 4).carrierVariety →ₗ[k]
      (UpperIndex → k) where
  toFun D pq := D (hyperbolicMatrixCoordinate 4
    (opposite (indexEquiv.symm pq.1.1)) (indexEquiv.symm pq.1.2))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma tangentUpperCoordinates_injective :
    Function.Injective (tangentUpperCoordinates (k := k)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro D hD
  by_contra hne
  obtain ⟨p, q, hpq⟩ := exists_hyperbolicMatrixCoordinate_ne_zero 4 D hne
  apply hpq
  have hupper (a b : hyperbolicTangentIndex 4) (hab : indexEquiv a < indexEquiv b) :
      D (hyperbolicMatrixCoordinate 4 (opposite a) b) = 0 := by
    have h := congrFun hD ⟨(indexEquiv a, indexEquiv b), hab⟩
    change D (hyperbolicMatrixCoordinate 4
      (opposite (indexEquiv.symm (indexEquiv a))) (indexEquiv.symm (indexEquiv b))) = 0 at h
    simpa only [Equiv.symm_apply_apply] using h
  rcases lt_trichotomy (indexEquiv (opposite p)) (indexEquiv q) with hlt | heq | hgt
  · simpa only [opposite_opposite] using hupper (opposite p) q hlt
  · have heq := indexEquiv.injective heq
    subst q
    simpa only [opposite_opposite] using tangent_opposite_self 4 (le_refl 4) D (opposite p)
  · have h := tangent_opposite_add 4 (le_refl 4) D (opposite p) q
    rw [opposite_opposite, hupper q (opposite p) hgt, add_zero] at h
    exact h

private theorem omega_tangent_finrank_le :
    Module.finrank k (IdentityPointDerivation (evenOrthogonalOmega (k := k) 4).carrierVariety) ≤ 28 := by
  have h := LinearMap.finrank_le_finrank_of_injective (tangentUpperCoordinates_injective (k := k))
  have hcard : Fintype.card UpperIndex = 28 := by decide
  simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_one, hcard] using h

end Theory.AlgebraicGroup.SpinTangentOrthogonal

namespace Theory.AlgebraicGroup
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The exact split Omega carrier on four hyperbolic planes has identity
 tangent dimension at most 28, including in characteristic two. -/
public theorem evenOrthogonalOmega_four_tangent_finrank_le :
    Module.finrank k (Bor1.IdentityPointDerivation
      (evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) 4)
        (standardHyperbolicSplit 4)).carrierVariety) ≤ 28 :=
  SpinTangentOrthogonal.omega_tangent_finrank_le

end Theory.AlgebraicGroup
