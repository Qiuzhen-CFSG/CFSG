module

public import Theory.AlgebraicGroup.RootSystems.EvenOrthogonalRootSubgroups
public import Theory.AlgebraicGroup.RootSystems.Classical
public import Theory.AlgebraicGroup.Tori.Character.Tuple
public import Theory.AlgebraicGroup.Tori.Character.Operations
public import Theory.AlgebraicGroup.Tori.Character.Image
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false
set_option backward.isDefEq.respectTransparency false

/-!
# The diagonal torus in split even Omega

For hyperbolic rank `n ≥ 4`, this module constructs the characteristic-free
diagonal torus inside the exact split Omega carrier
`evenSpinActionImageClosedSubgroup (hyperbolicForm n) (standardHyperbolicSplit n)`.
The point morphism sends a Laurent tuple `d` to the hyperbolic isometry with
diagonal blocks `d` and `d⁻¹`.  Its regularity is proved coefficientwise, and
coordinate recovery identifies its closed image with `D_n`.

Exact Omega membership does not use a determinant or a characteristic
restriction.  The hyperbolic flip conjugates a diagonal tuple to its inverse;
algebraic closedness supplies coordinatewise square roots, so every diagonal
point is a commutator and hence lies in the Spin image.  Laurent characters are
then transported across the resulting torus isomorphism.  The exponent attached
to `s e_i + t e_j` is `-s e_i - t e_j`, matching the inverse-conjugation
convention of `RootWeightEquation`.  The existing elementary type-D
conjugation formula therefore gives `evenOrthogonalRootWeight_equation`.

This is the explicit split type-D torus and root-weight calculation underlying
GLS, Part I, Chapter A, Sections 1.9--1.10.  It uses neither classification of
type-D versions nor maximality or exhaustiveness of the displayed roots.
-/

universe u

open scoped BigOperators commutatorElement

namespace Theory.AlgebraicGroup

open StandardRootSystem

variable {k : Type u} [Field k] [IsAlgClosed k]

private def hyperbolicFlipLinearEquiv (n : Nat) :
    HyperbolicSpace k n ≃ₗ[k] HyperbolicSpace k n where
  toFun z := (z.2, z.1)
  invFun z := (z.2, z.1)
  left_inv z := rfl
  right_inv z := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def hyperbolicFlipPoint (n : Nat) :
    quadraticIsometrySubgroup (hyperbolicForm (k := k) n) :=
  ⟨hyperbolicFlipLinearEquiv n, by
    rw [mem_quadraticIsometrySubgroup]
    intro z
    simp [hyperbolicFlipLinearEquiv, hyperbolicForm_apply, mul_comm]⟩

private noncomputable def unitSquareRoot (x : kˣ) : kˣ :=
  let c := Classical.choose
    (IsAlgClosed.exists_pow_nat_eq (x : k) (show 0 < 2 by omega))
  Units.mk0 c (by
    intro hc
    have hs := Classical.choose_spec
      (IsAlgClosed.exists_pow_nat_eq (x : k) (show 0 < 2 by omega))
    change c ^ 2 = (x : k) at hs
    rw [hc] at hs
    norm_num at hs
    exact x.ne_zero hs.symm)

private lemma unitSquareRoot_sq (x : kˣ) :
    ((unitSquareRoot x : k) * unitSquareRoot x) = x := by
  simpa [unitSquareRoot, pow_two] using
    (Classical.choose_spec
      (IsAlgClosed.exists_pow_nat_eq (x : k) (show 0 < 2 by omega)))

private noncomputable def hyperbolicDiagonalSquareRoot (n : Nat)
    (d : Fin n → kˣ) : Fin n → kˣ :=
  fun i => unitSquareRoot (d i)

private lemma hyperbolicDiagonalPoint_one (n : Nat) :
    hyperbolicDiagonalPoint (k := k) n 1 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  apply Prod.ext <;> funext i <;>
    simp [hyperbolicDiagonalPoint, hyperbolicDiagonalIsometry,
      hyperbolicDiagonalLinearEquiv]

private lemma hyperbolicDiagonalPoint_mul (n : Nat) (d e : Fin n → kˣ) :
    hyperbolicDiagonalPoint n (d * e) =
      hyperbolicDiagonalPoint n d * hyperbolicDiagonalPoint n e := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  apply Prod.ext <;> funext i <;>
    simp [LinearEquiv.mul_apply, hyperbolicDiagonalPoint,
      hyperbolicDiagonalIsometry, hyperbolicDiagonalLinearEquiv,
      mul_assoc, mul_comm]

private lemma hyperbolicFlipPoint_mul_self (n : Nat) :
    hyperbolicFlipPoint (k := k) n * hyperbolicFlipPoint n = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  rfl

private lemma hyperbolicFlipPoint_inv (n : Nat) :
    (hyperbolicFlipPoint (k := k) n)⁻¹ = hyperbolicFlipPoint n := by
  apply inv_eq_of_mul_eq_one_right
  exact hyperbolicFlipPoint_mul_self n

private lemma hyperbolicDiagonalPoint_inv (n : Nat) (d : Fin n → kˣ) :
    (hyperbolicDiagonalPoint n d)⁻¹ = hyperbolicDiagonalPoint n d⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [← hyperbolicDiagonalPoint_mul,
    show d * d⁻¹ = 1 by funext i; exact mul_inv_cancel (d i),
    hyperbolicDiagonalPoint_one]

private lemma hyperbolicFlipPoint_conjugates_diagonal_inv (n : Nat)
    (d : Fin n → kˣ) :
    hyperbolicFlipPoint n * hyperbolicDiagonalPoint n d⁻¹ *
        hyperbolicFlipPoint n = hyperbolicDiagonalPoint n d := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  apply Prod.ext <;> funext i <;>
    simp [LinearEquiv.mul_apply, hyperbolicFlipPoint, hyperbolicFlipLinearEquiv,
      hyperbolicDiagonalPoint, hyperbolicDiagonalIsometry,
      hyperbolicDiagonalLinearEquiv]

private lemma hyperbolicDiagonalPoint_commutator (n : Nat)
    (d : Fin n → kˣ) :
    ⁅hyperbolicDiagonalPoint n (hyperbolicDiagonalSquareRoot n d),
        hyperbolicFlipPoint n⁆ = hyperbolicDiagonalPoint n d := by
  rw [commutatorElement_def, hyperbolicDiagonalPoint_inv,
    hyperbolicFlipPoint_inv]
  calc
    hyperbolicDiagonalPoint n (hyperbolicDiagonalSquareRoot n d) *
          hyperbolicFlipPoint n *
          hyperbolicDiagonalPoint n (hyperbolicDiagonalSquareRoot n d)⁻¹ *
          hyperbolicFlipPoint n =
        hyperbolicDiagonalPoint n (hyperbolicDiagonalSquareRoot n d) *
          (hyperbolicFlipPoint n *
            hyperbolicDiagonalPoint n (hyperbolicDiagonalSquareRoot n d)⁻¹ *
            hyperbolicFlipPoint n) := by simp only [mul_assoc]
    _ = hyperbolicDiagonalPoint n (hyperbolicDiagonalSquareRoot n d) *
          hyperbolicDiagonalPoint n (hyperbolicDiagonalSquareRoot n d) := by
      rw [hyperbolicFlipPoint_conjugates_diagonal_inv]
    _ = hyperbolicDiagonalPoint n
          (hyperbolicDiagonalSquareRoot n d * hyperbolicDiagonalSquareRoot n d) :=
      (hyperbolicDiagonalPoint_mul n _ _).symm
    _ = hyperbolicDiagonalPoint n d := by
      congr 1
      funext i
      apply Units.ext
      exact unitSquareRoot_sq (d i)

private noncomputable def evenOrthogonalDiagonalGeneralLinearPoint (n : Nat)
    (x : Variety.Point (dVariety k n)) :
    LinearMap.GeneralLinearGroup k (HyperbolicSpace k n) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv k
      (HyperbolicSpace k n)).symm
    (hyperbolicDiagonalPoint n (dPointEquiv n x)).1

private lemma evenOrthogonalDiagonalGeneralLinearPoint_one (n : Nat) :
    evenOrthogonalDiagonalGeneralLinearPoint (k := k) n 1 = 1 := by
  rw [evenOrthogonalDiagonalGeneralLinearPoint, dPointEquiv_one,
    hyperbolicDiagonalPoint_one]
  exact map_one (LinearMap.GeneralLinearGroup.generalLinearEquiv k
    (HyperbolicSpace k n)).symm

private lemma evenOrthogonalDiagonalGeneralLinearPoint_mul (n : Nat)
    (x y : Variety.Point (dVariety k n)) :
    evenOrthogonalDiagonalGeneralLinearPoint n (x * y) =
      evenOrthogonalDiagonalGeneralLinearPoint n x *
        evenOrthogonalDiagonalGeneralLinearPoint n y := by
  rw [evenOrthogonalDiagonalGeneralLinearPoint, dPointEquiv_mul,
    hyperbolicDiagonalPoint_mul]
  exact map_mul (LinearMap.GeneralLinearGroup.generalLinearEquiv k
    (HyperbolicSpace k n)).symm _ _

private noncomputable def evenOrthogonalDiagonalPointRepresentation (n : Nat) :
    Variety.Point (dVariety k n) →*
      LinearMap.GeneralLinearGroup k (HyperbolicSpace k n) where
  toFun := evenOrthogonalDiagonalGeneralLinearPoint n
  map_one' := evenOrthogonalDiagonalGeneralLinearPoint_one n
  map_mul' := evenOrthogonalDiagonalGeneralLinearPoint_mul n

private lemma evenOrthogonalDiagonalPointRepresentation_linear (n : Nat)
    (x : Variety.Point (dVariety k n)) :
    LinearMap.GeneralLinearGroup.generalLinearEquiv k (HyperbolicSpace k n)
        (evenOrthogonalDiagonalPointRepresentation n x) =
      (hyperbolicDiagonalPoint n (dPointEquiv n x)).1 := by
  change LinearMap.GeneralLinearGroup.generalLinearEquiv k (HyperbolicSpace k n)
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv k
        (HyperbolicSpace k n)).symm
          (hyperbolicDiagonalPoint n (dPointEquiv n x)).1) = _
  exact (LinearMap.GeneralLinearGroup.generalLinearEquiv k
    (HyperbolicSpace k n)).apply_symm_apply _

private noncomputable def hyperbolicFirstSummandVector (n : Nat)
    (v : HyperbolicSpace k n) (i : Fin n) : HyperbolicSpace k n :=
  (Pi.single i (v.1 i), 0)

private noncomputable def hyperbolicSecondSummandVector (n : Nat)
    (v : HyperbolicSpace k n) (i : Fin n) : HyperbolicSpace k n :=
  (0, Pi.single i (v.2 i))

private noncomputable def evenOrthogonalDiagonalMatrixCoefficient (n : Nat)
    (row column : Fin (Module.finrank k (HyperbolicSpace k n))) :
    (dVariety k n).PolynomialFunction :=
  let b := Module.finBasis k (HyperbolicSpace k n)
  Variety.PolynomialFunction.ofPolynomial (dVariety k n)
    (∑ i : Fin n, (
      MvPolynomial.X (Sum.inl (ULift.up i)) *
          MvPolynomial.C (b.repr (hyperbolicFirstSummandVector n (b column) i) row) +
        MvPolynomial.X (Sum.inr (ULift.up i)) *
          MvPolynomial.C (b.repr (hyperbolicSecondSummandVector n (b column) i) row)))

private noncomputable def evenOrthogonalDiagonalInverseMatrixCoefficient (n : Nat)
    (row column : Fin (Module.finrank k (HyperbolicSpace k n))) :
    (dVariety k n).PolynomialFunction :=
  let b := Module.finBasis k (HyperbolicSpace k n)
  Variety.PolynomialFunction.ofPolynomial (dVariety k n)
    (∑ i : Fin n, (
      MvPolynomial.X (Sum.inr (ULift.up i)) *
          MvPolynomial.C (b.repr (hyperbolicFirstSummandVector n (b column) i) row) +
        MvPolynomial.X (Sum.inl (ULift.up i)) *
          MvPolynomial.C (b.repr (hyperbolicSecondSummandVector n (b column) i) row)))

private lemma hyperbolicDiagonal_sum_decomposition (n : Nat)
    (x : Variety.Point (dVariety k n)) (v : HyperbolicSpace k n) :
    (hyperbolicDiagonalPoint n (dPointEquiv n x)).1 v =
      ∑ i : Fin n, ((dPointEntry n x i) • hyperbolicFirstSummandVector n v i +
        (dPointEntryInv n x i) • hyperbolicSecondSummandVector n v i) := by
  classical
  apply Prod.ext <;> funext j
  · change dPointEntry n x j * v.1 j = _
    simp [Prod.fst_sum, Prod.fst_add, Prod.fst_smul,
      hyperbolicFirstSummandVector, hyperbolicSecondSummandVector, Pi.single_apply]
  · change dPointEntryInv n x j * v.2 j = _
    simp [Prod.snd_sum, Prod.snd_add, Prod.snd_smul,
      hyperbolicFirstSummandVector, hyperbolicSecondSummandVector, Pi.single_apply]

private lemma hyperbolicDiagonal_inv_sum_decomposition (n : Nat)
    (x : Variety.Point (dVariety k n)) (v : HyperbolicSpace k n) :
    ((hyperbolicDiagonalPoint n (dPointEquiv n x)).1)⁻¹ v =
      ∑ i : Fin n, ((dPointEntryInv n x i) • hyperbolicFirstSummandVector n v i +
        (dPointEntry n x i) • hyperbolicSecondSummandVector n v i) := by
  classical
  apply Prod.ext <;> funext j
  · change dPointEntryInv n x j * v.1 j = _
    simp [Prod.fst_sum, Prod.fst_add, Prod.fst_smul,
      hyperbolicFirstSummandVector, hyperbolicSecondSummandVector, Pi.single_apply]
  · change dPointEntry n x j * v.2 j = _
    simp [Prod.snd_sum, Prod.snd_add, Prod.snd_smul,
      hyperbolicFirstSummandVector, hyperbolicSecondSummandVector, Pi.single_apply]

private lemma evenOrthogonalDiagonalMatrixCoefficient_apply (n : Nat)
    (row column : Fin (Module.finrank k (HyperbolicSpace k n)))
    (x : Variety.Point (dVariety k n)) :
    evenOrthogonalDiagonalMatrixCoefficient n row column x =
      (Module.finBasis k (HyperbolicSpace k n)).repr
        (((evenOrthogonalDiagonalPointRepresentation n x :
            LinearMap.GeneralLinearGroup k (HyperbolicSpace k n)) :
          Module.End k (HyperbolicSpace k n))
          ((Module.finBasis k (HyperbolicSpace k n)) column)) row := by
  classical
  simp only [evenOrthogonalDiagonalMatrixCoefficient,
    Variety.PolynomialFunction.ofPolynomial,
    Variety.PolynomialFunction.toFun]
  simp only [evalPolynomial, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_add,
    MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_X, MvPolynomial.eval₂_C, RingHom.id_apply]
  change (∑ i : Fin n,
      (dPointEntry n x i * _ + dPointEntryInv n x i * _)) = _
  change _ = (Module.finBasis k (HyperbolicSpace k n)).repr
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv k (HyperbolicSpace k n)
      (evenOrthogonalDiagonalPointRepresentation n x))
        ((Module.finBasis k (HyperbolicSpace k n)) column)) row
  rw [evenOrthogonalDiagonalPointRepresentation_linear]
  rw [hyperbolicDiagonal_sum_decomposition]
  simp [map_sum, map_add, map_smul]

private lemma evenOrthogonalDiagonalInverseMatrixCoefficient_apply (n : Nat)
    (row column : Fin (Module.finrank k (HyperbolicSpace k n)))
    (x : Variety.Point (dVariety k n)) :
    evenOrthogonalDiagonalInverseMatrixCoefficient n row column x =
      (Module.finBasis k (HyperbolicSpace k n)).repr
        (((((evenOrthogonalDiagonalPointRepresentation n x)⁻¹ :
            LinearMap.GeneralLinearGroup k (HyperbolicSpace k n)) :
          Module.End k (HyperbolicSpace k n))
          ((Module.finBasis k (HyperbolicSpace k n)) column))) row := by
  classical
  simp only [evenOrthogonalDiagonalInverseMatrixCoefficient,
    Variety.PolynomialFunction.ofPolynomial,
    Variety.PolynomialFunction.toFun]
  simp only [evalPolynomial, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_add,
    MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_X, MvPolynomial.eval₂_C, RingHom.id_apply]
  change (∑ i : Fin n,
      (dPointEntryInv n x i * _ + dPointEntry n x i * _)) = _
  change _ = (Module.finBasis k (HyperbolicSpace k n)).repr
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv k (HyperbolicSpace k n)
      ((evenOrthogonalDiagonalPointRepresentation n x)⁻¹))
      ((Module.finBasis k (HyperbolicSpace k n)) column)) row
  rw [map_inv, evenOrthogonalDiagonalPointRepresentation_linear]
  rw [hyperbolicDiagonal_inv_sum_decomposition]
  simp [map_sum, map_add, map_smul]

public noncomputable def evenOrthogonalDiagonalAmbientMorphism (n : Nat) :
    AlgebraicGroup.Morphism (dVariety k n)
      (glVarietyOf k (HyperbolicSpace k n)) :=
  generalLinearRepresentationMorphismOfInverseMatrixCoefficient
    (Module.finBasis k (HyperbolicSpace k n))
    (evenOrthogonalDiagonalPointRepresentation n)
    (evenOrthogonalDiagonalMatrixCoefficient n)
    (evenOrthogonalDiagonalInverseMatrixCoefficient n)
    (evenOrthogonalDiagonalMatrixCoefficient_apply n)
    (evenOrthogonalDiagonalInverseMatrixCoefficient_apply n)

private lemma evenOrthogonalDiagonalAmbientMorphism_apply (n : Nat)
    (x : Variety.Point (dVariety k n)) :
    (evenOrthogonalDiagonalAmbientMorphism n).onPoints x =
      generalLinearRepresentationPoint
        (Module.finBasis k (HyperbolicSpace k n))
        (evenOrthogonalDiagonalPointRepresentation n x) := by
  exact generalLinearRepresentationMorphismOfInverseMatrixCoefficient_apply
    (Module.finBasis k (HyperbolicSpace k n))
    (evenOrthogonalDiagonalPointRepresentation n)
    (evenOrthogonalDiagonalMatrixCoefficient n)
    (evenOrthogonalDiagonalInverseMatrixCoefficient n)
    (evenOrthogonalDiagonalMatrixCoefficient_apply n)
    (evenOrthogonalDiagonalInverseMatrixCoefficient_apply n) x

public lemma evenOrthogonalDiagonalAmbientMorphism_linear_points (n : Nat)
    (x : Variety.Point (dVariety k n)) :
    LinearMap.GeneralLinearGroup.generalLinearEquiv k (HyperbolicSpace k n)
        (glPointEquivOf k (HyperbolicSpace k n)
          (Module.finBasis k (HyperbolicSpace k n))
          ((evenOrthogonalDiagonalAmbientMorphism n).onPoints x)) =
      (hyperbolicDiagonalPoint n (dPointEquiv n x)).1 := by
  rw [evenOrthogonalDiagonalAmbientMorphism_apply,
    glPointEquivOf_generalLinearRepresentationPoint]
  change LinearMap.GeneralLinearGroup.generalLinearEquiv k (HyperbolicSpace k n)
      (evenOrthogonalDiagonalGeneralLinearPoint n x) = _
  exact (LinearMap.GeneralLinearGroup.generalLinearEquiv k
    (HyperbolicSpace k n)).apply_symm_apply _

public lemma evenOrthogonalDiagonalAmbientMorphism_mem (n : Nat) (hn : 4 ≤ n)
    (x : Variety.Point (dVariety k n)) :
    (evenOrthogonalDiagonalAmbientMorphism n).onPoints x ∈
      (evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
        (standardHyperbolicSplit n)).toSubgroup := by
  have hrank : 4 ≤ (standardHyperbolicSplit (k := k) n).rank := by
    simpa using hn
  rw [evenSpinActionImageClosedSubgroup_commutator_carrier
    (hyperbolicForm (k := k) n) (standardHyperbolicSplit n) hrank]
  let d := dPointEquiv n x
  let c := hyperbolicDiagonalSquareRoot n d
  let f := hyperbolicFlipPoint (k := k) n
  have hmem : ⁅hyperbolicDiagonalPoint n c, f⁆ ∈
      commutator (quadraticIsometrySubgroup (hyperbolicForm (k := k) n)) := by
    change ⁅hyperbolicDiagonalPoint n c, f⁆ ∈
      ⁅(⊤ : Subgroup (quadraticIsometrySubgroup
        (hyperbolicForm (k := k) n))), ⊤⁆
    exact Subgroup.commutator_mem_commutator
      (Subgroup.mem_top _) (Subgroup.mem_top _)
  refine ⟨⟨⁅hyperbolicDiagonalPoint n c, f⁆, hmem⟩, ?_⟩
  change (⁅hyperbolicDiagonalPoint n c, f⁆ :
      quadraticIsometrySubgroup (hyperbolicForm (k := k) n)).1 = _
  rw [hyperbolicDiagonalPoint_commutator]
  exact (evenOrthogonalDiagonalAmbientMorphism_linear_points n x).symm

@[expose]
public noncomputable def evenOrthogonalDiagonalMorphism (n : Nat) (hn : 4 ≤ n) :
    AlgebraicGroup.Morphism (dVariety k n)
      (evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
        (standardHyperbolicSplit n)).carrierVariety :=
  (evenOrthogonalDiagonalAmbientMorphism n).codRestrictClosedSubgroup
    (evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
      (standardHyperbolicSplit n))
    (evenOrthogonalDiagonalAmbientMorphism_mem n hn)

@[simp]
public lemma evenOrthogonalDiagonalMorphism_include_apply (n : Nat) (hn : 4 ≤ n)
    (x : Variety.Point (dVariety k n)) :
    (evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
        (standardHyperbolicSplit n)).includePoint
      ((evenOrthogonalDiagonalMorphism n hn).onPoints x) =
        (evenOrthogonalDiagonalAmbientMorphism n).onPoints x :=
  (evenOrthogonalDiagonalAmbientMorphism n).codRestrictClosedSubgroup_inclusion_apply
    (evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
      (standardHyperbolicSplit n))
    (evenOrthogonalDiagonalAmbientMorphism_mem n hn) x

public lemma evenOrthogonalDiagonalMorphism_linear_points (n : Nat) (hn : 4 ≤ n)
    (x : Variety.Point (dVariety k n)) :
    LinearMap.GeneralLinearGroup.generalLinearEquiv k (HyperbolicSpace k n)
        (glPointEquivOf k (HyperbolicSpace k n)
          (Module.finBasis k (HyperbolicSpace k n))
          ((evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
            (standardHyperbolicSplit n)).includePoint
              ((evenOrthogonalDiagonalMorphism n hn).onPoints x))) =
      (hyperbolicDiagonalPoint n (dPointEquiv n x)).1 := by
  rw [evenOrthogonalDiagonalMorphism_include_apply,
    evenOrthogonalDiagonalAmbientMorphism_linear_points]

public lemma evenOrthogonalDiagonalMorphism_injective (n : Nat) (hn : 4 ≤ n) :
    Function.Injective (evenOrthogonalDiagonalMorphism (k := k) n hn).onPoints := by
  intro x y hxy
  have hambient := congrArg
    (evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
      (standardHyperbolicSplit n)).includePoint hxy
  have hgl := congrArg
    (glPointEquivOf k (HyperbolicSpace k n)
      (Module.finBasis k (HyperbolicSpace k n))) hambient
  have hlinear := congrArg
    (LinearMap.GeneralLinearGroup.generalLinearEquiv k (HyperbolicSpace k n)) hgl
  rw [evenOrthogonalDiagonalMorphism_linear_points,
    evenOrthogonalDiagonalMorphism_linear_points] at hlinear
  apply (dPointEquiv n).injective
  funext i
  apply Units.ext
  have hi := congrArg
    (fun f : HyperbolicSpace k n ≃ₗ[k] HyperbolicSpace k n =>
      (f (Pi.single i 1, 0)).1 i) hlinear
  simpa [hyperbolicDiagonalPoint, hyperbolicDiagonalIsometry,
    hyperbolicDiagonalLinearEquiv] using hi

private def hyperbolicDiagonalCoordinate (n : Nat) (second : Bool) (i : Fin n) :
    HyperbolicSpace k n →ₗ[k] k where
  toFun z := if second then z.2 i else z.1 i
  map_add' x y := by cases second <;> simp
  map_smul' c x := by cases second <;> simp

private noncomputable def hyperbolicDiagonalCoordinateSource (n : Nat)
    (second : Bool) (i : Fin n) : HyperbolicSpace k n :=
  if second then (0, Pi.single i 1) else (Pi.single i 1, 0)

private noncomputable def evenOrthogonalDiagonalAmbientMatrixCoordinate (n : Nat)
    (i j : Fin (Module.finrank k (HyperbolicSpace k n))) :
    Variety.PolynomialFunction (glVarietyOf k (HyperbolicSpace k n)) := by
  change Variety.PolynomialFunction
    (glVariety (Module.finrank k (HyperbolicSpace k n)) : Variety k)
  exact generalLinearMatrixCoordinate
    (Module.finrank k (HyperbolicSpace k n)) i j

private noncomputable def evenOrthogonalDiagonalAmbientRecovery (n : Nat)
    (second : Bool) (p : Fin n) :
    Variety.PolynomialFunction (glVarietyOf k (HyperbolicSpace k n)) :=
  let b := Module.finBasis k (HyperbolicSpace k n)
  ∑ i, ∑ j,
    algebraMap k
      (Variety.PolynomialFunction (glVarietyOf k (HyperbolicSpace k n)))
      (hyperbolicDiagonalCoordinate n second p (b i) *
        b.repr (hyperbolicDiagonalCoordinateSource n second p) j) *
      evenOrthogonalDiagonalAmbientMatrixCoordinate n i j

private lemma evenOrthogonalDiagonalAmbientRecovery_apply (n : Nat)
    (second : Bool) (p : Fin n) (x : Variety.Point (dVariety k n)) :
    evenOrthogonalDiagonalAmbientRecovery n second p
        ((evenOrthogonalDiagonalAmbientMorphism n).onPoints x) =
      hyperbolicDiagonalCoordinate n second p
        ((hyperbolicDiagonalPoint n (dPointEquiv n x)).1
          (hyperbolicDiagonalCoordinateSource n second p)) := by
  classical
  rw [evenOrthogonalDiagonalAmbientRecovery]
  change polynomialFunctionEvalAddHom
      (glVarietyOf k (HyperbolicSpace k n))
      ((evenOrthogonalDiagonalAmbientMorphism n).onPoints x)
      (∑ i, ∑ j,
        algebraMap k
          (Variety.PolynomialFunction (glVarietyOf k (HyperbolicSpace k n)))
          (hyperbolicDiagonalCoordinate n second p
              ((Module.finBasis k (HyperbolicSpace k n)) i) *
            (Module.finBasis k (HyperbolicSpace k n)).repr
              (hyperbolicDiagonalCoordinateSource n second p) j) *
          evenOrthogonalDiagonalAmbientMatrixCoordinate n i j) = _
  rw [map_sum]
  simp only [map_sum, polynomialFunctionEvalAddHom_apply,
    polynomialFunction_mul_apply, polynomialFunction_algebraMap_apply]
  have hcoord (i j : Fin (Module.finrank k (HyperbolicSpace k n))) :
      evenOrthogonalDiagonalAmbientMatrixCoordinate n i j
          ((evenOrthogonalDiagonalAmbientMorphism n).onPoints x) =
        (Module.finBasis k (HyperbolicSpace k n)).repr
          ((hyperbolicDiagonalPoint n (dPointEquiv n x)).1
            ((Module.finBasis k (HyperbolicSpace k n)) j)) i := by
    rw [evenOrthogonalDiagonalAmbientMatrixCoordinate]
    change generalLinearMatrixCoordinate
        (Module.finrank k (HyperbolicSpace k n)) i j
          ((evenOrthogonalDiagonalAmbientMorphism n).onPoints x) = _
    rw [generalLinearMatrixCoordinate_apply,
      evenOrthogonalDiagonalAmbientMorphism_apply,
      generalLinearRepresentationPoint_matrix]
    exact congrArg
      (fun f : HyperbolicSpace k n ≃ₗ[k] HyperbolicSpace k n =>
        (Module.finBasis k (HyperbolicSpace k n)).repr
          (f ((Module.finBasis k (HyperbolicSpace k n)) j)) i)
      (evenOrthogonalDiagonalPointRepresentation_linear n x)
  simp_rw [hcoord]
  simpa [LinearMap.toMatrix_apply, mul_assoc] using
    LinearMap.dual_apply_eq_sum_toMatrix
      (Module.finBasis k (HyperbolicSpace k n))
      (hyperbolicDiagonalCoordinate n second p)
      (hyperbolicDiagonalPoint n (dPointEquiv n x)).1.toLinearMap
      (hyperbolicDiagonalCoordinateSource n second p)

private lemma hyperbolicDiagonalCoordinate_recovery (n : Nat)
    (second : Bool) (p : Fin n) (x : Variety.Point (dVariety k n)) :
    hyperbolicDiagonalCoordinate n second p
        ((hyperbolicDiagonalPoint n (dPointEquiv n x)).1
          (hyperbolicDiagonalCoordinateSource n second p)) =
      if second then dPointEntryInv n x p else dPointEntry n x p := by
  cases second
  · simp [hyperbolicDiagonalCoordinate, hyperbolicDiagonalCoordinateSource,
      hyperbolicDiagonalPoint, hyperbolicDiagonalIsometry,
      hyperbolicDiagonalLinearEquiv, Pi.single_apply]
    rfl
  · simp [hyperbolicDiagonalCoordinate, hyperbolicDiagonalCoordinateSource,
      hyperbolicDiagonalPoint, hyperbolicDiagonalIsometry,
      hyperbolicDiagonalLinearEquiv, Pi.single_apply]
    exact dPoint_entry_inv n x p

private noncomputable def evenOrthogonalDiagonalRecovery (n : Nat) (hn : 4 ≤ n)
    (second : Bool) (p : Fin n) :
    Variety.PolynomialFunction
      (evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
        (standardHyperbolicSplit n)).carrierVariety :=
  Variety.PolynomialFunction.pullback
    (evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
      (standardHyperbolicSplit n)).inclusion.toVariety
    (evenOrthogonalDiagonalAmbientRecovery n second p)

public lemma evenOrthogonalDiagonalMorphism_coordinate_preimage (n : Nat)
    (hn : 4 ≤ n) :
    ∀ c : (dVariety k n).Coordinates,
      ∃ q : Variety.PolynomialFunction
          (evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
            (standardHyperbolicSplit n)).carrierVariety,
        Variety.PolynomialFunction.pullback
            (evenOrthogonalDiagonalMorphism n hn).toVariety q =
          Variety.PolynomialFunction.ofPolynomial (dVariety k n)
            (MvPolynomial.X c) := by
  intro c
  rcases c with i | i
  · rcases i with ⟨i⟩
    refine ⟨evenOrthogonalDiagonalRecovery n hn false i, ?_⟩
    apply Variety.PolynomialFunction.ext
    intro x
    simp only [Variety.PolynomialFunction.pullback,
      Variety.PolynomialFunction.ofPolynomial,
      Variety.PolynomialFunction.toFun]
    change evenOrthogonalDiagonalRecovery n hn false i
        ((evenOrthogonalDiagonalMorphism n hn).onPoints x) =
      evalPolynomial x.val (MvPolynomial.X (Sum.inl (ULift.up i)))
    rw [evenOrthogonalDiagonalRecovery]
    change evenOrthogonalDiagonalAmbientRecovery n false i
        ((evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
          (standardHyperbolicSplit n)).includePoint
            ((evenOrthogonalDiagonalMorphism n hn).onPoints x)) = _
    rw [evenOrthogonalDiagonalMorphism_include_apply,
      evenOrthogonalDiagonalAmbientRecovery_apply,
      hyperbolicDiagonalCoordinate_recovery]
    rw [evalPolynomial_X]
    apply congrArg x.val
    rfl
  · rcases i with ⟨i⟩
    refine ⟨evenOrthogonalDiagonalRecovery n hn true i, ?_⟩
    apply Variety.PolynomialFunction.ext
    intro x
    simp only [Variety.PolynomialFunction.pullback,
      Variety.PolynomialFunction.ofPolynomial,
      Variety.PolynomialFunction.toFun]
    change evenOrthogonalDiagonalRecovery n hn true i
        ((evenOrthogonalDiagonalMorphism n hn).onPoints x) =
      evalPolynomial x.val (MvPolynomial.X (Sum.inr (ULift.up i)))
    rw [evenOrthogonalDiagonalRecovery]
    change evenOrthogonalDiagonalAmbientRecovery n true i
        ((evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
          (standardHyperbolicSplit n)).includePoint
            ((evenOrthogonalDiagonalMorphism n hn).onPoints x)) = _
    rw [evenOrthogonalDiagonalMorphism_include_apply,
      evenOrthogonalDiagonalAmbientRecovery_apply,
      hyperbolicDiagonalCoordinate_recovery]
    rw [evalPolynomial_X]
    apply congrArg x.val
    rfl

@[expose]
public noncomputable def evenOrthogonalDiagonalTorus (n : Nat) (hn : 4 ≤ n) :
    ClosedSubgroup
      (evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
        (standardHyperbolicSplit n)).carrierVariety :=
  (evenOrthogonalDiagonalMorphism n hn).imageClosedSubgroup

public lemma evenOrthogonalDiagonalTorus_isSubtorus (n : Nat) (hn : 4 ≤ n) :
    IsSubtorus (evenOrthogonalDiagonalTorus (k := k) n hn) :=
  morphism_image_isTorus (evenOrthogonalDiagonalMorphism n hn)
    (dVariety_isTorus n)

public noncomputable def evenOrthogonalDiagonalTorusIso (n : Nat) (hn : 4 ≤ n) :
    letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
    AlgebraicGroup.Iso (dVariety k n)
      (evenOrthogonalDiagonalTorus n hn).carrierVariety := by
  letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
  exact Classical.choose
    ((evenOrthogonalDiagonalMorphism n hn).iso_imageClosedSubgroup_of_coordinate_preimage
      (evenOrthogonalDiagonalMorphism_injective n hn)
      (evenOrthogonalDiagonalMorphism_coordinate_preimage n hn))

public lemma evenOrthogonalDiagonalTorusIso_hom (n : Nat) (hn : 4 ≤ n) :
    letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
    (evenOrthogonalDiagonalTorusIso (k := k) n hn).hom =
      (evenOrthogonalDiagonalMorphism n hn).codRestrictClosedSubgroup
        (evenOrthogonalDiagonalTorus n hn) (fun y => ⟨y, rfl⟩) := by
  letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
  exact Classical.choose_spec
    ((evenOrthogonalDiagonalMorphism n hn).iso_imageClosedSubgroup_of_coordinate_preimage
      (evenOrthogonalDiagonalMorphism_injective n hn)
      (evenOrthogonalDiagonalMorphism_coordinate_preimage n hn))

public lemma evenOrthogonalDiagonalTorusIso_inclusion_hom (n : Nat) (hn : 4 ≤ n)
    (x : Variety.Point (dVariety k n)) :
    letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
    (evenOrthogonalDiagonalTorus n hn).inclusion.onPoints
        ((evenOrthogonalDiagonalTorusIso n hn).hom.onPoints x) =
      (evenOrthogonalDiagonalMorphism n hn).onPoints x := by
  letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
  rw [evenOrthogonalDiagonalTorusIso_hom]
  exact AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply
    (evenOrthogonalDiagonalMorphism n hn) (evenOrthogonalDiagonalTorus n hn)
      (fun y => ⟨y, rfl⟩) x

@[expose]
public noncomputable def evenOrthogonalDiagonalTorusPointEquiv (n : Nat)
    (hn : 4 ≤ n) :
    letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
    Variety.Point (evenOrthogonalDiagonalTorus (k := k) n hn).carrierVariety ≃*
      Variety.Point (dVariety k n) := by
  letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
  exact (evenOrthogonalDiagonalTorusIso (k := k) n hn).toMulEquiv.symm

public lemma evenOrthogonalDiagonalTorusPointEquiv_symm_inclusion (n : Nat)
    (hn : 4 ≤ n) (x : Variety.Point (dVariety k n)) :
    letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
    (evenOrthogonalDiagonalTorus (k := k) n hn).inclusion.onPoints
        ((evenOrthogonalDiagonalTorusPointEquiv (k := k) n hn).symm x) =
      (evenOrthogonalDiagonalMorphism (k := k) n hn).onPoints x := by
  letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
  exact evenOrthogonalDiagonalTorusIso_inclusion_hom (k := k) n hn x

@[expose]
public noncomputable def evenOrthogonalDiagonalCharacterTransport (n : Nat)
    (hn : 4 ≤ n) :
    letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
    TorusCharacter (dVariety k n) ≃*
      TorusWeight (evenOrthogonalDiagonalTorus (k := k) n hn) := by
  letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
  let e := evenOrthogonalDiagonalTorusIso (k := k) n hn
  exact
    { toFun := TorusCharacter.pullback e.inv
      invFun := TorusCharacter.pullback e.hom
      left_inv := by
        intro chi
        apply AlgebraicGroup.Morphism.ext
        funext x
        change chi.onPoints (e.inv.onPoints (e.hom.onPoints x)) = chi.onPoints x
        rw [e.hom_inv_id]
      right_inv := by
        intro chi
        apply AlgebraicGroup.Morphism.ext
        funext x
        change chi.onPoints (e.hom.onPoints (e.inv.onPoints x)) = chi.onPoints x
        rw [e.inv_hom_id]
      map_mul' := (TorusCharacter.pullback e.inv).map_mul }

@[expose]
public noncomputable def evenOrthogonalDiagonalCharacter (n : Nat) (hn : 4 ≤ n)
    (z : Fin n → ℤ) :
    letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
    TorusWeight (evenOrthogonalDiagonalTorus (k := k) n hn) := by
  letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
  exact evenOrthogonalDiagonalCharacterTransport (k := k) n hn
    (dLaurentCharacter (k := k) n z)

public lemma evenOrthogonalDiagonalCharacter_apply (n : Nat) (hn : 4 ≤ n)
    (z : Fin n → ℤ) (x : Variety.Point (dVariety k n)) :
    letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
    dPointEquiv 1
        ((evenOrthogonalDiagonalCharacter (k := k) n hn z).onPoints
          ((evenOrthogonalDiagonalTorusIso (k := k) n hn).hom.onPoints x)) 0 =
      ∏ i, (dPointEquiv n x i) ^ z i := by
  letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
  change dPointEquiv 1
      ((dLaurentCharacter (k := k) n z).onPoints
        ((evenOrthogonalDiagonalTorusIso (k := k) n hn).inv.onPoints
          ((evenOrthogonalDiagonalTorusIso (k := k) n hn).hom.onPoints x))) 0 = _
  rw [(evenOrthogonalDiagonalTorusIso (k := k) n hn).hom_inv_id,
    dLaurentCharacter_apply]

@[expose]
public noncomputable def evenOrthogonalRootExponent (n : Nat) :
    TypeDRootIndex n → Fin n → ℤ
  | ⟨⟨⟨i, j⟩, _⟩, s, t⟩ =>
      (if s.1 = 1 then (-1 : ℤ) else 1) • Pi.single i 1 +
        (if t.1 = 1 then (-1 : ℤ) else 1) • Pi.single j 1

@[expose]
public noncomputable def evenOrthogonalRootWeight (n : Nat) (hn : 4 ≤ n)
    (r : TypeDRootIndex n) :
    letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
    TorusWeight (evenOrthogonalDiagonalTorus (k := k) n hn) := by
  letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
  exact evenOrthogonalDiagonalCharacter (k := k) n hn
    (evenOrthogonalRootExponent n r)

private lemma evenOrthogonalRootExponent_cast (n : Nat) (r : TypeDRootIndex n)
    (i : Fin n) :
    ((evenOrthogonalRootExponent n r i : ℤ) : ℝ) =
      -(typeDRootVector n r i) := by
  rcases r with ⟨⟨⟨a, b⟩, hab⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    by_cases hia : i = a <;> by_cases hib : i = b <;>
      norm_num [evenOrthogonalRootExponent, typeDRootVector, basisVector,
        Pi.single_apply, hia, hib, add_comm]

omit [IsAlgClosed k] in
private lemma evenOrthogonal_prod_zpow_single (n : Nat) (z : Fin n → kˣ)
    (i : Fin n) (q : ℤ) :
    (∏ j, z j ^ (Pi.single i q : Fin n → ℤ) j) = z i ^ q := by
  calc
    (∏ j, z j ^ (Pi.single i q : Fin n → ℤ) j) =
        z i ^ (Pi.single i q : Fin n → ℤ) i := by
      apply Fintype.prod_eq_single i
      intro j hji
      simp [hji]
    _ = z i ^ q := by simp

omit [IsAlgClosed k] in
private lemma evenOrthogonal_prod_zpow_add (n : Nat) (z : Fin n → kˣ)
    (a b : Fin n → ℤ) :
    (∏ j, z j ^ (a j + b j)) =
      (∏ j, z j ^ a j) * ∏ j, z j ^ b j := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  exact zpow_add _ _ _

omit [IsAlgClosed k] in
private lemma evenOrthogonal_prod_zpow_smul_single (n : Nat) (z : Fin n → kˣ)
    (i : Fin n) (q : ℤ) :
    (∏ j, z j ^ (q • Pi.single i 1 : Fin n → ℤ) j) = z i ^ q := by
  rw [show (q • Pi.single i 1 : Fin n → ℤ) = Pi.single i q by
    funext j
    by_cases hji : j = i <;> simp [hji]]
  exact evenOrthogonal_prod_zpow_single n z i q

public lemma evenOrthogonalRootWeight_injective (n : Nat) (hn : 4 ≤ n) :
    Function.Injective (evenOrthogonalRootWeight (k := k) n hn) := by
  intro r q hrq
  letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
  have hchar :
      dLaurentCharacter (k := k) n (evenOrthogonalRootExponent n r) =
        dLaurentCharacter n (evenOrthogonalRootExponent n q) := by
    apply (evenOrthogonalDiagonalCharacterTransport (k := k) n hn).injective
    simpa [evenOrthogonalRootWeight, evenOrthogonalDiagonalCharacter] using hrq
  have hexp := dLaurentCharacter_injective (k := k) n hchar
  apply typeDRootEmbedding_injective n
  apply Subtype.ext
  funext i
  have hi := congrArg (fun z : ℤ => (z : ℝ)) (congrFun hexp i)
  rw [evenOrthogonalRootExponent_cast, evenOrthogonalRootExponent_cast] at hi
  exact neg_injective hi

public lemma evenOrthogonalRootWeight_apply (n : Nat) (hn : 4 ≤ n)
    (r : TypeDRootIndex n) (x : Variety.Point (dVariety k n)) :
    letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
    dPointEquiv 1
        ((evenOrthogonalRootWeight (k := k) n hn r).onPoints
          ((evenOrthogonalDiagonalTorusIso n hn).hom.onPoints x)) 0 =
      evenOrthogonalRootScale n r (dPointEquiv n x) := by
  letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
  rw [evenOrthogonalRootWeight, evenOrthogonalDiagonalCharacter_apply]
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, s, t⟩
  simp only [evenOrthogonalRootExponent, Pi.add_apply]
  change ((∏ q, (dPointEquiv n x q) ^
    (((if s.1 = 1 then (-1 : ℤ) else 1) • Pi.single i 1) q +
     ((if t.1 = 1 then (-1 : ℤ) else 1) • Pi.single j 1) q) : kˣ) : k) = _
  rw [evenOrthogonal_prod_zpow_add, evenOrthogonal_prod_zpow_smul_single,
    evenOrthogonal_prod_zpow_smul_single]
  by_cases hs : s.1 = 1 <;> by_cases ht : t.1 = 1 <;>
    simp [evenOrthogonalRootScale, hs, ht]

public theorem evenOrthogonalRootWeight_pointCharacter (n : Nat) (hn : 4 ≤ n)
    (r : TypeDRootIndex n) :
    letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
    ∀ s : Variety.Point (evenOrthogonalDiagonalTorus (k := k) n hn).carrierVariety,
      (evenOrthogonalRootWeight (k := k) n hn r).pointCharacter s =
        evenOrthogonalRootScale (k := k) n r
          (dPointEquiv n (evenOrthogonalDiagonalTorusPointEquiv (k := k) n hn s)) := by
  letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
  intro s
  let x := evenOrthogonalDiagonalTorusPointEquiv (k := k) n hn s
  have hx : (evenOrthogonalDiagonalTorusIso (k := k) n hn).hom.onPoints x = s := by
    change (evenOrthogonalDiagonalTorusIso (k := k) n hn).hom.onPoints
        ((evenOrthogonalDiagonalTorusIso (k := k) n hn).inv.onPoints s) = s
    rw [(evenOrthogonalDiagonalTorusIso (k := k) n hn).inv_hom_id]
  change dPointEquiv 1 ((evenOrthogonalRootWeight (k := k) n hn r).onPoints s) 0 =
    evenOrthogonalRootScale (k := k) n r (dPointEquiv n x)
  rw [← hx]
  exact evenOrthogonalRootWeight_apply (k := k) n hn r x

public lemma evenOrthogonalRootParametrization_include_value (n : Nat)
    (hn : 4 ≤ n) (r : TypeDRootIndex n) (a : k) :
    (evenOrthogonalRootSubgroup (k := k) n hn r).includePoint
        (@OneParameterParametrization.value k _
          (evenOrthogonalRootSubgroup (k := k) n hn r).carrierVariety
          (evenOrthogonalRootSubgroup (k := k) n hn r).carrierAlgebraicGroup
          (evenOrthogonalRootParametrization n hn r) a) =
      (evenOrthogonalRootMorphism n hn r).onPoints (kPlusPoint a) := by
  let _ : AlgebraicGroup
      (evenOrthogonalRootSubgroup (k := k) n hn r).carrierVariety :=
    (evenOrthogonalRootSubgroup (k := k) n hn r).carrierAlgebraicGroup
  change (evenOrthogonalRootSubgroup (k := k) n hn r).inclusion.onPoints
      ((@AlgebraicGroup.Iso.hom k _ (KPlus k)
          (evenOrthogonalRootSubgroup (k := k) n hn r).carrierVariety
          (inferInstance : AlgebraicGroup (KPlus k))
          (evenOrthogonalRootSubgroup (k := k) n hn r).carrierAlgebraicGroup
          (evenOrthogonalRootParametrization n hn r)).onPoints (kPlusPoint a)) = _
  rw [evenOrthogonalRootParametrization_hom]
  exact (evenOrthogonalRootMorphism n hn r).codRestrictClosedSubgroup_inclusion_apply
    (evenOrthogonalRootSubgroup (k := k) n hn r) (fun y => ⟨y, rfl⟩)
      (kPlusPoint a)

private lemma evenOrthogonalRootMorphism_quadratic_points (n : Nat) (hn : 4 ≤ n)
    (r : TypeDRootIndex n) (a : k) :
    (evenSpinActionImageClosedSubgroupPoints (hyperbolicForm (k := k) n)
        (standardHyperbolicSplit n) (by simpa using hn)
        ((evenOrthogonalRootMorphism n hn r).onPoints (kPlusPoint a))).1 =
      evenOrthogonalRootQuadraticPoint n r a := by
  apply Subtype.ext
  rw [← evenSpinActionImageClosedSubgroup_linear_points]
  change LinearMap.GeneralLinearGroup.generalLinearEquiv k (HyperbolicSpace k n)
      (glPointEquivOf k (HyperbolicSpace k n)
        (Module.finBasis k (HyperbolicSpace k n))
        ((evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
          (standardHyperbolicSplit n)).includePoint
            ((evenOrthogonalRootMorphism n hn r).onPoints (kPlusPoint a)))) = _
  rw [evenOrthogonalRootMorphism_include_apply]
  convert evenOrthogonalRootAmbientMorphism_linear_points (k := k) n r
    (kPlusPoint a) using 1 <;> rfl

public theorem evenOrthogonalRootPoint_diagonal_conjugation_torus (n : Nat)
    (hn : 4 ≤ n) (r : TypeDRootIndex n) (a : k)
    (s : Variety.Point (evenOrthogonalDiagonalTorus (k := k) n hn).carrierVariety) :
    letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
    ((evenOrthogonalDiagonalTorus (k := k) n hn).includePoint s)⁻¹ *
        (evenOrthogonalRootMorphism n hn r).onPoints (kPlusPoint a) *
          (evenOrthogonalDiagonalTorus (k := k) n hn).includePoint s =
      (evenOrthogonalRootMorphism n hn r).onPoints
        (kPlusPoint ((evenOrthogonalRootWeight (k := k) n hn r).pointCharacter s * a)) := by
  letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
  let x := evenOrthogonalDiagonalTorusPointEquiv (k := k) n hn s
  have hx : (evenOrthogonalDiagonalTorusIso (k := k) n hn).hom.onPoints x = s := by
    change (evenOrthogonalDiagonalTorusIso (k := k) n hn).hom.onPoints
        ((evenOrthogonalDiagonalTorusIso (k := k) n hn).inv.onPoints s) = s
    rw [(evenOrthogonalDiagonalTorusIso (k := k) n hn).inv_hom_id]
  have hi := evenOrthogonalDiagonalTorusIso_inclusion_hom (k := k) n hn x
  rw [hx] at hi
  let omegaPoints := evenSpinActionImageClosedSubgroupPoints
    (hyperbolicForm (k := k) n) (standardHyperbolicSplit n) (by simpa using hn)
  have hdiag :
      (omegaPoints
          ((evenOrthogonalDiagonalTorus (k := k) n hn).includePoint s)).1 =
        hyperbolicDiagonalPoint n (dPointEquiv n x) := by
    apply Subtype.ext
    rw [← evenSpinActionImageClosedSubgroup_linear_points]
    rw [show (evenOrthogonalDiagonalTorus (k := k) n hn).includePoint s =
        (evenOrthogonalDiagonalTorus (k := k) n hn).inclusion.onPoints s by rfl,
      hi]
    change LinearMap.GeneralLinearGroup.generalLinearEquiv k (HyperbolicSpace k n)
      (glPointEquivOf k (HyperbolicSpace k n)
        (Module.finBasis k (HyperbolicSpace k n))
        ((evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) n)
          (standardHyperbolicSplit n)).includePoint
            ((evenOrthogonalDiagonalMorphism n hn).onPoints x))) = _
    exact evenOrthogonalDiagonalMorphism_linear_points n hn x
  apply omegaPoints.injective
  rw [map_mul, map_mul, map_inv]
  apply Subtype.ext
  change (omegaPoints
        ((evenOrthogonalDiagonalTorus (k := k) n hn).includePoint s)).1⁻¹ *
      (omegaPoints
        ((evenOrthogonalRootMorphism n hn r).onPoints (kPlusPoint a))).1 *
      (omegaPoints
        ((evenOrthogonalDiagonalTorus (k := k) n hn).includePoint s)).1 =
    (omegaPoints
      ((evenOrthogonalRootMorphism n hn r).onPoints
        (kPlusPoint ((evenOrthogonalRootWeight (k := k) n hn r).pointCharacter s * a)))).1
  rw [hdiag, evenOrthogonalRootMorphism_quadratic_points,
    evenOrthogonalRootMorphism_quadratic_points,
    evenOrthogonalRootWeight_pointCharacter]
  exact evenOrthogonalRoot_diagonal_conjugation n r (dPointEquiv n x) a

public theorem evenOrthogonalRootWeight_equation (n : Nat) (hn : 4 ≤ n)
    (r : TypeDRootIndex n) :
    letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
    RootWeightEquation (evenOrthogonalDiagonalTorus (k := k) n hn)
      (evenOrthogonalRootSubgroup (k := k) n hn r)
      (evenOrthogonalRootWeight n hn r) := by
  letI := (evenOrthogonalDiagonalTorus (k := k) n hn).carrierAlgebraicGroup
  intro y t s
  let _ : AlgebraicGroup
      (evenOrthogonalRootSubgroup (k := k) n hn r).carrierVariety :=
    (evenOrthogonalRootSubgroup (k := k) n hn r).carrierAlgebraicGroup
  let p := evenOrthogonalRootParametrization (k := k) n hn r
  rcases oneParameterParametrization_eq_rescale p y with ⟨c, hc, _⟩
  rw [show (evenOrthogonalRootSubgroup (k := k) n hn r).includePoint
        (y.value t) =
      (evenOrthogonalRootMorphism n hn r).onPoints (kPlusPoint (c * t)) by
    rw [hc.2, evenOrthogonalRootParametrization_include_value]]
  rw [show (evenOrthogonalRootSubgroup (k := k) n hn r).includePoint
        (y.value ((evenOrthogonalRootWeight n hn r).pointCharacter s * t)) =
      (evenOrthogonalRootMorphism n hn r).onPoints
        (kPlusPoint (c * ((evenOrthogonalRootWeight n hn r).pointCharacter s * t))) by
    rw [hc.2, evenOrthogonalRootParametrization_include_value]]
  rw [evenOrthogonalRootPoint_diagonal_conjugation_torus]
  congr 2
  ring

end Theory.AlgebraicGroup
