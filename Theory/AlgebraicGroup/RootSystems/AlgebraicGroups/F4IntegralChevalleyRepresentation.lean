module

public import Theory.AlgebraicGroup.Borel.IntegralChevalleyTorusConjugation
public import Theory.AlgebraicGroup.RootSystems.F4RootPairing

/-!
# The integral Chevalley representation of type F4

This module specializes the integral Cartan-plus-root Chevalley lattice to the
standard F4 root pairing.  The lattice has one coordinate for each simple
coroot and each root.  Integral Tits transport supplies every root operator and
its divided powers; the operators are nilpotent of index at most four, so their
root curves are finite exponential formulas over every commutative ring.

The construction also records the exact additive and inverse laws for those
curves, all-root bracket and opposite-root rank-one relations, and the split
torus conjugation weights.  Nonvanishing of every F4 root operator follows from
the opposite-root action on the transported Cartan vector, giving the faithful
root-line certificate needed by the generated matrix carrier.  This is the
integral admissible-lattice construction used in Steinberg, *Lectures on
Chevalley Groups*, Theorem 1 and Lemmas 5--6; no abstract Serre quotient or
general Chevalley-group existence theorem is used.
-/

@[expose] public section

open scoped Matrix

namespace Theory.AlgebraicGroup.F4Chevalley

open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction

public abbrev Root := typeF4Roots

public noncomputable instance : Fintype Root := Fintype.ofFinite Root

public abbrev BasisIndex := typeF4RootPairing_base.support ⊕ Root
public abbrev IntegralLattice := BasisIndex → ℤ
public abbrev IntegralMatrix := Matrix BasisIndex BasisIndex ℤ

/-- The canonical integral Cartan-plus-root operators for the standard F4 datum. -/
public noncomputable def integralOperators :
    IntegralChevalleyRootOperators typeF4RootPairing typeF4RootPairing_base :=
  integralChevalleyRootOperators

public instance : Module.Free ℤ IntegralLattice := integralOperators.carrierFree
public instance : Module.Finite ℤ IntegralLattice := integralOperators.carrierFinite

private theorem transportedVector_ne_zero
    (word : List typeF4RootPairing_base.support)
    {x : IntegralLattice} (hx : x ≠ 0) :
    transportedVector (P := typeF4RootPairing) word x ≠ 0 := by
  intro h
  apply hx
  have h' := congrArg
    (fun y : IntegralLattice =>
      titsWordInv (P := typeF4RootPairing) word *ᵥ y) h
  simp only [transportedVector, Matrix.mulVec_zero] at h'
  have h'' :
      (titsWordInv (P := typeF4RootPairing) word *
          titsWord (P := typeF4RootPairing) word) *ᵥ x = 0 := by
    rw [← Matrix.mulVec_mulVec]
    exact h'
  rw [titsWord_inv_mul, Matrix.one_mulVec] at h''
  exact h''

private theorem rootCartanVector_ne_zero (r : Root) :
    integralOperators.rootCartanVector r ≠ 0 := by
  change rootCartanVector (P := typeF4RootPairing)
    (b := typeF4RootPairing_base) r ≠ 0
  apply transportedVector_ne_zero
  intro h
  have hcoord := congrFun h
    (Sum.inl (rootRoute (P := typeF4RootPairing)
      (b := typeF4RootPairing_base) r).simple)
  simp [u] at hcoord

/-- Every F4 root acts nontrivially on the integral lattice. -/
public theorem rootOperator_ne_zero (r : Root) :
    integralOperators.rootOperator r ≠ 0 := by
  let _ := typeF4RootPairing.indexNeg
  by_cases hr : typeF4RootPairing_base.IsPos r
  · intro h
    have happ := congrArg
      (fun A : IntegralMatrix => A *ᵥ integralOperators.rootVector (-r)) h
    rw [integralOperators.opposite_root_sl2 r hr |>.1] at happ
    exact rootCartanVector_ne_zero r (by simpa using happ)
  · have hneg : typeF4RootPairing_base.IsPos (-r) :=
      (RootPairing.Base.IsPos.neg_iff_not typeF4RootPairing_base r).mpr hr
    intro h
    have happ := congrArg
      (fun A : IntegralMatrix => A *ᵥ integralOperators.rootVector (-r)) h
    have hsl2 := (integralOperators.opposite_root_sl2 (-r) hneg).2.1
    have hsl2' :
        integralOperators.rootOperator r *ᵥ integralOperators.rootVector (-r) =
          integralOperators.rootCartanVector (-r) := by
      simpa only [neg_neg] using hsl2
    rw [hsl2'] at happ
    exact rootCartanVector_ne_zero (-r) (by simpa using happ)

/-- The root-line part of the integral representation is faithful. -/
public theorem faithfulRootAction :
    ∀ r : Root, integralOperators.rootOperator r ≠ 0 :=
  rootOperator_ne_zero

/-- The specialized root curve, defined by the finite divided-power exponential. -/
public noncomputable def rootCurve {S : Type*} [CommRing S]
    (r : Root) (t : S) : (Matrix BasisIndex BasisIndex S)ˣ :=
  rootCurveUnit integralOperators r t

/-- The underlying matrix is the explicit degree-three divided-power exponential. -/
public theorem rootCurve_matrix_formula {S : Type*} [CommRing S]
    (r : Root) (t : S) :
    (rootCurve r t : Matrix BasisIndex BasisIndex S) =
      1 + t • specializeMatrix (S := S) (integralOperators.rootDividedPower r 1) +
        t ^ 2 • specializeMatrix (S := S) (integralOperators.rootDividedPower r 2) +
        t ^ 3 • specializeMatrix (S := S) (integralOperators.rootDividedPower r 3) := by
  rfl

/-- Root curves satisfy the additive one-parameter law over every commutative ring. -/
public theorem rootCurve_add {S : Type*} [CommRing S]
    (r : Root) (s t : S) :
    rootCurve r (s + t) = rootCurve r s * rootCurve r t :=
  rootCurveUnit_add integralOperators r s t

@[simp] public theorem rootCurve_zero {S : Type*} [CommRing S] (r : Root) :
    rootCurve (S := S) r 0 = 1 := by
  apply Units.ext
  exact rootCurveMatrix_zero integralOperators r

/-- Negating the parameter gives the inverse root curve in every characteristic. -/
public theorem rootCurve_inv {S : Type*} [CommRing S]
    (r : Root) (t : S) :
    (rootCurve r t)⁻¹ = rootCurve r (-t) :=
  rootCurveUnit_inv integralOperators r t

public theorem dividedPower_zero (r : Root) :
    integralOperators.rootDividedPower r 0 = 1 :=
  integralOperators.dividedPower_zero r

public theorem dividedPower_one (r : Root) :
    integralOperators.rootDividedPower r 1 = integralOperators.rootOperator r :=
  integralOperators.dividedPower_one r

public theorem dividedPower_mul (r : Root) (m n : ℕ) :
    integralOperators.rootDividedPower r m * integralOperators.rootDividedPower r n =
      (m + n).choose m • integralOperators.rootDividedPower r (m + n) :=
  integralOperators.dividedPower_mul r m n

public theorem operator_pow_eq_factorial_smul (r : Root) (n : ℕ) :
    integralOperators.rootOperator r ^ n =
      n.factorial • integralOperators.rootDividedPower r n :=
  integralOperators.operator_pow_eq_factorial_smul r n

public theorem dividedPower_eq_zero_of_four_le (r : Root) (n : ℕ) (h : 4 ≤ n) :
    integralOperators.rootDividedPower r n = 0 :=
  integralOperators.dividedPower_eq_zero_of_four_le r n h

public theorem operator_isNilpotent (r : Root) :
    IsNilpotent (integralOperators.rootOperator r) :=
  integralOperators.operator_isNilpotent r

public theorem bracket_signed {i j k : Root}
    (h : typeF4RootPairing.root k = typeF4RootPairing.root i +
      typeF4RootPairing.root j) :
    ∃ ε : ℤ, ε * ε = 1 ∧
      integralOperators.rootOperator i *ᵥ integralOperators.rootVector j =
        (ε * (typeF4RootPairing.chainBotCoeff i j + 1 : ℤ)) •
          integralOperators.rootVector k :=
  integralOperators.bracket_signed h

public theorem bracket_absolute {i j k : Root}
    (h : typeF4RootPairing.root k = typeF4RootPairing.root i +
      typeF4RootPairing.root j) :
    ∃ c : ℤ, c.natAbs = typeF4RootPairing.chainBotCoeff i j + 1 ∧
      integralOperators.rootOperator i *ᵥ integralOperators.rootVector j =
        c • integralOperators.rootVector k :=
  integralOperators.bracket_absolute h

public theorem opposite_root_sl2 (i : Root)
    (hi : typeF4RootPairing_base.IsPos i) :
    letI := typeF4RootPairing.indexNeg
    integralOperators.rootOperator i *ᵥ integralOperators.rootVector (-i) =
        integralOperators.rootCartanVector i ∧
      integralOperators.rootOperator (-i) *ᵥ integralOperators.rootVector i =
        integralOperators.rootCartanVector i ∧
      integralOperators.rootOperator i *ᵥ integralOperators.rootCartanVector i =
        (2 : ℤ) • integralOperators.rootVector i ∧
      integralOperators.rootOperator (-i) *ᵥ integralOperators.rootCartanVector i =
        (2 : ℤ) • integralOperators.rootVector (-i) :=
  integralOperators.opposite_root_sl2 i hi

/-- The split-torus conjugation certificate after arbitrary base change. -/
public noncomputable def torusConjugation {S : Type*} [CommRing S] :
    IntegralChevalleyTorusConjugation
      typeF4RootPairing typeF4RootPairing_base S :=
  integralChevalleyTorusConjugation

/-- Conjugation scales an F4 root curve by its root character. -/
public theorem rootCurve_torus_conjugation {S : Type*} [CommRing S]
    (u : IntegralChevalleyTorusParameter (b := typeF4RootPairing_base) S)
    (r : Root) (t : S) :
    (torusConjugation.torusElement u)⁻¹ * rootCurve r t *
        torusConjugation.torusElement u =
      rootCurve r
        ((integralChevalleyRootScale (P := typeF4RootPairing) u r : S) * t) :=
  torusConjugation.rootCurve_conjugation u r t

/-- A simple-coroot coordinate acts with the Cartan pairing exponent. -/
public theorem rootCurve_simpleCoroot_conjugation {S : Type*} [CommRing S]
    (q : typeF4RootPairing_base.support) (u : Sˣ) (r : Root) (t : S) :
    (torusConjugation.torusElement
        (integralChevalleySimpleCorootParameter (b := typeF4RootPairing_base) q u))⁻¹ *
        rootCurve r t *
        torusConjugation.torusElement
          (integralChevalleySimpleCorootParameter (b := typeF4RootPairing_base) q u) =
      rootCurve r (((u ^ typeF4RootPairing.pairingIn ℤ r q : Sˣ) : S) * t) :=
  torusConjugation.simpleCoroot_conjugation q u r t

/-- The complete checked integral representation package consumed by F4 carriers. -/
public structure IntegralModel where
  operators : IntegralChevalleyRootOperators
    typeF4RootPairing typeF4RootPairing_base
  operators_eq : operators = integralOperators
  rootAction_faithful : ∀ r : Root, operators.rootOperator r ≠ 0
  torus : ∀ (S : Type*) [CommRing S],
    IntegralChevalleyTorusConjugation
      typeF4RootPairing typeF4RootPairing_base S

/-- The canonical checked F4 integral model. -/
public noncomputable def integralModel : IntegralModel where
  operators := integralOperators
  operators_eq := rfl
  rootAction_faithful := faithfulRootAction
  torus := fun _ _ => torusConjugation

public noncomputable def typeF4IntegralChevalleyModel : IntegralModel := integralModel

/-- A faithful admissible integral Chevalley representation exists for the standard F4 datum. -/
public theorem typeF4_integralChevalleyRepresentation_exists : Nonempty IntegralModel :=
  ⟨typeF4IntegralChevalleyModel⟩

end Theory.AlgebraicGroup.F4Chevalley
