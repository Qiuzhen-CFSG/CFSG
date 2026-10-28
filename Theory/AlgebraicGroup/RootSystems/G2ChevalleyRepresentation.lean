module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Integer
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.NormNum
public meta import Mathlib.Data.Matrix.Basic

/-!
# An integral Chevalley representation of type G2

This module constructs the fourteen-dimensional integral Chevalley lattice of type `G2`: two
Cartan basis vectors and one basis vector for each of the twelve roots.  The root operators and
their second and third divided powers are given by sparse integral tables.  Finite calculations
over `ℤ` certify the divided-power identities and conjugation by the two simple Weyl operators.
Consequently the cubic root curves specialize over every commutative ring, including rings of
characteristic two and three, without dividing in the coefficient ring.

The construction follows the Chevalley-basis method in Steinberg, *Lectures on Chevalley Groups*,
Theorem 1 and the discussion of the integral lattice following it; see also GLS3, Remark 1.12.10.
The signs are the normalization obtained from Geck's integral simple-root operators.  The public
interface supplies the lattice, root operators, divided powers, Weyl relations, scalar extension,
root curves, diagonal torus, and their generated subgroup.  It deliberately does not depend on a
geometric `G2` carrier or on root-version classification.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace Theory.AlgebraicGroup.G2Chevalley

/-- The twelve roots, ordered as the six positive roots followed by their negatives. -/
public abbrev Root := Fin 12

namespace Root

public def short : Root := 0
public def long : Root := 1
public def shortLong : Root := 2
public def twoShortLong : Root := 3
public def threeShortLong : Root := 4
public def threeShortTwoLong : Root := 5
public def negShort : Root := 6
public def negLong : Root := 7
public def negShortLong : Root := 8
public def negTwoShortLong : Root := 9
public def negThreeShortLong : Root := 10
public def negThreeShortTwoLong : Root := 11

/-- Coordinates in the basis consisting of a short root followed by a long root. -/
public def coord : Root → ℤ × ℤ
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (1, 1)
  | 3 => (2, 1)
  | 4 => (3, 1)
  | 5 => (3, 2)
  | 6 => (-1, 0)
  | 7 => (0, -1)
  | 8 => (-1, -1)
  | 9 => (-2, -1)
  | 10 => (-3, -1)
  | 11 => (-3, -2)

public def neg : Root → Root
  | 0 => 6
  | 1 => 7
  | 2 => 8
  | 3 => 9
  | 4 => 10
  | 5 => 11
  | 6 => 0
  | 7 => 1
  | 8 => 2
  | 9 => 3
  | 10 => 4
  | 11 => 5

public instance : Neg Root := ⟨Root.neg⟩

@[simp] public theorem neg_neg (r : Root) : - -r = r := by
  fin_cases r <;> rfl

end Root

/-- The short and long simple roots. -/
public def simpleRoot : Fin 2 → Root
  | 0 => Root.short
  | 1 => Root.long

/-- Pairing of a root with the short and long simple coroots. -/
public def Root.pairingSimple : Root → Fin 2 → ℤ
  | r, 0 => 2 * r.coord.1 - 3 * r.coord.2
  | r, 1 => -r.coord.1 + 2 * r.coord.2

/-- The integral Chevalley basis, with coordinates `0,1` for the Cartan part and `r+2` for a root. -/
public abbrev Basis := Fin 14

/-- The inclusion of the two Cartan basis vectors in the Chevalley basis. -/
public def cartanBasis (i : Fin 2) : Basis := ⟨i.val, by omega⟩

/-- The inclusion of a root vector in the Chevalley basis. -/
public def rootBasis (r : Root) : Basis := ⟨r.val + 2, by omega⟩

/-- Integral endomorphisms of the Chevalley lattice. -/
public abbrev IntegralMatrix := Matrix Basis Basis ℤ

/-- Form a sparse integral matrix from `(row, column, coefficient)` entries. -/
public def matrixOfEntries (entries : List (ℕ × ℕ × ℤ)) : IntegralMatrix := fun row col =>
  entries.foldr
    (fun e value => if row.val = e.1 ∧ col.val = e.2.1 then e.2.2 else value) 0

/-- The two simple reflections on the chosen root enumeration. -/
public def simpleReflection : Fin 2 → Root → Root
  | 0, 0 => 6
  | 0, 1 => 4
  | 0, 2 => 3
  | 0, 3 => 2
  | 0, 4 => 1
  | 0, 5 => 5
  | 0, 6 => 0
  | 0, 7 => 10
  | 0, 8 => 9
  | 0, 9 => 8
  | 0, 10 => 7
  | 0, 11 => 11
  | 1, 0 => 2
  | 1, 1 => 7
  | 1, 2 => 0
  | 1, 3 => 3
  | 1, 4 => 5
  | 1, 5 => 4
  | 1, 6 => 8
  | 1, 7 => 1
  | 1, 8 => 6
  | 1, 9 => 9
  | 1, 10 => 11
  | 1, 11 => 10

/-- Sparse tables for the simple Weyl operators on the Cartan and root coordinates. -/
public def weylEntries : Fin 2 → List (ℕ × ℕ × ℤ)
  | 0 => [(0, 0, -1), (0, 1, -1), (1, 1, 1),
      (8, 2, 1), (6, 3, 1), (5, 4, -1), (4, 5, 1), (3, 6, -1), (7, 7, 1),
      (2, 8, 1), (12, 9, -1), (11, 10, 1), (10, 11, -1), (9, 12, 1), (13, 13, 1)]
  | 1 => [(0, 0, 1), (1, 0, -3), (1, 1, -1),
      (4, 2, 1), (9, 3, 1), (2, 4, -1), (5, 5, 1), (7, 6, 1), (6, 7, -1),
      (10, 8, -1), (3, 9, 1), (8, 10, 1), (11, 11, 1), (13, 12, -1), (12, 13, 1)]

/-- Sparse tables for the inverse simple Weyl operators. -/
public def weylInvEntries : Fin 2 → List (ℕ × ℕ × ℤ)
  | 0 => [(0, 0, -1), (0, 1, -1), (1, 1, 1),
      (8, 2, 1), (6, 3, -1), (5, 4, 1), (4, 5, -1), (3, 6, 1), (7, 7, 1),
      (2, 8, 1), (12, 9, 1), (11, 10, -1), (10, 11, 1), (9, 12, -1), (13, 13, 1)]
  | 1 => [(0, 0, 1), (1, 0, -3), (1, 1, -1),
      (4, 2, -1), (9, 3, 1), (2, 4, 1), (5, 5, 1), (7, 6, -1), (6, 7, 1),
      (10, 8, 1), (3, 9, 1), (8, 10, -1), (11, 11, 1), (13, 12, 1), (12, 13, -1)]

/-- The integral operator representing a simple Weyl reflection. -/
public def weyl (i : Fin 2) : IntegralMatrix := matrixOfEntries (weylEntries i)

/-- The inverse integral operator to `weyl`. -/
public def weylInv (i : Fin 2) : IntegralMatrix := matrixOfEntries (weylInvEntries i)

/-- Signs in the Weyl conjugation formula for the chosen root-vector normalization. -/
public def weylRootSign : Fin 2 → Root → ℤ
  | 0, 0 => 1
  | 0, 1 => 1
  | 0, 2 => 1
  | 0, 3 => -1
  | 0, 4 => -1
  | 0, 5 => 1
  | 0, 6 => 1
  | 0, 7 => 1
  | 0, 8 => 1
  | 0, 9 => -1
  | 0, 10 => -1
  | 0, 11 => 1
  | 1, 0 => 1
  | 1, 1 => 1
  | 1, 2 => -1
  | 1, 3 => 1
  | 1, 4 => 1
  | 1, 5 => -1
  | 1, 6 => 1
  | 1, 7 => 1
  | 1, 8 => -1
  | 1, 9 => 1
  | 1, 10 => 1
  | 1, 11 => -1

public def rootOperatorEntries : Root → List (ℕ × ℕ × ℤ)
  | 0 => [(0, 8, 1), (2, 0, 2), (2, 1, 1), (4, 3, 1), (5, 4, 2),
      (6, 5, 3), (9, 10, 3), (10, 11, 2), (11, 12, 1)]
  | 1 => [(1, 9, 1), (3, 0, 3), (3, 1, 2), (4, 2, 1), (7, 6, 1),
      (8, 10, 1), (12, 13, 1)]
  | 2 => [(0, 10, 1), (1, 10, -3), (2, 9, 1), (3, 8, -3), (4, 0, 1),
      (4, 1, 1), (5, 2, 2), (7, 5, -3), (8, 11, -2), (11, 13, 1)]
  | 3 => [(0, 11, -2), (1, 11, 3), (2, 10, -2), (4, 8, -2), (5, 0, -1),
      (6, 2, 3), (7, 4, 3), (8, 12, 1), (10, 13, 1)]
  | 4 => [(0, 12, -1), (1, 12, 1), (2, 11, -1), (5, 8, 1), (6, 0, 3),
      (6, 1, 1), (7, 3, 1), (9, 13, -1)]
  | 5 => [(0, 13, -1), (1, 13, 2), (3, 12, 1), (4, 11, 1), (5, 10, 1),
      (6, 9, 1), (7, 1, 1)]
  | 6 => [(0, 2, -1), (3, 4, -3), (4, 5, -2), (5, 6, -1), (8, 0, -2),
      (8, 1, -1), (10, 9, -1), (11, 10, -2), (12, 11, -3)]
  | 7 => [(1, 3, -1), (2, 4, -1), (6, 7, -1), (9, 0, -3), (9, 1, -2),
      (10, 8, -1), (13, 12, -1)]
  | 8 => [(0, 4, 1), (1, 4, -3), (2, 5, -2), (5, 7, 1), (8, 3, 1),
      (9, 2, -3), (10, 0, 1), (10, 1, 1), (11, 8, 2), (13, 11, -3)]
  | 9 => [(0, 5, 2), (1, 5, -3), (2, 6, -1), (4, 7, -1), (8, 4, 2),
      (10, 2, 2), (11, 0, 1), (12, 8, -3), (13, 10, -3)]
  | 10 => [(0, 6, -1), (1, 6, 1), (3, 7, -1), (8, 5, -1), (11, 2, 1),
      (12, 0, 3), (12, 1, 1), (13, 9, 1)]
  | 11 => [(0, 7, 1), (1, 7, -2), (9, 6, -1), (10, 5, -1), (11, 4, -1),
      (12, 3, -1), (13, 1, -1)]

/-- The twelve Chevalley root operators on the integral lattice. -/
public def rootOperator (r : Root) : IntegralMatrix :=
  matrixOfEntries (rootOperatorEntries r)

public def rootDividedPowerTwoEntries : Root → List (ℕ × ℕ × ℤ)
  | 0 => [(2, 8, 1), (5, 3, 1), (6, 4, 3), (9, 11, 3), (10, 12, 1)]
  | 1 => [(3, 9, 1)]
  | 2 => [(3, 11, 3), (4, 10, -1), (5, 9, 1), (7, 2, -3), (8, 13, -1)]
  | 3 => [(2, 13, -1), (4, 12, -1), (5, 11, 1), (6, 10, -3), (7, 8, -3)]
  | 4 => [(6, 12, -1)]
  | 5 => [(7, 13, 1)]
  | 6 => [(3, 5, 3), (4, 6, 1), (8, 2, 1), (11, 9, 1), (12, 10, 3)]
  | 7 => [(9, 3, 1)]
  | 8 => [(2, 7, -1), (9, 5, 3), (10, 4, -1), (11, 3, 1), (13, 8, -3)]
  | 9 => [(8, 7, -1), (10, 6, -1), (11, 5, 1), (12, 4, -3), (13, 2, -3)]
  | 10 => [(12, 6, -1)]
  | 11 => [(13, 7, 1)]

public def rootDividedPowerThreeEntries : Root → List (ℕ × ℕ × ℤ)
  | 0 => [(6, 3, 1), (9, 12, 1)]
  | 2 => [(3, 13, 1), (7, 9, -1)]
  | 3 => [(6, 13, -1), (7, 12, -1)]
  | 6 => [(3, 6, -1), (12, 9, -1)]
  | 8 => [(9, 7, 1), (13, 3, -1)]
  | 9 => [(12, 7, 1), (13, 6, 1)]
  | _ => []

/-- The zeroth through third integral divided powers of a root operator. -/
public def rootDividedPower (r : Root) (m : Fin 4) : IntegralMatrix :=
  match m with
  | 0 => 1
  | 1 => rootOperator r
  | 2 => matrixOfEntries (rootDividedPowerTwoEntries r)
  | 3 => matrixOfEntries (rootDividedPowerThreeEntries r)

public theorem rootDividedPower_zero (r : Root) : rootDividedPower r 0 = 1 := rfl
public theorem rootDividedPower_one (r : Root) : rootDividedPower r 1 = rootOperator r := rfl

public theorem weyl_mul_inv (i : Fin 2) : weyl i * weylInv i = 1 := by
  fin_cases i <;> decide

public theorem weyl_inv_mul (i : Fin 2) : weylInv i * weyl i = 1 := by
  fin_cases i <;> decide

/-- Relations characterizing the three nonconstant divided powers of a cubic root curve. -/
public def CubicRelations (X1 X2 X3 : IntegralMatrix) : Prop :=
  X1 * X1 = (2 : ℤ) • X2 ∧
  X1 * X2 = (3 : ℤ) • X3 ∧
  X2 * X1 = (3 : ℤ) • X3 ∧
  X1 * X3 = 0 ∧ X3 * X1 = 0 ∧ X2 * X2 = 0 ∧
  X2 * X3 = 0 ∧ X3 * X2 = 0 ∧ X3 * X3 = 0

/-- The four integral identities from which all cubic relations follow. -/
public def CoreCubicRelations (X1 X2 X3 : IntegralMatrix) : Prop :=
  X1 * X1 = (2 : ℤ) • X2 ∧
  X1 * X2 = (3 : ℤ) • X3 ∧
  X2 * X1 = (3 : ℤ) • X3 ∧
  X2 * X2 = 0

private lemma int_smul_eq_zero (n : ℤ) (hn : n ≠ 0) (A : IntegralMatrix)
    (h : n • A = 0) : A = 0 := by
  ext i j
  have hij := congrFun (congrFun h i) j
  change n * A i j = 0 at hij
  exact (mul_eq_zero.mp hij).resolve_left hn

private lemma cubicRelations_of_core (X1 X2 X3 : IntegralMatrix)
    (h11 : X1 * X1 = (2 : ℤ) • X2)
    (h12 : X1 * X2 = (3 : ℤ) • X3)
    (h21 : X2 * X1 = (3 : ℤ) • X3)
    (h22 : X2 * X2 = 0) : CubicRelations X1 X2 X3 := by
  have h13s : (3 : ℤ) • (X1 * X3) = 0 := by
    calc
      (3 : ℤ) • (X1 * X3) = X1 * ((3 : ℤ) • X3) := by noncomm_ring
      _ = X1 * (X1 * X2) := by rw [h12]
      _ = (X1 * X1) * X2 := by rw [mul_assoc]
      _ = ((2 : ℤ) • X2) * X2 := by rw [h11]
      _ = 0 := by rw [smul_mul_assoc, h22, smul_zero]
  have h13 := int_smul_eq_zero 3 (by norm_num) _ h13s
  have h31s : (3 : ℤ) • (X3 * X1) = 0 := by
    calc
      (3 : ℤ) • (X3 * X1) = ((3 : ℤ) • X3) * X1 := by noncomm_ring
      _ = (X2 * X1) * X1 := by rw [h21]
      _ = X2 * (X1 * X1) := by rw [mul_assoc]
      _ = X2 * ((2 : ℤ) • X2) := by rw [h11]
      _ = 0 := by rw [mul_smul_comm, h22, smul_zero]
  have h31 := int_smul_eq_zero 3 (by norm_num) _ h31s
  have h23s : (3 : ℤ) • (X2 * X3) = 0 := by
    calc
      (3 : ℤ) • (X2 * X3) = X2 * ((3 : ℤ) • X3) := by noncomm_ring
      _ = X2 * (X2 * X1) := by rw [h21]
      _ = (X2 * X2) * X1 := by rw [mul_assoc]
      _ = 0 := by rw [h22, zero_mul]
  have h23 := int_smul_eq_zero 3 (by norm_num) _ h23s
  have h32s : (3 : ℤ) • (X3 * X2) = 0 := by
    calc
      (3 : ℤ) • (X3 * X2) = ((3 : ℤ) • X3) * X2 := by noncomm_ring
      _ = (X1 * X2) * X2 := by rw [h12]
      _ = X1 * (X2 * X2) := by rw [mul_assoc]
      _ = 0 := by rw [h22, mul_zero]
  have h32 := int_smul_eq_zero 3 (by norm_num) _ h32s
  have h33s : (3 : ℤ) • (X3 * X3) = 0 := by
    calc
      (3 : ℤ) • (X3 * X3) = X3 * ((3 : ℤ) • X3) := by noncomm_ring
      _ = X3 * (X1 * X2) := by rw [h12]
      _ = (X3 * X1) * X2 := by rw [mul_assoc]
      _ = 0 := by rw [h31, zero_mul]
  have h33 := int_smul_eq_zero 3 (by norm_num) _ h33s
  exact ⟨h11, h12, h21, h13, h31, h22, h23, h32, h33⟩

set_option maxHeartbeats 0 in
private theorem rootCoreRelations0 : CoreCubicRelations
    (rootDividedPower 0 1) (rootDividedPower 0 2) (rootDividedPower 0 3) := by
  unfold CoreCubicRelations
  decide

set_option maxHeartbeats 0 in
private theorem rootCoreRelations1 : CoreCubicRelations
    (rootDividedPower 1 1) (rootDividedPower 1 2) (rootDividedPower 1 3) := by
  unfold CoreCubicRelations
  decide

set_option maxHeartbeats 0 in
private theorem rootCoreRelations2 : CoreCubicRelations
    (rootDividedPower 2 1) (rootDividedPower 2 2) (rootDividedPower 2 3) := by
  unfold CoreCubicRelations
  decide

set_option maxHeartbeats 0 in
private theorem rootCoreRelations3 : CoreCubicRelations
    (rootDividedPower 3 1) (rootDividedPower 3 2) (rootDividedPower 3 3) := by
  unfold CoreCubicRelations
  decide

set_option maxHeartbeats 0 in
private theorem rootCoreRelations4 : CoreCubicRelations
    (rootDividedPower 4 1) (rootDividedPower 4 2) (rootDividedPower 4 3) := by
  unfold CoreCubicRelations
  decide

set_option maxHeartbeats 0 in
private theorem rootCoreRelations5 : CoreCubicRelations
    (rootDividedPower 5 1) (rootDividedPower 5 2) (rootDividedPower 5 3) := by
  unfold CoreCubicRelations
  decide

set_option maxHeartbeats 0 in
private theorem rootCoreRelations6 : CoreCubicRelations
    (rootDividedPower 6 1) (rootDividedPower 6 2) (rootDividedPower 6 3) := by
  unfold CoreCubicRelations
  decide

set_option maxHeartbeats 0 in
private theorem rootCoreRelations7 : CoreCubicRelations
    (rootDividedPower 7 1) (rootDividedPower 7 2) (rootDividedPower 7 3) := by
  unfold CoreCubicRelations
  decide

set_option maxHeartbeats 0 in
private theorem rootCoreRelations8 : CoreCubicRelations
    (rootDividedPower 8 1) (rootDividedPower 8 2) (rootDividedPower 8 3) := by
  unfold CoreCubicRelations
  decide

set_option maxHeartbeats 0 in
private theorem rootCoreRelations9 : CoreCubicRelations
    (rootDividedPower 9 1) (rootDividedPower 9 2) (rootDividedPower 9 3) := by
  unfold CoreCubicRelations
  decide

set_option maxHeartbeats 0 in
private theorem rootCoreRelations10 : CoreCubicRelations
    (rootDividedPower 10 1) (rootDividedPower 10 2) (rootDividedPower 10 3) := by
  unfold CoreCubicRelations
  decide

set_option maxHeartbeats 0 in
private theorem rootCoreRelations11 : CoreCubicRelations
    (rootDividedPower 11 1) (rootDividedPower 11 2) (rootDividedPower 11 3) := by
  unfold CoreCubicRelations
  decide

public theorem rootCoreRelations (r : Root) :
    CoreCubicRelations (rootDividedPower r 1) (rootDividedPower r 2)
      (rootDividedPower r 3) := by
  fin_cases r
  · exact rootCoreRelations0
  · exact rootCoreRelations1
  · exact rootCoreRelations2
  · exact rootCoreRelations3
  · exact rootCoreRelations4
  · exact rootCoreRelations5
  · exact rootCoreRelations6
  · exact rootCoreRelations7
  · exact rootCoreRelations8
  · exact rootCoreRelations9
  · exact rootCoreRelations10
  · exact rootCoreRelations11

public theorem rootCubicRelations (r : Root) :
    CubicRelations (rootDividedPower r 1) (rootDividedPower r 2)
      (rootDividedPower r 3) := by
  rcases rootCoreRelations r with ⟨h11, h12, h21, h22⟩
  exact cubicRelations_of_core _ _ _ h11 h12 h21 h22

public theorem rootOperator_pow_four (r : Root) : rootOperator r ^ 4 = 0 := by
  rcases rootCubicRelations r with ⟨h11, _, _, _, _, h22, _⟩
  change rootDividedPower r 1 ^ 4 = 0
  noncomm_ring [h11, h22]

/-- The degree-one Weyl conjugation relation. -/
public def WeylRootOperatorRelation (i : Fin 2) (r : Root) : Prop :=
  weylInv i * rootOperator r * weyl i =
    weylRootSign i r • rootOperator (simpleReflection i r)

set_option maxHeartbeats 0 in
private theorem weylRootOperator00 : WeylRootOperatorRelation 0 0 := by
  unfold WeylRootOperatorRelation
  decide

set_option maxHeartbeats 0 in
private theorem weylRootOperator01 : WeylRootOperatorRelation 0 1 := by
  unfold WeylRootOperatorRelation
  decide

set_option maxHeartbeats 0 in
private theorem weylRootOperator02 : WeylRootOperatorRelation 0 2 := by
  unfold WeylRootOperatorRelation
  decide

set_option maxHeartbeats 0 in
private theorem weylRootOperator03 : WeylRootOperatorRelation 0 3 := by
  unfold WeylRootOperatorRelation
  decide

set_option maxHeartbeats 0 in
private theorem weylRootOperator04 : WeylRootOperatorRelation 0 4 := by
  unfold WeylRootOperatorRelation
  decide

set_option maxHeartbeats 0 in
private theorem weylRootOperator05 : WeylRootOperatorRelation 0 5 := by
  unfold WeylRootOperatorRelation
  decide

set_option maxHeartbeats 0 in
private theorem weylRootOperator06 : WeylRootOperatorRelation 0 6 := by
  unfold WeylRootOperatorRelation
  decide

set_option maxHeartbeats 0 in
private theorem weylRootOperator07 : WeylRootOperatorRelation 0 7 := by
  unfold WeylRootOperatorRelation
  decide

set_option maxHeartbeats 0 in
private theorem weylRootOperator08 : WeylRootOperatorRelation 0 8 := by
  unfold WeylRootOperatorRelation
  decide

set_option maxHeartbeats 0 in
private theorem weylRootOperator09 : WeylRootOperatorRelation 0 9 := by
  unfold WeylRootOperatorRelation
  decide

set_option maxHeartbeats 0 in
private theorem weylRootOperator010 : WeylRootOperatorRelation 0 10 := by
  unfold WeylRootOperatorRelation
  decide

set_option maxHeartbeats 0 in
private theorem weylRootOperator011 : WeylRootOperatorRelation 0 11 := by
  unfold WeylRootOperatorRelation
  decide

set_option maxHeartbeats 0 in
private theorem weylRootOperator10 : WeylRootOperatorRelation 1 0 := by
  unfold WeylRootOperatorRelation
  decide

set_option maxHeartbeats 0 in
private theorem weylRootOperator11 : WeylRootOperatorRelation 1 1 := by
  unfold WeylRootOperatorRelation
  decide

set_option maxHeartbeats 0 in
private theorem weylRootOperator12 : WeylRootOperatorRelation 1 2 := by
  unfold WeylRootOperatorRelation
  decide

set_option maxHeartbeats 0 in
private theorem weylRootOperator13 : WeylRootOperatorRelation 1 3 := by
  unfold WeylRootOperatorRelation
  decide

set_option maxHeartbeats 0 in
private theorem weylRootOperator14 : WeylRootOperatorRelation 1 4 := by
  unfold WeylRootOperatorRelation
  decide

set_option maxHeartbeats 0 in
private theorem weylRootOperator15 : WeylRootOperatorRelation 1 5 := by
  unfold WeylRootOperatorRelation
  decide

set_option maxHeartbeats 0 in
private theorem weylRootOperator16 : WeylRootOperatorRelation 1 6 := by
  unfold WeylRootOperatorRelation
  decide

set_option maxHeartbeats 0 in
private theorem weylRootOperator17 : WeylRootOperatorRelation 1 7 := by
  unfold WeylRootOperatorRelation
  decide

set_option maxHeartbeats 0 in
private theorem weylRootOperator18 : WeylRootOperatorRelation 1 8 := by
  unfold WeylRootOperatorRelation
  decide

set_option maxHeartbeats 0 in
private theorem weylRootOperator19 : WeylRootOperatorRelation 1 9 := by
  unfold WeylRootOperatorRelation
  decide

set_option maxHeartbeats 0 in
private theorem weylRootOperator110 : WeylRootOperatorRelation 1 10 := by
  unfold WeylRootOperatorRelation
  decide

set_option maxHeartbeats 0 in
private theorem weylRootOperator111 : WeylRootOperatorRelation 1 11 := by
  unfold WeylRootOperatorRelation
  decide

public theorem weyl_rootOperator (i : Fin 2) (r : Root) : WeylRootOperatorRelation i r := by
  fin_cases i <;> fin_cases r
  · exact weylRootOperator00
  · exact weylRootOperator01
  · exact weylRootOperator02
  · exact weylRootOperator03
  · exact weylRootOperator04
  · exact weylRootOperator05
  · exact weylRootOperator06
  · exact weylRootOperator07
  · exact weylRootOperator08
  · exact weylRootOperator09
  · exact weylRootOperator010
  · exact weylRootOperator011
  · exact weylRootOperator10
  · exact weylRootOperator11
  · exact weylRootOperator12
  · exact weylRootOperator13
  · exact weylRootOperator14
  · exact weylRootOperator15
  · exact weylRootOperator16
  · exact weylRootOperator17
  · exact weylRootOperator18
  · exact weylRootOperator19
  · exact weylRootOperator110
  · exact weylRootOperator111

private lemma int_smul_left_cancel (n : ℤ) (hn : n ≠ 0)
    {A B : IntegralMatrix} (h : n • A = n • B) : A = B := by
  ext i j
  have hij := congrFun (congrFun h i) j
  change n * A i j = n * B i j at hij
  exact mul_left_cancel₀ hn hij

private lemma conjugate_dividedPowers_pos (W Winv X D2 D3 Y E2 E3 : IntegralMatrix)
    (hW : W * Winv = 1) (hX : Winv * X * W = Y)
    (h11 : X * X = (2 : ℤ) • D2) (h11' : Y * Y = (2 : ℤ) • E2)
    (h12 : X * D2 = (3 : ℤ) • D3) (h12' : Y * E2 = (3 : ℤ) • E3) :
    Winv * D2 * W = E2 ∧ Winv * D3 * W = E3 := by
  have h2s : (2 : ℤ) • (Winv * D2 * W) = (2 : ℤ) • E2 := by
    calc
      (2 : ℤ) • (Winv * D2 * W) = Winv * ((2 : ℤ) • D2) * W := by noncomm_ring
      _ = Winv * (X * X) * W := by rw [h11]
      _ = (Winv * X * W) * (Winv * X * W) := by
        symm
        calc
          (Winv * X * W) * (Winv * X * W) =
              Winv * X * (W * Winv) * X * W := by noncomm_ring
          _ = Winv * (X * X) * W := by rw [hW]; noncomm_ring
      _ = Y * Y := by rw [hX]
      _ = (2 : ℤ) • E2 := h11'
  have h2 := int_smul_left_cancel 2 (by norm_num) h2s
  have h3s : (3 : ℤ) • (Winv * D3 * W) = (3 : ℤ) • E3 := by
    calc
      (3 : ℤ) • (Winv * D3 * W) = Winv * ((3 : ℤ) • D3) * W := by noncomm_ring
      _ = Winv * (X * D2) * W := by rw [h12]
      _ = (Winv * X * W) * (Winv * D2 * W) := by
        symm
        calc
          (Winv * X * W) * (Winv * D2 * W) =
              Winv * X * (W * Winv) * D2 * W := by noncomm_ring
          _ = Winv * (X * D2) * W := by rw [hW]; noncomm_ring
      _ = Y * E2 := by rw [hX, h2]
      _ = (3 : ℤ) • E3 := h12'
  exact ⟨h2, int_smul_left_cancel 3 (by norm_num) h3s⟩

private lemma conjugate_dividedPowers_neg (W Winv X D2 D3 Y E2 E3 : IntegralMatrix)
    (hW : W * Winv = 1) (hX : Winv * X * W = -Y)
    (h11 : X * X = (2 : ℤ) • D2) (h11' : Y * Y = (2 : ℤ) • E2)
    (h12 : X * D2 = (3 : ℤ) • D3) (h12' : Y * E2 = (3 : ℤ) • E3) :
    Winv * D2 * W = E2 ∧ Winv * D3 * W = -E3 := by
  have h2s : (2 : ℤ) • (Winv * D2 * W) = (2 : ℤ) • E2 := by
    calc
      (2 : ℤ) • (Winv * D2 * W) = Winv * ((2 : ℤ) • D2) * W := by noncomm_ring
      _ = Winv * (X * X) * W := by rw [h11]
      _ = (Winv * X * W) * (Winv * X * W) := by
        symm
        calc
          (Winv * X * W) * (Winv * X * W) =
              Winv * X * (W * Winv) * X * W := by noncomm_ring
          _ = Winv * (X * X) * W := by rw [hW]; noncomm_ring
      _ = (-Y) * (-Y) := by rw [hX]
      _ = Y * Y := by noncomm_ring
      _ = (2 : ℤ) • E2 := h11'
  have h2 := int_smul_left_cancel 2 (by norm_num) h2s
  have h3s : (3 : ℤ) • (Winv * D3 * W) = (3 : ℤ) • (-E3) := by
    calc
      (3 : ℤ) • (Winv * D3 * W) = Winv * ((3 : ℤ) • D3) * W := by noncomm_ring
      _ = Winv * (X * D2) * W := by rw [h12]
      _ = (Winv * X * W) * (Winv * D2 * W) := by
        symm
        calc
          (Winv * X * W) * (Winv * D2 * W) =
              Winv * X * (W * Winv) * D2 * W := by noncomm_ring
          _ = Winv * (X * D2) * W := by rw [hW]; noncomm_ring
      _ = (-Y) * E2 := by rw [hX, h2]
      _ = (3 : ℤ) • (-E3) := by noncomm_ring [h12']
  exact ⟨h2, int_smul_left_cancel 3 (by norm_num) h3s⟩

private theorem weyl_higher_dividedPowers (i : Fin 2) (r : Root) :
    weylInv i * rootDividedPower r 2 * weyl i =
        (weylRootSign i r ^ 2) • rootDividedPower (simpleReflection i r) 2 ∧
      weylInv i * rootDividedPower r 3 * weyl i =
        (weylRootSign i r ^ 3) • rootDividedPower (simpleReflection i r) 3 := by
  rcases rootCoreRelations r with ⟨h11, h12, _, _⟩
  rcases rootCoreRelations (simpleReflection i r) with ⟨h11', h12', _, _⟩
  have hs : weylRootSign i r = 1 ∨ weylRootSign i r = -1 := by
    fin_cases i <;> fin_cases r <;> simp [weylRootSign]
  rcases hs with hs | hs
  · have hX : weylInv i * rootOperator r * weyl i =
        rootOperator (simpleReflection i r) := by
      simpa [WeylRootOperatorRelation, hs] using weyl_rootOperator i r
    have h := conjugate_dividedPowers_pos
      (weyl i) (weylInv i)
      (rootDividedPower r 1) (rootDividedPower r 2) (rootDividedPower r 3)
      (rootDividedPower (simpleReflection i r) 1)
      (rootDividedPower (simpleReflection i r) 2)
      (rootDividedPower (simpleReflection i r) 3)
      (weyl_mul_inv i) (by simpa [rootDividedPower_one] using hX)
      h11 h11' h12 h12'
    simpa [hs] using h
  · have hX : weylInv i * rootOperator r * weyl i =
        -rootOperator (simpleReflection i r) := by
      simpa [WeylRootOperatorRelation, hs] using weyl_rootOperator i r
    have h := conjugate_dividedPowers_neg
      (weyl i) (weylInv i)
      (rootDividedPower r 1) (rootDividedPower r 2) (rootDividedPower r 3)
      (rootDividedPower (simpleReflection i r) 1)
      (rootDividedPower (simpleReflection i r) 2)
      (rootDividedPower (simpleReflection i r) 3)
      (weyl_mul_inv i) (by simpa [rootDividedPower_one] using hX)
      h11 h11' h12 h12'
    simpa [hs] using h

public theorem weyl_dividedPower (i : Fin 2) (r : Root) (m : Fin 4) :
    weylInv i * rootDividedPower r m * weyl i =
      (weylRootSign i r ^ m.val) •
        rootDividedPower (simpleReflection i r) m := by
  fin_cases m
  · simpa [rootDividedPower] using weyl_inv_mul i
  · simpa [rootDividedPower, WeylRootOperatorRelation] using weyl_rootOperator i r
  · simpa [rootDividedPower] using (weyl_higher_dividedPowers i r).1
  · simpa [rootDividedPower] using (weyl_higher_dividedPowers i r).2

/-- Scalar extension of an integral endomorphism to an arbitrary ring. -/
public def specialize {R : Type*} [Ring R] (A : IntegralMatrix) : Matrix Basis Basis R :=
  A.map (Int.castRingHom R)

public lemma specialize_mul {R : Type*} [Ring R] (A B : IntegralMatrix) :
    specialize (R := R) (A * B) =
      specialize (R := R) A * specialize (R := R) B := by
  exact Matrix.map_mul_intCast A B

public lemma specialize_int_smul {R : Type*} [Ring R] (n : ℤ) (A : IntegralMatrix) :
    specialize (R := R) (n • A) = (n : R) • specialize (R := R) A := by
  ext i j
  change ((n * A i j : ℤ) : R) = (n : R) * (A i j : R)
  exact Int.cast_mul n (A i j)

@[simp] public lemma specialize_zero {R : Type*} [Ring R] :
    specialize (R := R) 0 = 0 := by
  ext i j
  simp [specialize]

/-- The root curve over `R`, obtained from the integral divided powers. -/
public def rootCurve {R : Type*} [CommRing R] (r : Root) (t : R) :
    Matrix Basis Basis R :=
  1 + t • specialize (rootDividedPower r 1) +
    t ^ 2 • specialize (rootDividedPower r 2) +
    t ^ 3 • specialize (rootDividedPower r 3)

private lemma cubicCurve_add {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (X1 X2 X3 : A)
    (h11 : X1 * X1 = (2 : R) • X2)
    (h12 : X1 * X2 = (3 : R) • X3)
    (h21 : X2 * X1 = (3 : R) • X3)
    (h13 : X1 * X3 = 0) (h31 : X3 * X1 = 0)
    (h22 : X2 * X2 = 0) (h23 : X2 * X3 = 0)
    (h32 : X3 * X2 = 0) (h33 : X3 * X3 = 0)
    (a b : R) :
    1 + (a + b) • X1 + (a + b) ^ 2 • X2 + (a + b) ^ 3 • X3 =
      (1 + a • X1 + a ^ 2 • X2 + a ^ 3 • X3) *
        (1 + b • X1 + b ^ 2 • X2 + b ^ 3 • X3) := by
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, smul_smul, h11, h12, h21, h13, h31, h22, h23, h32, h33]
  module

private lemma specialize_cubicRelations {R : Type*} [CommRing R] (r : Root) :
    let X1 := specialize (R := R) (rootDividedPower r 1)
    let X2 := specialize (R := R) (rootDividedPower r 2)
    let X3 := specialize (R := R) (rootDividedPower r 3)
    X1 * X1 = (2 : R) • X2 ∧ X1 * X2 = (3 : R) • X3 ∧
      X2 * X1 = (3 : R) • X3 ∧ X1 * X3 = 0 ∧ X3 * X1 = 0 ∧
      X2 * X2 = 0 ∧ X2 * X3 = 0 ∧ X3 * X2 = 0 ∧ X3 * X3 = 0 := by
  rcases rootCubicRelations r with
    ⟨h11, h12, h21, h13, h31, h22, h23, h32, h33⟩
  dsimp
  constructor
  · rw [← specialize_mul, h11, specialize_int_smul]
    norm_num
  constructor
  · rw [← specialize_mul, h12, specialize_int_smul]
    norm_num
  constructor
  · rw [← specialize_mul, h21, specialize_int_smul]
    norm_num
  constructor
  · rw [← specialize_mul, h13, specialize_zero]
  constructor
  · rw [← specialize_mul, h31, specialize_zero]
  constructor
  · rw [← specialize_mul, h22, specialize_zero]
  constructor
  · rw [← specialize_mul, h23, specialize_zero]
  constructor
  · rw [← specialize_mul, h32, specialize_zero]
  · rw [← specialize_mul, h33, specialize_zero]

/-- The characteristic-free additive root-curve relation. -/
public theorem rootCurve_add {R : Type*} [CommRing R] (r : Root) (a b : R) :
    rootCurve r (a + b) = rootCurve r a * rootCurve r b := by
  rcases specialize_cubicRelations (R := R) r with
    ⟨h11, h12, h21, h13, h31, h22, h23, h32, h33⟩
  exact cubicCurve_add _ _ _ h11 h12 h21 h13 h31 h22 h23 h32 h33 a b

@[simp] public theorem rootCurve_zero {R : Type*} [CommRing R] (r : Root) :
    rootCurve (R := R) r 0 = 1 := by
  simp [rootCurve]

/-- A root curve as a unit, with inverse given by parameter negation. -/
public def rootCurveUnit {R : Type*} [CommRing R] (r : Root) (t : R) :
    (Matrix Basis Basis R)ˣ where
  val := rootCurve r t
  inv := rootCurve r (-t)
  val_inv := by rw [← rootCurve_add]; simp
  inv_val := by rw [← rootCurve_add]; simp

/-- Recover the root labeling a root coordinate; the two Cartan coordinates return `none`. -/
public def basisRoot : Basis → Option Root
  | 0 => none
  | 1 => none
  | 2 => some 0
  | 3 => some 1
  | 4 => some 2
  | 5 => some 3
  | 6 => some 4
  | 7 => some 5
  | 8 => some 6
  | 9 => some 7
  | 10 => some 8
  | 11 => some 9
  | 12 => some 10
  | 13 => some 11

@[simp] public theorem basisRoot_cartanBasis (i : Fin 2) : basisRoot (cartanBasis i) = none := by
  fin_cases i <;> rfl

@[simp] public theorem basisRoot_rootBasis (r : Root) : basisRoot (rootBasis r) = some r := by
  fin_cases r <;> rfl

/-- The weight of each lattice basis vector against the two simple coroots. -/
public def basisWeight (b : Basis) (i : Fin 2) : ℤ :=
  match basisRoot b with
  | none => 0
  | some r => r.pairingSimple i

public abbrev TorusParameter (R : Type*) [CommRing R] := Fin 2 → Rˣ

public def basisTorusUnit {R : Type*} [CommRing R]
    (u : TorusParameter R) (b : Basis) : Rˣ :=
  ∏ i : Fin 2, u i ^ (-basisWeight b i)

/-- The split rank-two diagonal torus on the Chevalley lattice. -/
public def torusElement {R : Type*} [CommRing R] (u : TorusParameter R) :
    (Matrix Basis Basis R)ˣ where
  val := Matrix.diagonal fun b => (basisTorusUnit u b : R)
  inv := Matrix.diagonal fun b => (↑((basisTorusUnit u b)⁻¹) : R)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    simp [Matrix.one_apply, Matrix.diagonal_apply]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    simp [Matrix.one_apply, Matrix.diagonal_apply]

/-- The integral data and checked relations used by the specialized models. -/
public structure IntegralModel where
  rootOperator : Root → IntegralMatrix
  dividedPower : Root → Fin 4 → IntegralMatrix
  weyl : Fin 2 → IntegralMatrix
  weylInv : Fin 2 → IntegralMatrix
  cubic : ∀ r, CubicRelations (dividedPower r 1) (dividedPower r 2) (dividedPower r 3)
  weyl_mul_inv : ∀ i, weyl i * weylInv i = 1
  weyl_inv_mul : ∀ i, weylInv i * weyl i = 1
  weyl_dividedPower : ∀ i r m,
    weylInv i * dividedPower r m * weyl i =
      (weylRootSign i r ^ m.val) • dividedPower (simpleReflection i r) m

/-- The certified integral `G2` Chevalley representation. -/
public def integralModel : IntegralModel where
  rootOperator := rootOperator
  dividedPower := rootDividedPower
  weyl := weyl
  weylInv := weylInv
  cubic := rootCubicRelations
  weyl_mul_inv := weyl_mul_inv
  weyl_inv_mul := weyl_inv_mul
  weyl_dividedPower := weyl_dividedPower

/-- A descriptive alias used by downstream `G2` carrier modules. -/
public def g2IntegralChevalleyModel : IntegralModel := integralModel

public def rootGenerator {R : Type*} [CommRing R] (p : Root × R) :
    (Matrix Basis Basis R)ˣ := rootCurveUnit p.1 p.2

/-- The root and torus generators of the specialized `G2` model. -/
public def carrierGenerators {R : Type*} [CommRing R] :
    Set ((Matrix Basis Basis R)ˣ) :=
  Set.range rootGenerator ∪ Set.range torusElement

/-- The exact pointwise carrier generated by the integral root curves and split torus. -/
public def carrier {R : Type*} [CommRing R] : Subgroup ((Matrix Basis Basis R)ˣ) :=
  Subgroup.closure carrierGenerators

/-- A descriptive alias for the exact specialized point carrier. -/
public abbrev g2ChevalleyCarrier {R : Type*} [CommRing R] := carrier (R := R)

public theorem rootCurveUnit_mem_carrier {R : Type*} [CommRing R] (r : Root) (t : R) :
    rootCurveUnit r t ∈ carrier :=
  Subgroup.subset_closure <| Or.inl ⟨(r, t), rfl⟩

public theorem torusElement_mem_carrier {R : Type*} [CommRing R] (u : TorusParameter R) :
    torusElement u ∈ carrier :=
  Subgroup.subset_closure <| Or.inr ⟨u, rfl⟩

end Theory.AlgebraicGroup.G2Chevalley
