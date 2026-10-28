module

import Mathlib.Algebra.Field.MinimalAxioms
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.FreeAbelianGroup.Finsupp
public import Mathlib.Algebra.Group.Commutator
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Multiplicity
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Commutator.Finite
public import Mathlib.GroupTheory.CommutingProbability
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup
public import Mathlib.GroupTheory.GroupExtension.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.Perm.Closure
import Mathlib.GroupTheory.Perm.Cycle.Factors
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Transfer
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NoncommRing
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

public import Theory.Alternating.Theorem523A6
set_option linter.style.nameCheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

/- Chapter 5-specific declarations, kept out of the general Theory library. -/

/- BEGIN Theory.Theorem523A7Matrix -/
noncomputable section
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
universe __ch5_Theorem523A7Matrix_w

open Theory.GroupTheory
open Theory.GroupTheory.Covering

namespace GLS3.Chapter5.SchurPresentation

open scoped commutatorElement

structure ExceptionalMatrix.F25 where
  re : ZMod 5
  im : ZMod 5
deriving DecidableEq, Repr

private def __ch5_Theorem523A7Matrix_a6StandardLiftXFull : A6FreeCentral :=
  a6FCGen 0 * a6z1⁻¹

private def __ch5_Theorem523A7Matrix_a6StandardLiftYFull : A6FreeCentral :=
  (a6FCGen 3)⁻¹ * (a6FCGen 2)⁻¹ * a6z4

private theorem __ch5_Theorem523A7Matrix_a6StandardLiftXFull_mem_commutator :
    __ch5_Theorem523A7Matrix_a6StandardLiftXFull ∈ commutator A6FreeCentral := by
  rw [← a6Exponent_ker_eq_commutator, MonoidHom.mem_ker]
  ext j
  change a6ExponentCoord __ch5_Theorem523A7Matrix_a6StandardLiftXFull j = 0
  fin_cases j <;>
    norm_num [__ch5_Theorem523A7Matrix_a6StandardLiftXFull, a6ExponentCoord_gen,
      a6ExponentCoord_z1]

private theorem __ch5_Theorem523A7Matrix_a6StandardLiftYFull_mem_commutator :
    __ch5_Theorem523A7Matrix_a6StandardLiftYFull ∈ commutator A6FreeCentral := by
  rw [← a6Exponent_ker_eq_commutator, MonoidHom.mem_ker]
  ext j
  change a6ExponentCoord __ch5_Theorem523A7Matrix_a6StandardLiftYFull j = 0
  fin_cases j <;>
    norm_num [__ch5_Theorem523A7Matrix_a6StandardLiftYFull, a6ExponentCoord_gen,
      a6ExponentCoord_z4]

private def __ch5_Theorem523A7Matrix_a6StandardLiftX : AlternatingFreeCentralDerived 1 :=
  ⟨__ch5_Theorem523A7Matrix_a6StandardLiftXFull, __ch5_Theorem523A7Matrix_a6StandardLiftXFull_mem_commutator⟩

private def __ch5_Theorem523A7Matrix_a6StandardLiftY : AlternatingFreeCentralDerived 1 :=
  ⟨__ch5_Theorem523A7Matrix_a6StandardLiftYFull, __ch5_Theorem523A7Matrix_a6StandardLiftYFull_mem_commutator⟩

@[expose]
public def a7StandardLiftXFull : A7FreeCentral :=
  a7FCGen 0 * a7z1⁻¹

@[expose]
public def a7StandardLiftYFull : A7FreeCentral :=
  (a7FCGen 3)⁻¹ * (a7FCGen 2)⁻¹ * a7z4

public theorem a7StandardLiftXFull_mem_commutator :
    a7StandardLiftXFull ∈ commutator A7FreeCentral := by
  rw [← a7Exponent_ker_eq_commutator, MonoidHom.mem_ker]
  ext j
  change a7ExponentCoord a7StandardLiftXFull j = 0
  fin_cases j <;>
    norm_num [a7StandardLiftXFull, a7ExponentCoord_gen,
      a7ExponentCoord_z1]

public theorem a7StandardLiftYFull_mem_commutator :
    a7StandardLiftYFull ∈ commutator A7FreeCentral := by
  rw [← a7Exponent_ker_eq_commutator, MonoidHom.mem_ker]
  ext j
  change a7ExponentCoord a7StandardLiftYFull j = 0
  fin_cases j <;>
    norm_num [a7StandardLiftYFull, a7ExponentCoord_gen,
      a7ExponentCoord_z4]

@[expose]
public def a7StandardLiftX : AlternatingFreeCentralDerived 2 :=
  ⟨a7StandardLiftXFull, a7StandardLiftXFull_mem_commutator⟩

@[expose]
public def a7StandardLiftY : AlternatingFreeCentralDerived 2 :=
  ⟨a7StandardLiftYFull, a7StandardLiftYFull_mem_commutator⟩

/-! ## Compact matrix certificates for the exceptional 3-parts

GAP is used only offline to locate the following faithful projective lifts of
the Suzuki generators.  Lean checks the finite-field arithmetic, all relator
defects, and the two exceptional kernel words directly.  No matrix group is
enumerated in the proof.
-/

namespace ExceptionalMatrix

namespace F25

private def __ch5_Theorem523A7Matrix_equivProd : F25 ≃ ZMod 5 × ZMod 5 where
  toFun x := (x.re, x.im)
  invFun x := ⟨x.1, x.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

instance : Fintype F25 :=
  Fintype.ofEquiv (ZMod 5 × ZMod 5) __ch5_Theorem523A7Matrix_equivProd.symm

instance : Zero F25 := ⟨⟨0, 0⟩⟩
instance : One F25 := ⟨⟨1, 0⟩⟩
instance : Add F25 := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩
instance : Neg F25 := ⟨fun x => ⟨-x.re, -x.im⟩⟩
instance : Mul F25 := ⟨fun x y =>
  ⟨x.re * y.re - 2 * x.im * y.im,
    x.re * y.im + x.im * y.re + x.im * y.im⟩⟩

private def __ch5_Theorem523A7Matrix_norm (x : F25) : ZMod 5 :=
  x.re ^ 2 + x.re * x.im + 2 * x.im ^ 2

instance : Inv F25 := ⟨fun x =>
  ⟨(x.re + x.im) * __ch5_Theorem523A7Matrix_norm x ^ 3, -x.im * __ch5_Theorem523A7Matrix_norm x ^ 3⟩⟩

private theorem __ch5_Theorem523A7Matrix_coordinate_ext {x y : F25}
    (hre : x.re = y.re) (him : x.im = y.im) : x = y := by
  cases x
  cases y
  simp_all

@[simp] private theorem __ch5_Theorem523A7Matrix_zero_re : (0 : F25).re = 0 := rfl
@[simp] private theorem __ch5_Theorem523A7Matrix_zero_im : (0 : F25).im = 0 := rfl
@[simp] private theorem __ch5_Theorem523A7Matrix_one_re : (1 : F25).re = 1 := rfl
@[simp] private theorem __ch5_Theorem523A7Matrix_one_im : (1 : F25).im = 0 := rfl
@[simp] private theorem __ch5_Theorem523A7Matrix_add_re (x y : F25) : (x + y).re = x.re + y.re := rfl
@[simp] private theorem __ch5_Theorem523A7Matrix_add_im (x y : F25) : (x + y).im = x.im + y.im := rfl
@[simp] private theorem __ch5_Theorem523A7Matrix_neg_re (x : F25) : (-x).re = -x.re := rfl
@[simp] private theorem __ch5_Theorem523A7Matrix_neg_im (x : F25) : (-x).im = -x.im := rfl
@[simp] private theorem __ch5_Theorem523A7Matrix_mul_re (x y : F25) :
    (x * y).re = x.re * y.re - 2 * x.im * y.im := rfl
@[simp] private theorem __ch5_Theorem523A7Matrix_mul_im (x y : F25) :
    (x * y).im = x.re * y.im + x.im * y.re + x.im * y.im := rfl

private theorem __ch5_Theorem523A7Matrix_add_assoc' (a b c : F25) : a + b + c = a + (b + c) := by
  apply __ch5_Theorem523A7Matrix_coordinate_ext <;> simp only [__ch5_Theorem523A7Matrix_add_re, __ch5_Theorem523A7Matrix_add_im, add_assoc]

private theorem __ch5_Theorem523A7Matrix_zero_add' (a : F25) : 0 + a = a := by
  apply __ch5_Theorem523A7Matrix_coordinate_ext <;> simp

private theorem __ch5_Theorem523A7Matrix_neg_add_cancel' (a : F25) : -a + a = 0 := by
  apply __ch5_Theorem523A7Matrix_coordinate_ext <;> simp

private theorem __ch5_Theorem523A7Matrix_mul_assoc' (a b c : F25) : a * b * c = a * (b * c) := by
  apply __ch5_Theorem523A7Matrix_coordinate_ext <;> simp only [__ch5_Theorem523A7Matrix_mul_re, __ch5_Theorem523A7Matrix_mul_im] <;> ring

private theorem __ch5_Theorem523A7Matrix_mul_comm' (a b : F25) : a * b = b * a := by
  apply __ch5_Theorem523A7Matrix_coordinate_ext <;> simp only [__ch5_Theorem523A7Matrix_mul_re, __ch5_Theorem523A7Matrix_mul_im] <;> ring

private theorem __ch5_Theorem523A7Matrix_one_mul' (a : F25) : 1 * a = a := by
  apply __ch5_Theorem523A7Matrix_coordinate_ext <;> simp

private theorem __ch5_Theorem523A7Matrix_mul_inv_cancel' (a : F25) (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  revert a
  all_goals decide
private theorem __ch5_Theorem523A7Matrix_inv_zero' : (0 : F25)⁻¹ = 0 := by
  all_goals decide
private theorem __ch5_Theorem523A7Matrix_left_distrib' (a b c : F25) :
    a * (b + c) = a * b + a * c := by
  apply __ch5_Theorem523A7Matrix_coordinate_ext <;> simp only [__ch5_Theorem523A7Matrix_mul_re, __ch5_Theorem523A7Matrix_mul_im, __ch5_Theorem523A7Matrix_add_re, __ch5_Theorem523A7Matrix_add_im] <;> ring

instance : Field F25 := Field.ofMinimalAxioms F25
  __ch5_Theorem523A7Matrix_add_assoc' __ch5_Theorem523A7Matrix_zero_add' __ch5_Theorem523A7Matrix_neg_add_cancel'
  __ch5_Theorem523A7Matrix_mul_assoc' __ch5_Theorem523A7Matrix_mul_comm' __ch5_Theorem523A7Matrix_one_mul'
  __ch5_Theorem523A7Matrix_mul_inv_cancel' __ch5_Theorem523A7Matrix_inv_zero' __ch5_Theorem523A7Matrix_left_distrib'
  ⟨0, 1, by decide⟩

def omega : F25 := ⟨0, 1⟩

end F25
private abbrev __ch5_Theorem523A7Matrix_GL3F25 := Matrix.GeneralLinearGroup (Fin 3) F25

private theorem __ch5_Theorem523A7Matrix_freeCentralKernel_le_ker_of_kernel_maps_to_center
    {F M : Type*} [Group F] [Group M]
    (K : Subgroup F) [K.Normal] (f : F →* M)
    (hK : K ≤ (Subgroup.center M).comap f) :
    FreeCentralExtension.freeCentralKernel K ≤ f.ker := by
  rw [FreeCentralExtension.freeCentralKernel, Subgroup.commutator_le]
  intro x _hx k hk
  rw [MonoidHom.mem_ker, map_commutatorElement]
  apply commutatorElement_eq_one_iff_commute.mpr
  exact Subgroup.mem_center_iff.mp (hK hk) (f x)

private def __ch5_Theorem523A7Matrix_a7MatG0 : __ch5_Theorem523A7Matrix_GL3F25 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![(0 : F25), F25.omega ^ 4, F25.omega ^ 10;
       F25.omega ^ 5, F25.omega ^ 16, F25.omega ^ 20;
       3, F25.omega ^ 13, F25.omega ^ 4] (by decide)

private def __ch5_Theorem523A7Matrix_a7MatG1 : __ch5_Theorem523A7Matrix_GL3F25 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![F25.omega ^ 2, F25.omega ^ 22, 4;
       F25.omega ^ 9, F25.omega ^ 22, F25.omega;
       F25.omega ^ 17, F25.omega ^ 19, F25.omega] (by decide)

private def __ch5_Theorem523A7Matrix_a7MatG2 : __ch5_Theorem523A7Matrix_GL3F25 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![F25.omega ^ 17, F25.omega ^ 17, F25.omega ^ 3;
       F25.omega ^ 20, F25.omega ^ 13, F25.omega ^ 9;
       F25.omega ^ 11, F25.omega ^ 14, F25.omega ^ 23] (by decide)

private def __ch5_Theorem523A7Matrix_a7MatG3 : __ch5_Theorem523A7Matrix_GL3F25 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![(4 : F25), 0, 0;
       F25.omega ^ 3, F25.omega ^ 8, F25.omega ^ 21;
       F25.omega, F25.omega ^ 2, F25.omega ^ 20] (by decide)

private def __ch5_Theorem523A7Matrix_a7MatG4 : __ch5_Theorem523A7Matrix_GL3F25 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![F25.omega ^ 11, 0, F25.omega ^ 16;
       F25.omega ^ 17, F25.omega ^ 4, F25.omega ^ 8;
       F25.omega ^ 9, 0, F25.omega ^ 23] (by decide)

private def __ch5_Theorem523A7Matrix_a7MatrixGenerator : Fin 5 → __ch5_Theorem523A7Matrix_GL3F25 :=
  ![__ch5_Theorem523A7Matrix_a7MatG0, __ch5_Theorem523A7Matrix_a7MatG1, __ch5_Theorem523A7Matrix_a7MatG2, __ch5_Theorem523A7Matrix_a7MatG3, __ch5_Theorem523A7Matrix_a7MatG4]

private abbrev __ch5_Theorem523A7Matrix_A7MatrixIsScalar (x : __ch5_Theorem523A7Matrix_GL3F25) : Prop :=
  x.val = Matrix.scalar (Fin 3) (x.val 0 0)

private theorem __ch5_Theorem523A7Matrix_a7RootCube :
    __ch5_Theorem523A7Matrix_A7MatrixIsScalar (__ch5_Theorem523A7Matrix_a7MatrixGenerator 0 ^ 3) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    apply F25.__ch5_Theorem523A7Matrix_coordinate_ext <;>
    norm_num [__ch5_Theorem523A7Matrix_a7MatrixGenerator, __ch5_Theorem523A7Matrix_a7MatG0, pow_succ, Matrix.mul_apply,
      Fin.sum_univ_succ, F25.omega] <;> decide

private theorem __ch5_Theorem523A7Matrix_a7TailSquare (i : Fin 5) (hi : i ≠ 0) :
    __ch5_Theorem523A7Matrix_A7MatrixIsScalar (__ch5_Theorem523A7Matrix_a7MatrixGenerator i ^ 2) := by
  fin_cases i <;> simp_all
  all_goals
    apply Matrix.ext
    intro r c
    fin_cases r <;> fin_cases c <;>
      apply F25.__ch5_Theorem523A7Matrix_coordinate_ext <;>
      norm_num [__ch5_Theorem523A7Matrix_a7MatrixGenerator, __ch5_Theorem523A7Matrix_a7MatG0, __ch5_Theorem523A7Matrix_a7MatG1, __ch5_Theorem523A7Matrix_a7MatG2, __ch5_Theorem523A7Matrix_a7MatG3,
        __ch5_Theorem523A7Matrix_a7MatG4, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ,
        F25.omega] <;> decide

private theorem __ch5_Theorem523A7Matrix_a7RootAdjacentCube :
    __ch5_Theorem523A7Matrix_A7MatrixIsScalar ((__ch5_Theorem523A7Matrix_a7MatrixGenerator 0 * __ch5_Theorem523A7Matrix_a7MatrixGenerator 1) ^ 3) := by
  apply Matrix.ext
  intro r c
  fin_cases r <;> fin_cases c <;>
    apply F25.__ch5_Theorem523A7Matrix_coordinate_ext <;>
    norm_num [__ch5_Theorem523A7Matrix_a7MatrixGenerator, __ch5_Theorem523A7Matrix_a7MatG0, __ch5_Theorem523A7Matrix_a7MatG1, pow_succ,
      Matrix.mul_apply, Fin.sum_univ_succ, F25.omega] <;> decide

private theorem __ch5_Theorem523A7Matrix_a7TailAdjacentCube (i : Fin 4) (hi : i ≠ 0) :
    __ch5_Theorem523A7Matrix_A7MatrixIsScalar
      ((__ch5_Theorem523A7Matrix_a7MatrixGenerator i.castSucc * __ch5_Theorem523A7Matrix_a7MatrixGenerator i.succ) ^ 3) := by
  fin_cases i
  · exact (hi rfl).elim
  · apply Matrix.ext
    intro r c
    fin_cases r <;> fin_cases c <;>
      apply F25.__ch5_Theorem523A7Matrix_coordinate_ext <;>
      norm_num [__ch5_Theorem523A7Matrix_a7MatrixGenerator, __ch5_Theorem523A7Matrix_a7MatG0, __ch5_Theorem523A7Matrix_a7MatG1, __ch5_Theorem523A7Matrix_a7MatG2, __ch5_Theorem523A7Matrix_a7MatG3,
        __ch5_Theorem523A7Matrix_a7MatG4, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ,
        F25.omega] <;> decide
  · apply Matrix.ext
    intro r c
    fin_cases r <;> fin_cases c <;>
      apply F25.__ch5_Theorem523A7Matrix_coordinate_ext <;>
      norm_num [__ch5_Theorem523A7Matrix_a7MatrixGenerator, __ch5_Theorem523A7Matrix_a7MatG0, __ch5_Theorem523A7Matrix_a7MatG1, __ch5_Theorem523A7Matrix_a7MatG2, __ch5_Theorem523A7Matrix_a7MatG3,
        __ch5_Theorem523A7Matrix_a7MatG4, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ,
        F25.omega] <;> decide
  · apply Matrix.ext
    intro r c
    fin_cases r <;> fin_cases c <;>
      apply F25.__ch5_Theorem523A7Matrix_coordinate_ext <;>
      norm_num [__ch5_Theorem523A7Matrix_a7MatrixGenerator, __ch5_Theorem523A7Matrix_a7MatG0, __ch5_Theorem523A7Matrix_a7MatG1, __ch5_Theorem523A7Matrix_a7MatG2, __ch5_Theorem523A7Matrix_a7MatG3,
        __ch5_Theorem523A7Matrix_a7MatG4, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ,
        F25.omega] <;> decide

private theorem __ch5_Theorem523A7Matrix_a7RootFarSquare (j : Fin 5) (hj : 1 < j.val) :
    __ch5_Theorem523A7Matrix_A7MatrixIsScalar ((__ch5_Theorem523A7Matrix_a7MatrixGenerator 0 * __ch5_Theorem523A7Matrix_a7MatrixGenerator j) ^ 2) := by
  fin_cases j <;> simp_all
  all_goals
    apply Matrix.ext
    intro r c
    fin_cases r <;> fin_cases c <;>
      apply F25.__ch5_Theorem523A7Matrix_coordinate_ext <;>
      norm_num [__ch5_Theorem523A7Matrix_a7MatrixGenerator, __ch5_Theorem523A7Matrix_a7MatG0, __ch5_Theorem523A7Matrix_a7MatG1, __ch5_Theorem523A7Matrix_a7MatG2, __ch5_Theorem523A7Matrix_a7MatG3,
        __ch5_Theorem523A7Matrix_a7MatG4, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ,
        F25.omega] <;> decide

private theorem __ch5_Theorem523A7Matrix_a7Commute13 : Commute __ch5_Theorem523A7Matrix_a7MatG1 __ch5_Theorem523A7Matrix_a7MatG3 := by
  rw [commute_iff_eq]
  apply Matrix.GeneralLinearGroup.ext
  intro r c
  fin_cases r <;> fin_cases c <;>
    apply F25.__ch5_Theorem523A7Matrix_coordinate_ext <;>
    norm_num [__ch5_Theorem523A7Matrix_a7MatG1, __ch5_Theorem523A7Matrix_a7MatG3, Matrix.mul_apply,
      Fin.sum_univ_succ, F25.omega] <;> decide

private theorem __ch5_Theorem523A7Matrix_a7Commute14 : Commute __ch5_Theorem523A7Matrix_a7MatG1 __ch5_Theorem523A7Matrix_a7MatG4 := by
  rw [commute_iff_eq]
  apply Matrix.GeneralLinearGroup.ext
  intro r c
  fin_cases r <;> fin_cases c <;>
    apply F25.__ch5_Theorem523A7Matrix_coordinate_ext <;>
    norm_num [__ch5_Theorem523A7Matrix_a7MatG1, __ch5_Theorem523A7Matrix_a7MatG4, Matrix.mul_apply,
      Fin.sum_univ_succ, F25.omega] <;> decide

private theorem __ch5_Theorem523A7Matrix_a7Commute24 : Commute __ch5_Theorem523A7Matrix_a7MatG2 __ch5_Theorem523A7Matrix_a7MatG4 := by
  rw [commute_iff_eq]
  apply Matrix.GeneralLinearGroup.ext
  intro r c
  fin_cases r <;> fin_cases c <;>
    apply F25.__ch5_Theorem523A7Matrix_coordinate_ext <;>
    norm_num [__ch5_Theorem523A7Matrix_a7MatG2, __ch5_Theorem523A7Matrix_a7MatG4, Matrix.mul_apply,
      Fin.sum_univ_succ, F25.omega] <;> decide

private theorem __ch5_Theorem523A7Matrix_a7TailFarCommutator (i j : Fin 5)
    (hi : i ≠ 0) (hj : j ≠ 0)
    (hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    __ch5_Theorem523A7Matrix_A7MatrixIsScalar ⁅__ch5_Theorem523A7Matrix_a7MatrixGenerator i, __ch5_Theorem523A7Matrix_a7MatrixGenerator j⁆ := by
  fin_cases i <;> fin_cases j <;> simp_all [__ch5_Theorem523A7Matrix_a7MatrixGenerator]
  all_goals
    first
    | rw [__ch5_Theorem523A7Matrix_a7Commute13.commutator_eq]
      rfl
    | rw [__ch5_Theorem523A7Matrix_a7Commute13.symm.commutator_eq]
      rfl
    | rw [__ch5_Theorem523A7Matrix_a7Commute14.commutator_eq]
      rfl
    | rw [__ch5_Theorem523A7Matrix_a7Commute14.symm.commutator_eq]
      rfl
    | rw [__ch5_Theorem523A7Matrix_a7Commute24.commutator_eq]
      rfl
    | rw [__ch5_Theorem523A7Matrix_a7Commute24.symm.commutator_eq]
      rfl

private theorem __ch5_Theorem523A7Matrix_a7MatrixRelationCertificate :
    __ch5_Theorem523A7Matrix_A7MatrixIsScalar (__ch5_Theorem523A7Matrix_a7MatrixGenerator 0 ^ 3) ∧
    (∀ i : Fin 5, i ≠ 0 → __ch5_Theorem523A7Matrix_A7MatrixIsScalar (__ch5_Theorem523A7Matrix_a7MatrixGenerator i ^ 2)) ∧
    __ch5_Theorem523A7Matrix_A7MatrixIsScalar ((__ch5_Theorem523A7Matrix_a7MatrixGenerator 0 * __ch5_Theorem523A7Matrix_a7MatrixGenerator 1) ^ 3) ∧
    (∀ i : Fin 4, i ≠ 0 →
      __ch5_Theorem523A7Matrix_A7MatrixIsScalar
        ((__ch5_Theorem523A7Matrix_a7MatrixGenerator i.castSucc * __ch5_Theorem523A7Matrix_a7MatrixGenerator i.succ) ^ 3)) ∧
    (∀ j : Fin 5, 1 < j.val →
      __ch5_Theorem523A7Matrix_A7MatrixIsScalar ((__ch5_Theorem523A7Matrix_a7MatrixGenerator 0 * __ch5_Theorem523A7Matrix_a7MatrixGenerator j) ^ 2)) ∧
    (∀ i j : Fin 5, i ≠ 0 → j ≠ 0 →
      (i.val + 1 < j.val ∨ j.val + 1 < i.val) →
      __ch5_Theorem523A7Matrix_A7MatrixIsScalar ⁅__ch5_Theorem523A7Matrix_a7MatrixGenerator i, __ch5_Theorem523A7Matrix_a7MatrixGenerator j⁆) := by
  exact ⟨__ch5_Theorem523A7Matrix_a7RootCube, __ch5_Theorem523A7Matrix_a7TailSquare, __ch5_Theorem523A7Matrix_a7RootAdjacentCube,
    __ch5_Theorem523A7Matrix_a7TailAdjacentCube, __ch5_Theorem523A7Matrix_a7RootFarSquare, __ch5_Theorem523A7Matrix_a7TailFarCommutator⟩

private theorem __ch5_Theorem523A7Matrix_a7MatrixIsScalar_mem_center {x : __ch5_Theorem523A7Matrix_GL3F25}
    (hx : __ch5_Theorem523A7Matrix_A7MatrixIsScalar x) : x ∈ Subgroup.center __ch5_Theorem523A7Matrix_GL3F25 := by
  apply Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
  exact ⟨x.val 0 0, hx.symm⟩

private def __ch5_Theorem523A7Matrix_a7MatrixFree : AlternatingSuzukiFreeGroup 2 →* __ch5_Theorem523A7Matrix_GL3F25 :=
  FreeGroup.lift __ch5_Theorem523A7Matrix_a7MatrixGenerator

private theorem __ch5_Theorem523A7Matrix_a7MatrixRelator_mem_center (r : SuzukiRelator 2) :
    __ch5_Theorem523A7Matrix_a7MatrixFree r.word ∈ Subgroup.center __ch5_Theorem523A7Matrix_GL3F25 := by
  rcases __ch5_Theorem523A7Matrix_a7MatrixRelationCertificate with
    ⟨hroot, htail, hadj, htailAdj, hrootFar, htailFar⟩
  cases r with
  | rootCube =>
      apply __ch5_Theorem523A7Matrix_a7MatrixIsScalar_mem_center
      simpa [__ch5_Theorem523A7Matrix_a7MatrixFree, SuzukiRelator.word, suzukiFreeGenerator] using hroot
  | tailSquare i hi =>
      apply __ch5_Theorem523A7Matrix_a7MatrixIsScalar_mem_center
      simpa [__ch5_Theorem523A7Matrix_a7MatrixFree, SuzukiRelator.word, suzukiFreeGenerator] using htail i hi
  | rootAdjacentCube =>
      apply __ch5_Theorem523A7Matrix_a7MatrixIsScalar_mem_center
      simpa [__ch5_Theorem523A7Matrix_a7MatrixFree, SuzukiRelator.word, suzukiFreeGenerator] using hadj
  | tailAdjacentCube i hi =>
      apply __ch5_Theorem523A7Matrix_a7MatrixIsScalar_mem_center
      simpa [__ch5_Theorem523A7Matrix_a7MatrixFree, SuzukiRelator.word, suzukiFreeGenerator] using
        htailAdj i hi
  | rootFarSquare j hj =>
      apply __ch5_Theorem523A7Matrix_a7MatrixIsScalar_mem_center
      simpa [__ch5_Theorem523A7Matrix_a7MatrixFree, SuzukiRelator.word, suzukiFreeGenerator] using
        hrootFar j hj
  | tailFarCommutator i j hi hj hfar =>
      apply __ch5_Theorem523A7Matrix_a7MatrixIsScalar_mem_center
      simpa [__ch5_Theorem523A7Matrix_a7MatrixFree, SuzukiRelator.word, suzukiFreeGenerator] using
        htailFar i j hi hj hfar

private theorem __ch5_Theorem523A7Matrix_a7Kernel_maps_to_center :
    alternatingSuzukiKernel 2 ≤ (Subgroup.center __ch5_Theorem523A7Matrix_GL3F25).comap __ch5_Theorem523A7Matrix_a7MatrixFree := by
  rw [alternatingSuzukiKernel_eq_normalClosure]
  apply Subgroup.normalClosure_le_normal
  intro x hx
  obtain ⟨r, rfl⟩ := hx
  exact __ch5_Theorem523A7Matrix_a7MatrixRelator_mem_center r

private def __ch5_Theorem523A7Matrix_a7MatrixHom : AlternatingFreeCentralGroup 2 →* __ch5_Theorem523A7Matrix_GL3F25 :=
  QuotientGroup.lift
    (FreeCentralExtension.freeCentralKernel (alternatingSuzukiKernel 2))
    __ch5_Theorem523A7Matrix_a7MatrixFree
    (__ch5_Theorem523A7Matrix_freeCentralKernel_le_ker_of_kernel_maps_to_center
      (alternatingSuzukiKernel 2) __ch5_Theorem523A7Matrix_a7MatrixFree __ch5_Theorem523A7Matrix_a7Kernel_maps_to_center)

private def __ch5_Theorem523A7Matrix_a7MatU3 : __ch5_Theorem523A7Matrix_GL3F25 := __ch5_Theorem523A7Matrix_a7MatG2 ^ 2
private def __ch5_Theorem523A7Matrix_a7MatU4 : __ch5_Theorem523A7Matrix_GL3F25 := __ch5_Theorem523A7Matrix_a7MatG3 ^ 2
private def __ch5_Theorem523A7Matrix_a7MatW3 : __ch5_Theorem523A7Matrix_GL3F25 := (__ch5_Theorem523A7Matrix_a7MatG0 * __ch5_Theorem523A7Matrix_a7MatG2) ^ 2
private def __ch5_Theorem523A7Matrix_a7MatW4 : __ch5_Theorem523A7Matrix_GL3F25 := (__ch5_Theorem523A7Matrix_a7MatG0 * __ch5_Theorem523A7Matrix_a7MatG3) ^ 2
private def __ch5_Theorem523A7Matrix_a7MatW : __ch5_Theorem523A7Matrix_GL3F25 := ⁅__ch5_Theorem523A7Matrix_a7MatG1, __ch5_Theorem523A7Matrix_a7MatG3⁆
private def __ch5_Theorem523A7Matrix_a7MatT3 : __ch5_Theorem523A7Matrix_GL3F25 := __ch5_Theorem523A7Matrix_a7MatW3 * __ch5_Theorem523A7Matrix_a7MatU3⁻¹
private def __ch5_Theorem523A7Matrix_a7MatT4 : __ch5_Theorem523A7Matrix_GL3F25 := __ch5_Theorem523A7Matrix_a7MatW4 * __ch5_Theorem523A7Matrix_a7MatU4⁻¹
private def __ch5_Theorem523A7Matrix_a7MatK : __ch5_Theorem523A7Matrix_GL3F25 := __ch5_Theorem523A7Matrix_a7MatW * __ch5_Theorem523A7Matrix_a7MatT4 * __ch5_Theorem523A7Matrix_a7MatT3⁻¹

private theorem __ch5_Theorem523A7Matrix_a7MatrixHom_a7k : __ch5_Theorem523A7Matrix_a7MatrixHom a7k = __ch5_Theorem523A7Matrix_a7MatK := by
  simp [__ch5_Theorem523A7Matrix_a7MatrixHom, __ch5_Theorem523A7Matrix_a7MatrixFree, a7k, a7t4, a7t3, a7w, a7w4,
    a7u4, a7w3, a7u3, a7FCGen, __ch5_Theorem523A7Matrix_a7MatK, __ch5_Theorem523A7Matrix_a7MatW, __ch5_Theorem523A7Matrix_a7MatT4, __ch5_Theorem523A7Matrix_a7MatT3,
    __ch5_Theorem523A7Matrix_a7MatW4, __ch5_Theorem523A7Matrix_a7MatU4, __ch5_Theorem523A7Matrix_a7MatW3, __ch5_Theorem523A7Matrix_a7MatU3, __ch5_Theorem523A7Matrix_a7MatrixGenerator, mul_assoc]

private def __ch5_Theorem523A7Matrix_a7OmegaUnit : F25ˣ := Units.mk0 F25.omega (by decide)
private def __ch5_Theorem523A7Matrix_a7MatKExpected : __ch5_Theorem523A7Matrix_GL3F25 :=
  Matrix.GeneralLinearGroup.scalar (Fin 3) (__ch5_Theorem523A7Matrix_a7OmegaUnit ^ 16)

private theorem __ch5_Theorem523A7Matrix_a7MatK_eq_expected : __ch5_Theorem523A7Matrix_a7MatK = __ch5_Theorem523A7Matrix_a7MatKExpected := by
  all_goals decide
private theorem __ch5_Theorem523A7Matrix_a7MatK_order : orderOf __ch5_Theorem523A7Matrix_a7MatK = 3 := by
  rw [__ch5_Theorem523A7Matrix_a7MatK_eq_expected]
  exact orderOf_eq_prime (by decide) (by decide)

private theorem __ch5_Theorem523A7Matrix_a7MatrixHom_a7k_order : orderOf (__ch5_Theorem523A7Matrix_a7MatrixHom a7k) = 3 := by
  rw [__ch5_Theorem523A7Matrix_a7MatrixHom_a7k]
  exact __ch5_Theorem523A7Matrix_a7MatK_order

@[simp]
private theorem __ch5_Theorem523A7Matrix_a7MatrixHom_a7FCGen (i : Fin 5) :
    __ch5_Theorem523A7Matrix_a7MatrixHom (a7FCGen i) = __ch5_Theorem523A7Matrix_a7MatrixGenerator i := by
  simp [__ch5_Theorem523A7Matrix_a7MatrixHom, __ch5_Theorem523A7Matrix_a7MatrixFree, a7FCGen]

private def __ch5_Theorem523A7Matrix_a7MatStandardZ1 : __ch5_Theorem523A7Matrix_GL3F25 :=
  __ch5_Theorem523A7Matrix_a7MatG0 ^ 3 * __ch5_Theorem523A7Matrix_a7MatT3⁻¹

private def __ch5_Theorem523A7Matrix_a7MatStandardZ4 : __ch5_Theorem523A7Matrix_GL3F25 :=
  (__ch5_Theorem523A7Matrix_a7MatG2 * __ch5_Theorem523A7Matrix_a7MatG3) ^ 3 * (__ch5_Theorem523A7Matrix_a7MatG2 ^ 2 * __ch5_Theorem523A7Matrix_a7MatG3 ^ 2)⁻¹

private def __ch5_Theorem523A7Matrix_a7MatStandardX : __ch5_Theorem523A7Matrix_GL3F25 :=
  __ch5_Theorem523A7Matrix_a7MatG0 * __ch5_Theorem523A7Matrix_a7MatStandardZ1⁻¹

private def __ch5_Theorem523A7Matrix_a7MatStandardY : __ch5_Theorem523A7Matrix_GL3F25 :=
  __ch5_Theorem523A7Matrix_a7MatG3⁻¹ * __ch5_Theorem523A7Matrix_a7MatG2⁻¹ * __ch5_Theorem523A7Matrix_a7MatStandardZ4

private theorem __ch5_Theorem523A7Matrix_a7MatrixHom_standardLiftXFull :
    __ch5_Theorem523A7Matrix_a7MatrixHom a7StandardLiftXFull = __ch5_Theorem523A7Matrix_a7MatStandardX := by
  simp [a7StandardLiftXFull, a7z1, a7u1, a7t3, a7w3, a7u3,
    __ch5_Theorem523A7Matrix_a7MatStandardX, __ch5_Theorem523A7Matrix_a7MatStandardZ1, __ch5_Theorem523A7Matrix_a7MatT3, __ch5_Theorem523A7Matrix_a7MatW3, __ch5_Theorem523A7Matrix_a7MatU3,
    __ch5_Theorem523A7Matrix_a7MatrixGenerator]

private theorem __ch5_Theorem523A7Matrix_a7MatrixHom_standardLiftYFull :
    __ch5_Theorem523A7Matrix_a7MatrixHom a7StandardLiftYFull = __ch5_Theorem523A7Matrix_a7MatStandardY := by
  simp [a7StandardLiftYFull, a7z4, a7v3, a7u3, a7u4,
    __ch5_Theorem523A7Matrix_a7MatStandardY, __ch5_Theorem523A7Matrix_a7MatStandardZ4, __ch5_Theorem523A7Matrix_a7MatrixGenerator]

private theorem __ch5_Theorem523A7Matrix_a7MatStandardCommutator_order :
    orderOf ⁅__ch5_Theorem523A7Matrix_a7MatStandardX, __ch5_Theorem523A7Matrix_a7MatStandardY⁆ = 3 := by
  exact orderOf_eq_prime (by decide) (by decide)

private theorem __ch5_Theorem523A7Matrix_a7StandardDetector_commutator_order :
    orderOf
      ((__ch5_Theorem523A7Matrix_a7MatrixHom.comp (AlternatingFreeCentralDerived 2).subtype)
        ⁅a7StandardLiftX, a7StandardLiftY⁆) = 3 := by
  rw [map_commutatorElement]
  change orderOf
    ⁅__ch5_Theorem523A7Matrix_a7MatrixHom a7StandardLiftXFull,
      __ch5_Theorem523A7Matrix_a7MatrixHom a7StandardLiftYFull⁆ = 3
  rw [__ch5_Theorem523A7Matrix_a7MatrixHom_standardLiftXFull, __ch5_Theorem523A7Matrix_a7MatrixHom_standardLiftYFull]
  exact __ch5_Theorem523A7Matrix_a7MatStandardCommutator_order

public theorem exists_a7StandardDetector :
    ∃ (M : Type) (_ : Group M)
      (detector : AlternatingFreeCentralDerived 2 →* M),
      orderOf (detector ⁅a7StandardLiftX, a7StandardLiftY⁆) = 3 := by
  exact ⟨__ch5_Theorem523A7Matrix_GL3F25, inferInstance,
    __ch5_Theorem523A7Matrix_a7MatrixHom.comp (AlternatingFreeCentralDerived 2).subtype,
    __ch5_Theorem523A7Matrix_a7StandardDetector_commutator_order⟩


end ExceptionalMatrix


public theorem a7UniversalKernel_three_dvd_new :
    3 ∣ Nat.card
      (alternatingFreeCentralCovering 2).toMonoidHom.ker := by
  change 3 ∣ Nat.card (alternatingFreeCentralDerivedProjection 2).ker
  rw [a7DerivedProjection_ker_eq_zpowers, Nat.card_zpowers]
  let f := ExceptionalMatrix.__ch5_Theorem523A7Matrix_a7MatrixHom.comp
    (AlternatingFreeCentralDerived 2).subtype
  have hdiv := orderOf_map_dvd f a7DerivedK
  have horder : orderOf (f a7DerivedK) = 3 := by
    change orderOf (ExceptionalMatrix.__ch5_Theorem523A7Matrix_a7MatrixHom a7k) = 3
    exact ExceptionalMatrix.__ch5_Theorem523A7Matrix_a7MatrixHom_a7k_order
  simpa only [horder] using hdiv

end GLS3.Chapter5.SchurPresentation
/- END Theory.Theorem523A7Matrix -/

/- BEGIN Theory.PrimeCycleRotationNaturalAction -/
noncomputable section

open GLS3.Chapter5.SchurPresentation

namespace GLS3.Chapter5

universe __ch5_PrimeCycleRotationNaturalAction_u

/-- Under prime-cycle rotation coordinates, the cycle-permuting complement
acts by the standard permutation of coordinates. -/
public theorem primeCycleRotationNaturalAction
    {Ω : Type __ch5_PrimeCycleRotationNaturalAction_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : (orderOf x).Prime)
    (l : cyclePermutationSubgroup x) :
    ((cyclePermutationActionOnCycleRotations x) l).trans
        (primeCycleRotationCoordinates x hx) =
      (primeCycleRotationCoordinates x hx).trans
        (SchurPresentation.permuteCoordinatesHom
          x.cycleFactorsFinset (Multiplicative (ZMod (orderOf x)))
          ((theorem_5_2_2_d_3_a x hx) l)) := by
  apply MulEquiv.ext
  intro a
  funext c
  let σ := (theorem_5_2_2_d_3_a x hx) l
  let d : x.cycleFactorsFinset := σ⁻¹ c
  let b := (cyclePermutationActionOnCycleRotations x) l a
  change (primeCycleRotationCoordinates x hx) b c =
    (primeCycleRotationCoordinates x hx) a d
  change Multiplicative.toAdd ((primeCycleRotationCoordinates x hx) b c) =
    Multiplicative.toAdd ((primeCycleRotationCoordinates x hx) a d)
  apply (cycleCoordinateEquiv x hx c).injective
  apply Subtype.ext
  rw [primeCycleRotationCoordinate_evaluation]
  have hcoord :
      l.1.1 (cycleCoordinateEquiv x hx d
        (Multiplicative.toAdd
          ((primeCycleRotationCoordinates x hx) a d))).1 =
        (cycleCoordinateEquiv x hx c
          (Multiplicative.toAdd
            ((primeCycleRotationCoordinates x hx) a d))).1 := by
    have h := primeCyclePermutation_apply_cycleCoordinate x hx l d
      (Multiplicative.toAdd ((primeCycleRotationCoordinates x hx) a d))
    have hdc : σ d = c := σ.apply_symm_apply c
    rw [hdc] at h
    exact h
  rw [← hcoord, primeCycleRotationCoordinate_evaluation]
  have hinvBasis : l.1.1⁻¹ (cycleBasis x c) = cycleBasis x d := by
    have h := primeCyclePermutation_apply_cycleCoordinate x hx l⁻¹ c 0
    simpa [cycleCoordinateEquiv_zero, σ, d] using h
  have hbasis :
      (cycleRotationToCentralizer x b).1 (cycleBasis x c) =
        (b c).1 (cycleBasis x c) := by
    simpa [cycleCoordinateEquiv_zero] using
      (cycleRotationToCentralizer_apply_cycleCoordinate x hx b c 0)
  have habasis :
      (cycleRotationToCentralizer x a).1 (cycleBasis x d) =
        (a d).1 (cycleBasis x d) := by
    simpa [cycleCoordinateEquiv_zero] using
      (cycleRotationToCentralizer_apply_cycleCoordinate x hx a d 0)
  rw [← hbasis, ← habasis]
  have hact := cyclePermutationActionOnCycleRotations_apply x l a
  have hactPoint :=
    congrArg (fun q : Equiv.Perm Ω => q (cycleBasis x c)) hact
  change (cycleRotationToCentralizer x b).1 (cycleBasis x c) = _ at hactPoint
  rw [hactPoint]
  change l.1.1 ((cycleRotationToCentralizer x a).1
    (l.1.1⁻¹ (cycleBasis x c))) = _
  rw [hinvBasis]

end GLS3.Chapter5
/- END Theory.PrimeCycleRotationNaturalAction -/

/- BEGIN Theory.Theorem523 -/
noncomputable section
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
universe __ch5_Theorem523_w __ch5_Theorem523_w₁ __ch5_Theorem523_w₂

namespace GLS3.Chapter5.SchurPresentation

open scoped commutatorElement

/-! ## Exceptional 3-parts without permutation certificates

The preceding Suzuki calculation proves that both exceptional universal
kernels are cyclic and that their orders divide six.  The only remaining
multiplier input is a small presentation-level witness that their 3-primary
parts are nontrivial.  No Schreier transversal or large permutation action is
used below.
-/

/-- Theorem 5.2.3(c), exceptional multiplier for `A6`. -/
public theorem theorem_5_2_3_c_multiplier_a6 :
    ∃ (G : Type) (_instG : Group G) (_instFin : Finite G)
      (_instQS : IsQuasisimple G)
      (f : Covering G (alternatingGroup (Fin 6))),
      Covering.IsUniversal.{0, 0, __ch5_Theorem523_w} f ∧
        IsCyclic (↥f.toMonoidHom.ker) ∧ Nat.card f.toMonoidHom.ker = 6 := by
  exact ⟨AlternatingFreeCentralDerived 1, inferInstance, inferInstance,
    inferInstance, alternatingFreeCentralCovering 1,
    alternatingFreeCentralCovering_isUniversal 1,
    a6UniversalKernel_isCyclic,
    a6UniversalKernel_card_eq_six a6UniversalKernel_three_dvd_new⟩

/-- Theorem 5.2.3(c), exceptional multiplier for `A7`. -/
public theorem theorem_5_2_3_c_multiplier_a7 :
    ∃ (G : Type) (_instG : Group G) (_instFin : Finite G)
      (_instQS : IsQuasisimple G)
      (f : Covering G (alternatingGroup (Fin 7))),
      Covering.IsUniversal.{0, 0, __ch5_Theorem523_w} f ∧
        IsCyclic (↥f.toMonoidHom.ker) ∧ Nat.card f.toMonoidHom.ker = 6 := by
  exact ⟨AlternatingFreeCentralDerived 2, inferInstance, inferInstance,
    inferInstance, alternatingFreeCentralCovering 2,
    alternatingFreeCentralCovering_isUniversal 2,
    a7UniversalKernel_isCyclic,
    a7UniversalKernel_card_eq_six a7UniversalKernel_three_dvd_new⟩

private theorem __ch5_Theorem523_exists_triple_cover_of_universal_kernel_card_six
    {L G : Type} [Group L] [Finite L] [IsQuasisimple L]
    [Group G] [Finite G] [IsQuasisimple G] [IsSimpleGroup G]
    (f₀ : Covering L G) (hf₀ : Covering.IsUniversal.{0, 0, 0} f₀)
    (hcard : Nat.card f₀.toMonoidHom.ker = 6)
    (hthree : 3 ∣ Nat.card f₀.toMonoidHom.ker)
    (hcenter : Subgroup.center G = ⊥) :
    ∃ (Q : Type) (_instQ : Group Q) (_instFin : Finite Q)
      (_instQS : IsQuasisimple Q) (f : Covering Q G),
      Nat.card f.toMonoidHom.ker = 3 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨X, hXnormal, fbar, _hXker, hfbarSurj, hfbarCenter, hfbarP, hfbarThree⟩ :=
    exists_pPrimary_quotient_central_extension
      f₀.toMonoidHom f₀.surjective f₀.ker_le_center hthree
  let : X.Normal := hXnormal
  have hfbarKer : fbar.ker = Subgroup.center (L ⧸ X) :=
    ker_eq_center_of_surjective_of_center_eq_bot
      fbar hfbarSurj hfbarCenter hcenter
  let e : (L ⧸ X) ⧸ Subgroup.center (L ⧸ X) ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hfbarKer.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective fbar hfbarSurj)
  let : IsQuasisimple (L ⧸ X) := {
    toIsPerfect := inferInstance
    simple := e.isSimpleGroup
  }
  let f : Covering (L ⧸ X) G := {
    toMonoidHom := fbar
    surjective := hfbarSurj
  }
  have hdvd : Nat.card fbar.ker ∣ 6 := by
    have h := Covering.coveringKernel_card_dvd_of_universal f₀ hf₀ f
    rw [hcard] at h
    simpa [f] using h
  have hle : Nat.card fbar.ker ≤ 6 :=
    Nat.le_of_dvd (by norm_num) hdvd
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hfbarP
  have hodd : Odd (Nat.card fbar.ker) := by
    rw [hk]
    exact Odd.pow ⟨1, by norm_num⟩
  have hfbarCard : Nat.card fbar.ker = 3 := by
    rcases hfbarThree with ⟨a, ha⟩
    rcases hodd with ⟨b, hb⟩
    omega
  exact ⟨L ⧸ X, inferInstance, inferInstance, inferInstance, f, by
    simpa [f] using hfbarCard⟩

private theorem __ch5_Theorem523_exists_algebraic_triple_cover_a6_new :
    ∃ (G : Type) (_instG : Group G) (_instFin : Finite G)
      (_instQS : IsQuasisimple G)
      (f : Covering G (alternatingGroup (Fin 6))),
      Nat.card f.toMonoidHom.ker = 3 := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  exact __ch5_Theorem523_exists_triple_cover_of_universal_kernel_card_six
    (alternatingFreeCentralCovering 1)
    (alternatingFreeCentralCovering_isUniversal 1)
    (a6UniversalKernel_card_eq_six a6UniversalKernel_three_dvd_new)
    a6UniversalKernel_three_dvd_new
    (alternatingGroup.center_eq_bot (by norm_num))

private theorem __ch5_Theorem523_exists_algebraic_triple_cover_a7_new :
    ∃ (G : Type) (_instG : Group G) (_instFin : Finite G)
      (_instQS : IsQuasisimple G)
      (f : Covering G (alternatingGroup (Fin 7))),
      Nat.card f.toMonoidHom.ker = 3 := by
  let : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  exact __ch5_Theorem523_exists_triple_cover_of_universal_kernel_card_six
    (alternatingFreeCentralCovering 2)
    (alternatingFreeCentralCovering_isUniversal 2)
    (a7UniversalKernel_card_eq_six a7UniversalKernel_three_dvd_new)
    a7UniversalKernel_three_dvd_new
    (alternatingGroup.center_eq_bot (by norm_num))

private theorem __ch5_Theorem523_factorization_1080_three_new :
    Nat.factorization 1080 3 = 3 := by
  have hzero : padicValNat 3 40 = 0 :=
    padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr (by norm_num)))
  rw [Nat.factorization_def 1080 Nat.prime_three,
    show (1080 : Nat) = 3 ^ 3 * 40 by norm_num,
    padicValNat_base_pow_mul (by norm_num) (by norm_num) 3, hzero]

private theorem __ch5_Theorem523_factorization_7560_three_new :
    Nat.factorization 7560 3 = 3 := by
  have hzero : padicValNat 3 280 = 0 :=
    padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr (by norm_num)))
  rw [Nat.factorization_def 7560 Nat.prime_three,
    show (7560 : Nat) = 3 ^ 3 * 280 by norm_num,
    padicValNat_base_pow_mul (by norm_num) (by norm_num) 3, hzero]

private theorem __ch5_Theorem523_center_card_eq_three_of_card_eq_twenty_seven_of_noncommutative_new
    {P : Type*} [Group P] [Finite P]
    (hcard : Nat.card P = 27) (hncomm : ¬ IsMulCommutative P) :
    Nat.card (Subgroup.center P) = 3 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcardPow : Nat.card P = 3 ^ 3 := by
    simpa using hcard
  obtain ⟨k, hkpos, hcenter⟩ :=
    IsPGroup.card_center_eq_prime_pow hcardPow (by norm_num)
  have hk_dvd : 3 ^ k ∣ 3 ^ 3 := by
    rw [← hcenter, ← hcardPow]
    simpa [Subgroup.card_top] using
      (Subgroup.card_dvd_of_le
        (show Subgroup.center P ≤ (⊤ : Subgroup P) from le_top))
  have hkle : k ≤ 3 :=
    (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hk_dvd
  have hkCases : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hkCases with hk1 | hk23
  · simpa [hk1] using hcenter
  · rcases hk23 with hk2 | hk3
    · have hindex : (Subgroup.center P).index = 3 := by
        have hmul := (Subgroup.center P).card_mul_index
        rw [hcenter, hk2, hcard] at hmul
        omega
      have hquotCard : Nat.card (P ⧸ Subgroup.center P) = 3 := by
        rw [← Subgroup.index_eq_card]
        exact hindex
      let : IsCyclic (P ⧸ Subgroup.center P) :=
        isCyclic_of_card_dvd_prime (by rw [hquotCard])
      exact (hncomm
        (isMulCommutative_of_isCyclic_quotient_center_self P)).elim
    · have hcenterCard : Nat.card (Subgroup.center P) = Nat.card P := by
        rw [hcenter, hk3, hcardPow]
      have hcenterTop : Subgroup.center P = ⊤ :=
        (Subgroup.card_eq_iff_eq_top _).mp hcenterCard
      exact (hncomm (Subgroup.center_eq_top_iff.mp hcenterTop)).elim

private theorem __ch5_Theorem523_triple_cover_a6_card_new
    {G : Type*} [Group G] [Finite G] [IsQuasisimple G]
    (f : Covering G (alternatingGroup (Fin 6)))
    (hker : Nat.card f.toMonoidHom.ker = 3) :
    Nat.card G = 1080 := by
  have hAlt : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    norm_num [Nat.factorial]
  calc
    Nat.card G = Nat.card (↥(⊤ : Subgroup G)) :=
      Nat.card_congr (Subgroup.topEquiv.symm).toEquiv
    _ = Nat.card (↥((⊤ : Subgroup (alternatingGroup (Fin 6))).comap
          f.toMonoidHom)) := by rw [Subgroup.comap_top]
    _ = Nat.card (↥(⊤ : Subgroup (alternatingGroup (Fin 6)))) *
          Nat.card f.toMonoidHom.ker :=
      card_comap_mul f.toMonoidHom f.surjective ⊤
    _ = Nat.card (alternatingGroup (Fin 6)) *
          Nat.card f.toMonoidHom.ker := by
      rw [Nat.card_congr (Subgroup.topEquiv.toEquiv)]
    _ = 1080 := by rw [hAlt, hker]

private theorem __ch5_Theorem523_triple_cover_a7_card_new
    {G : Type*} [Group G] [Finite G] [IsQuasisimple G]
    (f : Covering G (alternatingGroup (Fin 7)))
    (hker : Nat.card f.toMonoidHom.ker = 3) :
    Nat.card G = 7560 := by
  have hAlt : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    norm_num [Nat.factorial]
  calc
    Nat.card G = Nat.card (↥(⊤ : Subgroup G)) :=
      Nat.card_congr (Subgroup.topEquiv.symm).toEquiv
    _ = Nat.card (↥((⊤ : Subgroup (alternatingGroup (Fin 7))).comap
          f.toMonoidHom)) := by rw [Subgroup.comap_top]
    _ = Nat.card (↥(⊤ : Subgroup (alternatingGroup (Fin 7)))) *
          Nat.card f.toMonoidHom.ker :=
      card_comap_mul f.toMonoidHom f.surjective ⊤
    _ = Nat.card (alternatingGroup (Fin 7)) *
          Nat.card f.toMonoidHom.ker := by
      rw [Nat.card_congr (Subgroup.topEquiv.toEquiv)]
    _ = 7560 := by rw [hAlt, hker]

private theorem __ch5_Theorem523_sylow_three_card_center_of_noncommutative_subgroup_card_27_new
    {G : Type*} [Group G] [Finite G]
    (hfactor : (Nat.card G).factorization 3 = 3)
    (R : Subgroup G) (hRcard : Nat.card R = 27)
    (hRnoncomm : ¬ IsMulCommutative R) :
    ∀ P : Sylow 3 G,
      Nat.card (P : Subgroup G) = 27 ∧
        Nat.card (Subgroup.center (P : Subgroup G)) = 3 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRmax : Nat.card R = 3 ^ (Nat.card G).factorization 3 := by
    rw [hRcard, hfactor]
    norm_num
  let P₀ : Sylow 3 G := Sylow.ofCard R hRmax
  have hcenterR : Nat.card (Subgroup.center R) = 3 :=
    __ch5_Theorem523_center_card_eq_three_of_card_eq_twenty_seven_of_noncommutative_new
      hRcard hRnoncomm
  have hP₀eq : (P₀ : Subgroup G) = R := by
    simp [P₀]
  have hcenterP₀ : Nat.card (Subgroup.center (P₀ : Subgroup G)) = 3 := by
    rw [hP₀eq]
    exact hcenterR
  intro P
  have hPcard : Nat.card (P : Subgroup G) = 27 := by
    rw [Sylow.card_eq_multiplicity, hfactor]
    norm_num
  have hcenterCard :
      Nat.card (Subgroup.center (P : Subgroup G)) =
        Nat.card (Subgroup.center (P₀ : Subgroup G)) :=
    Nat.card_congr
      (Subgroup.centerCongr (Sylow.equiv P P₀)).toEquiv
  exact ⟨hPcard, hcenterCard.trans hcenterP₀⟩

private theorem __ch5_Theorem523_standard_preimage_noncommutative_of_universal_detector
    {L G A M : Type}
    [Group L] [Finite L] [IsQuasisimple L]
    [Group G] [Finite G] [IsQuasisimple G]
    [Group A] [Finite A] [IsQuasisimple A]
    [Group M]
    (f₀ : Covering L A) (hf₀ : Covering.IsUniversal.{0, 0, 0} f₀)
    (f : Covering G A)
    (hker₀ : Nat.card f₀.toMonoidHom.ker = 6)
    (hker : Nat.card f.toMonoidHom.ker = 3)
    (H : Subgroup A) (x y : L)
    (hx : f₀ x ∈ H) (hy : f₀ y ∈ H)
    (detector : L →* M)
    (hdetector : orderOf (detector ⁅x, y⁆) = 3) :
    ¬ IsMulCommutative (H.comap f.toMonoidHom) := by
  intro hcomm
  let φ : Covering L G := Covering.IsUniversal.lift hf₀ f
  have hfac : f.comp φ = f₀ := Covering.IsUniversal.lift_fac hf₀ f
  have hfacPoint (z : L) : f (φ z) = f₀ z := by
    simpa using DFunLike.congr_fun hfac z
  let xR : H.comap f.toMonoidHom :=
    ⟨φ x, by
      rw [Subgroup.mem_comap]
      change f (φ x) ∈ H
      rw [hfacPoint]
      exact hx⟩
  let yR : H.comap f.toMonoidHom :=
    ⟨φ y, by
      rw [Subgroup.mem_comap]
      change f (φ y) ∈ H
      rw [hfacPoint]
      exact hy⟩
  have hxyR : xR * yR = yR * xR := hcomm.is_comm.comm xR yR
  have hxy : Commute (φ x) (φ y) := by
    rw [commute_iff_eq]
    exact congrArg Subtype.val hxyR
  have hcommKer : φ ⁅x, y⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr hxy
  have hcKer : ⁅x, y⁆ ∈ φ.toMonoidHom.ker :=
    MonoidHom.mem_ker.mpr hcommKer
  have hcomap :
      f.toMonoidHom.ker.comap φ.toMonoidHom = f₀.toMonoidHom.ker := by
    ext z
    rw [Subgroup.mem_comap, MonoidHom.mem_ker, MonoidHom.mem_ker]
    change f (φ z) = 1 ↔ f₀ z = 1
    rw [hfacPoint]
  have hkerφ : Nat.card φ.toMonoidHom.ker = 2 := by
    have hmul := card_comap_mul φ.toMonoidHom φ.surjective
      f.toMonoidHom.ker
    rw [hcomap, hker₀, hker] at hmul
    omega
  have hdivTwo : orderOf ⁅x, y⁆ ∣ 2 := by
    have hdiv := φ.toMonoidHom.ker.orderOf_dvd_natCard hcKer
    rw [hkerφ] at hdiv
    exact hdiv
  have hdivThree : 3 ∣ orderOf ⁅x, y⁆ := by
    have hdiv := orderOf_map_dvd detector ⁅x, y⁆
    rw [hdetector] at hdiv
    exact hdiv
  have : 3 ∣ 2 := hdivThree.trans hdivTwo
  norm_num at this

private theorem __ch5_Theorem523_a6FullProjection_a6z1 :
    alternatingFreeCentralProjection 1 a6z1 = 1 := by
  apply MonoidHom.mem_ker.mp
  rw [a6FullProjection_ker_eq_exceptionalCenter]
  exact a6z1_mem_exceptionalCenter

private theorem __ch5_Theorem523_a6FullProjection_a6z4 :
    alternatingFreeCentralProjection 1 a6z4 = 1 := by
  apply MonoidHom.mem_ker.mp
  rw [a6FullProjection_ker_eq_exceptionalCenter]
  exact a6z4_mem_exceptionalCenter

private theorem __ch5_Theorem523_a7FullProjection_a7z1 :
    alternatingFreeCentralProjection 2 a7z1 = 1 := by
  apply MonoidHom.mem_ker.mp
  rw [a7FullProjection_ker_eq_exceptionalCenter]
  exact a7z1_mem_exceptionalCenter

private theorem __ch5_Theorem523_a7FullProjection_a7z4 :
    alternatingFreeCentralProjection 2 a7z4 = 1 := by
  apply MonoidHom.mem_ker.mp
  rw [a7FullProjection_ker_eq_exceptionalCenter]
  exact a7z4_mem_exceptionalCenter

private def __ch5_Theorem523_a6BaseX : alternatingGroup (Fin 6) :=
  alternatingSuzukiGenerator 1 0

private def __ch5_Theorem523_a6BaseY : alternatingGroup (Fin 6) :=
  (alternatingSuzukiGenerator 1 3)⁻¹ *
    (alternatingSuzukiGenerator 1 2)⁻¹

private def __ch5_Theorem523_a6BaseNine : Subgroup (alternatingGroup (Fin 6)) :=
  Subgroup.zpowers __ch5_Theorem523_a6BaseX ⊔ Subgroup.zpowers __ch5_Theorem523_a6BaseY

private theorem __ch5_Theorem523_alternatingFreeCentralCovering_a6StandardLiftX :
    alternatingFreeCentralCovering 1 a6StandardLiftX = __ch5_Theorem523_a6BaseX := by
  change alternatingFreeCentralProjection 1 a6StandardLiftXFull = __ch5_Theorem523_a6BaseX
  simp [a6StandardLiftXFull, __ch5_Theorem523_a6BaseX, __ch5_Theorem523_a6FullProjection_a6z1]

private theorem __ch5_Theorem523_alternatingFreeCentralCovering_a6StandardLiftY :
    alternatingFreeCentralCovering 1 a6StandardLiftY = __ch5_Theorem523_a6BaseY := by
  change alternatingFreeCentralProjection 1 a6StandardLiftYFull = __ch5_Theorem523_a6BaseY
  simp [a6StandardLiftYFull, __ch5_Theorem523_a6BaseY, __ch5_Theorem523_a6FullProjection_a6z4]

private theorem __ch5_Theorem523_a6BaseNine_card : Nat.card __ch5_Theorem523_a6BaseNine = 9 := by
  simpa [__ch5_Theorem523_a6BaseNine, __ch5_Theorem523_a6BaseX, __ch5_Theorem523_a6BaseY] using
    Theorem523BaseNine.a6_explicit_card

private def __ch5_Theorem523_a7BaseX : alternatingGroup (Fin 7) :=
  alternatingSuzukiGenerator 2 0

private def __ch5_Theorem523_a7BaseY : alternatingGroup (Fin 7) :=
  (alternatingSuzukiGenerator 2 3)⁻¹ *
    (alternatingSuzukiGenerator 2 2)⁻¹

private def __ch5_Theorem523_a7BaseNine : Subgroup (alternatingGroup (Fin 7)) :=
  Subgroup.zpowers __ch5_Theorem523_a7BaseX ⊔ Subgroup.zpowers __ch5_Theorem523_a7BaseY

private theorem __ch5_Theorem523_alternatingFreeCentralCovering_a7StandardLiftX :
    alternatingFreeCentralCovering 2 a7StandardLiftX = __ch5_Theorem523_a7BaseX := by
  change alternatingFreeCentralProjection 2 a7StandardLiftXFull = __ch5_Theorem523_a7BaseX
  simp [a7StandardLiftXFull, __ch5_Theorem523_a7BaseX, __ch5_Theorem523_a7FullProjection_a7z1]

private theorem __ch5_Theorem523_alternatingFreeCentralCovering_a7StandardLiftY :
    alternatingFreeCentralCovering 2 a7StandardLiftY = __ch5_Theorem523_a7BaseY := by
  change alternatingFreeCentralProjection 2 a7StandardLiftYFull = __ch5_Theorem523_a7BaseY
  simp [a7StandardLiftYFull, __ch5_Theorem523_a7BaseY, __ch5_Theorem523_a7FullProjection_a7z4]

private theorem __ch5_Theorem523_a7BaseNine_card : Nat.card __ch5_Theorem523_a7BaseNine = 9 := by
  simpa [__ch5_Theorem523_a7BaseNine, __ch5_Theorem523_a7BaseX, __ch5_Theorem523_a7BaseY] using
    Theorem523BaseNine.a7_explicit_card

private theorem __ch5_Theorem523_a6_standard_preimage_noncommutative_core_new
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (f : Covering G (alternatingGroup (Fin 6)))
    (hker : Nat.card f.toMonoidHom.ker = 3) :
    ¬ IsMulCommutative (__ch5_Theorem523_a6BaseNine.comap f.toMonoidHom) := by
  obtain ⟨M, instM, detector, hdetector⟩ :=
    ExceptionalMatrix.exists_a6StandardDetector
  let : Group M := instM
  apply __ch5_Theorem523_standard_preimage_noncommutative_of_universal_detector
    (f₀ := alternatingFreeCentralCovering 1)
    (hf₀ := alternatingFreeCentralCovering_isUniversal 1)
    (f := f)
    (hker₀ := a6UniversalKernel_card_eq_six
      a6UniversalKernel_three_dvd_new)
    (hker := hker)
    (H := __ch5_Theorem523_a6BaseNine)
    (x := a6StandardLiftX) (y := a6StandardLiftY)
    (detector := detector)
  · rw [__ch5_Theorem523_alternatingFreeCentralCovering_a6StandardLiftX]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers __ch5_Theorem523_a6BaseX)
  · rw [__ch5_Theorem523_alternatingFreeCentralCovering_a6StandardLiftY]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers __ch5_Theorem523_a6BaseY)
  · exact hdetector

private theorem __ch5_Theorem523_a7_standard_preimage_noncommutative_core_new
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (f : Covering G (alternatingGroup (Fin 7)))
    (hker : Nat.card f.toMonoidHom.ker = 3) :
    ¬ IsMulCommutative (__ch5_Theorem523_a7BaseNine.comap f.toMonoidHom) := by
  obtain ⟨M, instM, detector, hdetector⟩ :=
    ExceptionalMatrix.exists_a7StandardDetector
  let : Group M := instM
  apply __ch5_Theorem523_standard_preimage_noncommutative_of_universal_detector
    (f₀ := alternatingFreeCentralCovering 2)
    (hf₀ := alternatingFreeCentralCovering_isUniversal 2)
    (f := f)
    (hker₀ := a7UniversalKernel_card_eq_six
      a7UniversalKernel_three_dvd_new)
    (hker := hker)
    (H := __ch5_Theorem523_a7BaseNine)
    (x := a7StandardLiftX) (y := a7StandardLiftY)
    (detector := detector)
  · rw [__ch5_Theorem523_alternatingFreeCentralCovering_a7StandardLiftX]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers __ch5_Theorem523_a7BaseX)
  · rw [__ch5_Theorem523_alternatingFreeCentralCovering_a7StandardLiftY]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers __ch5_Theorem523_a7BaseY)
  · exact hdetector

private theorem __ch5_Theorem523_a6_sylow3_heisenberg_of_algebraic_triple_cover_new
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (f : Covering G (alternatingGroup (Fin 6)))
    (hker : Nat.card f.toMonoidHom.ker = 3) :
    ∀ P : Sylow 3 G,
      Nat.card (P : Subgroup G) = 27 ∧
        Nat.card (↥(Subgroup.center (↥(P : Subgroup G)))) = 3 := by
  let R : Subgroup G := __ch5_Theorem523_a6BaseNine.comap f.toMonoidHom
  have hRcard : Nat.card R = 27 := by
    dsimp [R]
    rw [card_comap_mul f.toMonoidHom f.surjective __ch5_Theorem523_a6BaseNine,
      __ch5_Theorem523_a6BaseNine_card, hker]
  have hRnoncomm : ¬ IsMulCommutative R := by
    simpa [R] using __ch5_Theorem523_a6_standard_preimage_noncommutative_core_new f hker
  have hGcard : Nat.card G = 1080 := __ch5_Theorem523_triple_cover_a6_card_new f hker
  have hfactor : (Nat.card G).factorization 3 = 3 := by
    rw [hGcard]
    exact __ch5_Theorem523_factorization_1080_three_new
  exact __ch5_Theorem523_sylow_three_card_center_of_noncommutative_subgroup_card_27_new
    hfactor R hRcard hRnoncomm

private theorem __ch5_Theorem523_a7_sylow3_heisenberg_of_algebraic_triple_cover_new
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (f : Covering G (alternatingGroup (Fin 7)))
    (hker : Nat.card f.toMonoidHom.ker = 3) :
    ∀ P : Sylow 3 G,
      Nat.card (P : Subgroup G) = 27 ∧
        Nat.card (↥(Subgroup.center (↥(P : Subgroup G)))) = 3 := by
  let R : Subgroup G := __ch5_Theorem523_a7BaseNine.comap f.toMonoidHom
  have hRcard : Nat.card R = 27 := by
    dsimp [R]
    rw [card_comap_mul f.toMonoidHom f.surjective __ch5_Theorem523_a7BaseNine,
      __ch5_Theorem523_a7BaseNine_card, hker]
  have hRnoncomm : ¬ IsMulCommutative R := by
    simpa [R] using __ch5_Theorem523_a7_standard_preimage_noncommutative_core_new f hker
  have hGcard : Nat.card G = 7560 := __ch5_Theorem523_triple_cover_a7_card_new f hker
  have hfactor : (Nat.card G).factorization 3 = 3 := by
    rw [hGcard]
    exact __ch5_Theorem523_factorization_7560_three_new
  exact __ch5_Theorem523_sylow_three_card_center_of_noncommutative_subgroup_card_27_new
    hfactor R hRcard hRnoncomm

/-- Theorem 5.2.3(d), Sylow-3 clause for `3.A6`. -/
public theorem theorem_5_2_3_d_sylow3_3A6 :
    ∃ (G : Type) (_instG : Group G) (_instFin : Finite G)
      (_instQS : IsQuasisimple G)
      (f : Covering G (alternatingGroup (Fin 6))),
      Nat.card f.toMonoidHom.ker = 3 ∧
        ∀ P : Sylow 3 G,
          Nat.card (P : Subgroup G) = 27 ∧
            Nat.card (↥(Subgroup.center (↥(P : Subgroup G)))) = 3 := by
  obtain ⟨G, instG, instFin, instQS, f, hker⟩ :=
    __ch5_Theorem523_exists_algebraic_triple_cover_a6_new
  let : Group G := instG
  let : Finite G := instFin
  let : IsQuasisimple G := instQS
  exact ⟨G, instG, instFin, instQS, f, hker,
    __ch5_Theorem523_a6_sylow3_heisenberg_of_algebraic_triple_cover_new f hker⟩

/-- Theorem 5.2.3(d), Sylow-3 clause for `3.A7`. -/
public theorem theorem_5_2_3_d_sylow3_3A7 :
    ∃ (G : Type) (_instG : Group G) (_instFin : Finite G)
      (_instQS : IsQuasisimple G)
      (f : Covering G (alternatingGroup (Fin 7))),
      Nat.card f.toMonoidHom.ker = 3 ∧
        ∀ P : Sylow 3 G,
          Nat.card (P : Subgroup G) = 27 ∧
            Nat.card (↥(Subgroup.center (↥(P : Subgroup G)))) = 3 := by
  obtain ⟨G, instG, instFin, instQS, f, hker⟩ :=
    __ch5_Theorem523_exists_algebraic_triple_cover_a7_new
  let : Group G := instG
  let : Finite G := instFin
  let : IsQuasisimple G := instQS
  exact ⟨G, instG, instFin, instQS, f, hker,
    __ch5_Theorem523_a7_sylow3_heisenberg_of_algebraic_triple_cover_new f hker⟩


private theorem __ch5_Theorem523_factorization_six_three : Nat.factorization 6 3 = 1 := by
  have hzero : padicValNat 3 2 = 0 :=
    padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr (by norm_num)))
  rw [Nat.factorization_def 6 Nat.prime_three,
    show (6 : Nat) = 3 ^ 1 * 2 by norm_num,
    padicValNat_base_pow_mul (by norm_num) (by norm_num) 1, hzero]

private theorem __ch5_Theorem523_subgroup_eq_of_isCyclic_card_eq_three_of_card_eq_six
    {K : Type*} [Group K] [Finite K] (hcyc : IsCyclic K)
    (hK : Nat.card K = 6) (H₁ H₂ : Subgroup K)
    (h₁ : Nat.card H₁ = 3) (h₂ : Nat.card H₂ = 3) : H₁ = H₂ := by
  let : IsCyclic K := hcyc
  let : CommGroup K := hcyc.commGroup
  let P₁ : Sylow 3 K := Sylow.ofCard H₁ (by
    rw [h₁, hK, __ch5_Theorem523_factorization_six_three]
    norm_num)
  let P₂ : Sylow 3 K := Sylow.ofCard H₂ (by
    rw [h₂, hK, __ch5_Theorem523_factorization_six_three]
    norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K P₁ P₂
  have hfix : g • P₁ = P₁ := Sylow.smul_eq_of_normal
  have hP : P₁ = P₂ := hfix.symm.trans hg
  exact congrArg Sylow.toSubgroup hP

private theorem __ch5_Theorem523_coveringIso_of_cyclic_kernel_card_six
    {L₀ G : Type} {G₁ : Type __ch5_Theorem523_w₁} {G₂ : Type __ch5_Theorem523_w₂}
    [Group L₀] [Finite L₀] [IsQuasisimple L₀]
    [Group G] [Finite G] [IsQuasisimple G]
    [Group G₁] [Finite G₁] [IsQuasisimple G₁]
    [Group G₂] [Finite G₂] [IsQuasisimple G₂]
    (f₀ : Covering L₀ G)
    (hf₁ : Covering.IsUniversal.{0, 0, __ch5_Theorem523_w₁} f₀)
    (hf₂ : Covering.IsUniversal.{0, 0, __ch5_Theorem523_w₂} f₀)
    (hcyc : IsCyclic (↥f₀.toMonoidHom.ker))
    (hcard : Nat.card f₀.toMonoidHom.ker = 6)
    (f₁ : Covering G₁ G) (f₂ : Covering G₂ G)
    (hk₁ : Nat.card f₁.toMonoidHom.ker = 2)
    (hk₂ : Nat.card f₂.toMonoidHom.ker = 2) :
    ∃! e : G₁ ≃* G₂, f₂.comp (Covering.ofMulEquiv e) = f₁ := by
  let h₁ : Covering L₀ G₁ := Covering.IsUniversal.lift hf₁ f₁
  let h₂ : Covering L₀ G₂ := Covering.IsUniversal.lift hf₂ f₂
  have hfac₁ : f₁.comp h₁ = f₀ := Covering.IsUniversal.lift_fac hf₁ f₁
  have hfac₂ : f₂.comp h₂ = f₀ := Covering.IsUniversal.lift_fac hf₂ f₂
  have hle₁ : h₁.toMonoidHom.ker ≤ f₀.toMonoidHom.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    change h₁ x = 1 at hx
    have hpt : f₁ (h₁ x) = f₀ x := by
      simpa using DFunLike.congr_fun hfac₁ x
    calc
      f₀ x = f₁ (h₁ x) := hpt.symm
      _ = 1 := by rw [hx]; exact map_one f₁.toMonoidHom
  have hle₂ : h₂.toMonoidHom.ker ≤ f₀.toMonoidHom.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    change h₂ x = 1 at hx
    have hpt : f₂ (h₂ x) = f₀ x := by
      simpa using DFunLike.congr_fun hfac₂ x
    calc
      f₀ x = f₂ (h₂ x) := hpt.symm
      _ = 1 := by rw [hx]; exact map_one f₂.toMonoidHom
  have hcomap₁ : f₁.toMonoidHom.ker.comap h₁.toMonoidHom = f₀.toMonoidHom.ker := by
    ext x
    rw [Subgroup.mem_comap, MonoidHom.mem_ker, MonoidHom.mem_ker]
    change f₁ (h₁ x) = 1 ↔ f₀ x = 1
    have hpt : f₁ (h₁ x) = f₀ x := by
      simpa using DFunLike.congr_fun hfac₁ x
    rw [hpt]
  have hcomap₂ : f₂.toMonoidHom.ker.comap h₂.toMonoidHom = f₀.toMonoidHom.ker := by
    ext x
    rw [Subgroup.mem_comap, MonoidHom.mem_ker, MonoidHom.mem_ker]
    change f₂ (h₂ x) = 1 ↔ f₀ x = 1
    have hpt : f₂ (h₂ x) = f₀ x := by
      simpa using DFunLike.congr_fun hfac₂ x
    rw [hpt]
  have hkerCard₁ : Nat.card h₁.toMonoidHom.ker = 3 := by
    have hmul := card_comap_mul h₁.toMonoidHom h₁.surjective f₁.toMonoidHom.ker
    rw [hcomap₁, hcard, hk₁] at hmul
    omega
  have hkerCard₂ : Nat.card h₂.toMonoidHom.ker = 3 := by
    have hmul := card_comap_mul h₂.toMonoidHom h₂.surjective f₂.toMonoidHom.ker
    rw [hcomap₂, hcard, hk₂] at hmul
    omega
  have hsubCard₁ : Nat.card (h₁.toMonoidHom.ker.subgroupOf f₀.toMonoidHom.ker) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle₁).toEquiv, hkerCard₁]
  have hsubCard₂ : Nat.card (h₂.toMonoidHom.ker.subgroupOf f₀.toMonoidHom.ker) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle₂).toEquiv, hkerCard₂]
  have hsubEq :
      h₁.toMonoidHom.ker.subgroupOf f₀.toMonoidHom.ker =
        h₂.toMonoidHom.ker.subgroupOf f₀.toMonoidHom.ker :=
    __ch5_Theorem523_subgroup_eq_of_isCyclic_card_eq_three_of_card_eq_six hcyc hcard _ _
      hsubCard₁ hsubCard₂
  have hkerEq : h₁.toMonoidHom.ker = h₂.toMonoidHom.ker := by
    calc
      h₁.toMonoidHom.ker =
          (h₁.toMonoidHom.ker.subgroupOf f₀.toMonoidHom.ker).map
            f₀.toMonoidHom.ker.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hle₁).symm
      _ = (h₂.toMonoidHom.ker.subgroupOf f₀.toMonoidHom.ker).map
            f₀.toMonoidHom.ker.subtype := by rw [hsubEq]
      _ = h₂.toMonoidHom.ker := Subgroup.map_subgroupOf_eq_of_le hle₂
  exact Covering.coveringIso_of_liftKernel_eq f₀ hf₁ hf₂ f₁ f₂ (by
    simpa [h₁, h₂] using hkerEq)

/-- Theorem 5.2.3, unrestricted uniqueness: two double covers of the same
alternating group are uniquely isomorphic over the base.  Unlike
`theorem_5_2_3_a_2_universal` this does not assume universality; it is the
full Schur uniqueness statement for `A_{n+5}`. -/
public theorem theorem_5_2_3_a_2
    {G₁ : Type __ch5_Theorem523_w₁} {G₂ : Type __ch5_Theorem523_w₂}
    [Group G₁] [Finite G₁] [IsQuasisimple G₁]
    [Group G₂] [Finite G₂] [IsQuasisimple G₂]
    (n : Nat)
    (f₁ : Covering G₁ (alternatingGroup (Fin (n + 5))))
    (f₂ : Covering G₂ (alternatingGroup (Fin (n + 5))))
    (hk₁ : Nat.card f₁.toMonoidHom.ker = 2)
    (hk₂ : Nat.card f₂.toMonoidHom.ker = 2) :
    ∃! e : G₁ ≃* G₂, f₂.comp (Covering.ofMulEquiv e) = f₁ := by
  by_cases hn6 : n + 5 = 6
  · have hn : n = 1 := by omega
    subst n
    exact __ch5_Theorem523_coveringIso_of_cyclic_kernel_card_six
      (alternatingFreeCentralCovering 1)
      (alternatingFreeCentralCovering_isUniversal 1)
      (alternatingFreeCentralCovering_isUniversal 1)
      a6UniversalKernel_isCyclic
      (a6UniversalKernel_card_eq_six a6UniversalKernel_three_dvd_new)
      f₁ f₂ hk₁ hk₂
  · by_cases hn7 : n + 5 = 7
    · have hn : n = 2 := by omega
      subst n
      exact __ch5_Theorem523_coveringIso_of_cyclic_kernel_card_six
        (alternatingFreeCentralCovering 2)
        (alternatingFreeCentralCovering_isUniversal 2)
        (alternatingFreeCentralCovering_isUniversal 2)
        a7UniversalKernel_isCyclic
        (a7UniversalKernel_card_eq_six a7UniversalKernel_three_dvd_new)
        f₁ f₂ hk₁ hk₂
    · exact Covering.coveringIso_of_card_two
        (schurAlternatingCovering n)
        (theorem_5_2_3_b_universality n hn6 hn7)
        (theorem_5_2_3_b_universality n hn6 hn7)
        (natCard_ker_schurAlternatingCovering n)
        f₁ f₂ hk₁ hk₂

end GLS3.Chapter5.SchurPresentation
/- END Theory.Theorem523 -/

/- BEGIN Theory.InvolutionCycleRotationCoordinateRelation -/
noncomputable section
namespace GLS3.Chapter5
universe __ch5_InvolutionCycleRotationCoordinateRelation_u
/-- Involution rotation coordinates are prime-cycle coordinates transported
along `orderOf x = 2`. -/
public theorem involutionCycleRotationCoordinates_eq_primeTransport
    {Ω : Type __ch5_InvolutionCycleRotationCoordinateRelation_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2) :
    involutionCycleRotationCoordinates x hx =
      (primeCycleRotationCoordinates x (by simpa [hx] using Nat.prime_two)).trans
        (MulEquiv.piCongrRight fun _ : x.cycleFactorsFinset =>
          AddEquiv.toMultiplicative (ZMod.ringEquivCongr hx).toAddEquiv) := by
  apply MulEquiv.ext
  intro a
  funext c
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (a c).2
  have hac : a c = (cycleFactorGenerator c) ^ i := by
    apply Subtype.ext
    exact hi.symm
  change _ = Multiplicative.ofAdd (ZMod.ringEquivCongr hx
    (Multiplicative.toAdd ((primeCycleRotationCoordinates x _) a c)))
  rw [show (involutionCycleRotationCoordinates x hx) a c =
      Multiplicative.ofAdd (i : ZMod 2) by
    rw [involutionCycleRotationCoordinates_apply, hac,
      zmodMulEquivOfGenerator_symm_apply_zpow]]
  rw [show (primeCycleRotationCoordinates x _) a c =
      Multiplicative.ofAdd (i : ZMod (orderOf x)) by
    rw [primeCycleRotationCoordinates_apply, hac,
      zmodMulEquivOfGenerator_symm_apply_zpow]]
  change Multiplicative.ofAdd (i : ZMod 2) =
    Multiplicative.ofAdd (ZMod.ringEquivCongr hx (i : ZMod (orderOf x)))
  rw [ZMod.ringEquivCongr_intCast]
end GLS3.Chapter5
/- END Theory.InvolutionCycleRotationCoordinateRelation -/

/- BEGIN Theory.PrimeCycleWreathEquiv -/
noncomputable section

open GLS3.Chapter5.SchurPresentation

namespace GLS3.Chapter5
universe __ch5_PrimeCycleWreathEquiv_u

public abbrev PrimeCycleWreath
    {Ω : Type __ch5_PrimeCycleWreathEquiv_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) :=
  ((c : x.cycleFactorsFinset) → Multiplicative (ZMod (orderOf x))) ⋊[
    SchurPresentation.permuteCoordinatesHom x.cycleFactorsFinset
      (Multiplicative (ZMod (orderOf x)))]
    Equiv.Perm x.cycleFactorsFinset

/-- The rotation-permutation semidirect product of a prime-order permutation
is the standard wreath product on its cycle factors. -/
@[expose]
public noncomputable def primeCycleRotationPermutationSemidirectEquiv
    {Ω : Type __ch5_PrimeCycleWreathEquiv_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : (orderOf x).Prime) :
    InvolutionRotationPermutationSemidirect x ≃* PrimeCycleWreath x :=
  SemidirectProduct.congr
    (primeCycleRotationCoordinates x hx)
    (theorem_5_2_2_d_3_a x hx)
    (primeCycleRotationNaturalAction x hx)

end GLS3.Chapter5
/- END Theory.PrimeCycleWreathEquiv -/

/- BEGIN KGroup.GLS3.Chapter5.theorem_5_2_3 -/

/- END KGroup.GLS3.Chapter5.theorem_5_2_3 -/

/- BEGIN Theory.InvolutionCycleRotationNaturalAction -/
noncomputable section
open GLS3.Chapter5.SchurPresentation
namespace GLS3.Chapter5
universe __ch5_InvolutionCycleRotationNaturalAction_u
/-- The cycle-permuting complement acts on involution rotation coordinates
by the standard coordinate permutation. -/
public theorem involutionCycleRotationNaturalAction
    {Ω : Type __ch5_InvolutionCycleRotationNaturalAction_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2)
    (l : cyclePermutationSubgroup x) :
    ((cyclePermutationActionOnCycleRotations x) l).trans
        (involutionCycleRotationCoordinates x hx) =
      (involutionCycleRotationCoordinates x hx).trans
        (SchurPresentation.permuteCoordinatesHom
          x.cycleFactorsFinset (Multiplicative (ZMod 2))
          ((theorem_5_2_2_d_3_a x (by simpa [hx] using Nat.prime_two)) l)) := by
  let hp : (orderOf x).Prime := by simpa [hx] using Nat.prime_two
  let q := MulEquiv.piCongrRight fun _ : x.cycleFactorsFinset =>
    AddEquiv.toMultiplicative (ZMod.ringEquivCongr hx).toAddEquiv
  rw [involutionCycleRotationCoordinates_eq_primeTransport]
  apply MulEquiv.ext
  intro a
  funext c
  have h := congrArg (fun E => E a)
    (primeCycleRotationNaturalAction x hp l)
  have hc := congrFun h c
  change q ((primeCycleRotationCoordinates x hp)
      ((cyclePermutationActionOnCycleRotations x) l a)) c =
    q ((primeCycleRotationCoordinates x hp) a)
      (((theorem_5_2_2_d_3_a x hp) l)⁻¹ c)
  exact congrArg (fun z => Multiplicative.ofAdd
    (ZMod.ringEquivCongr hx (Multiplicative.toAdd z))) hc
end GLS3.Chapter5
/- END Theory.InvolutionCycleRotationNaturalAction -/

/- BEGIN Theory.InvolutionWreathEquiv -/
noncomputable section

open GLS3.Chapter5.SchurPresentation

namespace GLS3.Chapter5
universe __ch5_InvolutionWreathEquiv_u

public abbrev InvolutionWreath (r : Nat) :=
  (Fin r → Multiplicative (ZMod 2)) ⋊[
    SchurPresentation.permuteCoordinatesHom (Fin r)
      (Multiplicative (ZMod 2))]
    Equiv.Perm (Fin r)

@[expose]
public def reindexZModTwoAddEquiv {I : Type*} [Fintype I]
    (e : I ≃ Fin (Fintype.card I)) :
    (I → ZMod 2) ≃+ (Fin (Fintype.card I) → ZMod 2) where
  toFun f i := f (e.symm i)
  invFun f i := f (e i)
  left_inv f := by ext i; simp
  right_inv f := by ext i; simp
  map_add' _ _ := rfl

@[expose]
public noncomputable def involutionWreathBaseEquiv
    {I : Type*} [Fintype I]
    (e : I ≃ Fin (Fintype.card I)) {m : Nat} (hm : m = 2) :
    (I → Multiplicative (ZMod m)) ≃*
      (Fin (Fintype.card I) → Multiplicative (ZMod 2)) :=
  (MulEquiv.piCongrRight fun _ : I =>
      AddEquiv.toMultiplicative (ZMod.ringEquivCongr hm).toAddEquiv).trans
    ((MulEquiv.piMultiplicative fun _ : I => ZMod 2).symm.trans
      (AddEquiv.toMultiplicative (reindexZModTwoAddEquiv e)))

@[simp]
public theorem involutionWreathBaseEquiv_apply
    {I : Type*} [Fintype I]
    (e : I ≃ Fin (Fintype.card I)) {m : Nat} (hm : m = 2)
    (f : I → Multiplicative (ZMod m)) (i : Fin (Fintype.card I)) :
    involutionWreathBaseEquiv e hm f i = Multiplicative.ofAdd
      (ZMod.ringEquivCongr hm
        (Multiplicative.toAdd (f (e.symm i)))) := rfl

/-- Reindex the cycle factors of an involution by `Fin r`, obtaining the
standard wreath product `Z₂ wr Σ_r`. -/
@[expose]
public noncomputable def involutionPrimeCycleWreathEquiv
    {Ω : Type __ch5_InvolutionWreathEquiv_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2) :
    PrimeCycleWreath x ≃*
      InvolutionWreath (Fintype.card x.cycleFactorsFinset) := by
  let e := Fintype.equivFin x.cycleFactorsFinset
  let fn := involutionWreathBaseEquiv e hx
  let fg := e.permCongrHom
  apply SemidirectProduct.congr fn fg
  intro σ
  apply MulEquiv.ext
  intro f
  funext i
  change fn ((SchurPresentation.permuteCoordinatesHom _ _ σ) f) i =
    (SchurPresentation.permuteCoordinatesHom _ _ (fg σ)) (fn f) i
  rw [involutionWreathBaseEquiv_apply,
    SchurPresentation.permuteCoordinatesHom_apply,
    SchurPresentation.permuteCoordinatesHom_apply,
    involutionWreathBaseEquiv_apply]
  change Multiplicative.ofAdd
      (ZMod.ringEquivCongr hx
        (Multiplicative.toAdd (f (σ⁻¹ (e.symm i))))) =
    Multiplicative.ofAdd
      (ZMod.ringEquivCongr hx
        (Multiplicative.toAdd (f (e.symm ((e.permCongr σ)⁻¹ i)))))
  congr 3
  apply congrArg f
  apply e.injective
  rw [e.apply_symm_apply]
  rw [← Equiv.permCongr_apply]
  rfl

/-- The concrete rotation-permutation subgroup of an involution is the
standard wreath product `Z₂ wr Σ_r`. -/
@[expose]
public noncomputable def involutionRotationPermutationWreathEquiv
    {Ω : Type __ch5_InvolutionWreathEquiv_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2) :
    ↥(cycleRotationSubgroup x ⊔ cyclePermutationSubgroup x) ≃*
      InvolutionWreath (Fintype.card x.cycleFactorsFinset) :=
  (involutionRotationPermutationSemidirectEquiv x).symm.trans
    ((primeCycleRotationPermutationSemidirectEquiv x
      (by simpa [hx] using Nat.prime_two)).trans
      (involutionPrimeCycleWreathEquiv x hx))

end GLS3.Chapter5
/- END Theory.InvolutionWreathEquiv -/

/- BEGIN KGroup.GLS3.Chapter5.proposition_5_2_5 -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

private theorem __ch5_proposition_5_2_5_factorization_six_two : Nat.factorization 6 2 = 1 := by
  have hzero : padicValNat 2 3 = 0 :=
    padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr (by norm_num)))
  rw [Nat.factorization_def 6 Nat.prime_two,
    show (6 : Nat) = 2 ^ 1 * 3 by norm_num,
    padicValNat_base_pow_mul (by norm_num) (by norm_num) 1, hzero]

private theorem __ch5_proposition_5_2_5_subgroup_eq_of_isCyclic_card_eq_two_of_card_eq_six
    {M : Type*} [Group M] [Finite M] (hcyc : IsCyclic M)
    (hM : Nat.card M = 6) (H₁ H₂ : Subgroup M)
    (h₁ : Nat.card H₁ = 2) (h₂ : Nat.card H₂ = 2) : H₁ = H₂ := by
  let : IsCyclic M := hcyc
  let : CommGroup M := hcyc.commGroup
  let P₁ : Sylow 2 M := Sylow.ofCard H₁ (by
    rw [h₁, hM, __ch5_proposition_5_2_5_factorization_six_two]
    norm_num)
  let P₂ : Sylow 2 M := Sylow.ofCard H₂ (by
    rw [h₂, hM, __ch5_proposition_5_2_5_factorization_six_two]
    norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M P₁ P₂
  have hfix : g • P₁ = P₁ := Sylow.smul_eq_of_normal
  have hP : P₁ = P₂ := hfix.symm.trans hg
  exact congrArg Sylow.toSubgroup hP

/-- Two triple coverings of the same base are uniquely isomorphic when they
are quotients of a universal covering with cyclic kernel of order six. -/
public theorem coveringIso_of_cyclic_kernel_card_six_of_kernel_card_three
    {L₀ G G₁ G₂ : Type}
    [Group L₀] [Finite L₀] [IsQuasisimple L₀]
    [Group G] [Finite G] [IsQuasisimple G]
    [Group G₁] [Finite G₁] [IsQuasisimple G₁]
    [Group G₂] [Finite G₂] [IsQuasisimple G₂]
    (f₀ : Covering L₀ G) (hf₀ : Covering.IsUniversal.{0, 0, 0} f₀)
    (hcyc : IsCyclic (↥f₀.toMonoidHom.ker))
    (hcard : Nat.card f₀.toMonoidHom.ker = 6)
    (f₁ : Covering G₁ G) (f₂ : Covering G₂ G)
    (hk₁ : Nat.card f₁.toMonoidHom.ker = 3)
    (hk₂ : Nat.card f₂.toMonoidHom.ker = 3) :
    ∃! e : G₁ ≃* G₂, f₂.comp (Covering.ofMulEquiv e) = f₁ := by
  let h₁ : Covering L₀ G₁ := Covering.IsUniversal.lift hf₀ f₁
  let h₂ : Covering L₀ G₂ := Covering.IsUniversal.lift hf₀ f₂
  have hfac₁ : f₁.comp h₁ = f₀ := Covering.IsUniversal.lift_fac hf₀ f₁
  have hfac₂ : f₂.comp h₂ = f₀ := Covering.IsUniversal.lift_fac hf₀ f₂
  have hle₁ : h₁.toMonoidHom.ker ≤ f₀.toMonoidHom.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    change h₁ x = 1 at hx
    have hpt : f₁ (h₁ x) = f₀ x := by
      simpa using DFunLike.congr_fun hfac₁ x
    calc
      f₀ x = f₁ (h₁ x) := hpt.symm
      _ = 1 := by rw [hx]; exact map_one f₁.toMonoidHom
  have hle₂ : h₂.toMonoidHom.ker ≤ f₀.toMonoidHom.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    change h₂ x = 1 at hx
    have hpt : f₂ (h₂ x) = f₀ x := by
      simpa using DFunLike.congr_fun hfac₂ x
    calc
      f₀ x = f₂ (h₂ x) := hpt.symm
      _ = 1 := by rw [hx]; exact map_one f₂.toMonoidHom
  have hcomap₁ : f₁.toMonoidHom.ker.comap h₁.toMonoidHom = f₀.toMonoidHom.ker := by
    ext x
    rw [Subgroup.mem_comap, MonoidHom.mem_ker, MonoidHom.mem_ker]
    change f₁ (h₁ x) = 1 ↔ f₀ x = 1
    have hpt : f₁ (h₁ x) = f₀ x := by
      simpa using DFunLike.congr_fun hfac₁ x
    rw [hpt]
  have hcomap₂ : f₂.toMonoidHom.ker.comap h₂.toMonoidHom = f₀.toMonoidHom.ker := by
    ext x
    rw [Subgroup.mem_comap, MonoidHom.mem_ker, MonoidHom.mem_ker]
    change f₂ (h₂ x) = 1 ↔ f₀ x = 1
    have hpt : f₂ (h₂ x) = f₀ x := by
      simpa using DFunLike.congr_fun hfac₂ x
    rw [hpt]
  have hkerCard₁ : Nat.card h₁.toMonoidHom.ker = 2 := by
    have hmul := card_comap_mul h₁.toMonoidHom h₁.surjective f₁.toMonoidHom.ker
    rw [hcomap₁, hcard, hk₁] at hmul
    omega
  have hkerCard₂ : Nat.card h₂.toMonoidHom.ker = 2 := by
    have hmul := card_comap_mul h₂.toMonoidHom h₂.surjective f₂.toMonoidHom.ker
    rw [hcomap₂, hcard, hk₂] at hmul
    omega
  have hsubCard₁ : Nat.card (h₁.toMonoidHom.ker.subgroupOf f₀.toMonoidHom.ker) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle₁).toEquiv, hkerCard₁]
  have hsubCard₂ : Nat.card (h₂.toMonoidHom.ker.subgroupOf f₀.toMonoidHom.ker) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle₂).toEquiv, hkerCard₂]
  have hsubEq :
      h₁.toMonoidHom.ker.subgroupOf f₀.toMonoidHom.ker =
        h₂.toMonoidHom.ker.subgroupOf f₀.toMonoidHom.ker :=
    __ch5_proposition_5_2_5_subgroup_eq_of_isCyclic_card_eq_two_of_card_eq_six hcyc hcard _ _
      hsubCard₁ hsubCard₂
  have hkerEq : h₁.toMonoidHom.ker = h₂.toMonoidHom.ker := by
    calc
      h₁.toMonoidHom.ker =
          (h₁.toMonoidHom.ker.subgroupOf f₀.toMonoidHom.ker).map
            f₀.toMonoidHom.ker.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hle₁).symm
      _ = (h₂.toMonoidHom.ker.subgroupOf f₀.toMonoidHom.ker).map
            f₀.toMonoidHom.ker.subtype := by rw [hsubEq]
      _ = h₂.toMonoidHom.ker := Subgroup.map_subgroupOf_eq_of_le hle₂
  exact Covering.coveringIso_of_liftKernel_eq f₀ hf₀ hf₀ f₁ f₂ (by
    simpa [h₁, h₂] using hkerEq)

private theorem __ch5_proposition_5_2_5_tripleCoverA7_sylow3
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (f : Covering K (alternatingGroup (Fin 7)))
    (hker : Nat.card f.toMonoidHom.ker = 3) :
    ∀ P : Sylow 3 K,
      Nat.card (P : Subgroup K) = 27 ∧
        Nat.card (↥(Subgroup.center ↥(P : Subgroup K))) = 3 := by
  obtain ⟨L₀, instL₀, finL₀, qsL₀, f₀, hf₀, hcyc, hcard⟩ :=
    theorem_5_2_3_c_multiplier_a7
  let : Group L₀ := instL₀
  let : Finite L₀ := finL₀
  let : IsQuasisimple L₀ := qsL₀
  obtain ⟨G, instG, finG, qsG, g, hgker, hgSylow⟩ :=
    theorem_5_2_3_d_sylow3_3A7
  let : Group G := instG
  let : Finite G := finG
  let : IsQuasisimple G := qsG
  obtain ⟨e, _, _⟩ :=
    coveringIso_of_cyclic_kernel_card_six_of_kernel_card_three
      f₀ hf₀ hcyc hcard f g hker hgker
  intro P
  let Q : Sylow 3 G := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ := hgSylow Q
  have eP : P ≃* Q := by
    change P ≃* P.map e.toMonoidHom
    exact e.subgroupMap P
  constructor
  · exact (Nat.card_congr eP.toEquiv).trans hQ.1
  · exact (Nat.card_congr (Subgroup.centerCongr eP).toEquiv).trans hQ.2

/-- Proposition 5.2.5: in a triple covering of `A₇`, the full preimage of
the standard root `A₆` is quasisimple, has center of order three, and has
central quotient `A₆`; equivalently, it is `3A₆`. -/
public theorem proposition_5_2_5
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (f : Covering K (alternatingGroup (Fin 7)))
    (hker : Nat.card f.toMonoidHom.ker = 3)
    (Lbar : Subgroup (alternatingGroup (Fin 7)))
    (hroot : ∃ omega : Fin 7, ∀ sigma : alternatingGroup (Fin 7),
      sigma ∈ Lbar ↔ sigma.1 omega = omega)
    (eLbar : Nonempty (↥Lbar ≃* alternatingGroup (Fin 6))) :
    let L := Lbar.comap f.toMonoidHom
    IsQuasisimple ↥L ∧
      Nat.card (Subgroup.center ↥L) = 3 ∧
      Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 6)) := by
  rcases hroot with ⟨_, _⟩
  let L : Subgroup K := Lbar.comap f.toMonoidHom
  change IsQuasisimple L ∧
    Nat.card (Subgroup.center L) = 3 ∧
    Nonempty (L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 6))
  obtain ⟨e⟩ := eLbar
  let r0 : L →* Lbar :=
    (f.toMonoidHom.comp L.subtype).codRestrict Lbar (fun x => x.2)
  let r : L →* alternatingGroup (Fin 6) := e.toMonoidHom.comp r0
  have hr0surj : Function.Surjective r0 := by
    intro y
    obtain ⟨x, hx⟩ := f.surjective y.1
    have hxL : x ∈ L := by
      have hfx : f x = y.1 := by simpa using hx
      change f x ∈ Lbar
      rw [hfx]
      exact y.2
    refine ⟨⟨x, hxL⟩, ?_⟩
    apply Subtype.ext
    exact hx
  have hrsurj : Function.Surjective r := e.surjective.comp hr0surj
  have hrkercenter : r.ker ≤ Subgroup.center L := by
    intro x hx
    have hr0x : r0 x = 1 := by
      apply e.injective
      simpa [r] using MonoidHom.mem_ker.mp hx
    have hfx : f x.1 = 1 := by
      change f x.1 = (1 : Lbar).1
      have hval := congrArg Subtype.val hr0x
      dsimp [r0] at hval
      change f x.1 = (1 : Lbar).1 at hval
      exact hval
    have hxGlobal : x.1 ∈ f.toMonoidHom.ker := MonoidHom.mem_ker.mpr hfx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (f.ker_le_center hxGlobal) y.1
  have hLcard : Nat.card L = Nat.card Lbar * Nat.card f.toMonoidHom.ker := by
    simpa [L] using card_comap_mul f.toMonoidHom f.surjective Lbar
  have hLbarCard : Nat.card Lbar = Nat.card (alternatingGroup (Fin 6)) :=
    Nat.card_congr e.toEquiv
  have hrCard : Nat.card L =
      Nat.card (alternatingGroup (Fin 6)) * Nat.card r.ker := by
    have h := card_comap_mul r hrsurj
      (⊤ : Subgroup (alternatingGroup (Fin 6)))
    simpa only [Subgroup.comap_top, Subgroup.card_top] using h
  have hrkerCard : Nat.card r.ker = 3 := by
    rw [hLbarCard, hker] at hLcard
    apply Nat.mul_left_cancel (Nat.card_pos :
      0 < Nat.card (alternatingGroup (Fin 6)))
    exact hrCard.symm.trans hLcard
  let D : Subgroup L := commutator L
  let rD : D →* alternatingGroup (Fin 6) := r.comp D.subtype
  have hrDsurj : Function.Surjective rD := by
    have hrRange : r.range = ⊤ := MonoidHom.range_eq_top.mpr hrsurj
    have hmap : D.map r = ⊤ := by
      dsimp [D]
      rw [map_commutator_eq, hrRange]
      exact Group.IsPerfect.commutator_eq_top
    intro y
    have hy : y ∈ D.map r := by rw [hmap]; trivial
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, hxy⟩
  let : Group.IsPerfect D :=
    commutator_isPerfect_of_surjective_of_ker_le_center r hrsurj hrkercenter
  let : Finite D := inferInstance
  have hrDkerDvd : Nat.card rD.ker ∣ Nat.card r.ker := by
    change Nat.card (r.ker.comap D.subtype) ∣ Nat.card r.ker
    exact Subgroup.card_comap_dvd_of_injective r.ker D.subtype D.subtype_injective
  rw [hrkerCard] at hrDkerDvd
  rcases (Nat.dvd_prime Nat.prime_three).mp hrDkerDvd with hrDkerCard | hrDkerCard
  · have hrDkerBot : rD.ker = ⊥ := Subgroup.card_eq_one.mp hrDkerCard
    let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    let B : Subgroup D := Theorem523BaseNine.a6StandardNine.comap rD
    have hBcard : Nat.card B = 9 := by
      have h := card_comap_mul rD hrDsurj Theorem523BaseNine.a6StandardNine
      rw [Theorem523BaseNine.a6_card, hrDkerCard, Nat.mul_one] at h
      exact h
    let : CommGroup B := IsPGroup.commGroupOfCardEqPrimeSq (p := 3) (by
      simpa using hBcard)
    let BD : Subgroup L := B.map D.subtype
    have hBDcard : Nat.card BD = 9 := by
      change Nat.card (B.map D.subtype) = 9
      rw [Subgroup.card_map_of_injective D.subtype_injective, hBcard]
    let : IsMulCommutative BD := Subgroup.map_isMulCommutative B D.subtype
    let : CommGroup BD :=
      Group.commGroupOfCenterEqTop (Subgroup.center_eq_top (G := BD))
    let R : Subgroup L := r.ker
    have hRcard : Nat.card R = 3 := hrkerCard
    let : IsCyclic R := isCyclic_of_prime_card hRcard
    let : CommGroup R := IsCyclic.commGroup
    have hBDleD : BD ≤ D := by
      intro x hx
      rcases hx with ⟨b, hb, rfl⟩
      exact b.2
    have hdisj : Disjoint R BD := by
      rw [disjoint_iff_inf_le]
      intro x hx
      rcases hx with ⟨hxR, hxBD⟩
      have hxD : x ∈ D := hBDleD hxBD
      let d : D := ⟨x, hxD⟩
      have hdker : d ∈ rD.ker := by
        rw [MonoidHom.mem_ker]
        exact MonoidHom.mem_ker.mp hxR
      have hd1 : d = 1 := by
        rw [hrDkerBot, Subgroup.mem_bot] at hdker
        exact hdker
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val hd1
    have hcomm (a : R) (b : BD) :
        Commute (R.subtype a) (BD.subtype b) := by
      rw [commute_iff_eq]
      exact (Subgroup.mem_center_iff.mp (hrkercenter a.2) b.1).symm
    let m : R × BD →* L :=
      MonoidHom.noncommCoprod R.subtype BD.subtype hcomm
    have hminj : Function.Injective m := by
      dsimp [m]
      rw [MonoidHom.noncommCoprod_injective]
      refine ⟨R.subtype_injective, BD.subtype_injective, ?_⟩
      simpa using hdisj
    have hmrangeCard : Nat.card m.range = 27 := by
      have hcardRange : Nat.card m.range = Nat.card (R × BD) :=
        (Nat.card_congr (Equiv.ofInjective m hminj)).symm
      calc
        Nat.card m.range = Nat.card (R × BD) := hcardRange
        _ = Nat.card R * Nat.card BD := Nat.card_prod _ _
        _ = 27 := by rw [hRcard, hBDcard]
    let A : Subgroup K := m.range.map L.subtype
    have hAcard : Nat.card A = 27 := by
      change Nat.card (m.range.map L.subtype) = 27
      rw [Subgroup.card_map_of_injective L.subtype_injective, hmrangeCard]
    let : IsMulCommutative A := Subgroup.map_isMulCommutative m.range L.subtype
    have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by
      rw [hAcard]
      norm_num)
    obtain ⟨P, hAP⟩ := hAp.exists_le_sylow
    have hP := __ch5_proposition_5_2_5_tripleCoverA7_sylow3 f hker P
    have hAeqP : A = (P : Subgroup K) := by
      apply Subgroup.eq_of_le_of_card_ge hAP
      rw [hAcard, hP.1]
    let : IsMulCommutative P := by
      rw [← hAeqP]
      infer_instance
    have hcenterTop : Subgroup.center P = ⊤ := Subgroup.center_eq_top
    rw [hcenterTop, Subgroup.card_top, hP.1] at hP
    omega
  · have hDcard : Nat.card D =
        Nat.card (alternatingGroup (Fin 6)) * 3 := by
      have h := card_comap_mul rD hrDsurj
        (⊤ : Subgroup (alternatingGroup (Fin 6)))
      simpa only [Subgroup.comap_top, Subgroup.card_top, hrDkerCard] using h
    have hDtop : D = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      exact hDcard.trans (hrCard.trans (by rw [hrkerCard])).symm
    have hperfect : commutator L = ⊤ := by simpa [D] using hDtop
    let : Group.IsPerfect L := ⟨hperfect⟩
    have hrkerEqCenter : r.ker = Subgroup.center L := by
      apply ker_eq_center_of_surjective_of_center_eq_bot r hrsurj hrkercenter
      exact alternatingGroup.center_eq_bot (by simp)
    let q : L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 6) :=
      (QuotientGroup.quotientMulEquivOfEq hrkerEqCenter.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective r hrsurj)
    let : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by simp)
    let : IsQuasisimple L := {
      toIsPerfect := inferInstance
      simple := q.isSimpleGroup
    }
    exact ⟨inferInstance, by rw [← hrkerEqCenter, hrkerCard], ⟨q⟩⟩

end GLS3.Chapter5.SchurPresentation
/- END KGroup.GLS3.Chapter5.proposition_5_2_5 -/

/- BEGIN Theory.DoubleCoverAutomorphismLift -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

/-- Every automorphism of an alternating quotient lifts uniquely to any Schur
double cover. This is the double-cover analogue of the universal-cover lift
API and includes the exceptional degrees six and seven through unrestricted
covering uniqueness. -/
public theorem existsUnique_doubleCoverLiftMulAut
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (alpha : MulAut (alternatingGroup (Fin (n + 5)))) :
    ∃! beta : MulAut G,
      f.comp (Covering.ofMulEquiv beta) =
        (Covering.ofMulEquiv alpha).comp f := by
  let g : Covering G (alternatingGroup (Fin (n + 5))) :=
    (Covering.ofMulEquiv alpha).comp f
  have hker : g.toMonoidHom.ker = f.toMonoidHom.ker := by
    ext x
    change alpha (f x) = 1 ↔ f x = 1
    constructor
    · intro hx
      exact alpha.injective (by simpa using hx)
    · intro hx
      simp [hx]
  have hgcard : Nat.card g.toMonoidHom.ker = 2 := by
    rw [hker, hcard]
  simpa [g] using theorem_5_2_3_a_2 n g f hgcard hcard

@[expose] public noncomputable def doubleCoverLiftMulAut
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (alpha : MulAut (alternatingGroup (Fin (n + 5)))) : MulAut G :=
  Classical.choose (existsUnique_doubleCoverLiftMulAut n f hcard alpha)

public theorem doubleCoverLiftMulAut_fac
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (alpha : MulAut (alternatingGroup (Fin (n + 5)))) :
    f.comp (Covering.ofMulEquiv
      (doubleCoverLiftMulAut n f hcard alpha)) =
        (Covering.ofMulEquiv alpha).comp f :=
  (Classical.choose_spec
    (existsUnique_doubleCoverLiftMulAut n f hcard alpha)).1

public theorem doubleCoverLiftMulAut_unique
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (alpha : MulAut (alternatingGroup (Fin (n + 5))))
    {beta : MulAut G}
    (hbeta : f.comp (Covering.ofMulEquiv beta) =
      (Covering.ofMulEquiv alpha).comp f) :
    beta = doubleCoverLiftMulAut n f hcard alpha :=
  (existsUnique_doubleCoverLiftMulAut n f hcard alpha).unique hbeta
    (doubleCoverLiftMulAut_fac n f hcard alpha)

@[expose] public noncomputable def doubleCoverLiftMulAutHom
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2) :
    MulAut (alternatingGroup (Fin (n + 5))) →* MulAut G where
  toFun := doubleCoverLiftMulAut n f hcard
  map_one' := by
    symm
    apply doubleCoverLiftMulAut_unique n f hcard 1
    apply Theory.GroupTheory.Covering.ext
    intro x
    rfl
  map_mul' alpha beta := by
    symm
    apply doubleCoverLiftMulAut_unique n f hcard (alpha * beta)
    apply Theory.GroupTheory.Covering.ext
    intro x
    have halpha := congrArg (fun q : Covering G (alternatingGroup (Fin (n + 5))) =>
      q (doubleCoverLiftMulAut n f hcard beta x))
      (doubleCoverLiftMulAut_fac n f hcard alpha)
    have hbeta := congrArg (fun q : Covering G (alternatingGroup (Fin (n + 5))) => q x)
      (doubleCoverLiftMulAut_fac n f hcard beta)
    exact halpha.trans (congrArg (fun y => alpha y) hbeta)

public theorem doubleCoverLiftMulAutHom_injective
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2) :
    Function.Injective (doubleCoverLiftMulAutHom n f hcard) := by
  intro alpha beta hab
  apply MulEquiv.ext
  intro y
  obtain ⟨x, rfl⟩ := f.surjective y
  have halpha := congrArg
    (fun q : Covering G (alternatingGroup (Fin (n + 5))) => q x)
    (doubleCoverLiftMulAut_fac n f hcard alpha)
  have hbeta := congrArg
    (fun q : Covering G (alternatingGroup (Fin (n + 5))) => q x)
    (doubleCoverLiftMulAut_fac n f hcard beta)
  change f (doubleCoverLiftMulAutHom n f hcard alpha x) = alpha (f x) at halpha
  change f (doubleCoverLiftMulAutHom n f hcard beta x) = beta (f x) at hbeta
  rw [hab] at halpha
  exact halpha.symm.trans hbeta

public theorem orderOf_doubleCoverLiftMulAut
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (alpha : MulAut (alternatingGroup (Fin (n + 5)))) :
    orderOf (doubleCoverLiftMulAut n f hcard alpha) = orderOf alpha := by
  change orderOf (doubleCoverLiftMulAutHom n f hcard alpha) = orderOf alpha
  exact orderOf_injective (doubleCoverLiftMulAutHom n f hcard)
    (doubleCoverLiftMulAutHom_injective n f hcard) alpha

end GLS3.Chapter5.SchurPresentation
/- END Theory.DoubleCoverAutomorphismLift -/

/- BEGIN Theory.DoubleCoverRootInvolutionSquare -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

open RootFourSubgroup

/-- In every finite perfect central double cover of an alternating group, the
standard root involution has a lift with nontrivial square. -/
public theorem exists_lift_rho1_sq_ne_one_of_central_extension_ker_card_two
    (q : Nat) {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (f : H →* alternatingGroup (Fin (q + 5)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hcard : Nat.card f.ker = 2) :
    ∃ u : H,
      f u = (⟨rho1 q, rho1_mem_alternating q⟩ :
        alternatingGroup (Fin (q + 5))) ∧
      u ^ 2 ≠ 1 := by
  have hkerEq : f.ker = Subgroup.center H := by
    apply ker_eq_center_of_surjective_of_center_eq_bot f hf hker
    exact alternatingGroup.center_eq_bot (by simp)
  let eH : H ⧸ Subgroup.center H ≃* alternatingGroup (Fin (q + 5)) :=
    (QuotientGroup.quotientMulEquivOfEq hkerEq.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  let : IsQuasisimple H := {
    toIsPerfect := inferInstance
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin (q + 5))) :=
        alternatingGroup.isSimpleGroup (by simp)
      exact eH.isSimpleGroup
  }
  let c : Covering H (alternatingGroup (Fin (q + 5))) := {
    toMonoidHom := f
    surjective := hf
  }
  obtain ⟨e, he, _⟩ := theorem_5_2_3_a_2 q
    (schurAlternatingCovering q) c
    (natCard_ker_schurAlternatingCovering q) (by simpa [c] using hcard)
  let u : H := e (u1 q)
  have hstd : schurAlternatingCovering q (u1 q) =
      (⟨rho1 q, rho1_mem_alternating q⟩ :
        alternatingGroup (Fin (q + 5))) := by
    apply Subtype.ext
    exact u1_proj q
  have hfac : c (e (u1 q)) = schurAlternatingCovering q (u1 q) := by
    change (c.comp (Covering.ofMulEquiv e)) (u1 q) =
      schurAlternatingCovering q (u1 q)
    rw [he]
  refine ⟨u, hfac.trans hstd, ?_⟩
  have hu2eq : u ^ 2 = e (schurAlternatingCentral q) := by
    change e (u1 q) ^ 2 = e (schurAlternatingCentral q)
    rw [← map_pow, u1_sq]
  rw [hu2eq]
  intro h
  apply schurAlternatingCentral_ne_one q
  apply e.injective
  simpa using h

end GLS3.Chapter5.SchurPresentation
/- END Theory.DoubleCoverRootInvolutionSquare -/

/- BEGIN Theory.ThreeDvdCenterForcesExceptionalDegree -/
noncomputable section

namespace GLS3.Chapter5

/-- A central quotient isomorphic to `Aₙ` whose center order is divisible by
three can occur only in the two exceptional Schur-multiplier degrees. -/
public theorem three_dvd_center_forces_exceptional_degree
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (n : Nat) (hn : 5 ≤ n)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n))
    (hthree : 3 ∣ Nat.card (Subgroup.center K)) :
    n = 6 ∨ n = 7 := by
  let q := n - 5
  have hq : q + 5 = n := Nat.sub_add_cancel hn
  let : IsQuasisimple (alternatingGroup (Fin n)) := by
    rw [← hq]
    exact SchurPresentation.alternatingGroup_isQuasisimple q
  obtain ⟨f, hfker⟩ := exists_alternatingCenterQuotientCovering n e
  by_contra h
  have h6 : n ≠ 6 := fun hn6 => h (Or.inl hn6)
  have h7 : n ≠ 7 := fun hn7 => h (Or.inr hn7)
  have hq6 : q + 5 ≠ 6 := by simpa [hq] using h6
  have hq7 : q + 5 ≠ 7 := by simpa [hq] using h7
  let ef : Fin (q + 5) ≃ Fin n := finCongr hq
  let eA := ef.symm.altCongrHom
  let f' : K →* alternatingGroup (Fin (q + 5)) :=
    eA.toMonoidHom.comp f.toMonoidHom
  have hf'ker : f'.ker = f.toMonoidHom.ker := by
    rw [show f' = eA.toMonoidHom.comp f.toMonoidHom by rfl,
      MonoidHom.ker_comp_of_injective f.toMonoidHom eA.toMonoidHom eA.injective]
  let c : Covering K (alternatingGroup (Fin (q + 5))) := {
    toMonoidHom := f'
    surjective := eA.surjective.comp f.surjective
  }
  have hdiv : Nat.card f'.ker ∣ 2 := by
    have hkernel := Covering.coveringKernel_card_dvd_of_universal
      (SchurPresentation.schurAlternatingCovering q)
      (SchurPresentation.theorem_5_2_3_b_universality q hq6 hq7) c
    rw [SchurPresentation.theorem_5_2_3_a q] at hkernel
    simpa [c] using hkernel
  have : 3 ∣ 2 := by
    apply hthree.trans
    rw [← hfker, ← hf'ker]
    exact hdiv
  norm_num at this

end GLS3.Chapter5
/- END Theory.ThreeDvdCenterForcesExceptionalDegree -/

/- BEGIN Theory.proposition_5_2_4_a_general -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

/-- Proposition 5.2.4(a) for an arbitrary Schur double cover: every lift of a
root involution has order four. The nontrivial-square fact is transported from
the explicit Schur model through unrestricted double-cover uniqueness. -/
public theorem proposition_5_2_4_a_general
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (i : Fin (n + 3)) (hi : i ≠ 0) :
    orderOf (DoubleCoverUniqueness.suzukiLift n f i) = 4 := by
  obtain ⟨e, he, _⟩ := theorem_5_2_3_a_2 n f (schurAlternatingCovering n)
    hcard (natCard_ker_schurAlternatingCovering n)
  let x := DoubleCoverUniqueness.suzukiLift n f i
  let y := schurSuzukiGenerator n i
  have hbase : schurAlternatingCovering n (e x) =
      schurAlternatingCovering n y := by
    have heval := DFunLike.congr_fun he x
    change schurAlternatingCovering n (e x) = f x at heval
    rw [heval]
    change f (DoubleCoverUniqueness.suzukiLift n f i) =
      schurAlternatingProjection n (schurSuzukiGenerator n i)
    rw [DoubleCoverUniqueness.suzukiLift_apply]
    rfl
  have hsquares : (e x) ^ 2 = y ^ 2 :=
    DoubleCoverUniqueness.sq_eq_sq_of_apply_eq
      (schurAlternatingCovering n)
      (natCard_ker_schurAlternatingCovering n) hbase
  have hysq : y ^ 2 = schurAlternatingCentral n :=
    schurSuzukiGenerator_tail_sq n i hi
  have hxsq_ne : x ^ 2 ≠ 1 := by
    intro hx
    have hmap : (e x) ^ 2 = 1 := by
      calc
        (e x) ^ 2 = e (x ^ 2) := (map_pow e x 2).symm
        _ = e 1 := by rw [hx]
        _ = 1 := map_one e
    rw [hsquares, hysq] at hmap
    exact schurAlternatingCentral_ne_one n hmap
  exact DoubleCoverUniqueness.orderOf_suzukiLift_tail_eq_four_of_nontrivial_square
    n f hcard i hi hxsq_ne

end GLS3.Chapter5.SchurPresentation
/- END Theory.proposition_5_2_4_a_general -/

/- BEGIN Theory.proposition_5_2_4_f_general -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

/-- Proposition 5.2.4(f)(1) when the image of the ambient extension is the
alternating group: all elements lie over even permutations, and disjoint lifts
commute in every Schur double cover. -/
public theorem proposition_5_2_4_f_general_alternating
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2) (x y : G)
    (hdisjoint : Equiv.Perm.Disjoint (f x).1 (f y).1) :
    x * y * x⁻¹ * y⁻¹ = 1 := by
  obtain ⟨e, he, _⟩ := theorem_5_2_3_a_2 n f (schurAlternatingCovering n)
    hcard (natCard_ker_schurAlternatingCovering n)
  have hxbase : schurSymmetricProjection n (e x).1 = (f x).1 := by
    have h := DFunLike.congr_fun he x
    exact congrArg Subtype.val h
  have hybase : schurSymmetricProjection n (e y).1 = (f y).1 := by
    have h := DFunLike.congr_fun he y
    exact congrArg Subtype.val h
  have hcommRaw :
      (e x).1 * (e y).1 * (e x).1⁻¹ * (e y).1⁻¹ = 1 := by
    apply proposition_5_2_4_f_1 n (e x).1 (e y).1
    · simpa [hxbase, hybase] using hdisjoint
    · exact Or.inl (by simp [hxbase])
  have hcomm : e x * e y * (e x)⁻¹ * (e y)⁻¹ = 1 := by
    apply Subtype.ext
    exact hcommRaw
  apply e.injective
  simpa only [map_mul, map_inv, map_one] using hcomm

end GLS3.Chapter5.SchurPresentation
/- END Theory.proposition_5_2_4_f_general -/

/- BEGIN Theory.InvolutionSignKernelTraceZeroPermutationModule -/
noncomputable section
namespace GLS3.Chapter5
universe __ch5_InvolutionSignKernelTraceZeroPermutationModule_u
/-- The even rotation kernel and the cycle-permuting kernel form the natural
trace-zero permutation module for an involution. -/
public theorem involutionSignKernelIsTraceZeroPermutationModule
    {Ω : Type __ch5_InvolutionSignKernelTraceZeroPermutationModule_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2) :
    let C := Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))
    let χ : C →* ℤˣ := Equiv.Perm.sign.comp C.subtype
    let Z := χ.ker
    let RZ := (cycleRotationSubgroup x).comap Z.subtype
    let LZ := (cyclePermutationSubgroup x).comap Z.subtype
    IsTraceZeroPermutationModule RZ LZ
      (Fintype.card x.cycleFactorsFinset) := by
  dsimp only
  let C := Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))
  let χ : C →* ℤˣ := Equiv.Perm.sign.comp C.subtype
  let Z := χ.ker
  let RZ := (cycleRotationSubgroup x).comap Z.subtype
  let LZ := (cyclePermutationSubgroup x).comap Z.subtype
  let eFin := Fintype.equivFin x.cycleFactorsFinset
  let eR0 := evenCycleRotationsSignKernelEquiv x
  let eR := involutionRotationSignKernelEquivTraceZero x hx
    (Fintype.card x.cycleFactorsFinset) eFin
  let eL0 := subgroupComapKernelEquivOfLe χ (cyclePermutationSubgroup x) (by
    intro l hl
    rw [MonoidHom.mem_ker]
    exact involutionCyclePermutation_sign x hx ⟨l, hl⟩)
  let eL := (involutionCyclePermutationSignKernelEquiv x hx).trans eFin.permCongrHom
  refine ⟨eR, eL, ?_⟩
  intro l v
  let l0 : cyclePermutationSubgroup x := eL0 l
  let a : CycleRotationGroup x := (eR0 v).1
  let b : CycleRotationGroup x := (cyclePermutationActionOnCycleRotations x) l0 a
  have hb : b ∈ evenInvolutionCycleRotations x := by
    rw [mem_evenInvolutionCycleRotations]
    have hact := cyclePermutationActionOnCycleRotations_apply x l0 a
    have hactC : cycleRotationToCentralizer x b =
        l0.1 * cycleRotationToCentralizer x a * l0.1⁻¹ := by
      apply Subtype.ext
      exact hact
    rw [hactC]
    have ha : Equiv.Perm.sign ((cycleRotationToCentralizer x a).1) = 1 :=
      (mem_evenInvolutionCycleRotations x a).mp (eR0 v).2
    simp [map_mul, ha]
  let w : RZ := eR0.symm ⟨b, hb⟩
  refine ⟨w, ?_, ?_⟩
  · apply Subtype.ext
    have hw := evenCycleRotationsSignKernelEquiv_apply_coe x w
    have hwback : eR0 w = ⟨b, hb⟩ := eR0.apply_symm_apply ⟨b, hb⟩
    rw [hwback] at hw
    have hact := cyclePermutationActionOnCycleRotations_apply x l0 a
    have hactC : cycleRotationToCentralizer x b =
        l0.1 * cycleRotationToCentralizer x a * l0.1⁻¹ := by
      apply Subtype.ext
      exact hact
    change w.1.1 = l.1.1 * v.1.1 * l.1.1⁻¹
    rw [← hw, hactC, evenCycleRotationsSignKernelEquiv_apply_coe]
    change l0.1 * v.1.1 * l0.1⁻¹ = l.1.1 * v.1.1 * l.1.1⁻¹
    rw [show l0.1 = l.1.1 by
      exact subgroupComapKernelEquivOfLe_apply_coe χ
        (cyclePermutationSubgroup x) _ l]
  · funext i
    rw [involutionRotationSignKernelEquivTraceZero_apply,
      involutionRotationSignKernelEquivTraceZero_apply,
      evenInvolutionCycleRotations_mulEquiv_traceZero_apply,
      evenInvolutionCycleRotations_mulEquiv_traceZero_apply]
    have hwback : eR0 w = ⟨b, hb⟩ := eR0.apply_symm_apply ⟨b, hb⟩
    change Multiplicative.toAdd
        ((involutionCycleRotationCoordinates x hx) (eR0 w).1 (eFin.symm i)) = _
    rw [hwback]
    have hnat := congrArg (fun E => E a)
      (involutionCycleRotationNaturalAction x hx l0)
    have hcoord := congrFun hnat (eFin.symm i)
    have hcoord' :
        (involutionCycleRotationCoordinates x hx) b (eFin.symm i) =
          (involutionCycleRotationCoordinates x hx) a
            (((theorem_5_2_2_d_3_a x (by simpa [hx] using Nat.prime_two)) l0)⁻¹ (eFin.symm i)) := by
      simpa [b, SchurPresentation.permuteCoordinatesHom_apply] using hcoord
    change Multiplicative.toAdd
        ((involutionCycleRotationCoordinates x hx) b (eFin.symm i)) =
      Multiplicative.toAdd
        ((involutionCycleRotationCoordinates x hx) a
          (eFin.symm ((eL l).symm i)))
    rw [hcoord']
    let σ := (theorem_5_2_2_d_3_a x
      (by simpa [hx] using Nat.prime_two)) l0
    rw [show eL l = eFin.permCongr σ by
      change eFin.permCongr (involutionCyclePermutationSignKernelEquiv x hx l) = _
      rw [involutionCyclePermutationSignKernelEquiv_apply]]
    have hind : σ⁻¹ (eFin.symm i) =
        eFin.symm ((eFin.permCongr σ)⁻¹ i) := by
      apply eFin.injective
      rw [eFin.apply_symm_apply]
      rw [← Equiv.permCongr_apply]
      rfl
    rw [hind]
    rfl
end GLS3.Chapter5
/- END Theory.InvolutionSignKernelTraceZeroPermutationModule -/

/- BEGIN Theory.InvolutionTwoCycleRotationInvariant -/
noncomputable section
namespace GLS3.Chapter5
universe __ch5_InvolutionTwoCycleRotationInvariant_u

/-- The rotation supported on two involution cycles is fixed by the complement element swapping those cycles. -/
public theorem involutionTwoCycleRotation_fixed_by_swap
    {Ω : Type __ch5_InvolutionTwoCycleRotationInvariant_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2)
    (c d : x.cycleFactorsFinset) (hcd : c ≠ d) :
    let e := theorem_5_2_2_d_3_a x (by simpa [hx] using Nat.prime_two)
    let l := e.symm (Equiv.swap c d)
    let v : x.cycleFactorsFinset → Multiplicative (ZMod 2) :=
      fun k => if k = c ∨ k = d then Multiplicative.ofAdd 1 else 1
    let a := (involutionCycleRotationCoordinates x hx).symm v
    (cyclePermutationActionOnCycleRotations x) l a = a := by
  dsimp only
  let hp : (orderOf x).Prime := by simpa [hx] using Nat.prime_two
  let e := theorem_5_2_2_d_3_a x hp
  let l := e.symm (Equiv.swap c d)
  let v : x.cycleFactorsFinset → Multiplicative (ZMod 2) :=
    fun k => if k = c ∨ k = d then Multiplicative.ofAdd 1 else 1
  let a := (involutionCycleRotationCoordinates x hx).symm v
  apply (involutionCycleRotationCoordinates x hx).injective
  have hnat := congrArg (fun E => E a)
    (involutionCycleRotationNaturalAction x hx l)
  change (involutionCycleRotationCoordinates x hx)
      ((cyclePermutationActionOnCycleRotations x) l a) = _
  rw [show (involutionCycleRotationCoordinates x hx) a = v by simp [a]]
  have ha : (involutionCycleRotationCoordinates x hx) a = v := by simp [a]
  have hnat' : (involutionCycleRotationCoordinates x hx)
      ((cyclePermutationActionOnCycleRotations x) l a) =
      SchurPresentation.permuteCoordinatesHom
        x.cycleFactorsFinset (Multiplicative (ZMod 2)) (e l) v := by
    simpa only [MulEquiv.trans_apply, ha] using hnat
  rw [hnat']
  have hel : e l = Equiv.swap c d := e.apply_symm_apply _
  rw [hel]
  funext k
  simp only [SchurPresentation.permuteCoordinatesHom_apply]
  by_cases hkc : k = c
  · subst k
    simp [v, hcd]
  · by_cases hkd : k = d
    · subst k
      simp [v, hcd, Ne.symm hcd]
    · rw [Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne hkc hkd]

end GLS3.Chapter5
/- END Theory.InvolutionTwoCycleRotationInvariant -/

/- BEGIN Theory.InvolutionKernelWreathIndexTwo -/
noncomputable section

namespace GLS3.Chapter5
universe __ch5_InvolutionKernelWreathIndexTwo_u

/-- The even rotation-permutation factor of an involution is isomorphic to an
index-two subgroup of the standard wreath product. -/
public theorem involutionKernelWreathIndexTwo
    {Ω : Type __ch5_InvolutionKernelWreathIndexTwo_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2) :
    let C := Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))
    let χ : C →* ℤˣ := Equiv.Perm.sign.comp C.subtype
    let Z := χ.ker
    let RZ := (cycleRotationSubgroup x).comap Z.subtype
    let LZ := (cyclePermutationSubgroup x).comap Z.subtype
    ∃ P : Subgroup (InvolutionWreath (Fintype.card x.cycleFactorsFinset)),
      P.index = 2 ∧ Nonempty (↥(RZ ⊔ LZ) ≃* P) := by
  dsimp only
  let C := Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))
  let χ : C →* ℤˣ := Equiv.Perm.sign.comp C.subtype
  let Z := χ.ker
  let R : Subgroup C := cycleRotationSubgroup x
  let L : Subgroup C := cyclePermutationSubgroup x
  let H : Subgroup C := R ⊔ L
  let RZ : Subgroup Z := R.comap Z.subtype
  let LZ : Subgroup Z := L.comap Z.subtype
  let H1Z : Subgroup Z := RZ ⊔ LZ
  let ψ : H →* ℤˣ := χ.comp H.subtype
  let eW := involutionRotationPermutationWreathEquiv x hx
  let P : Subgroup (InvolutionWreath (Fintype.card x.cycleFactorsFinset)) :=
    ψ.ker.map eW.toMonoidHom
  have hHZ : H.comap Z.subtype = H1Z :=
    involutionRotationPermutationKernelPullback x hx
  let eHZ : H1Z ≃* H.comap Z.subtype := MulEquiv.subgroupCongr hHZ.symm
  let eKer := subgroupComapKernelEquivRestrictKernel χ H
  let eP := Subgroup.equivMapOfInjective ψ.ker eW.toMonoidHom eW.injective
  have hψsurj : Function.Surjective ψ := by
    obtain ⟨r0, hr0, hr0χ, _⟩ :=
      exists_odd_involution_mem_cycleRotationSubgroup x hx
    let rH : H := ⟨r0, (le_sup_left : R ≤ H) hr0⟩
    intro z
    rcases Int.units_eq_one_or z with rfl | rfl
    · exact ⟨1, map_one ψ⟩
    · exact ⟨rH, hr0χ⟩
  have hkerIndex : ψ.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hψsurj,
      Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_units_int]
  have hPindex : P.index = 2 := by
    exact (Subgroup.index_map_equiv ψ.ker eW).trans hkerIndex
  exact ⟨P, hPindex, ⟨eHZ.trans (eKer.trans eP)⟩⟩

end GLS3.Chapter5
/- END Theory.InvolutionKernelWreathIndexTwo -/

/- BEGIN Theory.InvolutionSignKernelFullExtensions -/
noncomputable section

namespace GLS3.Chapter5
universe __ch5_InvolutionSignKernelFullExtensions_u

/-- When an involution has at least two fixed points, one coupled odd
involution simultaneously completes the rotation-permutation factor to its
full wreath product and the fixed-point factor to its full symmetric group. -/
public theorem involutionSignKernelFullExtensions
    {Ω : Type __ch5_InvolutionSignKernelFullExtensions_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2)
    (hs : 2 ≤ Fintype.card (Function.fixedPoints x)) :
    let C := Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))
    let χ : C →* ℤˣ := Equiv.Perm.sign.comp C.subtype
    let Z := χ.ker
    let R := cycleRotationSubgroup x
    let L := cyclePermutationSubgroup x
    let I := fixedPointPermutationSubgroup x
    let RZ := R.comap Z.subtype
    let LZ := L.comap Z.subtype
    let IZ := I.comap Z.subtype
    ∃ t : Z,
      ((RZ ⊔ LZ) ⊔ IZ) ⊔ Subgroup.zpowers t = ⊤ ∧
      t ^ 2 = 1 ∧
      Subgroup.zpowers t ≤
        Subgroup.normalizer ((RZ ⊔ LZ : Subgroup Z) : Set Z) ∧
      Subgroup.zpowers t ≤ Subgroup.normalizer (IZ : Set Z) ∧
      Nonempty (↥((RZ ⊔ LZ) ⊔ Subgroup.zpowers t) ≃* ↥(R ⊔ L)) ∧
      Nonempty (↥(IZ ⊔ Subgroup.zpowers t) ≃*
        Equiv.Perm (Function.fixedPoints x)) := by
  dsimp only
  let C := Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))
  let χ : C →* ℤˣ := Equiv.Perm.sign.comp C.subtype
  let Z := χ.ker
  let R : Subgroup C := cycleRotationSubgroup x
  let L : Subgroup C := cyclePermutationSubgroup x
  let I : Subgroup C := fixedPointPermutationSubgroup x
  let H : Subgroup C := R ⊔ L
  let RZ : Subgroup Z := R.comap Z.subtype
  let LZ : Subgroup Z := L.comap Z.subtype
  let IZ : Subgroup Z := I.comap Z.subtype
  have hxprime : (orderOf x).Prime := by simpa [hx] using Nat.prime_two
  have hLχ : L ≤ χ.ker := by
    intro l hl
    rw [MonoidHom.mem_ker]
    exact involutionCyclePermutation_sign x hx ⟨l, hl⟩
  have hLnorm : L ≤ Subgroup.normalizer R :=
    cyclePermutationSubgroup_le_normalizer_cycleRotationSubgroup x
  have hIcomm : I ≤ Subgroup.centralizer (H : Set C) :=
    (theorem_5_2_2_d_1 x hxprime).2.2.2.2
  have hsup : I ⊔ H = ⊤ :=
    (theorem_5_2_2_d_1 x hxprime).2.2.2.1
  have hdisj : I ⊓ H = ⊥ :=
    (theorem_5_2_2_d_1 x hxprime).2.2.1
  obtain ⟨r0, hr0, hr0χ, hr02⟩ :=
    exists_odd_involution_mem_cycleRotationSubgroup x hx
  obtain ⟨i0, hi0, hi0χ, hi02⟩ :=
    exists_odd_involution_mem_fixedPointPermutationSubgroup x hs
  have hcomm : Commute r0 i0 := by
    have hi := hIcomm hi0
    rw [Subgroup.mem_centralizer_iff] at hi
    exact hi r0 ((le_sup_left : R ≤ H) hr0)
  let f := signKernelParityLift χ H I i0 hi0 hi0χ hi02 hIcomm
  let rH : H := ⟨r0, (le_sup_left : R ≤ H) hr0⟩
  let t : Z := f rH
  have htval : t.1 = i0 * r0 := by
    rw [show t.1 = r0 * i0 by
      dsimp [t, f, rH]
      rw [hr0χ, unitsInvolutionHom_neg_one]]
    exact hcomm.eq
  have hdecomp0 := signKernel_decomp_rotation_odd_pair χ R L I hLχ
    hLnorm hIcomm hsup r0 i0 hr0 hi0 hr0χ hi0χ hr02 hi02
  have hdecomp : ((RZ ⊔ LZ) ⊔ IZ) ⊔ Subgroup.zpowers t = ⊤ := by
    rw [show t = (⟨i0 * r0, by
      rw [MonoidHom.mem_ker, map_mul, hi0χ, hr0χ]
      norm_num⟩ : Z) by
        apply Subtype.ext
        exact htval]
    exact hdecomp0.1
  have ht2 : t ^ 2 = 1 := by
    rw [show t = (⟨i0 * r0, by
      rw [MonoidHom.mem_ker, map_mul, hi0χ, hr0χ]
      norm_num⟩ : Z) by
        apply Subtype.ext
        exact htval]
    exact hdecomp0.2
  have hHZ : H.comap Z.subtype = RZ ⊔ LZ :=
    involutionRotationPermutationKernelPullback x hx
  have htHnorm : Subgroup.zpowers t ≤
      Subgroup.normalizer ((RZ ⊔ LZ : Subgroup Z) : Set Z) := by
    rw [Subgroup.zpowers_le]
    rw [← hHZ]
    apply Subgroup.le_normalizer_comap Z.subtype
    change t.1 ∈ Subgroup.normalizer H
    rw [htval]
    exact (Subgroup.normalizer (H : Set C)).mul_mem
      (Subgroup.centralizer_le_normalizer (H : Set C) (hIcomm hi0))
      (Subgroup.le_normalizer ((le_sup_left : R ≤ H) hr0))
  have htInorm : Subgroup.zpowers t ≤ Subgroup.normalizer (IZ : Set Z) := by
    rw [Subgroup.zpowers_le]
    apply Subgroup.le_normalizer_comap Z.subtype
    change t.1 ∈ Subgroup.normalizer I
    rw [htval]
    have hr0I : r0 ∈ Subgroup.centralizer (I : Set C) := by
      rw [Subgroup.mem_centralizer_iff]
      intro i hi
      exact (hIcomm hi r0 ((le_sup_left : R ≤ H) hr0)).symm
    exact (Subgroup.normalizer (I : Set C)).mul_mem
      (Subgroup.le_normalizer hi0)
      (Subgroup.centralizer_le_normalizer (I : Set C) hr0I)
  have hHext : Nonempty
      (↥((RZ ⊔ LZ) ⊔ Subgroup.zpowers t) ≃* H) := by
    have hext := signKernelParityFullExtension χ H I r0 i0
      ((le_sup_left : R ≤ H) hr0) hi0 hr0χ hi0χ hr02 hi02 hIcomm hdisj
    change Nonempty (↥((H.comap Z.subtype) ⊔ Subgroup.zpowers t) ≃* H) at hext
    rw [hHZ] at hext
    exact hext
  let σ0 := theorem_5_2_2_d_4 x ⟨i0, hi0⟩
  have hσ0χ : Equiv.Perm.sign σ0 = -1 := by
    rw [← fixedPointPermutation_sign x ⟨i0, hi0⟩]
    exact hi0χ
  have hσ02 : σ0 ^ 2 = 1 := by
    have hi02_sub : (⟨i0, hi0⟩ : I) ^ 2 = 1 := by
      apply Subtype.ext
      simpa using hi02
    simpa only [map_pow, map_one] using
      congrArg (theorem_5_2_2_d_4 x) hi02_sub
  have hr0χ' : Equiv.Perm.sign r0.1 = -1 := by
    simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply] using hr0χ
  have hIext0 := involutionFixedPointFullExtension x r0 hr0 hr0χ' hr02
    σ0 hσ0χ hσ02
  let g := involutionFixedPointParityLift x r0 hr0 hr0χ' hr02
  have hgt : g σ0 = t := by
    apply Subtype.ext
    dsimp [g]
    rw [hσ0χ, unitsInvolutionHom_neg_one, htval]
    have hσ0 : fixedPointPermToCentralizer x σ0 = i0 := by
      have h := (fixedPointPermMulEquivSubgroup x).apply_symm_apply ⟨i0, hi0⟩
      exact congrArg Subtype.val h
    rw [hσ0]
  have hIext : Nonempty
      (↥(IZ ⊔ Subgroup.zpowers t) ≃*
        Equiv.Perm (Function.fixedPoints x)) := by
    change Nonempty (↥(IZ ⊔ Subgroup.zpowers (g σ0)) ≃*
      Equiv.Perm (Function.fixedPoints x)) at hIext0
    rw [hgt] at hIext0
    exact hIext0
  exact ⟨t, hdecomp, ht2, htHnorm, htInorm, hHext, hIext⟩

end GLS3.Chapter5
/- END Theory.InvolutionSignKernelFullExtensions -/

/- BEGIN Theory.TripleCoverA6Sylow3 -/
noncomputable section

namespace GLS3.Chapter5

/-- Every Sylow `3`-subgroup of an arbitrary triple cover of `A₆` has order
`27` and center of order `3`. -/
public theorem tripleCoverA6_sylow3
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (f : Covering K (alternatingGroup (Fin 6)))
    (hker : Nat.card f.toMonoidHom.ker = 3) :
    ∀ P : Sylow 3 K,
      Nat.card (P : Subgroup K) = 27 ∧
        Nat.card (Subgroup.center (P : Subgroup K)) = 3 := by
  obtain ⟨L₀, instL₀, finL₀, qsL₀, f₀, hf₀, hcyc, hcard⟩ :=
    SchurPresentation.theorem_5_2_3_c_multiplier_a6
  let : Group L₀ := instL₀
  let : Finite L₀ := finL₀
  let : IsQuasisimple L₀ := qsL₀
  obtain ⟨G, instG, finG, qsG, g, hgker, hgSylow⟩ :=
    SchurPresentation.theorem_5_2_3_d_sylow3_3A6
  let : Group G := instG
  let : Finite G := finG
  let : IsQuasisimple G := qsG
  obtain ⟨e, _, _⟩ :=
    SchurPresentation.coveringIso_of_cyclic_kernel_card_six_of_kernel_card_three
      f₀ hf₀ hcyc hcard f g hker hgker
  intro P
  let Q : Sylow 3 G :=
    P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ := hgSylow Q
  let eP : P ≃* Q := by
    change P ≃* P.map e.toMonoidHom
    exact e.subgroupMap P
  exact ⟨(Nat.card_congr eP.toEquiv).trans hQ.1,
    (Nat.card_congr (Subgroup.centerCongr eP).toEquiv).trans hQ.2⟩

end GLS3.Chapter5
/- END Theory.TripleCoverA6Sylow3 -/

/- BEGIN Theory.TripleCoverA7Sylow3 -/
noncomputable section

namespace GLS3.Chapter5

/-- Every Sylow `3`-subgroup of an arbitrary triple cover of `A₇` has order
`27` and center of order `3`. -/
public theorem tripleCoverA7_sylow3
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (f : Covering K (alternatingGroup (Fin 7)))
    (hker : Nat.card f.toMonoidHom.ker = 3) :
    ∀ P : Sylow 3 K,
      Nat.card (P : Subgroup K) = 27 ∧
        Nat.card (Subgroup.center (P : Subgroup K)) = 3 := by
  obtain ⟨L₀, instL₀, finL₀, qsL₀, f₀, hf₀, hcyc, hcard⟩ :=
    SchurPresentation.theorem_5_2_3_c_multiplier_a7
  let : Group L₀ := instL₀
  let : Finite L₀ := finL₀
  let : IsQuasisimple L₀ := qsL₀
  obtain ⟨G, instG, finG, qsG, g, hgker, hgSylow⟩ :=
    SchurPresentation.theorem_5_2_3_d_sylow3_3A7
  let : Group G := instG
  let : Finite G := finG
  let : IsQuasisimple G := qsG
  obtain ⟨e, _, _⟩ :=
    SchurPresentation.coveringIso_of_cyclic_kernel_card_six_of_kernel_card_three
      f₀ hf₀ hcyc hcard f g hker hgker
  intro P
  let Q : Sylow 3 G :=
    P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ := hgSylow Q
  let eP : P ≃* Q := by
    change P ≃* P.map e.toMonoidHom
    exact e.subgroupMap P
  exact ⟨(Nat.card_congr eP.toEquiv).trans hQ.1,
    (Nat.card_congr (Subgroup.centerCongr eP).toEquiv).trans hQ.2⟩

end GLS3.Chapter5
/- END Theory.TripleCoverA7Sylow3 -/

/- BEGIN Theory.DoubleCoverAutomorphismLiftIntertwine -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

/-- The unique lifts of a quotient automorphism to two Schur double covers are
intertwined by every covering equivalence over the alternating quotient. -/
public theorem doubleCoverLiftMulAut_intertwine
    {G₁ G₂ : Type} [Group G₁] [Finite G₁] [IsQuasisimple G₁]
    [Group G₂] [Finite G₂] [IsQuasisimple G₂]
    (n : Nat)
    (f₁ : Covering G₁ (alternatingGroup (Fin (n + 5))))
    (f₂ : Covering G₂ (alternatingGroup (Fin (n + 5))))
    (hk₁ : Nat.card f₁.toMonoidHom.ker = 2)
    (hk₂ : Nat.card f₂.toMonoidHom.ker = 2)
    (e : G₁ ≃* G₂)
    (he : f₂.comp (Covering.ofMulEquiv e) = f₁)
    (beta : MulAut (alternatingGroup (Fin (n + 5)))) :
    ∀ g : G₁,
      e (doubleCoverLiftMulAut n f₁ hk₁ beta g) =
        doubleCoverLiftMulAut n f₂ hk₂ beta (e g) := by
  let alpha₁ := doubleCoverLiftMulAut n f₁ hk₁ beta
  let alpha₂ := doubleCoverLiftMulAut n f₂ hk₂ beta
  have he_apply (g : G₁) : f₂ (e g) = f₁ g := by
    exact DFunLike.congr_fun he g
  have hhom : e.toMonoidHom.comp alpha₁.toMonoidHom =
      alpha₂.toMonoidHom.comp e.toMonoidHom := by
    apply monoidHom_eq_of_isPerfect_of_comp_eq
      f₂.toMonoidHom f₂.ker_le_center
    apply MonoidHom.ext
    intro g
    have h₁ := congrArg
      (fun q : Covering G₁ (alternatingGroup (Fin (n + 5))) => q g)
      (doubleCoverLiftMulAut_fac n f₁ hk₁ beta)
    have h₂ := congrArg
      (fun q : Covering G₂ (alternatingGroup (Fin (n + 5))) => q (e g))
      (doubleCoverLiftMulAut_fac n f₂ hk₂ beta)
    change f₁ (alpha₁ g) = beta (f₁ g) at h₁
    change f₂ (alpha₂ (e g)) = beta (f₂ (e g)) at h₂
    rw [he_apply] at h₂
    exact (he_apply (alpha₁ g)).trans (h₁.trans h₂.symm)
  intro g
  exact DFunLike.congr_fun hhom g

end GLS3.Chapter5.SchurPresentation
/- END Theory.DoubleCoverAutomorphismLiftIntertwine -/

/- BEGIN Theory.DoubleCoverFixedFiber -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

/-- A compatible lift of a quotient automorphism fixes the unique nontrivial
kernel element of a double cover. -/
public theorem doubleCoverLift_kernelInvolution_fixed
    {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hcard : Nat.card f.ker = 2)
    (alpha : MulAut G) (beta : MulAut Q)
    (hcompat : ∀ g : G, f (alpha g) = beta (f g)) :
    alpha (DoubleCoverUniqueness.kernelInvolution f hcard : G) =
      DoubleCoverUniqueness.kernelInvolution f hcard := by
  let z : G := DoubleCoverUniqueness.kernelInvolution f hcard
  have hzker : z ∈ f.ker :=
    DoubleCoverUniqueness.kernelInvolution f hcard |>.property
  have halphazker : alpha z ∈ f.ker := by
    rw [MonoidHom.mem_ker, hcompat, MonoidHom.mem_ker.mp hzker]
    simp
  have halphazne : alpha z ≠ 1 := by
    intro h
    apply DoubleCoverUniqueness.kernelInvolution_ne_one f hcard
    have hzEq : z = 1 := by
      apply alpha.injective
      simpa using h
    simpa [z] using hzEq
  let alphaz : f.ker := ⟨alpha z, halphazker⟩
  have hEq := DoubleCoverUniqueness.eq_kernelInvolution_of_ne_one
    f hcard alphaz (by
      intro h
      apply halphazne
      exact congrArg Subtype.val h)
  exact congrArg Subtype.val hEq

/-- Over a quotient fixed point, a compatible automorphism of a double cover
fixes a chosen lift or multiplies it by the unique central involution. -/
public theorem doubleCoverLift_fixed_or_twisted
    {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hcard : Nat.card f.ker = 2)
    (alpha : MulAut G) (beta : MulAut Q)
    (hcompat : ∀ g : G, f (alpha g) = beta (f g))
    (y : G) (hy : beta (f y) = f y) :
    alpha y = y ∨
      alpha y =
        (DoubleCoverUniqueness.kernelInvolution f hcard : G) * y := by
  have hker : alpha y * y⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcompat, hy]
    simp
  rcases DoubleCoverUniqueness.eq_one_or_eq_kernelInvolution
      f hcard hker with hOne | hTwist
  · left
    calc
      alpha y = (alpha y * y⁻¹) * y := by group
      _ = y := by rw [hOne, one_mul]
  · right
    calc
      alpha y = (alpha y * y⁻¹) * y := by group
      _ =
          (DoubleCoverUniqueness.kernelInvolution f hcard : G) * y := by
        rw [hTwist]

/-- Every order-five quotient element has a unique order-five lift in a
central double cover with kernel of order two. -/
public theorem existsUnique_orderFive_lift
    {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hsurj : Function.Surjective f)
    (hkerCenter : f.ker ≤ Subgroup.center G)
    (hcard : Nat.card f.ker = 2) {q : Q} (hq : orderOf q = 5) :
    ∃! y : G, f y = q ∧ orderOf y = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let z : G := DoubleCoverUniqueness.kernelInvolution f hcard
  have hzker : z ∈ f.ker :=
    DoubleCoverUniqueness.kernelInvolution f hcard |>.property
  have hz2 : z ^ 2 = 1 :=
    DoubleCoverUniqueness.kernelInvolution_sq f hcard
  have hzcenter : z ∈ Subgroup.center G := hkerCenter hzker
  have hqne : q ≠ 1 := by
    intro h
    rw [h] at hq
    norm_num at hq
  obtain ⟨x, hx⟩ := hsurj q
  have hxker : x ^ 5 ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_pow, hx]
    rw [← hq]
    exact pow_orderOf_eq_one q
  have hxpow_cases : x ^ 5 = 1 ∨ x ^ 5 = z := by
    simpa [z] using
      (DoubleCoverUniqueness.eq_one_or_eq_kernelInvolution f hcard hxker)
  have hxeq : x ^ 5 = 1 → orderOf x = 5 := by
    intro hxp
    apply orderOf_eq_prime hxp
    intro hxone
    apply hqne
    rw [← hx, hxone]
    simp
  have hzeq : z ^ 5 = z := by
    rw [show 5 = 2 + 2 + 1 by norm_num, pow_add, pow_add, hz2]
    simp
  have hex : ∃ y : G, f y = q ∧ orderOf y = 5 := by
    rcases hxpow_cases with h | h
    · exact ⟨x, hx, hxeq h⟩
    · have hcomm : Commute z x :=
        (Subgroup.mem_center_iff.mp hzcenter x).symm
      have hzt : (z * x) ^ 5 = 1 := by
        rw [hcomm.mul_pow, hzeq, h]
        simpa [pow_two] using hz2
      have hztne : z * x ≠ 1 := by
        intro htx
        apply hqne
        calc
          q = f (z * x) := by
            rw [map_mul, MonoidHom.mem_ker.mp hzker, hx, one_mul]
          _ = f 1 := congrArg f htx
          _ = 1 := map_one f
      exact ⟨z * x, by
        rw [map_mul, MonoidHom.mem_ker.mp hzker, hx, one_mul],
        orderOf_eq_prime hzt hztne⟩
  refine ⟨hex.choose, hex.choose_spec, ?_⟩
  intro y hy
  rcases hy with ⟨hyq, hy5⟩
  have hker : y * hex.choose⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyq, hex.choose_spec.1]
    simp
  rcases DoubleCoverUniqueness.eq_one_or_eq_kernelInvolution f hcard hker with
    h1 | hz
  · exact mul_inv_eq_one.mp h1
  · have hcenter_y : Commute z hex.choose :=
      (Subgroup.mem_center_iff.mp hzcenter hex.choose).symm
    have hyEq : y = z * hex.choose := by
      calc
        y = (y * hex.choose⁻¹) * hex.choose := by group
        _ = z * hex.choose := by rw [hz]
    have hpow : y ^ 5 = 1 := by
      rw [← hy5]
      exact pow_orderOf_eq_one y
    have hcPow : hex.choose ^ 5 = 1 := by
      simpa [hex.choose_spec.2] using pow_orderOf_eq_one hex.choose
    rw [hyEq, hcenter_y.mul_pow, hzeq, hcPow] at hpow
    exact (DoubleCoverUniqueness.kernelInvolution_ne_one f hcard
      (by simpa [z] using hpow)).elim

/-- A compatible automorphism fixes the unique order-five lift of every
order-five fixed point in the quotient. -/
public theorem doubleCoverLift_fixes_orderFive_lift
    {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hsurj : Function.Surjective f)
    (hkerCenter : f.ker ≤ Subgroup.center G)
    (hcard : Nat.card f.ker = 2)
    (alpha : MulAut G) (beta : MulAut Q)
    (hcompat : ∀ g : G, f (alpha g) = beta (f g))
    {q : Q} (hq : orderOf q = 5) (hqfixed : beta q = q)
    {y : G} (hyq : f y = q) (hy5 : orderOf y = 5) :
    alpha y = y := by
  apply (existsUnique_orderFive_lift f hsurj hkerCenter hcard hq).unique
  · constructor
    · rw [hcompat, hyq, hqfixed]
    · exact (orderOf_injective alpha.toMonoidHom alpha.injective y).trans hy5
  · exact ⟨hyq, hy5⟩

/-- The fixed-versus-twisted alternative is independent of the chosen lift in
one fiber of a central double cover. -/
public theorem doubleCoverLift_fixed_iff_same_fiber
    {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hcard : Nat.card f.ker = 2)
    (hkerCenter : f.ker ≤ Subgroup.center G)
    (alpha : MulAut G) (beta : MulAut Q)
    (hcompat : ∀ g : G, f (alpha g) = beta (f g))
    {x y : G} (hxy : f x = f y) :
    alpha x = x ↔ alpha y = y := by
  let k := y * x⁻¹
  have hk : k ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy]
    simp
  have hak : alpha k = k := by
    rcases DoubleCoverUniqueness.eq_one_or_eq_kernelInvolution f hcard hk with
      hk1 | hkz
    · simp [hk1]
    · rw [hkz]
      exact doubleCoverLift_kernelInvolution_fixed f hcard alpha beta hcompat
  have hkx : Commute k x :=
    (Subgroup.mem_center_iff.mp (hkerCenter hk) x).symm
  have hy : y = k * x := by
    dsimp [k]
    group
  constructor
  · intro hax
    rw [hy, map_mul, hak, hax]
  · intro hay
    have hkInv : k⁻¹ ∈ f.ker := f.ker.inv_mem hk
    have hakInv : alpha k⁻¹ = k⁻¹ := by rw [map_inv, hak]
    have hx : x = k⁻¹ * y := by rw [hy]; group
    rw [hx, map_mul, hakInv, hay]

end GLS3.Chapter5.SchurPresentation
/- END Theory.DoubleCoverFixedFiber -/

/- BEGIN Theory.SchurAlternatingConjugationLift -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

/-- Conjugation by an element of the Schur symmetric cover preserves its Schur
alternating subgroup. -/
@[expose]
public def schurAlternatingConj (n : Nat) (w : SchurPresentedGroup n) :
    MulAut (SchurAlternatingGroup n) :=
  MulAut.conjNormal w

public theorem schurAlternatingConj_apply_coe
    (n : Nat) (w : SchurPresentedGroup n) (g : SchurAlternatingGroup n) :
    (schurAlternatingConj n w g : SchurPresentedGroup n) =
      w * g.1 * w⁻¹ := by
  exact MulAut.conjNormal_apply w g

public theorem schurAlternatingConj_fac
    (n : Nat) (w : SchurPresentedGroup n) (g : SchurAlternatingGroup n) :
    schurAlternatingProjection n (schurAlternatingConj n w g) =
      MulAut.conjNormal (H := alternatingGroup (Fin (n + 5)))
        (schurSymmetricProjection n w) (schurAlternatingProjection n g) := by
  apply Subtype.ext
  change schurSymmetricProjection n
      ((schurAlternatingConj n w g : SchurAlternatingGroup n).1) =
    schurSymmetricProjection n w *
      schurSymmetricProjection n g.1 *
        (schurSymmetricProjection n w)⁻¹
  rw [schurAlternatingConj_apply_coe, map_mul, map_mul, map_inv]

/-- The unique lifted quotient conjugation is the concrete conjugation action
of any chosen symmetric-cover lift. -/
public theorem doubleCoverLiftMulAut_conjNormal_eq_schurAlternatingConj
    (n : Nat) (w : SchurPresentedGroup n) :
    doubleCoverLiftMulAut n (schurAlternatingCovering n)
        (natCard_ker_schurAlternatingCovering n)
        (MulAut.conjNormal (H := alternatingGroup (Fin (n + 5)))
          (schurSymmetricProjection n w)) =
      schurAlternatingConj n w := by
  symm
  apply doubleCoverLiftMulAut_unique n (schurAlternatingCovering n)
    (natCard_ker_schurAlternatingCovering n)
    (MulAut.conjNormal (H := alternatingGroup (Fin (n + 5)))
      (schurSymmetricProjection n w))
  apply Theory.GroupTheory.Covering.ext
  intro g
  exact schurAlternatingConj_fac n w g

end GLS3.Chapter5.SchurPresentation
/- END Theory.SchurAlternatingConjugationLift -/

/- BEGIN Theory.DerivedKernelTrivialOfRootSquare -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

open RootFourSubgroup

/-- A central extension of an alternating group has trivial derived kernel if
that kernel has cardinality at most two and every derived lift of the standard
root involution has square one. -/
public theorem derivedKernel_eq_bot_of_root_lifts_sq_one
    (q : Nat) {E : Type} [Group E] [Finite E]
    (f : E →* alternatingGroup (Fin (q + 5)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center E)
    (hcard : Nat.card
      (f.comp (_root_.commutator E).subtype).ker ≤ 2)
    (hroot : ∀ u : _root_.commutator E,
      (f.comp (_root_.commutator E).subtype) u =
        (⟨rho1 q, rho1_mem_alternating q⟩ :
          alternatingGroup (Fin (q + 5))) →
      u ^ 2 = 1) :
    (f.comp (_root_.commutator E).subtype).ker = ⊥ := by
  let D := _root_.commutator E
  let fD := f.comp D.subtype
  let : Group.IsPerfect D :=
    commutator_isPerfect_of_surjective_of_ker_le_center f hf hker
  let : Finite D := inferInstance
  have hfD : Function.Surjective fD := by
    have hmap : D.map f = ⊤ := by
      dsimp [D]
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf]
      exact Group.IsPerfect.commutator_eq_top
    intro y
    have hy : y ∈ D.map f := by rw [hmap]; trivial
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, hxy⟩
  have hcenter : fD.ker ≤ Subgroup.center D := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hker hz) y
  by_contra hne
  have hcardNeOne : Nat.card fD.ker ≠ 1 := by
    intro hone
    apply hne
    exact Subgroup.card_eq_one.mp hone
  have : Nonempty fD.ker := ⟨1⟩
  have hcardPos : 0 < Nat.card fD.ker := Nat.card_pos
  have hcardTwo : Nat.card fD.ker = 2 := by
    have hle : Nat.card fD.ker ≤ 2 := by simpa [fD, D] using hcard
    omega
  obtain ⟨u, hu, huSq⟩ :=
    exists_lift_rho1_sq_ne_one_of_central_extension_ker_card_two
      q fD hfD hcenter hcardTwo
  exact huSq (hroot u hu)

end GLS3.Chapter5.SchurPresentation
/- END Theory.DerivedKernelTrivialOfRootSquare -/

/- BEGIN Theory.DoubleCoverPreimageTransport -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

/-- Full preimages of any subgroup of the alternating quotient are preserved
by the unique equivalence between an arbitrary double cover and the explicit
Schur double cover. -/
public theorem nonempty_doubleCoverPreimageMulEquiv
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (Lbar : Subgroup (alternatingGroup (Fin (n + 5)))) :
    Nonempty ((Lbar.comap f.toMonoidHom : Subgroup G) ≃*
      Lbar.comap (schurAlternatingProjection n)) := by
  obtain ⟨e, he, _⟩ := theorem_5_2_3_a_2 n f (schurAlternatingCovering n)
    hcard (natCard_ker_schurAlternatingCovering n)
  let L := Lbar.comap f.toMonoidHom
  have hmap : L.map e.toMonoidHom =
      Lbar.comap (schurAlternatingProjection n) := by
    ext w
    constructor
    · rintro ⟨g, hg, rfl⟩
      change schurAlternatingProjection n (e g) ∈ Lbar
      have hev := DFunLike.congr_fun he g
      have hev' : schurAlternatingProjection n (e g) = f g := hev
      rw [hev']
      exact hg
    · intro hw
      obtain ⟨g, rfl⟩ := e.surjective w
      refine ⟨g, ?_, rfl⟩
      change f g ∈ Lbar
      have hev := DFunLike.congr_fun he g
      have hev' : schurAlternatingProjection n (e g) = f g := hev
      rw [← hev']
      exact hw
  exact ⟨(e.subgroupMap L).trans (MulEquiv.subgroupCongr hmap)⟩

end GLS3.Chapter5.SchurPresentation
/- END Theory.DoubleCoverPreimageTransport -/

/- BEGIN Theory.InvolutionLiftCommutesEvenRotationLift -/
noncomputable section
namespace GLS3.Chapter5.SchurPresentation

open GLS3.Chapter5

/-- In a Schur double cover, every lift of an even involution rotation commutes
with every lift of the original involution. -/
public theorem involutionLift_commutes_evenRotationLift
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (xA : alternatingGroup (Fin (n + 5))) (hx : orderOf xA.1 = 2)
    (a : evenInvolutionCycleRotations xA.1)
    (u y : G) (hu : f u = xA)
    (hy : f y = evenInvolutionCycleRotationToAlternating xA.1 a) :
    Commute u y := by
  let rhoA := evenInvolutionCycleRotationToAlternating xA.1 a
  let compA : alternatingGroup (Fin (n + 5)) := xA * rhoA
  obtain ⟨c, hc⟩ := f.surjective compA
  change f c = compA at hc
  have hdisjoint : Equiv.Perm.Disjoint (f y).1 (f c).1 := by
    rw [hy, hc]
    exact involutionRotation_disjoint_complement xA.1 hx a.1
  have hcy : Commute c y := by
    exact (commutatorElement_eq_one_iff_commute.mp
      (proposition_5_2_4_f_general_alternating
        n f hcard y c hdisjoint)).symm
  have ha2 : a.1 ^ 2 = 1 := by
    simpa [hx] using cycleRotationGroup_pow_orderOf_eq_one_of_primeOrder
      xA.1 (by simpa [hx] using Nat.prime_two) a.1
  have hrho2 : rhoA ^ 2 = 1 := by
    apply Subtype.ext
    change (cycleRotationToCentralizer xA.1 a.1).1 ^ 2 = 1
    rw [cycleRotationToCentralizer_pow_coe, ha2, map_one]
    rfl
  have hrhomul : rhoA * rhoA = 1 := by simpa [pow_two] using hrho2
  have hprod : f u = f (c * y) := by
    rw [hu, map_mul, hc, hy]
    change xA = compA * rhoA
    simp [compA, hrhomul, mul_assoc]
  exact commute_of_image_eq_mul_of_central_kernel
    f.toMonoidHom f.ker_le_center u c y y hprod hcy (Commute.refl y)

end GLS3.Chapter5.SchurPresentation
/- END Theory.InvolutionLiftCommutesEvenRotationLift -/

/- BEGIN Theory.proposition_5_2_8_d_1 -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

/-- Proposition 5.2.8(d)(1): full preimages of quotient factors with disjoint
permutation supports commute in every Schur double cover. -/
public theorem proposition_5_2_8_d_1
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (H0bar H2bar : Subgroup (alternatingGroup (Fin (n + 5))))
    (hdisjoint : ∀ a ∈ H0bar, ∀ b ∈ H2bar,
      Equiv.Perm.Disjoint a.1 b.1) :
    ∀ a : H0bar.comap f.toMonoidHom,
      ∀ b : H2bar.comap f.toMonoidHom, Commute a.1 b.1 := by
  intro a b
  apply commutatorElement_eq_one_iff_commute.mp
  apply proposition_5_2_4_f_general_alternating n f hcard a.1 b.1
  exact hdisjoint (f a.1) a.2 (f b.1) b.2

end GLS3.Chapter5.SchurPresentation
/- END Theory.proposition_5_2_8_d_1 -/

/- BEGIN Theory.TraceZeroPermutationModuleMap -/
noncomputable section
namespace GLS3.Chapter5
/-- An injective homomorphism transports a trace-zero permutation-module
structure to the image subgroups. -/
public theorem isTraceZeroPermutationModule_map_of_injective
    {G K : Type*} [Group G] [Group K]
    (R L : Subgroup G) (r : Nat) (φ : G →* K)
    (hφ : Function.Injective φ)
    (hmod : IsTraceZeroPermutationModule R L r) :
    IsTraceZeroPermutationModule (R.map φ) (L.map φ) r := by
  rcases hmod with ⟨eR, eL, hact⟩
  let mR := Subgroup.equivMapOfInjective R φ hφ
  let mL := Subgroup.equivMapOfInjective L φ hφ
  refine ⟨mR.symm.trans eR, mL.symm.trans eL, ?_⟩
  intro l v
  let l0 : L := mL.symm l
  let v0 : R := mR.symm v
  obtain ⟨w0, hw0, hcoord⟩ := hact l0 v0
  let w : R.map φ := mR w0
  refine ⟨w, ?_, ?_⟩
  · change φ w0.1 = l.1 * v.1 * l.1⁻¹
    have hl : φ l0.1 = l.1 := by
      exact congrArg Subtype.val (mL.apply_symm_apply l)
    have hv : φ v0.1 = v.1 := by
      exact congrArg Subtype.val (mR.apply_symm_apply v)
    rw [← hl, ← hv, ← map_inv, ← map_mul, ← map_mul, hw0]
  · simpa [l0, v0, w, mR, mL] using hcoord
end GLS3.Chapter5
/- END Theory.TraceZeroPermutationModuleMap -/

/- BEGIN Theory.InvolutionCycleSwapCommuteRotation -/
noncomputable section
namespace GLS3.Chapter5
universe __ch5_InvolutionCycleSwapCommuteRotation_u

public theorem involutionCycleSwap_commute_twoCycleRotation
    {Ω : Type __ch5_InvolutionCycleSwapCommuteRotation_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2)
    (c d : x.cycleFactorsFinset) (hcd : c ≠ d) :
    let e := theorem_5_2_2_d_3_a x (by simpa [hx] using Nat.prime_two)
    let l := e.symm (Equiv.swap c d)
    let v : x.cycleFactorsFinset → Multiplicative (ZMod 2) :=
      fun k => if k = c ∨ k = d then Multiplicative.ofAdd 1 else 1
    let a := (involutionCycleRotationCoordinates x hx).symm v
    Commute l.1.1 (cycleRotationToCentralizer x a).1 := by
  dsimp only
  let hp : (orderOf x).Prime := by simpa [hx] using Nat.prime_two
  let e := theorem_5_2_2_d_3_a x hp
  let l := e.symm (Equiv.swap c d)
  let v : x.cycleFactorsFinset → Multiplicative (ZMod 2) :=
    fun k => if k = c ∨ k = d then Multiplicative.ofAdd 1 else 1
  let a := (involutionCycleRotationCoordinates x hx).symm v
  have hfixed : (cyclePermutationActionOnCycleRotations x) l a = a := by
    simpa [e, l, v, a] using
      (involutionTwoCycleRotation_fixed_by_swap x hx c d hcd)
  have hact := cyclePermutationActionOnCycleRotations_apply x l a
  have hconj : (cycleRotationToCentralizer x a).1 =
      l.1.1 * (cycleRotationToCentralizer x a).1 * l.1.1⁻¹ := by
    rw [hfixed] at hact
    exact hact
  rw [commute_iff_eq]
  calc
    l.1.1 * (cycleRotationToCentralizer x a).1 =
        (l.1.1 * (cycleRotationToCentralizer x a).1 * l.1.1⁻¹) * l.1.1 := by
          simp
    _ = (cycleRotationToCentralizer x a).1 * l.1.1 := by rw [← hconj]

end GLS3.Chapter5
/- END Theory.InvolutionCycleSwapCommuteRotation -/

/- BEGIN Theory.A6StandardNinePreimageNoncommutative -/
noncomputable section

namespace GLS3.Chapter5

/-- The preimage of the standard elementary abelian subgroup of order nine is
noncommutative in every triple cover of `A₆`. -/
public theorem a6StandardNine_preimage_noncommutative
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (f : Covering K (alternatingGroup (Fin 6)))
    (hker : Nat.card f.toMonoidHom.ker = 3) :
    ¬ IsMulCommutative
      (SchurPresentation.Theorem523BaseNine.a6StandardNine.comap
        f.toMonoidHom) := by
  let R : Subgroup K :=
    SchurPresentation.Theorem523BaseNine.a6StandardNine.comap f.toMonoidHom
  have hRcard : Nat.card R = 27 := by
    dsimp [R]
    rw [SchurPresentation.card_comap_mul f.toMonoidHom f.surjective
      SchurPresentation.Theorem523BaseNine.a6StandardNine,
      SchurPresentation.Theorem523BaseNine.a6_card, hker]
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRp : IsPGroup 3 R := by
    apply IsPGroup.iff_card.mpr
    exact ⟨3, by simpa using hRcard⟩
  obtain ⟨P, hRP⟩ := hRp.exists_le_sylow
  have hP := tripleCoverA6_sylow3 f hker P
  have hReq : R = (P : Subgroup K) := by
    apply Subgroup.eq_of_le_of_card_ge hRP
    rw [hRcard, hP.1]
  intro hcomm
  have hcenterTop : Subgroup.center R = ⊤ :=
    Subgroup.center_eq_top_iff.mpr hcomm
  have hcenterCard : Nat.card (Subgroup.center R) = 27 := by
    rw [hcenterTop, Subgroup.card_top, hRcard]
  have hcenterCardThree : Nat.card (Subgroup.center R) = 3 := by
    rw [hReq]
    exact hP.2
  omega

end GLS3.Chapter5
/- END Theory.A6StandardNinePreimageNoncommutative -/

/- BEGIN Theory.A7StandardNinePreimageNoncommutative -/
noncomputable section

namespace GLS3.Chapter5

/-- The preimage of the standard elementary abelian subgroup of order nine is
noncommutative in every triple cover of `A₇`. -/
public theorem a7StandardNine_preimage_noncommutative
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (f : Covering K (alternatingGroup (Fin 7)))
    (hker : Nat.card f.toMonoidHom.ker = 3) :
    ¬ IsMulCommutative
      (SchurPresentation.Theorem523BaseNine.a7StandardNine.comap
        f.toMonoidHom) := by
  let R : Subgroup K :=
    SchurPresentation.Theorem523BaseNine.a7StandardNine.comap f.toMonoidHom
  have hRcard : Nat.card R = 27 := by
    dsimp [R]
    rw [SchurPresentation.card_comap_mul f.toMonoidHom f.surjective
      SchurPresentation.Theorem523BaseNine.a7StandardNine,
      SchurPresentation.Theorem523BaseNine.a7_card, hker]
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRp : IsPGroup 3 R := by
    apply IsPGroup.iff_card.mpr
    exact ⟨3, by simpa using hRcard⟩
  obtain ⟨P, hRP⟩ := hRp.exists_le_sylow
  have hP := tripleCoverA7_sylow3 f hker P
  have hReq : R = (P : Subgroup K) := by
    apply Subgroup.eq_of_le_of_card_ge hRP
    rw [hRcard, hP.1]
  intro hcomm
  have hcenterTop : Subgroup.center R = ⊤ :=
    Subgroup.center_eq_top_iff.mpr hcomm
  have hcenterCard : Nat.card (Subgroup.center R) = 27 := by
    rw [hcenterTop, Subgroup.card_top, hRcard]
  have hcenterCardThree : Nat.card (Subgroup.center R) = 3 := by
    rw [hReq]
    exact hP.2
  omega

end GLS3.Chapter5
/- END Theory.A7StandardNinePreimageNoncommutative -/

/- BEGIN Theory.InvolutionFixedSubgroupIndexWitness -/
noncomputable section

namespace GLS3.Chapter5

/-- A single twisted lift over a quotient fixed point proves that the fixed
subgroup image has index two, and supplies the source's element `g` with
`g^x = gz`. -/
public theorem involutionFixedSubgroup_index_two_of_twisted_lift
    {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center G)
    (hkerCard : Nat.card f.ker = 2)
    (alpha : MulAut G) (beta : MulAut H)
    (hcompat : ∀ g : G, f (alpha g) = beta (f g))
    (y : G) (hyFixed : beta (f y) = f y)
    (hyTwist : alpha y =
      (SchurPresentation.DoubleCoverUniqueness.kernelInvolution f hkerCard : G) * y) :
    ∃ _hle :
        (automorphismFixedSubgroup alpha).map f ≤
          automorphismFixedSubgroup beta,
      (((automorphismFixedSubgroup alpha).map f).subgroupOf
          (automorphismFixedSubgroup beta)).index = 2 ∧
        ∃ g : G, alpha g =
          (SchurPresentation.DoubleCoverUniqueness.kernelInvolution f hkerCard : G) * g := by
  have hzNe : (SchurPresentation.DoubleCoverUniqueness.kernelInvolution f hkerCard : G) ≠ 1 := by
    intro hz
    apply SchurPresentation.DoubleCoverUniqueness.kernelInvolution_ne_one f hkerCard
    apply Subtype.ext
    exact hz
  have hyNotFixed : alpha y ≠ y := by
    rw [hyTwist]
    intro h
    have hzOne : (SchurPresentation.DoubleCoverUniqueness.kernelInvolution f hkerCard : G) = 1 := by
      apply mul_right_cancel (b := y)
      simpa using h
    exact hzNe hzOne
  have hneq :
      (automorphismFixedSubgroup alpha).map f ≠
        automorphismFixedSubgroup beta := by
    intro heq
    have hyMem : f y ∈ automorphismFixedSubgroup beta := hyFixed
    rw [← heq] at hyMem
    obtain ⟨c, hcFixed, hcy⟩ := hyMem
    have hiff := SchurPresentation.doubleCoverLift_fixed_iff_same_fiber
      f hkerCard hker alpha beta hcompat hcy
    have hc : alpha c = c := hcFixed
    exact hyNotFixed (hiff.mp hc)
  obtain ⟨hle, hindex⟩ :=
    automorphismFixedSubgroup_image_index_eq_two_of_failure
      f hf hker hkerCard alpha beta hcompat hneq
  exact ⟨hle, hindex, y, hyTwist⟩

end GLS3.Chapter5
/- END Theory.InvolutionFixedSubgroupIndexWitness -/

/- BEGIN Theory.proposition_5_2_4_b_general -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

/-- Proposition 5.2.4(b) for an arbitrary Schur double cover. -/
public theorem proposition_5_2_4_b_general
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n m : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (h5 : 5 ≤ m) (hmn : m ≤ n + 5) :
    Nonempty (↥((RootAm.rootAm n m hmn).comap f.toMonoidHom) ≃*
      SchurAlternatingGroup (m - 5)) := by
  obtain ⟨e⟩ := nonempty_doubleCoverPreimageMulEquiv n f hcard (RootAm.rootAm n m hmn)
  obtain ⟨d⟩ := RootAm.proposition_5_2_4_b n m h5 hmn
  exact ⟨e.trans d⟩

end GLS3.Chapter5.SchurPresentation
/- END Theory.proposition_5_2_4_b_general -/

/- BEGIN Theory.InvolutionAlternatingCentralizerCoreStructure -/
noncomputable section

namespace GLS3.Chapter5

/-- The quotient-centralizer core of Proposition 5.2.8(a), before identifying
the two groups enlarged by the extra involution with the full symmetric and
wreath products. -/
public theorem involutionAlternatingCentralizerCoreStructure
    (n : Nat) (σ : Equiv.Perm (Fin n)) (hσ : orderOf σ = 2) :
    let x : Equiv.Perm (Fin n) := σ
    let r := Fintype.card x.cycleFactorsFinset
    let s := Fintype.card (Function.fixedPoints x)
    ∃ (Rbar Lbar H1bar H2bar : Subgroup (alternatingGroup (Fin n)))
      (tbar : alternatingGroup (Fin n)),
      automorphismFixedSubgroup
          (MulAut.conjNormal (H := alternatingGroup (Fin n)) σ) =
          (H1bar ⊔ H2bar) ⊔ Subgroup.zpowers tbar ∧
        H1bar = Rbar ⊔ Lbar ∧
        (Rbar.subgroupOf H1bar).Normal ∧
        Disjoint H1bar H2bar ∧
        (∀ g : H1bar, ∀ h : H2bar, Commute g.1 h.1) ∧
        IsTraceZeroPermutationModule Rbar Lbar r ∧
        (∃ P : Subgroup (InvolutionWreath r),
          P.index = 2 ∧ Nonempty (H1bar ≃* P)) ∧
        Nonempty (Rbar ≃* Multiplicative ↥(traceZeroTwoSubgroup r)) ∧
        Nonempty (Lbar ≃* Equiv.Perm (Fin r)) ∧
        (∃ eH2 : H2bar ≃* alternatingGroup (Fin s),
          ∀ u : H2bar,
            (eH2 u).1.support.card = u.1.1.support.card) ∧
        tbar ^ 2 = 1 ∧
        Subgroup.zpowers tbar ≤ Subgroup.normalizer (H1bar : Set _) ∧
        Subgroup.zpowers tbar ≤ Subgroup.normalizer (H2bar : Set _) ∧
        (s ≤ 1 → tbar = 1) ∧
        (2 ≤ s →
          Nonempty (↥(H1bar ⊔ Subgroup.zpowers tbar) ≃*
            InvolutionWreath r) ∧
          Nonempty (↥(H2bar ⊔ Subgroup.zpowers tbar) ≃*
            Equiv.Perm (Fin s))) := by
  dsimp only
  let x : Equiv.Perm (Fin n) := σ
  let r := Fintype.card x.cycleFactorsFinset
  let s := Fintype.card (Function.fixedPoints x)
  let C := Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n)))
  let χ : C →* ℤˣ := Equiv.Perm.sign.comp C.subtype
  let Z := χ.ker
  let F := automorphismFixedSubgroup
    (MulAut.conjNormal (H := alternatingGroup (Fin n)) σ)
  let eZ : Z ≃* F :=
    alternatingCentralizerSignKernelEquivFixedConjNormal σ
  let φ : Z →* alternatingGroup (Fin n) := F.subtype.comp eZ.toMonoidHom
  let R : Subgroup C := cycleRotationSubgroup x
  let L : Subgroup C := cyclePermutationSubgroup x
  let I : Subgroup C := fixedPointPermutationSubgroup x
  let RZ : Subgroup Z := R.comap Z.subtype
  let LZ : Subgroup Z := L.comap Z.subtype
  let IZ : Subgroup Z := I.comap Z.subtype
  let H1Z : Subgroup Z := RZ ⊔ LZ
  let Rbar : Subgroup (alternatingGroup (Fin n)) := RZ.map φ
  let Lbar : Subgroup (alternatingGroup (Fin n)) := LZ.map φ
  let H1bar : Subgroup (alternatingGroup (Fin n)) := H1Z.map φ
  let H2bar : Subgroup (alternatingGroup (Fin n)) := IZ.map φ
  have haPerm : orderOf x = 2 := hσ
  have hxprime : (orderOf x).Prime := by simpa [haPerm] using Nat.prime_two
  have hφinj : Function.Injective φ :=
    F.subtype_injective.comp eZ.injective
  have hφrange : φ.range = F := by
    ext g
    constructor
    · rintro ⟨z, rfl⟩
      exact (eZ z).2
    · intro hg
      let gf : F := ⟨g, hg⟩
      refine ⟨eZ.symm gf, ?_⟩
      change (eZ (eZ.symm gf)).1 = g
      exact congrArg Subtype.val (eZ.apply_symm_apply gf)
  have hH1eq : H1bar = Rbar ⊔ Lbar := by
    dsimp [H1bar, H1Z, Rbar, Lbar]
    exact Subgroup.map_sup RZ LZ φ
  have hnormal : (Rbar.subgroupOf H1bar).Normal := by
    have hRZnormal : RZ.Normal :=
      (cycleRotationSubgroup_normal x).comap Z.subtype
    have hRZH : (RZ.subgroupOf H1Z).Normal := hRZnormal.subgroupOf H1Z
    let eH : H1Z ≃* H1bar :=
      Subgroup.equivMapOfInjective H1Z φ hφinj
    have hmapped := hRZH.map eH.toMonoidHom eH.surjective
    convert hmapped using 1
    ext r
    change (r.1 ∈ RZ.map φ) ↔
      ∃ z : H1Z, z ∈ RZ.subgroupOf H1Z ∧ eH z = r
    constructor
    · rintro ⟨q, hq, hqr⟩
      let qH : H1Z := ⟨q, (le_sup_left : RZ ≤ RZ ⊔ LZ) hq⟩
      exact ⟨qH, hq, Subtype.ext hqr⟩
    · rintro ⟨z, hz, hzr⟩
      exact ⟨z.1, hz, congrArg Subtype.val hzr⟩
  have hdisjoint : Disjoint H1bar H2bar := by
    have hH1le : H1Z ≤ (R ⊔ L).comap Z.subtype := by
      apply sup_le
      · intro z hz
        exact (le_sup_left : R ≤ R ⊔ L) hz
      · intro z hz
        exact (le_sup_right : L ≤ R ⊔ L) hz
    have hdisjZ : Disjoint H1Z IZ := by
      rw [Subgroup.disjoint_def]
      intro z hzH1 hzI
      have hzC : z.1 ∈ I ⊓ (R ⊔ L) := ⟨hzI, hH1le hzH1⟩
      have hbot : z.1 ∈ (⊥ : Subgroup C) := by
        rw [← (theorem_5_2_2_d_1 x hxprime).2.2.1]
        exact hzC
      simpa using hbot
    exact Subgroup.disjoint_map hφinj hdisjZ
  have hcommute : ∀ g : H1bar, ∀ h : H2bar, Commute g.1 h.1 := by
    have hH1le : H1Z ≤ (R ⊔ L).comap Z.subtype := by
      apply sup_le
      · intro z hz
        exact (le_sup_left : R ≤ R ⊔ L) hz
      · intro z hz
        exact (le_sup_right : L ≤ R ⊔ L) hz
    intro g h
    obtain ⟨z, hz, hzg⟩ := g.2
    obtain ⟨i, hi, hih⟩ := h.2
    have himem := (theorem_5_2_2_d_1 x hxprime).2.2.2.2 hi
    rw [Subgroup.mem_centralizer_iff] at himem
    have hC : Commute z.1 i.1 := himem z.1 (hH1le hz)
    have hZ : Commute z i := Subtype.ext hC.eq
    rw [← hzg, ← hih]
    exact hZ.map φ
  have hmodule : IsTraceZeroPermutationModule Rbar Lbar r := by
    have hkernel := involutionSignKernelIsTraceZeroPermutationModule x haPerm
    simpa [Rbar, Lbar, RZ, LZ, r] using
      isTraceZeroPermutationModule_map_of_injective RZ LZ r φ hφinj hkernel
  have hindexTwo : ∃ P : Subgroup (InvolutionWreath r),
      P.index = 2 ∧ Nonempty (H1bar ≃* P) := by
    obtain ⟨P, hPindex, ⟨eP⟩⟩ := involutionKernelWreathIndexTwo x haPerm
    let eMap : H1Z ≃* H1bar :=
      Subgroup.equivMapOfInjective H1Z φ hφinj
    exact ⟨P, by simpa [r] using hPindex,
      ⟨by simpa [H1bar, H1Z] using eMap.symm.trans eP⟩⟩
  have hRbarEquiv : Nonempty
      (Rbar ≃* Multiplicative ↥(traceZeroTwoSubgroup
        (Fintype.card x.cycleFactorsFinset))) := by
    let eMap : RZ ≃* Rbar := Subgroup.equivMapOfInjective RZ φ hφinj
    let eFin := Fintype.equivFin x.cycleFactorsFinset
    let eR := involutionRotationSignKernelEquivTraceZero x haPerm
      (Fintype.card x.cycleFactorsFinset) eFin
    exact ⟨by simpa [C, χ, Z, R, RZ, Rbar] using eMap.symm.trans eR⟩
  have hLbarEquiv : Nonempty
      (Lbar ≃* Equiv.Perm (Fin (Fintype.card x.cycleFactorsFinset))) := by
    let eMap : LZ ≃* Lbar := Subgroup.equivMapOfInjective LZ φ hφinj
    let eL := involutionCyclePermutationSignKernelEquiv x haPerm
    let eFin := (Fintype.equivFin x.cycleFactorsFinset).permCongrHom
    exact ⟨by
      simpa [C, χ, Z, L, LZ, Lbar] using eMap.symm.trans (eL.trans eFin)⟩
  have hH2barEquiv : ∃ eH2 : H2bar ≃* alternatingGroup
      (Fin (Fintype.card (Function.fixedPoints x))),
      ∀ u : H2bar, (eH2 u).1.support.card = u.1.1.support.card := by
    let eMap : IZ ≃* H2bar := Subgroup.equivMapOfInjective IZ φ hφinj
    let eI := fixedPointPermutationSignKernelEquiv x
    let eFin := (Fintype.equivFin (Function.fixedPoints x)).altCongrHom
    let eH2 : H2bar ≃* alternatingGroup
        (Fin (Fintype.card (Function.fixedPoints x))) := by
      simpa [C, χ, Z, I, IZ, H2bar] using eMap.symm.trans (eI.trans eFin)
    refine ⟨eH2, ?_⟩
    intro u
    change (eFin (eI (eMap.symm u))).1.support.card = u.1.1.support.card
    calc
      _ = (eI (eMap.symm u)).1.support.card := by
        simpa [eFin] using card_support_permCongr
          (Fintype.equivFin (Function.fixedPoints x))
          (eI (eMap.symm u)).1
      _ = (eMap.symm u).1.1.1.support.card :=
        fixedPointPermutationSignKernelEquiv_support_card x (eMap.symm u)
      _ = u.1.1.support.card := by
        have hu := congrArg Subtype.val (eMap.apply_symm_apply u)
        change φ (eMap.symm u).1 = u.1 at hu
        have hφcoe : (φ (eMap.symm u).1).1 =
            (eMap.symm u).1.1.1 := by
          exact alternatingCentralizerSignKernelEquivFixedConjNormal_coe
            σ (eMap.symm u).1
        rw [← hφcoe]
        exact congrArg
          (fun g : alternatingGroup (Fin n) => g.1.support.card) hu
  have htZdata : ∃ tZ : Z,
      ((RZ ⊔ LZ) ⊔ IZ) ⊔ Subgroup.zpowers tZ = ⊤ ∧
      tZ ^ 2 = 1 ∧
      Subgroup.zpowers tZ ≤ Subgroup.normalizer (H1Z : Set Z) ∧
      Subgroup.zpowers tZ ≤ Subgroup.normalizer (IZ : Set Z) ∧
      (s ≤ 1 → tZ = 1) ∧
      (2 ≤ s →
        Nonempty (↥((RZ ⊔ LZ) ⊔ Subgroup.zpowers tZ) ≃* ↥(R ⊔ L)) ∧
        Nonempty (↥(IZ ⊔ Subgroup.zpowers tZ) ≃*
          Equiv.Perm (Function.fixedPoints x))) := by
    by_cases hs2 : 2 ≤ s
    · obtain ⟨tZ, hdecompZ, ht2Z, htHnormZ, htInormZ, hHextZ, hIextZ⟩ :=
        involutionSignKernelFullExtensions x haPerm hs2
      change Subgroup.zpowers tZ ≤
        Subgroup.normalizer ((RZ ⊔ LZ : Subgroup Z) : Set Z) at htHnormZ
      exact ⟨tZ, hdecompZ, ht2Z, htHnormZ, htInormZ, fun hs1 => by omega,
        fun _ => ⟨hHextZ, hIextZ⟩⟩
    · obtain ⟨tZ, hdecompZ, ht2Z, hsmallZ⟩ :=
        involutionSignKernelDecomposition x haPerm
      have hsle : s ≤ 1 := by omega
      exact ⟨tZ, hdecompZ, ht2Z, by simp [hsmallZ hsle],
        by simp [hsmallZ hsle], hsmallZ,
        fun hs2' => (hs2 hs2').elim⟩
  obtain ⟨tZ, hdecompZ, ht2Z, htHnormZ, htInormZ, hsmallZ, hfullZ⟩ := htZdata
  let tbar : alternatingGroup (Fin n) := φ tZ
  have hdecomp : F = (H1bar ⊔ H2bar) ⊔ Subgroup.zpowers tbar := by
    rw [← hφrange, φ.range_eq_map, ← hdecompZ]
    simp only [Subgroup.map_sup, MonoidHom.map_zpowers]
    change (Rbar ⊔ Lbar ⊔ H2bar) ⊔ Subgroup.zpowers tbar =
      (H1bar ⊔ H2bar) ⊔ Subgroup.zpowers tbar
    rw [hH1eq]
  have ht2 : tbar ^ 2 = 1 := by
    dsimp [tbar]
    rw [← map_pow, ht2Z, map_one]
  have htHnorm : Subgroup.zpowers tbar ≤
      Subgroup.normalizer (H1bar : Set (alternatingGroup (Fin n))) := by
    simpa [H1bar, H1Z, tbar] using
      ((Subgroup.map_mono htHnormZ).trans (Subgroup.le_normalizer_map φ))
  have htInorm : Subgroup.zpowers tbar ≤
      Subgroup.normalizer (H2bar : Set (alternatingGroup (Fin n))) := by
    simpa [H2bar, tbar] using
      ((Subgroup.map_mono htInormZ).trans (Subgroup.le_normalizer_map φ))
  have hsmall : Fintype.card (Function.fixedPoints x) ≤ 1 → tbar = 1 := by
    intro hs
    dsimp [tbar]
    rw [hsmallZ hs, map_one]
  have hfull : 2 ≤ s →
      Nonempty (↥(H1bar ⊔ Subgroup.zpowers tbar) ≃* InvolutionWreath r) ∧
      Nonempty (↥(H2bar ⊔ Subgroup.zpowers tbar) ≃*
        Equiv.Perm (Fin s)) := by
    intro hs2
    obtain ⟨⟨eH⟩, ⟨eI⟩⟩ := hfullZ hs2
    let eHmap := subgroupSupZpowersMapEquivOfInjective H1Z tZ φ hφinj
    let eImap := subgroupSupZpowersMapEquivOfInjective IZ tZ φ hφinj
    let eW := involutionRotationPermutationWreathEquiv x haPerm
    let eFin := (Fintype.equivFin (Function.fixedPoints x)).permCongrHom
    refine ⟨⟨?eHfull⟩, ⟨?eIfull⟩⟩
    · exact (by
        simpa [H1bar, H1Z, tbar] using eHmap.symm.trans (eH.trans eW))
    · exact (by
        simpa [H2bar, tbar, s] using eImap.symm.trans (eI.trans eFin))
  exact ⟨Rbar, Lbar, H1bar, H2bar, tbar, hdecomp, hH1eq,
    hnormal, hdisjoint, hcommute, hmodule, hindexTwo,
    hRbarEquiv, hLbarEquiv,
    hH2barEquiv, ht2, htHnorm, htInorm, hsmall, hfull⟩

end GLS3.Chapter5
/- END Theory.InvolutionAlternatingCentralizerCoreStructure -/

/- BEGIN Theory.InvolutionCycleSwapRotationProductSupport -/
noncomputable section
namespace GLS3.Chapter5
universe __ch5_InvolutionCycleSwapRotationProductSupport_u

public theorem involutionCycleSwapRotationProduct_support_card
    {Ω : Type __ch5_InvolutionCycleSwapRotationProductSupport_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2)
    (c d : x.cycleFactorsFinset) (hcd : c ≠ d) :
    let e := theorem_5_2_2_d_3_a x (by simpa [hx] using Nat.prime_two)
    let l := e.symm (Equiv.swap c d)
    let v : x.cycleFactorsFinset → Multiplicative (ZMod 2) :=
      fun k => if k = c ∨ k = d then Multiplicative.ofAdd 1 else 1
    let a := (involutionCycleRotationCoordinates x hx).symm v
    (l.1.1 * (cycleRotationToCentralizer x a).1).support.card = 4 := by
  dsimp only
  let hp : (orderOf x).Prime := by simpa [hx] using Nat.prime_two
  let e := theorem_5_2_2_d_3_a x hp
  let l := e.symm (Equiv.swap c d)
  let v : x.cycleFactorsFinset → Multiplicative (ZMod 2) :=
    fun k => if k = c ∨ k = d then Multiplicative.ofAdd 1 else 1
  let a := (involutionCycleRotationCoordinates x hx).symm v
  let ρ := cycleRotationToCentralizer x a
  let p := l.1.1 * ρ.1
  have hl2 : l ^ 2 = 1 := by
    apply e.injective
    simp [l, pow_two]
  have hlPerm2 : l.1.1 ^ 2 = 1 :=
    congrArg (fun z : cyclePermutationSubgroup x => z.1.1) hl2
  have ha2 : a ^ 2 = 1 := by
    simpa [hx] using cycleRotationGroup_pow_orderOf_eq_one_of_primeOrder x hp a
  have hρ2 : ρ.1 ^ 2 = 1 := by
    change (cycleRotationToCentralizer x a).1 ^ 2 = 1
    rw [cycleRotationToCentralizer_pow_coe x a 2, ha2, map_one]
    rfl
  have hcomm : Commute l.1.1 ρ.1 := by
    simpa [e, l, v, a, ρ] using
      (involutionCycleSwap_commute_twoCycleRotation x hx c d hcd)
  have hp2 : p ^ 2 = 1 := by
    dsimp [p]
    calc
      (l.1.1 * ρ.1) ^ 2 = l.1.1 * (ρ.1 * l.1.1) * ρ.1 := by
        simp [pow_two, mul_assoc]
      _ = l.1.1 * (l.1.1 * ρ.1) * ρ.1 := by rw [← hcomm.eq]
      _ = (l.1.1 ^ 2) * (ρ.1 ^ 2) := by simp [pow_two, mul_assoc]
      _ = 1 := by rw [hlPerm2, hρ2, one_mul]
  have hρinv : ρ.1⁻¹ = ρ.1 := by
    exact (eq_inv_of_mul_eq_one_left (by simpa [pow_two] using hρ2)).symm
  have hpNe : p ≠ 1 := by
    intro hpOne
    have hlρ : l.1 = ρ := by
      apply Subtype.ext
      have h := eq_inv_of_mul_eq_one_left hpOne
      simpa [p, hρinv] using h
    have hlR : l.1 ∈ cycleRotationSubgroup x := by
      rw [hlρ]
      exact ⟨a, rfl⟩
    have hlBot : l.1 ∈ (⊥ : Subgroup (Subgroup.centralizer ({x} : Set (Equiv.Perm Ω)))) := by
      rw [← cycleRotationSubgroup_inf_cyclePermutationSubgroup_eq_bot x]
      exact ⟨hlR, l.2⟩
    have hlOne : l.1 = 1 := Subgroup.mem_bot.mp hlBot
    have hcard := involutionCycleSwap_support_card x hx c d hcd
    change l.1.1.support.card = 4 at hcard
    rw [hlOne] at hcard
    simp at hcard
  have hpSign : Equiv.Perm.sign p = 1 := by
    dsimp [p]
    rw [map_mul, involutionCyclePermutation_sign x hx l]
    have hρSign : Equiv.Perm.sign ρ.1 = 1 := by
      simpa [e, l, v, a, ρ] using involutionTwoCycleRotation_sign x hx c d hcd
    rw [hρSign, one_mul]
  let pA : alternatingGroup Ω := ⟨p, Equiv.Perm.mem_alternatingGroup.mpr hpSign⟩
  have hpLe : pA.1.support.card ≤ 4 := by
    have hlSupport : l.1.1.support = c.1.support ∪ d.1.support := by
      simpa [e, l] using involutionCycleSwap_support_eq_union x hx c d hcd
    have hρSupport : ρ.1.support ⊆ c.1.support ∪ d.1.support := by
      simpa [v, a, ρ] using involutionTwoCycleRotation_support_le_union x hx c d
    have hsupport : p.support ⊆ c.1.support ∪ d.1.support := by
      exact (Equiv.Perm.support_mul_le l.1.1 ρ.1).trans (by
        rw [hlSupport]
        exact sup_le le_rfl hρSupport)
    calc
      pA.1.support.card = p.support.card := rfl
      _ ≤ (c.1.support ∪ d.1.support).card := Finset.card_le_card hsupport
      _ = c.1.support.card + d.1.support.card := by
        apply Finset.card_union_of_disjoint
        exact Equiv.Perm.disjoint_iff_disjoint_support.mp
          (Equiv.Perm.cycleFactorsFinset_pairwise_disjoint x c.2 d.2 (by
            intro h
            exact hcd (Subtype.ext h)))
      _ = 4 := by
        rw [cycleFactor_support_card_eq_orderOf_of_primeOrder x hp c,
          cycleFactor_support_card_eq_orderOf_of_primeOrder x hp d, hx]
  have hpA2 : pA.1 ^ 2 = 1 := hp2
  have hpANe : pA ≠ 1 := by
    intro h
    apply hpNe
    exact congrArg Subtype.val h
  exact evenInvolution_support_card_eq_four_of_le pA hpA2 hpANe hpLe

end GLS3.Chapter5
/- END Theory.InvolutionCycleSwapRotationProductSupport -/

