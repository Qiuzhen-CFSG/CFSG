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

public import Theory.Alternating.Theorem523Reduction
set_option linter.style.nameCheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

/- Chapter 5-specific declarations, kept out of the general Theory library. -/

/- BEGIN Theory.Theorem523Suzuki -/
noncomputable section
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
universe __ch5_Theorem523Suzuki_w

namespace GLS3.Chapter5.SchurPresentation

open scoped commutatorElement

/-- The finite relator family in Suzuki's presentation (2.15) of
`A_{n+5}`, written on the repository's zero-based Suzuki generators. -/
public inductive SuzukiRelator (n : Nat) where
  | rootCube
  | tailSquare (i : Fin (n + 3)) (hi : i ≠ 0)
  | rootAdjacentCube
  | tailAdjacentCube (i : Fin (n + 2)) (hi : i ≠ 0)
  | rootFarSquare (j : Fin (n + 3)) (hj : 1 < j.val)
  | tailFarCommutator (i j : Fin (n + 3))
      (hi : i ≠ 0) (hj : j ≠ 0)
      (hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val)

public abbrev suzukiFreeGenerator (n : Nat) (i : Fin (n + 3)) :
    AlternatingSuzukiFreeGroup n :=
  FreeGroup.of i

/-- The word represented by one of Suzuki's defining relators. -/
@[expose]
public def SuzukiRelator.word {n : Nat} : SuzukiRelator n → AlternatingSuzukiFreeGroup n
  | .rootCube => suzukiFreeGenerator n 0 ^ 3
  | .tailSquare i _ => suzukiFreeGenerator n i ^ 2
  | .rootAdjacentCube =>
      (suzukiFreeGenerator n 0 * suzukiFreeGenerator n (Fin.succ 0)) ^ 3
  | .tailAdjacentCube i _ =>
      (suzukiFreeGenerator n i.castSucc * suzukiFreeGenerator n i.succ) ^ 3
  | .rootFarSquare j _ =>
      (suzukiFreeGenerator n 0 * suzukiFreeGenerator n j) ^ 2
  | .tailFarCommutator i j _ _ _ =>
      ⁅suzukiFreeGenerator n i, suzukiFreeGenerator n j⁆

public theorem suzukiAdjacentSwap_far_commute (n : Nat) {i j : Fin (n + 4)}
    (hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    Commute (adjacentSwap n i) (adjacentSwap n j) := by
  have hca : j.castSucc ≠ i.castSucc := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_castSucc] at hval
    omega
  have hcb : j.castSucc ≠ i.succ := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at hval
    omega
  have hda : j.succ ≠ i.castSucc := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_castSucc] at hval
    omega
  have hdb : j.succ ≠ i.succ := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_succ] at hval
    omega
  change adjacentSwap n i * adjacentSwap n j =
    adjacentSwap n j * adjacentSwap n i
  rw [adjacentSwap, adjacentSwap, Equiv.mul_swap_eq_swap_mul]
  rw [Equiv.swap_apply_of_ne_of_ne hca hcb,
    Equiv.swap_apply_of_ne_of_ne hda hdb]

public theorem alternatingSuzukiGenerator_root_far_mul_sq
    (n : Nat) (j : Fin (n + 3)) (hj : 1 < j.val) :
    (alternatingSuzukiGenerator n 0 * alternatingSuzukiGenerator n j) ^ 2 = 1 := by
  apply Subtype.ext
  change (((alternatingSuzukiGenerator n 0 : Equiv.Perm (Fin (n + 5))) *
      (alternatingSuzukiGenerator n j : Equiv.Perm (Fin (n + 5)))) ^ 2) = 1
  rw [show (alternatingSuzukiGenerator n 0 : Equiv.Perm (Fin (n + 5))) =
      adjacentSwap n 0 * adjacentSwap n 1 by
    simpa using alternatingSuzukiGenerator_val n 0]
  rw [alternatingSuzukiGenerator_val]
  let a : Equiv.Perm (Fin (n + 5)) := adjacentSwap n 0
  let b : Equiv.Perm (Fin (n + 5)) := adjacentSwap n 1
  let c : Equiv.Perm (Fin (n + 5)) := adjacentSwap n j.succ
  have hac : Commute a c := by
    apply suzukiAdjacentSwap_far_commute n
    left
    change 1 < j.val + 1
    omega
  have hbc : Commute b c := by
    apply suzukiAdjacentSwap_far_commute n
    left
    change 2 < j.val + 1
    omega
  have ha2 : a ^ 2 = 1 := adjacentSwap_sq n 0
  have hb2 : b ^ 2 = 1 := adjacentSwap_sq n 1
  have hc2 : c ^ 2 = 1 := adjacentSwap_sq n j.succ
  let d := a * b * a
  have hd2 : d ^ 2 = 1 := by
    dsimp [d]
    calc
      (a * b * a) ^ 2 = a * b * (a ^ 2) * b * a := by simp [pow_two, mul_assoc]
      _ = a * (b ^ 2) * a := by rw [ha2]; simp [pow_two, mul_assoc]
      _ = a ^ 2 := by rw [hb2]; simp [pow_two]
      _ = 1 := ha2
  have hdc : Commute d c := by
    exact Commute.mul_left (Commute.mul_left hac hbc) hac
  change (((a * b) * (a * c)) ^ 2) = 1
  calc
    ((a * b) * (a * c)) ^ 2 = (d * c) ^ 2 := by
      simp [d, mul_assoc]
    _ = d ^ 2 * c ^ 2 := hdc.mul_pow 2
    _ = 1 := by rw [hd2, hc2]; simp

/-- Every relator in Suzuki's finite presentation evaluates trivially in
the alternating group. -/
public theorem SuzukiRelator.lift_alternatingSuzukiGenerator_eq_one
    {n : Nat} (r : SuzukiRelator n) :
    FreeGroup.lift (alternatingSuzukiGenerator n) r.word = 1 := by
  cases r with
  | rootCube =>
      simpa [SuzukiRelator.word, suzukiFreeGenerator] using
        alternatingSuzukiGenerator_zero_pow_three n
  | tailSquare i hi =>
      simpa [SuzukiRelator.word, suzukiFreeGenerator] using
        alternatingSuzukiGenerator_tail_sq n i hi
  | rootAdjacentCube =>
      simpa [SuzukiRelator.word, suzukiFreeGenerator] using
        alternatingSuzukiGenerator_zero_succ_mul_pow_three n
  | tailAdjacentCube i hi =>
      simpa [SuzukiRelator.word, suzukiFreeGenerator] using
        alternatingSuzukiGenerator_tail_mul_pow_three n i hi
  | rootFarSquare j hj =>
      simpa [SuzukiRelator.word, suzukiFreeGenerator] using
        alternatingSuzukiGenerator_root_far_mul_sq n j hj
  | tailFarCommutator i j hi hj hfar =>
      have hprod := alternatingSuzukiGenerator_tail_far_mul_sq n hi hj hfar
      have hi2 := alternatingSuzukiGenerator_tail_sq n i hi
      have hj2 := alternatingSuzukiGenerator_tail_sq n j hj
      have hiInv : (alternatingSuzukiGenerator n i)⁻¹ =
          alternatingSuzukiGenerator n i := by
        exact (eq_inv_of_mul_eq_one_left (by simpa [pow_two] using hi2)).symm
      have hjInv : (alternatingSuzukiGenerator n j)⁻¹ =
          alternatingSuzukiGenerator n j := by
        exact (eq_inv_of_mul_eq_one_left (by simpa [pow_two] using hj2)).symm
      rw [SuzukiRelator.word, map_commutatorElement]
      simp only [suzukiFreeGenerator, FreeGroup.lift_apply_of]
      apply commutatorElement_eq_one_iff_commute.mpr
      show alternatingSuzukiGenerator n i * alternatingSuzukiGenerator n j =
        alternatingSuzukiGenerator n j * alternatingSuzukiGenerator n i
      have hprodInv :
          (alternatingSuzukiGenerator n i * alternatingSuzukiGenerator n j)⁻¹ =
            alternatingSuzukiGenerator n i * alternatingSuzukiGenerator n j := by
        exact (eq_inv_of_mul_eq_one_left (by simpa [pow_two] using hprod)).symm
      calc
        alternatingSuzukiGenerator n i * alternatingSuzukiGenerator n j =
            (alternatingSuzukiGenerator n i * alternatingSuzukiGenerator n j)⁻¹ :=
          hprodInv.symm
        _ = (alternatingSuzukiGenerator n j)⁻¹ *
            (alternatingSuzukiGenerator n i)⁻¹ := mul_inv_rev _ _
        _ = alternatingSuzukiGenerator n j * alternatingSuzukiGenerator n i := by
          rw [hiInv, hjInv]

/-- The finite relation set associated with Suzuki's presentation (2.15). -/
@[expose]
public def suzukiRelatorSet (n : Nat) : Set (AlternatingSuzukiFreeGroup n) :=
  Set.range SuzukiRelator.word

/-- The abstract group defined by Suzuki's finite relator family. -/
public abbrev SuzukiPresentedGroup (n : Nat) := PresentedGroup (suzukiRelatorSet n)

public theorem suzukiRelator_normalClosure_le_kernel (n : Nat) :
    Subgroup.normalClosure (suzukiRelatorSet n) ≤ alternatingSuzukiKernel n := by
  apply Subgroup.normalClosure_le_normal
  intro x hx
  obtain ⟨r, rfl⟩ := hx
  exact MonoidHom.mem_ker.mpr
    (SuzukiRelator.lift_alternatingSuzukiGenerator_eq_one r)

/-- The canonical epimorphism from the finite Suzuki presentation to the
alternating group.  Its injectivity is exactly the missing reverse
normal-closure inclusion. -/
public def suzukiPresentedProjection (n : Nat) :
    SuzukiPresentedGroup n →* alternatingGroup (Fin (n + 5)) :=
  PresentedGroup.toGroup (fun r hr => by
    obtain ⟨s, rfl⟩ := hr
    exact SuzukiRelator.lift_alternatingSuzukiGenerator_eq_one s)

@[simp]
public theorem suzukiPresentedProjection_of (n : Nat) (i : Fin (n + 3)) :
    suzukiPresentedProjection n (PresentedGroup.of i) =
      alternatingSuzukiGenerator n i := by
  rfl

public theorem suzukiPresentedProjection_surjective (n : Nat) :
    Function.Surjective (suzukiPresentedProjection n) := by
  rw [← MonoidHom.range_eq_top]
  apply top_unique
  rw [← alternatingSuzukiGenerator_closure_eq_top n]
  rw [Subgroup.closure_le]
  rintro x ⟨i, rfl⟩
  exact ⟨PresentedGroup.of i, by simp⟩

public theorem alternatingSuzukiKernel_eq_normalClosure_of_projection_injective
    (n : Nat) (hinj : Function.Injective (suzukiPresentedProjection n)) :
    alternatingSuzukiKernel n = Subgroup.normalClosure (suzukiRelatorSet n) := by
  apply le_antisymm
  · intro x hx
    rw [← PresentedGroup.mk_eq_one_iff]
    apply hinj
    change suzukiPresentedProjection n
        (PresentedGroup.mk (suzukiRelatorSet n) x) =
      suzukiPresentedProjection n 1
    change alternatingSuzukiMap n x = 1
    exact MonoidHom.mem_ker.mp hx
  · exact suzukiRelator_normalClosure_le_kernel n

public theorem reverse_mul_pow_eq_one {G : Type*} [Group G]
    (a b : G) (m : Nat) (h : (a * b) ^ m = 1) :
    (a⁻¹ * b⁻¹) ^ m = 1 := by
  have hrev : (b * a) ^ m = 1 := by
    calc
      (b * a) ^ m = (a⁻¹ * (a * b) * a) ^ m := by
        congr 1
        simp
      _ = a⁻¹ * (a * b) ^ m * a := by
        simpa using (conj_pow (a := a⁻¹) (b := a * b) (i := m))
      _ = 1 := by rw [h]; simp
  calc
    (a⁻¹ * b⁻¹) ^ m = ((b * a)⁻¹) ^ m := by rw [mul_inv_rev]
    _ = ((b * a) ^ m)⁻¹ := by rw [inv_pow]
    _ = 1 := by rw [hrev]; simp

public theorem suzukiPresented_relator_eq_one {n : Nat} (r : SuzukiRelator n) :
    FreeGroup.lift (fun i => (PresentedGroup.of i : SuzukiPresentedGroup n)) r.word = 1 := by
  rw [show FreeGroup.lift
      (fun i => (PresentedGroup.of i : SuzukiPresentedGroup n)) =
      PresentedGroup.mk (suzukiRelatorSet n) by
    apply FreeGroup.ext_hom
    intro i
    rfl]
  exact PresentedGroup.one_of_mem ⟨r, rfl⟩

public theorem suzukiInvertGenerator_relator_eq_one
    {n : Nat} (r : SuzukiRelator n) :
    FreeGroup.lift
      (fun i => (PresentedGroup.of i : SuzukiPresentedGroup n)⁻¹) r.word = 1 := by
  cases r with
  | rootCube =>
      have h := suzukiPresented_relator_eq_one
        (SuzukiRelator.rootCube : SuzukiRelator n)
      simpa [SuzukiRelator.word, suzukiFreeGenerator, inv_pow] using congrArg Inv.inv h
  | tailSquare i hi =>
      have h := suzukiPresented_relator_eq_one
        (SuzukiRelator.tailSquare i hi)
      simpa [SuzukiRelator.word, suzukiFreeGenerator, inv_pow] using congrArg Inv.inv h
  | rootAdjacentCube =>
      have h := suzukiPresented_relator_eq_one
        (SuzukiRelator.rootAdjacentCube : SuzukiRelator n)
      simpa [SuzukiRelator.word, suzukiFreeGenerator] using
        reverse_mul_pow_eq_one
          (PresentedGroup.of (0 : Fin (n + 3)) : SuzukiPresentedGroup n)
          (PresentedGroup.of ((0 : Fin (n + 2)).succ) : SuzukiPresentedGroup n)
          3 (by simpa [SuzukiRelator.word, suzukiFreeGenerator] using h)
  | tailAdjacentCube i hi =>
      have h := suzukiPresented_relator_eq_one
        (SuzukiRelator.tailAdjacentCube i hi)
      simpa [SuzukiRelator.word, suzukiFreeGenerator] using
        reverse_mul_pow_eq_one
          (PresentedGroup.of i.castSucc : SuzukiPresentedGroup n)
          (PresentedGroup.of i.succ : SuzukiPresentedGroup n)
          3 (by simpa [SuzukiRelator.word, suzukiFreeGenerator] using h)
  | rootFarSquare j hj =>
      have h := suzukiPresented_relator_eq_one
        (SuzukiRelator.rootFarSquare j hj)
      simpa [SuzukiRelator.word, suzukiFreeGenerator] using
        reverse_mul_pow_eq_one
          (PresentedGroup.of (0 : Fin (n + 3)) : SuzukiPresentedGroup n)
          (PresentedGroup.of j : SuzukiPresentedGroup n)
          2 (by simpa [SuzukiRelator.word, suzukiFreeGenerator] using h)
  | tailFarCommutator i j hi hj hfar =>
      have h := suzukiPresented_relator_eq_one
        (SuzukiRelator.tailFarCommutator i j hi hj hfar)
      have hc : Commute
          (PresentedGroup.of i : SuzukiPresentedGroup n)
          (PresentedGroup.of j : SuzukiPresentedGroup n) :=
        commutatorElement_eq_one_iff_commute.mp
          (by simpa [SuzukiRelator.word, suzukiFreeGenerator] using h)
      simpa [SuzukiRelator.word, suzukiFreeGenerator] using
        hc.inv_left.inv_right.commutator_eq

public def suzukiInvertGeneratorHom (n : Nat) :
    SuzukiPresentedGroup n →* SuzukiPresentedGroup n :=
  PresentedGroup.toGroup (fun r hr => by
    obtain ⟨s, rfl⟩ := hr
    exact suzukiInvertGenerator_relator_eq_one s)

@[simp]
public theorem suzukiInvertGeneratorHom_of (n : Nat) (i : Fin (n + 3)) :
    suzukiInvertGeneratorHom n (PresentedGroup.of i) =
      (PresentedGroup.of i : SuzukiPresentedGroup n)⁻¹ := by
  rfl

public theorem suzukiInvertGeneratorHom_involutive (n : Nat) (x : SuzukiPresentedGroup n) :
    suzukiInvertGeneratorHom n (suzukiInvertGeneratorHom n x) = x := by
  have hcomp : (suzukiInvertGeneratorHom n).comp (suzukiInvertGeneratorHom n) =
      MonoidHom.id (SuzukiPresentedGroup n) := by
    apply PresentedGroup.ext
    intro i
    simp
  exact DFunLike.congr_fun hcomp x

public def suzukiInvertGeneratorAut (n : Nat) : MulAut (SuzukiPresentedGroup n) where
  toFun := suzukiInvertGeneratorHom n
  invFun := suzukiInvertGeneratorHom n
  left_inv := suzukiInvertGeneratorHom_involutive n
  right_inv := suzukiInvertGeneratorHom_involutive n
  map_mul' := map_mul (suzukiInvertGeneratorHom n)

@[simp]
public theorem suzukiInvertGeneratorAut_of (n : Nat) (i : Fin (n + 3)) :
    suzukiInvertGeneratorAut n (PresentedGroup.of i) =
      (PresentedGroup.of i : SuzukiPresentedGroup n)⁻¹ := by
  rfl

public theorem suzukiInvertGeneratorAut_sq (n : Nat) :
    suzukiInvertGeneratorAut n ^ 2 = 1 := by
  ext x
  exact suzukiInvertGeneratorHom_involutive n x

public abbrev SuzukiPresentationC2 := Multiplicative (ZMod 2)

public def suzukiPresentationC2Generator : SuzukiPresentationC2 :=
  Multiplicative.ofAdd 1

public theorem one_ne_suzukiPresentationC2Generator :
    (1 : SuzukiPresentationC2) ≠ suzukiPresentationC2Generator := by
  all_goals decide
public theorem suzukiPresentationC2Generator_sq :
    suzukiPresentationC2Generator * suzukiPresentationC2Generator = 1 := by
  all_goals decide
public theorem suzukiPresentationC2_eq_one_or_generator
    (x : SuzukiPresentationC2) :
    x = 1 ∨ x = suzukiPresentationC2Generator := by
  fin_cases x <;> decide

public noncomputable def suzukiPresentationC2Action (n : Nat) :
    SuzukiPresentationC2 →* MulAut (SuzukiPresentedGroup n) where
  toFun x := if x = suzukiPresentationC2Generator then
      suzukiInvertGeneratorAut n else 1
  map_one' := by
    simp [one_ne_suzukiPresentationC2Generator]
  map_mul' := by
    intro x y
    rcases suzukiPresentationC2_eq_one_or_generator x with rfl | rfl <;>
      rcases suzukiPresentationC2_eq_one_or_generator y with rfl | rfl
    all_goals simp [one_ne_suzukiPresentationC2Generator,
      suzukiPresentationC2Generator_sq]
    simpa [pow_two] using (suzukiInvertGeneratorAut_sq n).symm

@[simp]
public theorem suzukiPresentationC2Action_generator (n : Nat) :
    suzukiPresentationC2Action n suzukiPresentationC2Generator =
      suzukiInvertGeneratorAut n := by
  simp [suzukiPresentationC2Action]

public abbrev SuzukiPresentationSemidirect (n : Nat) :=
  SuzukiPresentedGroup n ⋊[suzukiPresentationC2Action n] SuzukiPresentationC2

public noncomputable def suzukiCoxeterSimple (n : Nat) :
    Fin (n + 4) → SuzukiPresentationSemidirect n :=
  Fin.cases (SemidirectProduct.inr suzukiPresentationC2Generator)
    (fun i => SemidirectProduct.inr suzukiPresentationC2Generator *
      SemidirectProduct.inl (PresentedGroup.of i))

@[simp]
public theorem suzukiCoxeterSimple_zero (n : Nat) :
    suzukiCoxeterSimple n 0 =
      (SemidirectProduct.inr suzukiPresentationC2Generator :
        SuzukiPresentationSemidirect n) := by
  rfl

@[simp]
public theorem suzukiCoxeterSimple_succ (n : Nat) (i : Fin (n + 3)) :
    suzukiCoxeterSimple n i.succ =
      SemidirectProduct.inr suzukiPresentationC2Generator *
        SemidirectProduct.inl (PresentedGroup.of i) := by
  rfl

public theorem suzukiPresented_root_cube (n : Nat) :
    (PresentedGroup.of (0 : Fin (n + 3)) : SuzukiPresentedGroup n) ^ 3 = 1 := by
  simpa [SuzukiRelator.word, suzukiFreeGenerator] using
    suzukiPresented_relator_eq_one (SuzukiRelator.rootCube : SuzukiRelator n)

public theorem suzukiPresented_tail_sq (n : Nat) (i : Fin (n + 3)) (hi : i ≠ 0) :
    (PresentedGroup.of i : SuzukiPresentedGroup n) ^ 2 = 1 := by
  simpa [SuzukiRelator.word, suzukiFreeGenerator] using
    suzukiPresented_relator_eq_one (SuzukiRelator.tailSquare i hi)

public theorem suzukiPresented_root_adjacent_cube (n : Nat) :
    ((PresentedGroup.of (0 : Fin (n + 3)) : SuzukiPresentedGroup n) *
      PresentedGroup.of ((0 : Fin (n + 2)).succ)) ^ 3 = 1 := by
  simpa [SuzukiRelator.word, suzukiFreeGenerator] using
    suzukiPresented_relator_eq_one
      (SuzukiRelator.rootAdjacentCube : SuzukiRelator n)

public theorem suzukiPresented_tail_adjacent_cube (n : Nat)
    (i : Fin (n + 2)) (hi : i ≠ 0) :
    ((PresentedGroup.of i.castSucc : SuzukiPresentedGroup n) *
      PresentedGroup.of i.succ) ^ 3 = 1 := by
  simpa [SuzukiRelator.word, suzukiFreeGenerator] using
    suzukiPresented_relator_eq_one (SuzukiRelator.tailAdjacentCube i hi)

public theorem suzukiPresented_root_far_sq (n : Nat)
    (j : Fin (n + 3)) (hj : 1 < j.val) :
    ((PresentedGroup.of (0 : Fin (n + 3)) : SuzukiPresentedGroup n) *
      PresentedGroup.of j) ^ 2 = 1 := by
  simpa [SuzukiRelator.word, suzukiFreeGenerator] using
    suzukiPresented_relator_eq_one (SuzukiRelator.rootFarSquare j hj)

public theorem suzukiPresented_tail_far_commute (n : Nat)
    (i j : Fin (n + 3)) (hi : i ≠ 0) (hj : j ≠ 0)
    (hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    Commute (PresentedGroup.of i : SuzukiPresentedGroup n) (PresentedGroup.of j) := by
  apply commutatorElement_eq_one_iff_commute.mp
  simpa [SuzukiRelator.word, suzukiFreeGenerator] using
    suzukiPresented_relator_eq_one
      (SuzukiRelator.tailFarCommutator i j hi hj hfar)

public theorem suzukiPresentationC2Generator_inv :
    suzukiPresentationC2Generator⁻¹ = suzukiPresentationC2Generator := by
  exact (eq_inv_of_mul_eq_one_left suzukiPresentationC2Generator_sq).symm

public theorem suzukiSemidirect_t_conj_inl (n : Nat) (x : SuzukiPresentedGroup n) :
    (SemidirectProduct.inr suzukiPresentationC2Generator :
        SuzukiPresentationSemidirect n) *
      SemidirectProduct.inl x *
      SemidirectProduct.inr suzukiPresentationC2Generator =
        SemidirectProduct.inl (suzukiInvertGeneratorAut n x) := by
  have h := SemidirectProduct.inl_aut
    (φ := suzukiPresentationC2Action n) suzukiPresentationC2Generator x
  rw [suzukiPresentationC2Action_generator,
    suzukiPresentationC2Generator_inv] at h
  exact h.symm

public theorem suzukiCoxeterSimple_sq (n : Nat) (i : Fin (n + 4)) :
    suzukiCoxeterSimple n i ^ 2 = 1 := by
  refine Fin.cases ?_ (fun k => ?_) i
  · rw [suzukiCoxeterSimple_zero, ← map_pow,
      show suzukiPresentationC2Generator ^ 2 = 1 by
        simpa [pow_two] using suzukiPresentationC2Generator_sq, map_one]
  · rw [suzukiCoxeterSimple_succ]
    let t : SuzukiPresentationSemidirect n :=
      SemidirectProduct.inr suzukiPresentationC2Generator
    let s : SuzukiPresentedGroup n := PresentedGroup.of k
    change (t * SemidirectProduct.inl s) ^ 2 = 1
    calc
      (t * SemidirectProduct.inl s) ^ 2 =
          (t * SemidirectProduct.inl s * t) * SemidirectProduct.inl s := by
        simp [pow_two, mul_assoc]
      _ = SemidirectProduct.inl (suzukiInvertGeneratorAut n s) *
          SemidirectProduct.inl s := by
        rw [suzukiSemidirect_t_conj_inl]
      _ = 1 := by
        rw [← map_mul]
        change SemidirectProduct.inl (s⁻¹ * s) = 1
        simp

public theorem suzukiCoxeterSimple_zero_mul_succ (n : Nat)
    (i : Fin (n + 3)) :
    suzukiCoxeterSimple n 0 * suzukiCoxeterSimple n i.succ =
      SemidirectProduct.inl (PresentedGroup.of i) := by
  rw [suzukiCoxeterSimple_zero, suzukiCoxeterSimple_succ]
  rw [← mul_assoc, ← map_mul, suzukiPresentationC2Generator_sq, map_one,
    one_mul]

public theorem suzukiCoxeterSimple_succ_mul_succ (n : Nat)
    (i j : Fin (n + 3)) :
    suzukiCoxeterSimple n i.succ * suzukiCoxeterSimple n j.succ =
      SemidirectProduct.inl
        ((PresentedGroup.of i : SuzukiPresentedGroup n)⁻¹ *
          PresentedGroup.of j) := by
  rw [suzukiCoxeterSimple_succ, suzukiCoxeterSimple_succ]
  let t : SuzukiPresentationSemidirect n :=
    SemidirectProduct.inr suzukiPresentationC2Generator
  let si : SuzukiPresentedGroup n := PresentedGroup.of i
  let sj : SuzukiPresentedGroup n := PresentedGroup.of j
  change (t * SemidirectProduct.inl si) * (t * SemidirectProduct.inl sj) = _
  calc
    (t * SemidirectProduct.inl si) * (t * SemidirectProduct.inl sj) =
        (t * SemidirectProduct.inl si * t) * SemidirectProduct.inl sj := by
      simp [mul_assoc]
    _ = SemidirectProduct.inl (suzukiInvertGeneratorAut n si) *
        SemidirectProduct.inl sj := by
      rw [suzukiSemidirect_t_conj_inl]
    _ = SemidirectProduct.inl (si⁻¹ * sj) := by
      rw [← map_mul]
      rfl

public theorem inv_mul_pow_eq_one_of_mul_pow_eq_one_of_sq_eq_one
    {G : Type*} [Group G] (a b : G) (m : Nat)
    (hb : b ^ 2 = 1) (hab : (a * b) ^ m = 1) :
    (a⁻¹ * b) ^ m = 1 := by
  have hbb : b * b = 1 := by simpa [pow_two] using hb
  have hbinv : b⁻¹ = b := (eq_inv_of_mul_eq_one_left hbb).symm
  have hconj : a⁻¹ * b = b * (a * b)⁻¹ * b⁻¹ := by
    rw [mul_inv_rev, hbinv]
    simp [← mul_assoc, hbb]
  rw [hconj, conj_pow, inv_pow, hab, inv_one]
  simp

public theorem rotate_mul_pow_eq_one {G : Type*} [Group G]
    (a b : G) (m : Nat) (hab : (a * b) ^ m = 1) :
    (b * a) ^ m = 1 := by
  have hrotate : b * a = a⁻¹ * (a * b) * (a⁻¹)⁻¹ := by
    simp
  rw [hrotate, conj_pow, hab]
  simp

public theorem suzukiPresented_inv_adjacent_cube (n : Nat)
    (i : Fin (n + 2)) :
    (((PresentedGroup.of i.castSucc : SuzukiPresentedGroup n)⁻¹) *
      PresentedGroup.of i.succ) ^ 3 = 1 := by
  by_cases hi : i = 0
  · subst i
    apply inv_mul_pow_eq_one_of_mul_pow_eq_one_of_sq_eq_one
    · apply suzukiPresented_tail_sq
      simp
    · simpa using suzukiPresented_root_adjacent_cube n
  · have hi' : i.castSucc ≠ (0 : Fin (n + 3)) := by
      intro h
      apply hi
      ext
      simpa using congrArg Fin.val h
    have hinv :
        (PresentedGroup.of i.castSucc : SuzukiPresentedGroup n)⁻¹ =
          PresentedGroup.of i.castSucc := by
      apply (eq_inv_of_mul_eq_one_left ?_).symm
      simpa [pow_two] using suzukiPresented_tail_sq n i.castSucc hi'
    rw [hinv]
    exact suzukiPresented_tail_adjacent_cube n i hi

public theorem suzukiCoxeterSimple_braid (n : Nat) (i : Fin (n + 3)) :
    (suzukiCoxeterSimple n i.castSucc *
      suzukiCoxeterSimple n i.succ) ^ 3 = 1 := by
  refine Fin.cases ?_ (fun k => ?_) i
  · rw [show (0 : Fin (n + 3)).castSucc = 0 by rfl,
      show (0 : Fin (n + 3)).succ = (0 : Fin (n + 3)).succ by rfl,
      suzukiCoxeterSimple_zero_mul_succ, ← map_pow,
      suzukiPresented_root_cube, map_one]
  · rw [show k.succ.castSucc = k.castSucc.succ by rfl,
      show k.succ.succ = k.succ.succ by rfl,
      suzukiCoxeterSimple_succ_mul_succ, ← map_pow,
      suzukiPresented_inv_adjacent_cube, map_one]

public theorem suzukiCoxeterSimple_braid_rev (n : Nat) (i : Fin (n + 3)) :
    (suzukiCoxeterSimple n i.succ *
      suzukiCoxeterSimple n i.castSucc) ^ 3 = 1 :=
  rotate_mul_pow_eq_one _ _ 3 (suzukiCoxeterSimple_braid n i)

public theorem suzukiPresented_inv_far_sq (n : Nat)
    (i j : Fin (n + 3))
    (hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    (((PresentedGroup.of i : SuzukiPresentedGroup n)⁻¹) *
      PresentedGroup.of j) ^ 2 = 1 := by
  by_cases hi : i = 0
  · subst i
    simp only [Fin.val_zero] at hfar
    have hjfar : 1 < j.val := by omega
    apply inv_mul_pow_eq_one_of_mul_pow_eq_one_of_sq_eq_one
    · apply suzukiPresented_tail_sq n j
      apply Fin.ne_of_val_ne
      simpa only [Fin.val_zero] using
        (Nat.ne_of_gt (show 0 < j.val by omega))
    · exact suzukiPresented_root_far_sq n j hjfar
  · have hi2 := suzukiPresented_tail_sq n i hi
    have hiinv :
        (PresentedGroup.of i : SuzukiPresentedGroup n)⁻¹ = PresentedGroup.of i := by
      apply (eq_inv_of_mul_eq_one_left ?_).symm
      simpa [pow_two] using hi2
    rw [hiinv]
    by_cases hj : j = 0
    · subst j
      simp only [Fin.val_zero] at hfar
      have hifar : 1 < i.val := by omega
      exact rotate_mul_pow_eq_one _ _ 2
        (suzukiPresented_root_far_sq n i hifar)
    · have hj2 := suzukiPresented_tail_sq n j hj
      have hcomm := suzukiPresented_tail_far_commute n i j hi hj hfar
      rw [hcomm.mul_pow, hi2, hj2, one_mul]

public theorem suzukiCoxeterSimple_far_forward (n : Nat)
    (i j : Fin (n + 4)) (hfar : i.val + 1 < j.val) :
    (suzukiCoxeterSimple n i * suzukiCoxeterSimple n j) ^ 2 = 1 := by
  revert hfar
  refine Fin.cases ?_ (fun a => ?_) i
  · intro hfar
    revert hfar
    refine Fin.cases (by intro hfar; change 0 + 1 < 0 at hfar; omega)
      (fun b hfar => ?_) j
    change 0 + 1 < b.val + 1 at hfar
    have hb : b ≠ 0 := by
      intro hb0
      subst b
      change 0 + 1 < 0 + 1 at hfar
      omega
    rw [suzukiCoxeterSimple_zero_mul_succ, ← map_pow,
      suzukiPresented_tail_sq n b hb, map_one]
  · intro hfar
    revert hfar
    refine Fin.cases
      (by intro hfar; change a.val + 1 + 1 < 0 at hfar; omega)
      (fun b hfar => ?_) j
    change a.val + 1 + 1 < b.val + 1 at hfar
    rw [suzukiCoxeterSimple_succ_mul_succ, ← map_pow]
    apply congrArg SemidirectProduct.inl
      (suzukiPresented_inv_far_sq n a b (by left; omega))

public theorem suzukiCoxeterSimple_far (n : Nat)
    {i j : Fin (n + 4)}
    (hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    (suzukiCoxeterSimple n i * suzukiCoxeterSimple n j) ^ 2 = 1 := by
  rcases hfar with hij | hji
  · exact suzukiCoxeterSimple_far_forward n i j hij
  · exact rotate_mul_pow_eq_one _ _ 2
      (suzukiCoxeterSimple_far_forward n j i hji)

public theorem suzukiCoxeterSimple_isLiftable (n : Nat) :
    CoxeterMatrix.IsLiftable (CoxeterMatrix.A (n + 4))
      (suzukiCoxeterSimple n) := by
  intro i j
  by_cases hij : i = j
  · subst j
    simpa [CoxeterMatrix.A, pow_two] using
      suzukiCoxeterSimple_sq n i
  by_cases hadj : j.val + 1 = i.val ∨ i.val + 1 = j.val
  · rcases hadj with hji | hij'
    · let k : Fin (n + 3) := ⟨j.val, by omega⟩
      have hk0 : k.castSucc = j := by ext; simp [k]
      have hk1 : k.succ = i := by ext; simp [k]; omega
      simpa [CoxeterMatrix.A, hij, hji, hk0, hk1] using
        suzukiCoxeterSimple_braid_rev n k
    · let k : Fin (n + 3) := ⟨i.val, by omega⟩
      have hk0 : k.castSucc = i := by ext; simp [k]
      have hk1 : k.succ = j := by ext; simp [k]; omega
      simpa [CoxeterMatrix.A, hij, hij', hk0, hk1] using
        suzukiCoxeterSimple_braid n k
  · have hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val := by omega
    simpa [CoxeterMatrix.A, hij, hadj] using
      suzukiCoxeterSimple_far n hfar

public noncomputable def coxeterToSuzukiPresentationSemidirect (n : Nat) :
    TypeACoxeterGroup n →* SuzukiPresentationSemidirect n :=
  (CoxeterMatrix.A (n + 4)).toCoxeterSystem.lift
    ⟨suzukiCoxeterSimple n, suzukiCoxeterSimple_isLiftable n⟩

@[simp]
public theorem coxeterToSuzukiPresentationSemidirect_simple (n : Nat)
    (i : Fin (n + 4)) :
    coxeterToSuzukiPresentationSemidirect n
        ((CoxeterMatrix.A (n + 4)).simple i) =
      suzukiCoxeterSimple n i := by
  change coxeterToSuzukiPresentationSemidirect n
      ((CoxeterMatrix.A (n + 4)).toCoxeterSystem.simple i) = _
  exact (CoxeterMatrix.A (n + 4)).toCoxeterSystem.lift_apply_simple
    (suzukiCoxeterSimple_isLiftable n) i

public theorem coxeterToSuzukiPresentationSemidirect_surjective (n : Nat) :
    Function.Surjective (coxeterToSuzukiPresentationSemidirect n) := by
  let f := coxeterToSuzukiPresentationSemidirect n
  have hinl : ∀ x : SuzukiPresentedGroup n,
      ∃ __ch5_Theorem523Suzuki_w : TypeACoxeterGroup n, f __ch5_Theorem523Suzuki_w = SemidirectProduct.inl x := by
    intro x
    let H : Subgroup (SuzukiPresentedGroup n) :=
      f.range.comap SemidirectProduct.inl
    have hx : x ∈ H := by
      apply PresentedGroup.generated_by _ H
      intro i
      change SemidirectProduct.inl (PresentedGroup.of i) ∈ f.range
      refine ⟨(CoxeterMatrix.A (n + 4)).simple 0 *
          (CoxeterMatrix.A (n + 4)).simple i.succ, ?_⟩
      change f (_ * _) = _
      rw [map_mul, coxeterToSuzukiPresentationSemidirect_simple,
        coxeterToSuzukiPresentationSemidirect_simple,
        suzukiCoxeterSimple_zero_mul_succ]
    exact hx
  have hinr : ∀ y : SuzukiPresentationC2,
      ∃ __ch5_Theorem523Suzuki_w : TypeACoxeterGroup n, f __ch5_Theorem523Suzuki_w = SemidirectProduct.inr y := by
    intro y
    rcases suzukiPresentationC2_eq_one_or_generator y with rfl | rfl
    · exact ⟨1, by simp [f]⟩
    · refine ⟨(CoxeterMatrix.A (n + 4)).simple 0, ?_⟩
      rw [coxeterToSuzukiPresentationSemidirect_simple,
        suzukiCoxeterSimple_zero]
  intro z
  rcases hinl z.left with ⟨u, hu⟩
  rcases hinr z.right with ⟨v, hv⟩
  refine ⟨u * v, ?_⟩
  rw [map_mul, hu, hv, SemidirectProduct.inl_left_mul_inr_right]

public theorem suzukiPresentedProjection_injective (n : Nat) :
    Function.Injective (suzukiPresentedProjection n) := by
  let : Finite (TypeACoxeterGroup n) :=
    TypeANormalForm.group_finite (n + 4)
  let : Finite (SuzukiPresentationSemidirect n) :=
    Finite.of_surjective (coxeterToSuzukiPresentationSemidirect n)
      (coxeterToSuzukiPresentationSemidirect_surjective n)
  let : Finite (SuzukiPresentedGroup n) :=
    Finite.of_injective (SemidirectProduct.inl :
      SuzukiPresentedGroup n → SuzukiPresentationSemidirect n)
      SemidirectProduct.inl_injective
  refine ((suzukiPresentedProjection_surjective n).bijective_of_nat_card_le ?_).1
  have hcox : Nat.card (SuzukiPresentationSemidirect n) ≤
      Nat.card (TypeACoxeterGroup n) :=
    Nat.card_le_card_of_surjective (coxeterToSuzukiPresentationSemidirect n)
      (coxeterToSuzukiPresentationSemidirect_surjective n)
  have hfac : Nat.card (TypeACoxeterGroup n) ≤ (n + 5).factorial := by
    simpa [TypeACoxeterGroup, TypeANormalForm.Group, Nat.add_assoc] using
      TypeANormalForm.natCard_group_le_factorial (n + 4)
  have hC2 : Nat.card SuzukiPresentationC2 = 2 := by
    simp [SuzukiPresentationC2]
  have hsemi : Nat.card (SuzukiPresentationSemidirect n) =
      2 * Nat.card (SuzukiPresentedGroup n) := by
    rw [SemidirectProduct.card, hC2]
    omega
  have hAlt : 2 * Nat.card (alternatingGroup (Fin (n + 5))) =
      (n + 5).factorial := by
    have h := two_mul_nat_card_alternatingGroup (α := Fin (n + 5))
    rw [Nat.card_perm, Nat.card_fin] at h
    exact h
  omega

public theorem alternatingSuzukiKernel_eq_normalClosure (n : Nat) :
    alternatingSuzukiKernel n = Subgroup.normalClosure (suzukiRelatorSet n) :=
  alternatingSuzukiKernel_eq_normalClosure_of_projection_injective n
    (suzukiPresentedProjection_injective n)


public theorem inv_eq_mul_inv_sq {G : Type*} [Group G] (x : G) :
    x⁻¹ = x * (x ^ 2)⁻¹ := by
  group

public theorem sq_defect_adjacent {G : Type*} [Group G] (x y : G)
    (hx : x ^ 2 ∈ Subgroup.center G)
    (hy : y ^ 2 ∈ Subgroup.center G)
    (hxy : (x * y) ^ 3 ∈ Subgroup.center G) :
    ((x * y) ^ 3) ^ 2 = (x ^ 2 * y ^ 2) ^ 3 := by
  let a := x ^ 2
  let b := y ^ 2
  let c := (x * y) ^ 3
  have ha : a ∈ Subgroup.center G := hx
  have hb : b ∈ Subgroup.center G := hy
  have hc : c ∈ Subgroup.center G := hxy
  have hainv : a⁻¹ ∈ Subgroup.center G := (Subgroup.center G).inv_mem ha
  have hbinv : b⁻¹ ∈ Subgroup.center G := (Subgroup.center G).inv_mem hb
  have habinv : (a * b)⁻¹ ∈ Subgroup.center G :=
    (Subgroup.center G).inv_mem ((Subgroup.center G).mul_mem ha hb)
  have hinv : (x * y)⁻¹ = (a * b)⁻¹ * (y * x) := by
    rw [mul_inv_rev, inv_eq_mul_inv_sq y, inv_eq_mul_inv_sq x]
    change (y * b⁻¹) * (x * a⁻¹) = _
    calc
      (y * b⁻¹) * (x * a⁻¹) = y * (b⁻¹ * x) * a⁻¹ := by
        simp [mul_assoc]
      _ = y * (x * b⁻¹) * a⁻¹ := by
        rw [Subgroup.mem_center_iff.mp hbinv x]
      _ = (y * x) * (b⁻¹ * a⁻¹) := by simp [mul_assoc]
      _ = (b⁻¹ * a⁻¹) * (y * x) := by
        rw [Subgroup.mem_center_iff.mp
          ((Subgroup.center G).mul_mem hbinv hainv) (y * x)]
      _ = (a * b)⁻¹ * (y * x) := by rw [mul_inv_rev]
  have hyx : (y * x) ^ 3 = c := by
    calc
      (y * x) ^ 3 = (y * (x * y) * y⁻¹) ^ 3 := by
        congr 1
        group
      _ = y * (x * y) ^ 3 * y⁻¹ := by rw [conj_pow]
      _ = c := by
        change y * c * y⁻¹ = c
        rw [Subgroup.mem_center_iff.mp hc y]
        simp
  have hcinv : c⁻¹ = (a * b)⁻¹ ^ 3 * c := by
    calc
      c⁻¹ = ((x * y)⁻¹) ^ 3 := by
        change ((x * y) ^ 3)⁻¹ = _
        rw [inv_pow]
      _ = ((a * b)⁻¹ * (y * x)) ^ 3 := by rw [hinv]
      _ = (a * b)⁻¹ ^ 3 * (y * x) ^ 3 := by
        have hcomm : Commute (a * b)⁻¹ (y * x) := by
          change (a * b)⁻¹ * (y * x) = (y * x) * (a * b)⁻¹
          exact (Subgroup.mem_center_iff.mp habinv (y * x)).symm
        rw [hcomm.mul_pow]
      _ = (a * b)⁻¹ ^ 3 * c := by rw [hyx]
  have hcsolve : c = c⁻¹ * (a * b) ^ 3 := by
    calc
      c = (c⁻¹)⁻¹ := by simp
      _ = ((a * b)⁻¹ ^ 3 * c)⁻¹ := by rw [hcinv]
      _ = c⁻¹ * ((a * b)⁻¹ ^ 3)⁻¹ := mul_inv_rev _ _
      _ = c⁻¹ * (a * b) ^ 3 := by rw [inv_pow]; simp
  change c ^ 2 = (a * b) ^ 3
  rw [pow_two]
  nth_rw 1 [hcsolve]
  calc
    (c⁻¹ * (a * b) ^ 3) * c = c⁻¹ * ((a * b) ^ 3 * c) := by
      simp [mul_assoc]
    _ = c⁻¹ * (c * (a * b) ^ 3) := by
      rw [Subgroup.mem_center_iff.mp hc ((a * b) ^ 3)]
    _ = (a * b) ^ 3 := by simp

public theorem inv_eq_sq_mul_inv_cube {G : Type*} [Group G] (x : G) :
    x⁻¹ = x ^ 2 * (x ^ 3)⁻¹ := by
  group

public theorem cube_defect_root_far {G : Type*} [Group G] (x y : G)
    (hx : x ^ 3 ∈ Subgroup.center G)
    (hy : y ^ 2 ∈ Subgroup.center G)
    (hxy : (x * y) ^ 2 ∈ Subgroup.center G) :
    (x ^ 3) ^ 2 * (y ^ 2) ^ 3 = ((x * y) ^ 2) ^ 3 := by
  let a := x ^ 3
  let b := y ^ 2
  let c := (x * y) ^ 2
  let q := a * b * c⁻¹
  have ha : a ∈ Subgroup.center G := hx
  have hb : b ∈ Subgroup.center G := hy
  have hc : c ∈ Subgroup.center G := hxy
  have hainv : a⁻¹ ∈ Subgroup.center G := (Subgroup.center G).inv_mem ha
  have hbinv : b⁻¹ ∈ Subgroup.center G := (Subgroup.center G).inv_mem hb
  have hcinv : c⁻¹ ∈ Subgroup.center G := (Subgroup.center G).inv_mem hc
  have habinv : (a * b)⁻¹ ∈ Subgroup.center G :=
    (Subgroup.center G).inv_mem ((Subgroup.center G).mul_mem ha hb)
  have hq : q ∈ Subgroup.center G :=
    (Subgroup.center G).mul_mem ((Subgroup.center G).mul_mem ha hb) hcinv
  have hyx_sq : (y * x) ^ 2 = c := by
    calc
      (y * x) ^ 2 = (y * (x * y) * y⁻¹) ^ 2 := by
        congr 1
        group
      _ = y * (x * y) ^ 2 * y⁻¹ := by rw [conj_pow]
      _ = c := by
        change y * c * y⁻¹ = c
        rw [Subgroup.mem_center_iff.mp hc y]
        simp
  have hxy_inv_center : (x * y)⁻¹ = c⁻¹ * (x * y) := by
    rw [inv_eq_mul_inv_sq]
    change x * y * c⁻¹ = c⁻¹ * (x * y)
    exact Subgroup.mem_center_iff.mp hcinv (x * y)
  have hxy_inv_powers : (x * y)⁻¹ = (a * b)⁻¹ * (y * x ^ 2) := by
    rw [mul_inv_rev, inv_eq_mul_inv_sq y, inv_eq_sq_mul_inv_cube x]
    change (y * b⁻¹) * (x ^ 2 * a⁻¹) = _
    calc
      (y * b⁻¹) * (x ^ 2 * a⁻¹) = y * (b⁻¹ * x ^ 2) * a⁻¹ := by
        simp [mul_assoc]
      _ = y * (x ^ 2 * b⁻¹) * a⁻¹ := by
        rw [Subgroup.mem_center_iff.mp hbinv (x ^ 2)]
      _ = (y * x ^ 2) * (b⁻¹ * a⁻¹) := by simp [mul_assoc]
      _ = (b⁻¹ * a⁻¹) * (y * x ^ 2) := by
        rw [Subgroup.mem_center_iff.mp
          ((Subgroup.center G).mul_mem hbinv hainv) (y * x ^ 2)]
      _ = (a * b)⁻¹ * (y * x ^ 2) := by rw [mul_inv_rev]
  have hyx2 : y * x ^ 2 = q * (x * y) := by
    have heq : (a * b)⁻¹ * (y * x ^ 2) = c⁻¹ * (x * y) :=
      hxy_inv_powers.symm.trans hxy_inv_center
    calc
      y * x ^ 2 = (a * b) * ((a * b)⁻¹ * (y * x ^ 2)) := by group
      _ = (a * b) * (c⁻¹ * (x * y)) := by rw [heq]
      _ = q * (x * y) := by simp [q, mul_assoc]
  have hyx_inv_center : (y * x)⁻¹ = c⁻¹ * (y * x) := by
    rw [inv_eq_mul_inv_sq, hyx_sq]
    exact Subgroup.mem_center_iff.mp hcinv (y * x)
  have hyx_inv_powers : (y * x)⁻¹ = (a * b)⁻¹ * (x ^ 2 * y) := by
    rw [mul_inv_rev, inv_eq_sq_mul_inv_cube x, inv_eq_mul_inv_sq y]
    change (x ^ 2 * a⁻¹) * (y * b⁻¹) = _
    calc
      (x ^ 2 * a⁻¹) * (y * b⁻¹) = x ^ 2 * (a⁻¹ * y) * b⁻¹ := by
        simp [mul_assoc]
      _ = x ^ 2 * (y * a⁻¹) * b⁻¹ := by
        rw [Subgroup.mem_center_iff.mp hainv y]
      _ = (x ^ 2 * y) * (a⁻¹ * b⁻¹) := by simp [mul_assoc]
      _ = (a⁻¹ * b⁻¹) * (x ^ 2 * y) := by
        rw [Subgroup.mem_center_iff.mp
          ((Subgroup.center G).mul_mem hainv hbinv) (x ^ 2 * y)]
      _ = (b⁻¹ * a⁻¹) * (x ^ 2 * y) := by
        congr 1
        exact (Subgroup.mem_center_iff.mp hainv b⁻¹).symm
      _ = (a * b)⁻¹ * (x ^ 2 * y) := by rw [mul_inv_rev]
  have hx2y : x ^ 2 * y = q * (y * x) := by
    have heq : (a * b)⁻¹ * (x ^ 2 * y) = c⁻¹ * (y * x) :=
      hyx_inv_powers.symm.trans hyx_inv_center
    calc
      x ^ 2 * y = (a * b) * ((a * b)⁻¹ * (x ^ 2 * y)) := by group
      _ = (a * b) * (c⁻¹ * (y * x)) := by rw [heq]
      _ = q * (y * x) := by simp [q, mul_assoc]
  have hxyx : x * y * x = c * b⁻¹ * y := by
    have hcdef : x * y * x * y = c := by simp [c, pow_two, mul_assoc]
    calc
      x * y * x = (x * y * x * y) * y⁻¹ := by simp [mul_assoc]
      _ = c * y⁻¹ := by rw [hcdef]
      _ = c * (y * b⁻¹) := by rw [inv_eq_mul_inv_sq y]
      _ = c * b⁻¹ * y := by
        rw [Subgroup.mem_center_iff.mp hbinv y]
        simp [mul_assoc]
  have hleft1 : x ^ 2 * y * x = q ^ 2 * (x * y) := by
    calc
      x ^ 2 * y * x = (q * (y * x)) * x := by rw [hx2y]
      _ = q * (y * x ^ 2) := by simp [pow_two, mul_assoc]
      _ = q * (q * (x * y)) := by rw [hyx2]
      _ = q ^ 2 * (x * y) := by simp [pow_two, mul_assoc]
  have hleft2 : x ^ 2 * y * x = (c * b⁻¹) * (x * y) := by
    calc
      x ^ 2 * y * x = x * (x * y * x) := by simp [pow_two, mul_assoc]
      _ = x * (c * b⁻¹ * y) := by rw [hxyx]
      _ = (c * b⁻¹) * (x * y) := by
        calc
          x * (c * b⁻¹ * y) = (x * (c * b⁻¹)) * y := by simp [mul_assoc]
          _ = ((c * b⁻¹) * x) * y := by
            rw [Subgroup.mem_center_iff.mp
              ((Subgroup.center G).mul_mem hc hbinv) x]
          _ = (c * b⁻¹) * (x * y) := by simp [mul_assoc]
  have hq2 : q ^ 2 = c * b⁻¹ := by
    apply mul_right_cancel (b := x * y)
    exact hleft1.symm.trans hleft2
  let : CommGroup (Subgroup.center G) := {
    mul_comm := fun u v => Subtype.ext
      (Subgroup.mem_center_iff.mp u.2 v.1).symm }
  let aa : Subgroup.center G := ⟨a, ha⟩
  let bb : Subgroup.center G := ⟨b, hb⟩
  let cc : Subgroup.center G := ⟨c, hc⟩
  let qq : Subgroup.center G := ⟨q, hq⟩
  have hqdef : qq = aa * bb * cc⁻¹ := rfl
  have hq2' : qq ^ 2 = cc * bb⁻¹ := by exact Subtype.ext hq2
  have hcenterEq : aa ^ 2 * bb ^ 3 = cc ^ 3 := by
    calc
      aa ^ 2 * bb ^ 3 = (aa * bb * cc⁻¹) ^ 2 * cc ^ 2 * bb := by
        symm
        calc
          (aa * bb * cc⁻¹) ^ 2 * cc ^ 2 * bb =
              aa ^ 2 * bb ^ 3 * (cc⁻¹ * cc) * (cc⁻¹ * cc) := by
            simp only [pow_succ, pow_zero]
            ac_rfl
          _ = aa ^ 2 * bb ^ 3 := by simp
      _ = qq ^ 2 * cc ^ 2 * bb := by rw [← hqdef]
      _ = (cc * bb⁻¹) * cc ^ 2 * bb := by rw [hq2']
      _ = cc ^ 3 := by
        calc
          (cc * bb⁻¹) * cc ^ 2 * bb = cc ^ 3 * (bb⁻¹ * bb) := by
            simp only [pow_succ]
            ac_rfl
          _ = cc ^ 3 := by simp
  exact congrArg Subtype.val hcenterEq

public theorem fourth_defect_root_adjacent {G : Type*} [Group G] (x y : G)
    (hx : x ^ 3 ∈ Subgroup.center G)
    (hy : y ^ 2 ∈ Subgroup.center G)
    (hxy : (x * y) ^ 3 ∈ Subgroup.center G) :
    (x ^ 3) ^ 4 * (y ^ 2) ^ 6 = ((x * y) ^ 3) ^ 4 := by
  let a := x ^ 3
  let b := y ^ 2
  let c := (x * y) ^ 3
  let d := x * y * x
  let q := a * b * c⁻¹
  have ha : a ∈ Subgroup.center G := hx
  have hb : b ∈ Subgroup.center G := hy
  have hc : c ∈ Subgroup.center G := hxy
  have hainv : a⁻¹ ∈ Subgroup.center G := (Subgroup.center G).inv_mem ha
  have hbinv : b⁻¹ ∈ Subgroup.center G := (Subgroup.center G).inv_mem hb
  have hcinv : c⁻¹ ∈ Subgroup.center G := (Subgroup.center G).inv_mem hc
  have hq : q ∈ Subgroup.center G :=
    (Subgroup.center G).mul_mem ((Subgroup.center G).mul_mem ha hb) hcinv
  have hxy_inv_center : (x * y)⁻¹ = c⁻¹ * (x * y) ^ 2 := by
    rw [inv_eq_sq_mul_inv_cube]
    change (x * y) ^ 2 * c⁻¹ = c⁻¹ * (x * y) ^ 2
    exact Subgroup.mem_center_iff.mp hcinv ((x * y) ^ 2)
  have hxy_inv_powers : (x * y)⁻¹ = (a * b)⁻¹ * (y * x ^ 2) := by
    rw [mul_inv_rev, inv_eq_mul_inv_sq y, inv_eq_sq_mul_inv_cube x]
    change (y * b⁻¹) * (x ^ 2 * a⁻¹) = _
    calc
      (y * b⁻¹) * (x ^ 2 * a⁻¹) = y * (b⁻¹ * x ^ 2) * a⁻¹ := by
        simp [mul_assoc]
      _ = y * (x ^ 2 * b⁻¹) * a⁻¹ := by
        rw [Subgroup.mem_center_iff.mp hbinv (x ^ 2)]
      _ = (y * x ^ 2) * (b⁻¹ * a⁻¹) := by simp [mul_assoc]
      _ = (b⁻¹ * a⁻¹) * (y * x ^ 2) := by
        rw [Subgroup.mem_center_iff.mp
          ((Subgroup.center G).mul_mem hbinv hainv) (y * x ^ 2)]
      _ = (a * b)⁻¹ * (y * x ^ 2) := by rw [mul_inv_rev]
  have hyx2 : y * x ^ 2 = q * (x * y) ^ 2 := by
    have heq : (a * b)⁻¹ * (y * x ^ 2) = c⁻¹ * (x * y) ^ 2 :=
      hxy_inv_powers.symm.trans hxy_inv_center
    calc
      y * x ^ 2 = (a * b) * ((a * b)⁻¹ * (y * x ^ 2)) := by group
      _ = (a * b) * (c⁻¹ * (x * y) ^ 2) := by rw [heq]
      _ = q * (x * y) ^ 2 := by simp [q, mul_assoc]
  have hd_center_form : d = c * b⁻¹ * (y * x⁻¹ * y⁻¹) := by
    dsimp [d, c, b]
    simp only [pow_succ, pow_zero]
    group
  have ht_cube : (y * x⁻¹ * y⁻¹) ^ 3 = a⁻¹ := by
    calc
      (y * x⁻¹ * y⁻¹) ^ 3 = y * (x⁻¹) ^ 3 * y⁻¹ := by rw [conj_pow]
      _ = y * a⁻¹ * y⁻¹ := by rw [inv_pow]
      _ = a⁻¹ := by
        rw [Subgroup.mem_center_iff.mp hainv y]
        simp
  have hd_cube_center : d ^ 3 = c ^ 3 * b⁻¹ ^ 3 * a⁻¹ := by
    rw [hd_center_form]
    have hcb : Commute (c * b⁻¹) (y * x⁻¹ * y⁻¹) := by
      change (c * b⁻¹) * (y * x⁻¹ * y⁻¹) =
        (y * x⁻¹ * y⁻¹) * (c * b⁻¹)
      exact (Subgroup.mem_center_iff.mp
        ((Subgroup.center G).mul_mem hc hbinv) (y * x⁻¹ * y⁻¹)).symm
    rw [hcb.mul_pow, ht_cube]
    have hcb' : Commute c b⁻¹ := by
      change c * b⁻¹ = b⁻¹ * c
      exact (Subgroup.mem_center_iff.mp hc b⁻¹).symm
    rw [hcb'.mul_pow]
  have hd_cube_direct : d ^ 3 = a ^ 3 * b ^ 3 * c⁻¹ := by
    change (x * y * x) ^ 3 = _
    calc
      (x * y * x) ^ 3 = x * (y * x ^ 2) * y * x ^ 2 * y * x := by
        simp [pow_succ, mul_assoc]
      _ = x * (q * (x * y) ^ 2) * y * x ^ 2 * y * x := by rw [hyx2]
      _ = q * (x * (x * y) ^ 2 * y * x ^ 2 * y * x) := by
        calc
          x * (q * (x * y) ^ 2) * y * x ^ 2 * y * x =
              (x * q) * ((x * y) ^ 2 * y * x ^ 2 * y * x) := by
            simp [mul_assoc]
          _ = (q * x) * ((x * y) ^ 2 * y * x ^ 2 * y * x) := by
            rw [Subgroup.mem_center_iff.mp hq x]
          _ = q * (x * (x * y) ^ 2 * y * x ^ 2 * y * x) := by
            simp [mul_assoc]
      _ = q * (a ^ 2 * b ^ 2) := by
        congr 1
        calc
          x * (x * y) ^ 2 * y * x ^ 2 * y * x =
              x ^ 2 * y * x * b * x ^ 2 * y * x := by
            dsimp [b]
            simp [pow_two, mul_assoc]
          _ = b * (x ^ 2 * y * x * x ^ 2 * y * x) := by
            calc
              x ^ 2 * y * x * b * x ^ 2 * y * x =
                  (x ^ 2 * y * x) * b * (x ^ 2 * y * x) := by
                simp [mul_assoc]
              _ = b * (x ^ 2 * y * x) * (x ^ 2 * y * x) := by
                rw [Subgroup.mem_center_iff.mp hb (x ^ 2 * y * x)]
              _ = b * (x ^ 2 * y * x * x ^ 2 * y * x) := by
                simp [mul_assoc]
          _ = b * (x ^ 2 * y * a * y * x) := by
            dsimp [a]
            group
          _ = a * b * (x ^ 2 * y * y * x) := by
            calc
              b * (x ^ 2 * y * a * y * x) = b * ((x ^ 2 * y) * a * (y * x)) := by
                simp [mul_assoc]
              _ = b * (a * (x ^ 2 * y) * (y * x)) := by
                rw [Subgroup.mem_center_iff.mp ha (x ^ 2 * y)]
              _ = (b * a) * ((x ^ 2 * y) * (y * x)) := by simp [mul_assoc]
              _ = (a * b) * ((x ^ 2 * y) * (y * x)) := by
                rw [Subgroup.mem_center_iff.mp ha b]
              _ = a * b * (x ^ 2 * y * y * x) := by simp [mul_assoc]
          _ = a ^ 2 * b ^ 2 := by
            have hab : Commute a b := by
              change a * b = b * a
              exact (Subgroup.mem_center_iff.mp ha b).symm
            calc
              a * b * (x ^ 2 * y * y * x) = a * b * (x ^ 2 * b * x) := by
                dsimp [b]
                simp [pow_two, mul_assoc]
              _ = a * b * (b * (x ^ 2 * x)) := by
                rw [Subgroup.mem_center_iff.mp hb (x ^ 2)]
                simp [mul_assoc]
              _ = a * b * (b * a) := by
                rw [show x ^ 2 * x = a by
                  change x ^ 2 * x = x ^ 3
                  rw [← pow_succ]]
              _ = a ^ 2 * b ^ 2 := by
                rw [← hab.mul_pow 2, pow_two]
                simp only [mul_assoc]
                rw [hab.eq.symm]
      _ = a ^ 3 * b ^ 3 * c⁻¹ := by
        have hab : Commute a b := by
          change a * b = b * a
          exact (Subgroup.mem_center_iff.mp ha b).symm
        change (a * b * c⁻¹) * (a ^ 2 * b ^ 2) = _
        calc
          (a * b * c⁻¹) * (a ^ 2 * b ^ 2) =
              c⁻¹ * ((a * b) * (a ^ 2 * b ^ 2)) := by
            calc
              (a * b * c⁻¹) * (a ^ 2 * b ^ 2) =
                  (c⁻¹ * (a * b)) * (a ^ 2 * b ^ 2) := by
                rw [Subgroup.mem_center_iff.mp hcinv (a * b)]
              _ = c⁻¹ * ((a * b) * (a ^ 2 * b ^ 2)) := by simp [mul_assoc]
          _ = c⁻¹ * (a ^ 3 * b ^ 3) := by
            congr 1
            calc
              (a * b) * (a ^ 2 * b ^ 2) = (a * b) * (a * b) ^ 2 := by
                rw [hab.mul_pow]
              _ = (a * b) ^ 3 := by group
              _ = a ^ 3 * b ^ 3 := hab.mul_pow 3
          _ = a ^ 3 * b ^ 3 * c⁻¹ := by
            exact (Subgroup.mem_center_iff.mp hcinv (a ^ 3 * b ^ 3)).symm
  have hrel : c ^ 3 * b⁻¹ ^ 3 * a⁻¹ = a ^ 3 * b ^ 3 * c⁻¹ :=
    hd_cube_center.symm.trans hd_cube_direct
  let : CommGroup (Subgroup.center G) := {
    mul_comm := fun u v => Subtype.ext
      (Subgroup.mem_center_iff.mp u.2 v.1).symm }
  let aa : Subgroup.center G := ⟨a, ha⟩
  let bb : Subgroup.center G := ⟨b, hb⟩
  let cc : Subgroup.center G := ⟨c, hc⟩
  have hrel' : cc ^ 3 * bb⁻¹ ^ 3 * aa⁻¹ = aa ^ 3 * bb ^ 3 * cc⁻¹ := by
    exact Subtype.ext hrel
  have hcenterEq : aa ^ 4 * bb ^ 6 = cc ^ 4 := by
    calc
      aa ^ 4 * bb ^ 6 =
          (aa ^ 3 * bb ^ 3 * cc⁻¹) * (aa * bb ^ 3 * cc) := by
        symm
        calc
          (aa ^ 3 * bb ^ 3 * cc⁻¹) * (aa * bb ^ 3 * cc) =
              (aa ^ 4 * bb ^ 6) * (cc⁻¹ * cc) := by
            simp only [pow_succ, pow_zero]
            ac_rfl
          _ = aa ^ 4 * bb ^ 6 := by simp
      _ = (cc ^ 3 * bb⁻¹ ^ 3 * aa⁻¹) * (aa * bb ^ 3 * cc) := by
        rw [← hrel']
      _ = cc ^ 4 := by
        calc
          (cc ^ 3 * bb⁻¹ ^ 3 * aa⁻¹) * (aa * bb ^ 3 * cc) =
              cc ^ 4 * (aa⁻¹ * aa) * (bb⁻¹ * bb) ^ 3 := by
            simp only [pow_succ, pow_zero]
            ac_rfl
          _ = cc ^ 4 := by simp
  exact congrArg Subtype.val hcenterEq

public theorem commutator_sq_eq_one_of_sq_mem_center
    {G : Type*} [Group G] {u v : G}
    (hu_sq : u * u ∈ Subgroup.center G)
    (hz : ⁅u, v⁆ ∈ Subgroup.center G) :
    ⁅u, v⁆ ^ 2 = 1 := by
  have hsq_comm : Commute (u * u) v :=
    (Subgroup.mem_center_iff.mp hu_sq v).symm
  have hconj : u * ⁅u, v⁆ * u⁻¹ = ⁅u, v⁆ := by
    rw [Subgroup.mem_center_iff.mp hz u, mul_inv_cancel_right]
  have hcomm := hsq_comm.commutator_eq
  rw [commutatorElement_mul_left_eq_conj_mul, hconj] at hcomm
  simpa [pow_two] using hcomm

public theorem exceptional_far_commutator_relation
    {G : Type*} [Group G] (x y z : G)
    (hx : x ^ 3 ∈ Subgroup.center G)
    (hy : y ^ 2 ∈ Subgroup.center G)
    (hz : z ^ 2 ∈ Subgroup.center G)
    (hxy : (x * y) ^ 3 ∈ Subgroup.center G)
    (hxz : (x * z) ^ 2 ∈ Subgroup.center G)
    (hyw : ⁅y, z⁆ ∈ Subgroup.center G) :
    ⁅y, z⁆ = ((x * y) ^ 3) ^ 2 * (x ^ 3)⁻¹ ^ 2 * (y ^ 2)⁻¹ ^ 3 := by
  let a := x ^ 3
  let b := y ^ 2
  let c := (x * y) ^ 3
  let d := z ^ 2
  let e := (x * z) ^ 2
  let __ch5_Theorem523Suzuki_w := ⁅y, z⁆
  have ha : a ∈ Subgroup.center G := hx
  have hb : b ∈ Subgroup.center G := hy
  have hc : c ∈ Subgroup.center G := hxy
  have hd : d ∈ Subgroup.center G := hz
  have he : e ∈ Subgroup.center G := hxz
  have hw : __ch5_Theorem523Suzuki_w ∈ Subgroup.center G := hyw
  have hbinv : b⁻¹ ∈ Subgroup.center G := (Subgroup.center G).inv_mem hb
  have hdinv : d⁻¹ ∈ Subgroup.center G := (Subgroup.center G).inv_mem hd
  have hw2 : __ch5_Theorem523Suzuki_w ^ 2 = 1 := by
    apply commutator_sq_eq_one_of_sq_mem_center
    · simpa [pow_two] using hy
    · exact hyw
  have hzx_sq : (z * x) ^ 2 = e := by
    calc
      (z * x) ^ 2 = (z * (x * z) * z⁻¹) ^ 2 := by
        congr 1
        group
      _ = z * (x * z) ^ 2 * z⁻¹ := by rw [conj_pow]
      _ = e := by
        change z * e * z⁻¹ = e
        rw [Subgroup.mem_center_iff.mp he z]
        simp
  have he_cancel : e * x⁻¹ * z⁻¹ = z * x := by
    calc
      e * x⁻¹ * z⁻¹ = e * (x⁻¹ * z⁻¹) := by simp [mul_assoc]
      _ = e * (z * x)⁻¹ := by rw [mul_inv_rev]
      _ = e * ((z * x) * e⁻¹) := by rw [inv_eq_mul_inv_sq, hzx_sq]
      _ = z * x := by
        calc
          e * ((z * x) * e⁻¹) = (e * (z * x)) * e⁻¹ := by simp [mul_assoc]
          _ = ((z * x) * e) * e⁻¹ := by
            rw [Subgroup.mem_center_iff.mp he (z * x)]
          _ = z * x := by simp [mul_assoc]
  have hyz : y * z = __ch5_Theorem523Suzuki_w * z * y := by
    dsimp [__ch5_Theorem523Suzuki_w, commutatorElement]
    group
  have hzconj : z⁻¹ * y * z = y * __ch5_Theorem523Suzuki_w := by
    calc
      z⁻¹ * y * z = z⁻¹ * (y * z) := by simp [mul_assoc]
      _ = z⁻¹ * (__ch5_Theorem523Suzuki_w * z * y) := by rw [hyz]
      _ = __ch5_Theorem523Suzuki_w * y := by
        calc
          z⁻¹ * (__ch5_Theorem523Suzuki_w * z * y) = (z⁻¹ * __ch5_Theorem523Suzuki_w) * (z * y) := by simp [mul_assoc]
          _ = (__ch5_Theorem523Suzuki_w * z⁻¹) * (z * y) := by
            rw [Subgroup.mem_center_iff.mp hw z⁻¹]
          _ = __ch5_Theorem523Suzuki_w * y := by simp [mul_assoc]
      _ = y * __ch5_Theorem523Suzuki_w := (Subgroup.mem_center_iff.mp hw y).symm
  have hroot : z * (x * y) * z⁻¹ =
      y * (x * y)⁻¹ * y⁻¹ * (b * e * __ch5_Theorem523Suzuki_w * d⁻¹) := by
    calc
      z * (x * y) * z⁻¹ = (z * x) * y * z⁻¹ := by simp [mul_assoc]
      _ = (e * x⁻¹ * z⁻¹) * y * z * d⁻¹ := by
        rw [he_cancel]
        dsimp [d]
        group
      _ = e * x⁻¹ * (z⁻¹ * y * z) * d⁻¹ := by simp [mul_assoc]
      _ = e * x⁻¹ * (y * __ch5_Theorem523Suzuki_w) * d⁻¹ := by rw [hzconj]
      _ = y * (x * y)⁻¹ * y⁻¹ * (b * e * __ch5_Theorem523Suzuki_w * d⁻¹) := by
        dsimp [b]
        let m := e * __ch5_Theorem523Suzuki_w * d⁻¹
        have hm' : m ∈ Subgroup.center G :=
          (Subgroup.center G).mul_mem
            ((Subgroup.center G).mul_mem he hw) hdinv
        have hleft : e * x⁻¹ * (y * __ch5_Theorem523Suzuki_w) * d⁻¹ = x⁻¹ * y * m := by
          dsimp [m]
          calc
            e * x⁻¹ * (y * __ch5_Theorem523Suzuki_w) * d⁻¹ = x⁻¹ * (e * (y * __ch5_Theorem523Suzuki_w) * d⁻¹) := by
              calc
                e * x⁻¹ * (y * __ch5_Theorem523Suzuki_w) * d⁻¹ = (e * x⁻¹) * ((y * __ch5_Theorem523Suzuki_w) * d⁻¹) := by
                  simp [mul_assoc]
                _ = (x⁻¹ * e) * ((y * __ch5_Theorem523Suzuki_w) * d⁻¹) := by
                  rw [(Subgroup.mem_center_iff.mp he x⁻¹).symm]
                _ = x⁻¹ * (e * (y * __ch5_Theorem523Suzuki_w) * d⁻¹) := by simp [mul_assoc]
            _ = x⁻¹ * (y * (e * __ch5_Theorem523Suzuki_w * d⁻¹)) := by
              congr 1
              calc
                e * (y * __ch5_Theorem523Suzuki_w) * d⁻¹ = (e * y) * (__ch5_Theorem523Suzuki_w * d⁻¹) := by simp [mul_assoc]
                _ = (y * e) * (__ch5_Theorem523Suzuki_w * d⁻¹) := by
                  rw [(Subgroup.mem_center_iff.mp he y).symm]
                _ = y * (e * __ch5_Theorem523Suzuki_w * d⁻¹) := by simp [mul_assoc]
            _ = x⁻¹ * y * (e * __ch5_Theorem523Suzuki_w * d⁻¹) := by simp [mul_assoc]
        have hcore : y * (x * y)⁻¹ * y⁻¹ * y ^ 2 = x⁻¹ * y := by group
        calc
          e * x⁻¹ * (y * __ch5_Theorem523Suzuki_w) * d⁻¹ = x⁻¹ * y * m := hleft
          _ = (y * (x * y)⁻¹ * y⁻¹ * y ^ 2) * m := by rw [hcore]
          _ = y * (x * y)⁻¹ * y⁻¹ * (y ^ 2 * e * __ch5_Theorem523Suzuki_w * d⁻¹) := by
            dsimp [m]
            simp [mul_assoc]
  have ht_cube : (y * (x * y)⁻¹ * y⁻¹) ^ 3 = c⁻¹ := by
    calc
      (y * (x * y)⁻¹ * y⁻¹) ^ 3 = y * ((x * y)⁻¹) ^ 3 * y⁻¹ := by
        rw [conj_pow]
      _ = y * c⁻¹ * y⁻¹ := by rw [inv_pow]
      _ = c⁻¹ := by
        have hcinv : c⁻¹ ∈ Subgroup.center G := (Subgroup.center G).inv_mem hc
        rw [Subgroup.mem_center_iff.mp hcinv y]
        simp
  have hm : b * e * __ch5_Theorem523Suzuki_w * d⁻¹ ∈ Subgroup.center G :=
    (Subgroup.center G).mul_mem
      ((Subgroup.center G).mul_mem ((Subgroup.center G).mul_mem hb he) hw) hdinv
  have hcube : c = c⁻¹ * (b * e * __ch5_Theorem523Suzuki_w * d⁻¹) ^ 3 := by
    calc
      c = (x * y) ^ 3 := by simp [c]
      _ = (z * (x * y) * z⁻¹) ^ 3 := by
        symm
        rw [conj_pow]
        rw [Subgroup.mem_center_iff.mp hxy z]
        simp
      _ = (y * (x * y)⁻¹ * y⁻¹ * (b * e * __ch5_Theorem523Suzuki_w * d⁻¹)) ^ 3 := by rw [hroot]
      _ = (y * (x * y)⁻¹ * y⁻¹) ^ 3 * (b * e * __ch5_Theorem523Suzuki_w * d⁻¹) ^ 3 := by
        have hcomm : Commute (y * (x * y)⁻¹ * y⁻¹) (b * e * __ch5_Theorem523Suzuki_w * d⁻¹) := by
          change (y * (x * y)⁻¹ * y⁻¹) * (b * e * __ch5_Theorem523Suzuki_w * d⁻¹) =
            (b * e * __ch5_Theorem523Suzuki_w * d⁻¹) * (y * (x * y)⁻¹ * y⁻¹)
          exact Subgroup.mem_center_iff.mp hm (y * (x * y)⁻¹ * y⁻¹)
        rw [hcomm.mul_pow]
      _ = c⁻¹ * (b * e * __ch5_Theorem523Suzuki_w * d⁻¹) ^ 3 := by rw [ht_cube]
  have hfar : a ^ 2 * d ^ 3 = e ^ 3 := by
    exact cube_defect_root_far x z hx hz hxz
  let : CommGroup (Subgroup.center G) := {
    mul_comm := fun u v => Subtype.ext
      (Subgroup.mem_center_iff.mp u.2 v.1).symm }
  let aa : Subgroup.center G := ⟨a, ha⟩
  let bb : Subgroup.center G := ⟨b, hb⟩
  let cc : Subgroup.center G := ⟨c, hc⟩
  let dd : Subgroup.center G := ⟨d, hd⟩
  let ee : Subgroup.center G := ⟨e, he⟩
  let ww : Subgroup.center G := ⟨__ch5_Theorem523Suzuki_w, hw⟩
  have hw2' : ww ^ 2 = 1 := Subtype.ext hw2
  have hcube' : cc = cc⁻¹ * (bb * ee * ww * dd⁻¹) ^ 3 := Subtype.ext hcube
  have hfar' : aa ^ 2 * dd ^ 3 = ee ^ 3 := Subtype.ext hfar
  have hcc2 : cc ^ 2 = aa ^ 2 * bb ^ 3 * ww := by
    calc
      cc ^ 2 = (bb * ee * ww * dd⁻¹) ^ 3 := by
        rw [pow_two]
        nth_rw 2 [hcube']
        simp
      _ = bb ^ 3 * ee ^ 3 * ww ^ 3 * (dd⁻¹) ^ 3 := by
        simp only [pow_succ, pow_zero]
        ac_rfl
      _ = bb ^ 3 * (aa ^ 2 * dd ^ 3) * ww ^ 3 * (dd⁻¹) ^ 3 := by
        rw [hfar']
      _ = aa ^ 2 * bb ^ 3 * ww := by
        have hww3 : ww ^ 3 = ww := by
          calc ww ^ 3 = ww ^ 2 * ww := by group
          _ = ww := by rw [hw2']; simp
        rw [hww3]
        calc
          bb ^ 3 * (aa ^ 2 * dd ^ 3) * ww * (dd⁻¹) ^ 3 =
              aa ^ 2 * bb ^ 3 * ww * (dd⁻¹ * dd) ^ 3 := by
            simp only [pow_succ, pow_zero]
            ac_rfl
          _ = aa ^ 2 * bb ^ 3 * ww := by simp
  have hresult : ww = cc ^ 2 * aa⁻¹ ^ 2 * bb⁻¹ ^ 3 := by
    calc
      ww = (aa ^ 2 * bb ^ 3 * ww) * aa⁻¹ ^ 2 * bb⁻¹ ^ 3 := by
        symm
        calc
          (aa ^ 2 * bb ^ 3 * ww) * aa⁻¹ ^ 2 * bb⁻¹ ^ 3 =
              ww * (aa⁻¹ * aa) ^ 2 * (bb⁻¹ * bb) ^ 3 := by
            simp only [pow_succ, pow_zero]
            ac_rfl
          _ = ww := by simp
      _ = cc ^ 2 * aa⁻¹ ^ 2 * bb⁻¹ ^ 3 := by rw [← hcc2]
  exact congrArg Subtype.val hresult


public abbrev A6FreeCentral := AlternatingFreeCentralGroup 1

@[expose]
public def a6FCGen (i : Fin 4) : A6FreeCentral :=
  QuotientGroup.mk' (FreeCentralExtension.freeCentralKernel
    (alternatingSuzukiKernel 1)) (FreeGroup.of i)

@[simp]
public theorem alternatingFreeCentralProjection_a6FCGen (i : Fin 4) :
    alternatingFreeCentralProjection 1 (a6FCGen i) =
      alternatingSuzukiGenerator 1 i := by
  rfl

@[expose]
public def a6u1 : A6FreeCentral := a6FCGen 0 ^ 3
@[expose]
public def a6u2 : A6FreeCentral := a6FCGen 1 ^ 2
@[expose]
public def a6u3 : A6FreeCentral := a6FCGen 2 ^ 2
@[expose]
public def a6u4 : A6FreeCentral := a6FCGen 3 ^ 2
@[expose]
public def a6v1 : A6FreeCentral := (a6FCGen 0 * a6FCGen 1) ^ 3
@[expose]
public def a6v2 : A6FreeCentral := (a6FCGen 1 * a6FCGen 2) ^ 3
@[expose]
public def a6v3 : A6FreeCentral := (a6FCGen 2 * a6FCGen 3) ^ 3
@[expose]
public def a6w3 : A6FreeCentral := (a6FCGen 0 * a6FCGen 2) ^ 2
@[expose]
public def a6w4 : A6FreeCentral := (a6FCGen 0 * a6FCGen 3) ^ 2
@[expose]
public def a6w : A6FreeCentral := ⁅a6FCGen 1, a6FCGen 3⁆

public theorem a6RelatorDefect_mem_ker (r : SuzukiRelator 1) :
    QuotientGroup.mk' (FreeCentralExtension.freeCentralKernel
        (alternatingSuzukiKernel 1)) r.word ∈
      (alternatingFreeCentralProjection 1).ker := by
  rw [MonoidHom.mem_ker]
  change alternatingSuzukiMap 1 r.word = 1
  exact SuzukiRelator.lift_alternatingSuzukiGenerator_eq_one r

public theorem a6RelatorDefect_mem_center (r : SuzukiRelator 1) :
    QuotientGroup.mk' (FreeCentralExtension.freeCentralKernel
        (alternatingSuzukiKernel 1)) r.word ∈
      Subgroup.center A6FreeCentral :=
  alternatingFreeCentralProjection_ker_le_center 1 (a6RelatorDefect_mem_ker r)

public theorem a6u1_mem_center : a6u1 ∈ Subgroup.center A6FreeCentral := by
  simpa [a6u1, a6FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
    a6RelatorDefect_mem_center (SuzukiRelator.rootCube : SuzukiRelator 1)

public theorem a6u2_mem_center : a6u2 ∈ Subgroup.center A6FreeCentral := by
  simpa [a6u2, a6FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
    a6RelatorDefect_mem_center
      (SuzukiRelator.tailSquare (1 : Fin 4) (by decide) : SuzukiRelator 1)

public theorem a6u3_mem_center : a6u3 ∈ Subgroup.center A6FreeCentral := by
  simpa [a6u3, a6FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
    a6RelatorDefect_mem_center
      (SuzukiRelator.tailSquare (2 : Fin 4) (by decide) : SuzukiRelator 1)

public theorem a6u4_mem_center : a6u4 ∈ Subgroup.center A6FreeCentral := by
  simpa [a6u4, a6FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
    a6RelatorDefect_mem_center
      (SuzukiRelator.tailSquare (3 : Fin 4) (by decide) : SuzukiRelator 1)

public theorem a6v1_mem_center : a6v1 ∈ Subgroup.center A6FreeCentral := by
  simpa [a6v1, a6FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
    a6RelatorDefect_mem_center
      (SuzukiRelator.rootAdjacentCube : SuzukiRelator 1)

public theorem a6v2_mem_center : a6v2 ∈ Subgroup.center A6FreeCentral := by
  simpa [a6v2, a6FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
    a6RelatorDefect_mem_center
      (SuzukiRelator.tailAdjacentCube (1 : Fin 3) (by decide) : SuzukiRelator 1)

public theorem a6v3_mem_center : a6v3 ∈ Subgroup.center A6FreeCentral := by
  simpa [a6v3, a6FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
    a6RelatorDefect_mem_center
      (SuzukiRelator.tailAdjacentCube (2 : Fin 3) (by decide) : SuzukiRelator 1)

public theorem a6w3_mem_center : a6w3 ∈ Subgroup.center A6FreeCentral := by
  simpa [a6w3, a6FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
    a6RelatorDefect_mem_center
      (SuzukiRelator.rootFarSquare (2 : Fin 4) (by decide) : SuzukiRelator 1)

public theorem a6w4_mem_center : a6w4 ∈ Subgroup.center A6FreeCentral := by
  simpa [a6w4, a6FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
    a6RelatorDefect_mem_center
      (SuzukiRelator.rootFarSquare (3 : Fin 4) (by decide) : SuzukiRelator 1)

public theorem a6w_mem_center : a6w ∈ Subgroup.center A6FreeCentral := by
  simpa [a6w, a6FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
    a6RelatorDefect_mem_center
      (SuzukiRelator.tailFarCommutator (1 : Fin 4) (3 : Fin 4)
        (by decide) (by decide) (by norm_num) : SuzukiRelator 1)

public theorem a6w_sq : a6w ^ 2 = 1 := by
  apply commutator_sq_eq_one_of_sq_mem_center
      (u := a6FCGen 1) (v := a6FCGen 3)
  · simpa [a6u2, pow_two] using a6u2_mem_center
  · simpa [a6w] using a6w_mem_center

public theorem a6v2_sq : a6v2 ^ 2 = (a6u2 * a6u3) ^ 3 := by
  simpa [a6v2, a6u2, a6u3] using
    sq_defect_adjacent (a6FCGen 1) (a6FCGen 2)
      a6u2_mem_center a6u3_mem_center a6v2_mem_center

public theorem a6v3_sq : a6v3 ^ 2 = (a6u3 * a6u4) ^ 3 := by
  simpa [a6v3, a6u3, a6u4] using
    sq_defect_adjacent (a6FCGen 2) (a6FCGen 3)
      a6u3_mem_center a6u4_mem_center a6v3_mem_center

public theorem a6u1_u3_w3_relation :
    a6u1 ^ 2 * a6u3 ^ 3 = a6w3 ^ 3 := by
  simpa [a6u1, a6u3, a6w3] using
    cube_defect_root_far (a6FCGen 0) (a6FCGen 2)
      a6u1_mem_center a6u3_mem_center a6w3_mem_center

public theorem a6u1_u4_w4_relation :
    a6u1 ^ 2 * a6u4 ^ 3 = a6w4 ^ 3 := by
  simpa [a6u1, a6u4, a6w4] using
    cube_defect_root_far (a6FCGen 0) (a6FCGen 3)
      a6u1_mem_center a6u4_mem_center a6w4_mem_center

public theorem a6w_relation :
    a6w = a6v1 ^ 2 * (a6u1⁻¹) ^ 2 * (a6u2⁻¹) ^ 3 := by
  simpa [a6u1, a6u2, a6u4, a6v1, a6w4, a6w] using
    exceptional_far_commutator_relation
      (a6FCGen 0) (a6FCGen 1) (a6FCGen 3)
      a6u1_mem_center a6u2_mem_center a6u4_mem_center
      a6v1_mem_center a6w4_mem_center a6w_mem_center

public theorem cubeSquareGenerator {A : Type*} [CommGroup A]
    (x y : A) (h : y ^ 2 = x ^ 3) :
    (y * x⁻¹) ^ 2 = x ∧ (y * x⁻¹) ^ 3 = y := by
  constructor
  · rw [mul_pow, h]
    group
  · rw [mul_pow]
    nth_rw 1 [show y ^ 3 = y * y ^ 2 by group]
    rw [h]
    group

@[expose]
public def a6t3 : A6FreeCentral := a6w3 * a6u3⁻¹
@[expose]
public def a6t4 : A6FreeCentral := a6w4 * a6u4⁻¹
@[expose]
public def a6A : A6FreeCentral := a6v1 * a6u1⁻¹
@[expose]
public def a6B : A6FreeCentral := a6w * a6u2

@[expose]
public def a6z1 : A6FreeCentral := a6u1 * a6t3⁻¹
@[expose]
public def a6z2 : A6FreeCentral := a6A * a6B⁻¹
@[expose]
public def a6z3 : A6FreeCentral := a6v2 * (a6u2 * a6u3)⁻¹
@[expose]
public def a6z4 : A6FreeCentral := a6v3 * (a6u3 * a6u4)⁻¹
@[expose]
public def a6k : A6FreeCentral := a6w * a6t4 * a6t3⁻¹

public theorem a6t3_mem_center : a6t3 ∈ Subgroup.center A6FreeCentral :=
  (Subgroup.center A6FreeCentral).mul_mem a6w3_mem_center
    ((Subgroup.center A6FreeCentral).inv_mem a6u3_mem_center)

public theorem a6t4_mem_center : a6t4 ∈ Subgroup.center A6FreeCentral :=
  (Subgroup.center A6FreeCentral).mul_mem a6w4_mem_center
    ((Subgroup.center A6FreeCentral).inv_mem a6u4_mem_center)

public theorem a6A_mem_center : a6A ∈ Subgroup.center A6FreeCentral :=
  (Subgroup.center A6FreeCentral).mul_mem a6v1_mem_center
    ((Subgroup.center A6FreeCentral).inv_mem a6u1_mem_center)

public theorem a6B_mem_center : a6B ∈ Subgroup.center A6FreeCentral :=
  (Subgroup.center A6FreeCentral).mul_mem a6w_mem_center a6u2_mem_center

public theorem a6z1_mem_center : a6z1 ∈ Subgroup.center A6FreeCentral :=
  (Subgroup.center A6FreeCentral).mul_mem a6u1_mem_center
    ((Subgroup.center A6FreeCentral).inv_mem a6t3_mem_center)

public theorem a6z2_mem_center : a6z2 ∈ Subgroup.center A6FreeCentral :=
  (Subgroup.center A6FreeCentral).mul_mem a6A_mem_center
    ((Subgroup.center A6FreeCentral).inv_mem a6B_mem_center)

public theorem a6z3_mem_center : a6z3 ∈ Subgroup.center A6FreeCentral :=
  (Subgroup.center A6FreeCentral).mul_mem a6v2_mem_center
    ((Subgroup.center A6FreeCentral).inv_mem
      ((Subgroup.center A6FreeCentral).mul_mem a6u2_mem_center a6u3_mem_center))

public theorem a6z4_mem_center : a6z4 ∈ Subgroup.center A6FreeCentral :=
  (Subgroup.center A6FreeCentral).mul_mem a6v3_mem_center
    ((Subgroup.center A6FreeCentral).inv_mem
      ((Subgroup.center A6FreeCentral).mul_mem a6u3_mem_center a6u4_mem_center))

public theorem a6k_mem_center : a6k ∈ Subgroup.center A6FreeCentral :=
  (Subgroup.center A6FreeCentral).mul_mem
    ((Subgroup.center A6FreeCentral).mul_mem a6w_mem_center a6t4_mem_center)
    ((Subgroup.center A6FreeCentral).inv_mem a6t3_mem_center)

public theorem a6u1_sq_eq_t3_cube : a6u1 ^ 2 = a6t3 ^ 3 := by
  let : CommGroup (Subgroup.center A6FreeCentral) := {
    mul_comm := fun u v => Subtype.ext
      (Subgroup.mem_center_iff.mp u.2 v.1).symm }
  let U1 : Subgroup.center A6FreeCentral := ⟨a6u1, a6u1_mem_center⟩
  let U3 : Subgroup.center A6FreeCentral := ⟨a6u3, a6u3_mem_center⟩
  let W3 : Subgroup.center A6FreeCentral := ⟨a6w3, a6w3_mem_center⟩
  let T3 : Subgroup.center A6FreeCentral := ⟨a6t3, a6t3_mem_center⟩
  have h : U1 ^ 2 * U3 ^ 3 = W3 ^ 3 := Subtype.ext a6u1_u3_w3_relation
  have hT : U1 ^ 2 = T3 ^ 3 := by
    dsimp [T3, a6t3]
    calc
      U1 ^ 2 = W3 ^ 3 * (U3 ^ 3)⁻¹ := by rw [← h]; group
      _ = (W3 * U3⁻¹) ^ 3 := by simp [mul_pow]
  exact congrArg Subtype.val hT

public theorem a6u1_sq_eq_t4_cube : a6u1 ^ 2 = a6t4 ^ 3 := by
  let : CommGroup (Subgroup.center A6FreeCentral) := {
    mul_comm := fun u v => Subtype.ext
      (Subgroup.mem_center_iff.mp u.2 v.1).symm }
  let U1 : Subgroup.center A6FreeCentral := ⟨a6u1, a6u1_mem_center⟩
  let U4 : Subgroup.center A6FreeCentral := ⟨a6u4, a6u4_mem_center⟩
  let W4 : Subgroup.center A6FreeCentral := ⟨a6w4, a6w4_mem_center⟩
  let T4 : Subgroup.center A6FreeCentral := ⟨a6t4, a6t4_mem_center⟩
  have h : U1 ^ 2 * U4 ^ 3 = W4 ^ 3 := Subtype.ext a6u1_u4_w4_relation
  have hT : U1 ^ 2 = T4 ^ 3 := by
    dsimp [T4, a6t4]
    calc
      U1 ^ 2 = W4 ^ 3 * (U4 ^ 3)⁻¹ := by rw [← h]; group
      _ = (W4 * U4⁻¹) ^ 3 := by simp [mul_pow]
  exact congrArg Subtype.val hT

public theorem a6A_sq_eq_B_cube : a6A ^ 2 = a6B ^ 3 := by
  let : CommGroup (Subgroup.center A6FreeCentral) := {
    mul_comm := fun u v => Subtype.ext
      (Subgroup.mem_center_iff.mp u.2 v.1).symm }
  let U1 : Subgroup.center A6FreeCentral := ⟨a6u1, a6u1_mem_center⟩
  let U2 : Subgroup.center A6FreeCentral := ⟨a6u2, a6u2_mem_center⟩
  let V1 : Subgroup.center A6FreeCentral := ⟨a6v1, a6v1_mem_center⟩
  let W : Subgroup.center A6FreeCentral := ⟨a6w, a6w_mem_center⟩
  let A : Subgroup.center A6FreeCentral := ⟨a6A, a6A_mem_center⟩
  let B : Subgroup.center A6FreeCentral := ⟨a6B, a6B_mem_center⟩
  have hw : W = V1 ^ 2 * U1⁻¹ ^ 2 * U2⁻¹ ^ 3 := Subtype.ext a6w_relation
  have hw2 : W ^ 2 = 1 := Subtype.ext a6w_sq
  have hAB : A ^ 2 = B ^ 3 := by
    dsimp [A, B, a6A, a6B]
    calc
      (V1 * U1⁻¹) ^ 2 = V1 ^ 2 * U1⁻¹ ^ 2 := by rw [mul_pow]
      _ = W * U2 ^ 3 := by rw [hw]; group
      _ = W ^ 3 * U2 ^ 3 := by
        rw [show W ^ 3 = W by
          calc
            W ^ 3 = W ^ 2 * W := by group
            _ = W := by rw [hw2]; simp]
      _ = (W * U2) ^ 3 := by rw [mul_pow]
  exact congrArg Subtype.val hAB

public theorem a6z1_sq : a6z1 ^ 2 = a6t3 := by
  let : CommGroup (Subgroup.center A6FreeCentral) := {
    mul_comm := fun u v => Subtype.ext
      (Subgroup.mem_center_iff.mp u.2 v.1).symm }
  let T3 : Subgroup.center A6FreeCentral := ⟨a6t3, a6t3_mem_center⟩
  let U1 : Subgroup.center A6FreeCentral := ⟨a6u1, a6u1_mem_center⟩
  have h : U1 ^ 2 = T3 ^ 3 := Subtype.ext a6u1_sq_eq_t3_cube
  exact congrArg Subtype.val (cubeSquareGenerator T3 U1 h).1

public theorem a6z1_cube : a6z1 ^ 3 = a6u1 := by
  let : CommGroup (Subgroup.center A6FreeCentral) := {
    mul_comm := fun u v => Subtype.ext
      (Subgroup.mem_center_iff.mp u.2 v.1).symm }
  let T3 : Subgroup.center A6FreeCentral := ⟨a6t3, a6t3_mem_center⟩
  let U1 : Subgroup.center A6FreeCentral := ⟨a6u1, a6u1_mem_center⟩
  have h : U1 ^ 2 = T3 ^ 3 := Subtype.ext a6u1_sq_eq_t3_cube
  exact congrArg Subtype.val (cubeSquareGenerator T3 U1 h).2

public theorem a6z2_sq : a6z2 ^ 2 = a6B := by
  let : CommGroup (Subgroup.center A6FreeCentral) := {
    mul_comm := fun u v => Subtype.ext
      (Subgroup.mem_center_iff.mp u.2 v.1).symm }
  let B : Subgroup.center A6FreeCentral := ⟨a6B, a6B_mem_center⟩
  let A : Subgroup.center A6FreeCentral := ⟨a6A, a6A_mem_center⟩
  have h : A ^ 2 = B ^ 3 := Subtype.ext a6A_sq_eq_B_cube
  exact congrArg Subtype.val (cubeSquareGenerator B A h).1

public theorem a6z2_cube : a6z2 ^ 3 = a6A := by
  let : CommGroup (Subgroup.center A6FreeCentral) := {
    mul_comm := fun u v => Subtype.ext
      (Subgroup.mem_center_iff.mp u.2 v.1).symm }
  let B : Subgroup.center A6FreeCentral := ⟨a6B, a6B_mem_center⟩
  let A : Subgroup.center A6FreeCentral := ⟨a6A, a6A_mem_center⟩
  have h : A ^ 2 = B ^ 3 := Subtype.ext a6A_sq_eq_B_cube
  exact congrArg Subtype.val (cubeSquareGenerator B A h).2

public theorem a6z3_sq : a6z3 ^ 2 = a6u2 * a6u3 := by
  let : CommGroup (Subgroup.center A6FreeCentral) := {
    mul_comm := fun u v => Subtype.ext
      (Subgroup.mem_center_iff.mp u.2 v.1).symm }
  let X : Subgroup.center A6FreeCentral :=
    ⟨a6u2 * a6u3, (Subgroup.center A6FreeCentral).mul_mem
      a6u2_mem_center a6u3_mem_center⟩
  let Y : Subgroup.center A6FreeCentral := ⟨a6v2, a6v2_mem_center⟩
  have h : Y ^ 2 = X ^ 3 := Subtype.ext a6v2_sq
  exact congrArg Subtype.val (cubeSquareGenerator X Y h).1

public theorem a6z3_cube : a6z3 ^ 3 = a6v2 := by
  let : CommGroup (Subgroup.center A6FreeCentral) := {
    mul_comm := fun u v => Subtype.ext
      (Subgroup.mem_center_iff.mp u.2 v.1).symm }
  let X : Subgroup.center A6FreeCentral :=
    ⟨a6u2 * a6u3, (Subgroup.center A6FreeCentral).mul_mem
      a6u2_mem_center a6u3_mem_center⟩
  let Y : Subgroup.center A6FreeCentral := ⟨a6v2, a6v2_mem_center⟩
  have h : Y ^ 2 = X ^ 3 := Subtype.ext a6v2_sq
  exact congrArg Subtype.val (cubeSquareGenerator X Y h).2

public theorem a6z4_sq : a6z4 ^ 2 = a6u3 * a6u4 := by
  let : CommGroup (Subgroup.center A6FreeCentral) := {
    mul_comm := fun u v => Subtype.ext
      (Subgroup.mem_center_iff.mp u.2 v.1).symm }
  let X : Subgroup.center A6FreeCentral :=
    ⟨a6u3 * a6u4, (Subgroup.center A6FreeCentral).mul_mem
      a6u3_mem_center a6u4_mem_center⟩
  let Y : Subgroup.center A6FreeCentral := ⟨a6v3, a6v3_mem_center⟩
  have h : Y ^ 2 = X ^ 3 := Subtype.ext a6v3_sq
  exact congrArg Subtype.val (cubeSquareGenerator X Y h).1

public theorem a6z4_cube : a6z4 ^ 3 = a6v3 := by
  let : CommGroup (Subgroup.center A6FreeCentral) := {
    mul_comm := fun u v => Subtype.ext
      (Subgroup.mem_center_iff.mp u.2 v.1).symm }
  let X : Subgroup.center A6FreeCentral :=
    ⟨a6u3 * a6u4, (Subgroup.center A6FreeCentral).mul_mem
      a6u3_mem_center a6u4_mem_center⟩
  let Y : Subgroup.center A6FreeCentral := ⟨a6v3, a6v3_mem_center⟩
  have h : Y ^ 2 = X ^ 3 := Subtype.ext a6v3_sq
  exact congrArg Subtype.val (cubeSquareGenerator X Y h).2

public theorem a6k_cube : a6k ^ 3 = a6w := by
  let : CommGroup (Subgroup.center A6FreeCentral) := {
    mul_comm := fun u v => Subtype.ext
      (Subgroup.mem_center_iff.mp u.2 v.1).symm }
  let W : Subgroup.center A6FreeCentral := ⟨a6w, a6w_mem_center⟩
  let T3 : Subgroup.center A6FreeCentral := ⟨a6t3, a6t3_mem_center⟩
  let T4 : Subgroup.center A6FreeCentral := ⟨a6t4, a6t4_mem_center⟩
  let K : Subgroup.center A6FreeCentral := W * T4 * T3⁻¹
  have hw2 : W ^ 2 = 1 := Subtype.ext a6w_sq
  have ht : T3 ^ 3 = T4 ^ 3 := by
    rw [← show (⟨a6u1, a6u1_mem_center⟩ : Subgroup.center A6FreeCentral) ^ 2 =
      T3 ^ 3 from Subtype.ext a6u1_sq_eq_t3_cube,
      ← show (⟨a6u1, a6u1_mem_center⟩ : Subgroup.center A6FreeCentral) ^ 2 =
      T4 ^ 3 from Subtype.ext a6u1_sq_eq_t4_cube]
  have hK : K ^ 3 = W := by
    dsimp [K]
    rw [mul_pow, mul_pow]
    rw [inv_pow, ht]
    have hw3 : W ^ 3 = W := by
      calc
        W ^ 3 = W ^ 2 * W := by group
        _ = W := by rw [hw2]; simp
    rw [hw3]
    group
  simpa [a6k, K, W, T3, T4] using congrArg Subtype.val hK

public def a6ExceptionalCenterGenerators : Set A6FreeCentral :=
  {a6z1, a6z2, a6z3, a6z4, a6k}

public def a6ExceptionalCenter : Subgroup A6FreeCentral :=
  Subgroup.closure a6ExceptionalCenterGenerators

public theorem a6z1_mem_exceptionalCenter : a6z1 ∈ a6ExceptionalCenter :=
  Subgroup.subset_closure (by simp [a6ExceptionalCenterGenerators])

public theorem a6z2_mem_exceptionalCenter : a6z2 ∈ a6ExceptionalCenter :=
  Subgroup.subset_closure (by simp [a6ExceptionalCenterGenerators])

public theorem a6z3_mem_exceptionalCenter : a6z3 ∈ a6ExceptionalCenter :=
  Subgroup.subset_closure (by simp [a6ExceptionalCenterGenerators])

public theorem a6z4_mem_exceptionalCenter : a6z4 ∈ a6ExceptionalCenter :=
  Subgroup.subset_closure (by simp [a6ExceptionalCenterGenerators])

public theorem a6k_mem_exceptionalCenter : a6k ∈ a6ExceptionalCenter :=
  Subgroup.subset_closure (by simp [a6ExceptionalCenterGenerators])

public theorem a6ExceptionalCenter_le_center :
    a6ExceptionalCenter ≤ Subgroup.center A6FreeCentral := by
  rw [a6ExceptionalCenter, Subgroup.closure_le]
  intro x hx
  simp only [a6ExceptionalCenterGenerators, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact a6z1_mem_center
  · exact a6z2_mem_center
  · exact a6z3_mem_center
  · exact a6z4_mem_center
  · exact a6k_mem_center

public theorem a6w_mem_exceptionalCenter : a6w ∈ a6ExceptionalCenter := by
  rw [← a6k_cube]
  exact a6ExceptionalCenter.pow_mem a6k_mem_exceptionalCenter 3

public theorem a6u1_mem_exceptionalCenter : a6u1 ∈ a6ExceptionalCenter := by
  rw [← a6z1_cube]
  exact a6ExceptionalCenter.pow_mem a6z1_mem_exceptionalCenter 3

public theorem a6t3_mem_exceptionalCenter : a6t3 ∈ a6ExceptionalCenter := by
  rw [← a6z1_sq]
  exact a6ExceptionalCenter.pow_mem a6z1_mem_exceptionalCenter 2

public theorem a6B_mem_exceptionalCenter : a6B ∈ a6ExceptionalCenter := by
  rw [← a6z2_sq]
  exact a6ExceptionalCenter.pow_mem a6z2_mem_exceptionalCenter 2

public theorem a6u2_mem_exceptionalCenter : a6u2 ∈ a6ExceptionalCenter := by
  have hEq : a6u2 = a6w⁻¹ * a6B := by simp [a6B]
  rw [hEq]
  exact a6ExceptionalCenter.mul_mem
    (a6ExceptionalCenter.inv_mem a6w_mem_exceptionalCenter)
    a6B_mem_exceptionalCenter

public theorem a6u3_mem_exceptionalCenter : a6u3 ∈ a6ExceptionalCenter := by
  have hEq : a6u3 = a6u2⁻¹ * (a6u2 * a6u3) := by group
  rw [hEq, ← a6z3_sq]
  exact a6ExceptionalCenter.mul_mem
    (a6ExceptionalCenter.inv_mem a6u2_mem_exceptionalCenter)
    (a6ExceptionalCenter.pow_mem a6z3_mem_exceptionalCenter 2)

public theorem a6u4_mem_exceptionalCenter : a6u4 ∈ a6ExceptionalCenter := by
  have hEq : a6u4 = a6u3⁻¹ * (a6u3 * a6u4) := by group
  rw [hEq, ← a6z4_sq]
  exact a6ExceptionalCenter.mul_mem
    (a6ExceptionalCenter.inv_mem a6u3_mem_exceptionalCenter)
    (a6ExceptionalCenter.pow_mem a6z4_mem_exceptionalCenter 2)

public theorem a6t4_mem_exceptionalCenter : a6t4 ∈ a6ExceptionalCenter := by
  have hEq : a6t4 = a6w⁻¹ * a6k * a6t3 := by
    dsimp [a6k]
    group
  rw [hEq]
  exact a6ExceptionalCenter.mul_mem
    (a6ExceptionalCenter.mul_mem
      (a6ExceptionalCenter.inv_mem a6w_mem_exceptionalCenter)
      a6k_mem_exceptionalCenter)
    a6t3_mem_exceptionalCenter

public theorem a6w3_mem_exceptionalCenter : a6w3 ∈ a6ExceptionalCenter := by
  have hEq : a6w3 = a6t3 * a6u3 := by simp [a6t3]
  rw [hEq]
  exact a6ExceptionalCenter.mul_mem a6t3_mem_exceptionalCenter
    a6u3_mem_exceptionalCenter

public theorem a6w4_mem_exceptionalCenter : a6w4 ∈ a6ExceptionalCenter := by
  have hEq : a6w4 = a6t4 * a6u4 := by simp [a6t4]
  rw [hEq]
  exact a6ExceptionalCenter.mul_mem a6t4_mem_exceptionalCenter
    a6u4_mem_exceptionalCenter

public theorem a6A_mem_exceptionalCenter : a6A ∈ a6ExceptionalCenter := by
  rw [← a6z2_cube]
  exact a6ExceptionalCenter.pow_mem a6z2_mem_exceptionalCenter 3

public theorem a6v1_mem_exceptionalCenter : a6v1 ∈ a6ExceptionalCenter := by
  have hEq : a6v1 = a6A * a6u1 := by simp [a6A]
  rw [hEq]
  exact a6ExceptionalCenter.mul_mem a6A_mem_exceptionalCenter
    a6u1_mem_exceptionalCenter

public theorem a6v2_mem_exceptionalCenter : a6v2 ∈ a6ExceptionalCenter := by
  rw [← a6z3_cube]
  exact a6ExceptionalCenter.pow_mem a6z3_mem_exceptionalCenter 3

public theorem a6v3_mem_exceptionalCenter : a6v3 ∈ a6ExceptionalCenter := by
  rw [← a6z4_cube]
  exact a6ExceptionalCenter.pow_mem a6z4_mem_exceptionalCenter 3

public theorem a6RelatorDefect_mem_exceptionalCenter (r : SuzukiRelator 1) :
    QuotientGroup.mk' (FreeCentralExtension.freeCentralKernel
        (alternatingSuzukiKernel 1)) r.word ∈ a6ExceptionalCenter := by
  cases r with
  | rootCube =>
      simpa [a6u1, a6FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
        a6u1_mem_exceptionalCenter
  | tailSquare i hi =>
      fin_cases i
      · simp at hi
      · simpa [a6u2, a6FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
          a6u2_mem_exceptionalCenter
      · simpa [a6u3, a6FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
          a6u3_mem_exceptionalCenter
      · simpa [a6u4, a6FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
          a6u4_mem_exceptionalCenter
  | rootAdjacentCube =>
      simpa [a6v1, a6FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
        a6v1_mem_exceptionalCenter
  | tailAdjacentCube i hi =>
      fin_cases i
      · simp at hi
      · simpa [a6v2, a6FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
          a6v2_mem_exceptionalCenter
      · simpa [a6v3, a6FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
          a6v3_mem_exceptionalCenter
  | rootFarSquare j hj =>
      fin_cases j
      · norm_num at hj
      · norm_num at hj
      · simpa [a6w3, a6FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
          a6w3_mem_exceptionalCenter
      · simpa [a6w4, a6FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
          a6w4_mem_exceptionalCenter
  | tailFarCommutator i j hi hj hfar =>
      fin_cases i <;> fin_cases j <;> simp at hi hj hfar
      · simpa [a6w, a6FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
          a6w_mem_exceptionalCenter
      · change ⁅a6FCGen 3, a6FCGen 1⁆ ∈ a6ExceptionalCenter
        rw [← commutatorElement_inv]
        exact a6ExceptionalCenter.inv_mem a6w_mem_exceptionalCenter

public theorem a6FullProjection_ker_eq_exceptionalCenter :
    (alternatingFreeCentralProjection 1).ker = a6ExceptionalCenter := by
  let q : AlternatingSuzukiFreeGroup 1 →* A6FreeCentral :=
    QuotientGroup.mk' (FreeCentralExtension.freeCentralKernel
      (alternatingSuzukiKernel 1))
  have hker : (alternatingFreeCentralProjection 1).ker =
      (FreeCentralExtension.freeCentralProjection
        (alternatingSuzukiKernel 1)).ker := by
    exact MonoidHom.ker_comp_of_injective
      (FreeCentralExtension.freeCentralProjection (alternatingSuzukiKernel 1))
      (alternatingSuzukiQuotientEquiv 1).toMonoidHom
      (alternatingSuzukiQuotientEquiv 1).injective
  rw [hker, FreeCentralExtension.freeCentralProjection_ker]
  change (alternatingSuzukiKernel 1).map q = a6ExceptionalCenter
  have hmap : (alternatingSuzukiKernel 1).map q =
      (Subgroup.normalClosure (suzukiRelatorSet 1)).map q :=
    congrArg (fun H : Subgroup (AlternatingSuzukiFreeGroup 1) => H.map q)
      (alternatingSuzukiKernel_eq_normalClosure 1)
  rw [hmap, Subgroup.map_normalClosure (suzukiRelatorSet 1) q
    (QuotientGroup.mk'_surjective _)]
  apply le_antisymm
  · let : a6ExceptionalCenter.Normal := ⟨fun n hn g => by
      have hncenter := a6ExceptionalCenter_le_center hn
      have hcomm := Subgroup.mem_center_iff.mp hncenter g
      rw [hcomm]
      simpa using hn⟩
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨x, ⟨r, rfl⟩, rfl⟩
    exact a6RelatorDefect_mem_exceptionalCenter r
  · rw [a6ExceptionalCenter, Subgroup.closure_le]
    intro x hx
    let N := Subgroup.normalClosure (q '' suzukiRelatorSet 1)
    have hdefect (r : SuzukiRelator 1) : q r.word ∈ N := by
      apply Subgroup.subset_normalClosure
      exact ⟨r.word, ⟨r, rfl⟩, rfl⟩
    have hu1 : a6u1 ∈ N := by
      simpa [N, q, a6u1, a6FCGen, SuzukiRelator.word,
        suzukiFreeGenerator] using
        hdefect (SuzukiRelator.rootCube : SuzukiRelator 1)
    have hu2 : a6u2 ∈ N := by
      simpa [N, q, a6u2, a6FCGen, SuzukiRelator.word,
        suzukiFreeGenerator] using
        hdefect (SuzukiRelator.tailSquare (1 : Fin 4) (by decide) :
          SuzukiRelator 1)
    have hu3 : a6u3 ∈ N := by
      simpa [N, q, a6u3, a6FCGen, SuzukiRelator.word,
        suzukiFreeGenerator] using
        hdefect (SuzukiRelator.tailSquare (2 : Fin 4) (by decide) :
          SuzukiRelator 1)
    have hu4 : a6u4 ∈ N := by
      simpa [N, q, a6u4, a6FCGen, SuzukiRelator.word,
        suzukiFreeGenerator] using
        hdefect (SuzukiRelator.tailSquare (3 : Fin 4) (by decide) :
          SuzukiRelator 1)
    have hv1 : a6v1 ∈ N := by
      simpa [N, q, a6v1, a6FCGen, SuzukiRelator.word,
        suzukiFreeGenerator] using
        hdefect (SuzukiRelator.rootAdjacentCube : SuzukiRelator 1)
    have hv2 : a6v2 ∈ N := by
      simpa [N, q, a6v2, a6FCGen, SuzukiRelator.word,
        suzukiFreeGenerator] using
        hdefect (SuzukiRelator.tailAdjacentCube (1 : Fin 3) (by decide) :
          SuzukiRelator 1)
    have hv3 : a6v3 ∈ N := by
      simpa [N, q, a6v3, a6FCGen, SuzukiRelator.word,
        suzukiFreeGenerator] using
        hdefect (SuzukiRelator.tailAdjacentCube (2 : Fin 3) (by decide) :
          SuzukiRelator 1)
    have hw3 : a6w3 ∈ N := by
      simpa [N, q, a6w3, a6FCGen, SuzukiRelator.word,
        suzukiFreeGenerator] using
        hdefect (SuzukiRelator.rootFarSquare (2 : Fin 4) (by decide) :
          SuzukiRelator 1)
    have hw4 : a6w4 ∈ N := by
      simpa [N, q, a6w4, a6FCGen, SuzukiRelator.word,
        suzukiFreeGenerator] using
        hdefect (SuzukiRelator.rootFarSquare (3 : Fin 4) (by decide) :
          SuzukiRelator 1)
    have hw : a6w ∈ N := by
      simpa [N, q, a6w, a6FCGen, SuzukiRelator.word,
        suzukiFreeGenerator] using
        hdefect (SuzukiRelator.tailFarCommutator (1 : Fin 4) (3 : Fin 4)
          (by decide) (by decide) (by norm_num) : SuzukiRelator 1)
    have hz1 : a6z1 ∈ N := by
      exact N.mul_mem hu1 (N.inv_mem
        (N.mul_mem hw3 (N.inv_mem hu3)))
    have hz2 : a6z2 ∈ N := by
      exact N.mul_mem (N.mul_mem hv1 (N.inv_mem hu1))
        (N.inv_mem (N.mul_mem hw hu2))
    have hz3 : a6z3 ∈ N := by
      exact N.mul_mem hv2 (N.inv_mem (N.mul_mem hu2 hu3))
    have hz4 : a6z4 ∈ N := by
      exact N.mul_mem hv3 (N.inv_mem (N.mul_mem hu3 hu4))
    have hk : a6k ∈ N := by
      exact N.mul_mem
        (N.mul_mem hw (N.mul_mem hw4 (N.inv_mem hu4)))
        (N.inv_mem (N.mul_mem hw3 (N.inv_mem hu3)))
    simp only [a6ExceptionalCenterGenerators, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · simpa [N, a6z1, a6t3] using hz1
    · simpa [N, a6z2, a6A, a6B] using hz2
    · simpa [N, a6z3] using hz3
    · simpa [N, a6z4] using hz4
    · simpa [N, a6k, a6t4, a6t3] using hk

@[expose]
public def a6ExponentFree :
    AlternatingSuzukiFreeGroup 1 →* Multiplicative (Fin 4 → ℤ) :=
  FreeGroup.lift
    (fun i => Multiplicative.ofAdd (fun j => if j = i then 1 else 0))

@[expose]
public noncomputable def a6AbelianizationEquiv :
    Abelianization (AlternatingSuzukiFreeGroup 1) ≃*
      Multiplicative (Fin 4 → ℤ) :=
  ((FreeAbelianGroup.equivFinsupp (Fin 4)).trans
    Finsupp.addEquivFunOnFinite).toMultiplicative

public theorem a6ExponentFree_eq_abelianization :
    a6ExponentFree =
      (a6AbelianizationEquiv.toMonoidHom).comp Abelianization.of := by
  apply FreeGroup.ext_hom
  intro i
  ext j
  simp only [a6ExponentFree, FreeGroup.lift_apply_of, MonoidHom.comp_apply]
  dsimp [a6AbelianizationEquiv]
  change (if j = i then 1 else 0) =
    Finsupp.equivFunOnFinite
      (FreeAbelianGroup.toFinsupp (FreeAbelianGroup.of i)) j
  rw [FreeAbelianGroup.toFinsupp_of]
  simp [Finsupp.single_apply, eq_comm]

public theorem a6ExponentFree_ker_eq_commutator :
    a6ExponentFree.ker = commutator (AlternatingSuzukiFreeGroup 1) := by
  rw [a6ExponentFree_eq_abelianization,
    MonoidHom.ker_comp_of_injective Abelianization.of
      a6AbelianizationEquiv.toMonoidHom a6AbelianizationEquiv.injective]
  exact Abelianization.ker_of _

@[expose]
public def a6Exponent : A6FreeCentral →* Multiplicative (Fin 4 → ℤ) :=
  QuotientGroup.lift
    (FreeCentralExtension.freeCentralKernel (alternatingSuzukiKernel 1))
    a6ExponentFree (by
      intro x hx
      apply Abelianization.commutator_subset_ker a6ExponentFree
      exact Subgroup.commutator_mono le_rfl le_top hx)

@[expose]
public def a6ExponentCoord (x : A6FreeCentral) (j : Fin 4) : ℤ :=
  Multiplicative.toAdd (a6Exponent x) j

@[simp]
public theorem a6ExponentCoord_one (j : Fin 4) :
    a6ExponentCoord 1 j = 0 := by
  simp [a6ExponentCoord]

@[simp]
public theorem a6ExponentCoord_mul (x y : A6FreeCentral) (j : Fin 4) :
    a6ExponentCoord (x * y) j =
      a6ExponentCoord x j + a6ExponentCoord y j := by
  simp [a6ExponentCoord]

@[simp]
public theorem a6ExponentCoord_inv (x : A6FreeCentral) (j : Fin 4) :
    a6ExponentCoord x⁻¹ j = -a6ExponentCoord x j := by
  simp [a6ExponentCoord]

@[simp]
public theorem a6ExponentCoord_pow (x : A6FreeCentral) (m : Nat) (j : Fin 4) :
    a6ExponentCoord (x ^ m) j = m * a6ExponentCoord x j := by
  simp [a6ExponentCoord]

@[simp]
public theorem a6ExponentCoord_zpow (x : A6FreeCentral) (m : ℤ) (j : Fin 4) :
    a6ExponentCoord (x ^ m) j = m * a6ExponentCoord x j := by
  simp [a6ExponentCoord]

@[simp]
public theorem a6ExponentCoord_gen (i j : Fin 4) :
    a6ExponentCoord (a6FCGen i) j = if j = i then 1 else 0 := by
  simp [a6ExponentCoord, a6Exponent, a6ExponentFree, a6FCGen]

public theorem a6ExponentCoord_z1 (j : Fin 4) :
    a6ExponentCoord a6z1 j = if j = 0 then 1 else 0 := by
  fin_cases j <;>
    norm_num [a6z1, a6t3, a6u1, a6u3, a6w3,
      a6ExponentCoord_gen]; decide

public theorem a6ExponentCoord_z2 (j : Fin 4) :
    a6ExponentCoord a6z2 j = if j = 1 then 1 else 0 := by
  fin_cases j <;>
    norm_num [a6z2, a6A, a6B, a6v1, a6u1, a6w, a6u2,
      a6ExponentCoord_gen, commutatorElement_def]

public theorem a6ExponentCoord_z3 (j : Fin 4) :
    a6ExponentCoord a6z3 j =
      (if j = 1 then 1 else 0) + (if j = 2 then 1 else 0) := by
  fin_cases j <;>
    norm_num [a6z3, a6v2, a6u2, a6u3, a6ExponentCoord_gen] <;>
      all_goals decide
public theorem a6ExponentCoord_z4 (j : Fin 4) :
    a6ExponentCoord a6z4 j =
      (if j = 2 then 1 else 0) + (if j = 3 then 1 else 0) := by
  fin_cases j <;>
    norm_num [a6z4, a6v3, a6u3, a6u4, a6ExponentCoord_gen] <;>
      all_goals decide
public theorem a6ExponentCoord_k (j : Fin 4) :
    a6ExponentCoord a6k j = 0 := by
  fin_cases j <;>
    norm_num [a6k, a6t4, a6t3, a6w,
      a6w4, a6u4, a6w3, a6u3, a6ExponentCoord_gen,
      commutatorElement_def]; decide

public theorem a6Exponent_ker_eq_commutator :
    a6Exponent.ker = commutator A6FreeCentral := by
  let q : AlternatingSuzukiFreeGroup 1 →* A6FreeCentral :=
    QuotientGroup.mk' (FreeCentralExtension.freeCentralKernel
      (alternatingSuzukiKernel 1))
  apply le_antisymm
  · intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
      (FreeCentralExtension.freeCentralKernel (alternatingSuzukiKernel 1)) x
    have hy : y ∈ a6ExponentFree.ker := by
      rw [MonoidHom.mem_ker]
      change a6Exponent (q y) = 1 at hx
      exact MonoidHom.mem_ker.mp hx
    rw [a6ExponentFree_ker_eq_commutator] at hy
    have hmap : (commutator (AlternatingSuzukiFreeGroup 1)).map q =
        commutator A6FreeCentral := by
      rw [map_commutator_eq,
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _),
        commutator_def]
    rw [← hmap]
    exact ⟨y, hy, rfl⟩
  · exact Abelianization.commutator_subset_ker a6Exponent

public theorem a6k_mem_commutator : a6k ∈ commutator A6FreeCentral := by
  rw [← a6Exponent_ker_eq_commutator, MonoidHom.mem_ker]
  ext j
  exact a6ExponentCoord_k j

public theorem a6k_pow_six : a6k ^ 6 = 1 := by
  calc
    a6k ^ 6 = (a6k ^ 3) ^ 2 := by group
    _ = a6w ^ 2 := by rw [a6k_cube]
    _ = 1 := a6w_sq

@[expose]
public def a6DerivedK : AlternatingFreeCentralDerived 1 :=
  ⟨a6k, a6k_mem_commutator⟩

public theorem a6DerivedK_pow_six : a6DerivedK ^ 6 = 1 :=
  Subtype.ext a6k_pow_six

public def A6NormalForm (x : A6FreeCentral) : Prop :=
  ∃ a1 a2 a3 a4 ak : ℤ,
    x = a6z1 ^ a1 * a6z2 ^ a2 * a6z3 ^ a3 * a6z4 ^ a4 * a6k ^ ak

public theorem a6NormalForm_one : A6NormalForm (1 : A6FreeCentral) := by
  refine ⟨0, 0, 0, 0, 0, ?_⟩
  simp

public theorem a6NormalForm_mul {x y : A6FreeCentral}
    (hx : A6NormalForm x) (hy : A6NormalForm y) :
    A6NormalForm (x * y) := by
  rcases hx with ⟨a1, a2, a3, a4, ak, rfl⟩
  rcases hy with ⟨b1, b2, b3, b4, bk, rfl⟩
  refine ⟨a1 + b1, a2 + b2, a3 + b3, a4 + b4, ak + bk, ?_⟩
  let : CommGroup (Subgroup.center A6FreeCentral) := {
    mul_comm := fun u v => Subtype.ext
      (Subgroup.mem_center_iff.mp u.2 v.1).symm }
  let Z1 : Subgroup.center A6FreeCentral := ⟨a6z1, a6z1_mem_center⟩
  let Z2 : Subgroup.center A6FreeCentral := ⟨a6z2, a6z2_mem_center⟩
  let Z3 : Subgroup.center A6FreeCentral := ⟨a6z3, a6z3_mem_center⟩
  let Z4 : Subgroup.center A6FreeCentral := ⟨a6z4, a6z4_mem_center⟩
  let K : Subgroup.center A6FreeCentral := ⟨a6k, a6k_mem_center⟩
  have h :
      (Z1 ^ a1 * Z2 ^ a2 * Z3 ^ a3 * Z4 ^ a4 * K ^ ak) *
          (Z1 ^ b1 * Z2 ^ b2 * Z3 ^ b3 * Z4 ^ b4 * K ^ bk) =
        Z1 ^ (a1 + b1) * Z2 ^ (a2 + b2) * Z3 ^ (a3 + b3) *
          Z4 ^ (a4 + b4) * K ^ (ak + bk) := by
    simp only [zpow_add]
    ac_rfl
  exact congrArg Subtype.val h

public theorem a6NormalForm_inv {x : A6FreeCentral}
    (hx : A6NormalForm x) : A6NormalForm x⁻¹ := by
  rcases hx with ⟨a1, a2, a3, a4, ak, rfl⟩
  refine ⟨-a1, -a2, -a3, -a4, -ak, ?_⟩
  let : CommGroup (Subgroup.center A6FreeCentral) := {
    mul_comm := fun u v => Subtype.ext
      (Subgroup.mem_center_iff.mp u.2 v.1).symm }
  let Z1 : Subgroup.center A6FreeCentral := ⟨a6z1, a6z1_mem_center⟩
  let Z2 : Subgroup.center A6FreeCentral := ⟨a6z2, a6z2_mem_center⟩
  let Z3 : Subgroup.center A6FreeCentral := ⟨a6z3, a6z3_mem_center⟩
  let Z4 : Subgroup.center A6FreeCentral := ⟨a6z4, a6z4_mem_center⟩
  let K : Subgroup.center A6FreeCentral := ⟨a6k, a6k_mem_center⟩
  have h :
      (Z1 ^ a1 * Z2 ^ a2 * Z3 ^ a3 * Z4 ^ a4 * K ^ ak)⁻¹ =
        Z1 ^ (-a1) * Z2 ^ (-a2) * Z3 ^ (-a3) * Z4 ^ (-a4) * K ^ (-ak) := by
    simp only [mul_inv_rev, zpow_neg]
    ac_rfl
  exact congrArg Subtype.val h

public theorem a6NormalForm_of_generator {x : A6FreeCentral}
    (hx : x ∈ a6ExceptionalCenterGenerators) : A6NormalForm x := by
  simp only [a6ExceptionalCenterGenerators, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 0, 0, 0, 0, by simp⟩
  · exact ⟨0, 1, 0, 0, 0, by simp⟩
  · exact ⟨0, 0, 1, 0, 0, by simp⟩
  · exact ⟨0, 0, 0, 1, 0, by simp⟩
  · exact ⟨0, 0, 0, 0, 1, by simp⟩

public theorem a6ExceptionalCenter_normalForm {x : A6FreeCentral}
    (hx : x ∈ a6ExceptionalCenter) : A6NormalForm x := by
  change x ∈ Subgroup.closure a6ExceptionalCenterGenerators at hx
  exact Subgroup.closure_induction
    (fun y hy => a6NormalForm_of_generator hy)
    a6NormalForm_one
    (fun _ _ _ _ hx hy => a6NormalForm_mul hx hy)
    (fun _ _ hx => a6NormalForm_inv hx)
    hx

public theorem a6DerivedProjection_ker_eq_zpowers :
    (alternatingFreeCentralDerivedProjection 1).ker =
      Subgroup.zpowers a6DerivedK := by
  apply le_antisymm
  · intro x hx
    have hxFull : (x : A6FreeCentral) ∈
        (alternatingFreeCentralProjection 1).ker := hx
    rw [a6FullProjection_ker_eq_exceptionalCenter] at hxFull
    rcases a6ExceptionalCenter_normalForm hxFull with
      ⟨a1, a2, a3, a4, ak, hrep⟩
    have hxExp : a6Exponent (x : A6FreeCentral) = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [a6Exponent_ker_eq_commutator]
      exact x.property
    have hxCoord (j : Fin 4) :
        a6ExponentCoord (x : A6FreeCentral) j = 0 := by
      simp [a6ExponentCoord, hxExp]
    have hcoord (j : Fin 4) :
        0 = a6ExponentCoord
          (a6z1 ^ a1 * a6z2 ^ a2 * a6z3 ^ a3 * a6z4 ^ a4 * a6k ^ ak) j := by
      rw [← hrep, hxCoord]
    have h0 := hcoord (0 : Fin 4)
    have h1 := hcoord (1 : Fin 4)
    have h2 := hcoord (2 : Fin 4)
    have h3 := hcoord (3 : Fin 4)
    simp [a6ExponentCoord_z1, a6ExponentCoord_z2,
      a6ExponentCoord_z3, a6ExponentCoord_z4, a6ExponentCoord_k,
      Fin.ext_iff] at h0 h1 h2 h3
    have ha1 : a1 = 0 := by omega
    have ha4 : a4 = 0 := by omega
    have ha3 : a3 = 0 := by omega
    have ha2 : a2 = 0 := by omega
    rw [ha1, ha2, ha3, ha4] at hrep
    simp at hrep
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨ak, ?_⟩
    apply Subtype.ext
    exact hrep.symm
  · rw [Subgroup.zpowers_le]
    rw [MonoidHom.mem_ker]
    change alternatingFreeCentralProjection 1 a6k = 1
    apply MonoidHom.mem_ker.mp
    rw [a6FullProjection_ker_eq_exceptionalCenter]
    exact a6k_mem_exceptionalCenter

public theorem a6UniversalKernel_isCyclic :
    IsCyclic (↥(alternatingFreeCentralCovering 1).toMonoidHom.ker) := by
  change IsCyclic (↥(alternatingFreeCentralDerivedProjection 1).ker)
  rw [a6DerivedProjection_ker_eq_zpowers]
  infer_instance

public theorem a6UniversalKernel_card_eq_six
    (h3 : 3 ∣ Nat.card
      (alternatingFreeCentralCovering 1).toMonoidHom.ker) :
    Nat.card (alternatingFreeCentralCovering 1).toMonoidHom.ker = 6 := by
  have h2 : 2 ∣ Nat.card
      (alternatingFreeCentralCovering 1).toMonoidHom.ker :=
    two_dvd_natCard_ker_alternatingFreeCentralCovering 1
  have hlower : 6 ∣ Nat.card
      (alternatingFreeCentralCovering 1).toMonoidHom.ker := by
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
  have hupper : Nat.card
      (alternatingFreeCentralCovering 1).toMonoidHom.ker ∣ 6 := by
    change Nat.card (alternatingFreeCentralDerivedProjection 1).ker ∣ 6
    rw [a6DerivedProjection_ker_eq_zpowers, Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one a6DerivedK_pow_six
  exact Nat.dvd_antisymm hupper hlower


public theorem exceptional_commutator_mul_left_of_center
    {G : Type*} [Group G] (k x y : G) (hk : k ∈ Subgroup.center G) :
    ⁅k * x, y⁆ = ⁅x, y⁆ := by
  have hky : Commute k y := (Subgroup.mem_center_iff.mp hk y).symm
  have hkcomm : Commute k ⁅x, y⁆ :=
    (Subgroup.mem_center_iff.mp hk ⁅x, y⁆).symm
  rw [commutatorElement_mul_left_eq_conj_mul, hky.commutator_eq, mul_one]
  exact hkcomm.mul_inv_cancel

public theorem exceptional_commutator_mul_right_of_center
    {G : Type*} [Group G] (x k y : G) (hk : k ∈ Subgroup.center G) :
    ⁅x, k * y⁆ = ⁅x, y⁆ := by
  have hxk : Commute x k := Subgroup.mem_center_iff.mp hk x
  have hkcomm : Commute k ⁅x, y⁆ :=
    (Subgroup.mem_center_iff.mp hk ⁅x, y⁆).symm
  rw [commutatorElement_mul_right_eq_mul_conj, hxk.commutator_eq, one_mul]
  exact hkcomm.mul_inv_cancel

public theorem commutator_eq_of_central_extension_conjugate_images
    {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center G)
    {x y x' y' : G} (hxy : ⁅x, y⁆ ∈ Subgroup.center G)
    (q : Q)
    (hx : q * f x * q⁻¹ = f x')
    (hy : q * f y * q⁻¹ = f y') :
    ⁅x', y'⁆ = ⁅x, y⁆ := by
  obtain ⟨g, rfl⟩ := hf q
  let cx : G := g * x * g⁻¹
  let cy : G := g * y * g⁻¹
  let kx : G := x' * cx⁻¹
  let ky : G := y' * cy⁻¹
  have hkx : kx ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    dsimp [kx, cx]
    simp only [map_mul, map_inv]
    rw [hx]
    group
  have hky : ky ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    dsimp [ky, cy]
    simp only [map_mul, map_inv]
    rw [hy]
    group
  have hxrep : x' = kx * cx := by
    dsimp [kx]
    group
  have hyrep : y' = ky * cy := by
    dsimp [ky]
    group
  calc
    ⁅x', y'⁆ = ⁅kx * cx, ky * cy⁆ := by rw [hxrep, hyrep]
    _ = ⁅cx, ky * cy⁆ :=
      exceptional_commutator_mul_left_of_center kx cx (ky * cy) (hker hkx)
    _ = ⁅cx, cy⁆ :=
      exceptional_commutator_mul_right_of_center cx ky cy (hker hky)
    _ = g * ⁅x, y⁆ * g⁻¹ := (conjugate_commutatorElement x y g).symm
    _ = ⁅x, y⁆ := by
      rw [Subgroup.mem_center_iff.mp hxy g]
      simp

public theorem a7_exists_conjugator_13_14 :
    ∃ q : alternatingGroup (Fin 7),
      q * alternatingSuzukiGenerator 2 (1 : Fin 5) * q⁻¹ =
          alternatingSuzukiGenerator 2 (1 : Fin 5) ∧
        q * alternatingSuzukiGenerator 2 (3 : Fin 5) * q⁻¹ =
          alternatingSuzukiGenerator 2 (4 : Fin 5) := by
  all_goals decide
public theorem a7_exists_conjugator_13_24 :
    ∃ q : alternatingGroup (Fin 7),
      q * alternatingSuzukiGenerator 2 (1 : Fin 5) * q⁻¹ =
          alternatingSuzukiGenerator 2 (2 : Fin 5) ∧
        q * alternatingSuzukiGenerator 2 (3 : Fin 5) * q⁻¹ =
          alternatingSuzukiGenerator 2 (4 : Fin 5) := by
  all_goals decide
public theorem root_far_reduced_cube
    {G : Type*} [Group G] (x a : G)
    (hx : x ^ 3 ∈ Subgroup.center G)
    (ha : a ^ 2 ∈ Subgroup.center G)
    (hxa : (x * a) ^ 2 ∈ Subgroup.center G) :
    ((x * a) ^ 2 * (a ^ 2)⁻¹) ^ 3 = (x ^ 3) ^ 2 := by
  let : CommGroup (Subgroup.center G) := {
    mul_comm := fun u v => Subtype.ext
      (Subgroup.mem_center_iff.mp u.2 v.1).symm }
  let X : Subgroup.center G := ⟨x ^ 3, hx⟩
  let A : Subgroup.center G := ⟨a ^ 2, ha⟩
  let W : Subgroup.center G := ⟨(x * a) ^ 2, hxa⟩
  have h : X ^ 2 * A ^ 3 = W ^ 3 :=
    Subtype.ext (cube_defect_root_far x a hx ha hxa)
  have h' : (W * A⁻¹) ^ 3 = X ^ 2 := by
    rw [mul_pow, ← h]
    group
  exact congrArg Subtype.val h'

public theorem root_far_reduced_square_eq
    {G : Type*} [Group G] (x a b : G)
    (ha : a ^ 2 ∈ Subgroup.center G)
    (hb : b ^ 2 ∈ Subgroup.center G)
    (hxa : (x * a) ^ 2 ∈ Subgroup.center G)
    (hxb : (x * b) ^ 2 ∈ Subgroup.center G)
    (hab : ⁅a, b⁆ ∈ Subgroup.center G) :
    ((x * b) ^ 2 * (b ^ 2)⁻¹) ^ 2 =
      ((x * a) ^ 2 * (a ^ 2)⁻¹) ^ 2 := by
  let ta : G := (x * a) ^ 2 * (a ^ 2)⁻¹
  let tb : G := (x * b) ^ 2 * (b ^ 2)⁻¹
  have hta : ta ∈ Subgroup.center G :=
    (Subgroup.center G).mul_mem hxa ((Subgroup.center G).inv_mem ha)
  have htb : tb ∈ Subgroup.center G :=
    (Subgroup.center G).mul_mem hxb ((Subgroup.center G).inv_mem hb)
  have hconjA : a * x * a⁻¹ = x⁻¹ * ta := by
    dsimp [ta]
    simp only [pow_two, mul_inv_rev]
    group
  have hconjB : b * x * b⁻¹ = x⁻¹ * tb := by
    dsimp [tb]
    simp only [pow_two, mul_inv_rev]
    group
  have habMul : a * b = ⁅a, b⁆ * (b * a) := by
    simp only [commutatorElement_def]
    group
  have hconjComm :
      a * (b * x * b⁻¹) * a⁻¹ = b * (a * x * a⁻¹) * b⁻¹ := by
    calc
      a * (b * x * b⁻¹) * a⁻¹ = (a * b) * x * (a * b)⁻¹ := by group
      _ = (⁅a, b⁆ * (b * a)) * x * (⁅a, b⁆ * (b * a))⁻¹ := by rw [habMul]
      _ = (b * a) * x * (b * a)⁻¹ := by
        have hwconj :
            ⁅a, b⁆ * ((b * a) * x * (b * a)⁻¹) * ⁅a, b⁆⁻¹ =
              (b * a) * x * (b * a)⁻¹ := by
          rw [← Subgroup.mem_center_iff.mp hab ((b * a) * x * (b * a)⁻¹)]
          group
        rw [mul_inv_rev]
        calc
          (⁅a, b⁆ * (b * a)) * x * ((b * a)⁻¹ * ⁅a, b⁆⁻¹) =
              ⁅a, b⁆ * ((b * a) * x * (b * a)⁻¹) * ⁅a, b⁆⁻¹ := by group
          _ = (b * a) * x * (b * a)⁻¹ := hwconj
      _ = b * (a * x * a⁻¹) * b⁻¹ := by group
  have hleft :
      a * (b * x * b⁻¹) * a⁻¹ = x * ta⁻¹ * tb := by
    rw [hconjB]
    calc
      a * (x⁻¹ * tb) * a⁻¹ = (a * x * a⁻¹)⁻¹ * tb := by
        have htbConj : a * tb * a⁻¹ = tb := by
          rw [Subgroup.mem_center_iff.mp htb a]
          simp
        calc
          a * (x⁻¹ * tb) * a⁻¹ =
              (a * x * a⁻¹)⁻¹ * (a * tb * a⁻¹) := by group
          _ = (a * x * a⁻¹)⁻¹ * tb := by rw [htbConj]
      _ = (x⁻¹ * ta)⁻¹ * tb := by rw [hconjA]
      _ = ta⁻¹ * x * tb := by rw [mul_inv_rev, inv_inv]
      _ = x * ta⁻¹ * tb := by
        rw [← Subgroup.mem_center_iff.mp
          ((Subgroup.center G).inv_mem hta) x]
  have hright :
      b * (a * x * a⁻¹) * b⁻¹ = x * tb⁻¹ * ta := by
    rw [hconjA]
    calc
      b * (x⁻¹ * ta) * b⁻¹ = (b * x * b⁻¹)⁻¹ * ta := by
        have htaConj : b * ta * b⁻¹ = ta := by
          rw [Subgroup.mem_center_iff.mp hta b]
          simp
        calc
          b * (x⁻¹ * ta) * b⁻¹ =
              (b * x * b⁻¹)⁻¹ * (b * ta * b⁻¹) := by group
          _ = (b * x * b⁻¹)⁻¹ * ta := by rw [htaConj]
      _ = (x⁻¹ * tb)⁻¹ * ta := by rw [hconjB]
      _ = tb⁻¹ * x * ta := by rw [mul_inv_rev, inv_inv]
      _ = x * tb⁻¹ * ta := by
        rw [← Subgroup.mem_center_iff.mp
          ((Subgroup.center G).inv_mem htb) x]
  have hrel0 : x * ta⁻¹ * tb = x * tb⁻¹ * ta :=
    hleft.symm.trans (hconjComm.trans hright)
  have hrel0' : x * (ta⁻¹ * tb) = x * (tb⁻¹ * ta) := by
    simpa [mul_assoc] using hrel0
  have hrel : ta⁻¹ * tb = tb⁻¹ * ta := mul_left_cancel hrel0'
  let : CommGroup (Subgroup.center G) := {
    mul_comm := fun u v => Subtype.ext
      (Subgroup.mem_center_iff.mp u.2 v.1).symm }
  let TA : Subgroup.center G := ⟨ta, hta⟩
  let TB : Subgroup.center G := ⟨tb, htb⟩
  have hrel' : TA⁻¹ * TB = TB⁻¹ * TA := Subtype.ext hrel
  have hsq : TB ^ 2 = TA ^ 2 := by
    calc
      TB ^ 2 = (TA⁻¹ * TA) * (TB * TB) := by simp [pow_two]
      _ = (TA⁻¹ * TB) * TA * TB := by ac_rfl
      _ = (TB⁻¹ * TA) * TA * TB := by rw [hrel']
      _ = (TB⁻¹ * TB) * (TA * TA) := by ac_rfl
      _ = TA ^ 2 := by simp [pow_two]
  exact congrArg Subtype.val hsq

public abbrev A7FreeCentral := AlternatingFreeCentralGroup 2

@[expose]
public def a7FCGen (i : Fin 5) : A7FreeCentral :=
  QuotientGroup.mk' (FreeCentralExtension.freeCentralKernel
    (alternatingSuzukiKernel 2)) (FreeGroup.of i)

@[simp]
public theorem alternatingFreeCentralProjection_a7FCGen (i : Fin 5) :
    alternatingFreeCentralProjection 2 (a7FCGen i) =
      alternatingSuzukiGenerator 2 i := by
  rfl

@[expose]
public def a7u1 : A7FreeCentral := a7FCGen 0 ^ 3
@[expose]
public def a7u2 : A7FreeCentral := a7FCGen 1 ^ 2
@[expose]
public def a7u3 : A7FreeCentral := a7FCGen 2 ^ 2
@[expose]
public def a7u4 : A7FreeCentral := a7FCGen 3 ^ 2
@[expose]
public def a7u5 : A7FreeCentral := a7FCGen 4 ^ 2
@[expose]
public def a7v1 : A7FreeCentral := (a7FCGen 0 * a7FCGen 1) ^ 3
@[expose]
public def a7v2 : A7FreeCentral := (a7FCGen 1 * a7FCGen 2) ^ 3
@[expose]
public def a7v3 : A7FreeCentral := (a7FCGen 2 * a7FCGen 3) ^ 3
@[expose]
public def a7v4 : A7FreeCentral := (a7FCGen 3 * a7FCGen 4) ^ 3
@[expose]
public def a7w3 : A7FreeCentral := (a7FCGen 0 * a7FCGen 2) ^ 2
@[expose]
public def a7w4 : A7FreeCentral := (a7FCGen 0 * a7FCGen 3) ^ 2
@[expose]
public def a7w5 : A7FreeCentral := (a7FCGen 0 * a7FCGen 4) ^ 2
@[expose]
public def a7w : A7FreeCentral := ⁅a7FCGen 1, a7FCGen 3⁆
@[expose]
public def a7w14 : A7FreeCentral := ⁅a7FCGen 1, a7FCGen 4⁆
@[expose]
public def a7w24 : A7FreeCentral := ⁅a7FCGen 2, a7FCGen 4⁆

public theorem a7RelatorDefect_mem_ker (r : SuzukiRelator 2) :
    QuotientGroup.mk' (FreeCentralExtension.freeCentralKernel
        (alternatingSuzukiKernel 2)) r.word ∈
      (alternatingFreeCentralProjection 2).ker := by
  rw [MonoidHom.mem_ker]
  change alternatingSuzukiMap 2 r.word = 1
  exact SuzukiRelator.lift_alternatingSuzukiGenerator_eq_one r

public theorem a7RelatorDefect_mem_center (r : SuzukiRelator 2) :
    QuotientGroup.mk' (FreeCentralExtension.freeCentralKernel
        (alternatingSuzukiKernel 2)) r.word ∈
      Subgroup.center A7FreeCentral :=
  alternatingFreeCentralProjection_ker_le_center 2 (a7RelatorDefect_mem_ker r)

public theorem a7u1_mem_center : a7u1 ∈ Subgroup.center A7FreeCentral := by
  simpa [a7u1, a7FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
    a7RelatorDefect_mem_center (SuzukiRelator.rootCube : SuzukiRelator 2)

public theorem a7u2_mem_center : a7u2 ∈ Subgroup.center A7FreeCentral := by
  simpa [a7u2, a7FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
    a7RelatorDefect_mem_center
      (SuzukiRelator.tailSquare (1 : Fin 5) (by decide) : SuzukiRelator 2)

public theorem a7u3_mem_center : a7u3 ∈ Subgroup.center A7FreeCentral := by
  simpa [a7u3, a7FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
    a7RelatorDefect_mem_center
      (SuzukiRelator.tailSquare (2 : Fin 5) (by decide) : SuzukiRelator 2)

public theorem a7u4_mem_center : a7u4 ∈ Subgroup.center A7FreeCentral := by
  simpa [a7u4, a7FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
    a7RelatorDefect_mem_center
      (SuzukiRelator.tailSquare (3 : Fin 5) (by decide) : SuzukiRelator 2)

public theorem a7u5_mem_center : a7u5 ∈ Subgroup.center A7FreeCentral := by
  simpa [a7u5, a7FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
    a7RelatorDefect_mem_center
      (SuzukiRelator.tailSquare (4 : Fin 5) (by decide) : SuzukiRelator 2)

public theorem a7v1_mem_center : a7v1 ∈ Subgroup.center A7FreeCentral := by
  simpa [a7v1, a7FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
    a7RelatorDefect_mem_center (SuzukiRelator.rootAdjacentCube : SuzukiRelator 2)

public theorem a7v2_mem_center : a7v2 ∈ Subgroup.center A7FreeCentral := by
  simpa [a7v2, a7FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
    a7RelatorDefect_mem_center
      (SuzukiRelator.tailAdjacentCube (1 : Fin 4) (by decide) : SuzukiRelator 2)

public theorem a7v3_mem_center : a7v3 ∈ Subgroup.center A7FreeCentral := by
  simpa [a7v3, a7FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
    a7RelatorDefect_mem_center
      (SuzukiRelator.tailAdjacentCube (2 : Fin 4) (by decide) : SuzukiRelator 2)

public theorem a7v4_mem_center : a7v4 ∈ Subgroup.center A7FreeCentral := by
  simpa [a7v4, a7FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
    a7RelatorDefect_mem_center
      (SuzukiRelator.tailAdjacentCube (3 : Fin 4) (by decide) : SuzukiRelator 2)

public theorem a7w3_mem_center : a7w3 ∈ Subgroup.center A7FreeCentral := by
  simpa [a7w3, a7FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
    a7RelatorDefect_mem_center
      (SuzukiRelator.rootFarSquare (2 : Fin 5) (by decide) : SuzukiRelator 2)

public theorem a7w4_mem_center : a7w4 ∈ Subgroup.center A7FreeCentral := by
  simpa [a7w4, a7FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
    a7RelatorDefect_mem_center
      (SuzukiRelator.rootFarSquare (3 : Fin 5) (by decide) : SuzukiRelator 2)

public theorem a7w5_mem_center : a7w5 ∈ Subgroup.center A7FreeCentral := by
  simpa [a7w5, a7FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
    a7RelatorDefect_mem_center
      (SuzukiRelator.rootFarSquare (4 : Fin 5) (by decide) : SuzukiRelator 2)

public theorem a7w_mem_center : a7w ∈ Subgroup.center A7FreeCentral := by
  simpa [a7w, a7FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
    a7RelatorDefect_mem_center
      (SuzukiRelator.tailFarCommutator (1 : Fin 5) (3 : Fin 5)
        (by decide) (by decide) (by norm_num) : SuzukiRelator 2)

public theorem a7w14_mem_center : a7w14 ∈ Subgroup.center A7FreeCentral := by
  simpa [a7w14, a7FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
    a7RelatorDefect_mem_center
      (SuzukiRelator.tailFarCommutator (1 : Fin 5) (4 : Fin 5)
        (by decide) (by decide) (by norm_num) : SuzukiRelator 2)

public theorem a7w24_mem_center : a7w24 ∈ Subgroup.center A7FreeCentral := by
  simpa [a7w24, a7FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
    a7RelatorDefect_mem_center
      (SuzukiRelator.tailFarCommutator (2 : Fin 5) (4 : Fin 5)
        (by decide) (by decide) (by norm_num) : SuzukiRelator 2)

public theorem a7w14_eq_w : a7w14 = a7w := by
  obtain ⟨q, hq1, hq2⟩ := a7_exists_conjugator_13_14
  exact commutator_eq_of_central_extension_conjugate_images
    (alternatingFreeCentralProjection 2)
    (alternatingFreeCentralProjection_surjective 2)
    (alternatingFreeCentralProjection_ker_le_center 2)
    a7w_mem_center q (by simpa using hq1) (by simpa using hq2)

public theorem a7w24_eq_w : a7w24 = a7w := by
  obtain ⟨q, hq1, hq2⟩ := a7_exists_conjugator_13_24
  exact commutator_eq_of_central_extension_conjugate_images
    (alternatingFreeCentralProjection 2)
    (alternatingFreeCentralProjection_surjective 2)
    (alternatingFreeCentralProjection_ker_le_center 2)
    a7w_mem_center q (by simpa using hq1) (by simpa using hq2)

public theorem a7w_sq : a7w ^ 2 = 1 := by
  apply commutator_sq_eq_one_of_sq_mem_center
      (u := a7FCGen 1) (v := a7FCGen 3)
  · simpa [a7u2, pow_two] using a7u2_mem_center
  · simpa [a7w] using a7w_mem_center

public theorem a7v2_sq : a7v2 ^ 2 = (a7u2 * a7u3) ^ 3 := by
  simpa [a7v2, a7u2, a7u3] using
    sq_defect_adjacent (a7FCGen 1) (a7FCGen 2)
      a7u2_mem_center a7u3_mem_center a7v2_mem_center

public theorem a7v3_sq : a7v3 ^ 2 = (a7u3 * a7u4) ^ 3 := by
  simpa [a7v3, a7u3, a7u4] using
    sq_defect_adjacent (a7FCGen 2) (a7FCGen 3)
      a7u3_mem_center a7u4_mem_center a7v3_mem_center

public theorem a7v4_sq : a7v4 ^ 2 = (a7u4 * a7u5) ^ 3 := by
  simpa [a7v4, a7u4, a7u5] using
    sq_defect_adjacent (a7FCGen 3) (a7FCGen 4)
      a7u4_mem_center a7u5_mem_center a7v4_mem_center

@[expose]
public def a7t3 : A7FreeCentral := a7w3 * a7u3⁻¹
@[expose]
public def a7t4 : A7FreeCentral := a7w4 * a7u4⁻¹
@[expose]
public def a7t5 : A7FreeCentral := a7w5 * a7u5⁻¹

public theorem a7t3_mem_center : a7t3 ∈ Subgroup.center A7FreeCentral :=
  (Subgroup.center A7FreeCentral).mul_mem a7w3_mem_center
    ((Subgroup.center A7FreeCentral).inv_mem a7u3_mem_center)

public theorem a7t4_mem_center : a7t4 ∈ Subgroup.center A7FreeCentral :=
  (Subgroup.center A7FreeCentral).mul_mem a7w4_mem_center
    ((Subgroup.center A7FreeCentral).inv_mem a7u4_mem_center)

public theorem a7t5_mem_center : a7t5 ∈ Subgroup.center A7FreeCentral :=
  (Subgroup.center A7FreeCentral).mul_mem a7w5_mem_center
    ((Subgroup.center A7FreeCentral).inv_mem a7u5_mem_center)

public theorem a7t3_cube : a7t3 ^ 3 = a7u1 ^ 2 := by
  simpa [a7t3, a7w3, a7u3, a7u1] using
    root_far_reduced_cube (a7FCGen 0) (a7FCGen 2)
      a7u1_mem_center a7u3_mem_center a7w3_mem_center

public theorem a7t4_cube : a7t4 ^ 3 = a7u1 ^ 2 := by
  simpa [a7t4, a7w4, a7u4, a7u1] using
    root_far_reduced_cube (a7FCGen 0) (a7FCGen 3)
      a7u1_mem_center a7u4_mem_center a7w4_mem_center

public theorem a7t5_cube : a7t5 ^ 3 = a7u1 ^ 2 := by
  simpa [a7t5, a7w5, a7u5, a7u1] using
    root_far_reduced_cube (a7FCGen 0) (a7FCGen 4)
      a7u1_mem_center a7u5_mem_center a7w5_mem_center

public theorem a7t5_sq_eq_t3_sq : a7t5 ^ 2 = a7t3 ^ 2 := by
  simpa [a7t3, a7t5, a7w3, a7w5, a7u3, a7u5] using
    root_far_reduced_square_eq (a7FCGen 0) (a7FCGen 2) (a7FCGen 4)
      a7u3_mem_center a7u5_mem_center a7w3_mem_center a7w5_mem_center
      a7w24_mem_center

public theorem a7t5_eq_t3 : a7t5 = a7t3 := by
  calc
    a7t5 = a7t5 ^ 3 * (a7t5 ^ 2)⁻¹ := by group
    _ = a7t3 ^ 3 * (a7t3 ^ 2)⁻¹ := by rw [a7t5_cube, a7t3_cube, a7t5_sq_eq_t3_sq]
    _ = a7t3 := by group

public theorem a7w_relation :
    a7w = a7v1 ^ 2 * (a7u1⁻¹) ^ 2 * (a7u2⁻¹) ^ 3 := by
  simpa [a7u1, a7u2, a7u4, a7v1, a7w4, a7w] using
    exceptional_far_commutator_relation
      (a7FCGen 0) (a7FCGen 1) (a7FCGen 3)
      a7u1_mem_center a7u2_mem_center a7u4_mem_center
      a7v1_mem_center a7w4_mem_center a7w_mem_center

@[expose]
public def a7A : A7FreeCentral := a7v1 * a7u1⁻¹
@[expose]
public def a7B : A7FreeCentral := a7w * a7u2
@[expose]
public def a7z1 : A7FreeCentral := a7u1 * a7t3⁻¹
@[expose]
public def a7z2 : A7FreeCentral := a7A * a7B⁻¹
@[expose]
public def a7z3 : A7FreeCentral := a7v2 * (a7u2 * a7u3)⁻¹
@[expose]
public def a7z4 : A7FreeCentral := a7v3 * (a7u3 * a7u4)⁻¹
@[expose]
public def a7z5 : A7FreeCentral := a7v4 * (a7u4 * a7u5)⁻¹
@[expose]
public def a7k : A7FreeCentral := a7w * a7t4 * a7t3⁻¹

public theorem a7A_mem_center : a7A ∈ Subgroup.center A7FreeCentral :=
  (Subgroup.center A7FreeCentral).mul_mem a7v1_mem_center
    ((Subgroup.center A7FreeCentral).inv_mem a7u1_mem_center)

public theorem a7B_mem_center : a7B ∈ Subgroup.center A7FreeCentral :=
  (Subgroup.center A7FreeCentral).mul_mem a7w_mem_center a7u2_mem_center

public theorem a7z1_mem_center : a7z1 ∈ Subgroup.center A7FreeCentral :=
  (Subgroup.center A7FreeCentral).mul_mem a7u1_mem_center
    ((Subgroup.center A7FreeCentral).inv_mem a7t3_mem_center)

public theorem a7z2_mem_center : a7z2 ∈ Subgroup.center A7FreeCentral :=
  (Subgroup.center A7FreeCentral).mul_mem a7A_mem_center
    ((Subgroup.center A7FreeCentral).inv_mem a7B_mem_center)

public theorem a7z3_mem_center : a7z3 ∈ Subgroup.center A7FreeCentral :=
  (Subgroup.center A7FreeCentral).mul_mem a7v2_mem_center
    ((Subgroup.center A7FreeCentral).inv_mem
      ((Subgroup.center A7FreeCentral).mul_mem a7u2_mem_center a7u3_mem_center))

public theorem a7z4_mem_center : a7z4 ∈ Subgroup.center A7FreeCentral :=
  (Subgroup.center A7FreeCentral).mul_mem a7v3_mem_center
    ((Subgroup.center A7FreeCentral).inv_mem
      ((Subgroup.center A7FreeCentral).mul_mem a7u3_mem_center a7u4_mem_center))

public theorem a7z5_mem_center : a7z5 ∈ Subgroup.center A7FreeCentral :=
  (Subgroup.center A7FreeCentral).mul_mem a7v4_mem_center
    ((Subgroup.center A7FreeCentral).inv_mem
      ((Subgroup.center A7FreeCentral).mul_mem a7u4_mem_center a7u5_mem_center))

public theorem a7k_mem_center : a7k ∈ Subgroup.center A7FreeCentral :=
  (Subgroup.center A7FreeCentral).mul_mem
    ((Subgroup.center A7FreeCentral).mul_mem a7w_mem_center a7t4_mem_center)
    ((Subgroup.center A7FreeCentral).inv_mem a7t3_mem_center)

public theorem a7A_sq_eq_B_cube : a7A ^ 2 = a7B ^ 3 := by
  let : CommGroup (Subgroup.center A7FreeCentral) := {
    mul_comm := fun u v => Subtype.ext
      (Subgroup.mem_center_iff.mp u.2 v.1).symm }
  let U1 : Subgroup.center A7FreeCentral := ⟨a7u1, a7u1_mem_center⟩
  let U2 : Subgroup.center A7FreeCentral := ⟨a7u2, a7u2_mem_center⟩
  let V1 : Subgroup.center A7FreeCentral := ⟨a7v1, a7v1_mem_center⟩
  let W : Subgroup.center A7FreeCentral := ⟨a7w, a7w_mem_center⟩
  let A : Subgroup.center A7FreeCentral := ⟨a7A, a7A_mem_center⟩
  let B : Subgroup.center A7FreeCentral := ⟨a7B, a7B_mem_center⟩
  have hw : W = V1 ^ 2 * U1⁻¹ ^ 2 * U2⁻¹ ^ 3 := Subtype.ext a7w_relation
  have hw2 : W ^ 2 = 1 := Subtype.ext a7w_sq
  have hAB : A ^ 2 = B ^ 3 := by
    dsimp [A, B, a7A, a7B]
    calc
      (V1 * U1⁻¹) ^ 2 = V1 ^ 2 * U1⁻¹ ^ 2 := by rw [mul_pow]
      _ = W * U2 ^ 3 := by rw [hw]; group
      _ = W ^ 3 * U2 ^ 3 := by
        rw [show W ^ 3 = W by
          calc
            W ^ 3 = W ^ 2 * W := by group
            _ = W := by rw [hw2]; simp]
      _ = (W * U2) ^ 3 := by rw [mul_pow]
  exact congrArg Subtype.val hAB

public theorem a7z1_sq : a7z1 ^ 2 = a7t3 := by
  let : CommGroup (Subgroup.center A7FreeCentral) := {
    mul_comm := fun u v => Subtype.ext
      (Subgroup.mem_center_iff.mp u.2 v.1).symm }
  let T3 : Subgroup.center A7FreeCentral := ⟨a7t3, a7t3_mem_center⟩
  let U1 : Subgroup.center A7FreeCentral := ⟨a7u1, a7u1_mem_center⟩
  have h : U1 ^ 2 = T3 ^ 3 := Subtype.ext a7t3_cube.symm
  exact congrArg Subtype.val (cubeSquareGenerator T3 U1 h).1

public theorem a7z1_cube : a7z1 ^ 3 = a7u1 := by
  let : CommGroup (Subgroup.center A7FreeCentral) := {
    mul_comm := fun u v => Subtype.ext
      (Subgroup.mem_center_iff.mp u.2 v.1).symm }
  let T3 : Subgroup.center A7FreeCentral := ⟨a7t3, a7t3_mem_center⟩
  let U1 : Subgroup.center A7FreeCentral := ⟨a7u1, a7u1_mem_center⟩
  have h : U1 ^ 2 = T3 ^ 3 := Subtype.ext a7t3_cube.symm
  exact congrArg Subtype.val (cubeSquareGenerator T3 U1 h).2

public theorem a7z2_sq : a7z2 ^ 2 = a7B := by
  let : CommGroup (Subgroup.center A7FreeCentral) := {
    mul_comm := fun u v => Subtype.ext
      (Subgroup.mem_center_iff.mp u.2 v.1).symm }
  let B : Subgroup.center A7FreeCentral := ⟨a7B, a7B_mem_center⟩
  let A : Subgroup.center A7FreeCentral := ⟨a7A, a7A_mem_center⟩
  have h : A ^ 2 = B ^ 3 := Subtype.ext a7A_sq_eq_B_cube
  exact congrArg Subtype.val (cubeSquareGenerator B A h).1

public theorem a7z2_cube : a7z2 ^ 3 = a7A := by
  let : CommGroup (Subgroup.center A7FreeCentral) := {
    mul_comm := fun u v => Subtype.ext
      (Subgroup.mem_center_iff.mp u.2 v.1).symm }
  let B : Subgroup.center A7FreeCentral := ⟨a7B, a7B_mem_center⟩
  let A : Subgroup.center A7FreeCentral := ⟨a7A, a7A_mem_center⟩
  have h : A ^ 2 = B ^ 3 := Subtype.ext a7A_sq_eq_B_cube
  exact congrArg Subtype.val (cubeSquareGenerator B A h).2

public theorem a7z3_sq : a7z3 ^ 2 = a7u2 * a7u3 := by
  let : CommGroup (Subgroup.center A7FreeCentral) := {
    mul_comm := fun u v => Subtype.ext
      (Subgroup.mem_center_iff.mp u.2 v.1).symm }
  let X : Subgroup.center A7FreeCentral :=
    ⟨a7u2 * a7u3, (Subgroup.center A7FreeCentral).mul_mem
      a7u2_mem_center a7u3_mem_center⟩
  let Y : Subgroup.center A7FreeCentral := ⟨a7v2, a7v2_mem_center⟩
  have h : Y ^ 2 = X ^ 3 := Subtype.ext a7v2_sq
  exact congrArg Subtype.val (cubeSquareGenerator X Y h).1

public theorem a7z3_cube : a7z3 ^ 3 = a7v2 := by
  let : CommGroup (Subgroup.center A7FreeCentral) := {
    mul_comm := fun u v => Subtype.ext
      (Subgroup.mem_center_iff.mp u.2 v.1).symm }
  let X : Subgroup.center A7FreeCentral :=
    ⟨a7u2 * a7u3, (Subgroup.center A7FreeCentral).mul_mem
      a7u2_mem_center a7u3_mem_center⟩
  let Y : Subgroup.center A7FreeCentral := ⟨a7v2, a7v2_mem_center⟩
  have h : Y ^ 2 = X ^ 3 := Subtype.ext a7v2_sq
  exact congrArg Subtype.val (cubeSquareGenerator X Y h).2

public theorem a7z4_sq : a7z4 ^ 2 = a7u3 * a7u4 := by
  let : CommGroup (Subgroup.center A7FreeCentral) := {
    mul_comm := fun u v => Subtype.ext
      (Subgroup.mem_center_iff.mp u.2 v.1).symm }
  let X : Subgroup.center A7FreeCentral :=
    ⟨a7u3 * a7u4, (Subgroup.center A7FreeCentral).mul_mem
      a7u3_mem_center a7u4_mem_center⟩
  let Y : Subgroup.center A7FreeCentral := ⟨a7v3, a7v3_mem_center⟩
  have h : Y ^ 2 = X ^ 3 := Subtype.ext a7v3_sq
  exact congrArg Subtype.val (cubeSquareGenerator X Y h).1

public theorem a7z4_cube : a7z4 ^ 3 = a7v3 := by
  let : CommGroup (Subgroup.center A7FreeCentral) := {
    mul_comm := fun u v => Subtype.ext
      (Subgroup.mem_center_iff.mp u.2 v.1).symm }
  let X : Subgroup.center A7FreeCentral :=
    ⟨a7u3 * a7u4, (Subgroup.center A7FreeCentral).mul_mem
      a7u3_mem_center a7u4_mem_center⟩
  let Y : Subgroup.center A7FreeCentral := ⟨a7v3, a7v3_mem_center⟩
  have h : Y ^ 2 = X ^ 3 := Subtype.ext a7v3_sq
  exact congrArg Subtype.val (cubeSquareGenerator X Y h).2

public theorem a7z5_sq : a7z5 ^ 2 = a7u4 * a7u5 := by
  let : CommGroup (Subgroup.center A7FreeCentral) := {
    mul_comm := fun u v => Subtype.ext
      (Subgroup.mem_center_iff.mp u.2 v.1).symm }
  let X : Subgroup.center A7FreeCentral :=
    ⟨a7u4 * a7u5, (Subgroup.center A7FreeCentral).mul_mem
      a7u4_mem_center a7u5_mem_center⟩
  let Y : Subgroup.center A7FreeCentral := ⟨a7v4, a7v4_mem_center⟩
  have h : Y ^ 2 = X ^ 3 := Subtype.ext a7v4_sq
  exact congrArg Subtype.val (cubeSquareGenerator X Y h).1

public theorem a7z5_cube : a7z5 ^ 3 = a7v4 := by
  let : CommGroup (Subgroup.center A7FreeCentral) := {
    mul_comm := fun u v => Subtype.ext
      (Subgroup.mem_center_iff.mp u.2 v.1).symm }
  let X : Subgroup.center A7FreeCentral :=
    ⟨a7u4 * a7u5, (Subgroup.center A7FreeCentral).mul_mem
      a7u4_mem_center a7u5_mem_center⟩
  let Y : Subgroup.center A7FreeCentral := ⟨a7v4, a7v4_mem_center⟩
  have h : Y ^ 2 = X ^ 3 := Subtype.ext a7v4_sq
  exact congrArg Subtype.val (cubeSquareGenerator X Y h).2

public theorem a7k_cube : a7k ^ 3 = a7w := by
  let : CommGroup (Subgroup.center A7FreeCentral) := {
    mul_comm := fun u v => Subtype.ext
      (Subgroup.mem_center_iff.mp u.2 v.1).symm }
  let W : Subgroup.center A7FreeCentral := ⟨a7w, a7w_mem_center⟩
  let T3 : Subgroup.center A7FreeCentral := ⟨a7t3, a7t3_mem_center⟩
  let T4 : Subgroup.center A7FreeCentral := ⟨a7t4, a7t4_mem_center⟩
  let K : Subgroup.center A7FreeCentral := W * T4 * T3⁻¹
  have hw2 : W ^ 2 = 1 := Subtype.ext a7w_sq
  have ht : T3 ^ 3 = T4 ^ 3 := by
    apply Subtype.ext
    exact a7t3_cube.trans a7t4_cube.symm
  have hK : K ^ 3 = W := by
    dsimp [K]
    rw [mul_pow, mul_pow, inv_pow, ht]
    have hw3 : W ^ 3 = W := by
      calc
        W ^ 3 = W ^ 2 * W := by group
        _ = W := by rw [hw2]; simp
    rw [hw3]
    group
  simpa [a7k, K, W, T3, T4] using congrArg Subtype.val hK

public theorem a7k_pow_six : a7k ^ 6 = 1 := by
  calc
    a7k ^ 6 = (a7k ^ 3) ^ 2 := by group
    _ = a7w ^ 2 := by rw [a7k_cube]
    _ = 1 := a7w_sq

public def a7ExceptionalCenterGenerators : Set A7FreeCentral :=
  {a7z1, a7z2, a7z3, a7z4, a7z5, a7k}

public def a7ExceptionalCenter : Subgroup A7FreeCentral :=
  Subgroup.closure a7ExceptionalCenterGenerators

public theorem a7z1_mem_exceptionalCenter : a7z1 ∈ a7ExceptionalCenter :=
  Subgroup.subset_closure (by simp [a7ExceptionalCenterGenerators])

public theorem a7z2_mem_exceptionalCenter : a7z2 ∈ a7ExceptionalCenter :=
  Subgroup.subset_closure (by simp [a7ExceptionalCenterGenerators])

public theorem a7z3_mem_exceptionalCenter : a7z3 ∈ a7ExceptionalCenter :=
  Subgroup.subset_closure (by simp [a7ExceptionalCenterGenerators])

public theorem a7z4_mem_exceptionalCenter : a7z4 ∈ a7ExceptionalCenter :=
  Subgroup.subset_closure (by simp [a7ExceptionalCenterGenerators])

public theorem a7z5_mem_exceptionalCenter : a7z5 ∈ a7ExceptionalCenter :=
  Subgroup.subset_closure (by simp [a7ExceptionalCenterGenerators])

public theorem a7k_mem_exceptionalCenter : a7k ∈ a7ExceptionalCenter :=
  Subgroup.subset_closure (by simp [a7ExceptionalCenterGenerators])

public theorem a7ExceptionalCenter_le_center :
    a7ExceptionalCenter ≤ Subgroup.center A7FreeCentral := by
  rw [a7ExceptionalCenter, Subgroup.closure_le]
  intro x hx
  simp only [a7ExceptionalCenterGenerators, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact a7z1_mem_center
  · exact a7z2_mem_center
  · exact a7z3_mem_center
  · exact a7z4_mem_center
  · exact a7z5_mem_center
  · exact a7k_mem_center

public theorem a7w_mem_exceptionalCenter : a7w ∈ a7ExceptionalCenter := by
  rw [← a7k_cube]
  exact a7ExceptionalCenter.pow_mem a7k_mem_exceptionalCenter 3

public theorem a7u1_mem_exceptionalCenter : a7u1 ∈ a7ExceptionalCenter := by
  rw [← a7z1_cube]
  exact a7ExceptionalCenter.pow_mem a7z1_mem_exceptionalCenter 3

public theorem a7t3_mem_exceptionalCenter : a7t3 ∈ a7ExceptionalCenter := by
  rw [← a7z1_sq]
  exact a7ExceptionalCenter.pow_mem a7z1_mem_exceptionalCenter 2

public theorem a7B_mem_exceptionalCenter : a7B ∈ a7ExceptionalCenter := by
  rw [← a7z2_sq]
  exact a7ExceptionalCenter.pow_mem a7z2_mem_exceptionalCenter 2

public theorem a7u2_mem_exceptionalCenter : a7u2 ∈ a7ExceptionalCenter := by
  have hEq : a7u2 = a7w⁻¹ * a7B := by simp [a7B]
  rw [hEq]
  exact a7ExceptionalCenter.mul_mem
    (a7ExceptionalCenter.inv_mem a7w_mem_exceptionalCenter)
    a7B_mem_exceptionalCenter

public theorem a7u3_mem_exceptionalCenter : a7u3 ∈ a7ExceptionalCenter := by
  have hEq : a7u3 = a7u2⁻¹ * (a7u2 * a7u3) := by group
  rw [hEq, ← a7z3_sq]
  exact a7ExceptionalCenter.mul_mem
    (a7ExceptionalCenter.inv_mem a7u2_mem_exceptionalCenter)
    (a7ExceptionalCenter.pow_mem a7z3_mem_exceptionalCenter 2)

public theorem a7u4_mem_exceptionalCenter : a7u4 ∈ a7ExceptionalCenter := by
  have hEq : a7u4 = a7u3⁻¹ * (a7u3 * a7u4) := by group
  rw [hEq, ← a7z4_sq]
  exact a7ExceptionalCenter.mul_mem
    (a7ExceptionalCenter.inv_mem a7u3_mem_exceptionalCenter)
    (a7ExceptionalCenter.pow_mem a7z4_mem_exceptionalCenter 2)

public theorem a7u5_mem_exceptionalCenter : a7u5 ∈ a7ExceptionalCenter := by
  have hEq : a7u5 = a7u4⁻¹ * (a7u4 * a7u5) := by group
  rw [hEq, ← a7z5_sq]
  exact a7ExceptionalCenter.mul_mem
    (a7ExceptionalCenter.inv_mem a7u4_mem_exceptionalCenter)
    (a7ExceptionalCenter.pow_mem a7z5_mem_exceptionalCenter 2)

public theorem a7t4_mem_exceptionalCenter : a7t4 ∈ a7ExceptionalCenter := by
  have hEq : a7t4 = a7w⁻¹ * a7k * a7t3 := by
    dsimp [a7k]
    group
  rw [hEq]
  exact a7ExceptionalCenter.mul_mem
    (a7ExceptionalCenter.mul_mem
      (a7ExceptionalCenter.inv_mem a7w_mem_exceptionalCenter)
      a7k_mem_exceptionalCenter)
    a7t3_mem_exceptionalCenter

public theorem a7t5_mem_exceptionalCenter : a7t5 ∈ a7ExceptionalCenter := by
  rw [a7t5_eq_t3]
  exact a7t3_mem_exceptionalCenter

public theorem a7w3_mem_exceptionalCenter : a7w3 ∈ a7ExceptionalCenter := by
  have hEq : a7w3 = a7t3 * a7u3 := by simp [a7t3]
  rw [hEq]
  exact a7ExceptionalCenter.mul_mem a7t3_mem_exceptionalCenter
    a7u3_mem_exceptionalCenter

public theorem a7w4_mem_exceptionalCenter : a7w4 ∈ a7ExceptionalCenter := by
  have hEq : a7w4 = a7t4 * a7u4 := by simp [a7t4]
  rw [hEq]
  exact a7ExceptionalCenter.mul_mem a7t4_mem_exceptionalCenter
    a7u4_mem_exceptionalCenter

public theorem a7w5_mem_exceptionalCenter : a7w5 ∈ a7ExceptionalCenter := by
  have hEq : a7w5 = a7t5 * a7u5 := by simp [a7t5]
  rw [hEq]
  exact a7ExceptionalCenter.mul_mem a7t5_mem_exceptionalCenter
    a7u5_mem_exceptionalCenter

public theorem a7A_mem_exceptionalCenter : a7A ∈ a7ExceptionalCenter := by
  rw [← a7z2_cube]
  exact a7ExceptionalCenter.pow_mem a7z2_mem_exceptionalCenter 3

public theorem a7v1_mem_exceptionalCenter : a7v1 ∈ a7ExceptionalCenter := by
  have hEq : a7v1 = a7A * a7u1 := by simp [a7A]
  rw [hEq]
  exact a7ExceptionalCenter.mul_mem a7A_mem_exceptionalCenter
    a7u1_mem_exceptionalCenter

public theorem a7v2_mem_exceptionalCenter : a7v2 ∈ a7ExceptionalCenter := by
  rw [← a7z3_cube]
  exact a7ExceptionalCenter.pow_mem a7z3_mem_exceptionalCenter 3

public theorem a7v3_mem_exceptionalCenter : a7v3 ∈ a7ExceptionalCenter := by
  rw [← a7z4_cube]
  exact a7ExceptionalCenter.pow_mem a7z4_mem_exceptionalCenter 3

public theorem a7v4_mem_exceptionalCenter : a7v4 ∈ a7ExceptionalCenter := by
  rw [← a7z5_cube]
  exact a7ExceptionalCenter.pow_mem a7z5_mem_exceptionalCenter 3

public theorem a7w14_mem_exceptionalCenter : a7w14 ∈ a7ExceptionalCenter := by
  rw [a7w14_eq_w]
  exact a7w_mem_exceptionalCenter

public theorem a7w24_mem_exceptionalCenter : a7w24 ∈ a7ExceptionalCenter := by
  rw [a7w24_eq_w]
  exact a7w_mem_exceptionalCenter

public theorem a7RelatorDefect_mem_exceptionalCenter (r : SuzukiRelator 2) :
    QuotientGroup.mk' (FreeCentralExtension.freeCentralKernel
        (alternatingSuzukiKernel 2)) r.word ∈ a7ExceptionalCenter := by
  cases r with
  | rootCube =>
      simpa [a7u1, a7FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
        a7u1_mem_exceptionalCenter
  | tailSquare i hi =>
      fin_cases i
      · simp at hi
      · simpa [a7u2, a7FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
          a7u2_mem_exceptionalCenter
      · simpa [a7u3, a7FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
          a7u3_mem_exceptionalCenter
      · simpa [a7u4, a7FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
          a7u4_mem_exceptionalCenter
      · simpa [a7u5, a7FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
          a7u5_mem_exceptionalCenter
  | rootAdjacentCube =>
      simpa [a7v1, a7FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
        a7v1_mem_exceptionalCenter
  | tailAdjacentCube i hi =>
      fin_cases i
      · simp at hi
      · simpa [a7v2, a7FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
          a7v2_mem_exceptionalCenter
      · simpa [a7v3, a7FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
          a7v3_mem_exceptionalCenter
      · simpa [a7v4, a7FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
          a7v4_mem_exceptionalCenter
  | rootFarSquare j hj =>
      fin_cases j
      · norm_num at hj
      · norm_num at hj
      · simpa [a7w3, a7FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
          a7w3_mem_exceptionalCenter
      · simpa [a7w4, a7FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
          a7w4_mem_exceptionalCenter
      · simpa [a7w5, a7FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
          a7w5_mem_exceptionalCenter
  | tailFarCommutator i j hi hj hfar =>
      fin_cases i <;> fin_cases j <;> simp at hi hj hfar
      · simpa [a7w, a7FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
          a7w_mem_exceptionalCenter
      · simpa [a7w14, a7FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
          a7w14_mem_exceptionalCenter
      · simpa [a7w24, a7FCGen, SuzukiRelator.word, suzukiFreeGenerator] using
          a7w24_mem_exceptionalCenter
      · change ⁅a7FCGen 3, a7FCGen 1⁆ ∈ a7ExceptionalCenter
        rw [← commutatorElement_inv]
        exact a7ExceptionalCenter.inv_mem a7w_mem_exceptionalCenter
      · change ⁅a7FCGen 4, a7FCGen 1⁆ ∈ a7ExceptionalCenter
        rw [← commutatorElement_inv]
        exact a7ExceptionalCenter.inv_mem a7w14_mem_exceptionalCenter
      · change ⁅a7FCGen 4, a7FCGen 2⁆ ∈ a7ExceptionalCenter
        rw [← commutatorElement_inv]
        exact a7ExceptionalCenter.inv_mem a7w24_mem_exceptionalCenter

public theorem a7FullProjection_ker_eq_exceptionalCenter :
    (alternatingFreeCentralProjection 2).ker = a7ExceptionalCenter := by
  let q : AlternatingSuzukiFreeGroup 2 →* A7FreeCentral :=
    QuotientGroup.mk' (FreeCentralExtension.freeCentralKernel
      (alternatingSuzukiKernel 2))
  have hker : (alternatingFreeCentralProjection 2).ker =
      (FreeCentralExtension.freeCentralProjection
        (alternatingSuzukiKernel 2)).ker := by
    exact MonoidHom.ker_comp_of_injective
      (FreeCentralExtension.freeCentralProjection (alternatingSuzukiKernel 2))
      (alternatingSuzukiQuotientEquiv 2).toMonoidHom
      (alternatingSuzukiQuotientEquiv 2).injective
  rw [hker, FreeCentralExtension.freeCentralProjection_ker]
  change (alternatingSuzukiKernel 2).map q = a7ExceptionalCenter
  have hmap : (alternatingSuzukiKernel 2).map q =
      (Subgroup.normalClosure (suzukiRelatorSet 2)).map q :=
    congrArg (fun H : Subgroup (AlternatingSuzukiFreeGroup 2) => H.map q)
      (alternatingSuzukiKernel_eq_normalClosure 2)
  rw [hmap, Subgroup.map_normalClosure (suzukiRelatorSet 2) q
    (QuotientGroup.mk'_surjective _)]
  apply le_antisymm
  · let : a7ExceptionalCenter.Normal := ⟨fun n hn g => by
      have hncenter := a7ExceptionalCenter_le_center hn
      have hcomm := Subgroup.mem_center_iff.mp hncenter g
      rw [hcomm]
      simpa using hn⟩
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨x, ⟨r, rfl⟩, rfl⟩
    exact a7RelatorDefect_mem_exceptionalCenter r
  · rw [a7ExceptionalCenter, Subgroup.closure_le]
    intro x hx
    let N := Subgroup.normalClosure (q '' suzukiRelatorSet 2)
    have hdefect (r : SuzukiRelator 2) : q r.word ∈ N := by
      apply Subgroup.subset_normalClosure
      exact ⟨r.word, ⟨r, rfl⟩, rfl⟩
    have hu1 : a7u1 ∈ N := by
      simpa [N, q, a7u1, a7FCGen, SuzukiRelator.word,
        suzukiFreeGenerator] using
        hdefect (SuzukiRelator.rootCube : SuzukiRelator 2)
    have hu2 : a7u2 ∈ N := by
      simpa [N, q, a7u2, a7FCGen, SuzukiRelator.word,
        suzukiFreeGenerator] using
        hdefect (SuzukiRelator.tailSquare (1 : Fin 5) (by decide) :
          SuzukiRelator 2)
    have hu3 : a7u3 ∈ N := by
      simpa [N, q, a7u3, a7FCGen, SuzukiRelator.word,
        suzukiFreeGenerator] using
        hdefect (SuzukiRelator.tailSquare (2 : Fin 5) (by decide) :
          SuzukiRelator 2)
    have hu4 : a7u4 ∈ N := by
      simpa [N, q, a7u4, a7FCGen, SuzukiRelator.word,
        suzukiFreeGenerator] using
        hdefect (SuzukiRelator.tailSquare (3 : Fin 5) (by decide) :
          SuzukiRelator 2)
    have hu5 : a7u5 ∈ N := by
      simpa [N, q, a7u5, a7FCGen, SuzukiRelator.word,
        suzukiFreeGenerator] using
        hdefect (SuzukiRelator.tailSquare (4 : Fin 5) (by decide) :
          SuzukiRelator 2)
    have hv1 : a7v1 ∈ N := by
      simpa [N, q, a7v1, a7FCGen, SuzukiRelator.word,
        suzukiFreeGenerator] using
        hdefect (SuzukiRelator.rootAdjacentCube : SuzukiRelator 2)
    have hv2 : a7v2 ∈ N := by
      simpa [N, q, a7v2, a7FCGen, SuzukiRelator.word,
        suzukiFreeGenerator] using
        hdefect (SuzukiRelator.tailAdjacentCube (1 : Fin 4) (by decide) :
          SuzukiRelator 2)
    have hv3 : a7v3 ∈ N := by
      simpa [N, q, a7v3, a7FCGen, SuzukiRelator.word,
        suzukiFreeGenerator] using
        hdefect (SuzukiRelator.tailAdjacentCube (2 : Fin 4) (by decide) :
          SuzukiRelator 2)
    have hv4 : a7v4 ∈ N := by
      simpa [N, q, a7v4, a7FCGen, SuzukiRelator.word,
        suzukiFreeGenerator] using
        hdefect (SuzukiRelator.tailAdjacentCube (3 : Fin 4) (by decide) :
          SuzukiRelator 2)
    have hw3 : a7w3 ∈ N := by
      simpa [N, q, a7w3, a7FCGen, SuzukiRelator.word,
        suzukiFreeGenerator] using
        hdefect (SuzukiRelator.rootFarSquare (2 : Fin 5) (by decide) :
          SuzukiRelator 2)
    have hw4 : a7w4 ∈ N := by
      simpa [N, q, a7w4, a7FCGen, SuzukiRelator.word,
        suzukiFreeGenerator] using
        hdefect (SuzukiRelator.rootFarSquare (3 : Fin 5) (by decide) :
          SuzukiRelator 2)
    have hw : a7w ∈ N := by
      simpa [N, q, a7w, a7FCGen, SuzukiRelator.word,
        suzukiFreeGenerator] using
        hdefect (SuzukiRelator.tailFarCommutator (1 : Fin 5) (3 : Fin 5)
          (by decide) (by decide) (by norm_num) : SuzukiRelator 2)
    have hz1 : a7z1 ∈ N := by
      exact N.mul_mem hu1 (N.inv_mem (N.mul_mem hw3 (N.inv_mem hu3)))
    have hz2 : a7z2 ∈ N := by
      exact N.mul_mem (N.mul_mem hv1 (N.inv_mem hu1))
        (N.inv_mem (N.mul_mem hw hu2))
    have hz3 : a7z3 ∈ N := by
      exact N.mul_mem hv2 (N.inv_mem (N.mul_mem hu2 hu3))
    have hz4 : a7z4 ∈ N := by
      exact N.mul_mem hv3 (N.inv_mem (N.mul_mem hu3 hu4))
    have hz5 : a7z5 ∈ N := by
      exact N.mul_mem hv4 (N.inv_mem (N.mul_mem hu4 hu5))
    have hk : a7k ∈ N := by
      exact N.mul_mem
        (N.mul_mem hw (N.mul_mem hw4 (N.inv_mem hu4)))
        (N.inv_mem (N.mul_mem hw3 (N.inv_mem hu3)))
    simp only [a7ExceptionalCenterGenerators, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [N, a7z1, a7t3] using hz1
    · simpa [N, a7z2, a7A, a7B] using hz2
    · simpa [N, a7z3] using hz3
    · simpa [N, a7z4] using hz4
    · simpa [N, a7z5] using hz5
    · simpa [N, a7k, a7t4, a7t3] using hk

@[expose]
public def a7ExponentFree :
    AlternatingSuzukiFreeGroup 2 →* Multiplicative (Fin 5 → ℤ) :=
  FreeGroup.lift
    (fun i => Multiplicative.ofAdd (fun j => if j = i then 1 else 0))

@[expose]
public noncomputable def a7AbelianizationEquiv :
    Abelianization (AlternatingSuzukiFreeGroup 2) ≃*
      Multiplicative (Fin 5 → ℤ) :=
  ((FreeAbelianGroup.equivFinsupp (Fin 5)).trans
    Finsupp.addEquivFunOnFinite).toMultiplicative

public theorem a7ExponentFree_eq_abelianization :
    a7ExponentFree =
      (a7AbelianizationEquiv.toMonoidHom).comp Abelianization.of := by
  apply FreeGroup.ext_hom
  intro i
  ext j
  simp only [a7ExponentFree, FreeGroup.lift_apply_of, MonoidHom.comp_apply]
  dsimp [a7AbelianizationEquiv]
  change (if j = i then 1 else 0) =
    Finsupp.equivFunOnFinite
      (FreeAbelianGroup.toFinsupp (FreeAbelianGroup.of i)) j
  rw [FreeAbelianGroup.toFinsupp_of]
  simp [Finsupp.single_apply, eq_comm]

public theorem a7ExponentFree_ker_eq_commutator :
    a7ExponentFree.ker = commutator (AlternatingSuzukiFreeGroup 2) := by
  rw [a7ExponentFree_eq_abelianization,
    MonoidHom.ker_comp_of_injective Abelianization.of
      a7AbelianizationEquiv.toMonoidHom a7AbelianizationEquiv.injective]
  exact Abelianization.ker_of _

@[expose]
public def a7Exponent : A7FreeCentral →* Multiplicative (Fin 5 → ℤ) :=
  QuotientGroup.lift
    (FreeCentralExtension.freeCentralKernel (alternatingSuzukiKernel 2))
    a7ExponentFree (by
      intro x hx
      apply Abelianization.commutator_subset_ker a7ExponentFree
      exact Subgroup.commutator_mono le_rfl le_top hx)

@[expose]
public def a7ExponentCoord (x : A7FreeCentral) (j : Fin 5) : ℤ :=
  Multiplicative.toAdd (a7Exponent x) j

@[simp]
public theorem a7ExponentCoord_one (j : Fin 5) :
    a7ExponentCoord 1 j = 0 := by
  simp [a7ExponentCoord]

@[simp]
public theorem a7ExponentCoord_mul (x y : A7FreeCentral) (j : Fin 5) :
    a7ExponentCoord (x * y) j =
      a7ExponentCoord x j + a7ExponentCoord y j := by
  simp [a7ExponentCoord]

@[simp]
public theorem a7ExponentCoord_inv (x : A7FreeCentral) (j : Fin 5) :
    a7ExponentCoord x⁻¹ j = -a7ExponentCoord x j := by
  simp [a7ExponentCoord]

@[simp]
public theorem a7ExponentCoord_pow (x : A7FreeCentral) (m : Nat) (j : Fin 5) :
    a7ExponentCoord (x ^ m) j = m * a7ExponentCoord x j := by
  simp [a7ExponentCoord]

@[simp]
public theorem a7ExponentCoord_zpow (x : A7FreeCentral) (m : ℤ) (j : Fin 5) :
    a7ExponentCoord (x ^ m) j = m * a7ExponentCoord x j := by
  simp [a7ExponentCoord]

@[simp]
public theorem a7ExponentCoord_gen (i j : Fin 5) :
    a7ExponentCoord (a7FCGen i) j = if j = i then 1 else 0 := by
  simp [a7ExponentCoord, a7Exponent, a7ExponentFree, a7FCGen]

public theorem a7ExponentCoord_z1 (j : Fin 5) :
    a7ExponentCoord a7z1 j = if j = 0 then 1 else 0 := by
  fin_cases j <;>
    norm_num [a7z1, a7t3, a7u1, a7u3, a7w3,
      a7ExponentCoord_gen]; decide

public theorem a7ExponentCoord_z2 (j : Fin 5) :
    a7ExponentCoord a7z2 j = if j = 1 then 1 else 0 := by
  fin_cases j <;>
    norm_num [a7z2, a7A, a7B, a7v1, a7u1, a7w, a7u2,
      a7ExponentCoord_gen, commutatorElement_def]

public theorem a7ExponentCoord_z3 (j : Fin 5) :
    a7ExponentCoord a7z3 j =
      (if j = 1 then 1 else 0) + (if j = 2 then 1 else 0) := by
  fin_cases j <;>
    norm_num [a7z3, a7v2, a7u2, a7u3, a7ExponentCoord_gen] <;>
      all_goals decide
public theorem a7ExponentCoord_z4 (j : Fin 5) :
    a7ExponentCoord a7z4 j =
      (if j = 2 then 1 else 0) + (if j = 3 then 1 else 0) := by
  fin_cases j <;>
    norm_num [a7z4, a7v3, a7u3, a7u4, a7ExponentCoord_gen] <;>
      all_goals decide
public theorem a7ExponentCoord_z5 (j : Fin 5) :
    a7ExponentCoord a7z5 j =
      (if j = 3 then 1 else 0) + (if j = 4 then 1 else 0) := by
  fin_cases j <;>
    norm_num [a7z5, a7v4, a7u4, a7u5, a7ExponentCoord_gen] <;>
      all_goals decide
public theorem a7ExponentCoord_k (j : Fin 5) :
    a7ExponentCoord a7k j = 0 := by
  fin_cases j <;>
    norm_num [a7k, a7t4, a7t3, a7w,
      a7w4, a7u4, a7w3, a7u3, a7ExponentCoord_gen,
      commutatorElement_def]; decide

public theorem a7Exponent_ker_eq_commutator :
    a7Exponent.ker = commutator A7FreeCentral := by
  let q : AlternatingSuzukiFreeGroup 2 →* A7FreeCentral :=
    QuotientGroup.mk' (FreeCentralExtension.freeCentralKernel
      (alternatingSuzukiKernel 2))
  apply le_antisymm
  · intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
      (FreeCentralExtension.freeCentralKernel (alternatingSuzukiKernel 2)) x
    have hy : y ∈ a7ExponentFree.ker := by
      rw [MonoidHom.mem_ker]
      change a7Exponent (q y) = 1 at hx
      exact MonoidHom.mem_ker.mp hx
    rw [a7ExponentFree_ker_eq_commutator] at hy
    have hmap : (commutator (AlternatingSuzukiFreeGroup 2)).map q =
        commutator A7FreeCentral := by
      rw [map_commutator_eq,
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _),
        commutator_def]
    rw [← hmap]
    exact ⟨y, hy, rfl⟩
  · exact Abelianization.commutator_subset_ker a7Exponent

public theorem a7k_mem_commutator : a7k ∈ commutator A7FreeCentral := by
  rw [← a7Exponent_ker_eq_commutator, MonoidHom.mem_ker]
  ext j
  exact a7ExponentCoord_k j

@[expose]
public def a7DerivedK : AlternatingFreeCentralDerived 2 :=
  ⟨a7k, a7k_mem_commutator⟩

public theorem a7DerivedK_pow_six : a7DerivedK ^ 6 = 1 :=
  Subtype.ext a7k_pow_six

public def A7NormalForm (x : A7FreeCentral) : Prop :=
  ∃ a1 a2 a3 a4 a5 ak : ℤ,
    x = a7z1 ^ a1 * a7z2 ^ a2 * a7z3 ^ a3 * a7z4 ^ a4 *
      a7z5 ^ a5 * a7k ^ ak

public theorem a7NormalForm_one : A7NormalForm (1 : A7FreeCentral) := by
  refine ⟨0, 0, 0, 0, 0, 0, ?_⟩
  simp

public theorem a7NormalForm_mul {x y : A7FreeCentral}
    (hx : A7NormalForm x) (hy : A7NormalForm y) :
    A7NormalForm (x * y) := by
  rcases hx with ⟨a1, a2, a3, a4, a5, ak, rfl⟩
  rcases hy with ⟨b1, b2, b3, b4, b5, bk, rfl⟩
  refine ⟨a1 + b1, a2 + b2, a3 + b3, a4 + b4, a5 + b5, ak + bk, ?_⟩
  let : CommGroup (Subgroup.center A7FreeCentral) := {
    mul_comm := fun u v => Subtype.ext
      (Subgroup.mem_center_iff.mp u.2 v.1).symm }
  let Z1 : Subgroup.center A7FreeCentral := ⟨a7z1, a7z1_mem_center⟩
  let Z2 : Subgroup.center A7FreeCentral := ⟨a7z2, a7z2_mem_center⟩
  let Z3 : Subgroup.center A7FreeCentral := ⟨a7z3, a7z3_mem_center⟩
  let Z4 : Subgroup.center A7FreeCentral := ⟨a7z4, a7z4_mem_center⟩
  let Z5 : Subgroup.center A7FreeCentral := ⟨a7z5, a7z5_mem_center⟩
  let K : Subgroup.center A7FreeCentral := ⟨a7k, a7k_mem_center⟩
  have h :
      (Z1 ^ a1 * Z2 ^ a2 * Z3 ^ a3 * Z4 ^ a4 * Z5 ^ a5 * K ^ ak) *
          (Z1 ^ b1 * Z2 ^ b2 * Z3 ^ b3 * Z4 ^ b4 * Z5 ^ b5 * K ^ bk) =
        Z1 ^ (a1 + b1) * Z2 ^ (a2 + b2) * Z3 ^ (a3 + b3) *
          Z4 ^ (a4 + b4) * Z5 ^ (a5 + b5) * K ^ (ak + bk) := by
    simp only [zpow_add]
    ac_rfl
  exact congrArg Subtype.val h

public theorem a7NormalForm_inv {x : A7FreeCentral}
    (hx : A7NormalForm x) : A7NormalForm x⁻¹ := by
  rcases hx with ⟨a1, a2, a3, a4, a5, ak, rfl⟩
  refine ⟨-a1, -a2, -a3, -a4, -a5, -ak, ?_⟩
  let : CommGroup (Subgroup.center A7FreeCentral) := {
    mul_comm := fun u v => Subtype.ext
      (Subgroup.mem_center_iff.mp u.2 v.1).symm }
  let Z1 : Subgroup.center A7FreeCentral := ⟨a7z1, a7z1_mem_center⟩
  let Z2 : Subgroup.center A7FreeCentral := ⟨a7z2, a7z2_mem_center⟩
  let Z3 : Subgroup.center A7FreeCentral := ⟨a7z3, a7z3_mem_center⟩
  let Z4 : Subgroup.center A7FreeCentral := ⟨a7z4, a7z4_mem_center⟩
  let Z5 : Subgroup.center A7FreeCentral := ⟨a7z5, a7z5_mem_center⟩
  let K : Subgroup.center A7FreeCentral := ⟨a7k, a7k_mem_center⟩
  have h :
      (Z1 ^ a1 * Z2 ^ a2 * Z3 ^ a3 * Z4 ^ a4 * Z5 ^ a5 * K ^ ak)⁻¹ =
        Z1 ^ (-a1) * Z2 ^ (-a2) * Z3 ^ (-a3) * Z4 ^ (-a4) *
          Z5 ^ (-a5) * K ^ (-ak) := by
    simp only [mul_inv_rev, zpow_neg]
    ac_rfl
  exact congrArg Subtype.val h

public theorem a7NormalForm_of_generator {x : A7FreeCentral}
    (hx : x ∈ a7ExceptionalCenterGenerators) : A7NormalForm x := by
  simp only [a7ExceptionalCenterGenerators, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 0, 0, 0, 0, 0, by simp⟩
  · exact ⟨0, 1, 0, 0, 0, 0, by simp⟩
  · exact ⟨0, 0, 1, 0, 0, 0, by simp⟩
  · exact ⟨0, 0, 0, 1, 0, 0, by simp⟩
  · exact ⟨0, 0, 0, 0, 1, 0, by simp⟩
  · exact ⟨0, 0, 0, 0, 0, 1, by simp⟩

public theorem a7ExceptionalCenter_normalForm {x : A7FreeCentral}
    (hx : x ∈ a7ExceptionalCenter) : A7NormalForm x := by
  change x ∈ Subgroup.closure a7ExceptionalCenterGenerators at hx
  exact Subgroup.closure_induction
    (fun y hy => a7NormalForm_of_generator hy)
    a7NormalForm_one
    (fun _ _ _ _ hx hy => a7NormalForm_mul hx hy)
    (fun _ _ hx => a7NormalForm_inv hx)
    hx

public theorem a7DerivedProjection_ker_eq_zpowers :
    (alternatingFreeCentralDerivedProjection 2).ker =
      Subgroup.zpowers a7DerivedK := by
  apply le_antisymm
  · intro x hx
    have hxFull : (x : A7FreeCentral) ∈
        (alternatingFreeCentralProjection 2).ker := hx
    rw [a7FullProjection_ker_eq_exceptionalCenter] at hxFull
    rcases a7ExceptionalCenter_normalForm hxFull with
      ⟨a1, a2, a3, a4, a5, ak, hrep⟩
    have hxExp : a7Exponent (x : A7FreeCentral) = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [a7Exponent_ker_eq_commutator]
      exact x.property
    have hxCoord (j : Fin 5) :
        a7ExponentCoord (x : A7FreeCentral) j = 0 := by
      simp [a7ExponentCoord, hxExp]
    have hcoord (j : Fin 5) :
        0 = a7ExponentCoord
          (a7z1 ^ a1 * a7z2 ^ a2 * a7z3 ^ a3 * a7z4 ^ a4 *
            a7z5 ^ a5 * a7k ^ ak) j := by
      rw [← hrep, hxCoord]
    have h0 := hcoord (0 : Fin 5)
    have h1 := hcoord (1 : Fin 5)
    have h2 := hcoord (2 : Fin 5)
    have h3 := hcoord (3 : Fin 5)
    have h4 := hcoord (4 : Fin 5)
    simp [a7ExponentCoord_z1, a7ExponentCoord_z2,
      a7ExponentCoord_z3, a7ExponentCoord_z4, a7ExponentCoord_z5,
      a7ExponentCoord_k, Fin.ext_iff] at h0 h1 h2 h3 h4
    have ha1 : a1 = 0 := by omega
    have ha5 : a5 = 0 := by omega
    have ha4 : a4 = 0 := by omega
    have ha3 : a3 = 0 := by omega
    have ha2 : a2 = 0 := by omega
    rw [ha1, ha2, ha3, ha4, ha5] at hrep
    simp at hrep
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨ak, ?_⟩
    apply Subtype.ext
    exact hrep.symm
  · rw [Subgroup.zpowers_le]
    rw [MonoidHom.mem_ker]
    change alternatingFreeCentralProjection 2 a7k = 1
    apply MonoidHom.mem_ker.mp
    rw [a7FullProjection_ker_eq_exceptionalCenter]
    exact a7k_mem_exceptionalCenter

public theorem a7UniversalKernel_isCyclic :
    IsCyclic (↥(alternatingFreeCentralCovering 2).toMonoidHom.ker) := by
  change IsCyclic (↥(alternatingFreeCentralDerivedProjection 2).ker)
  rw [a7DerivedProjection_ker_eq_zpowers]
  infer_instance

public theorem a7UniversalKernel_card_eq_six
    (h3 : 3 ∣ Nat.card
      (alternatingFreeCentralCovering 2).toMonoidHom.ker) :
    Nat.card (alternatingFreeCentralCovering 2).toMonoidHom.ker = 6 := by
  have h2 : 2 ∣ Nat.card
      (alternatingFreeCentralCovering 2).toMonoidHom.ker :=
    two_dvd_natCard_ker_alternatingFreeCentralCovering 2
  have hlower : 6 ∣ Nat.card
      (alternatingFreeCentralCovering 2).toMonoidHom.ker := by
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
  have hupper : Nat.card
      (alternatingFreeCentralCovering 2).toMonoidHom.ker ∣ 6 := by
    change Nat.card (alternatingFreeCentralDerivedProjection 2).ker ∣ 6
    rw [a7DerivedProjection_ker_eq_zpowers, Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one a7DerivedK_pow_six
  exact Nat.dvd_antisymm hupper hlower

end GLS3.Chapter5.SchurPresentation
/- END Theory.Theorem523Suzuki -/

/- BEGIN Theory.PrimeCyclePermutationCoordinate -/
noncomputable section

namespace GLS3.Chapter5
universe __ch5_PrimeCyclePermutationCoordinate_u

/-- The chosen cycle-permuting section transports every prime-cycle
coordinate without changing its exponent. -/
public theorem primeCyclePermutation_apply_cycleCoordinate
    {Ω : Type __ch5_PrimeCyclePermutationCoordinate_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : (orderOf x).Prime)
    (l : cyclePermutationSubgroup x) (c : x.cycleFactorsFinset)
    (n : ZMod (orderOf x)) :
    l.1.1 (cycleCoordinateEquiv x hx c n).1 =
      (cycleCoordinateEquiv x hx
        ((theorem_5_2_2_d_3_a x hx) l c) n).1 := by
  let : NeZero (orderOf x) := ⟨hx.ne_zero⟩
  have hn : n = ((n.val : ℤ) : ZMod (orderOf x)) := by simp
  rw [hn]
  rw [cycleCoordinateEquiv_intCast_eq_x_zpow x hx c (n.val : ℤ),
    cycleCoordinateEquiv_intCast_eq_x_zpow x hx
      ((theorem_5_2_2_d_3_a x hx) l c) (n.val : ℤ)]
  rcases l with ⟨_, q, rfl⟩
  change Equiv.Perm.Basis.ofPermHomFun (cycleBasis x)
      (cycleActionRangeToExplicitRange x q)
      ((x ^ (n.val : ℤ)) (cycleBasis x c)) = _
  have hc : (x ^ (n.val : ℤ)) (cycleBasis x c) ∈ c.1.support := by
    rw [Equiv.Perm.zpow_apply_mem_support_of_mem_cycleFactorsFinset_iff]
    exact (cycleBasis x).mem_support_self c
  rw [Equiv.Perm.Basis.ofPermHomFun_apply_of_cycleOf_mem
    (cycleBasis x) (cycleActionRangeToExplicitRange x q) hc
    (m := n.val) rfl]
  congr 2
  let lq : cyclePermutationSubgroup x :=
    ⟨(cycleCentralizerSplitting x).toMonoidHom q, by
      show ∃ y, (cycleCentralizerSplitting x).toMonoidHom y = _
      exact ⟨q, rfl⟩⟩
  have hsigma : theorem_5_2_2_d_3_a x hx lq = q.1 := by
    change ((cycleActionRangeMulEquivCyclePermutationSubgroup x).symm lq).1 = q.1
    have hq :
        (cycleActionRangeMulEquivCyclePermutationSubgroup x).symm lq = q := by
      apply (cycleActionRangeMulEquivCyclePermutationSubgroup x).injective
      rw [(cycleActionRangeMulEquivCyclePermutationSubgroup x).apply_symm_apply]
      apply Subtype.ext
      rfl
    exact congrArg Subtype.val hq
  rw [hsigma]
  rfl

end GLS3.Chapter5
/- END Theory.PrimeCyclePermutationCoordinate -/

/- BEGIN Theory.Theorem523A6Matrix -/
noncomputable section
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
universe __ch5_Theorem523A6Matrix_w

namespace GLS3.Chapter5.SchurPresentation

open scoped commutatorElement

structure ExceptionalMatrix.F4 where
  re : ZMod 2
  im : ZMod 2
deriving DecidableEq, Repr

@[expose]
public def a6StandardLiftXFull : A6FreeCentral :=
  a6FCGen 0 * a6z1⁻¹

@[expose]
public def a6StandardLiftYFull : A6FreeCentral :=
  (a6FCGen 3)⁻¹ * (a6FCGen 2)⁻¹ * a6z4

public theorem a6StandardLiftXFull_mem_commutator :
    a6StandardLiftXFull ∈ commutator A6FreeCentral := by
  rw [← a6Exponent_ker_eq_commutator, MonoidHom.mem_ker]
  ext j
  change a6ExponentCoord a6StandardLiftXFull j = 0
  fin_cases j <;>
    norm_num [a6StandardLiftXFull, a6ExponentCoord_gen,
      a6ExponentCoord_z1]

public theorem a6StandardLiftYFull_mem_commutator :
    a6StandardLiftYFull ∈ commutator A6FreeCentral := by
  rw [← a6Exponent_ker_eq_commutator, MonoidHom.mem_ker]
  ext j
  change a6ExponentCoord a6StandardLiftYFull j = 0
  fin_cases j <;>
    norm_num [a6StandardLiftYFull, a6ExponentCoord_gen,
      a6ExponentCoord_z4]

@[expose]
public def a6StandardLiftX : AlternatingFreeCentralDerived 1 :=
  ⟨a6StandardLiftXFull, a6StandardLiftXFull_mem_commutator⟩

@[expose]
public def a6StandardLiftY : AlternatingFreeCentralDerived 1 :=
  ⟨a6StandardLiftYFull, a6StandardLiftYFull_mem_commutator⟩

private def __ch5_Theorem523A6Matrix_a7StandardLiftXFull : A7FreeCentral :=
  a7FCGen 0 * a7z1⁻¹

private def __ch5_Theorem523A6Matrix_a7StandardLiftYFull : A7FreeCentral :=
  (a7FCGen 3)⁻¹ * (a7FCGen 2)⁻¹ * a7z4

private theorem __ch5_Theorem523A6Matrix_a7StandardLiftXFull_mem_commutator :
    __ch5_Theorem523A6Matrix_a7StandardLiftXFull ∈ commutator A7FreeCentral := by
  rw [← a7Exponent_ker_eq_commutator, MonoidHom.mem_ker]
  ext j
  change a7ExponentCoord __ch5_Theorem523A6Matrix_a7StandardLiftXFull j = 0
  fin_cases j <;>
    norm_num [__ch5_Theorem523A6Matrix_a7StandardLiftXFull, a7ExponentCoord_gen,
      a7ExponentCoord_z1]

private theorem __ch5_Theorem523A6Matrix_a7StandardLiftYFull_mem_commutator :
    __ch5_Theorem523A6Matrix_a7StandardLiftYFull ∈ commutator A7FreeCentral := by
  rw [← a7Exponent_ker_eq_commutator, MonoidHom.mem_ker]
  ext j
  change a7ExponentCoord __ch5_Theorem523A6Matrix_a7StandardLiftYFull j = 0
  fin_cases j <;>
    norm_num [__ch5_Theorem523A6Matrix_a7StandardLiftYFull, a7ExponentCoord_gen,
      a7ExponentCoord_z4]

private def __ch5_Theorem523A6Matrix_a7StandardLiftX : AlternatingFreeCentralDerived 2 :=
  ⟨__ch5_Theorem523A6Matrix_a7StandardLiftXFull, __ch5_Theorem523A6Matrix_a7StandardLiftXFull_mem_commutator⟩

private def __ch5_Theorem523A6Matrix_a7StandardLiftY : AlternatingFreeCentralDerived 2 :=
  ⟨__ch5_Theorem523A6Matrix_a7StandardLiftYFull, __ch5_Theorem523A6Matrix_a7StandardLiftYFull_mem_commutator⟩

/-! ## Compact matrix certificates for the exceptional 3-parts

GAP is used only offline to locate the following faithful projective lifts of
the Suzuki generators.  Lean checks the finite-field arithmetic, all relator
defects, and the two exceptional kernel words directly.  No matrix group is
enumerated in the proof.
-/

namespace ExceptionalMatrix

namespace F4

private def __ch5_Theorem523A6Matrix_equivProd : F4 ≃ ZMod 2 × ZMod 2 where
  toFun x := (x.re, x.im)
  invFun x := ⟨x.1, x.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

instance : Fintype F4 :=
  Fintype.ofEquiv (ZMod 2 × ZMod 2) __ch5_Theorem523A6Matrix_equivProd.symm

instance : Zero F4 := ⟨⟨0, 0⟩⟩
instance : One F4 := ⟨⟨1, 0⟩⟩
instance : Add F4 := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩
instance : Neg F4 := ⟨fun x => ⟨-x.re, -x.im⟩⟩
instance : Mul F4 := ⟨fun x y =>
  ⟨x.re * y.re + x.im * y.im,
    x.re * y.im + x.im * y.re + x.im * y.im⟩⟩
instance : Inv F4 := ⟨fun x => ⟨x.re + x.im, x.im⟩⟩

instance : Field F4 := Field.ofMinimalAxioms F4
  (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide)
  ⟨0, 1, by decide⟩

def omega : F4 := ⟨0, 1⟩

private theorem __ch5_Theorem523A6Matrix_coordinate_ext {x y : F4}
    (hre : x.re = y.re) (him : x.im = y.im) : x = y := by
  cases x
  cases y
  simp_all

@[simp] private theorem __ch5_Theorem523A6Matrix_zero_re : (0 : F4).re = 0 := rfl
@[simp] private theorem __ch5_Theorem523A6Matrix_zero_im : (0 : F4).im = 0 := rfl
@[simp] private theorem __ch5_Theorem523A6Matrix_one_re : (1 : F4).re = 1 := rfl
@[simp] private theorem __ch5_Theorem523A6Matrix_one_im : (1 : F4).im = 0 := rfl
@[simp] private theorem __ch5_Theorem523A6Matrix_add_re (x y : F4) : (x + y).re = x.re + y.re := rfl
@[simp] private theorem __ch5_Theorem523A6Matrix_add_im (x y : F4) : (x + y).im = x.im + y.im := rfl
@[simp] private theorem __ch5_Theorem523A6Matrix_mul_re (x y : F4) :
    (x * y).re = x.re * y.re + x.im * y.im := rfl
@[simp] private theorem __ch5_Theorem523A6Matrix_mul_im (x y : F4) :
    (x * y).im = x.re * y.im + x.im * y.re + x.im * y.im := rfl

end F4
private abbrev __ch5_Theorem523A6Matrix_GL3F4 := Matrix.GeneralLinearGroup (Fin 3) F4
private def __ch5_Theorem523A6Matrix_a6MatG0 : __ch5_Theorem523A6Matrix_GL3F4 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![(0 : F4), F4.omega ^ 2, F4.omega;
       1, 0, 1;
       0, F4.omega ^ 2, 0] (by decide)

private def __ch5_Theorem523A6Matrix_a6MatG1 : __ch5_Theorem523A6Matrix_GL3F4 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![(0 : F4), F4.omega ^ 2, F4.omega;
       F4.omega ^ 2, 0, F4.omega;
       0, 0, F4.omega ^ 2] (by decide)

private def __ch5_Theorem523A6Matrix_a6MatG2 : __ch5_Theorem523A6Matrix_GL3F4 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![(0 : F4), 1, F4.omega ^ 2;
       F4.omega, 0, F4.omega;
       0, 0, F4.omega ^ 2] (by decide)

private def __ch5_Theorem523A6Matrix_a6MatG3 : __ch5_Theorem523A6Matrix_GL3F4 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![(0 : F4), 1, 1;
       1, 0, 1;
       0, 0, 1] (by decide)

private def __ch5_Theorem523A6Matrix_a6MatrixGenerator : Fin 4 → __ch5_Theorem523A6Matrix_GL3F4 :=
  ![__ch5_Theorem523A6Matrix_a6MatG0, __ch5_Theorem523A6Matrix_a6MatG1, __ch5_Theorem523A6Matrix_a6MatG2, __ch5_Theorem523A6Matrix_a6MatG3]

private abbrev __ch5_Theorem523A6Matrix_A6MatrixIsScalar (x : __ch5_Theorem523A6Matrix_GL3F4) : Prop :=
  x.val = Matrix.scalar (Fin 3) (x.val 0 0)

private theorem __ch5_Theorem523A6Matrix_a6RootCube :
    __ch5_Theorem523A6Matrix_A6MatrixIsScalar (__ch5_Theorem523A6Matrix_a6MatrixGenerator 0 ^ 3) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    apply F4.__ch5_Theorem523A6Matrix_coordinate_ext <;>
    norm_num [__ch5_Theorem523A6Matrix_a6MatrixGenerator, __ch5_Theorem523A6Matrix_a6MatG0, pow_succ, Matrix.mul_apply,
      Fin.sum_univ_succ, F4.omega] <;> decide

private theorem __ch5_Theorem523A6Matrix_a6TailSquare (i : Fin 4) (hi : i ≠ 0) :
    __ch5_Theorem523A6Matrix_A6MatrixIsScalar (__ch5_Theorem523A6Matrix_a6MatrixGenerator i ^ 2) := by
  fin_cases i <;> simp_all
  all_goals
    apply Matrix.ext
    intro r c
    fin_cases r <;> fin_cases c <;>
      apply F4.__ch5_Theorem523A6Matrix_coordinate_ext <;>
      norm_num [__ch5_Theorem523A6Matrix_a6MatrixGenerator, __ch5_Theorem523A6Matrix_a6MatG0, __ch5_Theorem523A6Matrix_a6MatG1, __ch5_Theorem523A6Matrix_a6MatG2, __ch5_Theorem523A6Matrix_a6MatG3,
        pow_succ, Matrix.mul_apply, Fin.sum_univ_succ, F4.omega] <;> decide

private theorem __ch5_Theorem523A6Matrix_a6RootAdjacentCube :
    __ch5_Theorem523A6Matrix_A6MatrixIsScalar ((__ch5_Theorem523A6Matrix_a6MatrixGenerator 0 * __ch5_Theorem523A6Matrix_a6MatrixGenerator 1) ^ 3) := by
  apply Matrix.ext
  intro r c
  fin_cases r <;> fin_cases c <;>
    apply F4.__ch5_Theorem523A6Matrix_coordinate_ext <;>
    norm_num [__ch5_Theorem523A6Matrix_a6MatrixGenerator, __ch5_Theorem523A6Matrix_a6MatG0, __ch5_Theorem523A6Matrix_a6MatG1, pow_succ,
      Matrix.mul_apply, Fin.sum_univ_succ, F4.omega] <;> decide

private theorem __ch5_Theorem523A6Matrix_a6TailAdjacentCube (i : Fin 3) (hi : i ≠ 0) :
    __ch5_Theorem523A6Matrix_A6MatrixIsScalar
      ((__ch5_Theorem523A6Matrix_a6MatrixGenerator i.castSucc * __ch5_Theorem523A6Matrix_a6MatrixGenerator i.succ) ^ 3) := by
  fin_cases i <;> simp_all
  all_goals
    apply Matrix.ext
    intro r c
    fin_cases r <;> fin_cases c <;>
      apply F4.__ch5_Theorem523A6Matrix_coordinate_ext <;>
      norm_num [__ch5_Theorem523A6Matrix_a6MatrixGenerator, __ch5_Theorem523A6Matrix_a6MatG0, __ch5_Theorem523A6Matrix_a6MatG1, __ch5_Theorem523A6Matrix_a6MatG2, __ch5_Theorem523A6Matrix_a6MatG3,
        pow_succ, Matrix.mul_apply, Fin.sum_univ_succ, F4.omega] <;> decide

private theorem __ch5_Theorem523A6Matrix_a6RootFarSquare (j : Fin 4) (hj : 1 < j.val) :
    __ch5_Theorem523A6Matrix_A6MatrixIsScalar ((__ch5_Theorem523A6Matrix_a6MatrixGenerator 0 * __ch5_Theorem523A6Matrix_a6MatrixGenerator j) ^ 2) := by
  fin_cases j <;> simp_all
  all_goals
    apply Matrix.ext
    intro r c
    fin_cases r <;> fin_cases c <;>
      apply F4.__ch5_Theorem523A6Matrix_coordinate_ext <;>
      norm_num [__ch5_Theorem523A6Matrix_a6MatrixGenerator, __ch5_Theorem523A6Matrix_a6MatG0, __ch5_Theorem523A6Matrix_a6MatG1, __ch5_Theorem523A6Matrix_a6MatG2, __ch5_Theorem523A6Matrix_a6MatG3,
        pow_succ, Matrix.mul_apply, Fin.sum_univ_succ, F4.omega] <;> decide

private theorem __ch5_Theorem523A6Matrix_a6TailFarCommutator (i j : Fin 4)
    (hi : i ≠ 0) (hj : j ≠ 0)
    (hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    __ch5_Theorem523A6Matrix_A6MatrixIsScalar ⁅__ch5_Theorem523A6Matrix_a6MatrixGenerator i, __ch5_Theorem523A6Matrix_a6MatrixGenerator j⁆ := by
  fin_cases i <;> fin_cases j <;> simp_all
  all_goals
    have hcomm : Commute (__ch5_Theorem523A6Matrix_a6MatrixGenerator 1) (__ch5_Theorem523A6Matrix_a6MatrixGenerator 3) := by
      rw [commute_iff_eq]
      apply Matrix.GeneralLinearGroup.ext
      intro r c
      fin_cases r <;> fin_cases c <;>
        apply F4.__ch5_Theorem523A6Matrix_coordinate_ext <;>
        norm_num [__ch5_Theorem523A6Matrix_a6MatrixGenerator, __ch5_Theorem523A6Matrix_a6MatG1, __ch5_Theorem523A6Matrix_a6MatG3,
          Matrix.mul_apply, Fin.sum_univ_succ, F4.omega] <;> decide
    first
    | rw [hcomm.commutator_eq]
      rfl
    | rw [hcomm.symm.commutator_eq]
      rfl

private theorem __ch5_Theorem523A6Matrix_a6MatrixRelationCertificate :
    __ch5_Theorem523A6Matrix_A6MatrixIsScalar (__ch5_Theorem523A6Matrix_a6MatrixGenerator 0 ^ 3) ∧
    (∀ i : Fin 4, i ≠ 0 → __ch5_Theorem523A6Matrix_A6MatrixIsScalar (__ch5_Theorem523A6Matrix_a6MatrixGenerator i ^ 2)) ∧
    __ch5_Theorem523A6Matrix_A6MatrixIsScalar ((__ch5_Theorem523A6Matrix_a6MatrixGenerator 0 * __ch5_Theorem523A6Matrix_a6MatrixGenerator 1) ^ 3) ∧
    (∀ i : Fin 3, i ≠ 0 →
      __ch5_Theorem523A6Matrix_A6MatrixIsScalar
        ((__ch5_Theorem523A6Matrix_a6MatrixGenerator i.castSucc * __ch5_Theorem523A6Matrix_a6MatrixGenerator i.succ) ^ 3)) ∧
    (∀ j : Fin 4, 1 < j.val →
      __ch5_Theorem523A6Matrix_A6MatrixIsScalar ((__ch5_Theorem523A6Matrix_a6MatrixGenerator 0 * __ch5_Theorem523A6Matrix_a6MatrixGenerator j) ^ 2)) ∧
    (∀ i j : Fin 4, i ≠ 0 → j ≠ 0 →
      (i.val + 1 < j.val ∨ j.val + 1 < i.val) →
      __ch5_Theorem523A6Matrix_A6MatrixIsScalar ⁅__ch5_Theorem523A6Matrix_a6MatrixGenerator i, __ch5_Theorem523A6Matrix_a6MatrixGenerator j⁆) := by
  exact ⟨__ch5_Theorem523A6Matrix_a6RootCube, __ch5_Theorem523A6Matrix_a6TailSquare, __ch5_Theorem523A6Matrix_a6RootAdjacentCube,
    __ch5_Theorem523A6Matrix_a6TailAdjacentCube, __ch5_Theorem523A6Matrix_a6RootFarSquare, __ch5_Theorem523A6Matrix_a6TailFarCommutator⟩

private theorem __ch5_Theorem523A6Matrix_a6MatrixIsScalar_mem_center {x : __ch5_Theorem523A6Matrix_GL3F4}
    (hx : __ch5_Theorem523A6Matrix_A6MatrixIsScalar x) : x ∈ Subgroup.center __ch5_Theorem523A6Matrix_GL3F4 := by
  apply Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
  exact ⟨x.val 0 0, hx.symm⟩

private def __ch5_Theorem523A6Matrix_a6MatrixFree : AlternatingSuzukiFreeGroup 1 →* __ch5_Theorem523A6Matrix_GL3F4 :=
  FreeGroup.lift __ch5_Theorem523A6Matrix_a6MatrixGenerator

private theorem __ch5_Theorem523A6Matrix_a6MatrixRelator_mem_center (r : SuzukiRelator 1) :
    __ch5_Theorem523A6Matrix_a6MatrixFree r.word ∈ Subgroup.center __ch5_Theorem523A6Matrix_GL3F4 := by
  rcases __ch5_Theorem523A6Matrix_a6MatrixRelationCertificate with
    ⟨hroot, htail, hadj, htailAdj, hrootFar, htailFar⟩
  cases r with
  | rootCube =>
      apply __ch5_Theorem523A6Matrix_a6MatrixIsScalar_mem_center
      simpa [__ch5_Theorem523A6Matrix_a6MatrixFree, SuzukiRelator.word, suzukiFreeGenerator] using hroot
  | tailSquare i hi =>
      apply __ch5_Theorem523A6Matrix_a6MatrixIsScalar_mem_center
      simpa [__ch5_Theorem523A6Matrix_a6MatrixFree, SuzukiRelator.word, suzukiFreeGenerator] using htail i hi
  | rootAdjacentCube =>
      apply __ch5_Theorem523A6Matrix_a6MatrixIsScalar_mem_center
      simpa [__ch5_Theorem523A6Matrix_a6MatrixFree, SuzukiRelator.word, suzukiFreeGenerator] using hadj
  | tailAdjacentCube i hi =>
      apply __ch5_Theorem523A6Matrix_a6MatrixIsScalar_mem_center
      simpa [__ch5_Theorem523A6Matrix_a6MatrixFree, SuzukiRelator.word, suzukiFreeGenerator] using
        htailAdj i hi
  | rootFarSquare j hj =>
      apply __ch5_Theorem523A6Matrix_a6MatrixIsScalar_mem_center
      simpa [__ch5_Theorem523A6Matrix_a6MatrixFree, SuzukiRelator.word, suzukiFreeGenerator] using
        hrootFar j hj
  | tailFarCommutator i j hi hj hfar =>
      apply __ch5_Theorem523A6Matrix_a6MatrixIsScalar_mem_center
      simpa [__ch5_Theorem523A6Matrix_a6MatrixFree, SuzukiRelator.word, suzukiFreeGenerator] using
        htailFar i j hi hj hfar

private theorem __ch5_Theorem523A6Matrix_freeCentralKernel_le_ker_of_kernel_maps_to_center
    {F M : Type*} [Group F] [Group M]
    (K : Subgroup F) [K.Normal] (f : F →* M)
    (hK : K ≤ (Subgroup.center M).comap f) :
    FreeCentralExtension.freeCentralKernel K ≤ f.ker := by
  rw [FreeCentralExtension.freeCentralKernel, Subgroup.commutator_le]
  intro x _hx k hk
  rw [MonoidHom.mem_ker, map_commutatorElement]
  apply commutatorElement_eq_one_iff_commute.mpr
  exact Subgroup.mem_center_iff.mp (hK hk) (f x)

private theorem __ch5_Theorem523A6Matrix_a6Kernel_maps_to_center :
    alternatingSuzukiKernel 1 ≤ (Subgroup.center __ch5_Theorem523A6Matrix_GL3F4).comap __ch5_Theorem523A6Matrix_a6MatrixFree := by
  rw [alternatingSuzukiKernel_eq_normalClosure]
  apply Subgroup.normalClosure_le_normal
  intro x hx
  obtain ⟨r, rfl⟩ := hx
  exact __ch5_Theorem523A6Matrix_a6MatrixRelator_mem_center r

private def __ch5_Theorem523A6Matrix_a6MatrixHom : AlternatingFreeCentralGroup 1 →* __ch5_Theorem523A6Matrix_GL3F4 :=
  QuotientGroup.lift
    (FreeCentralExtension.freeCentralKernel (alternatingSuzukiKernel 1))
    __ch5_Theorem523A6Matrix_a6MatrixFree
    (__ch5_Theorem523A6Matrix_freeCentralKernel_le_ker_of_kernel_maps_to_center
      (alternatingSuzukiKernel 1) __ch5_Theorem523A6Matrix_a6MatrixFree __ch5_Theorem523A6Matrix_a6Kernel_maps_to_center)

private def __ch5_Theorem523A6Matrix_a6MatU3 : __ch5_Theorem523A6Matrix_GL3F4 := __ch5_Theorem523A6Matrix_a6MatG2 ^ 2
private def __ch5_Theorem523A6Matrix_a6MatU4 : __ch5_Theorem523A6Matrix_GL3F4 := __ch5_Theorem523A6Matrix_a6MatG3 ^ 2
private def __ch5_Theorem523A6Matrix_a6MatW3 : __ch5_Theorem523A6Matrix_GL3F4 := (__ch5_Theorem523A6Matrix_a6MatG0 * __ch5_Theorem523A6Matrix_a6MatG2) ^ 2
private def __ch5_Theorem523A6Matrix_a6MatW4 : __ch5_Theorem523A6Matrix_GL3F4 := (__ch5_Theorem523A6Matrix_a6MatG0 * __ch5_Theorem523A6Matrix_a6MatG3) ^ 2
private def __ch5_Theorem523A6Matrix_a6MatW : __ch5_Theorem523A6Matrix_GL3F4 := ⁅__ch5_Theorem523A6Matrix_a6MatG1, __ch5_Theorem523A6Matrix_a6MatG3⁆
private def __ch5_Theorem523A6Matrix_a6MatT3 : __ch5_Theorem523A6Matrix_GL3F4 := __ch5_Theorem523A6Matrix_a6MatW3 * __ch5_Theorem523A6Matrix_a6MatU3⁻¹
private def __ch5_Theorem523A6Matrix_a6MatT4 : __ch5_Theorem523A6Matrix_GL3F4 := __ch5_Theorem523A6Matrix_a6MatW4 * __ch5_Theorem523A6Matrix_a6MatU4⁻¹
private def __ch5_Theorem523A6Matrix_a6MatK : __ch5_Theorem523A6Matrix_GL3F4 := __ch5_Theorem523A6Matrix_a6MatW * __ch5_Theorem523A6Matrix_a6MatT4 * __ch5_Theorem523A6Matrix_a6MatT3⁻¹

private theorem __ch5_Theorem523A6Matrix_a6MatrixHom_a6k : __ch5_Theorem523A6Matrix_a6MatrixHom a6k = __ch5_Theorem523A6Matrix_a6MatK := by
  simp [__ch5_Theorem523A6Matrix_a6MatrixHom, __ch5_Theorem523A6Matrix_a6MatrixFree, a6k, a6t4, a6t3, a6w, a6w4,
    a6u4, a6w3, a6u3, a6FCGen, __ch5_Theorem523A6Matrix_a6MatK, __ch5_Theorem523A6Matrix_a6MatW, __ch5_Theorem523A6Matrix_a6MatT4, __ch5_Theorem523A6Matrix_a6MatT3,
    __ch5_Theorem523A6Matrix_a6MatW4, __ch5_Theorem523A6Matrix_a6MatU4, __ch5_Theorem523A6Matrix_a6MatW3, __ch5_Theorem523A6Matrix_a6MatU3, __ch5_Theorem523A6Matrix_a6MatrixGenerator, mul_assoc]

private theorem __ch5_Theorem523A6Matrix_a6MatK_order : orderOf __ch5_Theorem523A6Matrix_a6MatK = 3 :=
  orderOf_eq_prime (by decide) (by decide)

private theorem __ch5_Theorem523A6Matrix_a6MatrixHom_a6k_order : orderOf (__ch5_Theorem523A6Matrix_a6MatrixHom a6k) = 3 := by
  rw [__ch5_Theorem523A6Matrix_a6MatrixHom_a6k]
  exact __ch5_Theorem523A6Matrix_a6MatK_order

@[simp]
private theorem __ch5_Theorem523A6Matrix_a6MatrixHom_a6FCGen (i : Fin 4) :
    __ch5_Theorem523A6Matrix_a6MatrixHom (a6FCGen i) = __ch5_Theorem523A6Matrix_a6MatrixGenerator i := by
  simp [__ch5_Theorem523A6Matrix_a6MatrixHom, __ch5_Theorem523A6Matrix_a6MatrixFree, a6FCGen]

private def __ch5_Theorem523A6Matrix_a6MatStandardZ1 : __ch5_Theorem523A6Matrix_GL3F4 :=
  __ch5_Theorem523A6Matrix_a6MatG0 ^ 3 * __ch5_Theorem523A6Matrix_a6MatT3⁻¹

private def __ch5_Theorem523A6Matrix_a6MatStandardZ4 : __ch5_Theorem523A6Matrix_GL3F4 :=
  (__ch5_Theorem523A6Matrix_a6MatG2 * __ch5_Theorem523A6Matrix_a6MatG3) ^ 3 * (__ch5_Theorem523A6Matrix_a6MatG2 ^ 2 * __ch5_Theorem523A6Matrix_a6MatG3 ^ 2)⁻¹

private def __ch5_Theorem523A6Matrix_a6MatStandardX : __ch5_Theorem523A6Matrix_GL3F4 :=
  __ch5_Theorem523A6Matrix_a6MatG0 * __ch5_Theorem523A6Matrix_a6MatStandardZ1⁻¹

private def __ch5_Theorem523A6Matrix_a6MatStandardY : __ch5_Theorem523A6Matrix_GL3F4 :=
  __ch5_Theorem523A6Matrix_a6MatG3⁻¹ * __ch5_Theorem523A6Matrix_a6MatG2⁻¹ * __ch5_Theorem523A6Matrix_a6MatStandardZ4

private theorem __ch5_Theorem523A6Matrix_a6MatrixHom_standardLiftXFull :
    __ch5_Theorem523A6Matrix_a6MatrixHom a6StandardLiftXFull = __ch5_Theorem523A6Matrix_a6MatStandardX := by
  simp [a6StandardLiftXFull, a6z1, a6u1, a6t3, a6w3, a6u3,
    __ch5_Theorem523A6Matrix_a6MatStandardX, __ch5_Theorem523A6Matrix_a6MatStandardZ1, __ch5_Theorem523A6Matrix_a6MatT3, __ch5_Theorem523A6Matrix_a6MatW3, __ch5_Theorem523A6Matrix_a6MatU3,
    __ch5_Theorem523A6Matrix_a6MatrixGenerator]

private theorem __ch5_Theorem523A6Matrix_a6MatrixHom_standardLiftYFull :
    __ch5_Theorem523A6Matrix_a6MatrixHom a6StandardLiftYFull = __ch5_Theorem523A6Matrix_a6MatStandardY := by
  simp [a6StandardLiftYFull, a6z4, a6v3, a6u3, a6u4,
    __ch5_Theorem523A6Matrix_a6MatStandardY, __ch5_Theorem523A6Matrix_a6MatStandardZ4, __ch5_Theorem523A6Matrix_a6MatrixGenerator]

private theorem __ch5_Theorem523A6Matrix_a6MatStandardCommutator_order :
    orderOf ⁅__ch5_Theorem523A6Matrix_a6MatStandardX, __ch5_Theorem523A6Matrix_a6MatStandardY⁆ = 3 := by
  exact orderOf_eq_prime (by decide) (by decide)

private theorem __ch5_Theorem523A6Matrix_a6StandardDetector_commutator_order :
    orderOf
      ((__ch5_Theorem523A6Matrix_a6MatrixHom.comp (AlternatingFreeCentralDerived 1).subtype)
        ⁅a6StandardLiftX, a6StandardLiftY⁆) = 3 := by
  rw [map_commutatorElement]
  change orderOf
    ⁅__ch5_Theorem523A6Matrix_a6MatrixHom a6StandardLiftXFull,
      __ch5_Theorem523A6Matrix_a6MatrixHom a6StandardLiftYFull⁆ = 3
  rw [__ch5_Theorem523A6Matrix_a6MatrixHom_standardLiftXFull, __ch5_Theorem523A6Matrix_a6MatrixHom_standardLiftYFull]
  exact __ch5_Theorem523A6Matrix_a6MatStandardCommutator_order

public theorem exists_a6StandardDetector :
    ∃ (M : Type) (_ : Group M)
      (detector : AlternatingFreeCentralDerived 1 →* M),
      orderOf (detector ⁅a6StandardLiftX, a6StandardLiftY⁆) = 3 := by
  exact ⟨__ch5_Theorem523A6Matrix_GL3F4, inferInstance,
    __ch5_Theorem523A6Matrix_a6MatrixHom.comp (AlternatingFreeCentralDerived 1).subtype,
    __ch5_Theorem523A6Matrix_a6StandardDetector_commutator_order⟩


end ExceptionalMatrix


public theorem a6UniversalKernel_three_dvd_new :
    3 ∣ Nat.card
      (alternatingFreeCentralCovering 1).toMonoidHom.ker := by
  change 3 ∣ Nat.card (alternatingFreeCentralDerivedProjection 1).ker
  rw [a6DerivedProjection_ker_eq_zpowers, Nat.card_zpowers]
  let f := ExceptionalMatrix.__ch5_Theorem523A6Matrix_a6MatrixHom.comp
    (AlternatingFreeCentralDerived 1).subtype
  have hdiv := orderOf_map_dvd f a6DerivedK
  have horder : orderOf (f a6DerivedK) = 3 := by
    change orderOf (ExceptionalMatrix.__ch5_Theorem523A6Matrix_a6MatrixHom a6k) = 3
    exact ExceptionalMatrix.__ch5_Theorem523A6Matrix_a6MatrixHom_a6k_order
  simpa only [horder] using hdiv

end GLS3.Chapter5.SchurPresentation
/- END Theory.Theorem523A6Matrix -/

