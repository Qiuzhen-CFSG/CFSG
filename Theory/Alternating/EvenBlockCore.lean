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

public import Theory.Alternating.EvenBlockReduction
set_option linter.style.nameCheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

/- Chapter 5-specific declarations, kept out of the general Theory library. -/

/- BEGIN Theory.EvenBlockCore -/
noncomputable section
set_option maxHeartbeats 800000

namespace GLS3.Chapter5.SchurPresentation

public def evenBlockLeftPoint (qA qB : Nat) (i : Fin (qA + 5)) :
    Fin ((qA + 5) + (qB + 5)) :=
  finSumFinEquiv (Sum.inl i)

public def evenBlockRightPoint (qA qB : Nat) (i : Fin (qB + 5)) :
    Fin ((qA + 5) + (qB + 5)) :=
  finSumFinEquiv (Sum.inr i)

public theorem permCongr_swap'
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (i j : α) :
    e.permCongr (Equiv.swap i j) = Equiv.swap (e i) (e j) := by
  apply Equiv.ext
  intro x
  obtain ⟨x, rfl⟩ := e.surjective x
  rw [Equiv.permCongr_apply, e.symm_apply_apply]
  exact e.injective.map_swap i j x

public theorem evenBlockLeftPoint_injective (qA qB : Nat) :
    Function.Injective (evenBlockLeftPoint qA qB) :=
  finSumFinEquiv.injective.comp Sum.inl_injective

public theorem evenBlockRightPoint_injective (qA qB : Nat) :
    Function.Injective (evenBlockRightPoint qA qB) :=
  finSumFinEquiv.injective.comp Sum.inr_injective

public theorem evenBlockLeftPoint_ne_right
    (qA qB : Nat) (i : Fin (qA + 5)) (j : Fin (qB + 5)) :
    evenBlockLeftPoint qA qB i ≠ evenBlockRightPoint qA qB j := by
  intro h
  have h' := finSumFinEquiv.injective h
  cases h'

public theorem root_p0_ne_p1 (q : Nat) :
    RootFourSubgroup.p0 q ≠ RootFourSubgroup.p1 q := by
  intro h
  have := congrArg Fin.val h
  simp [RootFourSubgroup.p0, RootFourSubgroup.p1] at this

public theorem permProdBlockHom_swap_left
    (qA qB : Nat) (i j : Fin (qA + 5)) :
    permProdBlockHom (qA + 5) (qB + 5) (Equiv.swap i j, 1) =
      Equiv.swap (evenBlockLeftPoint qA qB i)
        (evenBlockLeftPoint qA qB j) := by
  rw [permProdBlockHom_apply, Equiv.Perm.sumCongr_swap_one,
    permCongr_swap']
  rfl

public theorem permProdBlockHom_swap_right
    (qA qB : Nat) (i j : Fin (qB + 5)) :
    permProdBlockHom (qA + 5) (qB + 5) (1, Equiv.swap i j) =
      Equiv.swap (evenBlockRightPoint qA qB i)
        (evenBlockRightPoint qA qB j) := by
  rw [permProdBlockHom_apply, Equiv.Perm.sumCongr_one_swap,
    permCongr_swap']
  rfl

public def evenBlockOddPair (qA qB : Nat) :
    evenBlockProductGroup (qA + 5) (qB + 5) :=
  ⟨(Equiv.swap (RootFourSubgroup.p0 qA) (RootFourSubgroup.p1 qA),
      Equiv.swap (RootFourSubgroup.p0 qB) (RootFourSubgroup.p1 qB)), by
    change permProdBlockHom (qA + 5) (qB + 5) _ ∈
      alternatingGroup (Fin ((qA + 5) + (qB + 5)))
    rw [Equiv.Perm.mem_alternatingGroup, permProdBlockHom_apply,
      Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr,
      Equiv.Perm.sign_swap, Equiv.Perm.sign_swap]
    · norm_num
    · exact root_p0_ne_p1 qB
    · exact root_p0_ne_p1 qA⟩

public theorem evenBlockParityHom_oddPair (qA qB : Nat) :
    evenBlockParityHom (qA + 5) (qB + 5) (evenBlockOddPair qA qB) = -1 := by
  change Equiv.Perm.sign
      (Equiv.swap (RootFourSubgroup.p0 qA) (RootFourSubgroup.p1 qA)) = -1
  exact Equiv.Perm.sign_swap (root_p0_ne_p1 qA)

public def evenBlockParityConjugatorPerm (qA qB : Nat) :
    Equiv.Perm (Fin ((qA + 5) + (qB + 5))) :=
  Equiv.swap
      (evenBlockLeftPoint qA qB (RootFourSubgroup.p2 qA))
      (evenBlockRightPoint qA qB (RootFourSubgroup.p0 qB)) *
    Equiv.swap
      (evenBlockLeftPoint qA qB (RootFourSubgroup.p3 qA))
      (evenBlockRightPoint qA qB (RootFourSubgroup.p1 qB))

public theorem sign_evenBlockParityConjugatorPerm (qA qB : Nat) :
    Equiv.Perm.sign (evenBlockParityConjugatorPerm qA qB) = 1 := by
  rw [evenBlockParityConjugatorPerm, map_mul,
    Equiv.Perm.sign_swap, Equiv.Perm.sign_swap]
  · norm_num
  · exact evenBlockLeftPoint_ne_right qA qB _ _
  · exact evenBlockLeftPoint_ne_right qA qB _ _

public def evenBlockParityConjugator (qA qB : Nat) :
    alternatingGroup (Fin ((qA + 5) + (qB + 5))) :=
  ⟨evenBlockParityConjugatorPerm qA qB, by
    rw [Equiv.Perm.mem_alternatingGroup,
      sign_evenBlockParityConjugatorPerm]⟩

@[simp]
public theorem coe_evenBlockParityConjugator (qA qB : Nat) :
    ((evenBlockParityConjugator qA qB :
      alternatingGroup (Fin ((qA + 5) + (qB + 5)))) :
        Equiv.Perm (Fin ((qA + 5) + (qB + 5)))) =
      evenBlockParityConjugatorPerm qA qB := by
  rfl

public theorem evenBlockParityConjugatorPerm_p0 (qA qB : Nat) :
    evenBlockParityConjugatorPerm qA qB
        (evenBlockLeftPoint qA qB (RootFourSubgroup.p0 qA)) =
      evenBlockLeftPoint qA qB (RootFourSubgroup.p0 qA) := by
  have h03 : RootFourSubgroup.p0 qA ≠ RootFourSubgroup.p3 qA := by
    intro h; have := congrArg Fin.val h
    simp [RootFourSubgroup.p0, RootFourSubgroup.p3] at this
  have h02 : RootFourSubgroup.p0 qA ≠ RootFourSubgroup.p2 qA := by
    intro h; have := congrArg Fin.val h
    simp [RootFourSubgroup.p0, RootFourSubgroup.p2] at this
  rw [evenBlockParityConjugatorPerm, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne
      ((evenBlockLeftPoint_injective qA qB).ne h03)
      (evenBlockLeftPoint_ne_right qA qB _ _),
    Equiv.swap_apply_of_ne_of_ne
      ((evenBlockLeftPoint_injective qA qB).ne h02)
      (evenBlockLeftPoint_ne_right qA qB _ _)]

public theorem evenBlockParityConjugatorPerm_p1 (qA qB : Nat) :
    evenBlockParityConjugatorPerm qA qB
        (evenBlockLeftPoint qA qB (RootFourSubgroup.p1 qA)) =
      evenBlockLeftPoint qA qB (RootFourSubgroup.p1 qA) := by
  have h13 : RootFourSubgroup.p1 qA ≠ RootFourSubgroup.p3 qA := by
    intro h; have := congrArg Fin.val h
    simp [RootFourSubgroup.p1, RootFourSubgroup.p3] at this
  have h12 : RootFourSubgroup.p1 qA ≠ RootFourSubgroup.p2 qA := by
    intro h; have := congrArg Fin.val h
    simp [RootFourSubgroup.p1, RootFourSubgroup.p2] at this
  rw [evenBlockParityConjugatorPerm, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne
      ((evenBlockLeftPoint_injective qA qB).ne h13)
      (evenBlockLeftPoint_ne_right qA qB _ _),
    Equiv.swap_apply_of_ne_of_ne
      ((evenBlockLeftPoint_injective qA qB).ne h12)
      (evenBlockLeftPoint_ne_right qA qB _ _)]

public theorem evenBlockParityConjugatorPerm_p2 (qA qB : Nat) :
    evenBlockParityConjugatorPerm qA qB
        (evenBlockLeftPoint qA qB (RootFourSubgroup.p2 qA)) =
      evenBlockRightPoint qA qB (RootFourSubgroup.p0 qB) := by
  have h23 : RootFourSubgroup.p2 qA ≠ RootFourSubgroup.p3 qA := by
    intro h; have := congrArg Fin.val h
    simp [RootFourSubgroup.p2, RootFourSubgroup.p3] at this
  rw [evenBlockParityConjugatorPerm, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne
      ((evenBlockLeftPoint_injective qA qB).ne h23)
      (evenBlockLeftPoint_ne_right qA qB _ _),
    Equiv.swap_apply_left]

public theorem evenBlockParityConjugatorPerm_p3 (qA qB : Nat) :
    evenBlockParityConjugatorPerm qA qB
        (evenBlockLeftPoint qA qB (RootFourSubgroup.p3 qA)) =
      evenBlockRightPoint qA qB (RootFourSubgroup.p1 qB) := by
  have h10 : RootFourSubgroup.p1 qB ≠ RootFourSubgroup.p0 qB :=
    (root_p0_ne_p1 qB).symm
  rw [evenBlockParityConjugatorPerm, Equiv.Perm.mul_apply,
    Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne
      (evenBlockLeftPoint_ne_right qA qB _ _).symm
      ((evenBlockRightPoint_injective qA qB).ne h10)]

public theorem evenBlockParityConjugator_conj_left_rho1 (qA qB : Nat) :
    evenBlockParityConjugator qA qB *
        alternatingProdBlockHom (qA + 5) (qB + 5)
          ((⟨RootFourSubgroup.rho1 qA,
              RootFourSubgroup.rho1_mem_alternating qA⟩ :
                alternatingGroup (Fin (qA + 5))), 1) *
        (evenBlockParityConjugator qA qB)⁻¹ =
      evenBlockProductHom (qA + 5) (qB + 5)
        (evenBlockOddPair qA qB) := by
  apply Subtype.ext
  let s := evenBlockParityConjugatorPerm qA qB
  let l0 := evenBlockLeftPoint qA qB (RootFourSubgroup.p0 qA)
  let l1 := evenBlockLeftPoint qA qB (RootFourSubgroup.p1 qA)
  let l2 := evenBlockLeftPoint qA qB (RootFourSubgroup.p2 qA)
  let l3 := evenBlockLeftPoint qA qB (RootFourSubgroup.p3 qA)
  let r0 := evenBlockRightPoint qA qB (RootFourSubgroup.p0 qB)
  let r1 := evenBlockRightPoint qA qB (RootFourSubgroup.p1 qB)
  have hleft :
      permProdBlockHom (qA + 5) (qB + 5)
          (RootFourSubgroup.rho1 qA, 1) =
        Equiv.swap l0 l1 * Equiv.swap l2 l3 := by
    rw [RootFourSubgroup.rho1]
    change permProdBlockHom (qA + 5) (qB + 5)
        ((Equiv.swap _ _ , 1) * (Equiv.swap _ _, 1)) = _
    rw [map_mul, permProdBlockHom_swap_left,
      permProdBlockHom_swap_left]
  have htarget :
      permProdBlockHom (qA + 5) (qB + 5)
          (evenBlockOddPair qA qB :
            Equiv.Perm (Fin (qA + 5)) × Equiv.Perm (Fin (qB + 5))) =
        Equiv.swap l0 l1 * Equiv.swap r0 r1 := by
    change permProdBlockHom (qA + 5) (qB + 5)
        ((Equiv.swap _ _, 1) * (1, Equiv.swap _ _)) = _
    rw [map_mul, permProdBlockHom_swap_left,
      permProdBlockHom_swap_right]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [coe_evenBlockParityConjugator,
    coe_alternatingProdBlockHom_apply,
    coe_evenBlockProductHom_apply]
  change s * permProdBlockHom (qA + 5) (qB + 5)
      (RootFourSubgroup.rho1 qA, 1) * s⁻¹ =
    permProdBlockHom (qA + 5) (qB + 5)
      (evenBlockOddPair qA qB :
        Equiv.Perm (Fin (qA + 5)) × Equiv.Perm (Fin (qB + 5)))
  rw [hleft, htarget]
  calc
    s * (Equiv.swap l0 l1 * Equiv.swap l2 l3) * s⁻¹ =
        (s * Equiv.swap l0 l1 * s⁻¹) *
          (s * Equiv.swap l2 l3 * s⁻¹) := by group
    _ = Equiv.swap (s l0) (s l1) * Equiv.swap (s l2) (s l3) := by
      rw [Equiv.swap_apply_apply, Equiv.swap_apply_apply]
    _ = Equiv.swap l0 l1 * Equiv.swap r0 r1 := by
      rw [evenBlockParityConjugatorPerm_p0,
        evenBlockParityConjugatorPerm_p1,
        evenBlockParityConjugatorPerm_p2,
        evenBlockParityConjugatorPerm_p3]

@[expose] public def alternatingBlockPreimageToEvenBlockPreimage
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b))) :
    alternatingBlockPreimage a b f →* evenBlockPreimage a b f :=
  (alternatingBlockPreimage a b f).subtype.codRestrict
    (evenBlockPreimage a b f) (fun x => by
      obtain ⟨y, hy⟩ := x.2
      refine ⟨evenBlockAlternatingHom a b y, ?_⟩
      exact (DFunLike.congr_fun
        (evenBlockProductHom_comp_evenBlockAlternatingHom a b) y).trans hy)

public theorem evenBlockPreimageProjection_alternatingEmbedding
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b)))
    (x : alternatingBlockPreimage a b f) :
    evenBlockPreimageProjection a b f
        (alternatingBlockPreimageToEvenBlockPreimage a b f x) =
      evenBlockAlternatingHom a b
        (alternatingBlockPreimageProjection a b f x) := by
  apply evenBlockProductHom_injective a b
  calc
    evenBlockProductHom a b
        (evenBlockPreimageProjection a b f
          (alternatingBlockPreimageToEvenBlockPreimage a b f x)) = f x :=
      evenBlockPreimageProjection_fac a b f _
    _ = alternatingProdBlockHom a b
        (alternatingBlockPreimageProjection a b f x) :=
      (alternatingBlockPreimageProjection_fac a b f x).symm
    _ = evenBlockProductHom a b
        (evenBlockAlternatingHom a b
          (alternatingBlockPreimageProjection a b f x)) := by
      exact (DFunLike.congr_fun
        (evenBlockProductHom_comp_evenBlockAlternatingHom a b) _).symm

public def evenBlockConjOnAlternatingPreimage
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b)))
    (u : evenBlockPreimage a b f) :
    alternatingBlockPreimage a b f →*
      alternatingBlockPreimage a b f where
  toFun x := ⟨(u : H) * (x : H) * (u : H)⁻¹, by
    let j := alternatingBlockPreimageToEvenBlockPreimage a b f
    let parity := evenBlockPreimageParity a b f
    have hjker : j x ∈ parity.ker := by
      rw [evenBlockPreimageParity_ker_eq_alternatingBlockPreimage_comap]
      exact x.2
    have hzker : u * j x * u⁻¹ ∈ parity.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv,
        MonoidHom.mem_ker.mp hjker]
      simp
    rw [evenBlockPreimageParity_ker_eq_alternatingBlockPreimage_comap]
      at hzker
    exact hzker⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    change (u : H) * ((x : H) * (y : H)) * (u : H)⁻¹ =
      ((u : H) * (x : H) * (u : H)⁻¹) *
        ((u : H) * (y : H) * (u : H)⁻¹)
    group

public theorem evenBlockConjOnAlternatingPreimage_projection
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b)))
    (u : evenBlockPreimage a b f)
    (x : alternatingBlockPreimage a b f) :
    evenBlockAlternatingHom a b
        (alternatingBlockPreimageProjection a b f
          (evenBlockConjOnAlternatingPreimage a b f u x)) =
      evenBlockPreimageProjection a b f u *
        evenBlockAlternatingHom a b
          (alternatingBlockPreimageProjection a b f x) *
        (evenBlockPreimageProjection a b f u)⁻¹ := by
  let j := alternatingBlockPreimageToEvenBlockPreimage a b f
  let c := evenBlockConjOnAlternatingPreimage a b f u
  calc
    evenBlockAlternatingHom a b
        (alternatingBlockPreimageProjection a b f (c x)) =
        evenBlockPreimageProjection a b f (j (c x)) :=
      (evenBlockPreimageProjection_alternatingEmbedding a b f (c x)).symm
    _ = evenBlockPreimageProjection a b f (u * j x * u⁻¹) := by
      rfl
    _ = _ := by
      rw [map_mul, map_mul, map_inv,
        evenBlockPreimageProjection_alternatingEmbedding]

public def evenBlockConjOnLeftPreimage
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b)))
    (u : evenBlockPreimage a b f) :
    prodLeftPreimage (alternatingBlockPreimageProjection a b f) →*
      prodLeftPreimage (alternatingBlockPreimageProjection a b f) where
  toFun x := ⟨evenBlockConjOnAlternatingPreimage a b f u x, by
    let r := alternatingBlockPreimageProjection a b f
    have hproj := evenBlockConjOnAlternatingPreimage_projection
      a b f u (x : alternatingBlockPreimage a b f)
    have hsnd := congrArg (fun z : evenBlockProductGroup a b =>
      (z : Equiv.Perm (Fin a) × Equiv.Perm (Fin b)).2) hproj
    change (↑(r (evenBlockConjOnAlternatingPreimage a b f u x)).2 :
        Equiv.Perm (Fin b)) =
      (evenBlockPreimageProjection a b f u :
          Equiv.Perm (Fin a) × Equiv.Perm (Fin b)).2 *
        (↑(r (x : alternatingBlockPreimage a b f)).2 :
          Equiv.Perm (Fin b)) *
        ((evenBlockPreimageProjection a b f u :
          Equiv.Perm (Fin a) × Equiv.Perm (Fin b)).2)⁻¹ at hsnd
    have hxright : (r (x : alternatingBlockPreimage a b f)).2 = 1 :=
      Subgroup.mem_bot.mp x.2.2
    have hsnd' : (r (evenBlockConjOnAlternatingPreimage a b f u x)).2 = 1 := by
      apply Subtype.ext
      change (((r (evenBlockConjOnAlternatingPreimage a b f u x)).2 :
        alternatingGroup (Fin b)) : Equiv.Perm (Fin b)) = 1
      rw [hsnd]
      have hxright' := congrArg Subtype.val hxright
      rw [hxright']
      simp
    exact ⟨trivial, Subgroup.mem_bot.mpr hsnd'⟩⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (evenBlockConjOnAlternatingPreimage a b f u)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (evenBlockConjOnAlternatingPreimage a b f u)
      (x : alternatingBlockPreimage a b f)
      (y : alternatingBlockPreimage a b f)

public def evenBlockConjOnRightPreimage
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b)))
    (u : evenBlockPreimage a b f) :
    prodRightPreimage (alternatingBlockPreimageProjection a b f) →*
      prodRightPreimage (alternatingBlockPreimageProjection a b f) where
  toFun x := ⟨evenBlockConjOnAlternatingPreimage a b f u x, by
    let r := alternatingBlockPreimageProjection a b f
    have hproj := evenBlockConjOnAlternatingPreimage_projection
      a b f u (x : alternatingBlockPreimage a b f)
    have hfst := congrArg (fun z : evenBlockProductGroup a b =>
      (z : Equiv.Perm (Fin a) × Equiv.Perm (Fin b)).1) hproj
    change (↑(r (evenBlockConjOnAlternatingPreimage a b f u x)).1 :
        Equiv.Perm (Fin a)) =
      (evenBlockPreimageProjection a b f u :
          Equiv.Perm (Fin a) × Equiv.Perm (Fin b)).1 *
        (↑(r (x : alternatingBlockPreimage a b f)).1 :
          Equiv.Perm (Fin a)) *
        ((evenBlockPreimageProjection a b f u :
          Equiv.Perm (Fin a) × Equiv.Perm (Fin b)).1)⁻¹ at hfst
    have hxleft : (r (x : alternatingBlockPreimage a b f)).1 = 1 :=
      Subgroup.mem_bot.mp x.2.1
    have hfst' : (r (evenBlockConjOnAlternatingPreimage a b f u x)).1 = 1 := by
      apply Subtype.ext
      change (((r (evenBlockConjOnAlternatingPreimage a b f u x)).1 :
        alternatingGroup (Fin a)) : Equiv.Perm (Fin a)) = 1
      rw [hfst]
      have hxleft' := congrArg Subtype.val hxleft
      rw [hxleft']
      simp
    exact ⟨Subgroup.mem_bot.mpr hfst', trivial⟩⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (evenBlockConjOnAlternatingPreimage a b f u)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (evenBlockConjOnAlternatingPreimage a b f u)
      (x : alternatingBlockPreimage a b f)
      (y : alternatingBlockPreimage a b f)

public def evenBlockConjOnLeftDerived
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b)))
    (u : evenBlockPreimage a b f) :
    prodLeftPreimageDerived (alternatingBlockPreimageProjection a b f) →*
      prodLeftPreimageDerived (alternatingBlockPreimageProjection a b f) :=
  let φ := evenBlockConjOnLeftPreimage a b f u
  (φ.comp (commutator (prodLeftPreimage
      (alternatingBlockPreimageProjection a b f))).subtype).codRestrict
    (commutator (prodLeftPreimage
      (alternatingBlockPreimageProjection a b f))) (fun x => by
      have hmap : (commutator (prodLeftPreimage
          (alternatingBlockPreimageProjection a b f))).map φ ≤
          commutator (prodLeftPreimage
            (alternatingBlockPreimageProjection a b f)) := by
        rw [map_commutator_eq]
        exact Subgroup.commutator_mono le_top le_top
      apply hmap
      exact ⟨x, x.2, rfl⟩)

public theorem evenBlockConjOnLeftDerived_embedding_general
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b)))
    (u : evenBlockPreimage a b f)
    (x : prodLeftPreimageDerived
      (alternatingBlockPreimageProjection a b f)) :
    evenBlockLeftDerivedEmbedding a b f
        (evenBlockConjOnLeftDerived a b f u x) =
      (u : H) * evenBlockLeftDerivedEmbedding a b f x * (u : H)⁻¹ := by
  rfl

public def evenBlockConjOnRightDerived
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b)))
    (u : evenBlockPreimage a b f) :
    prodRightPreimageDerived (alternatingBlockPreimageProjection a b f) →*
      prodRightPreimageDerived (alternatingBlockPreimageProjection a b f) :=
  let φ := evenBlockConjOnRightPreimage a b f u
  (φ.comp (commutator (prodRightPreimage
      (alternatingBlockPreimageProjection a b f))).subtype).codRestrict
    (commutator (prodRightPreimage
      (alternatingBlockPreimageProjection a b f))) (fun x => by
      have hmap : (commutator (prodRightPreimage
          (alternatingBlockPreimageProjection a b f))).map φ ≤
          commutator (prodRightPreimage
            (alternatingBlockPreimageProjection a b f)) := by
        rw [map_commutator_eq]
        exact Subgroup.commutator_mono le_top le_top
      apply hmap
      exact ⟨x, x.2, rfl⟩)

public def evenBlockComponentDerivedProductInEvenBlock
    {H : Type} [Group H] [Finite H]
    (qA qB : Nat)
    (f : H →* alternatingGroup (Fin ((qA + 5) + (qB + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H) :
    Subgroup (evenBlockPreimage (qA + 5) (qB + 5) f) :=
  ((alternatingBlockPreimageToEvenBlockPreimage
      (qA + 5) (qB + 5) f).comp
    (evenBlockComponentDerivedMulHom qA qB f hf hker)).range

public theorem evenBlockComponentDerivedProductInEvenBlock_apply
    {H : Type} [Group H] [Finite H]
    (qA qB : Nat)
    (f : H →* alternatingGroup (Fin ((qA + 5) + (qB + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (x : prodLeftPreimageDerived
          (alternatingBlockPreimageProjection (qA + 5) (qB + 5) f) ×
        prodRightPreimageDerived
          (alternatingBlockPreimageProjection (qA + 5) (qB + 5) f)) :
    ((((alternatingBlockPreimageToEvenBlockPreimage
        (qA + 5) (qB + 5) f).comp
      (evenBlockComponentDerivedMulHom qA qB f hf hker)) x :
        evenBlockPreimage (qA + 5) (qB + 5) f) : H) =
      evenBlockLeftDerivedEmbedding (qA + 5) (qB + 5) f x.1 *
        evenBlockRightDerivedEmbedding (qA + 5) (qB + 5) f x.2 := by
  rfl

public theorem evenBlockConjOnLeftDerived_embedding
    {H : Type} [Group H] [Finite H]
    (qA qB : Nat)
    (f : H →* alternatingGroup (Fin ((qA + 5) + (qB + 5))))
    (u : evenBlockPreimage (qA + 5) (qB + 5) f)
    (x : prodLeftPreimageDerived
      (alternatingBlockPreimageProjection (qA + 5) (qB + 5) f)) :
    evenBlockLeftDerivedEmbedding (qA + 5) (qB + 5) f
        (evenBlockConjOnLeftDerived (qA + 5) (qB + 5) f u x) =
      (u : H) * evenBlockLeftDerivedEmbedding
        (qA + 5) (qB + 5) f x * (u : H)⁻¹ := by
  rfl

public theorem evenBlockConjOnRightDerived_embedding
    {H : Type} [Group H] [Finite H]
    (qA qB : Nat)
    (f : H →* alternatingGroup (Fin ((qA + 5) + (qB + 5))))
    (u : evenBlockPreimage (qA + 5) (qB + 5) f)
    (x : prodRightPreimageDerived
      (alternatingBlockPreimageProjection (qA + 5) (qB + 5) f)) :
    evenBlockRightDerivedEmbedding (qA + 5) (qB + 5) f
        (evenBlockConjOnRightDerived (qA + 5) (qB + 5) f u x) =
      (u : H) * evenBlockRightDerivedEmbedding
        (qA + 5) (qB + 5) f x * (u : H)⁻¹ := by
  rfl

public theorem evenBlockComponentDerivedProductInEvenBlock_conj_mem
    {H : Type} [Group H] [Finite H]
    (qA qB : Nat)
    (f : H →* alternatingGroup (Fin ((qA + 5) + (qB + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (u z : evenBlockPreimage (qA + 5) (qB + 5) f)
    (hz : z ∈ evenBlockComponentDerivedProductInEvenBlock
      qA qB f hf hker) :
    u * z * u⁻¹ ∈ evenBlockComponentDerivedProductInEvenBlock
      qA qB f hf hker := by
  obtain ⟨x, rfl⟩ := hz
  let cL := evenBlockConjOnLeftDerived (qA + 5) (qB + 5) f u
  let cR := evenBlockConjOnRightDerived (qA + 5) (qB + 5) f u
  refine ⟨(cL x.1, cR x.2), ?_⟩
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [evenBlockComponentDerivedProductInEvenBlock_apply,
    evenBlockComponentDerivedProductInEvenBlock_apply,
    evenBlockConjOnLeftDerived_embedding,
    evenBlockConjOnRightDerived_embedding]
  group

public theorem evenBlockComponentDerivedProductInEvenBlock_zpowers_le_normalizer
    {H : Type} [Group H] [Finite H]
    (qA qB : Nat)
    (f : H →* alternatingGroup (Fin ((qA + 5) + (qB + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (u : evenBlockPreimage (qA + 5) (qB + 5) f) :
    Subgroup.zpowers u ≤ Subgroup.normalizer
      (evenBlockComponentDerivedProductInEvenBlock qA qB f hf hker) := by
  rw [Subgroup.zpowers_le]
  rw [Subgroup.mem_set_normalizer_iff]
  intro z
  constructor
  · exact evenBlockComponentDerivedProductInEvenBlock_conj_mem
      qA qB f hf hker u z
  · intro hz
    have h := evenBlockComponentDerivedProductInEvenBlock_conj_mem
      qA qB f hf hker u⁻¹ (u * z * u⁻¹) hz
    have heq : u⁻¹ * (u * z * u⁻¹) * u = z := by group
    rw [inv_inv] at h
    rw [heq] at h
    exact h

@[expose] public def evenBlockCommonDerivedKernelInEvenBlock
    {H : Type} [Group H] [Finite H]
    (qA qB : Nat)
    (f : H →* alternatingGroup (Fin ((qA + 5) + (qB + 5)))) :
    Subgroup (evenBlockPreimage (qA + 5) (qB + 5) f) :=
  (evenBlockLeftDerivedKernelInBlock (qA + 5) (qB + 5) f).map
    (alternatingBlockPreimageToEvenBlockPreimage
      (qA + 5) (qB + 5) f)

public theorem evenBlockKernel_inf_componentProductInEvenBlock_eq_of_fusion
    {H : Type} [Group H] [Finite H]
    (qA qB : Nat)
    (f : H →* alternatingGroup (Fin ((qA + 5) + (qB + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hfusion : evenBlockLeftDerivedKernelInBlock
        (qA + 5) (qB + 5) f =
      evenBlockRightDerivedKernelInBlock (qA + 5) (qB + 5) f) :
    (f.ker.comap (evenBlockPreimage (qA + 5) (qB + 5) f).subtype) ⊓
        evenBlockComponentDerivedProductInEvenBlock qA qB f hf hker =
      evenBlockCommonDerivedKernelInEvenBlock qA qB f := by
  let E := alternatingBlockPreimage (qA + 5) (qB + 5) f
  let B := evenBlockPreimage (qA + 5) (qB + 5) f
  let r := alternatingBlockPreimageProjection (qA + 5) (qB + 5) f
  let j := alternatingBlockPreimageToEvenBlockPreimage
    (qA + 5) (qB + 5) f
  let m := evenBlockComponentDerivedMulHom qA qB f hf hker
  let C := evenBlockLeftDerivedKernelInBlock (qA + 5) (qB + 5) f
  have hinf : r.ker ⊓ evenBlockComponentDerivedProduct qA qB f hf hker = C :=
    evenBlockComponentDerivedProduct_ker_inf_eq_of_kernel_eq
      qA qB f hf hker hfusion
  ext z
  constructor
  · rintro ⟨hzK, hzL⟩
    obtain ⟨x, rfl⟩ := hzL
    let e : E := m x
    have heK : e ∈ r.ker := by
      rw [alternatingBlockPreimageProjection_ker_eq_comap]
      exact hzK
    have heL : e ∈ evenBlockComponentDerivedProduct qA qB f hf hker :=
      ⟨x, rfl⟩
    have heC : e ∈ C := by
      rw [← hinf]
      exact ⟨heK, heL⟩
    exact ⟨e, heC, rfl⟩
  · rintro ⟨e, heC, rfl⟩
    have heInf : e ∈ r.ker ⊓
        evenBlockComponentDerivedProduct qA qB f hf hker := by
      rw [hinf]
      exact heC
    constructor
    · rw [alternatingBlockPreimageProjection_ker_eq_comap] at heInf
      exact heInf.1
    · obtain ⟨x, hx⟩ := heInf.2
      exact ⟨x, congrArg j hx⟩

public theorem kernel_inf_sup_zpowers_eq_of_parity_of_square_mem
    {B : Type*} [Group B]
    (parity : B →* ℤˣ)
    (K L C : Subgroup B) (u : B)
    (hKparity : K ≤ parity.ker)
    (hLparity : L ≤ parity.ker)
    (huParity : parity u = -1)
    (hKinfL : K ⊓ L = C)
    (hu2C : u ^ 2 ∈ C)
    (hnormalizes : Subgroup.zpowers u ≤ Subgroup.normalizer L) :
    K ⊓ (Subgroup.zpowers u ⊔ L) = C := by
  have hCleK : C ≤ K := by
    rw [← hKinfL]
    exact inf_le_left
  have hCleL : C ≤ L := by
    rw [← hKinfL]
    exact inf_le_right
  apply le_antisymm
  · rintro x ⟨hxK, hxD⟩
    have hxSet : x ∈ (↑(Subgroup.zpowers u ⊔ L) : Set B) := hxD
    rw [Subgroup.coe_mul_of_left_le_normalizer_right
      (Subgroup.zpowers u) L hnormalizes] at hxSet
    obtain ⟨z, hzU, l, hl, rfl⟩ := hxSet
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hzU
    have hlParity : parity l = 1 := MonoidHom.mem_ker.mp (hLparity hl)
    have hpowParity : parity (u ^ n) = 1 := by
      have hxParity := MonoidHom.mem_ker.mp
        (hKparity (show u ^ n * l ∈ K from hxK))
      rw [map_mul, hlParity, mul_one] at hxParity
      exact hxParity
    have hnegPow : (-1 : ℤˣ) ^ n = 1 := by
      calc
        (-1 : ℤˣ) ^ n = parity (u ^ n) := by
          rw [map_zpow, huParity]
        _ = 1 := hpowParity
    have horder : orderOf (-1 : ℤˣ) = 2 :=
      orderOf_eq_prime (Int.units_sq _) (by decide)
    have htwo : (2 : ℤ) ∣ n := by
      have hdiv : (orderOf (-1 : ℤˣ) : ℤ) ∣ n :=
        orderOf_dvd_iff_zpow_eq_one.mpr hnegPow
      simpa [horder] using hdiv
    obtain ⟨k, rfl⟩ := htwo
    have huPowC : u ^ ((2 : ℤ) * k) ∈ C := by
      have heq : u ^ ((2 : ℤ) * k) = (u ^ (2 : Nat)) ^ k := by
        rw [zpow_mul, zpow_ofNat]
      rw [heq]
      exact C.zpow_mem hu2C k
    have huPowK : u ^ ((2 : ℤ) * k) ∈ K := hCleK huPowC
    have hlK : l ∈ K := by
      have h := K.mul_mem (K.inv_mem huPowK)
        (show u ^ ((2 : ℤ) * k) * l ∈ K from hxK)
      simpa using h
    have hlC : l ∈ C := by
      rw [← hKinfL]
      exact ⟨hlK, hl⟩
    exact C.mul_mem huPowC hlC
  · intro x hxC
    exact ⟨hCleK hxC, Subgroup.mem_sup_right (hCleL hxC)⟩

public theorem evenBlockKernel_inf_parityCosetProduct_eq_of_fusion_of_square_mem
    {H : Type} [Group H] [Finite H]
    (qA qB : Nat)
    (f : H →* alternatingGroup (Fin ((qA + 5) + (qB + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hfusion : evenBlockLeftDerivedKernelInBlock
        (qA + 5) (qB + 5) f =
      evenBlockRightDerivedKernelInBlock (qA + 5) (qB + 5) f)
    (u : evenBlockPreimage (qA + 5) (qB + 5) f)
    (huParity : evenBlockPreimageParity (qA + 5) (qB + 5) f u = -1)
    (hu2C : u ^ 2 ∈ evenBlockCommonDerivedKernelInEvenBlock qA qB f) :
    (f.ker.comap (evenBlockPreimage (qA + 5) (qB + 5) f).subtype) ⊓
        (Subgroup.zpowers u ⊔
          evenBlockComponentDerivedProductInEvenBlock qA qB f hf hker) =
      evenBlockCommonDerivedKernelInEvenBlock qA qB f := by
  let B := evenBlockPreimage (qA + 5) (qB + 5) f
  let parity := evenBlockPreimageParity (qA + 5) (qB + 5) f
  let K := f.ker.comap B.subtype
  let L := evenBlockComponentDerivedProductInEvenBlock qA qB f hf hker
  let C := evenBlockCommonDerivedKernelInEvenBlock qA qB f
  have hKparity : K ≤ parity.ker := by
    intro x hx
    have hxProjection : x ∈
        (evenBlockPreimageProjection (qA + 5) (qB + 5) f).ker := by
      rw [evenBlockPreimageProjection_ker_eq_comap]
      exact hx
    rw [MonoidHom.mem_ker]
    simpa [parity, evenBlockPreimageParity] using
      (show evenBlockParityHom (qA + 5) (qB + 5)
          (evenBlockPreimageProjection (qA + 5) (qB + 5) f x) = 1 by
        rw [MonoidHom.mem_ker.mp hxProjection, map_one])
  have hLparity : L ≤ parity.ker := by
    rintro z ⟨x, rfl⟩
    rw [evenBlockPreimageParity_ker_eq_alternatingBlockPreimage_comap]
    exact (evenBlockComponentDerivedMulHom qA qB f hf hker x).2
  exact kernel_inf_sup_zpowers_eq_of_parity_of_square_mem
    parity K L C u hKparity hLparity huParity
    (evenBlockKernel_inf_componentProductInEvenBlock_eq_of_fusion
      qA qB f hf hker hfusion)
    hu2C
    (evenBlockComponentDerivedProductInEvenBlock_zpowers_le_normalizer
      qA qB f hf hker u)

public theorem exists_evenBlockOddLift_of_multiplier_le_two
    {H : Type} [Group H] [Finite H]
    (qA qB : Nat)
    (hA : Nat.card
      (alternatingFreeCentralCovering qA).toMonoidHom.ker ≤ 2)
    (f : H →* alternatingGroup (Fin ((qA + 5) + (qB + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H) :
    ∃ u : evenBlockPreimage (qA + 5) (qB + 5) f,
      evenBlockPreimageParity (qA + 5) (qB + 5) f u = -1 ∧
        u ^ 2 ∈ evenBlockCommonDerivedKernelInEvenBlock qA qB f := by
  let r := alternatingBlockPreimageProjection (qA + 5) (qB + 5) f
  let rL := prodLeftPreimageDerivedProjection r
  let iL := evenBlockLeftDerivedEmbedding (qA + 5) (qB + 5) f
  let iLB := evenBlockLeftDerivedEmbeddingToBlock (qA + 5) (qB + 5) f
  let j := alternatingBlockPreimageToEvenBlockPreimage
    (qA + 5) (qB + 5) f
  obtain ⟨_, yL, hyL, hL⟩ :=
    evenBlock_leftComponent_pair_of_multiplier_le_two
      qA qB hA f hf hker
  obtain ⟨d, hd⟩ := hf (evenBlockParityConjugator qA qB)
  have hryL : r
      ((((yL : prodLeftPreimageDerived r) : prodLeftPreimage r) :
        alternatingBlockPreimage (qA + 5) (qB + 5) f)) =
      ((⟨RootFourSubgroup.rho1 qA,
          RootFourSubgroup.rho1_mem_alternating qA⟩ :
        alternatingGroup (Fin (qA + 5))), 1) := by
    apply Prod.ext
    · exact hyL
    · exact Subgroup.mem_bot.mp yL.1.2.2
  have hfyL : f (iL yL) =
      alternatingProdBlockHom (qA + 5) (qB + 5)
        ((⟨RootFourSubgroup.rho1 qA,
            RootFourSubgroup.rho1_mem_alternating qA⟩ :
          alternatingGroup (Fin (qA + 5))), 1) := by
    change f (((((yL : prodLeftPreimageDerived r) : prodLeftPreimage r) :
      alternatingBlockPreimage (qA + 5) (qB + 5) f) : H)) = _
    rw [← alternatingBlockPreimageProjection_fac]
    exact congrArg (alternatingProdBlockHom (qA + 5) (qB + 5)) hryL
  have huImage : f (d * iL yL * d⁻¹) =
      evenBlockProductHom (qA + 5) (qB + 5)
        (evenBlockOddPair qA qB) := by
    rw [map_mul, map_mul, map_inv, hd, hfyL]
    exact evenBlockParityConjugator_conj_left_rho1 qA qB
  have huMem : d * iL yL * d⁻¹ ∈
      evenBlockPreimage (qA + 5) (qB + 5) f :=
    ⟨evenBlockOddPair qA qB, huImage.symm⟩
  let u : evenBlockPreimage (qA + 5) (qB + 5) f :=
    ⟨d * iL yL * d⁻¹, huMem⟩
  have huProjection :
      evenBlockPreimageProjection (qA + 5) (qB + 5) f u =
        evenBlockOddPair qA qB := by
    apply evenBlockProductHom_injective
    calc
      evenBlockProductHom (qA + 5) (qB + 5)
          (evenBlockPreimageProjection (qA + 5) (qB + 5) f u) = f u :=
        evenBlockPreimageProjection_fac (qA + 5) (qB + 5) f u
      _ = evenBlockProductHom (qA + 5) (qB + 5)
          (evenBlockOddPair qA qB) := huImage
  have huParity : evenBlockPreimageParity
      (qA + 5) (qB + 5) f u = -1 := by
    simpa [evenBlockPreimageParity] using
      (show evenBlockParityHom (qA + 5) (qB + 5)
          (evenBlockPreimageProjection (qA + 5) (qB + 5) f u) = -1 by
        rw [huProjection]
        exact evenBlockParityHom_oddPair qA qB)
  have hyL2ker : yL ^ 2 ∈ rL.ker := by
    rw [hL]
    exact Subgroup.mem_zpowers (yL ^ 2)
  let e : alternatingBlockPreimage (qA + 5) (qB + 5) f := iLB (yL ^ 2)
  have heLeft : e ∈ evenBlockLeftDerivedKernelInBlock
      (qA + 5) (qB + 5) f := ⟨yL ^ 2, hyL2ker, rfl⟩
  have heC : j e ∈ evenBlockCommonDerivedKernelInEvenBlock qA qB f :=
    ⟨e, heLeft, rfl⟩
  have hyL2global : iL (yL ^ 2) ∈ f.ker :=
    evenBlockLeftDerivedKernel_le_ker (qA + 5) (qB + 5) f
      ⟨yL ^ 2, hyL2ker, rfl⟩
  have hyL2center : iL (yL ^ 2) ∈ Subgroup.center H :=
    hker hyL2global
  have hfixed : d * iL (yL ^ 2) * d⁻¹ = iL (yL ^ 2) := by
    have hc := Subgroup.mem_center_iff.mp hyL2center d
    rw [hc]
    simp
  have huSquare : u ^ 2 = j e := by
    apply Subtype.ext
    change (d * iL yL * d⁻¹) ^ 2 = iL (yL ^ 2)
    calc
      (d * iL yL * d⁻¹) ^ 2 = d * (iL yL) ^ 2 * d⁻¹ := by
        simp only [pow_two]
        group
      _ = d * iL (yL ^ 2) * d⁻¹ := by rw [map_pow]
      _ = iL (yL ^ 2) := hfixed
  refine ⟨u, huParity, ?_⟩
  rw [huSquare]
  exact heC

public theorem evenBlockParityCosetProduct_decomposition
    {H : Type} [Group H] [Finite H]
    (qA qB : Nat)
    (f : H →* alternatingGroup (Fin ((qA + 5) + (qB + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (u : evenBlockPreimage (qA + 5) (qB + 5) f)
    (huParity : evenBlockPreimageParity (qA + 5) (qB + 5) f u = -1) :
    ∀ x : evenBlockPreimage (qA + 5) (qB + 5) f,
      ∃ k : f.ker.comap
          (evenBlockPreimage (qA + 5) (qB + 5) f).subtype,
        ∃ d : ↥(Subgroup.zpowers u ⊔
            evenBlockComponentDerivedProductInEvenBlock qA qB f hf hker),
          (k : evenBlockPreimage (qA + 5) (qB + 5) f) *
              (d : evenBlockPreimage (qA + 5) (qB + 5) f) = x := by
  let B := evenBlockPreimage (qA + 5) (qB + 5) f
  let E := alternatingBlockPreimage (qA + 5) (qB + 5) f
  let r := alternatingBlockPreimageProjection (qA + 5) (qB + 5) f
  let j := alternatingBlockPreimageToEvenBlockPreimage
    (qA + 5) (qB + 5) f
  let parity := evenBlockPreimageParity (qA + 5) (qB + 5) f
  let L := evenBlockComponentDerivedProductInEvenBlock qA qB f hf hker
  let D := Subgroup.zpowers u ⊔ L
  have decomposeEven (x : B) (hx : parity x = 1) :
      ∃ k : f.ker.comap B.subtype, ∃ d : D,
        (k : B) * (d : B) = x := by
    have hxParityKer : x ∈ parity.ker := MonoidHom.mem_ker.mpr hx
    have hxE : (x : H) ∈ E := by
      rw [evenBlockPreimageParity_ker_eq_alternatingBlockPreimage_comap]
        at hxParityKer
      exact hxParityKer
    let e : E := ⟨(x : H), hxE⟩
    obtain ⟨k0, d0, hkd⟩ :=
      evenBlockComponentDerivedProduct_decomposition qA qB f hf hker e
    have hkGlobal : ((k0 : r.ker) : E) ∈
        f.ker.comap E.subtype := by
      rw [← alternatingBlockPreimageProjection_ker_eq_comap]
      exact k0.2
    have hkB : j (k0 : E) ∈ f.ker.comap B.subtype := hkGlobal
    have hdL : j (d0 : E) ∈ L := by
      obtain ⟨z, hz⟩ := d0.2
      refine ⟨z, ?_⟩
      change j (evenBlockComponentDerivedMulHom qA qB f hf hker z) =
        j (d0 : E)
      exact congrArg j hz
    have hdD : j (d0 : E) ∈ D := Subgroup.mem_sup_right hdL
    refine ⟨⟨j (k0 : E), hkB⟩, ⟨j (d0 : E), hdD⟩, ?_⟩
    apply Subtype.ext
    exact congrArg (fun z : E => (z : H)) hkd
  intro x
  rcases Int.units_eq_one_or (parity x) with hx | hx
  · exact decomposeEven x hx
  · let y : B := x * u⁻¹
    have huParity' : parity u = -1 := huParity
    have hyParity : parity y = 1 := by
      change parity (x * u⁻¹) = 1
      rw [map_mul, map_inv, hx, huParity']
      norm_num
    obtain ⟨k, d0, hkd⟩ := decomposeEven y hyParity
    have huD : u ∈ D :=
      Subgroup.mem_sup_left (Subgroup.mem_zpowers u)
    let d : D := ⟨(d0 : B) * u, D.mul_mem d0.2 huD⟩
    refine ⟨k, d, ?_⟩
    change (k : B) * ((d0 : B) * u) = x
    calc
      (k : B) * ((d0 : B) * u) = ((k : B) * (d0 : B)) * u := by
        simp only [mul_assoc]
      _ = y * u := by rw [hkd]
      _ = x := by simp [y]

public theorem evenBlockKernel_comap_eq_commonDerivedKernel_of_sylow_le_of_fusion
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (qA qB : Nat)
    (hA : Nat.card
      (alternatingFreeCentralCovering qA).toMonoidHom.ker ≤ 2)
    (f : H →* alternatingGroup (Fin ((qA + 5) + (qB + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerTwo : IsPGroup 2 f.ker)
    (P : Sylow 2 H)
    (hP : (P : Subgroup H) ≤
      evenBlockPreimage (qA + 5) (qB + 5) f)
    (hfusion : evenBlockLeftDerivedKernelInBlock
        (qA + 5) (qB + 5) f =
      evenBlockRightDerivedKernelInBlock (qA + 5) (qB + 5) f) :
    f.ker.comap (evenBlockPreimage (qA + 5) (qB + 5) f).subtype =
      evenBlockCommonDerivedKernelInEvenBlock qA qB f := by
  let B := evenBlockPreimage (qA + 5) (qB + 5) f
  let L := evenBlockComponentDerivedProductInEvenBlock qA qB f hf hker
  let C := evenBlockCommonDerivedKernelInEvenBlock qA qB f
  obtain ⟨u, huParity, hu2C⟩ :=
    exists_evenBlockOddLift_of_multiplier_le_two qA qB hA f hf hker
  let D := Subgroup.zpowers u ⊔ L
  exact kernel_comap_eq_of_sylow_le_subgroup_of_decomposition_of_inf_eq
    (p := 2) f hker hkerTwo P B hP D C
    (evenBlockParityCosetProduct_decomposition
      qA qB f hf hker u huParity)
    (evenBlockKernel_inf_parityCosetProduct_eq_of_fusion_of_square_mem
      qA qB f hf hker hfusion u huParity hu2C)

public theorem evenBlockKernel_comap_eq_commonDerivedKernel_of_equal_blocks
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (q : Nat)
    (hM : Nat.card
      (alternatingFreeCentralCovering q).toMonoidHom.ker ≤ 2)
    (ha : Even (q + 5))
    (f : H →* alternatingGroup (Fin ((q + 5) + (q + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerTwo : IsPGroup 2 f.ker)
    (P : Sylow 2 H)
    (hP : (P : Subgroup H) ≤
      evenBlockPreimage (q + 5) (q + 5) f) :
    f.ker.comap (evenBlockPreimage (q + 5) (q + 5) f).subtype =
      evenBlockCommonDerivedKernelInEvenBlock q q f := by
  have hglobal :=
    evenBlock_equalComponentDerivedKernel_eq_of_even_of_multiplier_le_two
      q hM ha f hf hker
  have hfusion := evenBlock_derivedKernelInBlock_eq_of_global_eq
    (q + 5) (q + 5) f hglobal
  exact evenBlockKernel_comap_eq_commonDerivedKernel_of_sylow_le_of_fusion
    q q hM f hf hker hkerTwo P hP hfusion

public theorem evenBlockKernel_comap_eq_commonDerivedKernel_of_unequal_blocks
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (qA qB : Nat)
    (hMA : Nat.card
      (alternatingFreeCentralCovering qA).toMonoidHom.ker ≤ 2)
    (hMB : Nat.card
      (alternatingFreeCentralCovering qB).toMonoidHom.ker ≤ 2)
    (hA : 1 ≤ qA) (hB : 1 ≤ qB)
    (f : H →* alternatingGroup (Fin ((qA + 5) + (qB + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerTwo : IsPGroup 2 f.ker)
    (P : Sylow 2 H)
    (hP : (P : Subgroup H) ≤
      evenBlockPreimage (qA + 5) (qB + 5) f) :
    f.ker.comap (evenBlockPreimage (qA + 5) (qB + 5) f).subtype =
      evenBlockCommonDerivedKernelInEvenBlock qA qB f := by
  have hglobal :=
    evenBlock_unequalComponentDerivedKernel_eq_of_six_of_multiplier_le_two
      qA qB hMA hMB hA hB f hf hker
  have hfusion := evenBlock_derivedKernelInBlock_eq_of_global_eq
    (qA + 5) (qB + 5) f hglobal
  exact evenBlockKernel_comap_eq_commonDerivedKernel_of_sylow_le_of_fusion
    qA qB hMA f hf hker hkerTwo P hP hfusion

/- Source: EvenBlockTwoBoundary.lean -/

public theorem alternatingGroup_fin_two_eq_one (x : alternatingGroup (Fin 2)) :
    x = 1 := by
  have hcard : Nat.card (alternatingGroup (Fin 2)) ≤ 1 := by
    have h := two_mul_nat_card_alternatingGroup (α := Fin 2)
    rw [Nat.card_perm] at h
    norm_num [Nat.card_fin, Nat.factorial] at h
    simpa [Nat.card_eq_fintype_card] using h.le
  let : Subsingleton (alternatingGroup (Fin 2)) :=
    Finite.card_le_one_iff_subsingleton.mp hcard
  exact Subsingleton.elim x 1

public noncomputable def evenBlockLeftDerivedProductTwo
    {H : Type} [Group H] [Finite H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 2))) :
    Subgroup (alternatingBlockPreimage (q + 5) 2 f) :=
  (evenBlockLeftDerivedEmbeddingToBlock (q + 5) 2 f).range

public theorem evenBlockLeftDerivedProductTwo_decomposition
    {H : Type} [Group H] [Finite H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 2)))
    (hf : Function.Surjective f) :
    ∀ x : alternatingBlockPreimage (q + 5) 2 f,
      ∃ k : (alternatingBlockPreimageProjection (q + 5) 2 f).ker,
        ∃ d : evenBlockLeftDerivedProductTwo q f,
          (k : alternatingBlockPreimage (q + 5) 2 f) *
              (d : alternatingBlockPreimage (q + 5) 2 f) = x := by
  let E := alternatingBlockPreimage (q + 5) 2 f
  let r := alternatingBlockPreimageProjection (q + 5) 2 f
  let DL := prodLeftPreimageDerived r
  let rL := prodLeftPreimageDerivedProjection r
  let iL := evenBlockLeftDerivedEmbeddingToBlock (q + 5) 2 f
  have hr : Function.Surjective r :=
    alternatingBlockPreimageProjection_surjective (q + 5) 2 f hf
  have hrL : Function.Surjective rL :=
    prodLeftPreimageDerivedProjection_surjective r hr
  intro x
  obtain ⟨xL, hxL⟩ := hrL (r x).1
  have hproj : r (iL xL) = r x := by
    apply Prod.ext
    · exact hxL
    · exact (alternatingGroup_fin_two_eq_one _).trans
        (alternatingGroup_fin_two_eq_one _).symm
  have hk : x * (iL xL)⁻¹ ∈ r.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hproj]
    simp
  let k : r.ker := ⟨x * (iL xL)⁻¹, hk⟩
  let d : evenBlockLeftDerivedProductTwo q f :=
    ⟨iL xL, ⟨xL, rfl⟩⟩
  exact ⟨k, d, by simp [k, d]⟩

public theorem evenBlockLeftDerivedProductTwo_ker_inf_eq
    {H : Type} [Group H] [Finite H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 2))) :
    (alternatingBlockPreimageProjection (q + 5) 2 f).ker ⊓
        evenBlockLeftDerivedProductTwo q f =
      evenBlockLeftDerivedKernelInBlock (q + 5) 2 f := by
  let r := alternatingBlockPreimageProjection (q + 5) 2 f
  let rL := prodLeftPreimageDerivedProjection r
  let iL := evenBlockLeftDerivedEmbeddingToBlock (q + 5) 2 f
  apply le_antisymm
  · rintro z ⟨hzker, hzprod⟩
    obtain ⟨x, rfl⟩ := hzprod
    have hxker : x ∈ rL.ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Prod.fst (MonoidHom.mem_ker.mp hzker)
    exact ⟨x, hxker, rfl⟩
  · rintro z ⟨x, hxker, rfl⟩
    constructor
    · change r (iL x) = 1
      apply Prod.ext
      · exact MonoidHom.mem_ker.mp hxker
      · exact alternatingGroup_fin_two_eq_one _
    · exact ⟨x, rfl⟩

public noncomputable def evenBlockLeftDerivedProductTwoInEvenBlock
    {H : Type} [Group H] [Finite H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 2))) :
    Subgroup (evenBlockPreimage (q + 5) 2 f) :=
  ((alternatingBlockPreimageToEvenBlockPreimage (q + 5) 2 f).comp
    (evenBlockLeftDerivedEmbeddingToBlock (q + 5) 2 f)).range

public noncomputable def evenBlockLeftDerivedKernelTwoInEvenBlock
    {H : Type} [Group H] [Finite H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 2))) :
    Subgroup (evenBlockPreimage (q + 5) 2 f) :=
  (evenBlockLeftDerivedKernelInBlock (q + 5) 2 f).map
    (alternatingBlockPreimageToEvenBlockPreimage (q + 5) 2 f)

public theorem evenBlockKernel_inf_leftDerivedProductTwoInEvenBlock_eq
    {H : Type} [Group H] [Finite H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 2))) :
    f.ker.comap (evenBlockPreimage (q + 5) 2 f).subtype ⊓
        evenBlockLeftDerivedProductTwoInEvenBlock q f =
      evenBlockLeftDerivedKernelTwoInEvenBlock q f := by
  let E := alternatingBlockPreimage (q + 5) 2 f
  let r := alternatingBlockPreimageProjection (q + 5) 2 f
  let iL := evenBlockLeftDerivedEmbeddingToBlock (q + 5) 2 f
  let j := alternatingBlockPreimageToEvenBlockPreimage (q + 5) 2 f
  let L := evenBlockLeftDerivedProductTwo q f
  let C := evenBlockLeftDerivedKernelInBlock (q + 5) 2 f
  have hinf : r.ker ⊓ L = C :=
    evenBlockLeftDerivedProductTwo_ker_inf_eq q f
  ext z
  constructor
  · rintro ⟨hzK, hzL⟩
    obtain ⟨x, rfl⟩ := hzL
    let e : E := iL x
    have heK : e ∈ r.ker := by
      rw [alternatingBlockPreimageProjection_ker_eq_comap]
      exact hzK
    have heL : e ∈ L := ⟨x, rfl⟩
    have heC : e ∈ C := by
      rw [← hinf]
      exact ⟨heK, heL⟩
    exact ⟨e, heC, rfl⟩
  · rintro ⟨e, heC, rfl⟩
    have heInf : e ∈ r.ker ⊓ L := by
      rw [hinf]
      exact heC
    constructor
    · rw [alternatingBlockPreimageProjection_ker_eq_comap] at heInf
      exact heInf.1
    · obtain ⟨x, hx⟩ := heInf.2
      exact ⟨x, congrArg j hx⟩

public theorem evenBlockLeftDerivedProductTwoInEvenBlock_conj_mem
    {H : Type} [Group H] [Finite H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 2)))
    (u z : evenBlockPreimage (q + 5) 2 f)
    (hz : z ∈ evenBlockLeftDerivedProductTwoInEvenBlock q f) :
    u * z * u⁻¹ ∈ evenBlockLeftDerivedProductTwoInEvenBlock q f := by
  obtain ⟨x, rfl⟩ := hz
  refine ⟨evenBlockConjOnLeftDerived (q + 5) 2 f u x, ?_⟩
  apply Subtype.ext
  exact evenBlockConjOnLeftDerived_embedding_general (q + 5) 2 f u x

public theorem evenBlockLeftDerivedProductTwoInEvenBlock_zpowers_le_normalizer
    {H : Type} [Group H] [Finite H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 2)))
    (u : evenBlockPreimage (q + 5) 2 f) :
    Subgroup.zpowers u ≤ Subgroup.normalizer
      (evenBlockLeftDerivedProductTwoInEvenBlock q f) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_set_normalizer_iff]
  intro z
  constructor
  · exact evenBlockLeftDerivedProductTwoInEvenBlock_conj_mem q f u z
  · intro hz
    have h := evenBlockLeftDerivedProductTwoInEvenBlock_conj_mem
      q f u⁻¹ (u * z * u⁻¹) hz
    have heq : u⁻¹ * (u * z * u⁻¹) * u = z := by group
    rw [inv_inv, heq] at h
    exact h

public theorem evenBlockKernel_inf_leftParityCosetProductTwo_eq_of_square_mem
    {H : Type} [Group H] [Finite H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 2)))
    (u : evenBlockPreimage (q + 5) 2 f)
    (huParity : evenBlockPreimageParity (q + 5) 2 f u = -1)
    (hu2C : u ^ 2 ∈ evenBlockLeftDerivedKernelTwoInEvenBlock q f) :
    f.ker.comap (evenBlockPreimage (q + 5) 2 f).subtype ⊓
        (Subgroup.zpowers u ⊔
          evenBlockLeftDerivedProductTwoInEvenBlock q f) =
      evenBlockLeftDerivedKernelTwoInEvenBlock q f := by
  let B := evenBlockPreimage (q + 5) 2 f
  let parity := evenBlockPreimageParity (q + 5) 2 f
  let K := f.ker.comap B.subtype
  let L := evenBlockLeftDerivedProductTwoInEvenBlock q f
  let C := evenBlockLeftDerivedKernelTwoInEvenBlock q f
  have hKparity : K ≤ parity.ker := by
    intro x hx
    have hxProjection : x ∈ (evenBlockPreimageProjection (q + 5) 2 f).ker := by
      rw [evenBlockPreimageProjection_ker_eq_comap]
      exact hx
    rw [MonoidHom.mem_ker]
    simpa [parity, evenBlockPreimageParity] using
      (show evenBlockParityHom (q + 5) 2
          (evenBlockPreimageProjection (q + 5) 2 f x) = 1 by
        rw [MonoidHom.mem_ker.mp hxProjection, map_one])
  have hLparity : L ≤ parity.ker := by
    rintro z ⟨x, rfl⟩
    rw [evenBlockPreimageParity_ker_eq_alternatingBlockPreimage_comap]
    exact (evenBlockLeftDerivedEmbeddingToBlock (q + 5) 2 f x).2
  exact kernel_inf_sup_zpowers_eq_of_parity_of_square_mem
    parity K L C u hKparity hLparity huParity
    (evenBlockKernel_inf_leftDerivedProductTwoInEvenBlock_eq q f)
    hu2C
    (evenBlockLeftDerivedProductTwoInEvenBlock_zpowers_le_normalizer q f u)

public theorem evenBlockLeftParityCosetProductTwo_decomposition
    {H : Type} [Group H] [Finite H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 5) + 2)))
    (hf : Function.Surjective f)
    (u : evenBlockPreimage (q + 5) 2 f)
    (huParity : evenBlockPreimageParity (q + 5) 2 f u = -1) :
    ∀ x : evenBlockPreimage (q + 5) 2 f,
      ∃ k : f.ker.comap (evenBlockPreimage (q + 5) 2 f).subtype,
        ∃ d : ↥(Subgroup.zpowers u ⊔
            evenBlockLeftDerivedProductTwoInEvenBlock q f),
          (k : evenBlockPreimage (q + 5) 2 f) *
              (d : evenBlockPreimage (q + 5) 2 f) = x := by
  let B := evenBlockPreimage (q + 5) 2 f
  let E := alternatingBlockPreimage (q + 5) 2 f
  let r := alternatingBlockPreimageProjection (q + 5) 2 f
  let j := alternatingBlockPreimageToEvenBlockPreimage (q + 5) 2 f
  let parity := evenBlockPreimageParity (q + 5) 2 f
  let L := evenBlockLeftDerivedProductTwoInEvenBlock q f
  let D := Subgroup.zpowers u ⊔ L
  have decomposeEven (x : B) (hx : parity x = 1) :
      ∃ k : f.ker.comap B.subtype, ∃ d : D,
        (k : B) * (d : B) = x := by
    have hxParityKer : x ∈ parity.ker := MonoidHom.mem_ker.mpr hx
    have hxE : (x : H) ∈ E := by
      rw [evenBlockPreimageParity_ker_eq_alternatingBlockPreimage_comap]
        at hxParityKer
      exact hxParityKer
    let e : E := ⟨(x : H), hxE⟩
    obtain ⟨k0, d0, hkd⟩ :=
      evenBlockLeftDerivedProductTwo_decomposition q f hf e
    have hkGlobal : ((k0 : r.ker) : E) ∈ f.ker.comap E.subtype := by
      rw [← alternatingBlockPreimageProjection_ker_eq_comap]
      exact k0.2
    have hkB : j (k0 : E) ∈ f.ker.comap B.subtype := hkGlobal
    have hdL : j (d0 : E) ∈ L := by
      obtain ⟨z, hz⟩ := d0.2
      refine ⟨z, ?_⟩
      change j (evenBlockLeftDerivedEmbeddingToBlock (q + 5) 2 f z) =
        j (d0 : E)
      exact congrArg j hz
    have hdD : j (d0 : E) ∈ D := Subgroup.mem_sup_right hdL
    refine ⟨⟨j (k0 : E), hkB⟩, ⟨j (d0 : E), hdD⟩, ?_⟩
    apply Subtype.ext
    exact congrArg (fun z : E => (z : H)) hkd
  intro x
  rcases Int.units_eq_one_or (parity x) with hx | hx
  · exact decomposeEven x hx
  · let y : B := x * u⁻¹
    have huParity' : parity u = -1 := huParity
    have hyParity : parity y = 1 := by
      change parity (x * u⁻¹) = 1
      rw [map_mul, map_inv, hx, huParity']
      norm_num
    obtain ⟨k, d0, hkd⟩ := decomposeEven y hyParity
    have huD : u ∈ D :=
      Subgroup.mem_sup_left (Subgroup.mem_zpowers u)
    let d : D := ⟨(d0 : B) * u, D.mul_mem d0.2 huD⟩
    refine ⟨k, d, ?_⟩
    change (k : B) * ((d0 : B) * u) = x
    calc
      (k : B) * ((d0 : B) * u) = ((k : B) * (d0 : B)) * u := by
        simp only [mul_assoc]
      _ = y * u := by rw [hkd]
      _ = x := by simp [y]

public def evenBlockTwoLeftPoint (q : Nat) (i : Fin (q + 5)) :
    Fin ((q + 5) + 2) :=
  finSumFinEquiv (Sum.inl i)

public def evenBlockTwoRightPoint (q : Nat) (i : Fin 2) :
    Fin ((q + 5) + 2) :=
  finSumFinEquiv (Sum.inr i)

public theorem twoBlock_permCongr_swap
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (i j : α) :
    e.permCongr (Equiv.swap i j) = Equiv.swap (e i) (e j) := by
  apply Equiv.ext
  intro x
  obtain ⟨x, rfl⟩ := e.surjective x
  rw [Equiv.permCongr_apply, e.symm_apply_apply]
  exact e.injective.map_swap i j x

public theorem evenBlockTwoLeftPoint_injective (q : Nat) :
    Function.Injective (evenBlockTwoLeftPoint q) :=
  finSumFinEquiv.injective.comp Sum.inl_injective

public theorem evenBlockTwoRightPoint_injective (q : Nat) :
    Function.Injective (evenBlockTwoRightPoint q) :=
  finSumFinEquiv.injective.comp Sum.inr_injective

public theorem evenBlockTwoLeftPoint_ne_right
    (q : Nat) (i : Fin (q + 5)) (j : Fin 2) :
    evenBlockTwoLeftPoint q i ≠ evenBlockTwoRightPoint q j := by
  intro h
  have h' := finSumFinEquiv.injective h
  cases h'

public theorem twoBlock_permProdBlockHom_swap_left
    (q : Nat) (i j : Fin (q + 5)) :
    permProdBlockHom (q + 5) 2 (Equiv.swap i j, 1) =
      Equiv.swap (evenBlockTwoLeftPoint q i)
        (evenBlockTwoLeftPoint q j) := by
  rw [permProdBlockHom_apply, Equiv.Perm.sumCongr_swap_one,
    twoBlock_permCongr_swap]
  rfl

public theorem twoBlock_permProdBlockHom_swap_right
    (q : Nat) (i j : Fin 2) :
    permProdBlockHom (q + 5) 2 (1, Equiv.swap i j) =
      Equiv.swap (evenBlockTwoRightPoint q i)
        (evenBlockTwoRightPoint q j) := by
  rw [permProdBlockHom_apply, Equiv.Perm.sumCongr_one_swap,
    twoBlock_permCongr_swap]
  rfl

public def evenBlockOddPairTwo (q : Nat) :
    evenBlockProductGroup (q + 5) 2 :=
  ⟨(Equiv.swap (RootFourSubgroup.p0 q) (RootFourSubgroup.p1 q),
      Equiv.swap (0 : Fin 2) 1), by
    change permProdBlockHom (q + 5) 2 _ ∈
      alternatingGroup (Fin ((q + 5) + 2))
    rw [Equiv.Perm.mem_alternatingGroup, permProdBlockHom_apply,
      Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr,
      Equiv.Perm.sign_swap, Equiv.Perm.sign_swap]
    · norm_num
    · decide
    · intro h
      have := congrArg Fin.val h
      simp [RootFourSubgroup.p0, RootFourSubgroup.p1] at this⟩

public theorem evenBlockParityHom_oddPairTwo (q : Nat) :
    evenBlockParityHom (q + 5) 2 (evenBlockOddPairTwo q) = -1 := by
  change Equiv.Perm.sign
      (Equiv.swap (RootFourSubgroup.p0 q) (RootFourSubgroup.p1 q)) = -1
  apply Equiv.Perm.sign_swap
  intro h
  have := congrArg Fin.val h
  simp [RootFourSubgroup.p0, RootFourSubgroup.p1] at this

public def evenBlockParityConjugatorPermTwo (q : Nat) :
    Equiv.Perm (Fin ((q + 5) + 2)) :=
  Equiv.swap
      (evenBlockTwoLeftPoint q (RootFourSubgroup.p2 q))
      (evenBlockTwoRightPoint q 0) *
    Equiv.swap
      (evenBlockTwoLeftPoint q (RootFourSubgroup.p3 q))
      (evenBlockTwoRightPoint q 1)

public theorem sign_evenBlockParityConjugatorPermTwo (q : Nat) :
    Equiv.Perm.sign (evenBlockParityConjugatorPermTwo q) = 1 := by
  rw [evenBlockParityConjugatorPermTwo, map_mul,
    Equiv.Perm.sign_swap, Equiv.Perm.sign_swap]
  · norm_num
  · exact evenBlockTwoLeftPoint_ne_right q _ _
  · exact evenBlockTwoLeftPoint_ne_right q _ _

public def evenBlockParityConjugatorTwo (q : Nat) :
    alternatingGroup (Fin ((q + 5) + 2)) :=
  ⟨evenBlockParityConjugatorPermTwo q, by
    rw [Equiv.Perm.mem_alternatingGroup,
      sign_evenBlockParityConjugatorPermTwo]⟩

public theorem evenBlockParityConjugatorPermTwo_p0 (q : Nat) :
    evenBlockParityConjugatorPermTwo q
        (evenBlockTwoLeftPoint q (RootFourSubgroup.p0 q)) =
      evenBlockTwoLeftPoint q (RootFourSubgroup.p0 q) := by
  have h03 : RootFourSubgroup.p0 q ≠ RootFourSubgroup.p3 q := by
    intro h; have := congrArg Fin.val h
    simp [RootFourSubgroup.p0, RootFourSubgroup.p3] at this
  have h02 : RootFourSubgroup.p0 q ≠ RootFourSubgroup.p2 q := by
    intro h; have := congrArg Fin.val h
    simp [RootFourSubgroup.p0, RootFourSubgroup.p2] at this
  rw [evenBlockParityConjugatorPermTwo, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne
      ((evenBlockTwoLeftPoint_injective q).ne h03)
      (evenBlockTwoLeftPoint_ne_right q _ _),
    Equiv.swap_apply_of_ne_of_ne
      ((evenBlockTwoLeftPoint_injective q).ne h02)
      (evenBlockTwoLeftPoint_ne_right q _ _)]

public theorem evenBlockParityConjugatorPermTwo_p1 (q : Nat) :
    evenBlockParityConjugatorPermTwo q
        (evenBlockTwoLeftPoint q (RootFourSubgroup.p1 q)) =
      evenBlockTwoLeftPoint q (RootFourSubgroup.p1 q) := by
  have h13 : RootFourSubgroup.p1 q ≠ RootFourSubgroup.p3 q := by
    intro h; have := congrArg Fin.val h
    simp [RootFourSubgroup.p1, RootFourSubgroup.p3] at this
  have h12 : RootFourSubgroup.p1 q ≠ RootFourSubgroup.p2 q := by
    intro h; have := congrArg Fin.val h
    simp [RootFourSubgroup.p1, RootFourSubgroup.p2] at this
  rw [evenBlockParityConjugatorPermTwo, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne
      ((evenBlockTwoLeftPoint_injective q).ne h13)
      (evenBlockTwoLeftPoint_ne_right q _ _),
    Equiv.swap_apply_of_ne_of_ne
      ((evenBlockTwoLeftPoint_injective q).ne h12)
      (evenBlockTwoLeftPoint_ne_right q _ _)]

public theorem evenBlockParityConjugatorPermTwo_p2 (q : Nat) :
    evenBlockParityConjugatorPermTwo q
        (evenBlockTwoLeftPoint q (RootFourSubgroup.p2 q)) =
      evenBlockTwoRightPoint q 0 := by
  have h23 : RootFourSubgroup.p2 q ≠ RootFourSubgroup.p3 q := by
    intro h; have := congrArg Fin.val h
    simp [RootFourSubgroup.p2, RootFourSubgroup.p3] at this
  rw [evenBlockParityConjugatorPermTwo, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne
      ((evenBlockTwoLeftPoint_injective q).ne h23)
      (evenBlockTwoLeftPoint_ne_right q _ _),
    Equiv.swap_apply_left]

public theorem evenBlockParityConjugatorPermTwo_p3 (q : Nat) :
    evenBlockParityConjugatorPermTwo q
        (evenBlockTwoLeftPoint q (RootFourSubgroup.p3 q)) =
      evenBlockTwoRightPoint q 1 := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  rw [evenBlockParityConjugatorPermTwo, Equiv.Perm.mul_apply,
    Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne
      (evenBlockTwoLeftPoint_ne_right q _ _).symm
      ((evenBlockTwoRightPoint_injective q).ne h10)]

public theorem evenBlockParityConjugatorTwo_conj_left_rho1 (q : Nat) :
    evenBlockParityConjugatorTwo q *
        alternatingProdBlockHom (q + 5) 2
          ((⟨RootFourSubgroup.rho1 q,
              RootFourSubgroup.rho1_mem_alternating q⟩ :
                alternatingGroup (Fin (q + 5))), 1) *
        (evenBlockParityConjugatorTwo q)⁻¹ =
      evenBlockProductHom (q + 5) 2 (evenBlockOddPairTwo q) := by
  apply Subtype.ext
  let s := evenBlockParityConjugatorPermTwo q
  let l0 := evenBlockTwoLeftPoint q (RootFourSubgroup.p0 q)
  let l1 := evenBlockTwoLeftPoint q (RootFourSubgroup.p1 q)
  let l2 := evenBlockTwoLeftPoint q (RootFourSubgroup.p2 q)
  let l3 := evenBlockTwoLeftPoint q (RootFourSubgroup.p3 q)
  let r0 := evenBlockTwoRightPoint q 0
  let r1 := evenBlockTwoRightPoint q 1
  have hleft :
      permProdBlockHom (q + 5) 2 (RootFourSubgroup.rho1 q, 1) =
        Equiv.swap l0 l1 * Equiv.swap l2 l3 := by
    rw [RootFourSubgroup.rho1]
    change permProdBlockHom (q + 5) 2
        ((Equiv.swap _ _, 1) * (Equiv.swap _ _, 1)) = _
    rw [map_mul, twoBlock_permProdBlockHom_swap_left,
      twoBlock_permProdBlockHom_swap_left]
  have htarget :
      permProdBlockHom (q + 5) 2
          (evenBlockOddPairTwo q :
            Equiv.Perm (Fin (q + 5)) × Equiv.Perm (Fin 2)) =
        Equiv.swap l0 l1 * Equiv.swap r0 r1 := by
    change permProdBlockHom (q + 5) 2
        ((Equiv.swap _ _, 1) * (1, Equiv.swap _ _)) = _
    rw [map_mul, twoBlock_permProdBlockHom_swap_left,
      twoBlock_permProdBlockHom_swap_right]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [coe_alternatingProdBlockHom_apply, coe_evenBlockProductHom_apply]
  change s * permProdBlockHom (q + 5) 2
      (RootFourSubgroup.rho1 q, 1) * s⁻¹ =
    permProdBlockHom (q + 5) 2
      (evenBlockOddPairTwo q :
        Equiv.Perm (Fin (q + 5)) × Equiv.Perm (Fin 2))
  rw [hleft, htarget]
  calc
    s * (Equiv.swap l0 l1 * Equiv.swap l2 l3) * s⁻¹ =
        (s * Equiv.swap l0 l1 * s⁻¹) *
          (s * Equiv.swap l2 l3 * s⁻¹) := by group
    _ = Equiv.swap (s l0) (s l1) * Equiv.swap (s l2) (s l3) := by
      rw [Equiv.swap_apply_apply, Equiv.swap_apply_apply]
    _ = Equiv.swap l0 l1 * Equiv.swap r0 r1 := by
      rw [evenBlockParityConjugatorPermTwo_p0,
        evenBlockParityConjugatorPermTwo_p1,
        evenBlockParityConjugatorPermTwo_p2,
        evenBlockParityConjugatorPermTwo_p3]

public theorem exists_evenBlockOddLiftTwo_of_multiplier_le_two
    {H : Type} [Group H] [Finite H]
    (q : Nat)
    (hM : Nat.card
      (alternatingFreeCentralCovering q).toMonoidHom.ker ≤ 2)
    (f : H →* alternatingGroup (Fin ((q + 5) + 2)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H) :
    ∃ u : evenBlockPreimage (q + 5) 2 f,
      evenBlockPreimageParity (q + 5) 2 f u = -1 ∧
        u ^ 2 ∈ evenBlockLeftDerivedKernelTwoInEvenBlock q f := by
  let E := alternatingBlockPreimage (q + 5) 2 f
  let r := alternatingBlockPreimageProjection (q + 5) 2 f
  let EL := prodLeftPreimage r
  let rL0 := prodLeftPreimageProjection r
  let DL := prodLeftPreimageDerived r
  let rL := prodLeftPreimageDerivedProjection r
  let iL := evenBlockLeftDerivedEmbedding (q + 5) 2 f
  let iLB := evenBlockLeftDerivedEmbeddingToBlock (q + 5) 2 f
  let j := alternatingBlockPreimageToEvenBlockPreimage (q + 5) 2 f
  have hr : Function.Surjective r :=
    alternatingBlockPreimageProjection_surjective (q + 5) 2 f hf
  have hrker : r.ker ≤ Subgroup.center E :=
    alternatingBlockPreimageProjection_ker_le_center (q + 5) 2 f hker
  obtain ⟨_, yL, hyL, hL⟩ :=
    derived_natCard_ker_le_two_and_exists_lift_rho1_ker_eq_zpowers_of_multiplier_le_two
      q hM rL0 (prodLeftPreimageProjection_surjective r hr)
        (prodLeftPreimageProjection_ker_le_center r hrker)
  obtain ⟨d, hd⟩ := hf (evenBlockParityConjugatorTwo q)
  have hryL : r
      ((((yL : DL) : EL) : E)) =
      ((⟨RootFourSubgroup.rho1 q,
          RootFourSubgroup.rho1_mem_alternating q⟩ :
        alternatingGroup (Fin (q + 5))), 1) := by
    apply Prod.ext
    · exact hyL
    · exact Subgroup.mem_bot.mp yL.1.2.2
  have hfyL : f (iL yL) =
      alternatingProdBlockHom (q + 5) 2
        ((⟨RootFourSubgroup.rho1 q,
            RootFourSubgroup.rho1_mem_alternating q⟩ :
          alternatingGroup (Fin (q + 5))), 1) := by
    change f (((((yL : DL) : EL) : E) : H)) = _
    rw [← alternatingBlockPreimageProjection_fac]
    exact congrArg (alternatingProdBlockHom (q + 5) 2) hryL
  have huImage : f (d * iL yL * d⁻¹) =
      evenBlockProductHom (q + 5) 2 (evenBlockOddPairTwo q) := by
    rw [map_mul, map_mul, map_inv, hd, hfyL]
    exact evenBlockParityConjugatorTwo_conj_left_rho1 q
  have huMem : d * iL yL * d⁻¹ ∈ evenBlockPreimage (q + 5) 2 f :=
    ⟨evenBlockOddPairTwo q, huImage.symm⟩
  let u : evenBlockPreimage (q + 5) 2 f :=
    ⟨d * iL yL * d⁻¹, huMem⟩
  have huProjection : evenBlockPreimageProjection (q + 5) 2 f u =
      evenBlockOddPairTwo q := by
    apply evenBlockProductHom_injective
    calc
      evenBlockProductHom (q + 5) 2
          (evenBlockPreimageProjection (q + 5) 2 f u) = f u :=
        evenBlockPreimageProjection_fac (q + 5) 2 f u
      _ = evenBlockProductHom (q + 5) 2
          (evenBlockOddPairTwo q) := huImage
  have huParity : evenBlockPreimageParity (q + 5) 2 f u = -1 := by
    simpa [evenBlockPreimageParity] using
      (show evenBlockParityHom (q + 5) 2
          (evenBlockPreimageProjection (q + 5) 2 f u) = -1 by
        rw [huProjection]
        exact evenBlockParityHom_oddPairTwo q)
  have hyL2ker : yL ^ 2 ∈ (rL0.comp DL.subtype).ker := by
    rw [hL]
    exact Subgroup.mem_zpowers (yL ^ 2)
  let e : E := iLB (yL ^ 2)
  have heLeft : e ∈ evenBlockLeftDerivedKernelInBlock (q + 5) 2 f :=
    ⟨yL ^ 2, hyL2ker, rfl⟩
  have heC : j e ∈ evenBlockLeftDerivedKernelTwoInEvenBlock q f :=
    ⟨e, heLeft, rfl⟩
  have hyL2global : iL (yL ^ 2) ∈ f.ker :=
    evenBlockLeftDerivedKernel_le_ker (q + 5) 2 f
      ⟨yL ^ 2, hyL2ker, rfl⟩
  have hyL2center : iL (yL ^ 2) ∈ Subgroup.center H :=
    hker hyL2global
  have hfixed : d * iL (yL ^ 2) * d⁻¹ = iL (yL ^ 2) := by
    have hc := Subgroup.mem_center_iff.mp hyL2center d
    rw [hc]
    simp
  have huSquare : u ^ 2 = j e := by
    apply Subtype.ext
    change (d * iL yL * d⁻¹) ^ 2 = iL (yL ^ 2)
    calc
      (d * iL yL * d⁻¹) ^ 2 = d * (iL yL) ^ 2 * d⁻¹ := by
        simp only [pow_two]
        group
      _ = d * iL (yL ^ 2) * d⁻¹ := by rw [map_pow]
      _ = iL (yL ^ 2) := hfixed
  refine ⟨u, huParity, ?_⟩
  rw [huSquare]
  exact heC

public theorem evenBlockKernel_comap_eq_leftDerivedKernel_of_two_block
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (q : Nat)
    (hM : Nat.card
      (alternatingFreeCentralCovering q).toMonoidHom.ker ≤ 2)
    (f : H →* alternatingGroup (Fin ((q + 5) + 2)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerTwo : IsPGroup 2 f.ker)
    (P : Sylow 2 H)
    (hP : (P : Subgroup H) ≤ evenBlockPreimage (q + 5) 2 f) :
    f.ker.comap (evenBlockPreimage (q + 5) 2 f).subtype =
      evenBlockLeftDerivedKernelTwoInEvenBlock q f := by
  let B := evenBlockPreimage (q + 5) 2 f
  let L := evenBlockLeftDerivedProductTwoInEvenBlock q f
  let C := evenBlockLeftDerivedKernelTwoInEvenBlock q f
  obtain ⟨u, huParity, hu2C⟩ :=
    exists_evenBlockOddLiftTwo_of_multiplier_le_two q hM f hf hker
  let D := Subgroup.zpowers u ⊔ L
  exact kernel_comap_eq_of_sylow_le_subgroup_of_decomposition_of_inf_eq
    (p := 2) f hker hkerTwo P B hP D C
    (evenBlockLeftParityCosetProductTwo_decomposition
      q f hf u huParity)
    (evenBlockKernel_inf_leftParityCosetProductTwo_eq_of_square_mem
      q f u huParity hu2C)

/-- If a Sylow `2`-subgroup lies in the even-block preimage with a two-point
right block, then the central kernel has order at most two. -/
public theorem natCard_ker_le_two_of_sylow_le_evenBlockPreimage_two
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (q : Nat)
    (hM : Nat.card
      (alternatingFreeCentralCovering q).toMonoidHom.ker ≤ 2)
    (f : H →* alternatingGroup (Fin ((q + 5) + 2)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerTwo : IsPGroup 2 f.ker)
    (P : Sylow 2 H)
    (hP : (P : Subgroup H) ≤ evenBlockPreimage (q + 5) 2 f) :
    Nat.card f.ker ≤ 2 := by
  let B := evenBlockPreimage (q + 5) 2 f
  let E := alternatingBlockPreimage (q + 5) 2 f
  let r := alternatingBlockPreimageProjection (q + 5) 2 f
  let rL0 := prodLeftPreimageProjection r
  let rL := prodLeftPreimageDerivedProjection r
  let iLB := evenBlockLeftDerivedEmbeddingToBlock (q + 5) 2 f
  let j := alternatingBlockPreimageToEvenBlockPreimage (q + 5) 2 f
  let K := f.ker.comap B.subtype
  let C := evenBlockLeftDerivedKernelTwoInEvenBlock q f
  have hr : Function.Surjective r :=
    alternatingBlockPreimageProjection_surjective (q + 5) 2 f hf
  have hrker : r.ker ≤ Subgroup.center E :=
    alternatingBlockPreimageProjection_ker_le_center (q + 5) 2 f hker
  obtain ⟨hlocal, _, _, _⟩ :=
    derived_natCard_ker_le_two_and_exists_lift_rho1_ker_eq_zpowers_of_multiplier_le_two
      q hM rL0 (prodLeftPreimageProjection_surjective r hr)
        (prodLeftPreimageProjection_ker_le_center r hrker)
  have hlocal' : Nat.card rL.ker ≤ 2 := hlocal
  let eK : f.ker ≃* K :=
    { toFun := fun z => ⟨⟨z, by
          change f z ∈ (evenBlockProductHom (q + 5) 2).range
          rw [MonoidHom.mem_ker.mp z.2]
          exact Subgroup.one_mem _⟩, z.2⟩
      invFun := fun z => ⟨((z : K) : B), z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have hKC : K = C :=
    evenBlockKernel_comap_eq_leftDerivedKernel_of_two_block
      q hM f hf hker hkerTwo P hP
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : B => (z : H)) hxy
  have hiLB : Function.Injective iLB := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact hxy
  calc
    Nat.card f.ker = Nat.card K := Nat.card_congr eK.toEquiv
    _ = Nat.card C := by rw [hKC]
    _ = Nat.card (evenBlockLeftDerivedKernelInBlock (q + 5) 2 f) := by
      exact Subgroup.card_map_of_injective hj
    _ = Nat.card rL.ker := by
      exact Subgroup.card_map_of_injective hiLB
    _ ≤ 2 := hlocal'

/-! # Size-four even-block boundary -/


end GLS3.Chapter5.SchurPresentation
/- END Theory.EvenBlockCore -/

/- BEGIN Theory.InvolutionFixedPointParityLift -/
noncomputable section

namespace GLS3.Chapter5
universe __ch5_InvolutionFixedPointParityLift_u

private theorem __ch5_InvolutionFixedPointParityLift_unitsInvolutionHom_mem_cycleRotationSubgroup
    {Ω : Type __ch5_InvolutionFixedPointParityLift_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω)
    (r0 : Subgroup.centralizer ({x} : Set (Equiv.Perm Ω)))
    (hr0 : r0 ∈ cycleRotationSubgroup x) (hr02 : r0 ^ 2 = 1)
    (__ch5_InvolutionFixedPointParityLift_u : ℤˣ) : unitsInvolutionHom r0 hr02 __ch5_InvolutionFixedPointParityLift_u ∈ cycleRotationSubgroup x := by
  rcases Int.units_eq_one_or __ch5_InvolutionFixedPointParityLift_u with rfl | rfl
  · simp
  · simpa using hr0

/-- Correct the parity of a fixed-point permutation by multiplying by a fixed
odd cycle rotation. -/
@[expose]
public noncomputable def involutionFixedPointParityLift
    {Ω : Type __ch5_InvolutionFixedPointParityLift_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω)
    (r0 : Subgroup.centralizer ({x} : Set (Equiv.Perm Ω)))
    (hr0 : r0 ∈ cycleRotationSubgroup x)
    (hr0χ : Equiv.Perm.sign r0.1 = -1) (hr02 : r0 ^ 2 = 1) :
    Equiv.Perm (Function.fixedPoints x) →*
      (Equiv.Perm.sign.comp
        (Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))).subtype).ker where
  toFun σ := ⟨fixedPointPermToCentralizer x σ *
      unitsInvolutionHom r0 hr02 (Equiv.Perm.sign σ), by
    rw [MonoidHom.mem_ker, map_mul]
    change Equiv.Perm.sign (fixedPointPermToCentralizer x σ).1 *
      Equiv.Perm.sign (unitsInvolutionHom r0 hr02 (Equiv.Perm.sign σ)).1 = 1
    rw [fixedPointPermToCentralizer_coe, Equiv.Perm.sign_ofSubtype]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ
    · rw [hσ, unitsInvolutionHom_one]
      simp
    · rw [hσ, unitsInvolutionHom_neg_one, hr0χ]
      norm_num⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' σ τ := by
    apply Subtype.ext
    change fixedPointPermToCentralizer x (σ * τ) *
        unitsInvolutionHom r0 hr02 (Equiv.Perm.sign (σ * τ)) =
      (fixedPointPermToCentralizer x σ *
          unitsInvolutionHom r0 hr02 (Equiv.Perm.sign σ)) *
        (fixedPointPermToCentralizer x τ *
          unitsInvolutionHom r0 hr02 (Equiv.Perm.sign τ))
    rw [map_mul, map_mul, map_mul]
    have hcomm : Commute
        (unitsInvolutionHom r0 hr02 (Equiv.Perm.sign σ))
        (fixedPointPermToCentralizer x τ) :=
      (fixedPointPermutationSubgroup_commutes_cycleRotationSubgroup x
        (fixedPointPermToCentralizer x τ) ⟨τ, rfl⟩
        (unitsInvolutionHom r0 hr02 (Equiv.Perm.sign σ))
        (__ch5_InvolutionFixedPointParityLift_unitsInvolutionHom_mem_cycleRotationSubgroup x r0 hr0 hr02 _)).symm
    calc
      fixedPointPermToCentralizer x σ * fixedPointPermToCentralizer x τ *
          (unitsInvolutionHom r0 hr02 (Equiv.Perm.sign σ) *
            unitsInvolutionHom r0 hr02 (Equiv.Perm.sign τ)) =
        fixedPointPermToCentralizer x σ *
          (fixedPointPermToCentralizer x τ *
            unitsInvolutionHom r0 hr02 (Equiv.Perm.sign σ)) *
          unitsInvolutionHom r0 hr02 (Equiv.Perm.sign τ) := by group
      _ = fixedPointPermToCentralizer x σ *
          (unitsInvolutionHom r0 hr02 (Equiv.Perm.sign σ) *
            fixedPointPermToCentralizer x τ) *
          unitsInvolutionHom r0 hr02 (Equiv.Perm.sign τ) := by rw [hcomm.eq]
      _ = (fixedPointPermToCentralizer x σ *
          unitsInvolutionHom r0 hr02 (Equiv.Perm.sign σ)) *
        (fixedPointPermToCentralizer x τ *
          unitsInvolutionHom r0 hr02 (Equiv.Perm.sign τ)) := by group

@[simp]
public theorem involutionFixedPointParityLift_coe
    {Ω : Type __ch5_InvolutionFixedPointParityLift_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω)
    (r0 : Subgroup.centralizer ({x} : Set (Equiv.Perm Ω)))
    (hr0 : r0 ∈ cycleRotationSubgroup x)
    (hr0χ : Equiv.Perm.sign r0.1 = -1) (hr02 : r0 ^ 2 = 1)
    (σ : Equiv.Perm (Function.fixedPoints x)) :
    (involutionFixedPointParityLift x r0 hr0 hr0χ hr02 σ).1 =
      fixedPointPermToCentralizer x σ *
        unitsInvolutionHom r0 hr02 (Equiv.Perm.sign σ) := rfl

public theorem involutionFixedPointParityLift_injective
    {Ω : Type __ch5_InvolutionFixedPointParityLift_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω)
    (r0 : Subgroup.centralizer ({x} : Set (Equiv.Perm Ω)))
    (hr0 : r0 ∈ cycleRotationSubgroup x)
    (hr0χ : Equiv.Perm.sign r0.1 = -1) (hr02 : r0 ^ 2 = 1) :
    Function.Injective
      (involutionFixedPointParityLift x r0 hr0 hr0χ hr02) := by
  intro σ τ hστ
  apply Equiv.ext
  intro ω
  apply Subtype.ext
  have hval := congrArg
    (fun z : (Equiv.Perm.sign.comp
      (Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))).subtype).ker =>
        z.1.1 ω.1) hστ
  have hfix (__ch5_InvolutionFixedPointParityLift_u : ℤˣ) :
      (unitsInvolutionHom r0 hr02 __ch5_InvolutionFixedPointParityLift_u).1 ω.1 = ω.1 :=
    (mem_cycleRotationSubgroup_iff x
      (unitsInvolutionHom r0 hr02 __ch5_InvolutionFixedPointParityLift_u)).mp
        (__ch5_InvolutionFixedPointParityLift_unitsInvolutionHom_mem_cycleRotationSubgroup x r0 hr0 hr02 __ch5_InvolutionFixedPointParityLift_u) |>.2 ω
  change (fixedPointPermToCentralizer x σ).1
      ((unitsInvolutionHom r0 hr02 (Equiv.Perm.sign σ)).1 ω.1) =
    (fixedPointPermToCentralizer x τ).1
      ((unitsInvolutionHom r0 hr02 (Equiv.Perm.sign τ)).1 ω.1) at hval
  rw [hfix, hfix, fixedPointPermToCentralizer_coe,
    fixedPointPermToCentralizer_coe,
    Equiv.Perm.ofSubtype_apply_of_mem σ ω.2,
    Equiv.Perm.ofSubtype_apply_of_mem τ ω.2] at hval
  exact hval

end GLS3.Chapter5
/- END Theory.InvolutionFixedPointParityLift -/

/- BEGIN Theory.SignKernelParityLift -/
noncomputable section

namespace GLS3.Chapter5

/-- Correct a subgroup element's sign by multiplying by a commuting odd
involution. -/
@[expose]
public noncomputable def signKernelParityLift
    {C : Type*} [Group C] (χ : C →* ℤˣ) (H I : Subgroup C)
    (i0 : C) (hi0 : i0 ∈ I) (hi0χ : χ i0 = -1) (hi02 : i0 ^ 2 = 1)
    (hcomm : I ≤ Subgroup.centralizer (H : Set C)) : H →* χ.ker where
  toFun h := ⟨h.1 * unitsInvolutionHom i0 hi02 (χ h.1), by
    rw [MonoidHom.mem_ker, map_mul]
    rcases Int.units_eq_one_or (χ h.1) with hh | hh
    · rw [hh, unitsInvolutionHom_one, map_one, mul_one]
    · rw [hh, unitsInvolutionHom_neg_one, hi0χ]
      norm_num⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' h k := by
    apply Subtype.ext
    change (h.1 * k.1) * unitsInvolutionHom i0 hi02 (χ (h.1 * k.1)) =
      (h.1 * unitsInvolutionHom i0 hi02 (χ h.1)) *
        (k.1 * unitsInvolutionHom i0 hi02 (χ k.1))
    rw [map_mul, map_mul]
    have hmem (u : ℤˣ) : unitsInvolutionHom i0 hi02 u ∈ I := by
      rcases Int.units_eq_one_or u with rfl | rfl
      · simp
      · simpa using hi0
    have hc : Commute (unitsInvolutionHom i0 hi02 (χ h.1)) k.1 := by
      have hi := hcomm (hmem (χ h.1))
      rw [Subgroup.mem_centralizer_iff] at hi
      exact (hi k.1 k.2).symm
    calc
      (h.1 * k.1) *
          (unitsInvolutionHom i0 hi02 (χ h.1) *
            unitsInvolutionHom i0 hi02 (χ k.1)) =
        h.1 * (k.1 * unitsInvolutionHom i0 hi02 (χ h.1)) *
          unitsInvolutionHom i0 hi02 (χ k.1) := by group
      _ = h.1 * (unitsInvolutionHom i0 hi02 (χ h.1) * k.1) *
          unitsInvolutionHom i0 hi02 (χ k.1) := by rw [hc.eq]
      _ = (h.1 * unitsInvolutionHom i0 hi02 (χ h.1)) *
          (k.1 * unitsInvolutionHom i0 hi02 (χ k.1)) := by group

@[simp]
public theorem signKernelParityLift_coe
    {C : Type*} [Group C] (χ : C →* ℤˣ) (H I : Subgroup C)
    (i0 : C) (hi0 : i0 ∈ I) (hi0χ : χ i0 = -1) (hi02 : i0 ^ 2 = 1)
    (hcomm : I ≤ Subgroup.centralizer (H : Set C)) (h : H) :
    (signKernelParityLift χ H I i0 hi0 hi0χ hi02 hcomm h).1 =
      h.1 * unitsInvolutionHom i0 hi02 (χ h.1) := rfl

public theorem signKernelParityLift_injective
    {C : Type*} [Group C] (χ : C →* ℤˣ) (H I : Subgroup C)
    (i0 : C) (hi0 : i0 ∈ I) (hi0χ : χ i0 = -1) (hi02 : i0 ^ 2 = 1)
    (hcomm : I ≤ Subgroup.centralizer (H : Set C))
    (hdisj : I ⊓ H = ⊥) :
    Function.Injective (signKernelParityLift χ H I i0 hi0 hi0χ hi02 hcomm) := by
  intro h k hhk
  have hmem (u : ℤˣ) : unitsInvolutionHom i0 hi02 u ∈ I := by
    rcases Int.units_eq_one_or u with rfl | rfl
    · simp
    · simpa using hi0
  have hval := congrArg Subtype.val hhk
  rw [signKernelParityLift_coe, signKernelParityLift_coe] at hval
  have hratio : h.1⁻¹ * k.1 =
      unitsInvolutionHom i0 hi02 (χ h.1) *
        (unitsInvolutionHom i0 hi02 (χ k.1))⁻¹ := by
    have hhcomm : Commute (unitsInvolutionHom i0 hi02 (χ h.1)) h.1 := by
      have hi := hcomm (hmem (χ h.1))
      rw [Subgroup.mem_centralizer_iff] at hi
      exact (hi h.1 h.2).symm
    have hkcomm : Commute (unitsInvolutionHom i0 hi02 (χ k.1)) k.1 := by
      have hi := hcomm (hmem (χ k.1))
      rw [Subgroup.mem_centralizer_iff] at hi
      exact (hi k.1 k.2).symm
    calc
      h.1⁻¹ * k.1 = h.1⁻¹ *
          (h.1 * unitsInvolutionHom i0 hi02 (χ h.1)) *
          (unitsInvolutionHom i0 hi02 (χ k.1))⁻¹ := by rw [hval]; group
      _ = unitsInvolutionHom i0 hi02 (χ h.1) *
          (unitsInvolutionHom i0 hi02 (χ k.1))⁻¹ := by group
  have hinter : h.1⁻¹ * k.1 ∈ I ⊓ H := by
    constructor
    · rw [hratio]
      exact I.mul_mem (hmem _) (I.inv_mem (hmem _))
    · exact H.mul_mem (H.inv_mem h.2) k.2
  have hone : h.1⁻¹ * k.1 = 1 := by
    have : h.1⁻¹ * k.1 ∈ (⊥ : Subgroup C) := by rw [← hdisj]; exact hinter
    simpa using this
  apply Subtype.ext
  exact inv_mul_eq_one.mp hone

end GLS3.Chapter5
/- END Theory.SignKernelParityLift -/
