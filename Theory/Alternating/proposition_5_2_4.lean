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

public import Theory.Alternating.theorem_5_2_1_2
public import Theory.SpecificGroups.SL2.BinaryTetrahedral

/-!
# Schur covers and alternating-group local subgroups

This source development proves the double-cover structure, local quaternion
subgroups, and central-extension facts used in GLS3 Proposition 5.2.4.
Its presentation calculations follow the Schur alternating-group cover;
finite matrix calculations identify the binary tetrahedral subgroup.

The independent quaternion-by-cyclic-three matrix model is re-exported
from `Theory.SpecificGroups.SL2.BinaryTetrahedral`, preserving its original
public names. This separation makes the SL2(3) model available to ABG's
central-cover argument without importing the full alternating development.
The remaining local subgroup and presentation calculations stay here.
-/

set_option linter.style.nameCheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

/- Chapter 5-specific declarations, kept out of the general Theory library. -/

/- BEGIN KGroup.GLS3.Chapter5.proposition_5_2_4 -/
noncomputable section

/- Source: proposition_5_2_4_a.lean -/

set_option maxHeartbeats 800000
set_option maxRecDepth 10000

open Theory.GroupTheory
open Theory.GroupTheory.Covering

namespace GLS3.Chapter5.SchurPresentation

public theorem orderOf_eq_four_of_sq_ne_one_of_pow_four_eq_one
    {G : Type*} [Group G] (x : G)
    (hfour : x ^ 4 = 1) (hsq : x ^ 2 ≠ 1) :
    orderOf x = 4 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (n := 4) (by norm_num) hfour
  intro p hp hpdvd
  have hp_dvd_two : p ∣ 2 := hp.dvd_of_dvd_pow (n := 2) (by
    simpa [show (4 : Nat) = 2 ^ 2 by norm_num] using hpdvd)
  have hp2 : p = 2 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp_dvd_two
  subst p
  simpa using hsq

namespace DoubleCoverUniqueness

public theorem ker_pow_two_eq_one
    {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hcard : Nat.card f.ker = 2)
    {x : G} (hx : x ∈ f.ker) : x ^ 2 = 1 := by
  have h := pow_card_eq_one' (x := (⟨x, hx⟩ : f.ker))
  rw [hcard] at h
  simpa using congrArg Subtype.val h

@[expose]
public noncomputable def kernelInvolution
    {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hcard : Nat.card f.ker = 2) : f.ker :=
  Classical.choose ((Nat.card_eq_two_iff' (1 : f.ker)).mp hcard)

public theorem kernelInvolution_ne_one
    {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hcard : Nat.card f.ker = 2) :
    kernelInvolution f hcard ≠ 1 :=
  (Classical.choose_spec ((Nat.card_eq_two_iff' (1 : f.ker)).mp hcard)).1

public theorem eq_kernelInvolution_of_ne_one
    {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hcard : Nat.card f.ker = 2)
    (x : f.ker) (hx : x ≠ 1) :
    x = kernelInvolution f hcard := by
  exact (Classical.choose_spec
    ((Nat.card_eq_two_iff' (1 : f.ker)).mp hcard)).2 x hx

public theorem kernelInvolution_sq
    {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hcard : Nat.card f.ker = 2) :
    ((kernelInvolution f hcard : f.ker) : G) ^ 2 = 1 :=
  ker_pow_two_eq_one f hcard (kernelInvolution f hcard).property

public theorem eq_one_or_eq_kernelInvolution
    {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hcard : Nat.card f.ker = 2)
    {x : G} (hx : x ∈ f.ker) :
    x = 1 ∨ x = kernelInvolution f hcard := by
  let x' : f.ker := ⟨x, hx⟩
  by_cases hxone : x' = 1
  · left
    exact congrArg Subtype.val hxone
  · right
    exact congrArg Subtype.val
      (eq_kernelInvolution_of_ne_one f hcard x' hxone)

public theorem sq_eq_sq_of_apply_eq
    {G H : Type*} [Group G] [Finite G] [IsQuasisimple G]
    [Group H] [Finite H] [IsQuasisimple H]
    (f : Covering G H) (hcard : Nat.card f.toMonoidHom.ker = 2)
    {x y : G} (hxy : f x = f y) : x ^ 2 = y ^ 2 := by
  let k := x * y⁻¹
  have hk : k ∈ f.toMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    change f x * (f y)⁻¹ = 1
    rw [hxy]
    simp
  have hk2 : k ^ 2 = 1 := ker_pow_two_eq_one f.toMonoidHom hcard hk
  have hkcenter : k ∈ Subgroup.center G := f.ker_le_center hk
  have hcomm : Commute k y :=
    (Subgroup.mem_center_iff.mp hkcenter y).symm
  have hxy' : x = k * y := by
    simp [k]
  calc
    x ^ 2 = (k * y) ^ 2 := by rw [hxy']
    _ = k ^ 2 * y ^ 2 := hcomm.mul_pow 2
    _ = y ^ 2 := by rw [hk2]; simp

public theorem sq_eq_sq_of_conjugate_images
    {G H : Type*} [Group G] [Finite G] [IsQuasisimple G]
    [Group H] [Finite H] [IsQuasisimple H]
    (f : Covering G H) (hcard : Nat.card f.toMonoidHom.ker = 2)
    {x y : G} {c : H} (hx : f x ^ 2 = 1)
    (hconj : c * f x * c⁻¹ = f y) : x ^ 2 = y ^ 2 := by
  obtain ⟨d, rfl⟩ := f.surjective c
  change f d * f x * (f d)⁻¹ = f y at hconj
  have himage : f (d * x * d⁻¹) = f y := by
    simpa only [map_mul, map_inv] using hconj
  have hsquares := sq_eq_sq_of_apply_eq f hcard himage
  have hxker : x ^ 2 ∈ f.toMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    change f x ^ 2 = 1
    exact hx
  have hxcenter : x ^ 2 ∈ Subgroup.center G := f.ker_le_center hxker
  have hcomm : d * x ^ 2 = x ^ 2 * d :=
    Subgroup.mem_center_iff.mp hxcenter d
  calc
    x ^ 2 = (d * x * d⁻¹) ^ 2 := by
      rw [show (d * x * d⁻¹) ^ 2 = d * x ^ 2 * d⁻¹ by
        simp [pow_two, mul_assoc]]
      rw [hcomm]
      simp
    _ = y ^ 2 := hsquares

@[expose]
public noncomputable def suzukiLift
    {G : Type*} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (i : Fin (n + 3)) : G :=
  Classical.choose (f.surjective (alternatingSuzukiGenerator n i))

public theorem suzukiLift_apply
    {G : Type*} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (i : Fin (n + 3)) :
    f (suzukiLift n f i) = alternatingSuzukiGenerator n i :=
  Classical.choose_spec (f.surjective (alternatingSuzukiGenerator n i))

public theorem suzukiLift_zero_pow_three_mem_ker
    {G : Type*} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5)))) :
    suzukiLift n f (0 : Fin (n + 3)) ^ 3 ∈ f.toMonoidHom.ker := by
  rw [MonoidHom.mem_ker]
  change f (suzukiLift n f (0 : Fin (n + 3)) ^ 3) = 1
  rw [map_pow, suzukiLift_apply,
    alternatingSuzukiGenerator_zero_pow_three]

public theorem suzukiLift_tail_sq_mem_ker
    {G : Type*} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (i : Fin (n + 3)) (hi : i ≠ 0) :
    suzukiLift n f i ^ 2 ∈ f.toMonoidHom.ker := by
  rw [MonoidHom.mem_ker]
  change f (suzukiLift n f i ^ 2) = 1
  rw [map_pow, suzukiLift_apply,
    alternatingSuzukiGenerator_tail_sq n i hi]

public theorem suzukiLift_tail_sq_eq
    {G : Type*} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (hn : 1 ≤ n)
    (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    {i j : Fin (n + 3)} (hi : i ≠ 0) (hj : j ≠ 0) :
    suzukiLift n f i ^ 2 = suzukiLift n f j ^ 2 := by
  obtain ⟨c, hc⟩ := isConj_iff.mp
    (alternatingSuzukiGenerator_tail_isConj n hn hi hj)
  apply sq_eq_sq_of_conjugate_images f hcard (c := c)
  · rw [suzukiLift_apply, alternatingSuzukiGenerator_tail_sq n i hi]
  · simpa only [suzukiLift_apply] using hc

public theorem suzukiLift_tail_sq_eq_kernelInvolution_of_ne_one
    {G : Type*} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (i : Fin (n + 3)) (hi : i ≠ 0)
    (hne : suzukiLift n f i ^ 2 ≠ 1) :
    suzukiLift n f i ^ 2 = kernelInvolution f.toMonoidHom hcard := by
  let x : f.toMonoidHom.ker :=
    ⟨suzukiLift n f i ^ 2, suzukiLift_tail_sq_mem_ker n f i hi⟩
  have hx : x ≠ 1 := by
    intro h
    apply hne
    exact congrArg Subtype.val h
  exact congrArg Subtype.val
    (eq_kernelInvolution_of_ne_one f.toMonoidHom hcard x hx)

public theorem suzukiLift_all_tail_sq_eq_kernelInvolution_of_ne_one
    {G : Type*} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (hn : 1 ≤ n)
    (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    {i : Fin (n + 3)} (hi : i ≠ 0)
    (hne : suzukiLift n f i ^ 2 ≠ 1)
    (j : Fin (n + 3)) (hj : j ≠ 0) :
    suzukiLift n f j ^ 2 = kernelInvolution f.toMonoidHom hcard := by
  rw [← suzukiLift_tail_sq_eq n hn f hcard hi hj]
  exact suzukiLift_tail_sq_eq_kernelInvolution_of_ne_one n f hcard i hi hne

public theorem suzukiLift_zero_succ_mul_pow_three_mem_ker
    {G : Type*} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5)))) :
    (suzukiLift n f (0 : Fin (n + 3)) *
      suzukiLift n f ((0 : Fin (n + 2)).succ)) ^ 3 ∈
      f.toMonoidHom.ker := by
  rw [MonoidHom.mem_ker]
  change f ((suzukiLift n f (0 : Fin (n + 3)) *
    suzukiLift n f ((0 : Fin (n + 2)).succ)) ^ 3) = 1
  rw [map_pow, map_mul, suzukiLift_apply, suzukiLift_apply,
    alternatingSuzukiGenerator_zero_succ_mul_pow_three]

public theorem suzukiLift_tail_mul_pow_three_mem_ker
    {G : Type*} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (i : Fin (n + 2)) (hi : i ≠ 0) :
    (suzukiLift n f i.castSucc * suzukiLift n f i.succ) ^ 3 ∈
      f.toMonoidHom.ker := by
  rw [MonoidHom.mem_ker]
  change f ((suzukiLift n f i.castSucc * suzukiLift n f i.succ) ^ 3) = 1
  rw [map_pow, map_mul, suzukiLift_apply, suzukiLift_apply,
    alternatingSuzukiGenerator_tail_mul_pow_three n i hi]

public theorem suzukiLift_tail_far_mul_sq_mem_ker
    {G : Type*} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    {i j : Fin (n + 3)} (hi : i ≠ 0) (hj : j ≠ 0)
    (hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    (suzukiLift n f i * suzukiLift n f j) ^ 2 ∈ f.toMonoidHom.ker := by
  rw [MonoidHom.mem_ker]
  change f ((suzukiLift n f i * suzukiLift n f j) ^ 2) = 1
  rw [map_pow, map_mul, suzukiLift_apply, suzukiLift_apply,
    alternatingSuzukiGenerator_tail_far_mul_sq n hi hj hfar]

public theorem orderOf_suzukiLift_tail_eq_four_of_nontrivial_square
    {G : Type*} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (i : Fin (n + 3)) (hi : i ≠ 0)
    (hsq : suzukiLift n f i ^ 2 ≠ 1) :
    orderOf (suzukiLift n f i) = 4 := by
  have hsq_mem := suzukiLift_tail_sq_mem_ker n f i hi
  have hker_sq : (suzukiLift n f i ^ 2) ^ 2 = 1 := by
    exact ker_pow_two_eq_one f.toMonoidHom hcard hsq_mem
  apply orderOf_eq_four_of_sq_ne_one_of_pow_four_eq_one
  · calc
      suzukiLift n f i ^ 4 = (suzukiLift n f i ^ 2) ^ 2 := by
        rw [← pow_mul]
      _ = 1 := hker_sq
  · exact hsq

end DoubleCoverUniqueness

/-- The standard Suzuki lift of a root involution in the Schur double cover
has order four. This is the explicit-presentation core of Proposition 5.2.4(a). -/
public theorem orderOf_schurSuzukiGenerator_tail (n : Nat)
    (i : Fin (n + 3)) (hi : i ≠ 0) :
    orderOf (schurSuzukiGenerator n i) = 4 := by
  have hsq : schurSuzukiGenerator n i ^ 2 = schurAlternatingCentral n :=
    schurSuzukiGenerator_tail_sq n i hi
  have hfour : schurSuzukiGenerator n i ^ 4 = 1 := by
    rw [show (4 : Nat) = 2 * 2 by norm_num, pow_mul, hsq,
      schurAlternatingCentral_sq]
  apply orderOf_eq_four_of_sq_ne_one_of_pow_four_eq_one
  · exact hfour
  · simpa [hsq] using schurAlternatingCentral_ne_one n

/-- Printed Proposition 5.2.4(a), in the part determined by the current
covering API: a Suzuki lift with nontrivial square in a double cover has
order four. -/
public theorem proposition_5_2_4_a
    {G : Type*} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (i : Fin (n + 3)) (hi : i ≠ 0)
    (hsq : DoubleCoverUniqueness.suzukiLift n f i ^ 2 ≠ 1) :
    orderOf (DoubleCoverUniqueness.suzukiLift n f i) = 4 :=
  DoubleCoverUniqueness.orderOf_suzukiLift_tail_eq_four_of_nontrivial_square
    n f hcard i hi hsq

/-- Proposition 5.2.4(a), for the explicit Schur-cover representatives of
the root-involution class. -/
public theorem proposition_5_2_4_a_standard (n : Nat)
    (i : Fin (n + 3)) (hi : i ≠ 0) :
    orderOf (schurSuzukiGenerator n i) = 4 :=
  orderOf_schurSuzukiGenerator_tail n i hi

end GLS3.Chapter5.SchurPresentation

/- Source: proposition_5_2_4_e.lean -/

set_option maxHeartbeats 800000
set_option maxRecDepth 10000

namespace GLS3.Chapter5.SchurPresentation

/-! ## Root-block algebra in the Schur double cover (Proposition 5.2.4(e,f) core)

The full presented group `SchurPresentedGroup n` is the double cover of
`Equiv.Perm (Fin (n+5))`; `SchurAlternatingGroup n` is the preimage of the
alternating subgroup.  The `adjacentLift` elements are lifts of transpositions;
the root-block words `rootBlockWord n j h = t_{4j} * t_{4j+2}` lift the root
involutions `(4j,4j+1)(4j+2,4j+3)`.  This module proves the algebra behind the
printed Proposition 5.2.4(e): the preimage in the double cover of the subgroup
generated by an involution moving `4m` points is elementary abelian of order
four when `m` is even and cyclic of order four when `m` is odd.
-/

/-! ### Adjacent-transposition lifts -/

/-- The lift of the transposition `(i, i+1)` in the full presented group. -/
@[expose] public def adjacentLift (n : Nat) (i : Fin (n + 4)) : SchurPresentedGroup n :=
  PresentedGroup.of (.adjacent i)

/-- `t_i⁻¹ = z * t_i`, where `z = schurCentral n` is the central element. -/
public theorem adjacentLift_inv (n : Nat) (i : Fin (n + 4)) :
    (adjacentLift n i)⁻¹ = schurCentral n * adjacentLift n i := by
  let a := adjacentLift n i
  let z := schurCentral n
  have ha2 : a * a = z := by
    simpa [a, z, adjacentLift, pow_two] using schurAdjacent_sq n i
  have hza : Commute z a := schurCentral_commutes_generator n (.adjacent i)
  apply (eq_inv_of_mul_eq_one_right (a := a) (b := z * a) ?_).symm
  calc
    a * (z * a) = (a * z) * a := by simp [mul_assoc]
    _ = (z * a) * a := by rw [hza.eq.symm]
    _ = z * (a * a) := by simp [mul_assoc]
    _ = z * z := by rw [ha2]
    _ = 1 := by simpa [z, pow_two] using schurCentral_sq n

/-- Lifts of far-apart transpositions anticommute up to the central element:
`t_i * t_j = z * t_j * t_i` for `|i - j| > 1`. -/
public theorem adjacentLift_far_anticommute (n : Nat) {i j : Fin (n + 4)}
    (hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    adjacentLift n i * adjacentLift n j =
      schurCentral n * adjacentLift n j * adjacentLift n i := by
  let a := adjacentLift n i
  let b := adjacentLift n j
  let z := schurCentral n
  have hz : Commute z b := schurCentral_commutes_generator n (.adjacent j)
  have hs := schurAdjacent_far_sandwich n hfar
  have h1 : a * b = b * a⁻¹ := by
    have h' : (a * b * a) * a⁻¹ = b * a⁻¹ := by
      simpa [a, b, adjacentLift] using
        congrArg (fun y : SchurPresentedGroup n => y * a⁻¹) hs
    rwa [mul_assoc, mul_inv_cancel, mul_one] at h'
  calc
    a * b = b * a⁻¹ := h1
    _ = b * (z * a) := by rw [adjacentLift_inv n i]
    _ = z * b * a := by
      calc
        b * (z * a) = (b * z) * a := by simp [mul_assoc]
        _ = (z * b) * a := by rw [← hz.eq]

/-! ### Root blocks -/

/-- The first transposition index `4j` of block `j`. -/
@[expose] public def rootBlockFirst (n : Nat) (j : Nat) (h : 4 * j + 2 < n + 4) :
    Fin (n + 4) :=
  ⟨4 * j, by omega⟩

/-- The second transposition index `4j+2` of block `j`. -/
@[expose] public def rootBlockSecond (n : Nat) (j : Nat) (h : 4 * j + 2 < n + 4) :
    Fin (n + 4) :=
  ⟨4 * j + 2, h⟩

public theorem rootBlockFirst_irrel (n j : Nat) (h₁ h₂ : 4 * j + 2 < n + 4) :
    rootBlockFirst n j h₁ = rootBlockFirst n j h₂ := by
  apply Fin.ext
  rfl

public theorem rootBlockSecond_irrel (n j : Nat) (h₁ h₂ : 4 * j + 2 < n + 4) :
    rootBlockSecond n j h₁ = rootBlockSecond n j h₂ := by
  apply Fin.ext
  rfl

/-- The lift in the double cover of the root involution
`(4j,4j+1)(4j+2,4j+3)`: `t_{4j} * t_{4j+2}`. -/
@[expose] public def rootBlockWord (n : Nat) (j : Nat) (h : 4 * j + 2 < n + 4) :
    SchurPresentedGroup n :=
  adjacentLift n (rootBlockFirst n j h) * adjacentLift n (rootBlockSecond n j h)

public theorem rootBlockWord_irrel (n j : Nat) (h₁ h₂ : 4 * j + 2 < n + 4) :
    rootBlockWord n j h₁ = rootBlockWord n j h₂ := by
  simp [rootBlockWord, adjacentLift]

/-- The root-involution block `(4j,4j+1)(4j+2,4j+3)` on `Fin (n+5)`. -/
@[expose] public def blockPerm (n : Nat) (j : Nat) (h : 4 * j + 2 < n + 4) :
    Equiv.Perm (Fin (n + 5)) :=
  Equiv.swap ⟨4 * j, by omega⟩ ⟨4 * j + 1, by omega⟩ *
    Equiv.swap ⟨4 * j + 2, by omega⟩ ⟨4 * j + 3, by omega⟩

public theorem blockPerm_irrel (n j : Nat) (h₁ h₂ : 4 * j + 2 < n + 4) :
    blockPerm n j h₁ = blockPerm n j h₂ := by
  simp [blockPerm]

/-- A root-block lift squares to the central element. -/
public theorem rootBlockWord_sq (n : Nat) (j : Nat) (h : 4 * j + 2 < n + 4) :
    rootBlockWord n j h ^ 2 = schurCentral n := by
  have hfar : (rootBlockFirst n j h).val + 1 < (rootBlockSecond n j h).val := by
    simp [rootBlockFirst, rootBlockSecond]
  simpa [rootBlockWord, adjacentLift] using
    schurAdjacent_far_mul_sq n (i := rootBlockFirst n j h) (j := rootBlockSecond n j h)
      (Or.inl hfar)

/-- The projection of a root block word is the corresponding block permutation. -/
public theorem rootBlockWord_proj (n : Nat) (j : Nat) (h : 4 * j + 2 < n + 4) :
    schurSymmetricProjection n (rootBlockWord n j h) = blockPerm n j h := by
  simp [rootBlockWord, blockPerm, rootBlockFirst, rootBlockSecond, adjacentLift,
    schurSymmetricProjection_adjacent, adjacentSwap]

/-- Root-block lifts in distinct blocks commute. -/
public theorem rootBlockWord_commute (n : Nat) {i j : Nat}
    (hi : 4 * i + 2 < n + 4) (hj : 4 * j + 2 < n + 4) (hij : i ≠ j) :
    rootBlockWord n i hi * rootBlockWord n j hj =
      rootBlockWord n j hj * rootBlockWord n i hi := by
  let a0 := rootBlockFirst n i hi
  let a2 := rootBlockSecond n i hi
  let b0 := rootBlockFirst n j hj
  let b2 := rootBlockSecond n j hj
  let a := adjacentLift n a0
  let c := adjacentLift n a2
  let b := adjacentLift n b0
  let d := adjacentLift n b2
  let z := schurCentral n
  have hcb : a2.val + 1 < b0.val ∨ b0.val + 1 < a2.val := by
    simp [a2, b0, rootBlockFirst, rootBlockSecond]; omega
  have hab : a0.val + 1 < b0.val ∨ b0.val + 1 < a0.val := by
    simp [a0, b0, rootBlockFirst]; omega
  have hcd : a2.val + 1 < b2.val ∨ b2.val + 1 < a2.val := by
    simp [a2, b2, rootBlockSecond]; omega
  have had : a0.val + 1 < b2.val ∨ b2.val + 1 < a0.val := by
    simp [a0, b2, rootBlockFirst, rootBlockSecond]; omega
  have hza : Commute z a := schurCentral_commutes_generator n (.adjacent a0)
  have hz2 : z * z = 1 := by
    simpa [z, pow_two] using schurCentral_sq n
  calc
    (a * c) * (b * d) = a * (c * b) * d := by simp [mul_assoc]
    _ = a * (z * b * c) * d := by
      rw [adjacentLift_far_anticommute n (i := a2) (j := b0) hcb]
    _ = z * (a * b) * c * d := by
      calc
        a * (z * b * c) * d = (a * z) * (b * c) * d := by simp [mul_assoc]
        _ = (z * a) * (b * c) * d := by rw [hza.eq.symm]
        _ = z * (a * b) * c * d := by simp [mul_assoc]
    _ = z * (z * b * a) * c * d := by
      rw [adjacentLift_far_anticommute n (i := a0) (j := b0) hab]
    _ = b * a * c * d := by
      calc
        z * (z * b * a) * c * d = ((z * z) * (b * a)) * c * d := by simp [mul_assoc]
        _ = (1 * (b * a)) * c * d := by rw [hz2]
        _ = b * a * c * d := by simp [mul_assoc]
    _ = b * (a * (z * d * c)) := by
      calc
        b * a * c * d = b * (a * (c * d)) := by simp [mul_assoc]
        _ = b * (a * (z * d * c)) := by
          apply congrArg (fun w : SchurPresentedGroup n => b * (a * w))
          exact adjacentLift_far_anticommute n (i := a2) (j := b2) hcd
    _ = b * (z * (z * d * a) * c) := by
      calc
        b * (a * (z * d * c)) = b * (a * z * d * c) := by simp [mul_assoc]
        _ = b * (z * a * d * c) := by rw [hza.eq.symm]
        _ = b * (z * (a * d) * c) := by simp [mul_assoc]
        _ = b * (z * (z * d * a) * c) := by
          apply congrArg (fun w : SchurPresentedGroup n => b * (z * w * c))
          exact adjacentLift_far_anticommute n (i := a0) (j := b2) had
    _ = b * (d * a * c) := by
      calc
        b * (z * (z * d * a) * c) = b * ((z * z) * (d * a) * c) := by simp [mul_assoc]
        _ = b * (1 * (d * a) * c) := by rw [hz2]
        _ = b * (d * a * c) := by simp [mul_assoc]
    _ = (b * d) * (a * c) := by simp [mul_assoc]

/-- The sign of a root-involution block is trivial. -/
public theorem blockPerm_sign (n : Nat) (j : Nat) (h : 4 * j + 2 < n + 4) :
    Equiv.Perm.sign (blockPerm n j h) = 1 := by
  unfold blockPerm
  rw [Equiv.Perm.sign_mul]
  have h1 : (⟨4 * j, by omega⟩ : Fin (n + 5)) ≠ ⟨4 * j + 1, by omega⟩ := by
    intro hh
    have := congrArg Fin.val hh
    simp at this
  have h2 : (⟨4 * j + 2, by omega⟩ : Fin (n + 5)) ≠ ⟨4 * j + 3, by omega⟩ := by
    intro hh
    have := congrArg Fin.val hh
    simp at this
  rw [Equiv.Perm.sign_swap h1, Equiv.Perm.sign_swap h2]
  norm_num

/-- A root-involution block of index `j ≥ 1` fixes `0`. -/
public theorem blockPerm_fixes_zero (n : Nat) (j : Nat) (h : 4 * j + 2 < n + 4)
    (hj : 1 ≤ j) : blockPerm n j h 0 = 0 := by
  unfold blockPerm
  rw [Equiv.Perm.mul_apply]
  have hne1 : (0 : Fin (n + 5)) ≠ ⟨4 * j + 2, by omega⟩ := by
    intro hh
    have := congrArg Fin.val hh
    simp at this
  have hne2 : (0 : Fin (n + 5)) ≠ ⟨4 * j + 3, by omega⟩ := by
    intro hh
    have := congrArg Fin.val hh
    simp at this
  have hcd :
      Equiv.swap (⟨4 * j + 2, by omega⟩ : Fin (n + 5))
        (⟨4 * j + 3, by omega⟩ : Fin (n + 5)) 0 = 0 := by
    exact Equiv.swap_apply_of_ne_of_ne hne1 hne2
  rw [hcd]
  have hne3 : (0 : Fin (n + 5)) ≠ ⟨4 * j, by omega⟩ := by
    intro hh
    have := congrArg Fin.val hh
    simp at this
    omega
  have hne4 : (0 : Fin (n + 5)) ≠ ⟨4 * j + 1, by omega⟩ := by
    intro hh
    have := congrArg Fin.val hh
    simp at this
  exact Equiv.swap_apply_of_ne_of_ne hne3 hne4

/-- The block of index `0` sends `0` to `1`. -/
public theorem blockPerm_apply_zero (n : Nat) (h : 4 * 0 + 2 < n + 4) :
    blockPerm n 0 h 0 = 1 := by
  unfold blockPerm
  rw [Equiv.Perm.mul_apply]
  have hne1 : (0 : Fin (n + 5)) ≠ ⟨4 * 0 + 2, by omega⟩ := by
    intro hh
    have := congrArg Fin.val hh
    simp at this
  have hne2 : (0 : Fin (n + 5)) ≠ ⟨4 * 0 + 3, by omega⟩ := by
    intro hh
    have := congrArg Fin.val hh
    simp at this
  have hcd :
      Equiv.swap (⟨4 * 0 + 2, by omega⟩ : Fin (n + 5))
        (⟨4 * 0 + 3, by omega⟩ : Fin (n + 5)) 0 = 0 := by
    exact Equiv.swap_apply_of_ne_of_ne hne1 hne2
  rw [hcd]
  have hne3 : (⟨4 * 0, by omega⟩ : Fin (n + 5)) ≠ ⟨4 * 0 + 1, by omega⟩ := by
    intro hh
    have := congrArg Fin.val hh
    simp at this
  simp

/-! ### The canonical word and permutation -/

/-- The canonical lift `u_0 * u_1 * ⋯ * u_{m-1}` of the involution moving
`{0, …, 4m-1}`. -/
@[expose] public def canonicalWord (n m : Nat) (h4m : 4 * m ≤ n + 5) :
    SchurPresentedGroup n :=
  match m with
  | 0 => 1
  | k + 1 => canonicalWord n k (by omega) * rootBlockWord n k (by omega)

/-- The canonical involution moving `{0, …, 4m-1}` on `Fin (n+5)`. -/
@[expose] public def canonicalPerm (n m : Nat) (h4m : 4 * m ≤ n + 5) :
    Equiv.Perm (Fin (n + 5)) :=
  match m with
  | 0 => 1
  | k + 1 => canonicalPerm n k (by omega) * blockPerm n k (by omega)

public theorem canonicalWord_irrel (n m : Nat) (h₁ h₂ : 4 * m ≤ n + 5) :
    canonicalWord n m h₁ = canonicalWord n m h₂ := by
  induction m with
  | zero =>
      simp [canonicalWord]
  | succ k ih =>
      simp [canonicalWord]

public theorem canonicalPerm_irrel (n m : Nat) (h₁ h₂ : 4 * m ≤ n + 5) :
    canonicalPerm n m h₁ = canonicalPerm n m h₂ := by
  induction m with
  | zero =>
      simp [canonicalPerm]
  | succ k ih =>
      simp [canonicalPerm]

/-- Every block commutes with the product of all earlier blocks (in fact with
any block, since distinct blocks commute). -/
public theorem canonicalWord_commutes_any (n k : Nat) (h4k : 4 * k ≤ n + 5)
    {j : Nat} (hj : 4 * j + 2 < n + 4) :
    Commute (canonicalWord n k h4k) (rootBlockWord n j hj) := by
  induction k with
  | zero =>
      simp [canonicalWord]
  | succ k ih =>
      have h4k' : 4 * k ≤ n + 5 := by omega
      have hk : 4 * k + 2 < n + 4 := by omega
      simp [canonicalWord]
      rw [canonicalWord_irrel n k _ h4k', rootBlockWord_irrel n k _ hk]
      have hw : Commute (canonicalWord n k h4k') (rootBlockWord n j hj) := ih h4k'
      have hu : Commute (rootBlockWord n k hk) (rootBlockWord n j hj) := by
        by_cases hkj : k = j
        · subst j
          exact Commute.refl _
        · exact rootBlockWord_commute n hk hj hkj
      exact Commute.mul_left hw hu

/-- The canonical word squares to `z^m`. -/
public theorem canonicalWord_sq (n m : Nat) (h4m : 4 * m ≤ n + 5) :
    canonicalWord n m h4m ^ 2 = schurCentral n ^ m := by
  induction m with
  | zero =>
      simp [canonicalWord]
  | succ k ih =>
      have h4k : 4 * k ≤ n + 5 := by omega
      have hk : 4 * k + 2 < n + 4 := by omega
      simp [canonicalWord]
      rw [canonicalWord_irrel n k _ h4k, rootBlockWord_irrel n k _ hk]
      have hc : Commute (canonicalWord n k h4k) (rootBlockWord n k hk) :=
        canonicalWord_commutes_any n k h4k hk
      calc
        (canonicalWord n k h4k * rootBlockWord n k hk) ^ 2 =
            (canonicalWord n k h4k) ^ 2 * (rootBlockWord n k hk) ^ 2 := hc.mul_pow 2
        _ = schurCentral n ^ k * schurCentral n := by
          rw [ih, rootBlockWord_sq n k hk]
        _ = schurCentral n ^ (k + 1) := by
          rw [pow_succ]

/-- The projection of the canonical word is the canonical permutation. -/
public theorem canonicalWord_proj (n m : Nat) (h4m : 4 * m ≤ n + 5) :
    schurSymmetricProjection n (canonicalWord n m h4m) = canonicalPerm n m h4m := by
  induction m with
  | zero =>
      simp [canonicalWord, canonicalPerm]
  | succ k ih =>
      have h4k : 4 * k ≤ n + 5 := by omega
      have hk : 4 * k + 2 < n + 4 := by omega
      simp [canonicalWord, canonicalPerm]
      rw [canonicalWord_irrel n k _ h4k, rootBlockWord_irrel n k _ hk,
        canonicalPerm_irrel n k _ h4k, blockPerm_irrel n k _ hk]
      rw [ih, rootBlockWord_proj]

/-- For `m ≥ 1`, the canonical permutation sends `0` to `1`. -/
public theorem canonicalPerm_apply_zero (n m : Nat) (h4m : 4 * m ≤ n + 5)
    (hm : 1 ≤ m) : canonicalPerm n m h4m 0 = 1 := by
  induction m with
  | zero =>
      omega
  | succ k ih =>
      by_cases hk : 1 ≤ k
      · have h4k : 4 * k ≤ n + 5 := by omega
        have hk2 : 4 * k + 2 < n + 4 := by omega
        simp [canonicalPerm]
        rw [canonicalPerm_irrel n k _ h4k, blockPerm_irrel n k _ hk2]
        rw [blockPerm_fixes_zero n k hk2 hk]
        exact ih h4k hk
      · have hk0 : k = 0 := by omega
        subst k
        have h0 : 4 * 0 + 2 < n + 4 := by omega
        simp [canonicalPerm]
        rw [blockPerm_irrel n 0 _ h0]
        exact blockPerm_apply_zero n h0

/-- The canonical permutation is not the identity. -/
public theorem canonicalPerm_ne_one (n m : Nat) (h4m : 4 * m ≤ n + 5) (hm : 1 ≤ m) :
    canonicalPerm n m h4m ≠ 1 := by
  intro h
  have h0 := congrArg (fun f : Equiv.Perm (Fin (n + 5)) => f 0) h
  rw [canonicalPerm_apply_zero n m h4m hm] at h0
  simp at h0

/-! ### The canonical lift in the alternating double cover -/

/-- The sign of the canonical permutation is trivial. -/
public theorem canonicalPerm_sign (n m : Nat) (h4m : 4 * m ≤ n + 5) :
    Equiv.Perm.sign (canonicalPerm n m h4m) = 1 := by
  induction m with
  | zero =>
      simp [canonicalPerm]
  | succ k ih =>
      have h4k : 4 * k ≤ n + 5 := by omega
      have hk : 4 * k + 2 < n + 4 := by omega
      simp [canonicalPerm]
      rw [canonicalPerm_irrel n k _ h4k, blockPerm_irrel n k _ hk]
      rw [ih h4k, blockPerm_sign n k hk]
      simp

/-- The canonical lift in the alternating double cover. -/
@[expose]
public noncomputable def canonicalLift (n m : Nat) (h4m : 4 * m ≤ n + 5) :
    SchurAlternatingGroup n :=
  ⟨canonicalWord n m h4m, by
    rw [Subgroup.mem_comap, Equiv.Perm.mem_alternatingGroup]
    rw [canonicalWord_proj]
    exact canonicalPerm_sign n m h4m⟩

/-- The projection of the canonical lift is the canonical involution. -/
public theorem canonicalLift_proj (n m : Nat) (h4m : 4 * m ≤ n + 5) :
    (schurAlternatingProjection n (canonicalLift n m h4m) :
        Equiv.Perm (Fin (n + 5))) = canonicalPerm n m h4m := by
  change schurSymmetricProjection n (canonicalWord n m h4m) = canonicalPerm n m h4m
  exact canonicalWord_proj n m h4m

/-- The canonical lift squares to `z^m`. -/
public theorem canonicalLift_sq (n m : Nat) (h4m : 4 * m ≤ n + 5) :
    canonicalLift n m h4m ^ 2 = schurAlternatingCentral n ^ m := by
  apply Subtype.ext
  change canonicalWord n m h4m ^ 2 = schurCentral n ^ m
  exact canonicalWord_sq n m h4m

/-! ### The preimage analysis (Proposition 5.2.4(e)) -/

namespace InvolutionPreimage

/-- The preimage of the cyclic subgroup generated by an involution. -/
@[expose] public def involutionPreimage (n : Nat) (x : SchurAlternatingGroup n) :
    Subgroup (SchurAlternatingGroup n) :=
  (Subgroup.zpowers (schurAlternatingProjection n x)).comap (schurAlternatingProjection n)

/-- The subgroup generated by an element of order two has exactly two elements. -/
public theorem zpowers_mem_cases_of_order_two {G : Type*} [Group G] (g : G)
    (hg : orderOf g = 2) {h : G} (hh : h ∈ Subgroup.zpowers g) : h = 1 ∨ h = g := by
  let H := Subgroup.zpowers g
  have hcard : Nat.card (↥H) = 2 := by
    rw [Nat.card_zpowers, hg]
  rcases (Nat.card_eq_two_iff' (1 : ↥H)).mp hcard with ⟨y, hy, hy2⟩
  have hgmem : g ∈ H := Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
  have hgne : (⟨g, hgmem⟩ : ↥H) ≠ 1 := by
    intro hh
    have hg1 := congrArg Subtype.val hh
    have this := congrArg orderOf hg1
    change orderOf g = orderOf (1 : G) at this
    rw [hg, orderOf_one] at this
    norm_num at this
  by_cases hh1 : h = 1
  · left
    exact hh1
  · right
    have hne : (⟨h, hh⟩ : ↥H) ≠ 1 := by
      intro hhh
      exact hh1 (congrArg Subtype.val hhh)
    have heq : (⟨h, hh⟩ : ↥H) = y := hy2 ⟨h, hh⟩ hne
    exact congrArg Subtype.val (heq.trans (hy2 ⟨g, hgmem⟩ hgne).symm)

/-- The kernel of the alternating projection is `{1, z}`. -/
public theorem ker_mem_cases (n : Nat) {y : SchurAlternatingGroup n}
    (hy : y ∈ (schurAlternatingProjection n).ker) :
    y = 1 ∨ y = schurAlternatingCentral n := by
  let f := (schurAlternatingCovering n).toMonoidHom
  have hcard : Nat.card f.ker = 2 := natCard_ker_schurAlternatingCovering n
  rcases DoubleCoverUniqueness.eq_one_or_eq_kernelInvolution f hcard (by
    change y ∈ (schurAlternatingProjection n).ker
    exact hy) with h | h
  · exact Or.inl h
  · right
    have hz : (DoubleCoverUniqueness.kernelInvolution f hcard : SchurAlternatingGroup n) =
        schurAlternatingCentral n := by
      have hzmem : schurAlternatingCentral n ∈ f.ker := by
        rw [MonoidHom.mem_ker]
        change schurAlternatingProjection n (schurAlternatingCentral n) = 1
        exact MonoidHom.mem_ker.mp (schurAlternatingCentral_mem_ker n)
      let z' : f.ker := ⟨schurAlternatingCentral n, hzmem⟩
      have hz' : z' ≠ 1 := by
        intro hh
        apply schurAlternatingCentral_ne_one n
        exact congrArg Subtype.val hh
      have hzker : DoubleCoverUniqueness.kernelInvolution f hcard = z' :=
        (DoubleCoverUniqueness.eq_kernelInvolution_of_ne_one f hcard z' hz').symm
      exact congrArg Subtype.val hzker
    exact h.trans hz

/-- Elements of the preimage of `⟨x̄⟩` are `1`, `x`, `z` or `x z`. -/
public theorem preimage_mem_cases (n : Nat) {x : SchurAlternatingGroup n}
    (hx2 : orderOf (schurAlternatingProjection n x) = 2)
    {y : SchurAlternatingGroup n} (hy : y ∈ involutionPreimage n x) :
    y = 1 ∨ y = x ∨ y = schurAlternatingCentral n ∨ y = x * schurAlternatingCentral n := by
  have hπy : schurAlternatingProjection n y ∈
      Subgroup.zpowers (schurAlternatingProjection n x) :=
    (Subgroup.mem_comap).mp hy
  rcases Subgroup.mem_zpowers_iff.mp hπy with ⟨k, hk⟩
  rcases zpowers_mem_cases_of_order_two (schurAlternatingProjection n x) hx2 hπy with h | h
  · -- π y = 1
    have hker : y ∈ (schurAlternatingProjection n).ker := by
      rw [MonoidHom.mem_ker]
      exact h
    rcases ker_mem_cases n hker with h1 | hz
    · exact Or.inl h1
    · exact Or.inr (Or.inr (Or.inl hz))
  · -- π y = π x
    right
    have hker : y * x⁻¹ ∈ (schurAlternatingProjection n).ker := by
      rw [MonoidHom.mem_ker]
      rw [map_mul, map_inv, h]
      exact mul_inv_cancel (schurAlternatingProjection n x)
    rcases ker_mem_cases n hker with h1 | hz
    · left
      exact (mul_inv_eq_one.mp h1 : y = x)
    · right
      right
      have hzx : Commute x (schurAlternatingCentral n) :=
        (Subgroup.mem_center_iff.mp (schurAlternatingCentral_mem_center n) x)
      calc
        y = y * (x * x⁻¹) := by simp
        _ = (y * x⁻¹) * x := by simp [mul_assoc]
        _ = schurAlternatingCentral n * x := by rw [hz]
        _ = x * schurAlternatingCentral n := hzx.eq.symm

/-- Membership in the preimage is equivalent to being one of the four elements. -/
public theorem preimage_mem_iff (n : Nat) {x : SchurAlternatingGroup n}
    (hx2 : orderOf (schurAlternatingProjection n x) = 2) :
    ∀ y : SchurAlternatingGroup n, y ∈ involutionPreimage n x ↔
      y = 1 ∨ y = x ∨ y = schurAlternatingCentral n ∨
        y = x * schurAlternatingCentral n := by
  intro y
  constructor
  · exact preimage_mem_cases n hx2
  · intro hy
    rcases hy with rfl | rfl | rfl | rfl
    · simp [involutionPreimage]
    · rw [involutionPreimage, Subgroup.mem_comap]
      exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
    · rw [involutionPreimage, Subgroup.mem_comap]
      have hπz : schurAlternatingProjection n (schurAlternatingCentral n) = 1 := by
        simpa using (MonoidHom.mem_ker.mp (schurAlternatingCentral_mem_ker n))
      rw [hπz]
      exact Subgroup.one_mem _
    · rw [involutionPreimage, Subgroup.mem_comap]
      have hπz : schurAlternatingProjection n (schurAlternatingCentral n) = 1 := by
        simpa using (MonoidHom.mem_ker.mp (schurAlternatingCentral_mem_ker n))
      rw [map_mul, hπz, mul_one]
      exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩

/-- The image of the lift is not the identity: `x̄ ≠ 1`. -/
public theorem preimage_proj_ne_one (n : Nat) {x : SchurAlternatingGroup n}
    (hx2 : orderOf (schurAlternatingProjection n x) = 2) :
    schurAlternatingProjection n x ≠ 1 := by
  intro h
  have h1 := congrArg orderOf h
  rw [hx2, orderOf_one] at h1
  norm_num at h1

/-- The preimage of `⟨x̄⟩` has cardinality four. -/
public theorem involutionPreimage_card (n : Nat) {x : SchurAlternatingGroup n}
    (hx2 : orderOf (schurAlternatingProjection n x) = 2) :
    Nat.card (↥(involutionPreimage n x)) = 4 := by
  let L := involutionPreimage n x
  have hπx : schurAlternatingProjection n x ≠ 1 :=
    preimage_proj_ne_one n hx2
  have hxne1 : x ≠ 1 := by
    intro h
    apply hπx
    simpa using congrArg (schurAlternatingProjection n) h
  have hzneq : schurAlternatingCentral n ≠ 1 :=
    schurAlternatingCentral_ne_one n
  have hxz : schurAlternatingCentral n ≠ x := by
    intro h
    apply hπx
    have hπ : schurAlternatingProjection n (schurAlternatingCentral n) =
        schurAlternatingProjection n x := congrArg (schurAlternatingProjection n) h
    have hπz : schurAlternatingProjection n (schurAlternatingCentral n) = 1 := by
      simpa using (MonoidHom.mem_ker.mp (schurAlternatingCentral_mem_ker n))
    rw [hπz] at hπ
    exact hπ.symm
  have hxne1' : 1 ≠ x := hxne1.symm
  have hzxne : x * schurAlternatingCentral n ≠ 1 := by
    intro h
    apply hπx
    have hπ : schurAlternatingProjection n (x * schurAlternatingCentral n) =
        schurAlternatingProjection n 1 := congrArg (schurAlternatingProjection n) h
    have hπz : schurAlternatingProjection n (schurAlternatingCentral n) = 1 := by
      simpa using (MonoidHom.mem_ker.mp (schurAlternatingCentral_mem_ker n))
    rw [map_mul, hπz, mul_one, map_one] at hπ
    exact hπ
  have hxzx : x ≠ x * schurAlternatingCentral n := by
    intro h
    apply hzneq
    have h1 := congrArg (fun y : SchurAlternatingGroup n => x⁻¹ * y) h
    simpa [mul_assoc] using h1.symm
  have hzxz : schurAlternatingCentral n ≠ x * schurAlternatingCentral n := by
    intro h
    apply hxne1
    have h1 := congrArg (fun y : SchurAlternatingGroup n => y * (schurAlternatingCentral n)⁻¹) h
    simpa [mul_assoc] using h1.symm
  -- the bijection Fin 4 → L
  let fval : Nat → SchurAlternatingGroup n
    | 0 => 1
    | 1 => x
    | 2 => schurAlternatingCentral n
    | _ => x * schurAlternatingCentral n
  let f : Fin 4 → ↥L := fun i => ⟨fval i.val, by
    rcases i with ⟨i, hi⟩
    interval_cases i
    · change (1 : SchurAlternatingGroup n) ∈ involutionPreimage n x
      rw [involutionPreimage, Subgroup.mem_comap]
      rw [map_one]
      exact Subgroup.one_mem _
    · change x ∈ involutionPreimage n x
      rw [involutionPreimage, Subgroup.mem_comap]
      exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
    · change schurAlternatingCentral n ∈ involutionPreimage n x
      rw [involutionPreimage, Subgroup.mem_comap]
      have hπz : schurAlternatingProjection n (schurAlternatingCentral n) = 1 := by
        simpa using (MonoidHom.mem_ker.mp (schurAlternatingCentral_mem_ker n))
      rw [hπz]
      exact Subgroup.one_mem _
    · change x * schurAlternatingCentral n ∈ involutionPreimage n x
      rw [involutionPreimage, Subgroup.mem_comap]
      have hπz : schurAlternatingProjection n (schurAlternatingCentral n) = 1 := by
        simpa using (MonoidHom.mem_ker.mp (schurAlternatingCentral_mem_ker n))
      rw [map_mul, hπz, mul_one]
      exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩⟩
  have hsurj : Function.Surjective f := by
    intro y
    rcases preimage_mem_cases n hx2 y.2 with hy | hy | hy | hy
    · exact ⟨⟨0, by decide⟩, by apply Subtype.ext; simpa [f, fval] using hy.symm⟩
    · exact ⟨⟨1, by decide⟩, by apply Subtype.ext; simpa [f, fval] using hy.symm⟩
    · exact ⟨⟨2, by decide⟩, by apply Subtype.ext; simpa [f, fval] using hy.symm⟩
    · exact ⟨⟨3, by decide⟩, by apply Subtype.ext; simpa [f, fval] using hy.symm⟩
  have hinj : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp [f, fval] at hab ⊢
    all_goals
      first
      | exact False.elim (hxne1' hab)
      | exact False.elim (hxne1' hab.symm)
      | exact False.elim (hzneq hab)
      | exact False.elim (hzneq hab.symm)
      | exact False.elim (hxz hab)
      | exact False.elim (hxz hab.symm)
      | exact False.elim (hxzx hab)
      | exact False.elim (hxzx hab.symm)
      | exact False.elim (hzxne hab)
      | exact False.elim (hzxne hab.symm)
  calc
    Nat.card (↥L) = Nat.card (Fin 4) :=
      Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩).symm
    _ = 4 := Nat.card_fin 4

/-- The preimage is a Klein four group when a lift has order two. -/
public theorem involutionPreimage_kleinFour (n : Nat) {x : SchurAlternatingGroup n}
    (hx2 : orderOf (schurAlternatingProjection n x) = 2)
    (hxsq : x ^ 2 = 1) (_hxne1 : x ≠ 1) :
    IsKleinFour (involutionPreimage n x) := by
  let L := involutionPreimage n x
  have hcard : Nat.card (↥L) = 4 := involutionPreimage_card n hx2
  have hzmemL : schurAlternatingCentral n ∈ L := by
    change schurAlternatingCentral n ∈ involutionPreimage n x
    rw [involutionPreimage, Subgroup.mem_comap]
    have hπz : schurAlternatingProjection n (schurAlternatingCentral n) = 1 := by
      simpa using (MonoidHom.mem_ker.mp (schurAlternatingCentral_mem_ker n))
    rw [hπz]
    exact Subgroup.one_mem _
  have hexp : Monoid.exponent (↥L) = 2 := by
    have hdvd : Monoid.exponent (↥L) ∣ 2 := by
      rw [Monoid.exponent_dvd]
      intro y
      have hy2 : y ^ 2 = 1 := by
        apply Subtype.ext
        change (y : SchurAlternatingGroup n) ^ 2 = 1
        rcases preimage_mem_cases n hx2 y.2 with hy | hy | hy | hy
        · rw [hy]
          simp
        · rw [hy]
          exact hxsq
        · rw [hy]
          exact schurAlternatingCentral_sq n
        · rw [hy]
          have hzx : Commute x (schurAlternatingCentral n) :=
            (Subgroup.mem_center_iff.mp (schurAlternatingCentral_mem_center n) x)
          rw [hzx.mul_pow 2, hxsq, schurAlternatingCentral_sq]
          simp
      exact orderOf_dvd_iff_pow_eq_one.mpr hy2
    have h2dvd : 2 ∣ Monoid.exponent (↥L) := by
      let z' : ↥L := ⟨schurAlternatingCentral n, hzmemL⟩
      have hzexp : z' ^ Monoid.exponent (↥L) = 1 :=
        Monoid.pow_exponent_eq_one z'
      have hord : orderOf z' = 2 := by
        rw [← Subgroup.orderOf_coe (a := z')]
        exact orderOf_schurAlternatingCentral n
      simpa [hord] using (orderOf_dvd_iff_pow_eq_one.mpr hzexp)
    exact Nat.dvd_antisymm hdvd h2dvd
  exact { card_four := hcard, exponent_two := hexp }

/-- The preimage is cyclic when a lift has order four. -/
public theorem involutionPreimage_cyclic (n : Nat) {x : SchurAlternatingGroup n}
    (hx2 : orderOf (schurAlternatingProjection n x) = 2)
    (hxsq : x ^ 2 = schurAlternatingCentral n) (_hxne1 : x ≠ 1) :
    IsCyclic (involutionPreimage n x) := by
  let L := involutionPreimage n x
  have hx4 : orderOf x = 4 := by
    apply orderOf_eq_four_of_sq_ne_one_of_pow_four_eq_one x
    · rw [show 4 = 2 * 2 by norm_num, pow_mul, hxsq, schurAlternatingCentral_sq]
    · intro h
      apply schurAlternatingCentral_ne_one n
      rw [← hxsq]
      exact h
  have hxmem : x ∈ L := by
    change x ∈ involutionPreimage n x
    rw [involutionPreimage, Subgroup.mem_comap]
    exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
  have hxorder : orderOf (⟨x, hxmem⟩ : ↥L) = 4 := by
    rw [← Subgroup.orderOf_coe (a := (⟨x, hxmem⟩ : ↥L))]
    exact hx4
  have hcard : Nat.card (↥L) = 4 := involutionPreimage_card n hx2
  exact isCyclic_of_orderOf_eq_card (⟨x, hxmem⟩ : ↥L) (by rw [hxorder, hcard])

end InvolutionPreimage

/-! ### The main statements of Proposition 5.2.4(e) -/

/-- `z^m = 1` when `m` is even. -/
public theorem central_pow_of_even (n : Nat) {m : Nat} (h : Even m) :
    schurAlternatingCentral n ^ m = 1 := by
  rcases h with ⟨t, ht⟩
  have hm : m = 2 * t := by omega
  rw [hm, pow_mul, schurAlternatingCentral_sq]
  simp

/-- `z^m = z` when `m` is odd. -/
public theorem central_pow_of_odd (n : Nat) {m : Nat} (h : Odd m) :
    schurAlternatingCentral n ^ m = schurAlternatingCentral n := by
  rcases h with ⟨t, ht⟩
  rw [ht, pow_succ, pow_mul, schurAlternatingCentral_sq]
  simp

/-- The projection of the canonical lift is an involution. -/
public theorem canonicalLift_proj_order_two (n m : Nat) (h4m : 4 * m ≤ n + 5)
    (hm : 1 ≤ m) : orderOf (schurAlternatingProjection n (canonicalLift n m h4m)) = 2 := by
  have hsq : (schurAlternatingProjection n (canonicalLift n m h4m)) ^ 2 = 1 := by
    rw [← map_pow]
    rw [canonicalLift_sq]
    rw [map_pow]
    have hπz : schurAlternatingProjection n (schurAlternatingCentral n) = 1 := by
      simpa using (MonoidHom.mem_ker.mp (schurAlternatingCentral_mem_ker n))
    rw [hπz]
    simp
  have hne : schurAlternatingProjection n (canonicalLift n m h4m) ≠ 1 := by
    intro h
    have hperm : (schurAlternatingProjection n (canonicalLift n m h4m) :
        Equiv.Perm (Fin (n + 5))) = 1 := by simpa using h
    rw [canonicalLift_proj] at hperm
    exact canonicalPerm_ne_one n m h4m hm hperm
  exact orderOf_eq_prime hsq hne

/-- Proposition 5.2.4(e), elementary-abelian case: for `m` even, the preimage
of the subgroup generated by the canonical involution moving `4m` points is
isomorphic to the Klein four group. -/
public theorem proposition_5_2_4_e_E4 (n m : Nat) (hm : 1 ≤ m) (h4m : 4 * m ≤ n + 5)
    (heven : Even m) :
    Nonempty ((InvolutionPreimage.involutionPreimage n (canonicalLift n m h4m)) ≃*
      Multiplicative (ZMod 2 × ZMod 2)) := by
  let x := canonicalLift n m h4m
  let L := InvolutionPreimage.involutionPreimage n x
  have hx2 : orderOf (schurAlternatingProjection n x) = 2 :=
    canonicalLift_proj_order_two n m h4m hm
  have hxsq : x ^ 2 = 1 := by
    rw [canonicalLift_sq]
    exact central_pow_of_even n heven
  have hxne1 : x ≠ 1 := by
    intro h
    have hπ : schurAlternatingProjection n x ≠ 1 :=
      InvolutionPreimage.preimage_proj_ne_one n hx2
    apply hπ
    simpa using congrArg (schurAlternatingProjection n) h
  let : IsKleinFour L :=
    InvolutionPreimage.involutionPreimage_kleinFour n hx2 hxsq hxne1
  exact IsKleinFour.nonempty_mulEquiv (G₁ := L)
    (G₂ := Multiplicative (ZMod 2 × ZMod 2))

/-- Proposition 5.2.4(e), cyclic case: for `m` odd, the preimage of the
subgroup generated by the canonical involution moving `4m` points is
isomorphic to the cyclic group of order four. -/
public theorem proposition_5_2_4_e_Z4 (n m : Nat) (hm : 1 ≤ m) (h4m : 4 * m ≤ n + 5)
    (hodd : Odd m) :
    Nonempty ((InvolutionPreimage.involutionPreimage n (canonicalLift n m h4m)) ≃*
      Multiplicative (ZMod 4)) := by
  let x := canonicalLift n m h4m
  let L := InvolutionPreimage.involutionPreimage n x
  have hx2 : orderOf (schurAlternatingProjection n x) = 2 :=
    canonicalLift_proj_order_two n m h4m hm
  have hxsq : x ^ 2 = schurAlternatingCentral n := by
    rw [canonicalLift_sq]
    exact central_pow_of_odd n hodd
  have hxne1 : x ≠ 1 := by
    intro h
    have hπ : schurAlternatingProjection n x ≠ 1 :=
      InvolutionPreimage.preimage_proj_ne_one n hx2
    apply hπ
    simpa using congrArg (schurAlternatingProjection n) h
  have hcyc : IsCyclic L :=
    InvolutionPreimage.involutionPreimage_cyclic n hx2 hxsq hxne1
  have hcardL : Nat.card (↥L) = 4 := InvolutionPreimage.involutionPreimage_card n hx2
  have hzmod : Multiplicative (ZMod 4) ≃* ↥L := hcardL ▸ (zmodCyclicMulEquiv hcyc)
  exact ⟨hzmod.symm⟩

end GLS3.Chapter5.SchurPresentation

/- Source: proposition_5_2_4_b.lean -/

set_option maxHeartbeats 800000
set_option maxRecDepth 10000


namespace GLS3.Chapter5.SchurPresentation

/-! ## Proposition 5.2.4(b): root `A_m`-subgroups

The root `A_m`-subgroup of `K̄ = A_{n+5}` on the first `m` points
`{0, …, m-1}` has full preimage in the double cover isomorphic to
`SchurAlternatingGroup (m-5)` (the double cover `2A_m`).  The isomorphism is
the identity shift of generators: the transposition lifts on the first `m`
points generate the preimage.
-/

/-- For a surjective homomorphism, the preimage of a subgroup has cardinality
`|K| * |ker|`. -/
public theorem card_comap_mul {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hsurj : Function.Surjective f) (K : Subgroup H) :
    Nat.card (↥(K.comap f)) = Nat.card (↥K) * Nat.card (↥f.ker) := by
  classical
  let s : H → G := fun h => Classical.choose (hsurj h)
  have hs (h : H) : f (s h) = h := Classical.choose_spec (hsurj h)
  let e : ↥K × ↥f.ker ≃ ↥(K.comap f) :=
    { toFun := fun x => ⟨s x.1.1 * x.2.1, by
        rw [Subgroup.mem_comap, map_mul, hs, MonoidHom.mem_ker.mp x.2.2, mul_one]
        exact x.1.2⟩
      invFun := fun y => ⟨⟨f y.1, (Subgroup.mem_comap.mp y.2)⟩,
        ⟨(s (f y.1))⁻¹ * y.1, by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hs, inv_mul_cancel]⟩⟩
      left_inv := by
        intro x
        apply Prod.ext
        · apply Subtype.ext
          change f (s x.1.1 * x.2.1) = x.1.1
          rw [map_mul, hs, MonoidHom.mem_ker.mp x.2.2, mul_one]
        · apply Subtype.ext
          have hk : f (s x.1.1 * x.2.1) = x.1.1 := by
            rw [map_mul, hs, MonoidHom.mem_ker.mp x.2.2, mul_one]
          calc
            (s (f (s x.1.1 * x.2.1)))⁻¹ * (s x.1.1 * x.2.1)
                = (s x.1.1)⁻¹ * (s x.1.1 * x.2.1) := by rw [hk]
            _ = x.2.1 := by simp
      right_inv := by
        intro y
        apply Subtype.ext
        calc
          s (f y.1) * ((s (f y.1))⁻¹ * y.1) = y.1 := by simp }
  rw [← Nat.card_congr e]
  rw [Nat.card_prod]

/-- The cardinality of the Schur double cover `2A_{k+5}` is `(k+5)!`. -/
public theorem card_schurAlternatingGroup (k : Nat) :
    Nat.card (SchurAlternatingGroup k) = (k + 5).factorial := by
  rw [SchurAlternatingGroup, card_comap_mul (schurSymmetricProjection k)
      (schurSymmetricProjection_surjective k) (alternatingGroup (Fin (k + 5)))]
  have hker : Nat.card (schurSymmetricProjection k).ker = 2 := by
    rw [schurSymmetricProjection_ker_eq_zpowers]
    exact natCard_zpowers_schurCentral k
  have : Nontrivial (Fin (k + 5)) :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by intro h; have := congrArg Fin.val h; norm_num at this⟩
  have halt : Nat.card (↥(alternatingGroup (Fin (k + 5)))) = (k + 5).factorial / 2 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup (α := Fin (k + 5)), Fintype.card_fin]
  rw [hker, halt]
  exact Nat.div_mul_cancel (by
    have h := Nat.factorial_dvd_factorial (by omega : 2 ≤ k + 5)
    simpa using h)

namespace RootAm

/-- The inclusion of the first `(m-5)+5` points into `Fin (n+5)`. -/
@[expose] public def tailEmbedding (n m : Nat) (hmn : m ≤ n + 5) :
    Fin ((m - 5) + 5) ↪ Fin (n + 5) :=
  ⟨fun i => ⟨i.val, by omega⟩, by
    intro i j h
    apply Fin.ext
    have h' := congrArg Fin.val h
    change (⟨i.val, by omega⟩ : Fin (n + 5)).val =
      (⟨j.val, by omega⟩ : Fin (n + 5)).val at h'
    simp at h'
    exact h'⟩

/-- The permutation embedding induced by the tail. -/
@[expose] public def tailPermHom (n m : Nat) (hmn : m ≤ n + 5) :
    Equiv.Perm (Fin ((m - 5) + 5)) →* Equiv.Perm (Fin (n + 5)) :=
  Equiv.Perm.viaEmbeddingHom (tailEmbedding n m hmn)

/-- The sign of the tail extension is the sign of the original permutation. -/
public theorem sign_tailPermHom (n m : Nat) (hmn : m ≤ n + 5)
    (σ : Equiv.Perm (Fin ((m - 5) + 5))) :
    Equiv.Perm.sign (tailPermHom n m hmn σ) = Equiv.Perm.sign σ := by
  unfold tailPermHom
  rw [Equiv.Perm.viaEmbeddingHom_apply]
  simp [Equiv.Perm.viaEmbedding]

/-- The alternating group embedding induced by the tail. -/
@[expose] public def tailAltHom (n m : Nat) (hmn : m ≤ n + 5) :
    alternatingGroup (Fin ((m - 5) + 5)) →* alternatingGroup (Fin (n + 5)) :=
  { toFun := fun σ => ⟨tailPermHom n m hmn σ.1, by
      rw [Equiv.Perm.mem_alternatingGroup, sign_tailPermHom]
      exact σ.2⟩
    map_one' := by
      apply Subtype.ext
      simp [tailPermHom]
    map_mul' := by
      intro a b
      apply Subtype.ext
      simp [tailPermHom] }

/-- The root `A_m`-subgroup: the image of the alternating group on the first
`m` points. -/
@[expose] public def rootAm (n m : Nat) (hmn : m ≤ n + 5) :
    Subgroup (alternatingGroup (Fin (n + 5))) :=
  (tailAltHom n m hmn).range

/-- The index of the `j`-th tail adjacent generator (in `Fin (n+4)`). -/
@[expose] public def tailIndex (n m : Nat) (h5 : 5 ≤ m) (hmn : m ≤ n + 5)
    (j : Fin ((m - 5) + 4)) : Fin (n + 4) :=
  ⟨j.val, by omega⟩

/-- The image of the `j`-th tail adjacent transposition under the tail
embedding is the shifted adjacent transposition. -/
public theorem tailPermHom_adjacentSwap (n m : Nat) (h5 : 5 ≤ m) (hmn : m ≤ n + 5)
    (j : Fin ((m - 5) + 4)) :
    tailPermHom n m hmn (adjacentSwap (m - 5) j) = adjacentSwap n (tailIndex n m h5 hmn j) := by
  apply Equiv.Perm.ext
  intro x
  have hι1 : tailEmbedding n m hmn j.castSucc = (tailIndex n m h5 hmn j).castSucc := by
    apply Fin.ext
    simp [tailEmbedding, tailIndex]
  have hι2 : tailEmbedding n m hmn j.succ = (tailIndex n m h5 hmn j).succ := by
    apply Fin.ext
    simp [tailEmbedding, tailIndex]
  by_cases hmem : x ∈ Set.range (tailEmbedding n m hmn)
  · rcases hmem with ⟨t, rfl⟩
    unfold tailPermHom
    rw [Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding_apply]
    by_cases ht : t = j.castSucc
    · subst t
      rw [adjacentSwap, Equiv.swap_apply_left j.castSucc j.succ]
      rw [hι2, hι1]
      rw [adjacentSwap, Equiv.swap_apply_left (tailIndex n m h5 hmn j).castSucc
        (tailIndex n m h5 hmn j).succ]
    · by_cases ht2 : t = j.succ
      · subst t
        rw [adjacentSwap, Equiv.swap_apply_right j.castSucc j.succ]
        rw [hι1, hι2]
        rw [adjacentSwap, Equiv.swap_apply_right (tailIndex n m h5 hmn j).castSucc
          (tailIndex n m h5 hmn j).succ]
      · -- t is neither endpoint: σ t = t and the swap fixes the tail point
        have hσ : (adjacentSwap (m - 5) j) t = t := by
          unfold adjacentSwap
          exact Equiv.swap_apply_of_ne_of_ne ht ht2
        calc
          tailEmbedding n m hmn ((adjacentSwap (m - 5) j) t)
              = tailEmbedding n m hmn t := by rw [hσ]
          _ = (adjacentSwap n (tailIndex n m h5 hmn j)) (tailEmbedding n m hmn t) := by
            unfold adjacentSwap
            exact (Equiv.swap_apply_of_ne_of_ne (by
              intro hx
              have ht' : t = j.castSucc := by
                apply (tailEmbedding n m hmn).2
                exact hx.trans hι1.symm
              exact ht ht') (by
              intro hx
              have ht' : t = j.succ := by
                apply (tailEmbedding n m hmn).2
                exact hx.trans hι2.symm
              exact ht2 ht')).symm
  · unfold tailPermHom
    rw [Equiv.Perm.viaEmbeddingHom_apply,
      Equiv.Perm.viaEmbedding_apply_of_notMem _ _ x hmem]
    unfold adjacentSwap
    have hn1 : x ≠ (tailIndex n m h5 hmn j).castSucc := by
      intro hx
      apply hmem
      refine ⟨j.castSucc, ?_⟩
      exact (hx.trans hι1.symm).symm
    have hn2 : x ≠ (tailIndex n m h5 hmn j).succ := by
      intro hx
      apply hmem
      refine ⟨j.succ, ?_⟩
      exact (hx.trans hι2.symm).symm
    exact (Equiv.swap_apply_of_ne_of_ne hn1 hn2).symm

/-- The map of generators from the `(m-5)`-cover to the ambient cover. -/
@[expose] public def tailGen (n m : Nat) (h5 : 5 ≤ m) (hmn : m ≤ n + 5) :
    Gen (m - 5) → SchurPresentedGroup n
  | .central => schurCentral n
  | .adjacent j => PresentedGroup.of (.adjacent (tailIndex n m h5 hmn j))

/-- The tail relators hold in the ambient cover. -/
public theorem relator_lift_tailGen (n m : Nat) (h5 : 5 ≤ m) (hmn : m ≤ n + 5)
    (r : FreeGroup (Gen (m - 5))) (hr : Relator (m - 5) r) :
    FreeGroup.lift (tailGen n m h5 hmn) r = 1 := by
  cases hr with
  | central_sq =>
      simp [zWord, tailGen, FreeGroup.lift_apply_of, schurCentral_sq]
  | central_comm i =>
      have hz : Commute (schurCentral n) (PresentedGroup.of
          (.adjacent (tailIndex n m h5 hmn i))) :=
        schurCentral_commutes_generator n (.adjacent (tailIndex n m h5 hmn i))
      calc
        FreeGroup.lift (tailGen n m h5 hmn)
            (zWord (m - 5) * tWord (m - 5) i * (zWord (m - 5))⁻¹ *
              (tWord (m - 5) i)⁻¹) = 1 := by
          simp [zWord, tWord, tailGen, FreeGroup.lift_apply_of]
          rw [← commutatorElement_def]
          exact commutatorElement_eq_one_iff_commute.mpr hz
  | adjacent_sq i =>
      have hrel := schurAdjacent_sq n (tailIndex n m h5 hmn i)
      calc
        FreeGroup.lift (tailGen n m h5 hmn)
            (tWord (m - 5) i ^ 2 * (zWord (m - 5))⁻¹) = 1 := by
          simp [zWord, tWord, tailGen, FreeGroup.lift_apply_of]
          rw [hrel, mul_inv_cancel]
  | braid i =>
      let i' : Fin (n + 3) := ⟨i.val, by omega⟩
      have hrel := schurAdjacent_mul_pow_three n i'
      calc
        FreeGroup.lift (tailGen n m h5 hmn)
            ((tWord (m - 5) i.castSucc * tWord (m - 5) i.succ) ^ 3 *
              (zWord (m - 5))⁻¹) = 1 := by
          simp [zWord, tWord, tailGen, FreeGroup.lift_apply_of]
          have h1 : tailIndex n m h5 hmn i.castSucc = i'.castSucc := by
            apply Fin.ext
            simp [tailIndex, i']
          have h2 : tailIndex n m h5 hmn i.succ = i'.succ := by
            apply Fin.ext
            simp [tailIndex, i']
          rw [h1, h2]
          rw [hrel, mul_inv_cancel]
  | far i j hfar =>
      have hfar' : (tailIndex n m h5 hmn i).val + 1 < (tailIndex n m h5 hmn j).val ∨
          (tailIndex n m h5 hmn j).val + 1 < (tailIndex n m h5 hmn i).val := by
        rcases hfar with h | h
        · left
          simp [tailIndex]
          omega
        · right
          simp [tailIndex]
          omega
      have hrel := schurAdjacent_far_mul_sq n (i := tailIndex n m h5 hmn i)
        (j := tailIndex n m h5 hmn j) hfar'
      calc
        FreeGroup.lift (tailGen n m h5 hmn)
            ((tWord (m - 5) i * tWord (m - 5) j) ^ 2 * (zWord (m - 5))⁻¹) = 1 := by
          simp [zWord, tWord, tailGen, FreeGroup.lift_apply_of]
          rw [hrel, mul_inv_cancel]

/-- The covering homomorphism induced by the shift of generators. -/
@[expose] public def tailHom (n m : Nat) (h5 : 5 ≤ m) (hmn : m ≤ n + 5) :
    SchurPresentedGroup (m - 5) →* SchurPresentedGroup n :=
  PresentedGroup.toGroup (f := tailGen n m h5 hmn) (relator_lift_tailGen n m h5 hmn)

/-- The generator-level compatibility with the projections. -/
public theorem tailGen_proj (n m : Nat) (h5 : 5 ≤ m) (hmn : m ≤ n + 5)
    (g : Gen (m - 5)) :
    schurSymmetricProjection n (tailGen n m h5 hmn g) =
      tailPermHom n m hmn (generatorPerm (m - 5) g) := by
  rcases g with _ | j
  · simp [tailGen, generatorPerm, tailPermHom, schurSymmetricProjection_central]
  · rw [generatorPerm, tailPermHom_adjacentSwap n m h5 hmn j]
    simp [tailGen, tailIndex, schurSymmetricProjection_adjacent]

/-- The full compatibility of the tail covering hom with the projections. -/
public theorem tailHom_proj (n m : Nat) (h5 : 5 ≤ m) (hmn : m ≤ n + 5)
    (w : SchurPresentedGroup (m - 5)) :
    schurSymmetricProjection n (tailHom n m h5 hmn w) =
      tailPermHom n m hmn (schurSymmetricProjection (m - 5) w) := by
  have hcomp : (schurSymmetricProjection n).comp (tailHom n m h5 hmn) =
      (tailPermHom n m hmn).comp (schurSymmetricProjection (m - 5)) := by
    apply PresentedGroup.ext
    intro g
    have htail : tailHom n m h5 hmn (PresentedGroup.of g) = tailGen n m h5 hmn g :=
      PresentedGroup.toGroup.of
        (rels := (Relator (m - 5) : Set (FreeGroup (Gen (m - 5)))))
        (f := tailGen n m h5 hmn) (relator_lift_tailGen n m h5 hmn)
        (x := g)
    change schurSymmetricProjection n
        (tailHom n m h5 hmn (PresentedGroup.of g)) =
      tailPermHom n m hmn
        (schurSymmetricProjection (m - 5) (PresentedGroup.of g))
    rw [htail]
    have hgen : schurSymmetricProjection (m - 5) (PresentedGroup.of g) =
        generatorPerm (m - 5) g :=
      PresentedGroup.toGroup.of
        (rels := (Relator (m - 5) : Set (FreeGroup (Gen (m - 5)))))
        (f := generatorPerm (m - 5))
        (relator_lift_generatorPerm (m - 5)) (x := g)
    rw [hgen]
    exact tailGen_proj n m h5 hmn g
  have hw : (schurSymmetricProjection n).comp (tailHom n m h5 hmn) w =
      (tailPermHom n m hmn).comp (schurSymmetricProjection (m - 5)) w :=
    congrArg (fun f : SchurPresentedGroup (m - 5) →* Equiv.Perm (Fin (n + 5)) => f w) hcomp
  simpa [MonoidHom.comp_apply] using hw

/-- The induced map on the alternating double covers. -/
@[expose] public def tailCoveringMap (n m : Nat) (h5 : 5 ≤ m) (hmn : m ≤ n + 5) :
    SchurAlternatingGroup (m - 5) →* SchurAlternatingGroup n :=
  { toFun := fun w => ⟨tailHom n m h5 hmn w.1, by
      rw [Subgroup.mem_comap, Equiv.Perm.mem_alternatingGroup, tailHom_proj]
      rw [sign_tailPermHom]
      have hw := w.2
      rw [Subgroup.mem_comap, Equiv.Perm.mem_alternatingGroup] at hw
      exact hw⟩
    map_one' := by
      apply Subtype.ext
      simp [tailHom]
    map_mul' := by
      intro a b
      apply Subtype.ext
      simp [tailHom] }

-- The bound `h5` is retained for compatibility with this public construction's API.
set_option linter.unusedVariables false in
/-- The preimage of the root `A_m`-subgroup in the double cover. -/
@[expose] public def rootAmPreimage (n m : Nat) (h5 : 5 ≤ m) (hmn : m ≤ n + 5) :
    Subgroup (SchurAlternatingGroup n) :=
  (rootAm n m hmn).comap (schurAlternatingProjection n)

/-- The projection of the tail covering map factors through the tail embedding. -/
public theorem tailCoveringMap_proj (n m : Nat) (h5 : 5 ≤ m) (hmn : m ≤ n + 5)
    (w : SchurAlternatingGroup (m - 5)) :
    schurAlternatingProjection n (tailCoveringMap n m h5 hmn w) =
      tailAltHom n m hmn (schurAlternatingProjection (m - 5) w) := by
  apply Subtype.ext
  change schurSymmetricProjection n (tailHom n m h5 hmn w.1) =
    tailPermHom n m hmn (schurSymmetricProjection (m - 5) w.1)
  exact tailHom_proj n m h5 hmn w.1

/-- The map from `2A_m` to the preimage of the root `A_m`-subgroup. -/
@[expose] public def tailPreimageMap (n m : Nat) (h5 : 5 ≤ m) (hmn : m ≤ n + 5) :
    SchurAlternatingGroup (m - 5) →* ↥(rootAmPreimage n m h5 hmn) :=
  { toFun := fun w => ⟨tailCoveringMap n m h5 hmn w, by
      rw [rootAmPreimage, Subgroup.mem_comap]
      have hπ : (schurAlternatingProjection n (tailCoveringMap n m h5 hmn w) :
          Equiv.Perm (Fin (n + 5))) = tailPermHom n m hmn (schurSymmetricProjection (m - 5) w.1) := by
        change schurSymmetricProjection n (tailHom n m h5 hmn w.1) =
          tailPermHom n m hmn (schurSymmetricProjection (m - 5) w.1)
        exact tailHom_proj n m h5 hmn w.1
      apply MonoidHom.mem_range.mpr
      refine ⟨schurAlternatingProjection (m - 5) w, ?_⟩
      apply Subtype.ext
      exact hπ.symm⟩
    map_one' := by
      apply Subtype.ext
      apply Subtype.ext
      change tailHom n m h5 hmn 1 = 1
      simp [tailHom]
    map_mul' := by
      intro a b
      apply Subtype.ext
      apply Subtype.ext
      change tailHom n m h5 hmn (a.1 * b.1) =
        tailHom n m h5 hmn a.1 * tailHom n m h5 hmn b.1
      exact (tailHom n m h5 hmn).map_mul a.1 b.1 }

/-- The tail embedding of alternating groups is injective. -/
public theorem tailAltHom_injective (n m : Nat) (hmn : m ≤ n + 5) :
    Function.Injective (tailAltHom n m hmn) := by
  intro a b hab
  apply Subtype.ext
  have ht : (tailAltHom n m hmn a : Equiv.Perm (Fin (n + 5))) =
      (tailAltHom n m hmn b : Equiv.Perm (Fin (n + 5))) := congrArg Subtype.val hab
  change tailPermHom n m hmn a.1 = tailPermHom n m hmn b.1 at ht
  exact (Equiv.Perm.viaEmbeddingHom_injective (tailEmbedding n m hmn)) ht

/-- The preimage of the root `A_m` has cardinality `m!`. -/
public theorem card_rootAmPreimage (n m : Nat) (h5 : 5 ≤ m) (hmn : m ≤ n + 5) :
    Nat.card (↥(rootAmPreimage n m h5 hmn)) = m.factorial := by
  change Nat.card (↥((rootAm n m hmn).comap (schurAlternatingProjection n))) = m.factorial
  rw [card_comap_mul (schurAlternatingProjection n) (schurAlternatingProjection_surjective n)
      (rootAm n m hmn)]
  have hker : Nat.card (schurAlternatingProjection n).ker = 2 :=
    natCard_ker_schurAlternatingCovering n
  have hroot : Nat.card (↥(rootAm n m hmn)) = m.factorial / 2 := by
    rw [rootAm]
    have hbi : Function.Bijective (tailAltHom n m hmn).rangeRestrict := by
      refine ⟨?_, (tailAltHom n m hmn).rangeRestrict_surjective⟩
      intro a b hab
      have hv : tailAltHom n m hmn a = tailAltHom n m hmn b := by
        have hc := congrArg (fun x : ↥(tailAltHom n m hmn).range =>
          (x : alternatingGroup (Fin (n + 5)))) hab
        apply Subtype.ext
        have hc' : tailAltHom n m hmn a = tailAltHom n m hmn b := by
          simpa only [MonoidHom.coe_rangeRestrict] using hc
        exact congrArg Subtype.val hc'
      exact tailAltHom_injective n m hmn hv
    have hcongr : Nat.card (↥(tailAltHom n m hmn).range) =
        Nat.card (alternatingGroup (Fin ((m - 5) + 5))) :=
      Nat.card_congr (Equiv.ofBijective (tailAltHom n m hmn).rangeRestrict hbi).symm
    have : Nontrivial (Fin ((m - 5) + 5)) :=
      ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by intro h; have := congrArg Fin.val h; norm_num at this⟩
    rw [hcongr, Nat.card_eq_fintype_card, card_alternatingGroup (α := Fin ((m - 5) + 5)),
      Fintype.card_fin]
    have h : (m - 5 + 5).factorial / 2 = m.factorial / 2 := by
      rw [show m - 5 + 5 = m by omega]
    simpa using h
  rw [hker, hroot]
  have hdiv : 2 ∣ m.factorial := by
    have h := Nat.factorial_dvd_factorial (by omega : 2 ≤ m)
    simpa using h
  exact Nat.div_mul_cancel hdiv

/-- Proposition 5.2.4(b): the preimage of the root `A_m`-subgroup is
isomorphic to the double cover `2A_m`. -/
public theorem proposition_5_2_4_b (n m : Nat) (h5 : 5 ≤ m) (hmn : m ≤ n + 5) :
    Nonempty (↥(rootAmPreimage n m h5 hmn) ≃* SchurAlternatingGroup (m - 5)) := by
  let L := rootAmPreimage n m h5 hmn
  let φ := tailPreimageMap n m h5 hmn
  have hinj : Function.Injective φ := by
    intro a b hab
    have hφ1 : φ (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    have hπ : schurAlternatingProjection (m - 5) (a * b⁻¹) = 1 := by
      have hAlt : tailAltHom n m hmn (schurAlternatingProjection (m - 5) (a * b⁻¹)) = 1 := by
        have hval : (φ (a * b⁻¹) : SchurAlternatingGroup n) = 1 :=
          congrArg Subtype.val hφ1
        have hP : schurAlternatingProjection n (φ (a * b⁻¹) : SchurAlternatingGroup n) = 1 :=
          congrArg (schurAlternatingProjection n) hval
        rw [← tailCoveringMap_proj n m h5 hmn (a * b⁻¹)]
        exact hP
      exact (tailAltHom_injective n m hmn (by simpa using hAlt :
        tailAltHom n m hmn (schurAlternatingProjection (m - 5) (a * b⁻¹)) =
          tailAltHom n m hmn 1))
    have hker : a * b⁻¹ ∈ (schurAlternatingProjection (m - 5)).ker := by
      rw [MonoidHom.mem_ker]
      exact hπ
    rcases InvolutionPreimage.ker_mem_cases (m - 5) hker with h1 | hz
    · exact mul_inv_eq_one.mp h1
    · -- a·b⁻¹ = z' — but φ(a·b⁻¹) = 1 and φ(z') ≠ 1
      have hφz : φ (a * b⁻¹) = φ (schurAlternatingCentral (m - 5)) := by
        rw [hz]
      have hne : φ (schurAlternatingCentral (m - 5)) ≠ 1 := by
        intro hh
        apply schurAlternatingCentral_ne_one n
        exact congrArg Subtype.val hh
      exact False.elim (hne (hφ1.symm.trans hφz).symm)
  have hcardL : Nat.card (↥L) = m.factorial := card_rootAmPreimage n m h5 hmn
  have hcardD : Nat.card (SchurAlternatingGroup (m - 5)) = m.factorial := by
    rw [card_schurAlternatingGroup]
    congr 1
    omega
  have hbij : Function.Bijective φ :=
    (Function.Injective.bijective_of_nat_card_le hinj (by rw [hcardL, hcardD]))
  exact ⟨(MulEquiv.ofBijective φ hbij).symm⟩

end RootAm

end GLS3.Chapter5.SchurPresentation

/- Source: proposition_5_2_4_d.lean -/

set_option maxHeartbeats 800000
set_option maxRecDepth 10000


namespace GLS3.Chapter5.SchurPresentation

/-! ## Proposition 5.2.4(d): root four-subgroups

The root four-subgroup of `K̄ = A_{n+5}` on the four points `{0,1,2,3}`:
`V = {1, ρ₁, ρ₂, ρ₃}` with `ρ₁ = (0 1)(2 3)`, `ρ₂ = (0 2)(1 3)`,
`ρ₃ = ρ₁ρ₂`.  Its full preimage in the double cover is generated by the
lifts `u₁, u₂` of `ρ₁, ρ₂`, which satisfy `u₁² = u₂² = (u₁u₂)² = z`, i.e.
they generate a quaternion group of order eight.
-/

namespace RootFourSubgroup

/-- The index `0` in `Fin (n+4)`. -/
@[expose] public def idx0 (n : Nat) : Fin (n + 4) := ⟨0, by omega⟩

/-- The index `1` in `Fin (n+4)`. -/
@[expose] public def idx1 (n : Nat) : Fin (n + 4) := ⟨1, by omega⟩

/-- The index `2` in `Fin (n+4)`. -/
@[expose] public def idx2 (n : Nat) : Fin (n + 4) := ⟨2, by omega⟩

/-- The first adjacent generator `t_0 = (0 1)`. -/
@[expose] public def a (n : Nat) : SchurPresentedGroup n :=
  PresentedGroup.of (.adjacent (idx0 n))

/-- The second adjacent generator `t_1 = (1 2)`. -/
@[expose] public def b (n : Nat) : SchurPresentedGroup n :=
  PresentedGroup.of (.adjacent (idx1 n))

/-- The third adjacent generator `t_2 = (2 3)`. -/
@[expose] public def c (n : Nat) : SchurPresentedGroup n :=
  PresentedGroup.of (.adjacent (idx2 n))

/-- The point `0` in `Fin (n+5)`. -/
@[expose] public def p0 (n : Nat) : Fin (n + 5) := ⟨0, by omega⟩

/-- The point `1` in `Fin (n+5)`. -/
@[expose] public def p1 (n : Nat) : Fin (n + 5) := ⟨1, by omega⟩

/-- The point `2` in `Fin (n+5)`. -/
@[expose] public def p2 (n : Nat) : Fin (n + 5) := ⟨2, by omega⟩

/-- The point `3` in `Fin (n+5)`. -/
@[expose] public def p3 (n : Nat) : Fin (n + 5) := ⟨3, by omega⟩

/-- `ρ₁ = (0 1)(2 3)` on `Fin (n+5)`. -/
@[expose] public def rho1 (n : Nat) : Equiv.Perm (Fin (n + 5)) :=
  Equiv.swap (p0 n) (p1 n) * Equiv.swap (p2 n) (p3 n)

/-- `ρ₂ = (0 2)(1 3)` on `Fin (n+5)`. -/
@[expose] public def rho2 (n : Nat) : Equiv.Perm (Fin (n + 5)) :=
  Equiv.swap (p0 n) (p2 n) * Equiv.swap (p1 n) (p3 n)

/-- `ρ₃ = ρ₁ρ₂ = (0 3)(1 2)` on `Fin (n+5)`. -/
@[expose] public def rho3 (n : Nat) : Equiv.Perm (Fin (n + 5)) :=
  Equiv.swap (p0 n) (p3 n) * Equiv.swap (p1 n) (p2 n)

/-- `τ = (0 1 2)` (the 3-cycle) on `Fin (n+5)`. -/
@[expose] public def tau (n : Nat) : Equiv.Perm (Fin (n + 5)) :=
  Equiv.swap (p0 n) (p1 n) * Equiv.swap (p1 n) (p2 n)

/-- `ρ₁ρ₂ = ρ₃`. -/
public theorem rho1_mul_rho2 (n : Nat) : rho1 n * rho2 n = rho3 n := by
  apply Equiv.Perm.ext
  intro x
  rcases x with ⟨x, hx⟩
  by_cases h4 : 4 ≤ x
  · -- x is outside {0,1,2,3}: all swaps fix x
    have hfix (a b : Fin (n + 5)) (ha : a.val < 4) (hb : b.val < 4) :
        Equiv.swap a b (⟨x, hx⟩ : Fin (n + 5)) = ⟨x, hx⟩ := by
      have h1 : (⟨x, hx⟩ : Fin (n + 5)) ≠ a := by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      have h2 : (⟨x, hx⟩ : Fin (n + 5)) ≠ b := by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      exact Equiv.swap_apply_of_ne_of_ne h1 h2
    have hf01 := hfix (p0 n) (p1 n) (by simp [p0]) (by simp [p1])
    have hf23 := hfix (p2 n) (p3 n) (by simp [p2]) (by simp [p3])
    have hf02 := hfix (p0 n) (p2 n) (by simp [p0]) (by simp [p2])
    have hf13 := hfix (p1 n) (p3 n) (by simp [p1]) (by simp [p3])
    have hf03 := hfix (p0 n) (p3 n) (by simp [p0]) (by simp [p3])
    have hf12 := hfix (p1 n) (p2 n) (by simp [p1]) (by simp [p2])
    have hf3 : (rho3 n) (⟨x, hx⟩ : Fin (n + 5)) = ⟨x, hx⟩ := by
      calc
        (rho3 n) (⟨x, hx⟩) = (Equiv.swap (p0 n) (p3 n)) ((Equiv.swap (p1 n) (p2 n)) (⟨x, hx⟩)) := by
          simp [rho3]
        _ = (Equiv.swap (p0 n) (p3 n)) (⟨x, hx⟩) := by rw [hf12]
        _ = ⟨x, hx⟩ := by rw [hf03]
    calc
      (rho1 n * rho2 n) (⟨x, hx⟩ : Fin (n + 5)) = (rho1 n) ((rho2 n) (⟨x, hx⟩)) := by
        rw [Equiv.Perm.mul_apply]
      _ = (rho1 n) ((Equiv.swap (p0 n) (p2 n)) ((Equiv.swap (p1 n) (p3 n)) (⟨x, hx⟩))) := by
        simp [rho2]
      _ = (rho1 n) ((Equiv.swap (p0 n) (p2 n)) (⟨x, hx⟩)) := by
        rw [hf13]
      _ = (rho1 n) (⟨x, hx⟩) := by
        rw [hf02]
      _ = (Equiv.swap (p0 n) (p1 n)) ((Equiv.swap (p2 n) (p3 n)) (⟨x, hx⟩)) := by
        simp [rho1]
      _ = (Equiv.swap (p0 n) (p1 n)) (⟨x, hx⟩) := by
        rw [hf23]
      _ = ⟨x, hx⟩ := by
        rw [hf01]
      _ = (rho3 n) (⟨x, hx⟩) := hf3.symm
  · interval_cases x
    · change (rho1 n * rho2 n) (p0 n) = (rho3 n) (p0 n)
      simp [rho1, rho2, rho3, p0, p1, p2, p3,
        Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne]
    · change (rho1 n * rho2 n) (p1 n) = (rho3 n) (p1 n)
      simp [rho1, rho2, rho3, p0, p1, p2, p3,
        Equiv.swap_apply_left, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne]
    · change (rho1 n * rho2 n) (p2 n) = (rho3 n) (p2 n)
      simp [rho1, rho2, rho3, p0, p1, p2, p3,
        Equiv.swap_apply_left, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne]
    · change (rho1 n * rho2 n) (p3 n) = (rho3 n) (p3 n)
      simp [rho1, rho2, rho3, p0, p1, p2, p3,
        Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne]

/-- `τ·ρ₁·τ⁻¹ = ρ₃`. -/
public theorem tau_conj_rho1 (n : Nat) : tau n * rho1 n * (tau n)⁻¹ = rho3 n := by
  apply Equiv.Perm.ext
  intro x
  rcases x with ⟨x, hx⟩
  by_cases h4 : 4 ≤ x
  · -- x outside {0,1,2,3}
    have hfix (a b : Fin (n + 5)) (ha : a.val < 4) (hb : b.val < 4) :
        Equiv.swap a b (⟨x, hx⟩ : Fin (n + 5)) = ⟨x, hx⟩ := by
      have h1 : (⟨x, hx⟩ : Fin (n + 5)) ≠ a := by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      have h2 : (⟨x, hx⟩ : Fin (n + 5)) ≠ b := by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      exact Equiv.swap_apply_of_ne_of_ne h1 h2
    have hf01 := hfix (p0 n) (p1 n) (by simp [p0]) (by simp [p1])
    have hf12 := hfix (p1 n) (p2 n) (by simp [p1]) (by simp [p2])
    have hf23 := hfix (p2 n) (p3 n) (by simp [p2]) (by simp [p3])
    have hτx : (tau n) (⟨x, hx⟩ : Fin (n + 5)) = ⟨x, hx⟩ := by
      calc
        (tau n) (⟨x, hx⟩) = (Equiv.swap (p0 n) (p1 n)) ((Equiv.swap (p1 n) (p2 n)) (⟨x, hx⟩)) := by
          simp [tau]
        _ = (Equiv.swap (p0 n) (p1 n)) (⟨x, hx⟩) := by rw [hf12]
        _ = ⟨x, hx⟩ := by rw [hf01]
    have hρx : (rho1 n) (⟨x, hx⟩ : Fin (n + 5)) = ⟨x, hx⟩ := by
      calc
        (rho1 n) (⟨x, hx⟩) = (Equiv.swap (p0 n) (p1 n)) ((Equiv.swap (p2 n) (p3 n)) (⟨x, hx⟩)) := by
          simp [rho1]
        _ = (Equiv.swap (p0 n) (p1 n)) (⟨x, hx⟩) := by rw [hf23]
        _ = ⟨x, hx⟩ := by rw [hf01]
    have hτx_inv : ((tau n)⁻¹) (⟨x, hx⟩ : Fin (n + 5)) = ⟨x, hx⟩ := by
      have hc := congrArg (fun y : Fin (n + 5) => (tau n)⁻¹ y) hτx.symm
      calc
        ((tau n)⁻¹) (⟨x, hx⟩ : Fin (n + 5))
            = ((tau n)⁻¹) ((tau n) (⟨x, hx⟩ : Fin (n + 5))) := hc
        _ = ⟨x, hx⟩ := by simp
    have hf03' := hfix (p0 n) (p3 n) (by simp [p0]) (by simp [p3])
    have hf12' := hfix (p1 n) (p2 n) (by simp [p1]) (by simp [p2])
    have hf3' : (rho3 n) (⟨x, hx⟩ : Fin (n + 5)) = ⟨x, hx⟩ := by
      calc
        (rho3 n) (⟨x, hx⟩) = (Equiv.swap (p0 n) (p3 n)) ((Equiv.swap (p1 n) (p2 n)) (⟨x, hx⟩)) := by
          simp [rho3]
        _ = (Equiv.swap (p0 n) (p3 n)) (⟨x, hx⟩) := by rw [hf12']
        _ = ⟨x, hx⟩ := by rw [hf03']
    -- (τ·ρ₁·τ⁻¹) x = τ (ρ₁ (τ⁻¹ x)) — τ⁻¹ fixes x, ρ₁ fixes x, τ fixes x
    calc
      (tau n * rho1 n * (tau n)⁻¹) (⟨x, hx⟩ : Fin (n + 5))
          = (tau n) ((rho1 n) (((tau n)⁻¹) (⟨x, hx⟩ : Fin (n + 5)))) := by simp [mul_assoc]
      _ = (tau n) ((rho1 n) (⟨x, hx⟩ : Fin (n + 5))) := by rw [hτx_inv]
      _ = (tau n) (⟨x, hx⟩ : Fin (n + 5)) := by rw [hρx]
      _ = ⟨x, hx⟩ := hτx
      _ = (rho3 n) (⟨x, hx⟩ : Fin (n + 5)) := hf3'.symm
  · interval_cases x
    · change (tau n * rho1 n * (tau n)⁻¹) (p0 n) = (rho3 n) (p0 n)
      simp [tau, rho1, rho3, p0, p1, p2, p3,
        Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne]
    · change (tau n * rho1 n * (tau n)⁻¹) (p1 n) = (rho3 n) (p1 n)
      simp [tau, rho1, rho3, p0, p1, p2, p3,
        Equiv.swap_apply_left, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne]
    · change (tau n * rho1 n * (tau n)⁻¹) (p2 n) = (rho3 n) (p2 n)
      simp [tau, rho1, rho3, p0, p1, p2, p3,
        Equiv.swap_apply_left, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne]
    · change (tau n * rho1 n * (tau n)⁻¹) (p3 n) = (rho3 n) (p3 n)
      simp [tau, rho1, rho3, p0, p1, p2, p3,
        Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne]
@[expose] public def u1 (n : Nat) : SchurAlternatingGroup n :=
  ⟨a n * c n, by
    rw [Subgroup.mem_comap, Equiv.Perm.mem_alternatingGroup]
    simp [a, c, map_mul, schurSymmetricProjection_adjacent, adjacentSwap,
      Equiv.Perm.sign_swap', ne_of_lt Fin.castSucc_lt_succ]⟩

/-- The lift of `ρ₂ = (0 2)(1 3)`. -/
@[expose] public def u2 (n : Nat) : SchurAlternatingGroup n :=
  ⟨b n * a n * b n * (c n * b n * c n), by
    rw [Subgroup.mem_comap, Equiv.Perm.mem_alternatingGroup]
    simp [a, b, c, map_mul, schurSymmetricProjection_adjacent, adjacentSwap,
      Equiv.Perm.sign_swap', ne_of_lt Fin.castSucc_lt_succ]⟩

/-- `u₁` is a preimage of the root involution `(0 1)(2 3)`. -/
public theorem u1_sq (n : Nat) : u1 n ^ 2 = schurAlternatingCentral n := by
  apply Subtype.ext
  change (a n * c n) ^ 2 = schurCentral n
  have hfar : (idx0 n).val + 1 < (idx2 n).val := by
    simp [idx0, idx2]
  simpa [a, c] using schurAdjacent_far_mul_sq n (i := idx0 n) (j := idx2 n) (Or.inl hfar)

/-- `u₂` is a preimage of the root involution `(0 2)(1 3)`: its square is the
central element. -/
public theorem u2_sq (n : Nat) : u2 n ^ 2 = schurAlternatingCentral n := by
  apply Subtype.ext
  change (b n * a n * b n * (c n * b n * c n)) ^ 2 = schurCentral n
  let a := a n
  let b := b n
  let c := c n
  let z := schurCentral n
  have hb0 : a * b * a = b * a * b := schurAdjacent_braid n 0
  have hb1 : b * c * b = c * b * c := schurAdjacent_braid n 1
  have hza : Commute z a := schurCentral_commutes_generator n (.adjacent 0)
  have hzb : Commute z b := schurCentral_commutes_generator n (.adjacent 1)
  have hzc : Commute z c := schurCentral_commutes_generator n (.adjacent 2)
  have hz2 : z * z = 1 := by simpa [z, pow_two] using schurCentral_sq n
  have hzall (x : SchurPresentedGroup n) : Commute z x :=
    (Subgroup.mem_center_iff.mp (schurCentral_mem_center n) x).symm
  have hfar_ac : a * c = z * c * a := by
    change adjacentLift n (idx0 n) * adjacentLift n (idx2 n) =
      schurCentral n * adjacentLift n (idx2 n) * adjacentLift n (idx0 n)
    have hfar : (idx0 n).val + 1 < (idx2 n).val := by
      simp [idx0, idx2]
    exact adjacentLift_far_anticommute n (i := idx0 n) (j := idx2 n) (Or.inl hfar)
  have hsand : c * a * c = a := by
    change adjacentLift n (idx2 n) * adjacentLift n (idx0 n) * adjacentLift n (idx2 n) =
      adjacentLift n (idx0 n)
    have hfar : (idx0 n).val + 1 < (idx2 n).val := by
      simp [idx0, idx2]
    exact schurAdjacent_far_sandwich n (i := idx2 n) (j := idx0 n) (Or.inr hfar)
  have hab2 : (a * b) ^ 2 = z * b * a := by
    have h3 : (a * b) ^ 3 = z := schurAdjacent_mul_pow_three n 0
    have hrel : (a * b) ^ 2 = z * (a * b)⁻¹ := by
      apply mul_right_cancel (b := a * b)
      calc
        ((a * b) ^ 2) * (a * b) = (a * b) ^ 3 := by rw [← pow_succ]
        _ = z := h3
        _ = (z * (a * b)⁻¹) * (a * b) := by simp [mul_assoc]
    have hinv : (a * b)⁻¹ = b * a := by
      have ha : (RootFourSubgroup.a n)⁻¹ = z * RootFourSubgroup.a n :=
        adjacentLift_inv n (idx0 n)
      have hb : (RootFourSubgroup.b n)⁻¹ = z * RootFourSubgroup.b n :=
        adjacentLift_inv n (idx1 n)
      calc
        (a * b)⁻¹ = (RootFourSubgroup.a n * RootFourSubgroup.b n)⁻¹ := rfl
        _ = (RootFourSubgroup.b n)⁻¹ * (RootFourSubgroup.a n)⁻¹ := by rw [mul_inv_rev]
        _ = (z * RootFourSubgroup.b n) * (z * RootFourSubgroup.a n) := by rw [hb, ha]
        _ = RootFourSubgroup.b n * RootFourSubgroup.a n := by
          have hzb' : Commute z (RootFourSubgroup.b n) :=
            schurCentral_commutes_generator n (.adjacent (idx1 n))
          have hza' : Commute z (RootFourSubgroup.a n) :=
            schurCentral_commutes_generator n (.adjacent (idx0 n))
          calc
            (z * RootFourSubgroup.b n) * (z * RootFourSubgroup.a n) =
                (RootFourSubgroup.b n * z) * (z * RootFourSubgroup.a n) := by rw [hzb'.eq.symm]
            _ = (RootFourSubgroup.b n) * (z * z) * (RootFourSubgroup.a n) := by simp [mul_assoc]
            _ = (RootFourSubgroup.b n) * (RootFourSubgroup.a n) := by rw [hz2]; simp
        _ = b * a := rfl
    rwa [hinv] at hrel
  -- u₂ = (b a b)(c b c) — braid → (a b a)(b c b) = (ab)²·c·b = z·b·a·c·b
  have hu2 : b * a * b * (c * b * c) = z * b * a * c * b := by
    rw [← hb0, ← hb1]
    calc
      (a * b * a) * (b * c * b) = (a * b) ^ 2 * (c * b) := by
        simp [pow_two, mul_assoc]
      _ = (z * b * a) * (c * b) := by rw [hab2]
      _ = z * b * a * c * b := by simp [mul_assoc]
  -- u₂² = (b·a·c·b)² = z
  calc
    (b * a * b * (c * b * c)) ^ 2 = (z * b * a * c * b) ^ 2 := by rw [hu2]
    _ = (b * a * c * b) ^ 2 := by
      -- (z·w)² = w² (z central, z² = 1)
      have hz' : Commute z (b * a * c * b) := by
        change Commute z (b * (a * (c * b)))
        exact hzb.mul_right (hza.mul_right (hzc.mul_right hzb))
      calc
        (z * b * a * c * b) ^ 2 = (z * (b * a * c * b)) ^ 2 := by simp [mul_assoc]
        _ = z ^ 2 * (b * a * c * b) ^ 2 := hz'.mul_pow 2
        _ = (b * a * c * b) ^ 2 := by rw [show z ^ 2 = 1 by simpa [pow_two] using hz2]; simp
    _ = z := by
      -- (b a c b)² = b a c b b a c b = b a c z a c b = z b a (c a c) b = z b a a b
      --   = z b z b = z² b b = z
      calc
        (b * a * c * b) ^ 2 = b * a * c * b * (b * a * c * b) := by rw [pow_two]
        _ = b * a * c * (b * b) * a * c * b := by simp [mul_assoc]
        _ = b * a * c * z * a * c * b := by
          have hbb : b * b = z := by
            change adjacentLift n (idx1 n) * adjacentLift n (idx1 n) = schurCentral n
            exact schurAdjacent_sq n (idx1 n)
          rw [hbb]
        _ = z * b * a * (c * a * c) * b := by
          calc
            b * a * c * z * a * c * b = z * (b * a * c * a * c * b) := by
              rw [← (hzall (b * a * c)).eq]
              simp [mul_assoc]
            _ = z * b * a * (c * a * c) * b := by
              simp [mul_assoc]
        _ = z * b * a * a * b := by rw [hsand]
        _ = z * b * z * b := by
          have haa : a * a = z := by
            change adjacentLift n (idx0 n) * adjacentLift n (idx0 n) = schurCentral n
            exact schurAdjacent_sq n (idx0 n)
          calc
            z * b * a * a * b = z * b * (a * a) * b := by
              simp [mul_assoc]
            _ = z * b * z * b := by rw [haa]
        _ = z := by
          have hbb2 : b * b = z := by
            change adjacentLift n (idx1 n) * adjacentLift n (idx1 n) = schurCentral n
            exact schurAdjacent_sq n (idx1 n)
          calc
            z * b * z * b = z * (b * z) * b := by simp [mul_assoc]
            _ = z * (z * b) * b := by rw [hzb.eq.symm]
            _ = (z * z) * (b * b) := by simp [mul_assoc]
            _ = b * b := by rw [hz2]; simp
            _ = z := hbb2

/-- `(idx0 n).castSucc` is the point `0`. -/
public theorem idx0_castSucc (n : Nat) : (idx0 n).castSucc = p0 n := by
  apply Fin.ext
  simp [idx0, p0]

/-- `(idx0 n).succ` is the point `1`. -/
public theorem idx0_succ (n : Nat) : (idx0 n).succ = p1 n := by
  apply Fin.ext
  simp [idx0, p1]

/-- `(idx1 n).castSucc` is the point `1`. -/
public theorem idx1_castSucc (n : Nat) : (idx1 n).castSucc = p1 n := by
  apply Fin.ext
  simp [idx1, p1]

/-- `(idx1 n).succ` is the point `2`. -/
public theorem idx1_succ (n : Nat) : (idx1 n).succ = p2 n := by
  apply Fin.ext
  simp [idx1, p2]

/-- `(idx2 n).castSucc` is the point `2`. -/
public theorem idx2_castSucc (n : Nat) : (idx2 n).castSucc = p2 n := by
  apply Fin.ext
  simp [idx2, p2]

/-- `(idx2 n).succ` is the point `3`. -/
public theorem idx2_succ (n : Nat) : (idx2 n).succ = p3 n := by
  apply Fin.ext
  simp [idx2, p3]

/-- `adjacentSwap n (idx0 n)` is the swap of points `0, 1`. -/
public theorem adjacentSwap_idx0 (n : Nat) : adjacentSwap n (idx0 n) = Equiv.swap (p0 n) (p1 n) := by
  rw [adjacentSwap, idx0_castSucc, idx0_succ]

/-- `adjacentSwap n (idx1 n)` is the swap of points `1, 2`. -/
public theorem adjacentSwap_idx1 (n : Nat) : adjacentSwap n (idx1 n) = Equiv.swap (p1 n) (p2 n) := by
  rw [adjacentSwap, idx1_castSucc, idx1_succ]

/-- `adjacentSwap n (idx2 n)` is the swap of points `2, 3`. -/
public theorem adjacentSwap_idx2 (n : Nat) : adjacentSwap n (idx2 n) = Equiv.swap (p2 n) (p3 n) := by
  rw [adjacentSwap, idx2_castSucc, idx2_succ]

/-- The projection of `u₁` is `ρ₁ = (0 1)(2 3)`. -/
public theorem u1_proj (n : Nat) :
    (schurAlternatingProjection n (u1 n) : Equiv.Perm (Fin (n + 5))) = rho1 n := by
  -- π(u₁) = adjacentSwap(0)·adjacentSwap(2) = swap(p0,p1)·swap(p2,p3) = rho1
  change schurSymmetricProjection n (a n * c n) = rho1 n
  simp [a, c, map_mul, schurSymmetricProjection_adjacent]
  rw [adjacentSwap_idx0, adjacentSwap_idx2]
  rfl

/-- The projection of `u₂` is `ρ₂ = (0 2)(1 3)`. -/
public theorem u2_proj (n : Nat) :
    (schurAlternatingProjection n (u2 n) : Equiv.Perm (Fin (n + 5))) = rho2 n := by
  change schurSymmetricProjection n (b n * a n * b n * (c n * b n * c n)) = rho2 n
  simp [a, b, c, map_mul, schurSymmetricProjection_adjacent]
  rw [adjacentSwap_idx1, adjacentSwap_idx0, adjacentSwap_idx2]
  -- (p1 p2)(p0 p1)(p1 p2) = (p0 p2) and (p2 p3)(p1 p2)(p2 p3) = (p1 p3)
  have hne01 : p0 n ≠ p1 n := by
    intro h
    have := congrArg Fin.val h
    simp [p0, p1] at this
  have hne02 : p0 n ≠ p2 n := by
    intro h
    have := congrArg Fin.val h
    simp [p0, p2] at this
  have hne12 : p1 n ≠ p2 n := by
    intro h
    have := congrArg Fin.val h
    simp [p1, p2] at this
  have hne13 : p1 n ≠ p3 n := by
    intro h
    have := congrArg Fin.val h
    simp [p1, p3] at this
  have hne23 : p2 n ≠ p3 n := by
    intro h
    have := congrArg Fin.val h
    simp [p2, p3] at this
  have hc1 : Equiv.swap (p1 n) (p2 n) * Equiv.swap (p0 n) (p1 n) *
      Equiv.swap (p1 n) (p2 n) = Equiv.swap (p2 n) (p0 n) := by
    exact Equiv.swap_mul_swap_mul_swap (x := p0 n) (y := p1 n) (z := p2 n) hne01 hne02
  have hc2 : Equiv.swap (p2 n) (p3 n) * Equiv.swap (p1 n) (p2 n) *
      Equiv.swap (p2 n) (p3 n) = Equiv.swap (p3 n) (p1 n) := by
    exact Equiv.swap_mul_swap_mul_swap (x := p1 n) (y := p2 n) (z := p3 n) hne12 hne13
  calc
    (Equiv.swap (p1 n) (p2 n) * Equiv.swap (p0 n) (p1 n) * Equiv.swap (p1 n) (p2 n)) *
        (Equiv.swap (p2 n) (p3 n) * Equiv.swap (p1 n) (p2 n) * Equiv.swap (p2 n) (p3 n)) =
        Equiv.swap (p2 n) (p0 n) * Equiv.swap (p3 n) (p1 n) := by rw [hc1, hc2]
    _ = rho2 n := by
      simp [rho2, Equiv.swap_comm]

/-- The lift `g = a·b` of the 3-cycle `(0 1 2)` in the double cover. -/
@[expose] public def g (n : Nat) : SchurAlternatingGroup n :=
  ⟨a n * b n, by
    rw [Subgroup.mem_comap, Equiv.Perm.mem_alternatingGroup]
    simp [a, b, map_mul, schurSymmetricProjection_adjacent, adjacentSwap,
      Equiv.Perm.sign_swap', ne_of_lt Fin.castSucc_lt_succ]⟩

/-- The projection of `g` is the 3-cycle `τ = (0 1 2)`. -/
public theorem g_proj (n : Nat) :
    (schurAlternatingProjection n (g n) : Equiv.Perm (Fin (n + 5))) = tau n := by
  change schurSymmetricProjection n (a n * b n) = tau n
  simp [a, b, map_mul, schurSymmetricProjection_adjacent]
  rw [adjacentSwap_idx0, adjacentSwap_idx1]
  rfl

/-- The projection of the conjugate `g·u₁·g⁻¹` is `ρ₃`. -/
public theorem g_conj_u1_proj (n : Nat) :
    (schurAlternatingProjection n (g n * u1 n * (g n)⁻¹) :
        Equiv.Perm (Fin (n + 5))) = rho3 n := by
  change schurSymmetricProjection n ((g n).1 * (u1 n).1 * (g n).1⁻¹) = rho3 n
  rw [map_mul, map_mul, map_inv]
  -- π(g·u₁·g⁻¹) = π(g)·π(u₁)·π(g)⁻¹ = τ·ρ₁·τ⁻¹ = ρ₃
  have hg : schurSymmetricProjection n (g n).1 = tau n := by
    change schurSymmetricProjection n (a n * b n) = tau n
    exact g_proj n
  have hu : schurSymmetricProjection n (u1 n).1 = rho1 n := by
    change schurSymmetricProjection n (a n * c n) = rho1 n
    exact u1_proj n
  rw [hg, hu]
  exact tau_conj_rho1 n

public theorem u1_mul_u2_sq (n : Nat) : (u1 n * u2 n) ^ 2 = schurAlternatingCentral n := by
  -- u₁u₂ and g·u₁·g⁻¹ are both lifts of ρ₃; they differ by a central element
  -- and (g·u₁·g⁻¹)² = z — so (u₁u₂)² = z
  have hπ12 : (schurAlternatingProjection n (u1 n * u2 n) : Equiv.Perm (Fin (n + 5))) = rho3 n := by
    change schurSymmetricProjection n ((u1 n).1 * (u2 n).1) = rho3 n
    rw [map_mul]
    have hu1 : schurSymmetricProjection n (u1 n).1 = rho1 n := by
      change schurSymmetricProjection n (a n * c n) = rho1 n
      exact u1_proj n
    have hu2 : schurSymmetricProjection n (u2 n).1 = rho2 n := by
      change schurSymmetricProjection n (b n * a n * b n * (c n * b n * c n)) = rho2 n
      exact u2_proj n
    rw [hu1, hu2]
    exact rho1_mul_rho2 n
  have hπconj : (schurAlternatingProjection n (g n * u1 n * (g n)⁻¹) :
        Equiv.Perm (Fin (n + 5))) = rho3 n := g_conj_u1_proj n
  -- both projections equal ρ₃ — the difference lies in the kernel
  have hπ12' : schurSymmetricProjection n ((u1 n).1 * (u2 n).1) = rho3 n := by
    change (schurAlternatingProjection n (u1 n * u2 n) : Equiv.Perm (Fin (n + 5))) = rho3 n
    exact hπ12
  have hπconj' : schurSymmetricProjection n ((g n).1 * (u1 n).1 * (g n).1⁻¹) = rho3 n := by
    change (schurAlternatingProjection n (g n * u1 n * (g n)⁻¹) :
      Equiv.Perm (Fin (n + 5))) = rho3 n
    exact hπconj
  have hker : (u1 n * u2 n) * (g n * u1 n * (g n)⁻¹)⁻¹ ∈
      (schurAlternatingProjection n).ker := by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    change schurSymmetricProjection n
      (((u1 n).1 * (u2 n).1) * ((g n).1 * (u1 n).1 * (g n).1⁻¹)⁻¹) = 1
    rw [map_mul, map_inv]
    -- π((u₁u₂)·(conj)⁻¹) = π(u₁u₂)·π(conj)⁻¹ = ρ₃ρ₃⁻¹ = 1
    rw [hπ12', hπconj']
    group
  -- the conjugate-square: (g·u₁·g⁻¹)² = g·u₁²·g⁻¹ = z
  have hconj_sq : (g n * u1 n * (g n)⁻¹) ^ 2 = schurAlternatingCentral n := by
    apply Subtype.ext
    change (g n).1 * (u1 n).1 * (g n).1⁻¹ * ((g n).1 * (u1 n).1 * (g n).1⁻¹) =
      schurCentral n
    -- (g·x·g⁻¹)² = g·x²·g⁻¹ — via group normalization
    have hg : (g n).1 * (u1 n).1 * (g n).1⁻¹ * ((g n).1 * (u1 n).1 * (g n).1⁻¹) =
        (g n).1 * (u1 n).1 ^ 2 * (g n).1⁻¹ := by
      rw [pow_two]
      group
    rw [hg]
    -- u₁² = z at the presented level
    have hu1sq : (u1 n).1 ^ 2 = schurCentral n := by
      change (u1 n : SchurPresentedGroup n) ^ 2 = (schurAlternatingCentral n : SchurPresentedGroup n)
      exact congrArg Subtype.val (u1_sq n)
    rw [hu1sq]
    -- g·z·g⁻¹ = z (z central)
    have hz : Commute (schurCentral n) (g n).1 := by
      exact (Subgroup.mem_center_iff.mp (schurCentral_mem_center n) (g n).1).symm
    calc
      (g n).1 * schurCentral n * (g n).1⁻¹ = schurCentral n * (g n).1 * (g n).1⁻¹ := by
        rw [hz.eq]
      _ = schurCentral n := by simp [mul_assoc]
  -- the kernel element is 1 or z
  rcases InvolutionPreimage.ker_mem_cases n hker with hx1 | hxz
  · -- difference = 1: u₁u₂ = g·u₁·g⁻¹
    have hu12 : u1 n * u2 n = g n * u1 n * (g n)⁻¹ := by
      calc
        u1 n * u2 n = ((u1 n * u2 n) * (g n * u1 n * (g n)⁻¹)⁻¹) * (g n * u1 n * (g n)⁻¹) := by
          group
        _ = g n * u1 n * (g n)⁻¹ := by rw [hx1]; simp
    calc
      (u1 n * u2 n) ^ 2 = (g n * u1 n * (g n)⁻¹) ^ 2 := by rw [hu12]
      _ = schurAlternatingCentral n := hconj_sq
  · -- difference = z: u₁u₂ = z·(g·u₁·g⁻¹)
    have hu12 : u1 n * u2 n = schurAlternatingCentral n * (g n * u1 n * (g n)⁻¹) := by
      calc
        u1 n * u2 n = ((u1 n * u2 n) * (g n * u1 n * (g n)⁻¹)⁻¹) * (g n * u1 n * (g n)⁻¹) := by
          group
        _ = schurAlternatingCentral n * (g n * u1 n * (g n)⁻¹) := by rw [hxz]
    calc
      (u1 n * u2 n) ^ 2 = (schurAlternatingCentral n * (g n * u1 n * (g n)⁻¹)) ^ 2 := by
        rw [hu12]
      _ = (schurAlternatingCentral n) ^ 2 * (g n * u1 n * (g n)⁻¹) ^ 2 := by
        -- z commutes with everything, so (z·X)² = z²·X²
        exact (Commute.mul_pow (by
          apply Subtype.ext
          exact ((Subgroup.mem_center_iff.mp (schurCentral_mem_center n)
            ((g n * u1 n * (g n)⁻¹) : SchurPresentedGroup n)).symm)) 2)
      _ = (g n * u1 n * (g n)⁻¹) ^ 2 := by
        rw [schurAlternatingCentral_sq]; try simp
      _ = schurAlternatingCentral n := hconj_sq

-- ---------------------------------------------------------------------------
-- The quaternion group iso (Proposition 5.2.4(d))
-- ---------------------------------------------------------------------------

/-- The map from the quaternion group `Q₈` to the double cover: `a 1 ↦ u₁`,
`xa 0 ↦ u₂`. -/
public def q8Phi (n : Nat) : QuaternionGroup 2 → SchurAlternatingGroup n
  | QuaternionGroup.a i => (u1 n) ^ i.val
  | QuaternionGroup.xa i => (u2 n) * (u1 n) ^ i.val

@[simp] public theorem q8_u1_pow_four (n : Nat) : (u1 n) ^ 4 = 1 := by
  rw [show 4 = 2 + 2 by omega, pow_add, u1_sq, ← pow_two, schurAlternatingCentral_sq]

@[simp] public theorem q8_u2_pow_four (n : Nat) : (u2 n) ^ 4 = 1 := by
  rw [show 4 = 2 + 2 by omega, pow_add, u2_sq, ← pow_two, schurAlternatingCentral_sq]

@[simp] public theorem q8_z_comm (n : Nat) (x : SchurAlternatingGroup n) :
    schurAlternatingCentral n * x = x * schurAlternatingCentral n := by
  apply Subtype.ext
  exact ((Subgroup.mem_center_iff.mp (schurCentral_mem_center n) x.1).symm)

@[simp] public theorem q8_z_sq (n : Nat) : schurAlternatingCentral n * schurAlternatingCentral n = 1 := by
  rw [← pow_two, schurAlternatingCentral_sq]

@[simp] public theorem q8_u1_sq_mul (n : Nat) : u1 n * u1 n = schurAlternatingCentral n := by
  rw [← pow_two, u1_sq]

@[simp] public theorem q8_u2_sq_mul (n : Nat) : u2 n * u2 n = schurAlternatingCentral n := by
  rw [← pow_two, u2_sq]

/-- `u₁⁻¹ = z·u₁`. -/
public theorem q8_u1_inv (n : Nat) : (u1 n)⁻¹ = schurAlternatingCentral n * u1 n := by
  symm
  apply eq_inv_of_mul_eq_one_right
  rw [← mul_assoc, ← q8_z_comm, mul_assoc, ← pow_two, u1_sq]
  simp

/-- `u₂⁻¹ = z·u₂`. -/
public theorem q8_u2_inv (n : Nat) : (u2 n)⁻¹ = schurAlternatingCentral n * u2 n := by
  symm
  apply eq_inv_of_mul_eq_one_right
  rw [← mul_assoc, ← q8_z_comm, mul_assoc, ← pow_two, u2_sq]
  simp

/-- `u₁·u₂·u₁ = u₂`. -/
public theorem q8_u1_mul_u2_mul_u1 (n : Nat) : u1 n * u2 n * u1 n = u2 n := by
  have hu12 : (u1 n * u2 n) ^ 2 = schurAlternatingCentral n := u1_mul_u2_sq n
  rw [pow_two] at hu12
  calc
    u1 n * u2 n * u1 n = (u1 n * u2 n * u1 n * u2 n) * (u2 n)⁻¹ := by group
    _ = schurAlternatingCentral n * (u2 n)⁻¹ := by
      rw [mul_assoc (u1 n * u2 n) (u1 n) (u2 n), hu12]
    _ = schurAlternatingCentral n * (schurAlternatingCentral n * u2 n) := by
      rw [q8_u2_inv]
    _ = u2 n := by simp [mul_assoc]

/-- `u₂·u₁·u₂ = u₁`. -/
public theorem q8_u2_mul_u1_mul_u2 (n : Nat) : u2 n * u1 n * u2 n = u1 n := by
  have hu12 : (u1 n * u2 n) ^ 2 = schurAlternatingCentral n := u1_mul_u2_sq n
  rw [pow_two] at hu12
  calc
    u2 n * u1 n * u2 n = (u1 n)⁻¹ * (u1 n * u2 n * u1 n * u2 n) := by group
    _ = (u1 n)⁻¹ * schurAlternatingCentral n := by
      rw [mul_assoc (u1 n * u2 n) (u1 n) (u2 n), hu12]
    _ = (schurAlternatingCentral n * u1 n) * schurAlternatingCentral n := by
      rw [q8_u1_inv]
    _ = u1 n := by simp [mul_assoc]

/-- `u₁·u₂ = z·(u₂·u₁)`. -/
public theorem q8_u1_mul_u2_mul (n : Nat) :
    u1 n * u2 n = schurAlternatingCentral n * (u2 n * u1 n) := by
  calc
    u1 n * u2 n = (u1 n * u2 n * u1 n) * (u1 n)⁻¹ := by group
    _ = u2 n * (u1 n)⁻¹ := by rw [q8_u1_mul_u2_mul_u1]
    _ = u2 n * (schurAlternatingCentral n * u1 n) := by rw [q8_u1_inv]
    _ = schurAlternatingCentral n * (u2 n * u1 n) := by simp [mul_assoc]

@[simp] public theorem q8_u1_pow_two (n : Nat) : (u1 n) ^ 2 = schurAlternatingCentral n := u1_sq n


@[simp] public theorem q8_u1_pow_three (n : Nat) : (u1 n) ^ 3 = schurAlternatingCentral n * u1 n := by
  rw [show 3 = 2 + 1 by omega, pow_add, u1_sq]
  simp

/-- `φ` respects the multiplication. -/
@[simp] theorem q8_u1_pow_zero (n : Nat) : (u1 n) ^ 0 = 1 := rfl

@[simp] theorem q8_u1_pow_one (n : Nat) : (u1 n) ^ 1 = u1 n := by rw [pow_one]

@[simp] theorem q8_u2_pow_zero (n : Nat) : (u2 n) ^ 0 = 1 := rfl

@[simp] theorem q8_u2_pow_one (n : Nat) : (u2 n) ^ 1 = u2 n := by rw [pow_one]

@[simp] theorem q8_u2_pow_two (n : Nat) : (u2 n) ^ 2 = schurAlternatingCentral n := u2_sq n

@[simp] theorem q8_u2_pow_three (n : Nat) : (u2 n) ^ 3 = schurAlternatingCentral n * u2 n := by
  rw [show 3 = 2 + 1 by omega, pow_add, u2_sq]
  simp


-- u1, u2 have order dividing 4
@[simp] theorem q8_u2_z_u2 (n : Nat) : u2 n * schurAlternatingCentral n * u2 n = 1 := by
  calc
    u2 n * schurAlternatingCentral n * u2 n = schurAlternatingCentral n * (u2 n * u2 n) := by
      rw [← q8_z_comm, mul_assoc]
    _ = 1 := by rw [q8_u2_sq_mul, q8_z_sq]

@[simp] theorem q8_u1_z_u1 (n : Nat) : u1 n * schurAlternatingCentral n * u1 n = 1 := by
  calc
    u1 n * schurAlternatingCentral n * u1 n = schurAlternatingCentral n * (u1 n * u1 n) := by
      rw [← q8_z_comm, mul_assoc]
    _ = 1 := by rw [q8_u1_sq_mul, q8_z_sq]

@[simp] theorem q8_u2_u1_z_u2 (n : Nat) : u2 n * u1 n * schurAlternatingCentral n * u2 n =
    u1 n * schurAlternatingCentral n := by
  calc
    u2 n * u1 n * schurAlternatingCentral n * u2 n = schurAlternatingCentral n * (u2 n * u1 n) * u2 n := by
      rw [← q8_z_comm]
    _ = schurAlternatingCentral n * (u2 n * u1 n * u2 n) := by rw [mul_assoc]
    _ = schurAlternatingCentral n * u1 n := by rw [q8_u2_mul_u1_mul_u2]
    _ = u1 n * schurAlternatingCentral n := by rw [q8_z_comm]

@[simp] theorem q8_u1_z_z (n : Nat) : u1 n * schurAlternatingCentral n * schurAlternatingCentral n = u1 n := by
  rw [mul_assoc, q8_z_sq]
  simp

@[simp] theorem q8_u2_u1_z_z (n : Nat) : u2 n * u1 n * schurAlternatingCentral n * schurAlternatingCentral n =
    u2 n * u1 n := by
  rw [mul_assoc, q8_z_sq]
  simp

@[simp] theorem q8_u2_u1_z_comm (n : Nat) : u2 n * u1 n * schurAlternatingCentral n =
    u2 n * schurAlternatingCentral n * u1 n := by
  calc
    u2 n * u1 n * schurAlternatingCentral n = u2 n * (u1 n * schurAlternatingCentral n) := by
      rw [← mul_assoc]
    _ = u2 n * (schurAlternatingCentral n * u1 n) := by rw [← q8_z_comm]
    _ = (u2 n * schurAlternatingCentral n) * u1 n := by rw [mul_assoc]

@[simp] theorem q8_u1_u1_z (n : Nat) : u1 n * (u1 n * schurAlternatingCentral n) = 1 := by
  rw [← mul_assoc, q8_u1_sq_mul, q8_z_sq]

@[simp] theorem q8_u1_z_u2 (n : Nat) : u1 n * schurAlternatingCentral n * u2 n = u2 n * u1 n := by
  calc
    u1 n * schurAlternatingCentral n * u2 n = schurAlternatingCentral n * u1 n * u2 n := by
      rw [← q8_z_comm]
    _ = schurAlternatingCentral n * (u1 n * u2 n) := by rw [mul_assoc]
    _ = schurAlternatingCentral n * (schurAlternatingCentral n * (u2 n * u1 n)) := by
      rw [q8_u1_mul_u2_mul]
    _ = u2 n * u1 n := by
      rw [← mul_assoc, ← mul_assoc, q8_z_sq]
      simp

@[simp] theorem q8_u1_z_u2_u1 (n : Nat) : u1 n * schurAlternatingCentral n * u2 n * u1 n =
    u2 n * schurAlternatingCentral n := by
  calc
    u1 n * schurAlternatingCentral n * u2 n * u1 n = schurAlternatingCentral n * u1 n * u2 n * u1 n := by
      rw [← q8_z_comm]
    _ = schurAlternatingCentral n * (u1 n * u2 n * u1 n) := by
      rw [mul_assoc (G := SchurAlternatingGroup n) (schurAlternatingCentral n * u1 n) (u2 n) (u1 n),
        mul_assoc (G := SchurAlternatingGroup n) (schurAlternatingCentral n) (u1 n) (u2 n * u1 n),
        mul_assoc (G := SchurAlternatingGroup n) (u1 n) (u2 n) (u1 n)]
    _ = schurAlternatingCentral n * u2 n := by rw [q8_u1_mul_u2_mul_u1]
    _ = u2 n * schurAlternatingCentral n := by rw [q8_z_comm]

@[simp] theorem q8_u2_u1_sq (n : Nat) : u2 n * u1 n * u1 n = u2 n * schurAlternatingCentral n := by
  rw [mul_assoc, q8_u1_sq_mul]

@[simp] theorem q8_u2_z_u1_sq (n : Nat) : u2 n * schurAlternatingCentral n * u1 n * u1 n = u2 n := by
  rw [mul_assoc, mul_assoc, q8_u1_sq_mul, q8_z_sq]
  simp

@[simp] theorem q8_z_u1_u2_assoc (n : Nat) :
    schurAlternatingCentral n * (u1 n * (u2 n * u1 n)) =
      schurAlternatingCentral n * (u1 n * u2 n * u1 n) := by
  exact (congrArg (fun x : SchurAlternatingGroup n => schurAlternatingCentral n * x)
    (mul_assoc (u1 n) (u2 n) (u1 n))).symm

@[simp] theorem q8_z_u1_assoc2 (n : Nat) :
    schurAlternatingCentral n * u1 n * (u2 n * u1 n) =
      schurAlternatingCentral n * (u1 n * u2 n * u1 n) := by
  group

@[simp] theorem q8_z_u2_assoc (n : Nat) :
    schurAlternatingCentral n * (u2 n * (u1 n * u2 n)) =
      schurAlternatingCentral n * (u2 n * u1 n * u2 n) := by
  exact (congrArg (fun x : SchurAlternatingGroup n => schurAlternatingCentral n * x)
    (mul_assoc (u2 n) (u1 n) (u2 n))).symm


@[simp] theorem q8_u2_z_u1_u2 (n : Nat) : u2 n * schurAlternatingCentral n * u1 n * u2 n =
    u1 n * schurAlternatingCentral n := by
  calc
    u2 n * schurAlternatingCentral n * u1 n * u2 n =
        schurAlternatingCentral n * u2 n * u1 n * u2 n := by
      rw [← q8_z_comm]
    _ = schurAlternatingCentral n * (u2 n * u1 n * u2 n) := by
      rw [mul_assoc (G := SchurAlternatingGroup n) (schurAlternatingCentral n * u2 n) (u1 n) (u2 n),
        mul_assoc (G := SchurAlternatingGroup n) (schurAlternatingCentral n) (u2 n) (u1 n * u2 n),
        mul_assoc (G := SchurAlternatingGroup n) (u2 n) (u1 n) (u2 n)]
    _ = schurAlternatingCentral n * u1 n := by rw [q8_u2_mul_u1_mul_u2]
    _ = u1 n * schurAlternatingCentral n := by rw [q8_z_comm]



private theorem q8_u1_pow_mul_u2 (n : Nat) (i : Fin 4) :
    (u1 n) ^ i.val * u2 n = u2 n * (u1 n) ^ ((4 - i.val) % 4) := by
  fin_cases i
  · simp
  · simp [q8_u1_mul_u2_mul, q8_u1_pow_three]
    rw [mul_assoc, q8_z_comm]
  · simp
  · simp [q8_u1_pow_three]

private theorem q8_u2_u1_pow_mul_u2 (n : Nat) (i : Fin 4) :
    (u2 n * (u1 n) ^ i.val) * u2 n =
      (u1 n) ^ ((6 - i.val) % 4) := by
  fin_cases i
  · simp [q8_u2_sq_mul]
  · simp [q8_u2_mul_u1_mul_u2]
  · norm_num
  · norm_num
    rw [← mul_assoc (u2 n) (u1 n) (schurAlternatingCentral n),
      mul_assoc (u2 n * u1 n) (schurAlternatingCentral n) (u2 n),
      q8_z_comm (n := n) (x := u2 n),
      ← mul_assoc (u2 n * u1 n) (u2 n) (schurAlternatingCentral n),
      q8_u2_mul_u1_mul_u2]

private theorem q8_u1_pow_mul_u2_zmod (n : Nat) (i : ZMod 4) :
    (u1 n) ^ i.val * u2 n = u2 n * (u1 n) ^ ((4 - i.val) % 4) := by
  exact q8_u1_pow_mul_u2 n ⟨i.val, ZMod.val_lt i⟩

private theorem q8_u2_u1_pow_mul_u2_zmod (n : Nat) (i : ZMod 4) :
    (u2 n * (u1 n) ^ i.val) * u2 n =
      (u1 n) ^ ((6 - i.val) % 4) := by
  exact q8_u2_u1_pow_mul_u2 n ⟨i.val, ZMod.val_lt i⟩

public theorem q8Phi_mul (n : Nat) (x y : QuaternionGroup 2) :
    q8Phi n (x * y) = q8Phi n x * q8Phi n y := by
  cases x with
  | a i =>
    cases y with
    | a j =>
      rw [QuaternionGroup.a_mul_a]
      change (u1 n) ^ (i + j).val = (u1 n) ^ i.val * (u1 n) ^ j.val
      rw [← pow_add, pow_eq_pow_mod (i.val + j.val) (q8_u1_pow_four n)]
      fin_cases i <;> fin_cases j <;> norm_num <;> congr 1
    | xa j =>
      rw [QuaternionGroup.a_mul_xa]
      change (u2 n) * (u1 n) ^ (j - i).val =
        (u1 n) ^ i.val * ((u2 n) * (u1 n) ^ j.val)
      rw [← mul_assoc, q8_u1_pow_mul_u2_zmod, mul_assoc, ← pow_add,
        pow_eq_pow_mod (((4 - i.val) % 4) + j.val) (q8_u1_pow_four n)]
      fin_cases i <;> fin_cases j <;> norm_num <;> congr 1
  | xa i =>
    cases y with
    | a j =>
      rw [QuaternionGroup.xa_mul_a]
      change (u2 n) * (u1 n) ^ (i + j).val =
        ((u2 n) * (u1 n) ^ i.val) * (u1 n) ^ j.val
      rw [mul_assoc, ← pow_add,
        pow_eq_pow_mod (i.val + j.val) (q8_u1_pow_four n)]
      fin_cases i <;> fin_cases j <;> norm_num <;> congr 1
    | xa j =>
      rw [QuaternionGroup.xa_mul_xa]
      change (u1 n) ^ (2 + j - i).val =
        ((u2 n) * (u1 n) ^ i.val) * ((u2 n) * (u1 n) ^ j.val)
      rw [← mul_assoc (u2 n * (u1 n) ^ i.val) (u2 n) ((u1 n) ^ j.val),
        q8_u2_u1_pow_mul_u2_zmod, ← pow_add,
        pow_eq_pow_mod (((6 - i.val) % 4) + j.val) (q8_u1_pow_four n)]
      fin_cases i <;> fin_cases j <;> norm_num <;> congr 1
public theorem q8Phi_one (n : Nat) : q8Phi n 1 = 1 := by
  change (u1 n) ^ (0 : ZMod 4).val = 1
  rw [show (0 : ZMod 4).val = 0 by decide]
  rw [q8_u1_pow_zero]

/-- The quaternion group homomorphism into the double cover. -/
public def q8PhiHom (n : Nat) : QuaternionGroup 2 →* SchurAlternatingGroup n where
  toFun := q8Phi n
  map_one' := q8Phi_one n
  map_mul' := q8Phi_mul n

/-- `ρ₁` is an even permutation. -/
public theorem rho1_mem_alternating (n : Nat) : rho1 n ∈ alternatingGroup (Fin (n + 5)) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  rw [rho1]
  rw [map_mul, Equiv.Perm.sign_swap', Equiv.Perm.sign_swap']
  simp [p0, p1, p2, p3]

/-- `ρ₂` is an even permutation. -/
public theorem rho2_mem_alternating (n : Nat) : rho2 n ∈ alternatingGroup (Fin (n + 5)) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  rw [rho2]
  rw [map_mul, Equiv.Perm.sign_swap', Equiv.Perm.sign_swap']
  simp [p0, p1, p2, p3]

/-- The root four-subgroup of `A_{n+5}` on the points `{0,1,2,3}`. -/
public def rootFourSubgroup (n : Nat) : Subgroup (alternatingGroup (Fin (n + 5))) :=
  Subgroup.closure ({(⟨rho1 n, rho1_mem_alternating n⟩ : alternatingGroup (Fin (n + 5))),
    (⟨rho2 n, rho2_mem_alternating n⟩ : alternatingGroup (Fin (n + 5)))} :
      Set (alternatingGroup (Fin (n + 5))))

/-- The full preimage `L` of the root four-subgroup in the double cover. -/
public def rootFourPreimage (n : Nat) : Subgroup (SchurAlternatingGroup n) :=
  (rootFourSubgroup n).comap (schurAlternatingProjection n)

public theorem rootFourPreimage_eq_comap (n : Nat) :
    rootFourPreimage n =
      (rootFourSubgroup n).comap (schurAlternatingProjection n) := by
  rw [rootFourPreimage]

/-- `u₁` lies in the preimage. -/
public theorem u1_mem_rootFourPreimage (n : Nat) : u1 n ∈ rootFourPreimage n := by
  show (schurAlternatingProjection n (u1 n) : alternatingGroup (Fin (n + 5))) ∈ rootFourSubgroup n
  have hπ : (schurAlternatingProjection n (u1 n) : alternatingGroup (Fin (n + 5))) =
      (⟨rho1 n, rho1_mem_alternating n⟩ : alternatingGroup (Fin (n + 5))) := by
    apply Subtype.ext
    exact u1_proj n
  rw [hπ]
  -- ρ₁ ∈ ⟨ρ₁, ρ₂⟩
  exact Subgroup.subset_closure (by simp)

/-- `u₂` lies in the preimage. -/
public theorem u2_mem_rootFourPreimage (n : Nat) : u2 n ∈ rootFourPreimage n := by
  show (schurAlternatingProjection n (u2 n) : alternatingGroup (Fin (n + 5))) ∈ rootFourSubgroup n
  have hπ : (schurAlternatingProjection n (u2 n) : alternatingGroup (Fin (n + 5))) =
      (⟨rho2 n, rho2_mem_alternating n⟩ : alternatingGroup (Fin (n + 5))) := by
    apply Subtype.ext
    exact u2_proj n
  rw [hπ]
  exact Subgroup.subset_closure (by simp)



/-- `ρ₁² = 1`. -/
public theorem rho1_sq (n : Nat) : rho1 n * rho1 n = 1 := by
  apply Equiv.Perm.ext
  intro x
  rcases x with ⟨x, hx⟩
  by_cases h4 : 4 ≤ x
  · -- x outside {0,1,2,3}: all swaps fix x
    have hfix (a b : Fin (n + 5)) (ha : a.val < 4) (hb : b.val < 4) :
        Equiv.swap a b (⟨x, hx⟩ : Fin (n + 5)) = ⟨x, hx⟩ := by
      have h1 : (⟨x, hx⟩ : Fin (n + 5)) ≠ a := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      have h2 : (⟨x, hx⟩ : Fin (n + 5)) ≠ b := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      exact Equiv.swap_apply_of_ne_of_ne h1 h2
    have hf01 := hfix (p0 n) (p1 n) (by simp [p0]) (by simp [p1])
    have hf23 := hfix (p2 n) (p3 n) (by simp [p2]) (by simp [p3])
    simp [rho1, hf01, hf23]
  · -- x ∈ {0,1,2,3}: the concrete evaluation
    interval_cases x
    · change (rho1 n) ((rho1 n) (p0 n)) = p0 n
      simp [rho1, p0, p1, p2, p3, Equiv.swap_apply_left, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne]
    · change (rho1 n) ((rho1 n) (p1 n)) = p1 n
      simp [rho1, p0, p1, p2, p3, Equiv.swap_apply_left, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne]
    · change (rho1 n) ((rho1 n) (p2 n)) = p2 n
      simp [rho1, p0, p1, p2, p3, Equiv.swap_apply_left, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne]
    · change (rho1 n) ((rho1 n) (p3 n)) = p3 n
      simp [rho1, p0, p1, p2, p3, Equiv.swap_apply_left, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne]

/-- `ρ₂² = 1`. -/
public theorem rho2_sq (n : Nat) : rho2 n * rho2 n = 1 := by
  apply Equiv.Perm.ext
  intro x
  rcases x with ⟨x, hx⟩
  by_cases h4 : 4 ≤ x
  · have hfix (a b : Fin (n + 5)) (ha : a.val < 4) (hb : b.val < 4) :
        Equiv.swap a b (⟨x, hx⟩ : Fin (n + 5)) = ⟨x, hx⟩ := by
      have h1 : (⟨x, hx⟩ : Fin (n + 5)) ≠ a := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      have h2 : (⟨x, hx⟩ : Fin (n + 5)) ≠ b := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      exact Equiv.swap_apply_of_ne_of_ne h1 h2
    have hf02 := hfix (p0 n) (p2 n) (by simp [p0]) (by simp [p2])
    have hf13 := hfix (p1 n) (p3 n) (by simp [p1]) (by simp [p3])
    simp [rho2, hf02, hf13]
  · interval_cases x
    · change (rho2 n) ((rho2 n) (p0 n)) = p0 n
      simp [rho2, p0, p1, p2, p3, Equiv.swap_apply_left, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne]
    · change (rho2 n) ((rho2 n) (p1 n)) = p1 n
      simp [rho2, p0, p1, p2, p3, Equiv.swap_apply_left, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne]
    · change (rho2 n) ((rho2 n) (p2 n)) = p2 n
      simp [rho2, p0, p1, p2, p3, Equiv.swap_apply_left, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne]
    · change (rho2 n) ((rho2 n) (p3 n)) = p3 n
      simp [rho2, p0, p1, p2, p3, Equiv.swap_apply_left, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne]

/-- `ρ₂ρ₁ = ρ₃`. -/
public theorem rho2_mul_rho1 (n : Nat) : rho2 n * rho1 n = rho3 n := by
  apply Equiv.Perm.ext
  intro x
  rcases x with ⟨x, hx⟩
  by_cases h4 : 4 ≤ x
  · have hfix (a b : Fin (n + 5)) (ha : a.val < 4) (hb : b.val < 4) :
        Equiv.swap a b (⟨x, hx⟩ : Fin (n + 5)) = ⟨x, hx⟩ := by
      have h1 : (⟨x, hx⟩ : Fin (n + 5)) ≠ a := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      have h2 : (⟨x, hx⟩ : Fin (n + 5)) ≠ b := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      exact Equiv.swap_apply_of_ne_of_ne h1 h2
    have hf01 := hfix (p0 n) (p1 n) (by simp [p0]) (by simp [p1])
    have hf23 := hfix (p2 n) (p3 n) (by simp [p2]) (by simp [p3])
    have hf02 := hfix (p0 n) (p2 n) (by simp [p0]) (by simp [p2])
    have hf13 := hfix (p1 n) (p3 n) (by simp [p1]) (by simp [p3])
    have hf03 := hfix (p0 n) (p3 n) (by simp [p0]) (by simp [p3])
    have hf12 := hfix (p1 n) (p2 n) (by simp [p1]) (by simp [p2])
    simp [rho2, rho1, rho3, hf01, hf23, hf02, hf13, hf03, hf12]
  · interval_cases x
    · change (rho2 n * rho1 n) (p0 n) = (rho3 n) (p0 n)
      simp [rho2, rho1, rho3, p0, p1, p2, p3, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne]
    · change (rho2 n * rho1 n) (p1 n) = (rho3 n) (p1 n)
      simp [rho2, rho1, rho3, p0, p1, p2, p3, Equiv.swap_apply_left, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne]
    · change (rho2 n * rho1 n) (p2 n) = (rho3 n) (p2 n)
      simp [rho2, rho1, rho3, p0, p1, p2, p3, Equiv.swap_apply_left, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne]
    · change (rho2 n * rho1 n) (p3 n) = (rho3 n) (p3 n)
      simp [rho2, rho1, rho3, p0, p1, p2, p3, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne]

/-- `ρ₃² = 1`. -/
public theorem rho3_sq (n : Nat) : rho3 n * rho3 n = 1 := by
  calc
    rho3 n * rho3 n = (rho1 n * rho2 n) * (rho1 n * rho2 n) := by
      rw [← rho1_mul_rho2]
    _ = rho1 n * ((rho2 n * rho1 n) * rho2 n) := by group
    _ = rho1 n * ((rho1 n * rho2 n) * rho2 n) := by
      rw [rho2_mul_rho1, ← rho1_mul_rho2]
    _ = (rho1 n * rho1 n) * (rho2 n * rho2 n) := by group
    _ = 1 := by
      rw [rho1_sq, rho2_sq]
      simp


/-- `ρ₁ρ₃ = ρ₂`. -/
public theorem rho1_mul_rho3 (n : Nat) : rho1 n * rho3 n = rho2 n := by
  calc
    rho1 n * rho3 n = rho1 n * (rho1 n * rho2 n) := by rw [← rho1_mul_rho2]
    _ = (rho1 n * rho1 n) * rho2 n := by rw [mul_assoc]
    _ = rho2 n := by rw [rho1_sq]; simp

/-- `ρ₃ρ₁ = ρ₂`. -/
public theorem rho3_mul_rho1 (n : Nat) : rho3 n * rho1 n = rho2 n := by
  calc
    rho3 n * rho1 n = (rho2 n * rho1 n) * rho1 n := by rw [← rho2_mul_rho1]
    _ = rho2 n * (rho1 n * rho1 n) := by rw [mul_assoc]
    _ = rho2 n := by rw [rho1_sq]; simp

/-- `ρ₂ρ₃ = ρ₁`. -/
public theorem rho2_mul_rho3 (n : Nat) : rho2 n * rho3 n = rho1 n := by
  calc
    rho2 n * rho3 n = rho2 n * (rho2 n * rho1 n) := by rw [← rho2_mul_rho1]
    _ = (rho2 n * rho2 n) * rho1 n := by rw [mul_assoc]
    _ = rho1 n := by rw [rho2_sq]; simp

/-- `ρ₃ρ₂ = ρ₁`. -/
public theorem rho3_mul_rho2 (n : Nat) : rho3 n * rho2 n = rho1 n := by
  calc
    rho3 n * rho2 n = (rho1 n * rho2 n) * rho2 n := by rw [← rho1_mul_rho2]
    _ = rho1 n * (rho2 n * rho2 n) := by rw [mul_assoc]
    _ = rho1 n := by rw [rho2_sq]; simp

/-- The elements of the root four-subgroup: `⟨ρ₁, ρ₂⟩ = {1, ρ₁, ρ₂, ρ₃}`. -/
public theorem V_elements (n : Nat) {σ : alternatingGroup (Fin (n + 5))}
    (hσ : σ ∈ rootFourSubgroup n) :
    σ.1 = 1 ∨ σ.1 = rho1 n ∨ σ.1 = rho2 n ∨ σ.1 = rho3 n := by
  refine Subgroup.closure_induction (fun σ hσ => ?_) ?_ (fun σ τ _ _ Pσ Pτ => ?_) (fun σ _ Pσ => ?_) hσ
  · -- the generators ρ₁, ρ₂ satisfy P
    rcases hσ with h | h
    · right; left
      exact congrArg Subtype.val h
    · right; right; left
      exact congrArg Subtype.val h
  · -- p(1)
    left; rfl
  · -- closure under multiplication
    rcases Pσ with hσ0 | hσ1 | hσ2 | hσ3
    · -- σ = 1: σ·τ = τ
      rcases Pτ with hτ0 | hτ1 | hτ2 | hτ3
      · left; change (σ.1 * τ.1) = 1
        rw [hσ0, hτ0]; try simp
      · right; left; change (σ.1 * τ.1) = rho1 n
        rw [hσ0, hτ1]; try simp
      · right; right; left; change (σ.1 * τ.1) = rho2 n
        rw [hσ0, hτ2]; try simp
      · right; right; right; change (σ.1 * τ.1) = rho3 n
        rw [hσ0, hτ3]; try simp
    · -- σ = ρ₁
      rcases Pτ with hτ0 | hτ1 | hτ2 | hτ3
      · right; left; change (σ.1 * τ.1) = rho1 n
        rw [hσ1, hτ0]; try simp
      · left; change (σ.1 * τ.1) = 1
        rw [hσ1, hτ1, rho1_sq]; try simp
      · right; right; right; change (σ.1 * τ.1) = rho3 n
        rw [hσ1, hτ2, rho1_mul_rho2]; try simp
      · right; right; left; change (σ.1 * τ.1) = rho2 n
        rw [hσ1, hτ3, rho1_mul_rho3]; try simp
    · -- σ = ρ₂
      rcases Pτ with hτ0 | hτ1 | hτ2 | hτ3
      · right; right; left
        simp [hσ2, hτ0]; try simp
      · right; right; right; change (σ.1 * τ.1) = rho3 n
        rw [hσ2, hτ1, rho2_mul_rho1]; try simp
      · left; change (σ.1 * τ.1) = 1
        rw [hσ2, hτ2, rho2_sq]; try simp
      · right; left; change (σ.1 * τ.1) = rho1 n
        rw [hσ2, hτ3, rho2_mul_rho3]
    · -- σ = ρ₃
      rcases Pτ with hτ0 | hτ1 | hτ2 | hτ3
      · right; right; right
        simp [hσ3, hτ0]
      · right; right; left
        change (↑σ * ↑τ) = rho2 n
        rw [hσ3, hτ1, rho3_mul_rho1]
      · right; left; change (σ.1 * τ.1) = rho1 n
        rw [hσ3, hτ2, rho3_mul_rho2]; try simp
      · left; change (σ.1 * τ.1) = 1
        rw [hσ3, hτ3, rho3_sq]; try simp
  · -- closure under inverse
    rcases Pσ with hσ0 | hσ1 | hσ2 | hσ3
    · left; simp [hσ0]
    · right; left
      calc
        (↑σ)⁻¹ = (rho1 n)⁻¹ := by rw [hσ1]
        _ = rho1 n := by
          symm
          apply eq_inv_of_mul_eq_one_right
          rw [rho1_sq]
    · right; right; left
      calc
        (↑σ)⁻¹ = (rho2 n)⁻¹ := by rw [hσ2]
        _ = rho2 n := by
          symm
          apply eq_inv_of_mul_eq_one_right
          rw [rho2_sq]
    · right; right; right
      calc
        (↑σ)⁻¹ = (rho3 n)⁻¹ := by rw [hσ3]
        _ = rho3 n := by
          symm
          apply eq_inv_of_mul_eq_one_right
          rw [rho3_sq]

/-- The map `Q₈ → L` landing in the preimage. -/
public def q8PhiL (n : Nat) : QuaternionGroup 2 →* rootFourPreimage n :=
  (q8PhiHom n).codRestrict (rootFourPreimage n) (by
    intro x
    rcases x with (i | j)
    · -- φ(a i) = u₁^i — π = ρ₁^i ∈ ⟨ρ₁, ρ₂⟩
      have hu1 : u1 n ∈ rootFourPreimage n := u1_mem_rootFourPreimage n
      exact (rootFourPreimage n).pow_mem hu1 i.val
    · -- φ(xa j) = u₂·u₁^j — π = ρ₂·ρ₁^j ∈ ⟨ρ₁, ρ₂⟩
      have hu1 : u1 n ∈ rootFourPreimage n := u1_mem_rootFourPreimage n
      have hu2 : u2 n ∈ rootFourPreimage n := u2_mem_rootFourPreimage n
      exact (rootFourPreimage n).mul_mem hu2 ((rootFourPreimage n).pow_mem hu1 j.val))

/-- `u₁` and `u₂` are in the range of `φ`. -/
public theorem u1_mem_q8PhiL_range (n : Nat) :
    (⟨u1 n, u1_mem_rootFourPreimage n⟩ : rootFourPreimage n) ∈ (q8PhiL n).range := by
  refine ⟨QuaternionGroup.a 1, ?_⟩
  apply Subtype.ext
  simp [q8PhiL, q8PhiHom, q8Phi]
  -- (u1 n) ^ (1 : ZMod 4).val = u1 n
  rw [show (1 : ZMod 4).val = 1 by decide, q8_u1_pow_one]

public theorem u2_mem_q8PhiL_range (n : Nat) :
    (⟨u2 n, u2_mem_rootFourPreimage n⟩ : rootFourPreimage n) ∈ (q8PhiL n).range := by
  refine ⟨QuaternionGroup.xa 0, ?_⟩
  apply Subtype.ext
  simp [q8PhiL, q8PhiHom, q8Phi]

/-- Every element of the preimage is a product of powers of `u₁`, `u₂`:
the preimage of the Klein four group `⟨ρ₁, ρ₂⟩ = {1, ρ₁, ρ₂, ρ₃}`. -/
public theorem rootFourPreimage_eq_closure (n : Nat) :
    rootFourPreimage n = Subgroup.closure ({u1 n, u2 n} : Set (SchurAlternatingGroup n)) := by
  apply le_antisymm
  · -- L ⊆ ⟨u₁, u₂⟩
    intro x hx
    have hπ : (schurAlternatingProjection n x : alternatingGroup (Fin (n + 5))) ∈ rootFourSubgroup n := by
      exact (Subgroup.mem_comap).mp hx
    rcases V_elements n hπ with hπ1 | hπ2 | hπ3 | hπ4
    · -- π(x) = 1: x ∈ ker — x = 1 or z
      have hker : x ∈ (schurAlternatingProjection n).ker := by
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        change (schurAlternatingProjection n x : Equiv.Perm (Fin (n + 5))) = 1
        simpa using hπ1
      rcases InvolutionPreimage.ker_mem_cases n hker with hx1 | hxz
      · rw [Subgroup.mem_closure]
        intro H hH
        rw [hx1]
        exact H.one_mem
      · rw [Subgroup.mem_closure]
        intro H hH
        have hu1 : u1 n ∈ H := hH (by simp)
        rw [hxz, ← u1_sq]
        exact H.mul_mem hu1 hu1
    · -- π(x) = ρ₁: x = u₁ or z·u₁
      have hker : x * (u1 n)⁻¹ ∈ (schurAlternatingProjection n).ker := by
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        change (schurAlternatingProjection n (x * (u1 n)⁻¹) : Equiv.Perm (Fin (n + 5))) = 1
        rw [map_mul, map_inv]
        -- π(x)·π(u₁)⁻¹ = ρ₁·ρ₁ = 1
        change (schurAlternatingProjection n x : Equiv.Perm (Fin (n + 5))) *
          (schurAlternatingProjection n (u1 n) : Equiv.Perm (Fin (n + 5)))⁻¹ = 1
        rw [u1_proj, hπ2]
        simp
      rcases InvolutionPreimage.ker_mem_cases n hker with hk1 | hkz
      · -- x·u₁⁻¹ = 1 — x = u₁
        rw [Subgroup.mem_closure]
        intro H hH
        have hu1 : u1 n ∈ H := hH (by simp)
        have hk : x * (u1 n)⁻¹ = 1 := hk1
        have hx1' : x = u1 n := by
          calc
            x = (x * (u1 n)⁻¹) * u1 n := by group
            _ = u1 n := by rw [hk]; simp
        rw [hx1']
        exact hu1
      · -- x·u₁⁻¹ = z — x = z·u₁
        rw [Subgroup.mem_closure]
        intro H hH
        have hu1 : u1 n ∈ H := hH (by simp)
        have hz : schurAlternatingCentral n ∈ H := by
          rw [← u1_sq]
          exact H.mul_mem hu1 hu1
        -- x = z·u₁ — via x·u₁⁻¹ = z
        have hk : x * (u1 n)⁻¹ = schurAlternatingCentral n := hkz
        have hx1' : x = schurAlternatingCentral n * u1 n := by
          calc
            x = (x * (u1 n)⁻¹) * u1 n := by group
            _ = schurAlternatingCentral n * u1 n := by rw [hk]
        rw [hx1']
        exact H.mul_mem hz hu1
    · -- π(x) = ρ₂: x = u₂ or z·u₂
      have hker : x * (u2 n)⁻¹ ∈ (schurAlternatingProjection n).ker := by
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        change (schurAlternatingProjection n (x * (u2 n)⁻¹) : Equiv.Perm (Fin (n + 5))) = 1
        rw [map_mul, map_inv]
        change (schurAlternatingProjection n x : Equiv.Perm (Fin (n + 5))) *
          (schurAlternatingProjection n (u2 n) : Equiv.Perm (Fin (n + 5)))⁻¹ = 1
        rw [u2_proj, hπ3]
        simp
      rcases InvolutionPreimage.ker_mem_cases n hker with hk1 | hkz
      · -- x·u₂⁻¹ = 1 — x = u₂
        rw [Subgroup.mem_closure]
        intro H hH
        have hu2 : u2 n ∈ H := hH (by simp)
        have hk : x * (u2 n)⁻¹ = 1 := hk1
        have hx1' : x = u2 n := by
          calc
            x = (x * (u2 n)⁻¹) * u2 n := by group
            _ = u2 n := by rw [hk]; simp
        rw [hx1']
        exact hu2
      · -- x·u₂⁻¹ = z — x = z·u₂
        rw [Subgroup.mem_closure]
        intro H hH
        have hu1 : u1 n ∈ H := hH (by simp)
        have hu2 : u2 n ∈ H := hH (by simp)
        have hz : schurAlternatingCentral n ∈ H := by
          rw [← u1_sq]
          exact H.mul_mem hu1 hu1
        have hk : x * (u2 n)⁻¹ = schurAlternatingCentral n := hkz
        have hx1' : x = schurAlternatingCentral n * u2 n := by
          calc
            x = (x * (u2 n)⁻¹) * u2 n := by group
            _ = schurAlternatingCentral n * u2 n := by rw [hk]
        rw [hx1']
        exact H.mul_mem hz hu2
    · -- π(x) = ρ₃: x = u₁u₂ or z·u₁u₂
      have hker : x * (u1 n * u2 n)⁻¹ ∈ (schurAlternatingProjection n).ker := by
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        change (schurAlternatingProjection n (x * (u1 n * u2 n)⁻¹) : Equiv.Perm (Fin (n + 5))) = 1
        rw [map_mul, map_inv]
        change (schurAlternatingProjection n x : Equiv.Perm (Fin (n + 5))) *
          (schurAlternatingProjection n (u1 n * u2 n) : Equiv.Perm (Fin (n + 5)))⁻¹ = 1
        rw [map_mul]
        change (schurAlternatingProjection n x : Equiv.Perm (Fin (n + 5))) *
          ((schurAlternatingProjection n (u1 n) : Equiv.Perm (Fin (n + 5))) *
            (schurAlternatingProjection n (u2 n) : Equiv.Perm (Fin (n + 5))))⁻¹ = 1
        rw [u1_proj, u2_proj, hπ4]
        simp [rho1_mul_rho2]
      rcases InvolutionPreimage.ker_mem_cases n hker with hk1 | hkz
      · -- x·(u₁u₂)⁻¹ = 1 — x = u₁u₂
        rw [Subgroup.mem_closure]
        intro H hH
        have hu1 : u1 n ∈ H := hH (by simp)
        have hu2 : u2 n ∈ H := hH (by simp)
        have hk : x * (u1 n * u2 n)⁻¹ = 1 := hk1
        have hx1' : x = u1 n * u2 n := by
          calc
            x = (x * (u1 n * u2 n)⁻¹) * (u1 n * u2 n) := by group
            _ = u1 n * u2 n := by rw [hk]; simp
        rw [hx1']
        exact H.mul_mem hu1 hu2
      · -- x·(u₁u₂)⁻¹ = z — x = z·u₁u₂
        rw [Subgroup.mem_closure]
        intro H hH
        have hu1 : u1 n ∈ H := hH (by simp)
        have hu2 : u2 n ∈ H := hH (by simp)
        have hz : schurAlternatingCentral n ∈ H := by
          rw [← u1_sq]
          exact H.mul_mem hu1 hu1
        have hk : x * (u1 n * u2 n)⁻¹ = schurAlternatingCentral n := hkz
        have hx1' : x = schurAlternatingCentral n * (u1 n * u2 n) := by
          calc
            x = (x * (u1 n * u2 n)⁻¹) * (u1 n * u2 n) := by group
            _ = schurAlternatingCentral n * (u1 n * u2 n) := by rw [hk]
        rw [hx1']
        exact H.mul_mem hz (H.mul_mem hu1 hu2)
  · -- ⟨u₁, u₂⟩ ⊆ L
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact u1_mem_rootFourPreimage n
    · exact u2_mem_rootFourPreimage n


/-- `ρ₁ ≠ 1`. -/
public theorem rho1_ne_one (n : Nat) : rho1 n ≠ 1 := by
  intro h
  have h0 : (rho1 n) (p0 n) = (1 : Equiv.Perm (Fin (n + 5))) (p0 n) := by rw [h]
  have hval : (rho1 n) (p0 n) = p1 n := by
    simp [rho1, p0, p1, p2, p3, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne]
  rw [hval] at h0
  have : (p1 n).val = (p0 n).val := congrArg Fin.val (by simpa using h0)
  simp [p0, p1] at this

/-- `ρ₂ ≠ 1`. -/
public theorem rho2_ne_one (n : Nat) : rho2 n ≠ 1 := by
  intro h
  have h0 : (rho2 n) (p0 n) = (1 : Equiv.Perm (Fin (n + 5))) (p0 n) := by rw [h]
  have hval : (rho2 n) (p0 n) = p2 n := by
    simp [rho2, p0, p1, p2, p3, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne]
  rw [hval] at h0
  have : (p2 n).val = (p0 n).val := congrArg Fin.val (by simpa using h0)
  simp [p0, p2] at this

/-- `ρ₁ ≠ ρ₂`. -/
public theorem rho1_ne_rho2 (n : Nat) : rho1 n ≠ rho2 n := by
  intro h
  have h0 : (rho1 n) (p0 n) = (rho2 n) (p0 n) := by rw [h]
  have hv1 : (rho1 n) (p0 n) = p1 n := by
    simp [rho1, p0, p1, p2, p3, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne]
  have hv2 : (rho2 n) (p0 n) = p2 n := by
    simp [rho2, p0, p1, p2, p3, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne]
  rw [hv1, hv2] at h0
  have : (p1 n).val = (p2 n).val := congrArg Fin.val h0
  simp [p1, p2] at this


/-- `ρ₃` is an even permutation. -/
public theorem rho3_mem_alternating (n : Nat) : rho3 n ∈ alternatingGroup (Fin (n + 5)) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  rw [rho3]
  rw [map_mul, Equiv.Perm.sign_swap', Equiv.Perm.sign_swap']
  simp [p0, p1, p2, p3]

/-- `ρ₃` applied to `p₀` is `p₃`. -/
public theorem rho3_apply_p0 (n : Nat) : (rho3 n) (p0 n) = p3 n := by
  change (Equiv.swap (p0 n) (p3 n)) ((Equiv.swap (p1 n) (p2 n)) (p0 n)) = p3 n
  have hne1 : p0 n ≠ p1 n := by
    intro h; have := congrArg Fin.val h; simp [p0, p1] at this
  have hne2 : p0 n ≠ p2 n := by
    intro h; have := congrArg Fin.val h; simp [p0, p2] at this
  rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]
  -- swap(p0,p3)(p0) = p3
  rw [Equiv.swap_apply_left]

/-- `ρ₁` applied to `p₀` is `p₁`. -/
public theorem rho1_apply_p0 (n : Nat) : (rho1 n) (p0 n) = p1 n := by
  change (Equiv.swap (p0 n) (p1 n)) ((Equiv.swap (p2 n) (p3 n)) (p0 n)) = p1 n
  have hne1 : p0 n ≠ p2 n := by
    intro h; have := congrArg Fin.val h; simp [p0, p2] at this
  have hne2 : p0 n ≠ p3 n := by
    intro h; have := congrArg Fin.val h; simp [p0, p3] at this
  rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]
  rw [Equiv.swap_apply_left]

/-- `ρ₂` applied to `p₀` is `p₂`. -/
public theorem rho2_apply_p0 (n : Nat) : (rho2 n) (p0 n) = p2 n := by
  change (Equiv.swap (p0 n) (p2 n)) ((Equiv.swap (p1 n) (p3 n)) (p0 n)) = p2 n
  have hne1 : p0 n ≠ p1 n := by
    intro h; have := congrArg Fin.val h; simp [p0, p1] at this
  have hne2 : p0 n ≠ p3 n := by
    intro h; have := congrArg Fin.val h; simp [p0, p3] at this
  rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]
  rw [Equiv.swap_apply_left]

/-- The cardinality of the root four-subgroup is four. -/
public theorem rootFourSubgroup_card (n : Nat) : Nat.card (rootFourSubgroup n) = 4 := by
  have hset : (rootFourSubgroup n).carrier =
      ({(1 : alternatingGroup (Fin (n + 5))), ⟨rho1 n, rho1_mem_alternating n⟩,
        ⟨rho2 n, rho2_mem_alternating n⟩, ⟨rho3 n, rho3_mem_alternating n⟩} :
        Set (alternatingGroup (Fin (n + 5)))) := by
    apply Set.Subset.antisymm
    · intro σ hσ
      rcases V_elements n hσ with h | h | h | h
      · left; apply Subtype.ext; exact h
      · right; left; apply Subtype.ext; exact h
      · right; right; left; apply Subtype.ext; exact h
      · right; right; right; apply Subtype.ext; exact h
    · intro σ hσ
      rcases hσ with h | h | h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]
        exact Subgroup.subset_closure (by simp)
      · rw [h]
        exact Subgroup.subset_closure (by simp)
      · rw [h]
        have hsub : (⟨rho3 n, rho3_mem_alternating n⟩ : alternatingGroup (Fin (n + 5))) =
            ⟨rho1 n, rho1_mem_alternating n⟩ * ⟨rho2 n, rho2_mem_alternating n⟩ := by
          apply Subtype.ext
          change rho3 n = rho1 n * rho2 n
          rw [rho1_mul_rho2]
        rw [hsub]
        let K : Set (alternatingGroup (Fin (n + 5))) :=
          {(⟨rho1 n, rho1_mem_alternating n⟩ : alternatingGroup (Fin (n + 5))),
            (⟨rho2 n, rho2_mem_alternating n⟩ : alternatingGroup (Fin (n + 5)))}
        have h1 : (⟨rho1 n, rho1_mem_alternating n⟩ : alternatingGroup (Fin (n + 5))) ∈
            rootFourSubgroup n :=
          @Subgroup.subset_closure (alternatingGroup (Fin (n + 5))) _ K
            ⟨rho1 n, rho1_mem_alternating n⟩ (by simp [K])
        have h2 : (⟨rho2 n, rho2_mem_alternating n⟩ : alternatingGroup (Fin (n + 5))) ∈
            rootFourSubgroup n :=
          @Subgroup.subset_closure (alternatingGroup (Fin (n + 5))) _ K
            ⟨rho2 n, rho2_mem_alternating n⟩ (by simp [K])
        exact Subgroup.mul_mem (rootFourSubgroup n) h1 h2
  have h31 : (rho3 n ≠ (1 : Equiv.Perm (Fin (n + 5)))) := by
    intro h
    have h0 : (rho3 n) (p0 n) = (1 : Equiv.Perm (Fin (n + 5))) (p0 n) := by rw [h]
    rw [rho3_apply_p0] at h0
    have : (p3 n).val = (p0 n).val := congrArg Fin.val (by simpa using h0)
    simp [p0, p3] at this
  have h32 : rho3 n ≠ rho1 n := by
    intro h
    have h0 : (rho3 n) (p0 n) = (rho1 n) (p0 n) := by rw [h]
    rw [rho3_apply_p0, rho1_apply_p0] at h0
    have : (p3 n).val = (p1 n).val := congrArg Fin.val h0
    simp [p1, p3] at this
  have h33 : rho3 n ≠ rho2 n := by
    intro h
    have h0 : (rho3 n) (p0 n) = (rho2 n) (p0 n) := by rw [h]
    rw [rho3_apply_p0, rho2_apply_p0] at h0
    have : (p3 n).val = (p2 n).val := congrArg Fin.val h0
    simp [p2, p3] at this
  have hr13 : (⟨rho1 n, rho1_mem_alternating n⟩ : alternatingGroup (Fin (n + 5))) ≠
      (1 : alternatingGroup (Fin (n + 5))) := by
    intro h; exact rho1_ne_one n (congrArg Subtype.val h)
  have hr23 : (⟨rho2 n, rho2_mem_alternating n⟩ : alternatingGroup (Fin (n + 5))) ≠
      (1 : alternatingGroup (Fin (n + 5))) := by
    intro h; exact rho2_ne_one n (congrArg Subtype.val h)
  have hr33 : (⟨rho3 n, rho3_mem_alternating n⟩ : alternatingGroup (Fin (n + 5))) ≠
      (1 : alternatingGroup (Fin (n + 5))) := by
    intro h; exact h31 (congrArg Subtype.val h)
  have hr12 : (⟨rho1 n, rho1_mem_alternating n⟩ : alternatingGroup (Fin (n + 5))) ≠
      ⟨rho2 n, rho2_mem_alternating n⟩ := by
    intro h; exact rho1_ne_rho2 n (congrArg Subtype.val h)
  have hr21 : (⟨rho2 n, rho2_mem_alternating n⟩ : alternatingGroup (Fin (n + 5))) ≠
      ⟨rho1 n, rho1_mem_alternating n⟩ := fun h => hr12 h.symm
  have hr23b : (⟨rho2 n, rho2_mem_alternating n⟩ : alternatingGroup (Fin (n + 5))) ≠
      ⟨rho3 n, rho3_mem_alternating n⟩ := fun h => h33 (congrArg Subtype.val h.symm)
  have hr32 : (⟨rho3 n, rho3_mem_alternating n⟩ : alternatingGroup (Fin (n + 5))) ≠
      ⟨rho2 n, rho2_mem_alternating n⟩ := fun h => h33 (congrArg Subtype.val h)
  have hr31 : (⟨rho3 n, rho3_mem_alternating n⟩ : alternatingGroup (Fin (n + 5))) ≠
      ⟨rho1 n, rho1_mem_alternating n⟩ := fun h => h32 (congrArg Subtype.val h)
  -- the carrier, as a set, has cardinality 4 (four distinct elements)
  have hcard : (rootFourSubgroup n : Set (alternatingGroup (Fin (n + 5)))).ncard = 4 := by
    change (rootFourSubgroup n).carrier.ncard = 4
    rw [hset]
    rw [Set.ncard_eq_toFinset_card']
    have htoF : ({(1 : alternatingGroup (Fin (n + 5))), ⟨rho1 n, rho1_mem_alternating n⟩,
          ⟨rho2 n, rho2_mem_alternating n⟩, ⟨rho3 n, rho3_mem_alternating n⟩} :
          Set (alternatingGroup (Fin (n + 5)))).toFinset
        = ({1, ⟨rho1 n, rho1_mem_alternating n⟩, ⟨rho2 n, rho2_mem_alternating n⟩,
            ⟨rho3 n, rho3_mem_alternating n⟩} : Finset (alternatingGroup (Fin (n + 5)))) := by
      ext σ
      simp
    rw [htoF]
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_insert_of_notMem]
        · simp
        · -- ⟨rho2⟩ ∉ {⟨rho3⟩}
          simpa using hr23b
      · -- ⟨rho1⟩ ∉ insert ⟨rho2⟩ {⟨rho3⟩}
        simp [hr12, hr31.symm]
    · -- 1 ∉ insert ⟨rho1⟩ (insert ⟨rho2⟩ {⟨rho3⟩})
      simp [hr13.symm, hr23.symm, hr33.symm]
  -- Nat.card ↥(rootFourSubgroup n) = ncard of the carrier
  change Nat.card (rootFourSubgroup n : Set (alternatingGroup (Fin (n + 5)))) = 4
  rw [Nat.card_coe_set_eq]
  exact hcard

/-- The range of `φ : Q₈ → L` is all of `L`. -/
public theorem q8PhiL_range_eq_top (n : Nat) : (q8PhiL n).range = ⊤ := by
  -- every element of `L = ⟨u₁, u₂⟩` is a product of powers of `u₁`, `u₂`,
  -- both of which lie in the range of `φ`.
  have hmem_range : ∀ x : rootFourPreimage n, x ∈ (q8PhiL n).range := by
    intro x
    have hcl : x.1 ∈ Subgroup.closure ({u1 n, u2 n} : Set (SchurAlternatingGroup n)) := by
      rw [← rootFourPreimage_eq_closure n]
      exact x.2
    have hres :
        (⟨x.1, by simp⟩ : rootFourPreimage n) ∈
          (q8PhiL n).range :=
      Subgroup.closure_induction (k := ({u1 n, u2 n} : Set (SchurAlternatingGroup n)))
        (p := fun g hg => (⟨g, by simpa [← rootFourPreimage_eq_closure n] using hg⟩ : rootFourPreimage n) ∈
          (q8PhiL n).range)
        (by
          intro g hg
          rcases hg with hg | hg
          · subst g
            simpa using u1_mem_q8PhiL_range n
          · subst g
            simpa using u2_mem_q8PhiL_range n)
        (by
          -- 1 ∈ range
          refine ⟨1, ?_⟩
          apply Subtype.ext
          exact (q8PhiHom n).map_one)
        (by
          intro x y hx hy hx' hy'
          rcases hx' with ⟨a, ha⟩
          rcases hy' with ⟨b, hb⟩
          refine ⟨a * b, ?_⟩
          apply Subtype.ext
          rw [map_mul]
          rw [ha, hb]
          rfl)
        (by
          intro x hx hx'
          rcases hx' with ⟨a, ha⟩
          refine ⟨a⁻¹, ?_⟩
          apply Subtype.ext
          rw [map_inv]
          rw [ha]
          rfl)
        hcl
    convert hres using 1
  apply le_antisymm
  · intro x hx
    trivial
  · intro x hx
    exact hmem_range x

/-- The cardinality of the preimage is eight: `|L| = |V|·|ker| = 4·2`. -/
public theorem rootFourPreimage_card (n : Nat) : Nat.card (rootFourPreimage n) = 8 := by
  change Nat.card (↥((rootFourSubgroup n).comap (schurAlternatingProjection n))) = 8
  rw [card_comap_mul (schurAlternatingProjection n) (schurAlternatingProjection_surjective n)
      (rootFourSubgroup n)]
  rw [rootFourSubgroup_card n]
  rw [show Nat.card (schurAlternatingProjection n).ker = 2 by
    simpa [schurAlternatingCovering] using natCard_ker_schurAlternatingCovering n]

/-- Proposition 5.2.4(d): the preimage of the root four-subgroup is the
quaternion group of order eight. -/
public theorem proposition_5_2_4_d (n : Nat) :
    Nonempty (rootFourPreimage n ≃* QuaternionGroup 2) := by
  have : Fintype (rootFourPreimage n) := Fintype.ofFinite _
  -- `φ : Q₈ → L` is surjective (range = ⊤) and the two groups have the same
  -- cardinality (both eight), hence it is bijective.
  have hsurj : Function.Surjective (q8PhiL n) := by
    rw [← MonoidHom.range_eq_top]
    exact q8PhiL_range_eq_top n
  have hcard8 : Fintype.card (QuaternionGroup 2) = 8 := by
    rw [QuaternionGroup.card]
  have hcardL : Fintype.card (rootFourPreimage n) = 8 := by
    rw [← Nat.card_eq_fintype_card]
    exact rootFourPreimage_card n
  have hbij : Function.Bijective (q8PhiL n) := by
    let f : QuaternionGroup 2 → rootFourPreimage n := (q8PhiL n)
    exact (Fintype.bijective_iff_surjective_and_card f).2 ⟨hsurj, by rw [hcard8, hcardL]⟩
  exact ⟨(MulEquiv.ofBijective (q8PhiL n) hbij).symm⟩





end RootFourSubgroup

end GLS3.Chapter5.SchurPresentation

/- Source: proposition_5_2_4_f.lean -/

set_option maxHeartbeats 800000
set_option maxRecDepth 10000


namespace GLS3.Chapter5.SchurPresentation

/-! ## Proposition 5.2.4(f): disjoint-support commutators

In the full symmetric double cover `SchurPresentedGroup n` (projecting onto
`Σ_{n+5}`), lifts of far-apart transpositions anticommute:
`t_i * t_j = z * t_j * t_i`.  Consequently the commutator of two transposition
lifts with disjoint supports is the central element `z`, and lifts of disjoint
root involutions commute.  These are the core computations of the printed
5.2.4(f).
-/

/-- The commutator of two far-apart transposition lifts is the central
element. -/
public theorem adjacentLift_far_commutator (n : Nat) {i j : Fin (n + 4)}
    (hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    adjacentLift n i * adjacentLift n j * (adjacentLift n i)⁻¹ * (adjacentLift n j)⁻¹ =
      schurCentral n := by
  -- [a,b] = a·b·a⁻¹·b⁻¹ — from t_i·t_j = z·t_j·t_i and t² = z
  let a := adjacentLift n i
  let b := adjacentLift n j
  let z := schurCentral n
  have h : a * b = z * b * a := adjacentLift_far_anticommute n hfar
  have hz : Commute z a := schurCentral_commutes_generator n (.adjacent i)
  have hz2 : z * z = 1 := by simpa [z, pow_two] using schurCentral_sq n
  calc
    a * b * a⁻¹ * b⁻¹ = (z * b * a) * a⁻¹ * b⁻¹ := by rw [h]
    _ = z * b * (a * a⁻¹) * b⁻¹ := by simp [mul_assoc]
    _ = z * b * b⁻¹ := by simp
    _ = z := by
      have hbb : b * b⁻¹ = 1 := by simp
      calc
        z * b * b⁻¹ = z * (b * b⁻¹) := by simp [mul_assoc]
        _ = z * 1 := by rw [hbb]
        _ = z := by simp

/-- Lifts of disjoint root involutions commute (5.2.4(f)(1) for root
involutions). -/
public theorem rootBlockWord_disjoint_commute (n : Nat) {i j : Nat}
    (hi : 4 * i + 2 < n + 4) (hj : 4 * j + 2 < n + 4) (hij : i ≠ j) :
    rootBlockWord n i hi * rootBlockWord n j hj =
      rootBlockWord n j hj * rootBlockWord n i hi :=
  rootBlockWord_commute n hi hj hij

end GLS3.Chapter5.SchurPresentation

namespace GLS3.Chapter5.SchurPresentation

/-! ## Proposition 5.2.4(c) and (g): remaining statements -/

/-- The inclusion of the first four points into the ambient permutation
domain. -/
@[expose] public def standardRootA4Embedding (n : Nat) :
    Fin 4 ↪ Fin (n + 5) :=
  ⟨fun i => ⟨i.val, by omega⟩, by
    intro i j h
    apply Fin.ext
    exact congrArg (fun k : Fin (n + 5) => k.val) h⟩

/-- Extension by the identity of permutations of the first four points. -/
@[expose] public def standardRootA4PermHom (n : Nat) :
    Equiv.Perm (Fin 4) →* Equiv.Perm (Fin (n + 5)) :=
  Equiv.Perm.viaEmbeddingHom (standardRootA4Embedding n)

public theorem sign_standardRootA4PermHom (n : Nat)
    (σ : Equiv.Perm (Fin 4)) :
    Equiv.Perm.sign (standardRootA4PermHom n σ) = Equiv.Perm.sign σ := by
  unfold standardRootA4PermHom
  rw [Equiv.Perm.viaEmbeddingHom_apply]
  simp [Equiv.Perm.viaEmbedding]

/-- The standard root `A₄`, supported on the first four points. -/
@[expose] public def standardRootA4 (n : Nat) :
    Subgroup (alternatingGroup (Fin (n + 5))) :=
  (show alternatingGroup (Fin 4) →* alternatingGroup (Fin (n + 5)) from
    { toFun := fun σ => ⟨standardRootA4PermHom n σ.1, by
        rw [Equiv.Perm.mem_alternatingGroup, sign_standardRootA4PermHom]
        exact σ.2⟩
      map_one' := by
        apply Subtype.ext
        simp [standardRootA4PermHom]
      map_mul' := by
        intro a b
        apply Subtype.ext
        simp [standardRootA4PermHom] }).range

/-- The support of one canonical four-point block is contained in that
block. -/
public theorem blockPerm_support_bounds (n j : Nat)
    (h : 4 * j + 2 < n + 4) {x : Fin (n + 5)}
    (hx : x ∈ (blockPerm n j h).support) :
    4 * j ≤ x.val ∧ x.val < 4 * j + 4 := by
  have h01 : (⟨4 * j, by omega⟩ : Fin (n + 5)) ≠
      ⟨4 * j + 1, by omega⟩ := by
    intro hxy
    have := congrArg Fin.val hxy
    change 4 * j = 4 * j + 1 at this
    omega
  have h23 : (⟨4 * j + 2, by omega⟩ : Fin (n + 5)) ≠
      ⟨4 * j + 3, by omega⟩ := by
    intro hxy
    have := congrArg Fin.val hxy
    change 4 * j + 2 = 4 * j + 3 at this
    omega
  have hx' := Finset.mem_of_subset
    (Equiv.Perm.support_mul_le
      (Equiv.swap (⟨4 * j, by omega⟩ : Fin (n + 5)) ⟨4 * j + 1, by omega⟩)
      (Equiv.swap (⟨4 * j + 2, by omega⟩ : Fin (n + 5)) ⟨4 * j + 3, by omega⟩))
    (by simpa [blockPerm] using hx)
  rw [Equiv.Perm.support_swap h01, Equiv.Perm.support_swap h23] at hx'
  change x ∈
    ({(⟨4 * j, by omega⟩ : Fin (n + 5)), ⟨4 * j + 1, by omega⟩} ∪
      {(⟨4 * j + 2, by omega⟩ : Fin (n + 5)), ⟨4 * j + 3, by omega⟩} :
        Finset (Fin (n + 5))) at hx'
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx'
  rcases hx' with (h0 | h1) | (h2 | h3)
  all_goals subst x; simp only; omega

/-- Each canonical block moves exactly four points. -/
public theorem blockPerm_support_card (n j : Nat)
    (h : 4 * j + 2 < n + 4) :
    (blockPerm n j h).support.card = 4 := by
  have hnodup : List.Nodup
      [(⟨4 * j, by omega⟩ : Fin (n + 5)), ⟨4 * j + 1, by omega⟩,
       ⟨4 * j + 2, by omega⟩, ⟨4 * j + 3, by omega⟩] := by
    simp only [List.nodup_cons, List.nodup_nil, List.mem_cons, List.not_mem_nil,
      or_false, Fin.mk.injEq]
    push Not
    repeat' apply And.intro
    all_goals first | omega | trivial
  have hct : (blockPerm n j h).cycleType = {2, 2} := by
    rw [blockPerm]
    exact Equiv.Perm.cycleType_swap_mul_swap_of_nodup hnodup
  rw [← Equiv.Perm.sum_cycleType, hct]
  simp

/-- Every point moved by the first `m` canonical blocks has index below
`4m`. -/
public theorem canonicalPerm_support_val_lt (n m : Nat)
    (h4m : 4 * m ≤ n + 5) {x : Fin (n + 5)}
    (hx : x ∈ (canonicalPerm n m h4m).support) : x.val < 4 * m := by
  induction m with
  | zero =>
      simp [canonicalPerm] at hx
  | succ k ih =>
      have h4k : 4 * k ≤ n + 5 := by omega
      have hk : 4 * k + 2 < n + 4 := by omega
      have hx' := Finset.mem_of_subset
        (Equiv.Perm.support_mul_le
          (canonicalPerm n k h4k) (blockPerm n k hk))
        (by
          simpa only [canonicalPerm, canonicalPerm_irrel n k _ h4k,
            blockPerm_irrel n k _ hk] using hx)
      rcases Finset.mem_union.mp hx' with hxold | hxblock
      · have := ih h4k hxold
        omega
      · exact (blockPerm_support_bounds n k hk hxblock).2

/-- The next canonical block is disjoint from all preceding blocks. -/
public theorem canonicalPerm_disjoint_next (n k : Nat)
    (h4k : 4 * k ≤ n + 5) (hk : 4 * k + 2 < n + 4) :
    Equiv.Perm.Disjoint (canonicalPerm n k h4k) (blockPerm n k hk) := by
  rw [Equiv.Perm.disjoint_iff_disjoint_support, Finset.disjoint_left]
  intro x hxold hxblock
  have hlt := canonicalPerm_support_val_lt n k h4k hxold
  have hge := (blockPerm_support_bounds n k hk hxblock).1
  omega

/-- The canonical product of `m` root involutions moves exactly `4m`
points. -/
public theorem canonicalPerm_support_card (n m : Nat)
    (h4m : 4 * m ≤ n + 5) :
    (canonicalPerm n m h4m).support.card = 4 * m := by
  induction m with
  | zero => simp [canonicalPerm]
  | succ k ih =>
      have h4k : 4 * k ≤ n + 5 := by omega
      have hk : 4 * k + 2 < n + 4 := by omega
      have hd := canonicalPerm_disjoint_next n k h4k hk
      rw [show canonicalPerm n (k + 1) h4m =
          canonicalPerm n k h4k * blockPerm n k hk by
        simp only [canonicalPerm, canonicalPerm_irrel n k _ h4k,
          blockPerm_irrel n k _ hk]]
      rw [hd.card_support_mul, ih h4k, blockPerm_support_card n k hk]
      omega

/-- Two nontrivial involutions in an alternating group with equally large
supports are conjugate already inside the alternating group.  If a symmetric
conjugator is odd, multiply it by a transposition contained in the support of
the first involution. -/
public theorem alternating_involution_isConj_of_card_support_eq
    {N : Nat} {sigma tau : alternatingGroup (Fin N)}
    (hsigma2 : sigma.1 ^ 2 = 1) (htau2 : tau.1 ^ 2 = 1)
    (hsigma_ne : sigma ≠ 1)
    (hcard : sigma.1.support.card = tau.1.support.card) :
    IsConj sigma tau := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hct_sigma := Equiv.Perm.cycleType_of_pow_prime_eq_one hsigma2
  have hct_tau := Equiv.Perm.cycleType_of_pow_prime_eq_one htau2
  have hsum_sigma : sigma.1.support.card = 2 * sigma.1.cycleType.card := by
    rw [← Equiv.Perm.sum_cycleType, hct_sigma]
    simp [Nat.mul_comm]
  have hsum_tau : tau.1.support.card = 2 * tau.1.cycleType.card := by
    rw [← Equiv.Perm.sum_cycleType, hct_tau]
    simp [Nat.mul_comm]
  have hcycle_card : sigma.1.cycleType.card = tau.1.cycleType.card := by
    omega
  have hct : sigma.1.cycleType = tau.1.cycleType := by
    rw [hct_sigma, hct_tau, hcycle_card]
  obtain ⟨pi, hpi⟩ := isConj_iff.mp
    (Equiv.Perm.isConj_iff_cycleType_eq.mpr hct)
  rcases Int.units_eq_one_or (Equiv.Perm.sign pi) with hsign | hsign
  · rw [isConj_iff]
    refine ⟨⟨pi, Equiv.Perm.mem_alternatingGroup.mpr hsign⟩, Subtype.ext ?_⟩
    change pi * sigma.1 * pi⁻¹ = tau.1
    exact hpi
  · have hsupp : sigma.1.support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      apply hsigma_ne
      apply Subtype.ext
      exact Equiv.Perm.support_eq_empty_iff.mp hempty
    obtain ⟨a, ha⟩ := hsupp
    have hane : sigma.1 a ≠ a := Equiv.Perm.mem_support.mp ha
    let delta : Equiv.Perm (Fin N) := Equiv.swap a (sigma.1 a)
    have hdelta_comm : Commute delta sigma.1 := by
      have hinv : sigma.1⁻¹ = sigma.1 := by
        apply inv_eq_of_mul_eq_one_left
        simpa [pow_two] using hsigma2
      change Equiv.swap a (sigma.1 a) * sigma.1 =
        sigma.1 * Equiv.swap a (sigma.1 a)
      rw [Equiv.swap_mul_eq_mul_swap, hinv]
      have hsigma_sigma : sigma.1 (sigma.1 a) = a := by
        have := congrArg (fun p : Equiv.Perm (Fin N) ↦ p a) hsigma2
        simpa [pow_two] using this
      rw [hsigma_sigma, Equiv.swap_comm]
    rw [isConj_iff]
    refine ⟨⟨pi * delta, ?_⟩, Subtype.ext ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup, map_mul, hsign]
      have hsign_delta : Equiv.Perm.sign delta = -1 := by
        exact Equiv.Perm.sign_swap hane.symm
      rw [hsign_delta, Int.units_mul_self]
    · change (pi * delta) * sigma.1 * (pi * delta)⁻¹ = tau.1
      calc
        (pi * delta) * sigma.1 * (pi * delta)⁻¹ =
            pi * (delta * sigma.1 * delta⁻¹) * pi⁻¹ := by group
        _ = pi * sigma.1 * pi⁻¹ := by rw [hdelta_comm.eq]; simp
        _ = tau.1 := hpi

/-- If a finite permutation group acts semiregularly on the support of one
of its elements, its order divides the support cardinality. -/
public theorem semiregular_support_card_dvd
    {N : Nat} (Lbar : Subgroup (alternatingGroup (Fin N)))
    (hcomm : IsMulCommutative ↥Lbar)
    (x : ↥Lbar)
    (hsemiregular : ∀ y : ↥Lbar, y ≠ 1 →
      ∀ omega : Fin N,
        (∃ z : ↥Lbar, z.1.1 omega ≠ omega) → y.1.1 omega ≠ omega) :
    Nat.card ↥Lbar ∣ x.1.1.support.card := by
  let : IsMulCommutative ↥Lbar := hcomm
  let S : SubMulAction ↥Lbar (Fin N) :=
    { carrier := (x.1.1.support : Set (Fin N))
      smul_mem' := by
        intro y omega homega
        have hxy : Commute y.1.1 x.1.1 := by
          change y.1.1 * x.1.1 = x.1.1 * y.1.1
          exact congrArg (fun z : ↥Lbar ↦ z.1.1) (mul_comm' y x)
        change y.1.1 omega ∈ x.1.1.support
        exact (Equiv.Perm.mem_support_iff_of_commute hxy omega).2 homega }
  have hstab : ∀ omega : S, MulAction.stabilizer ↥Lbar omega = ⊥ := by
    intro omega
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    rw [MulAction.mem_stabilizer_iff] at hy
    by_contra hyone
    have hmove := hsemiregular y hyone omega.1 ⟨x,
      Equiv.Perm.mem_support.mp omega.2⟩
    exact hmove (congrArg Subtype.val hy)
  let e := MulAction.selfEquivOrbitsQuotientProd hstab
  have hcardS : Nat.card S = x.1.1.support.card := by
    change Nat.card (x.1.1.support : Set (Fin N)) = x.1.1.support.card
    rw [Nat.card_coe_set_eq]
    simp
  refine ⟨Nat.card (Quotient (MulAction.orbitRel ↥Lbar S)), ?_⟩
  rw [← hcardS, Nat.card_congr e, Nat.card_prod, Nat.mul_comm]

open RootFourSubgroup

private theorem __ch5_proposition_5_2_4_g_pow_three (n : Nat) :
    g n ^ 3 = schurAlternatingCentral n := by
  apply Subtype.ext
  change (a n * b n) ^ 3 = schurCentral n
  simpa [a, b, idx0, idx1] using schurAdjacent_mul_pow_three n 0

private theorem __ch5_proposition_5_2_4_g_inv_val (n : Nat) :
    (a n * b n)⁻¹ = b n * a n := by
  let z := schurCentral n
  have ha : (a n)⁻¹ = z * a n := adjacentLift_inv n (idx0 n)
  have hb : (b n)⁻¹ = z * b n := adjacentLift_inv n (idx1 n)
  have hzb : Commute z (b n) :=
    schurCentral_commutes_generator n (.adjacent (idx1 n))
  have hz2 : z * z = 1 := by
    simpa [z, pow_two] using schurCentral_sq n
  calc
    (a n * b n)⁻¹ = (b n)⁻¹ * (a n)⁻¹ := by rw [mul_inv_rev]
    _ = (z * b n) * (z * a n) := by rw [ha, hb]
    _ = (b n * z) * (z * a n) := by rw [hzb.eq.symm]
    _ = b n * (z * z) * a n := by simp [mul_assoc]
    _ = b n * a n := by rw [hz2]; simp

private theorem __ch5_proposition_5_2_4_g_conj_u2 (n : Nat) :
    g n * u2 n * (g n)⁻¹ = schurAlternatingCentral n * u1 n := by
  apply Subtype.ext
  change (a n * b n) * (b n * a n * b n * (c n * b n * c n)) *
      (a n * b n)⁻¹ = schurCentral n * (a n * c n)
  rw [__ch5_proposition_5_2_4_g_inv_val]
  let z := schurCentral n
  have ha2 : a n * a n = z := by
    simpa [a, z, pow_two] using schurAdjacent_sq n (idx0 n)
  have hb2 : b n * b n = z := by
    simpa [b, z, pow_two] using schurAdjacent_sq n (idx1 n)
  have hc2 : c n * c n = z := by
    simpa [c, z, pow_two] using schurAdjacent_sq n (idx2 n)
  have hbc : b n * c n * b n = c n * b n * c n :=
    schurAdjacent_braid n 1
  have hzca : c n * a n = z * a n * c n := by
    exact adjacentLift_far_anticommute n (i := idx2 n) (j := idx0 n)
      (Or.inr (by simp [idx0, idx2]))
  have hz2 : z * z = 1 := by
    simpa [z, pow_two] using schurCentral_sq n
  have hzall (x : SchurPresentedGroup n) : Commute z x :=
    (Subgroup.mem_center_iff.mp (schurCentral_mem_center n) x).symm
  calc
    (a n * b n) * (b n * a n * b n * (c n * b n * c n)) * (b n * a n) =
        a n * (b n * b n) * a n * b n * c n * b n * c n * b n * a n := by group
    _ = a n * z * a n * b n * c n * b n * c n * b n * a n := by rw [hb2]
    _ = z * (a n * a n) * b n * c n * b n * c n * b n * a n := by
      rw [← (hzall (a n)).eq]
      group
    _ = b n * c n * b n * c n * b n * a n := by rw [ha2, hz2]; simp
    _ = (c n * b n * c n) * c n * b n * a n := by rw [hbc]
    _ = c n * b n * (c n * c n) * b n * a n := by group
    _ = c n * b n * z * b n * a n := by rw [hc2]
    _ = c n * (b n * z) * b n * a n := by group
    _ = c n * (z * b n) * b n * a n := by rw [← (hzall (b n)).eq]
    _ = c n * z * (b n * b n) * a n := by group
    _ = c n * z * z * a n := by rw [hb2]
    _ = c n * (z * z) * a n := by group
    _ = c n * a n := by rw [hz2]; simp
    _ = z * a n * c n := hzca

private theorem __ch5_proposition_5_2_4_g_conj_u1 (n : Nat) :
    g n * u1 n * (g n)⁻¹ =
      schurAlternatingCentral n * (u1 n * u2 n) := by
  apply Subtype.ext
  change (a n * b n) * (a n * c n) * (a n * b n)⁻¹ =
    schurCentral n * ((a n * c n) *
      (b n * a n * b n * (c n * b n * c n)))
  rw [__ch5_proposition_5_2_4_g_inv_val]
  let z := schurCentral n
  have hab : a n * b n * a n = b n * a n * b n :=
    schurAdjacent_braid n 0
  have hbc : b n * c n * b n = c n * b n * c n :=
    schurAdjacent_braid n 1
  have haca : a n * c n * a n = c n := by
    exact schurAdjacent_far_sandwich n (i := idx0 n) (j := idx2 n)
      (Or.inl (by simp [idx0, idx2]))
  have hac : a n * c n = z * c n * a n := by
    exact adjacentLift_far_anticommute n (i := idx0 n) (j := idx2 n)
      (Or.inl (by simp [idx0, idx2]))
  have hca : c n * a n = z * a n * c n := by
    exact adjacentLift_far_anticommute n (i := idx2 n) (j := idx0 n)
      (Or.inr (by simp [idx0, idx2]))
  have hz2 : z * z = 1 := by
    simpa [z, pow_two] using schurCentral_sq n
  have hzall (x : SchurPresentedGroup n) : Commute z x :=
    (Subgroup.mem_center_iff.mp (schurCentral_mem_center n) x).symm
  have hu12word :
      (a n * c n) * (b n * a n * b n * (c n * b n * c n)) =
        c n * b n * a n * b n * c n * b n := by
    calc
      (a n * c n) * (b n * a n * b n * (c n * b n * c n)) =
          (a n * c n) * (a n * b n * a n * (c n * b n * c n)) := by rw [← hab]
      _ = (a n * c n) * (a n * b n * a n * (b n * c n * b n)) := by rw [← hbc]
      _ = (a n * c n * a n) * b n * a n * b n * c n * b n := by group
      _ = c n * b n * a n * b n * c n * b n := by rw [haca]
  calc
    (a n * b n) * (a n * c n) * (b n * a n) =
        b n * a n * b n * c n * b n * a n := by rw [show
          (a n * b n) * (a n * c n) * (b n * a n) =
            (a n * b n * a n) * c n * b n * a n by group, hab]
    _ = a n * b n * a n * c n * b n * a n := by rw [← hab]
    _ = a n * b n * (a n * c n) * b n * a n := by group
    _ = a n * b n * (z * c n * a n) * b n * a n := by rw [hac]
    _ = z * (a n * b n * c n * a n * b n * a n) := by
      calc
        a n * b n * (z * c n * a n) * b n * a n =
            a n * (b n * z) * c n * a n * b n * a n := by group
        _ = a n * (z * b n) * c n * a n * b n * a n := by rw [← (hzall (b n)).eq]
        _ = (a n * z) * b n * c n * a n * b n * a n := by group
        _ = (z * a n) * b n * c n * a n * b n * a n := by rw [← (hzall (a n)).eq]
        _ = z * (a n * b n * c n * a n * b n * a n) := by group
    _ = z * ((a n * b n * c n) * (a n * b n * a n)) := by group
    _ = z * ((a n * b n * c n) * (b n * a n * b n)) := by rw [hab]
    _ = z * (a n * b n * c n * b n * a n * b n) := by group
    _ = z * (a n * (b n * c n * b n) * a n * b n) := by group
    _ = z * (a n * (c n * b n * c n) * a n * b n) := by rw [hbc]
    _ = z * (a n * c n * b n * c n * a n * b n) := by group
    _ = c n * a n * b n * c n * a n * b n := by
      calc
        z * (a n * c n * b n * c n * a n * b n) =
            z * ((a n * c n) * b n * c n * a n * b n) := by group
        _ = z * ((z * c n * a n) * b n * c n * a n * b n) := by rw [hac]
        _ = (z * z) * (c n * a n * b n * c n * a n * b n) := by group
        _ = c n * a n * b n * c n * a n * b n := by rw [hz2]; simp
    _ = (c n * a n * b n) * (c n * a n) * b n := by group
    _ = (c n * a n * b n) * (z * a n * c n) * b n := by rw [hca]
    _ = z * (c n * a n * b n * a n * c n * b n) := by
      have hzpre : Commute z (c n * a n * b n) := hzall _
      calc
        (c n * a n * b n) * (z * a n * c n) * b n =
            ((c n * a n * b n) * z) * a n * c n * b n := by group
        _ = (z * (c n * a n * b n)) * a n * c n * b n := by rw [← hzpre.eq]
        _ = z * (c n * a n * b n * a n * c n * b n) := by group
    _ = z * (c n * (a n * b n * a n) * c n * b n) := by group
    _ = z * (c n * (b n * a n * b n) * c n * b n) := by rw [hab]
    _ = z * (c n * b n * a n * b n * c n * b n) := by group
    _ = z * ((a n * c n) * (b n * a n * b n * (c n * b n * c n))) := by
      rw [hu12word]

@[instance_reducible]
private def __ch5_proposition_5_2_4_binaryTetrahedralFintype :
    Fintype (QuaternionGroup 2 ⋊[q8C3Action] Multiplicative (ZMod 3)) :=
  Fintype.ofEquiv (QuaternionGroup 2 × Multiplicative (ZMod 3))
    SemidirectProduct.equivProd.symm


private def __ch5_proposition_5_2_4_smallRho1 : alternatingGroup (Fin 4) :=
  ⟨Equiv.swap (0 : Fin 4) 1 * Equiv.swap (2 : Fin 4) 3, by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul,
      Equiv.Perm.sign_swap', Equiv.Perm.sign_swap']
    decide⟩

private def __ch5_proposition_5_2_4_smallRho2 : alternatingGroup (Fin 4) :=
  ⟨Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3, by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul,
      Equiv.Perm.sign_swap', Equiv.Perm.sign_swap']
    decide⟩

private def __ch5_proposition_5_2_4_smallTau : alternatingGroup (Fin 4) :=
  ⟨Equiv.swap (0 : Fin 4) 1 * Equiv.swap (1 : Fin 4) 2, by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul,
      Equiv.Perm.sign_swap', Equiv.Perm.sign_swap']
    decide⟩

private theorem __ch5_proposition_5_2_4_standardRootA4PermHom_apply_lt_four (n : Nat)
    (σ : Equiv.Perm (Fin 4)) (x : Fin (n + 5)) (hx : x.val < 4) :
    standardRootA4PermHom n σ x =
      standardRootA4Embedding n (σ ⟨x.val, hx⟩) := by
  let y : Fin 4 := ⟨x.val, hx⟩
  have hxy : standardRootA4Embedding n y = x := by
    apply Fin.ext
    rfl
  calc
    standardRootA4PermHom n σ x =
        standardRootA4PermHom n σ (standardRootA4Embedding n y) := by rw [hxy]
    _ = standardRootA4Embedding n (σ y) :=
      Equiv.Perm.viaEmbedding_apply σ (standardRootA4Embedding n) y
    _ = standardRootA4Embedding n (σ ⟨x.val, hx⟩) := rfl

private theorem __ch5_proposition_5_2_4_standardRootA4PermHom_apply_of_four_le (n : Nat)
    (σ : Equiv.Perm (Fin 4)) (x : Fin (n + 5)) (hx : 4 ≤ x.val) :
    standardRootA4PermHom n σ x = x := by
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨y, hy⟩
  have := congrArg Fin.val hy
  simp [standardRootA4Embedding] at this
  omega

private theorem __ch5_proposition_5_2_4_swap_fix_of_four_le (n : Nat) (x i j : Fin (n + 5))
    (hx : 4 ≤ x.val) (hi : i.val < 4) (hj : j.val < 4) :
    Equiv.swap i j x = x := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    have := congrArg Fin.val h
    omega
  · intro h
    have := congrArg Fin.val h
    omega

private theorem __ch5_proposition_5_2_4_smallRho1_extend (n : Nat) :
    standardRootA4PermHom n __ch5_proposition_5_2_4_smallRho1.1 = rho1 n := by
  apply Equiv.Perm.ext
  intro x
  by_cases hx : x.val < 4
  · rw [__ch5_proposition_5_2_4_standardRootA4PermHom_apply_lt_four n __ch5_proposition_5_2_4_smallRho1.1 x hx]
    rcases x with ⟨x, hxn⟩
    interval_cases x <;>
      simp [__ch5_proposition_5_2_4_smallRho1, standardRootA4Embedding, rho1, p0, p1, p2, p3,
        Equiv.swap_apply_left, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne]
  · have hx4 : 4 ≤ x.val := by omega
    rw [__ch5_proposition_5_2_4_standardRootA4PermHom_apply_of_four_le n __ch5_proposition_5_2_4_smallRho1.1 x hx4]
    symm
    change Equiv.swap (p0 n) (p1 n) (Equiv.swap (p2 n) (p3 n) x) = x
    rw [__ch5_proposition_5_2_4_swap_fix_of_four_le n x (p2 n) (p3 n) hx4 (by simp [p2]) (by simp [p3])]
    rw [__ch5_proposition_5_2_4_swap_fix_of_four_le n x (p0 n) (p1 n) hx4 (by simp [p0]) (by simp [p1])]

private theorem __ch5_proposition_5_2_4_smallRho2_extend (n : Nat) :
    standardRootA4PermHom n __ch5_proposition_5_2_4_smallRho2.1 = rho2 n := by
  apply Equiv.Perm.ext
  intro x
  by_cases hx : x.val < 4
  · rw [__ch5_proposition_5_2_4_standardRootA4PermHom_apply_lt_four n __ch5_proposition_5_2_4_smallRho2.1 x hx]
    rcases x with ⟨x, hxn⟩
    interval_cases x <;>
      simp [__ch5_proposition_5_2_4_smallRho2, standardRootA4Embedding, rho2, p0, p1, p2, p3,
        Equiv.swap_apply_left, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne]
  · have hx4 : 4 ≤ x.val := by omega
    rw [__ch5_proposition_5_2_4_standardRootA4PermHom_apply_of_four_le n __ch5_proposition_5_2_4_smallRho2.1 x hx4]
    symm
    change Equiv.swap (p0 n) (p2 n) (Equiv.swap (p1 n) (p3 n) x) = x
    rw [__ch5_proposition_5_2_4_swap_fix_of_four_le n x (p1 n) (p3 n) hx4 (by simp [p1]) (by simp [p3])]
    rw [__ch5_proposition_5_2_4_swap_fix_of_four_le n x (p0 n) (p2 n) hx4 (by simp [p0]) (by simp [p2])]

private theorem __ch5_proposition_5_2_4_smallTau_extend (n : Nat) :
    standardRootA4PermHom n __ch5_proposition_5_2_4_smallTau.1 = tau n := by
  apply Equiv.Perm.ext
  intro x
  by_cases hx : x.val < 4
  · rw [__ch5_proposition_5_2_4_standardRootA4PermHom_apply_lt_four n __ch5_proposition_5_2_4_smallTau.1 x hx]
    rcases x with ⟨x, hxn⟩
    interval_cases x <;>
      simp [__ch5_proposition_5_2_4_smallTau, standardRootA4Embedding, tau, p0, p1, p2,
        Equiv.swap_apply_left, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne]
  · have hx4 : 4 ≤ x.val := by omega
    rw [__ch5_proposition_5_2_4_standardRootA4PermHom_apply_of_four_le n __ch5_proposition_5_2_4_smallTau.1 x hx4]
    symm
    change Equiv.swap (p0 n) (p1 n) (Equiv.swap (p1 n) (p2 n) x) = x
    rw [__ch5_proposition_5_2_4_swap_fix_of_four_le n x (p1 n) (p2 n) hx4 (by simp [p1]) (by simp [p2])]
    rw [__ch5_proposition_5_2_4_swap_fix_of_four_le n x (p0 n) (p1 n) hx4 (by simp [p0]) (by simp [p1])]

private theorem __ch5_proposition_5_2_4_rho1_mem_standardRootA4 (n : Nat) :
    (⟨rho1 n, rho1_mem_alternating n⟩ : alternatingGroup (Fin (n + 5))) ∈
      standardRootA4 n := by
  refine ⟨__ch5_proposition_5_2_4_smallRho1, ?_⟩
  apply Subtype.ext
  exact __ch5_proposition_5_2_4_smallRho1_extend n

private theorem __ch5_proposition_5_2_4_rho2_mem_standardRootA4 (n : Nat) :
    (⟨rho2 n, rho2_mem_alternating n⟩ : alternatingGroup (Fin (n + 5))) ∈
      standardRootA4 n := by
  refine ⟨__ch5_proposition_5_2_4_smallRho2, ?_⟩
  apply Subtype.ext
  exact __ch5_proposition_5_2_4_smallRho2_extend n

private theorem __ch5_proposition_5_2_4_tau_mem_alternating (n : Nat) :
    tau n ∈ alternatingGroup (Fin (n + 5)) := by
  rw [← g_proj n]
  exact (schurAlternatingProjection n (g n)).property

private theorem __ch5_proposition_5_2_4_tau_mem_standardRootA4 (n : Nat) :
    (⟨tau n, __ch5_proposition_5_2_4_tau_mem_alternating n⟩ : alternatingGroup (Fin (n + 5))) ∈
      standardRootA4 n := by
  refine ⟨__ch5_proposition_5_2_4_smallTau, ?_⟩
  apply Subtype.ext
  exact __ch5_proposition_5_2_4_smallTau_extend n

private theorem __ch5_proposition_5_2_4_rootFourSubgroup_le_standardRootA4 (n : Nat) :
    rootFourSubgroup n ≤ standardRootA4 n := by
  rw [rootFourSubgroup, Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl
  · exact __ch5_proposition_5_2_4_rho1_mem_standardRootA4 n
  · exact __ch5_proposition_5_2_4_rho2_mem_standardRootA4 n

private def __ch5_proposition_5_2_4_standardRootA4Hom (n : Nat) :
    alternatingGroup (Fin 4) →* alternatingGroup (Fin (n + 5)) :=
  { toFun := fun σ => ⟨standardRootA4PermHom n σ.1, by
      rw [Equiv.Perm.mem_alternatingGroup, sign_standardRootA4PermHom]
      exact σ.2⟩
    map_one' := by
      apply Subtype.ext
      simp [standardRootA4PermHom]
    map_mul' := by
      intro x y
      apply Subtype.ext
      simp [standardRootA4PermHom] }

private theorem __ch5_proposition_5_2_4_standardRootA4_eq_range (n : Nat) :
    standardRootA4 n = (__ch5_proposition_5_2_4_standardRootA4Hom n).range := rfl

private theorem __ch5_proposition_5_2_4_standardRootA4Hom_injective (n : Nat) :
    Function.Injective (__ch5_proposition_5_2_4_standardRootA4Hom n) := by
  intro x y hxy
  apply Subtype.ext
  apply Equiv.Perm.viaEmbeddingHom_injective (standardRootA4Embedding n)
  exact congrArg Subtype.val hxy

private theorem __ch5_proposition_5_2_4_standardRootA4_card (n : Nat) : Nat.card (standardRootA4 n) = 12 := by
  rw [__ch5_proposition_5_2_4_standardRootA4_eq_range]
  calc
    Nat.card (__ch5_proposition_5_2_4_standardRootA4Hom n).range = Nat.card (alternatingGroup (Fin 4)) :=
      (Nat.card_congr (Equiv.ofInjective (__ch5_proposition_5_2_4_standardRootA4Hom n)
        (__ch5_proposition_5_2_4_standardRootA4Hom_injective n))).symm
    _ = 12 := alternatingGroup.card_of_card_eq_four (by simp)

private abbrev __ch5_proposition_5_2_4_RootA4Preimage (n : Nat) :=
  (standardRootA4 n).comap (schurAlternatingProjection n)

private theorem __ch5_proposition_5_2_4_rootA4Preimage_card (n : Nat) : Nat.card (__ch5_proposition_5_2_4_RootA4Preimage n) = 24 := by
  rw [card_comap_mul (schurAlternatingProjection n)
    (schurAlternatingProjection_surjective n) (standardRootA4 n)]
  rw [__ch5_proposition_5_2_4_standardRootA4_card]
  rw [show Nat.card (schurAlternatingProjection n).ker = 2 by
    simpa [schurAlternatingCovering] using natCard_ker_schurAlternatingCovering n]

private def __ch5_proposition_5_2_4_q8RootA4Hom (n : Nat) : QuaternionGroup 2 →* __ch5_proposition_5_2_4_RootA4Preimage n :=
  (q8PhiHom n).codRestrict (__ch5_proposition_5_2_4_RootA4Preimage n) (by
    intro x
    exact __ch5_proposition_5_2_4_rootFourSubgroup_le_standardRootA4 n (q8PhiL n x).property)


private def __ch5_proposition_5_2_4_sourceS (n : Nat) : SchurAlternatingGroup n :=
  schurAlternatingCentral n * g n

private theorem __ch5_proposition_5_2_4_sourceS_mem_rootA4Preimage (n : Nat) :
    __ch5_proposition_5_2_4_sourceS n ∈ __ch5_proposition_5_2_4_RootA4Preimage n := by
  show schurAlternatingProjection n (__ch5_proposition_5_2_4_sourceS n) ∈ standardRootA4 n
  have hz : schurAlternatingProjection n (schurAlternatingCentral n) = 1 :=
    schurAlternatingProjection_central n
  have hg : schurAlternatingProjection n (g n) =
      ⟨tau n, __ch5_proposition_5_2_4_tau_mem_alternating n⟩ := by
    apply Subtype.ext
    exact g_proj n
  rw [__ch5_proposition_5_2_4_sourceS, map_mul, hz, one_mul, hg]
  exact __ch5_proposition_5_2_4_tau_mem_standardRootA4 n

private def __ch5_proposition_5_2_4_sourceSP (n : Nat) : __ch5_proposition_5_2_4_RootA4Preimage n :=
  ⟨__ch5_proposition_5_2_4_sourceS n, __ch5_proposition_5_2_4_sourceS_mem_rootA4Preimage n⟩

private theorem __ch5_proposition_5_2_4_sourceS_pow_three (n : Nat) : __ch5_proposition_5_2_4_sourceS n ^ 3 = 1 := by
  have hcomm : Commute (schurAlternatingCentral n) (g n) := by
    exact q8_z_comm n (g n)
  rw [__ch5_proposition_5_2_4_sourceS, hcomm.mul_pow, __ch5_proposition_5_2_4_g_pow_three]
  have hz2 := schurAlternatingCentral_sq n
  calc
    schurAlternatingCentral n ^ 3 * schurAlternatingCentral n =
        schurAlternatingCentral n ^ 4 := by group
    _ = (schurAlternatingCentral n ^ 2) ^ 2 := by
      rw [show 4 = 2 * 2 by norm_num, pow_mul]
    _ = 1 := by rw [hz2]; simp

private theorem __ch5_proposition_5_2_4_sourceSP_pow_three (n : Nat) : __ch5_proposition_5_2_4_sourceSP n ^ 3 = 1 := by
  apply Subtype.ext
  exact __ch5_proposition_5_2_4_sourceS_pow_three n

private def __ch5_proposition_5_2_4_c3SourceHom (n : Nat) :
    Multiplicative (ZMod 3) →* __ch5_proposition_5_2_4_RootA4Preimage n where
  toFun k := __ch5_proposition_5_2_4_sourceSP n ^ (Multiplicative.toAdd k).val
  map_one' := by simp
  map_mul' := by
    intro x y
    change ZMod 3 at x y
    change __ch5_proposition_5_2_4_sourceSP n ^ (x + y).val = __ch5_proposition_5_2_4_sourceSP n ^ x.val * __ch5_proposition_5_2_4_sourceSP n ^ y.val
    fin_cases x <;> fin_cases y
    all_goals simp only [ZMod.val]
    · change __ch5_proposition_5_2_4_sourceSP n ^ 0 = __ch5_proposition_5_2_4_sourceSP n ^ 0 * __ch5_proposition_5_2_4_sourceSP n ^ 0
      simp
    · change __ch5_proposition_5_2_4_sourceSP n ^ 1 = __ch5_proposition_5_2_4_sourceSP n ^ 0 * __ch5_proposition_5_2_4_sourceSP n ^ 1
      simp
    · change __ch5_proposition_5_2_4_sourceSP n ^ 2 = __ch5_proposition_5_2_4_sourceSP n ^ 0 * __ch5_proposition_5_2_4_sourceSP n ^ 2
      simp
    · change __ch5_proposition_5_2_4_sourceSP n ^ 1 = __ch5_proposition_5_2_4_sourceSP n ^ 1 * __ch5_proposition_5_2_4_sourceSP n ^ 0
      simp
    · change __ch5_proposition_5_2_4_sourceSP n ^ 2 = __ch5_proposition_5_2_4_sourceSP n ^ 1 * __ch5_proposition_5_2_4_sourceSP n ^ 1
      simp [pow_two]
    · change __ch5_proposition_5_2_4_sourceSP n ^ 0 = __ch5_proposition_5_2_4_sourceSP n ^ 1 * __ch5_proposition_5_2_4_sourceSP n ^ 2
      rw [← pow_add]
      norm_num
      exact (__ch5_proposition_5_2_4_sourceSP_pow_three n).symm
    · change __ch5_proposition_5_2_4_sourceSP n ^ 2 = __ch5_proposition_5_2_4_sourceSP n ^ 2 * __ch5_proposition_5_2_4_sourceSP n ^ 0
      simp
    · change __ch5_proposition_5_2_4_sourceSP n ^ 0 = __ch5_proposition_5_2_4_sourceSP n ^ 2 * __ch5_proposition_5_2_4_sourceSP n ^ 1
      rw [← pow_add]
      norm_num
      exact (__ch5_proposition_5_2_4_sourceSP_pow_three n).symm
    · change __ch5_proposition_5_2_4_sourceSP n ^ 1 = __ch5_proposition_5_2_4_sourceSP n ^ 2 * __ch5_proposition_5_2_4_sourceSP n ^ 2
      symm
      calc
        __ch5_proposition_5_2_4_sourceSP n ^ 2 * __ch5_proposition_5_2_4_sourceSP n ^ 2 = __ch5_proposition_5_2_4_sourceSP n ^ 4 := by
          rw [← pow_add]
        _ = __ch5_proposition_5_2_4_sourceSP n ^ 3 * __ch5_proposition_5_2_4_sourceSP n := by
          rw [show 4 = 3 + 1 by norm_num, pow_add, pow_one]
        _ = __ch5_proposition_5_2_4_sourceSP n := by rw [__ch5_proposition_5_2_4_sourceSP_pow_three]; simp

private theorem __ch5_proposition_5_2_4_sourceS_conj (n : Nat) (x : SchurAlternatingGroup n) :
    __ch5_proposition_5_2_4_sourceS n * x * (__ch5_proposition_5_2_4_sourceS n)⁻¹ = g n * x * (g n)⁻¹ := by
  calc
    __ch5_proposition_5_2_4_sourceS n * x * (__ch5_proposition_5_2_4_sourceS n)⁻¹ =
        schurAlternatingCentral n * (g n * x * (g n)⁻¹) *
          (schurAlternatingCentral n)⁻¹ := by
      rw [__ch5_proposition_5_2_4_sourceS]
      group
    _ = (g n * x * (g n)⁻¹) * schurAlternatingCentral n *
        (schurAlternatingCentral n)⁻¹ := by
      rw [q8_z_comm]
    _ = g n * x * (g n)⁻¹ := by simp

private theorem __ch5_proposition_5_2_4_source_action_one (n : Nat) (x : QuaternionGroup 2) :
    __ch5_proposition_5_2_4_q8RootA4Hom n (q8Cycle x) =
      __ch5_proposition_5_2_4_sourceSP n * __ch5_proposition_5_2_4_q8RootA4Hom n x * (__ch5_proposition_5_2_4_sourceSP n)⁻¹ := by
  let f : QuaternionGroup 2 →* __ch5_proposition_5_2_4_RootA4Preimage n :=
    (__ch5_proposition_5_2_4_q8RootA4Hom n).comp q8Cycle.toMonoidHom
  let h : QuaternionGroup 2 →* __ch5_proposition_5_2_4_RootA4Preimage n :=
    (MulAut.conj (__ch5_proposition_5_2_4_sourceSP n)).toMonoidHom.comp (__ch5_proposition_5_2_4_q8RootA4Hom n)
  have hA : f (QuaternionGroup.a 1) = h (QuaternionGroup.a 1) := by
    apply Subtype.ext
    change q8Phi n (q8Cycle (QuaternionGroup.a 1)) =
      __ch5_proposition_5_2_4_sourceS n * u1 n * (__ch5_proposition_5_2_4_sourceS n)⁻¹
    rw [show q8Cycle (QuaternionGroup.a 1) = QuaternionGroup.xa 1 by decide]
    change u2 n * u1 n = __ch5_proposition_5_2_4_sourceS n * u1 n * (__ch5_proposition_5_2_4_sourceS n)⁻¹
    rw [__ch5_proposition_5_2_4_sourceS_conj, __ch5_proposition_5_2_4_g_conj_u1, q8_u1_mul_u2_mul]
    simp [mul_assoc]
  have hJ : f (QuaternionGroup.xa 0) = h (QuaternionGroup.xa 0) := by
    apply Subtype.ext
    change q8Phi n (q8Cycle (QuaternionGroup.xa 0)) =
      __ch5_proposition_5_2_4_sourceS n * u2 n * (__ch5_proposition_5_2_4_sourceS n)⁻¹
    rw [show q8Cycle (QuaternionGroup.xa 0) = QuaternionGroup.a 3 by decide]
    change u1 n ^ 3 = __ch5_proposition_5_2_4_sourceS n * u2 n * (__ch5_proposition_5_2_4_sourceS n)⁻¹
    rw [__ch5_proposition_5_2_4_sourceS_conj, __ch5_proposition_5_2_4_g_conj_u2, q8_u1_pow_three]
  have hfh : f = h := by
    apply DFunLike.ext _ _
    intro y
    rcases y with i | i
    · rw [← ZMod.natCast_zmod_val i, ← QuaternionGroup.a_one_pow]
      rw [map_pow, map_pow, hA]
    · have hxa : QuaternionGroup.xa i =
          QuaternionGroup.xa 0 * QuaternionGroup.a i := by
        rw [QuaternionGroup.xa_mul_a]
        simp
      rw [hxa, map_mul, map_mul, hJ]
      rw [← ZMod.natCast_zmod_val i, ← QuaternionGroup.a_one_pow]
      rw [map_pow, map_pow, hA]
  have := DFunLike.congr_fun hfh x
  exact this

private theorem __ch5_proposition_5_2_4_source_action_compat (n : Nat)
    (k : Multiplicative (ZMod 3)) (x : QuaternionGroup 2) :
    __ch5_proposition_5_2_4_q8RootA4Hom n (q8C3Action k x) =
      __ch5_proposition_5_2_4_c3SourceHom n k * __ch5_proposition_5_2_4_q8RootA4Hom n x * (__ch5_proposition_5_2_4_c3SourceHom n k)⁻¹ := by
  change ZMod 3 at k
  change __ch5_proposition_5_2_4_q8RootA4Hom n ((q8Cycle ^ k.val) x) =
    __ch5_proposition_5_2_4_sourceSP n ^ k.val * __ch5_proposition_5_2_4_q8RootA4Hom n x * (__ch5_proposition_5_2_4_sourceSP n ^ k.val)⁻¹
  fin_cases k
  all_goals simp only [ZMod.val]
  · simp
  · simpa using __ch5_proposition_5_2_4_source_action_one n x
  · change __ch5_proposition_5_2_4_q8RootA4Hom n (q8Cycle (q8Cycle x)) =
      __ch5_proposition_5_2_4_sourceSP n ^ 2 * __ch5_proposition_5_2_4_q8RootA4Hom n x * (__ch5_proposition_5_2_4_sourceSP n ^ 2)⁻¹
    calc
      __ch5_proposition_5_2_4_q8RootA4Hom n (q8Cycle (q8Cycle x)) =
          __ch5_proposition_5_2_4_sourceSP n * __ch5_proposition_5_2_4_q8RootA4Hom n (q8Cycle x) * (__ch5_proposition_5_2_4_sourceSP n)⁻¹ :=
        __ch5_proposition_5_2_4_source_action_one n (q8Cycle x)
      _ = __ch5_proposition_5_2_4_sourceSP n *
          (__ch5_proposition_5_2_4_sourceSP n * __ch5_proposition_5_2_4_q8RootA4Hom n x * (__ch5_proposition_5_2_4_sourceSP n)⁻¹) *
          (__ch5_proposition_5_2_4_sourceSP n)⁻¹ := by rw [__ch5_proposition_5_2_4_source_action_one]
      _ = __ch5_proposition_5_2_4_sourceSP n ^ 2 * __ch5_proposition_5_2_4_q8RootA4Hom n x * (__ch5_proposition_5_2_4_sourceSP n ^ 2)⁻¹ := by
        rw [pow_two]
        group

private def __ch5_proposition_5_2_4_binaryTetrahedralToSource (n : Nat) :
    (QuaternionGroup 2 ⋊[q8C3Action] Multiplicative (ZMod 3)) →*
      __ch5_proposition_5_2_4_RootA4Preimage n :=
  SemidirectProduct.lift (__ch5_proposition_5_2_4_q8RootA4Hom n) (__ch5_proposition_5_2_4_c3SourceHom n) (by
    intro k
    apply MonoidHom.ext
    intro x
    exact __ch5_proposition_5_2_4_source_action_compat n k x)


private theorem __ch5_proposition_5_2_4_tau_ne_one (n : Nat) : tau n ≠ 1 := by
  intro h
  have hp := congrArg (fun σ : Equiv.Perm (Fin (n + 5)) => σ (p0 n)) h
  simp [tau, p0, p1, p2, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne] at hp

private theorem __ch5_proposition_5_2_4_tau_ne_rho1 (n : Nat) : tau n ≠ rho1 n := by
  intro h
  have hp := congrArg (fun σ : Equiv.Perm (Fin (n + 5)) => σ (p1 n)) h
  simp [tau, rho1, p0, p1, p2, p3, Equiv.swap_apply_left,
    Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne] at hp

private theorem __ch5_proposition_5_2_4_tau_ne_rho2 (n : Nat) : tau n ≠ rho2 n := by
  intro h
  have hp := congrArg (fun σ : Equiv.Perm (Fin (n + 5)) => σ (p0 n)) h
  simp [tau, rho2, p0, p1, p2, p3, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne] at hp

private theorem __ch5_proposition_5_2_4_tau_ne_rho3 (n : Nat) : tau n ≠ rho3 n := by
  intro h
  have hp := congrArg (fun σ : Equiv.Perm (Fin (n + 5)) => σ (p0 n)) h
  simp [tau, rho3, p0, p1, p2, p3, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne] at hp

private theorem __ch5_proposition_5_2_4_tau_sq_ne_one (n : Nat) : tau n ^ 2 ≠ 1 := by
  intro h
  have hp := congrArg (fun σ : Equiv.Perm (Fin (n + 5)) => σ (p0 n)) h
  simp [pow_two, tau, p0, p1, p2, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne] at hp

private theorem __ch5_proposition_5_2_4_tau_sq_ne_rho1 (n : Nat) : tau n ^ 2 ≠ rho1 n := by
  intro h
  have hp := congrArg (fun σ : Equiv.Perm (Fin (n + 5)) => σ (p0 n)) h
  simp [pow_two, tau, rho1, p0, p1, p2, p3, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne] at hp

private theorem __ch5_proposition_5_2_4_tau_sq_ne_rho2 (n : Nat) : tau n ^ 2 ≠ rho2 n := by
  intro h
  have hp := congrArg (fun σ : Equiv.Perm (Fin (n + 5)) => σ (p1 n)) h
  simp [pow_two, tau, rho2, p0, p1, p2, p3, Equiv.swap_apply_left,
    Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne] at hp

private theorem __ch5_proposition_5_2_4_tau_sq_ne_rho3 (n : Nat) : tau n ^ 2 ≠ rho3 n := by
  intro h
  have hp := congrArg (fun σ : Equiv.Perm (Fin (n + 5)) => σ (p0 n)) h
  simp [pow_two, tau, rho3, p0, p1, p2, p3, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne] at hp

private theorem __ch5_proposition_5_2_4_tau_not_mem_rootFourSubgroup (n : Nat) :
    (⟨tau n, __ch5_proposition_5_2_4_tau_mem_alternating n⟩ : alternatingGroup (Fin (n + 5))) ∉
      rootFourSubgroup n := by
  intro h
  rcases V_elements n h with h | h | h | h
  · exact __ch5_proposition_5_2_4_tau_ne_one n h
  · exact __ch5_proposition_5_2_4_tau_ne_rho1 n h
  · exact __ch5_proposition_5_2_4_tau_ne_rho2 n h
  · exact __ch5_proposition_5_2_4_tau_ne_rho3 n h

private theorem __ch5_proposition_5_2_4_tau_sq_not_mem_rootFourSubgroup (n : Nat) :
    (⟨tau n, __ch5_proposition_5_2_4_tau_mem_alternating n⟩ : alternatingGroup (Fin (n + 5))) ^ 2 ∉
      rootFourSubgroup n := by
  intro h
  rcases V_elements n h with h | h | h | h
  · exact __ch5_proposition_5_2_4_tau_sq_ne_one n h
  · exact __ch5_proposition_5_2_4_tau_sq_ne_rho1 n h
  · exact __ch5_proposition_5_2_4_tau_sq_ne_rho2 n h
  · exact __ch5_proposition_5_2_4_tau_sq_ne_rho3 n h

private theorem __ch5_proposition_5_2_4_q8PhiL_injective (n : Nat) : Function.Injective (q8PhiL n) := by
  have : Fintype (rootFourPreimage n) := Fintype.ofFinite _
  have hsurj : Function.Surjective (q8PhiL n) := by
    rw [← MonoidHom.range_eq_top]
    exact q8PhiL_range_eq_top n
  have hcardQ : Fintype.card (QuaternionGroup 2) = 8 := by
    rw [QuaternionGroup.card]
  have hcardL : Fintype.card (rootFourPreimage n) = 8 := by
    rw [← Nat.card_eq_fintype_card]
    exact rootFourPreimage_card n
  exact (Fintype.bijective_iff_surjective_and_card (q8PhiL n)).2
    ⟨hsurj, by rw [hcardQ, hcardL]⟩ |>.1

private theorem __ch5_proposition_5_2_4_q8RootA4Hom_injective (n : Nat) :
    Function.Injective (__ch5_proposition_5_2_4_q8RootA4Hom n) := by
  intro x y hxy
  apply __ch5_proposition_5_2_4_q8PhiL_injective n
  apply Subtype.ext
  exact congrArg (fun z : __ch5_proposition_5_2_4_RootA4Preimage n => z.1) hxy

private theorem __ch5_proposition_5_2_4_sourceSP_projection (n : Nat) :
    schurAlternatingProjection n (__ch5_proposition_5_2_4_sourceSP n).1 =
      ⟨tau n, __ch5_proposition_5_2_4_tau_mem_alternating n⟩ := by
  change schurAlternatingProjection n (__ch5_proposition_5_2_4_sourceS n) =
    ⟨tau n, __ch5_proposition_5_2_4_tau_mem_alternating n⟩
  rw [__ch5_proposition_5_2_4_sourceS, map_mul, schurAlternatingProjection_central, one_mul]
  apply Subtype.ext
  exact g_proj n

private theorem __ch5_proposition_5_2_4_binaryTetrahedralToSource_injective (n : Nat) :
    Function.Injective (__ch5_proposition_5_2_4_binaryTetrahedralToSource n) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rw [Subgroup.eq_bot_iff_forall]
  rintro ⟨q, k⟩ hk
  rw [MonoidHom.mem_ker] at hk
  change __ch5_proposition_5_2_4_q8RootA4Hom n q * __ch5_proposition_5_2_4_c3SourceHom n k = 1 at hk
  change ZMod 3 at k
  fin_cases k
  · simp only [__ch5_proposition_5_2_4_c3SourceHom, ZMod.val] at hk
    change __ch5_proposition_5_2_4_q8RootA4Hom n q * __ch5_proposition_5_2_4_sourceSP n ^ 0 = 1 at hk
    have hqim : __ch5_proposition_5_2_4_q8RootA4Hom n q = 1 := by simpa using hk
    have hq : q = 1 := __ch5_proposition_5_2_4_q8RootA4Hom_injective n (by simpa using hqim)
    apply SemidirectProduct.ext
    · simpa using hq
    · rfl
  · simp only [__ch5_proposition_5_2_4_c3SourceHom, ZMod.val] at hk
    change __ch5_proposition_5_2_4_q8RootA4Hom n q * __ch5_proposition_5_2_4_sourceSP n = 1 at hk
    let v := schurAlternatingProjection n (__ch5_proposition_5_2_4_q8RootA4Hom n q).1
    let t : alternatingGroup (Fin (n + 5)) :=
      ⟨tau n, __ch5_proposition_5_2_4_tau_mem_alternating n⟩
    have hv : v ∈ rootFourSubgroup n := by
      exact (q8PhiL n q).property
    have hp : v * t = 1 := by
      have hp' := congrArg
        (fun z : __ch5_proposition_5_2_4_RootA4Preimage n => schurAlternatingProjection n z.1) hk
      change schurAlternatingProjection n
        ((__ch5_proposition_5_2_4_q8RootA4Hom n q).1 * (__ch5_proposition_5_2_4_sourceSP n).1) = 1 at hp'
      rw [map_mul, __ch5_proposition_5_2_4_sourceSP_projection] at hp'
      exact hp'
    have ht : t = v⁻¹ := by
      calc
        t = 1 * t := by simp
        _ = (v⁻¹ * v) * t := by simp
        _ = v⁻¹ * (v * t) := by group
        _ = v⁻¹ := by rw [hp]; simp
    have htmem : t ∈ rootFourSubgroup n := by
      rw [ht]
      exact (rootFourSubgroup n).inv_mem hv
    exfalso
    exact (__ch5_proposition_5_2_4_tau_not_mem_rootFourSubgroup n) (by simpa [t] using htmem)
  · simp only [__ch5_proposition_5_2_4_c3SourceHom, ZMod.val] at hk
    change __ch5_proposition_5_2_4_q8RootA4Hom n q * __ch5_proposition_5_2_4_sourceSP n ^ 2 = 1 at hk
    let v := schurAlternatingProjection n (__ch5_proposition_5_2_4_q8RootA4Hom n q).1
    let t : alternatingGroup (Fin (n + 5)) :=
      ⟨tau n, __ch5_proposition_5_2_4_tau_mem_alternating n⟩
    have hv : v ∈ rootFourSubgroup n := by
      exact (q8PhiL n q).property
    have hp : v * t ^ 2 = 1 := by
      have hp' := congrArg
        (fun z : __ch5_proposition_5_2_4_RootA4Preimage n => schurAlternatingProjection n z.1) hk
      change schurAlternatingProjection n
        ((__ch5_proposition_5_2_4_q8RootA4Hom n q).1 * (__ch5_proposition_5_2_4_sourceSP n).1 ^ 2) = 1 at hp'
      rw [map_mul, map_pow, __ch5_proposition_5_2_4_sourceSP_projection] at hp'
      exact hp'
    have ht : t ^ 2 = v⁻¹ := by
      calc
        t ^ 2 = 1 * t ^ 2 := by simp
        _ = (v⁻¹ * v) * t ^ 2 := by simp
        _ = v⁻¹ * (v * t ^ 2) := by group
        _ = v⁻¹ := by rw [hp]; simp
    have htmem : t ^ 2 ∈ rootFourSubgroup n := by
      rw [ht]
      exact (rootFourSubgroup n).inv_mem hv
    exfalso
    exact (__ch5_proposition_5_2_4_tau_sq_not_mem_rootFourSubgroup n) (by simpa [t] using htmem)

private noncomputable def binaryTetrahedralEquivSource (n : Nat) :
    (QuaternionGroup 2 ⋊[q8C3Action] Multiplicative (ZMod 3)) ≃*
      __ch5_proposition_5_2_4_RootA4Preimage n := by
  letI := __ch5_proposition_5_2_4_binaryTetrahedralFintype
  haveI : Fintype (__ch5_proposition_5_2_4_RootA4Preimage n) := Fintype.ofFinite _
  apply MulEquiv.ofBijective (__ch5_proposition_5_2_4_binaryTetrahedralToSource n)
  apply (Fintype.bijective_iff_injective_and_card (__ch5_proposition_5_2_4_binaryTetrahedralToSource n)).2
  constructor
  · exact __ch5_proposition_5_2_4_binaryTetrahedralToSource_injective n
  · rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      SemidirectProduct.card, __ch5_proposition_5_2_4_rootA4Preimage_card]
    norm_num [QuaternionGroup.card]


/-- Proposition 5.2.4(c): the full preimage of the standard root `A₄`
subgroup in the Schur double cover is `2A₄ = SL₂(3)`. -/
public theorem proposition_5_2_4_c (n : Nat) :
    Nonempty
      (↥((standardRootA4 n).comap (schurAlternatingProjection n)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) := by
  exact ⟨(binaryTetrahedralEquivSource n).symm.trans binaryTetrahedralEquivSL⟩

/-- Proposition 5.2.4(g): if an elementary abelian `2`-subgroup of the
alternating quotient has order at least eight and acts semiregularly on its
support, then its full preimage in the Schur double cover is elementary
abelian. -/
public theorem proposition_5_2_4_g (n : Nat)
    (Lbar : Subgroup (alternatingGroup (Fin (n + 5))))
    (hLbar : IsMulCommutative ↥Lbar ∧
      ∀ x : ↥Lbar, orderOf x = 1 ∨ orderOf x = 2)
    (hcard : 8 ≤ Nat.card ↥Lbar)
    (hsemiregular : ∀ x : ↥Lbar, x ≠ 1 →
      ∀ omega : Fin (n + 5),
        (∃ y : ↥Lbar, y.1.1 omega ≠ omega) → x.1.1 omega ≠ omega) :
    let L := Lbar.comap (schurAlternatingProjection n)
    IsMulCommutative ↥L ∧ ∀ x : ↥L, orderOf x = 1 ∨ orderOf x = 2 := by
  let L := Lbar.comap (schurAlternatingProjection n)
  change IsMulCommutative ↥L ∧
    ∀ x : ↥L, orderOf x = 1 ∨ orderOf x = 2
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpgroup : IsPGroup 2 ↥Lbar := by
    rw [IsPGroup.iff_orderOf]
    intro x
    rcases hLbar.2 x with hx1 | hx2
    · exact ⟨0, by simp [hx1]⟩
    · exact ⟨1, by simpa using hx2⟩
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp hpgroup
  have hr3 : 3 ≤ r := by
    rw [hr] at hcard
    by_contra h
    have hrle : r ≤ 2 := by omega
    interval_cases r <;> norm_num at hcard
  have h8card : 8 ∣ Nat.card ↥Lbar := by
    refine ⟨2 ^ (r - 3), ?_⟩
    rw [hr, show (8 : Nat) = 2 ^ 3 by norm_num, ← pow_add,
      Nat.add_sub_of_le hr3]
  have hker : Nat.card (schurAlternatingProjection n).ker = 2 := by
    simpa [schurAlternatingCovering] using
      natCard_ker_schurAlternatingCovering n
  have hsq : ∀ x : ↥L, x ^ 2 = 1 := by
    intro x
    let xbar : ↥Lbar := ⟨schurAlternatingProjection n x.1, x.2⟩
    by_cases hxbar : xbar = 1
    · apply Subtype.ext
      apply DoubleCoverUniqueness.ker_pow_two_eq_one
        (schurAlternatingProjection n) hker
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val hxbar
    · have hxbar_order : orderOf xbar = 2 := by
        rcases hLbar.2 xbar with hx1 | hx2
        · exact (hxbar (orderOf_eq_one_iff.mp hx1)).elim
        · exact hx2
      have hxbar_sq : xbar.1 ^ 2 = 1 := by
        have hpow := pow_orderOf_eq_one xbar
        rw [hxbar_order] at hpow
        exact congrArg Subtype.val hpow
      have hsupp_dvd : 8 ∣ xbar.1.1.support.card :=
        h8card.trans
          (semiregular_support_card_dvd Lbar hLbar.1 xbar hsemiregular)
      obtain ⟨t, ht⟩ := hsupp_dvd
      let m := 2 * t
      have hsupp_pos : 0 < xbar.1.1.support.card := by
        rw [Finset.card_pos]
        rw [Finset.nonempty_iff_ne_empty]
        intro hempty
        apply hxbar
        apply Subtype.ext
        apply Subtype.ext
        exact Equiv.Perm.support_eq_empty_iff.mp hempty
      have htpos : 0 < t := by omega
      have hm : 1 ≤ m := by
        dsimp [m]
        omega
      have hsupp_le : xbar.1.1.support.card ≤ n + 5 := by
        simpa using Finset.card_le_univ xbar.1.1.support
      have h4m : 4 * m ≤ n + 5 := by
        dsimp [m]
        omega
      let y := canonicalLift n m h4m
      let ybar := schurAlternatingProjection n y
      have hybar_sq : ybar.1 ^ 2 = 1 := by
        have hyorder : orderOf ybar = 2 :=
          canonicalLift_proj_order_two n m h4m hm
        have hpow := pow_orderOf_eq_one ybar
        rw [hyorder] at hpow
        exact congrArg Subtype.val hpow
      have hcard_support : xbar.1.1.support.card = ybar.1.support.card := by
        rw [show ybar.1 = canonicalPerm n m h4m by
          exact canonicalLift_proj n m h4m]
        rw [canonicalPerm_support_card n m h4m]
        dsimp [m]
        omega
      have hxbar_ne_alt : xbar.1 ≠ 1 := by
        intro h
        apply hxbar
        apply Subtype.ext
        exact h
      have hconj : IsConj xbar.1 ybar :=
        alternating_involution_isConj_of_card_support_eq
          (congrArg Subtype.val hxbar_sq) hybar_sq hxbar_ne_alt hcard_support
      obtain ⟨c, hc⟩ := isConj_iff.mp hconj
      have hsquare_eq : x.1 ^ 2 = y ^ 2 :=
        DoubleCoverUniqueness.sq_eq_sq_of_conjugate_images
          (schurAlternatingCovering n) hker hxbar_sq (by
            change c * schurAlternatingProjection n x.1 * c⁻¹ =
              schurAlternatingProjection n y
            simpa [xbar, ybar] using hc)
      have hy_sq : y ^ 2 = 1 := by
        rw [canonicalLift_sq]
        exact central_pow_of_even n ⟨t, by simp [m, Nat.two_mul]⟩
      exact Subtype.ext (hsquare_eq.trans hy_sq)
  constructor
  · apply IsMulCommutative.of_comm
    intro x y
    have hxinv : x⁻¹ = x := by
      apply inv_eq_of_mul_eq_one_left
      simpa [pow_two] using hsq x
    have hyinv : y⁻¹ = y := by
      apply inv_eq_of_mul_eq_one_left
      simpa [pow_two] using hsq y
    have hxyinv : (x * y)⁻¹ = x * y := by
      apply inv_eq_of_mul_eq_one_left
      simpa [pow_two] using hsq (x * y)
    calc
      x * y = (x * y)⁻¹ := hxyinv.symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [hxinv, hyinv]
  · intro x
    by_cases hx : x = 1
    · left
      simp [hx]
    · right
      exact orderOf_eq_prime (hsq x) hx

end GLS3.Chapter5.SchurPresentation
/- END KGroup.GLS3.Chapter5.proposition_5_2_4 -/

/- BEGIN Theory.Theorem523BaseNine -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation.Theorem523BaseNine

@[expose] public def a6X : alternatingGroup (Fin 6) :=
  alternatingSuzukiGenerator 1 0

@[expose] public def a6Y : alternatingGroup (Fin 6) :=
  (alternatingSuzukiGenerator 1 3)⁻¹ *
    (alternatingSuzukiGenerator 1 2)⁻¹

public theorem a6X_order : orderOf a6X = 3 := by
  apply orderOf_eq_prime_iff.mpr
  constructor <;> decide

public theorem a6Y_order : orderOf a6Y = 3 := by
  apply orderOf_eq_prime_iff.mpr
  constructor <;> decide

public theorem a6_commute : Commute a6X a6Y := by
  rw [commute_iff_eq]
  all_goals decide
private def __ch5_Theorem523BaseNine_a6H : Subgroup (alternatingGroup (Fin 6)) :=
  Subgroup.zpowers a6X

private def __ch5_Theorem523BaseNine_a6K : Subgroup (alternatingGroup (Fin 6)) :=
  Subgroup.zpowers a6Y

private theorem __ch5_Theorem523BaseNine_a6_disjoint : Disjoint __ch5_Theorem523BaseNine_a6H __ch5_Theorem523BaseNine_a6K := by
  rw [disjoint_iff_inf_le]
  intro z hz
  rcases hz with ⟨hzH, hzK⟩
  have hzH' :=
    (isOfFinOrder_of_finite a6X).mem_zpowers_iff_mem_range_orderOf.mp hzH
  have hzK' :=
    (isOfFinOrder_of_finite a6Y).mem_zpowers_iff_mem_range_orderOf.mp hzK
  rw [a6X_order] at hzH'
  rw [a6Y_order] at hzK'
  rcases Finset.mem_image.mp hzH' with ⟨i, hi, hiz⟩
  rcases Finset.mem_image.mp hzK' with ⟨j, hj, hjz⟩
  have hij : a6X ^ i = a6Y ^ j := hiz.trans hjz.symm
  rw [Finset.mem_range] at hi hj
  rw [Subgroup.mem_bot, ← hiz]
  interval_cases i <;> interval_cases j
  all_goals try simp
  all_goals
    exfalso
    revert hij
    all_goals decide
private theorem __ch5_Theorem523BaseNine_a6_commutes (h : __ch5_Theorem523BaseNine_a6H) (k : __ch5_Theorem523BaseNine_a6K) :
    Commute (__ch5_Theorem523BaseNine_a6H.subtype h)
      (__ch5_Theorem523BaseNine_a6K.subtype k) := by
  change Commute (h : alternatingGroup (Fin 6)) (k : alternatingGroup (Fin 6))
  rcases h.2 with ⟨i, hi⟩
  rcases k.2 with ⟨j, hj⟩
  rw [← hi, ← hj]
  exact a6_commute.zpow_zpow i j

private def __ch5_Theorem523BaseNine_a6Product : __ch5_Theorem523BaseNine_a6H × __ch5_Theorem523BaseNine_a6K →* alternatingGroup (Fin 6) :=
  MonoidHom.noncommCoprod __ch5_Theorem523BaseNine_a6H.subtype __ch5_Theorem523BaseNine_a6K.subtype __ch5_Theorem523BaseNine_a6_commutes

private theorem __ch5_Theorem523BaseNine_a6Product_injective : Function.Injective __ch5_Theorem523BaseNine_a6Product := by
  rw [__ch5_Theorem523BaseNine_a6Product, MonoidHom.noncommCoprod_injective]
  refine ⟨__ch5_Theorem523BaseNine_a6H.subtype_injective, __ch5_Theorem523BaseNine_a6K.subtype_injective, ?_⟩
  simpa using __ch5_Theorem523BaseNine_a6_disjoint

public def a6StandardNine : Subgroup (alternatingGroup (Fin 6)) :=
  Subgroup.zpowers (alternatingSuzukiGenerator 1 (0 : Fin 4)) ⊔
    Subgroup.zpowers
      ((alternatingSuzukiGenerator 1 (3 : Fin 4))⁻¹ *
        (alternatingSuzukiGenerator 1 (2 : Fin 4))⁻¹)

public theorem a6StandardNine_eq :
    a6StandardNine = Subgroup.zpowers a6X ⊔ Subgroup.zpowers a6Y := by
  rfl

private theorem __ch5_Theorem523BaseNine_a6StandardNine_card_private : Nat.card a6StandardNine = 9 := by
  have hrange : __ch5_Theorem523BaseNine_a6Product.range = a6StandardNine := by
    rw [__ch5_Theorem523BaseNine_a6Product, MonoidHom.noncommCoprod_range]
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    rfl
  have hcardRange : Nat.card __ch5_Theorem523BaseNine_a6Product.range = Nat.card (__ch5_Theorem523BaseNine_a6H × __ch5_Theorem523BaseNine_a6K) :=
    (Nat.card_congr (Equiv.ofInjective __ch5_Theorem523BaseNine_a6Product __ch5_Theorem523BaseNine_a6Product_injective)).symm
  rw [hrange] at hcardRange
  have hHcard : Nat.card __ch5_Theorem523BaseNine_a6H = 3 := by
    rw [__ch5_Theorem523BaseNine_a6H, Nat.card_zpowers, a6X_order]
  have hKcard : Nat.card __ch5_Theorem523BaseNine_a6K = 3 := by
    rw [__ch5_Theorem523BaseNine_a6K, Nat.card_zpowers, a6Y_order]
  calc
    Nat.card a6StandardNine = Nat.card (__ch5_Theorem523BaseNine_a6H × __ch5_Theorem523BaseNine_a6K) := hcardRange
    _ = Nat.card __ch5_Theorem523BaseNine_a6H * Nat.card __ch5_Theorem523BaseNine_a6K := Nat.card_prod _ _
    _ = 9 := by rw [hHcard, hKcard]

public theorem a6_card :
    Nat.card a6StandardNine = 9 :=
  __ch5_Theorem523BaseNine_a6StandardNine_card_private

public theorem a6_explicit_card :
    Nat.card
      ((Subgroup.zpowers (alternatingSuzukiGenerator 1 (0 : Fin 4)) ⊔
          Subgroup.zpowers
            ((alternatingSuzukiGenerator 1 (3 : Fin 4))⁻¹ *
              (alternatingSuzukiGenerator 1 (2 : Fin 4))⁻¹)) :
        Subgroup (alternatingGroup (Fin 6))) = 9 := by
  change Nat.card a6StandardNine = 9
  exact a6_card

@[expose] public def a7X : alternatingGroup (Fin 7) :=
  alternatingSuzukiGenerator 2 0

@[expose] public def a7Y : alternatingGroup (Fin 7) :=
  (alternatingSuzukiGenerator 2 3)⁻¹ *
    (alternatingSuzukiGenerator 2 2)⁻¹

public theorem a7X_order : orderOf a7X = 3 := by
  apply orderOf_eq_prime_iff.mpr
  constructor <;> decide

public theorem a7Y_order : orderOf a7Y = 3 := by
  apply orderOf_eq_prime_iff.mpr
  constructor <;> decide

public theorem a7_commute : Commute a7X a7Y := by
  rw [commute_iff_eq]
  all_goals decide
private def __ch5_Theorem523BaseNine_a7H : Subgroup (alternatingGroup (Fin 7)) :=
  Subgroup.zpowers a7X

private def __ch5_Theorem523BaseNine_a7K : Subgroup (alternatingGroup (Fin 7)) :=
  Subgroup.zpowers a7Y

private theorem __ch5_Theorem523BaseNine_a7_disjoint : Disjoint __ch5_Theorem523BaseNine_a7H __ch5_Theorem523BaseNine_a7K := by
  rw [disjoint_iff_inf_le]
  intro z hz
  rcases hz with ⟨hzH, hzK⟩
  have hzH' :=
    (isOfFinOrder_of_finite a7X).mem_zpowers_iff_mem_range_orderOf.mp hzH
  have hzK' :=
    (isOfFinOrder_of_finite a7Y).mem_zpowers_iff_mem_range_orderOf.mp hzK
  rw [a7X_order] at hzH'
  rw [a7Y_order] at hzK'
  rcases Finset.mem_image.mp hzH' with ⟨i, hi, hiz⟩
  rcases Finset.mem_image.mp hzK' with ⟨j, hj, hjz⟩
  have hij : a7X ^ i = a7Y ^ j := hiz.trans hjz.symm
  rw [Finset.mem_range] at hi hj
  rw [Subgroup.mem_bot, ← hiz]
  interval_cases i <;> interval_cases j
  all_goals try simp
  all_goals
    exfalso
    revert hij
    all_goals decide
private theorem __ch5_Theorem523BaseNine_a7_commutes (h : __ch5_Theorem523BaseNine_a7H) (k : __ch5_Theorem523BaseNine_a7K) :
    Commute (__ch5_Theorem523BaseNine_a7H.subtype h)
      (__ch5_Theorem523BaseNine_a7K.subtype k) := by
  change Commute (h : alternatingGroup (Fin 7)) (k : alternatingGroup (Fin 7))
  rcases h.2 with ⟨i, hi⟩
  rcases k.2 with ⟨j, hj⟩
  rw [← hi, ← hj]
  exact a7_commute.zpow_zpow i j

private def __ch5_Theorem523BaseNine_a7Product : __ch5_Theorem523BaseNine_a7H × __ch5_Theorem523BaseNine_a7K →* alternatingGroup (Fin 7) :=
  MonoidHom.noncommCoprod __ch5_Theorem523BaseNine_a7H.subtype __ch5_Theorem523BaseNine_a7K.subtype __ch5_Theorem523BaseNine_a7_commutes

private theorem __ch5_Theorem523BaseNine_a7Product_injective : Function.Injective __ch5_Theorem523BaseNine_a7Product := by
  rw [__ch5_Theorem523BaseNine_a7Product, MonoidHom.noncommCoprod_injective]
  refine ⟨__ch5_Theorem523BaseNine_a7H.subtype_injective, __ch5_Theorem523BaseNine_a7K.subtype_injective, ?_⟩
  simpa using __ch5_Theorem523BaseNine_a7_disjoint

public def a7StandardNine : Subgroup (alternatingGroup (Fin 7)) :=
  Subgroup.zpowers (alternatingSuzukiGenerator 2 (0 : Fin 5)) ⊔
    Subgroup.zpowers
      ((alternatingSuzukiGenerator 2 (3 : Fin 5))⁻¹ *
        (alternatingSuzukiGenerator 2 (2 : Fin 5))⁻¹)

public theorem a7StandardNine_eq :
    a7StandardNine = Subgroup.zpowers a7X ⊔ Subgroup.zpowers a7Y := by
  rfl

private theorem __ch5_Theorem523BaseNine_a7StandardNine_card_private : Nat.card a7StandardNine = 9 := by
  have hrange : __ch5_Theorem523BaseNine_a7Product.range = a7StandardNine := by
    rw [__ch5_Theorem523BaseNine_a7Product, MonoidHom.noncommCoprod_range]
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    rfl
  have hcardRange : Nat.card __ch5_Theorem523BaseNine_a7Product.range = Nat.card (__ch5_Theorem523BaseNine_a7H × __ch5_Theorem523BaseNine_a7K) :=
    (Nat.card_congr (Equiv.ofInjective __ch5_Theorem523BaseNine_a7Product __ch5_Theorem523BaseNine_a7Product_injective)).symm
  rw [hrange] at hcardRange
  have hHcard : Nat.card __ch5_Theorem523BaseNine_a7H = 3 := by
    rw [__ch5_Theorem523BaseNine_a7H, Nat.card_zpowers, a7X_order]
  have hKcard : Nat.card __ch5_Theorem523BaseNine_a7K = 3 := by
    rw [__ch5_Theorem523BaseNine_a7K, Nat.card_zpowers, a7Y_order]
  calc
    Nat.card a7StandardNine = Nat.card (__ch5_Theorem523BaseNine_a7H × __ch5_Theorem523BaseNine_a7K) := hcardRange
    _ = Nat.card __ch5_Theorem523BaseNine_a7H * Nat.card __ch5_Theorem523BaseNine_a7K := Nat.card_prod _ _
    _ = 9 := by rw [hHcard, hKcard]

public theorem a7_card :
    Nat.card a7StandardNine = 9 :=
  __ch5_Theorem523BaseNine_a7StandardNine_card_private

public theorem a7_explicit_card :
    Nat.card
      ((Subgroup.zpowers (alternatingSuzukiGenerator 2 (0 : Fin 5)) ⊔
          Subgroup.zpowers
            ((alternatingSuzukiGenerator 2 (3 : Fin 5))⁻¹ *
              (alternatingSuzukiGenerator 2 (2 : Fin 5))⁻¹)) :
        Subgroup (alternatingGroup (Fin 7))) = 9 := by
  change Nat.card a7StandardNine = 9
  exact a7_card

end GLS3.Chapter5.SchurPresentation.Theorem523BaseNine
/- END Theory.Theorem523BaseNine -/

/- BEGIN Theory.PerfectActionCommutatorStable -/
namespace GLS3.Chapter5

/-- For a perfect subgroup acting on a normal abelian subgroup, the generated
commutator subgroup is stable under taking commutators once more. -/
public theorem commutator_le_iterated_of_isPerfect
    {G : Type*} [Group G] (M I : Subgroup G)
    [M.Normal] [IsMulCommutative M] [Group.IsPerfect I] :
    ⁅M, I⁆ ≤ ⁅⁅M, I⁆, I⁆ := by
  let S : Subgroup G := M ⊔ I
  let Ms : Subgroup S := M.subgroupOf S
  let Is : Subgroup S := I.subgroupOf S
  let M1 : Subgroup S := ⁅Ms, Is⁆
  let N : Subgroup S := ⁅M1, Is⁆
  have hMsNormal : Ms.Normal := Subgroup.normal_subgroupOf
  let : Ms.Normal := hMsNormal
  have hM1leMs : M1 ≤ Ms := Subgroup.commutator_le_left Ms Is
  have hNleM1 : N ≤ M1 :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      (Subgroup.normalizer_commutator_ge_right Ms Is)
  have hNleMs : N ≤ Ms := hNleM1.trans hM1leMs
  have hMsCentralizesN : Ms ≤ Subgroup.centralizer N := by
    intro m hm
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have hcomm := isMulCommutative_iff.mp
      (inferInstance : IsMulCommutative Ms) ⟨m, hm⟩ ⟨n, hNleMs hn⟩
    exact (congrArg Subtype.val hcomm).symm
  have hMsNormalizerN : Ms ≤ Subgroup.normalizer (N : Set S) :=
    hMsCentralizesN.trans (Subgroup.centralizer_le_normalizer (N : Set S))
  have hIsNormalizerN : Is ≤ Subgroup.normalizer (N : Set S) :=
    Subgroup.normalizer_commutator_ge_right M1 Is
  have hMsSupIs : Ms ⊔ Is = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (show M ≤ S from le_sup_left)
      (show I ≤ S from le_sup_right)]
    exact Subgroup.subgroupOf_eq_top.mpr le_rfl
  have hnormalizerTop : Subgroup.normalizer (N : Set S) = ⊤ := by
    apply top_unique
    rw [← hMsSupIs]
    exact sup_le hMsNormalizerN hIsNormalizerN
  have : N.Normal := Subgroup.normalizer_eq_top_iff.mp hnormalizerTop
  let q : S →* S ⧸ N := QuotientGroup.mk' N
  let A : Subgroup (S ⧸ N) := Is.map q
  let B : Subgroup (S ⧸ N) := Ms.map q
  have hBAA : ⁅⁅B, A⁆, A⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator]
    exact (Subgroup.map_eq_bot_iff N).mpr (by
      rw [QuotientGroup.ker_mk'])
  have hABA : ⁅⁅A, B⁆, A⁆ = ⊥ := by
    simpa only [Subgroup.commutator_comm A B] using hBAA
  have hAAB : ⁅⁅A, A⁆, B⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate hABA hBAA
  have hIsPerfect : ⁅Is, Is⁆ = Is := by
    apply Subgroup.map_injective S.subtype_injective
    rw [Subgroup.map_commutator]
    simp only [Is, S, Subgroup.map_subgroupOf_eq_of_le le_sup_right]
    rw [← Subgroup.map_subtype_commutator I,
      (inferInstance : Group.IsPerfect I).commutator_eq_top]
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hAperfect : ⁅A, A⁆ = A := by
    rw [← Subgroup.map_commutator, hIsPerfect]
  have hAB : ⁅A, B⁆ = ⊥ := by simpa [hAperfect] using hAAB
  have hM1map : M1.map q = ⊥ := by
    rw [Subgroup.map_commutator]
    simpa [A, B, Subgroup.commutator_comm B A] using hAB
  have hM1leN : M1 ≤ N := by
    rw [← QuotientGroup.ker_mk' N, ← Subgroup.map_eq_bot_iff]
    exact hM1map
  have hmapped := Subgroup.map_mono (f := S.subtype) hM1leN
  simpa [M1, N, Ms, Is, S, Subgroup.map_commutator,
    Subgroup.map_subgroupOf_eq_of_le] using hmapped

end GLS3.Chapter5
/- END Theory.PerfectActionCommutatorStable -/

/- BEGIN Theory.CentralVectorQuotientFactor -/
noncomputable section

namespace GLS3.Chapter5

/-- A finite `2`-group with an elementary-abelian quotient by a central
subgroup `Z` admits a factor `R₁` complementary to its center modulo `Z`;
that factor is extraspecial or is exactly `Z`. -/
public theorem exists_central_vector_quotient_factor
    {P V : Type*} [Group P] [Finite P]
    [AddCommGroup V] [Module (ZMod 2) V]
    (hP : IsPGroup 2 P) (q : P →* Multiplicative V)
    (Z : Subgroup P) (hker : q.ker = Z)
    (hZcenter : Z ≤ Subgroup.center P) (hZcard : Nat.card Z = 2) :
    ∃ R1 : Subgroup P,
      Subgroup.center P ⊔ R1 = ⊤ ∧
      Subgroup.center P ⊓ R1 = Z ∧
      (IsExtraspecialTwoSubgroup R1 ∨ R1 = Z) := by
  obtain ⟨R1, hsup, hinfKer⟩ :=
    exists_sup_eq_top_inf_eq_ker_of_vector_quotient q (Subgroup.center P)
      (hker ▸ hZcenter)
  have hinf : Subgroup.center P ⊓ R1 = Z := hinfKer.trans hker
  refine ⟨R1, hsup, hinf, ?_⟩
  have hZR : Z ≤ R1 := by
    rw [← hinf]
    exact inf_le_right
  have hcenterR1 : Subgroup.center R1 = Z.subgroupOf R1 :=
    center_eq_subgroupOf_of_center_sup_eq_top
      (Subgroup.center P) R1 Z rfl hsup hinf
  have hcenterR1Card : Nat.card (Subgroup.center R1) = 2 := by
    rw [hcenterR1]
    calc
      Nat.card (Z.subgroupOf R1) = Nat.card Z :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZR).toEquiv
      _ = 2 := hZcard
  let qR : R1 →* Multiplicative V := q.comp R1.subtype
  have hqRker : qR.ker = Subgroup.center R1 := by
    rw [hcenterR1]
    ext z
    change q z.1 = 1 ↔ z.1 ∈ Z
    rw [← hker]
    exact MonoidHom.mem_ker.symm
  rcases isExtraspecialTwoSubgroup_or_center_eq_top_of_vector_hom
      R1 (hP.to_subgroup R1) hcenterR1Card qR hqRker with hExtra | hCenter
  · exact Or.inl hExtra
  · right
    apply le_antisymm
    · exact Subgroup.subgroupOf_eq_top.mp (hcenterR1 ▸ hCenter)
    · exact hZR

end GLS3.Chapter5
/- END Theory.CentralVectorQuotientFactor -/

/- BEGIN Theory.InvolutionEvenCycleRotationsTraceZero -/
noncomputable section

open scoped BigOperators

namespace GLS3.Chapter5
universe __ch5_InvolutionEvenCycleRotationsTraceZero_u

public theorem minusOne_zmodTwo_pow_eq_one_iff (z : ZMod 2) :
    (-1 : ℤˣ) ^ z = 1 ↔ z = 0 := by
  have hzlt : z.val < 2 := ZMod.val_lt z
  have hz01 : z.val = 0 ∨ z.val = 1 := by omega
  rcases hz01 with hz | hz
  · have : z = 0 := by
      apply ZMod.val_injective 2
      simpa using hz
    subst z
    simp
  · have : z = 1 := by
      apply ZMod.val_injective 2
      rw [ZMod.val_one]
      exact hz
    subst z
    norm_num

/-- The subgroup of independent cycle rotations inducing even permutations. -/
public def evenInvolutionCycleRotations
    {Ω : Type __ch5_InvolutionEvenCycleRotationsTraceZero_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) : Subgroup (CycleRotationGroup x) :=
  (Equiv.Perm.sign.comp
    ((Subgroup.subtype (Subgroup.centralizer ({x} : Set (Equiv.Perm Ω)))).comp
      (cycleRotationToCentralizer x))).ker
@[simp]
public theorem mem_evenInvolutionCycleRotations
    {Ω : Type __ch5_InvolutionEvenCycleRotationsTraceZero_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (a : CycleRotationGroup x) :
    a ∈ evenInvolutionCycleRotations x ↔
      Equiv.Perm.sign ((cycleRotationToCentralizer x a).1) = 1 := Iff.rfl


@[expose]
public def traceZeroReindexZModTwoAddEquiv {I : Type*} [Fintype I]
    (r : Nat) (e : I ≃ Fin r) :
    (I → ZMod 2) ≃+ (Fin r → ZMod 2) where
  toFun f i := f (e.symm i)
  invFun f i := f (e i)
  left_inv f := by ext i; simp
  right_inv f := by ext i; simp
  map_add' _ _ := rfl

@[expose]
public def reindexedInvolutionCycleRotationCoordinates
    {Ω : Type __ch5_InvolutionEvenCycleRotationsTraceZero_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2) (r : Nat)
    (e : x.cycleFactorsFinset ≃ Fin r) :
    CycleRotationGroup x ≃* Multiplicative (Fin r → ZMod 2) :=
  (involutionCycleRotationCoordinates x hx).trans
    ((MulEquiv.piMultiplicative fun _ : x.cycleFactorsFinset => ZMod 2).symm.trans
      (AddEquiv.toMultiplicative (traceZeroReindexZModTwoAddEquiv r e)))

/-- After numbering the nontrivial cycles of an involution by `Fin r`, its
even independent rotations are the multiplicative form of the trace-zero
subgroup of the natural `ZMod 2` permutation module. -/
@[expose]
public noncomputable def evenInvolutionCycleRotations_mulEquiv_traceZero
    {Ω : Type __ch5_InvolutionEvenCycleRotationsTraceZero_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2) (r : Nat)
    (e : x.cycleFactorsFinset ≃ Fin r) :
    evenInvolutionCycleRotations x ≃*
      Multiplicative ↥(traceZeroTwoSubgroup r) := by
  let E := reindexedInvolutionCycleRotationCoordinates x hx r e
  have hmem (a : CycleRotationGroup x) :
      a ∈ evenInvolutionCycleRotations x ↔
        Multiplicative.toAdd (E a) ∈ traceZeroTwoSubgroup r := by
    rw [show a ∈ evenInvolutionCycleRotations x ↔
        Equiv.Perm.sign ((cycleRotationToCentralizer x a).1) = 1 by rfl]
    rw [involutionCycleRotation_sign x hx a,
      minusOne_zmodTwo_pow_eq_one_iff]
    rw [mem_traceZeroTwoSubgroup]
    rw [show (∑ i, (Multiplicative.toAdd (E a)) i) =
        ∑ c, Multiplicative.toAdd
          ((involutionCycleRotationCoordinates x hx) a c) by
      exact e.symm.sum_comp fun c =>
        Multiplicative.toAdd ((involutionCycleRotationCoordinates x hx) a c)]
  exact {
    toFun := fun a => Multiplicative.ofAdd
      ⟨Multiplicative.toAdd (E a.1), (hmem a.1).mp a.2⟩
    invFun := fun v =>
      ⟨E.symm (Multiplicative.ofAdd (Multiplicative.toAdd v).1),
        (hmem _).mpr (by
          simp)⟩
    left_inv := by
      intro a
      apply Subtype.ext
      exact E.symm_apply_apply a.1
    right_inv := by
      intro v
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd
        (E.apply_symm_apply (Multiplicative.ofAdd (Multiplicative.toAdd v).1))
    map_mul' := by
      intro a b
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      simp
  }

@[simp]
public theorem evenInvolutionCycleRotations_mulEquiv_traceZero_apply
    {Ω : Type __ch5_InvolutionEvenCycleRotationsTraceZero_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2) (r : Nat)
    (e : x.cycleFactorsFinset ≃ Fin r)
    (a : evenInvolutionCycleRotations x) (i : Fin r) :
    (Multiplicative.toAdd
      (evenInvolutionCycleRotations_mulEquiv_traceZero x hx r e a)).1 i =
      Multiplicative.toAdd
        ((involutionCycleRotationCoordinates x hx) a.1 (e.symm i)) := rfl

end GLS3.Chapter5
/- END Theory.InvolutionEvenCycleRotationsTraceZero -/

/- BEGIN Theory.InvolutionRotationDisjointComplement -/
noncomputable section
namespace GLS3.Chapter5
universe __ch5_InvolutionRotationDisjointComplement_u

/-- An involution-cycle rotation and its complementary rotation inside the
original involution have disjoint supports. -/
public theorem involutionRotation_disjoint_complement
    {Ω : Type __ch5_InvolutionRotationDisjointComplement_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2)
    (a : CycleRotationGroup x) :
    Equiv.Perm.Disjoint (cycleRotationToCentralizer x a).1
      (x * (cycleRotationToCentralizer x a).1) := by
  rw [Equiv.Perm.disjoint_iff_eq_or_eq]
  intro ω
  by_cases hω : x ω = ω
  · left
    let fixed : Function.fixedPoints x := ⟨ω, hω⟩
    exact cycleRotationToCentralizer_apply_fixed x a fixed
  · have hωsupp : ω ∈ x.support := Equiv.Perm.mem_support.mpr hω
    have hc : x.cycleOf ω ∈ x.cycleFactorsFinset :=
      Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hωsupp
    let c : x.cycleFactorsFinset := ⟨x.cycleOf ω, hc⟩
    have hωc : ω ∈ c.1.support := by
      change ω ∈ (x.cycleOf ω).support
      rw [Equiv.Perm.mem_support, Equiv.Perm.cycleOf_apply_self]
      exact hω
    let hp : (orderOf x).Prime := by simpa [hx] using Nat.prime_two
    obtain ⟨n, hn⟩ := (cycleCoordinateEquiv x hp c).surjective ⟨ω, hωc⟩
    let ec : Multiplicative (ZMod 2) ≃* Subgroup.zpowers c.1 :=
      zmodMulEquivOfGenerator (cycleFactorGenerator_generates c)
        (by simpa [hx] using cycleFactorZPowers_card_of_primeOrder x hp c)
    let z : ZMod 2 := Multiplicative.toAdd (ec.symm (a c))
    have hac : a c = ec (Multiplicative.ofAdd z) := (ec.apply_symm_apply (a c)).symm
    have hzlt : z.val < 2 := ZMod.val_lt z
    have hz01 : z.val = 0 ∨ z.val = 1 := by omega
    rcases hz01 with hz0 | hz1
    · left
      have hz : z = 0 := by
        apply ZMod.val_injective 2
        simpa using hz0
      have ha1 : a c = 1 := by simp [hac, hz]
      have happ := cycleRotationToCentralizer_apply_cycleCoordinate x hp a c n
      rw [congrArg Subtype.val hn] at happ
      change (cycleRotationToCentralizer x a).1 ω = (a c).1 ω at happ
      simpa [ha1] using happ
    · right
      have hz : z = 1 := by
        apply ZMod.val_injective 2
        rw [ZMod.val_one]
        exact hz1
      have hagen : a c = cycleFactorGenerator c := by
        rw [hac, hz]
        simp [ec]
      have happ := cycleRotationToCentralizer_apply_cycleCoordinate x hp a c n
      rw [congrArg Subtype.val hn] at happ
      change (cycleRotationToCentralizer x a).1 ω = (a c).1 ω at happ
      change (x * (cycleRotationToCentralizer x a).1) ω = ω
      rw [Equiv.Perm.mul_apply, happ, hagen]
      change x (c.1 ω) = ω
      change x ((x.cycleOf ω) ω) = ω
      rw [Equiv.Perm.cycleOf_apply_self]
      have hx2 : x ^ 2 = 1 := by
        rw [← orderOf_dvd_iff_pow_eq_one, hx]
      have := DFunLike.congr_fun hx2 ω
      simpa [pow_two, Equiv.Perm.mul_apply] using this

end GLS3.Chapter5
/- END Theory.InvolutionRotationDisjointComplement -/

/- BEGIN Theory.InvolutionTwoCycleRotationEven -/
noncomputable section

open scoped BigOperators

namespace GLS3.Chapter5
universe __ch5_InvolutionTwoCycleRotationEven_u

/-- The rotation on two selected involution cycles is even. -/
public theorem involutionTwoCycleRotation_sign
    {Ω : Type __ch5_InvolutionTwoCycleRotationEven_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2)
    (c d : x.cycleFactorsFinset) (hcd : c ≠ d) :
    let v : x.cycleFactorsFinset → Multiplicative (ZMod 2) :=
      fun k => if k = c ∨ k = d then Multiplicative.ofAdd 1 else 1
    let a := (involutionCycleRotationCoordinates x hx).symm v
    Equiv.Perm.sign ((cycleRotationToCentralizer x a).1) = 1 := by
  dsimp only
  let E := involutionCycleRotationCoordinates x hx
  let v : x.cycleFactorsFinset → Multiplicative (ZMod 2) :=
    fun k => if k = c ∨ k = d then Multiplicative.ofAdd 1 else 1
  let a := E.symm v
  have haCoord : E a = v := E.apply_symm_apply v
  rw [involutionCycleRotation_sign x hx a]
  rw [show (∑ k, Multiplicative.toAdd (E a k)) = 0 by
    rw [haCoord]
    rw [Fintype.sum_eq_add c d hcd]
    · simp [v, hcd]
      change (0 : ZMod 2) = 0
      rfl
    · intro k hk
      simp [v, hk.1, hk.2]]
  simp

end GLS3.Chapter5
/- END Theory.InvolutionTwoCycleRotationEven -/

/- BEGIN Theory.InvolutionTwoCycleRotationProduct -/
noncomputable section
namespace GLS3.Chapter5
universe __ch5_InvolutionTwoCycleRotationProduct_u

/-- Two root rotations sharing one cycle multiply to the root rotation on the
other two cycles. -/
public theorem involutionTwoCycleRotation_mul
    {Ω : Type __ch5_InvolutionTwoCycleRotationProduct_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2)
    (i j k : x.cycleFactorsFinset)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    let E := involutionCycleRotationCoordinates x hx
    let vij : x.cycleFactorsFinset → Multiplicative (ZMod 2) :=
      fun q => if q = i ∨ q = j then Multiplicative.ofAdd 1 else 1
    let vik : x.cycleFactorsFinset → Multiplicative (ZMod 2) :=
      fun q => if q = i ∨ q = k then Multiplicative.ofAdd 1 else 1
    let vjk : x.cycleFactorsFinset → Multiplicative (ZMod 2) :=
      fun q => if q = j ∨ q = k then Multiplicative.ofAdd 1 else 1
    E.symm vij * E.symm vik = E.symm vjk := by
  dsimp only
  let E := involutionCycleRotationCoordinates x hx
  apply E.injective
  rw [map_mul, E.apply_symm_apply, E.apply_symm_apply, E.apply_symm_apply]
  funext q
  by_cases hqi : q = i
  · subst q
    apply Multiplicative.toAdd.injective
    simp [hij, hik]
    exact ZMod.natCast_self 2
  by_cases hqj : q = j
  · subst q
    have hji : j ≠ i := hij.symm
    simp [hji, hjk]
  by_cases hqk : q = k
  · subst q
    have hki : k ≠ i := hik.symm
    have hkj : k ≠ j := hjk.symm
    simp [hki, hkj]
  · simp [hqi, hqj, hqk]

end GLS3.Chapter5
/- END Theory.InvolutionTwoCycleRotationProduct -/

/- BEGIN Theory.InvolutionTwoCycleRotationSupport -/
noncomputable section
open scoped BigOperators
namespace GLS3.Chapter5
universe __ch5_InvolutionTwoCycleRotationSupport_u

public theorem involutionTwoCycleRotation_support_card
    {Ω : Type __ch5_InvolutionTwoCycleRotationSupport_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2)
    (c d : x.cycleFactorsFinset) (hcd : c ≠ d) :
    let v : x.cycleFactorsFinset → Multiplicative (ZMod 2) :=
      fun k => if k = c ∨ k = d then Multiplicative.ofAdd 1 else 1
    let a := (involutionCycleRotationCoordinates x hx).symm v
    ((cycleRotationToCentralizer x a).1).support.card = 4 := by
  dsimp only
  let hp : (orderOf x).Prime := by simpa [hx] using Nat.prime_two
  let E := involutionCycleRotationCoordinates x hx
  let v : x.cycleFactorsFinset → Multiplicative (ZMod 2) :=
    fun k => if k = c ∨ k = d then Multiplicative.ofAdd 1 else 1
  let a := E.symm v
  let ρ := (cycleRotationToCentralizer x a).1
  have haCoord : E a = v := E.apply_symm_apply v
  have ha2 : a ^ 2 = 1 := by
    simpa [hx] using cycleRotationGroup_pow_orderOf_eq_one_of_primeOrder x hp a
  have hρ2 : ρ ^ 2 = 1 := by
    change (cycleRotationToCentralizer x a).1 ^ 2 = 1
    rw [cycleRotationToCentralizer_pow_coe x a 2, ha2, map_one]
    rfl
  have haNe : a ≠ 1 := by
    intro ha
    rw [ha, map_one] at haCoord
    have hcCoord := congrFun haCoord c
    simp [v] at hcCoord
    have := congrArg Multiplicative.toAdd hcCoord
    norm_num at this
  have hρNe : ρ ≠ 1 := by
    intro hρ
    apply haNe
    apply cycleRotationToCentralizer_injective x
    apply Subtype.ext
    simpa [ρ] using hρ
  have hρsign : Equiv.Perm.sign ρ = 1 := by
    change Equiv.Perm.sign ((cycleRotationToCentralizer x a).1) = 1
    rw [involutionCycleRotation_sign x hx a]
    rw [show (∑ k, Multiplicative.toAdd (E a k)) = 0 by
      rw [haCoord]
      rw [Fintype.sum_eq_add c d hcd]
      · simp [v, hcd]
        change (0 : ZMod 2) = 0
        rfl
      · intro k hk
        simp [v, hk.1, hk.2]]
    simp
  let ρA : alternatingGroup Ω := ⟨ρ, Equiv.Perm.mem_alternatingGroup.mpr hρsign⟩
  have hρALe : ρA.1.support.card ≤ 4 := by
    have hsupp : ρ.support ⊆ c.1.support ∪ d.1.support := by
      intro ω hω
      rw [Finset.mem_union]
      by_contra hout
      have hout := not_or.mp hout
      rw [Equiv.Perm.mem_support] at hω
      apply hω
      obtain ⟨q, rfl⟩ := (primeCycleCoordinates x hp).surjective ω
      cases q with
      | inl fixed =>
          exact cycleRotationToCentralizer_apply_fixed x a fixed
      | inr cycle =>
          rcases cycle with ⟨k, n⟩
          have hkc : k ≠ c := by
            intro h
            subst k
            exact hout.1 (cycleCoordinateEquiv x hp c n).2
          have hkd : k ≠ d := by
            intro h
            subst k
            exact hout.2 (cycleCoordinateEquiv x hp d n).2
          have hkCoord : (involutionCycleRotationCoordinates x hx) a k = 1 := by
            rw [show (involutionCycleRotationCoordinates x hx) a = v by simpa [E] using haCoord]
            simp [v, hkc, hkd]
          have hak : a k = 1 := by
            rw [involutionCycleRotationCoordinates_apply] at hkCoord
            apply ((zmodMulEquivOfGenerator (cycleFactorGenerator_generates k)
              (by simpa [hx] using
                (cycleFactorZPowers_card_of_primeOrder x hp k))).symm).injective
            simpa using hkCoord
          change (cycleRotationToCentralizer x a).1
            (cycleCoordinateEquiv x hp k n).1 = (cycleCoordinateEquiv x hp k n).1
          rw [cycleRotationToCentralizer_apply_cycleCoordinate x hp a k n, hak]
          rfl
    calc
      ρA.1.support.card = ρ.support.card := rfl
      _ ≤ (c.1.support ∪ d.1.support).card := Finset.card_le_card hsupp
      _ = c.1.support.card + d.1.support.card := by
        apply Finset.card_union_of_disjoint
        exact Equiv.Perm.disjoint_iff_disjoint_support.mp
          (Equiv.Perm.cycleFactorsFinset_pairwise_disjoint x c.2 d.2 (by
            intro h
            exact hcd (Subtype.ext h)))
      _ = 4 := by
        rw [cycleFactor_support_card_eq_orderOf_of_primeOrder x hp c,
          cycleFactor_support_card_eq_orderOf_of_primeOrder x hp d, hx]
  have hρA2 : ρA.1 ^ 2 = 1 := hρ2
  have hρANe : ρA ≠ 1 := by
    intro h
    apply hρNe
    exact congrArg Subtype.val h
  exact evenInvolution_support_card_eq_four_of_le ρA hρA2 hρANe hρALe

end GLS3.Chapter5
/- END Theory.InvolutionTwoCycleRotationSupport -/

/- BEGIN Theory.InvolutionTwoCycleRotationSupportLe -/
noncomputable section
namespace GLS3.Chapter5
universe __ch5_InvolutionTwoCycleRotationSupportLe_u

/-- The rotation nontrivial on two selected involution cycles is supported on their union. -/
public theorem involutionTwoCycleRotation_support_le_union
    {Ω : Type __ch5_InvolutionTwoCycleRotationSupportLe_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2)
    (c d : x.cycleFactorsFinset) :
    let v : x.cycleFactorsFinset → Multiplicative (ZMod 2) :=
      fun k => if k = c ∨ k = d then Multiplicative.ofAdd 1 else 1
    let a := (involutionCycleRotationCoordinates x hx).symm v
    ((cycleRotationToCentralizer x a).1).support ⊆ c.1.support ∪ d.1.support := by
  dsimp only
  let hp : (orderOf x).Prime := by simpa [hx] using Nat.prime_two
  let E := involutionCycleRotationCoordinates x hx
  let v : x.cycleFactorsFinset → Multiplicative (ZMod 2) :=
    fun k => if k = c ∨ k = d then Multiplicative.ofAdd 1 else 1
  let a := E.symm v
  have haCoord : E a = v := E.apply_symm_apply v
  intro ω hω
  rw [Finset.mem_union]
  by_contra hout
  have hout := not_or.mp hout
  rw [Equiv.Perm.mem_support] at hω
  apply hω
  obtain ⟨q, rfl⟩ := (primeCycleCoordinates x hp).surjective ω
  cases q with
  | inl fixed =>
      exact cycleRotationToCentralizer_apply_fixed x a fixed
  | inr cycle =>
      rcases cycle with ⟨k, n⟩
      have hkc : k ≠ c := by
        intro h
        subst k
        exact hout.1 (cycleCoordinateEquiv x hp c n).2
      have hkd : k ≠ d := by
        intro h
        subst k
        exact hout.2 (cycleCoordinateEquiv x hp d n).2
      have hkCoord : (involutionCycleRotationCoordinates x hx) a k = 1 := by
        rw [show (involutionCycleRotationCoordinates x hx) a = v by
          simpa [E] using haCoord]
        simp [v, hkc, hkd]
      have hak : a k = 1 := by
        rw [involutionCycleRotationCoordinates_apply] at hkCoord
        apply ((zmodMulEquivOfGenerator (cycleFactorGenerator_generates k)
          (by simpa [hx] using
            (cycleFactorZPowers_card_of_primeOrder x hp k))).symm).injective
        simpa using hkCoord
      change (cycleRotationToCentralizer x a).1
        (cycleCoordinateEquiv x hp k n).1 = (cycleCoordinateEquiv x hp k n).1
      rw [cycleRotationToCentralizer_apply_cycleCoordinate x hp a k n, hak]
      rfl

end GLS3.Chapter5
/- END Theory.InvolutionTwoCycleRotationSupportLe -/

/- BEGIN Theory.CoveringClassification -/
namespace GLS3.Chapter5.Covering
universe __ch5_CoveringClassification_u __ch5_CoveringClassification_v __ch5_CoveringClassification_w

/-! ## Covering classification over a universal cover (Theorem 5.2.3)

Given a universal covering `f₀ : L₀ → G` ([A1, 33.1–33.15]), every covering
`g : M → G` has kernel the image of the kernel of `f₀` under the unique
universal lift `L₀ → M`.  Consequently, when `ker f₀` has cardinality `2`
(i.e. `M(G) ≅ C₂`), every covering kernel has size `1` or `2`, any two
double covers are uniquely isomorphic over the base, and every double cover
is universal.  This is the classification backbone for the remaining clauses
of Theorem 5.2.3: the *computation* `M(A_n) = C₂` (resp. `C₆` for
`n = 6, 7`) is supplied separately ([Su1, (2.22)], `refs/KGroup/GLS3/Ch5Su1.tex`).

Sources: [A1, 33.1] uniqueness of the universal extension; [A1, 33.13]
kernel transfer; [Su1, Ch. 2 §9] the covering-classification principle.
-/

section Basic

/-- Cardinality via the fibration over a surjective homomorphism:
`|A| = |B| · |ker f|`. -/
private theorem __ch5_CoveringClassification_card_eq_mul_ker {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hsurj : Function.Surjective f) : Nat.card A = Nat.card B * Nat.card ↥f.ker := by
  calc
    Nat.card A = Nat.card (↥(⊤ : Subgroup A)) :=
      Nat.card_congr (Subgroup.topEquiv.symm).toEquiv
    _ = Nat.card (↥((⊤ : Subgroup B).comap f)) := by rw [Subgroup.comap_top]
    _ = Nat.card (↥(⊤ : Subgroup B)) * Nat.card ↥f.ker :=
      GLS3.Chapter5.SchurPresentation.card_comap_mul f hsurj ⊤
    _ = Nat.card B * Nat.card ↥f.ker := by
      rw [Nat.card_congr (Subgroup.topEquiv.toEquiv)]

end Basic

section KernelTransfer

variable {L₀ : Type __ch5_CoveringClassification_u} {G : Type __ch5_CoveringClassification_v} {M : Type __ch5_CoveringClassification_w}
variable [Group L₀] [Finite L₀] [IsQuasisimple L₀]
variable [Group G] [Finite G] [IsQuasisimple G]
variable [Group M] [Finite M] [IsQuasisimple M]

/-- The unique universal lift `L₀ → M` maps the kernel of `f₀` onto the
kernel of `g` (a covering of `G`): every covering kernel is the image of the
Schur multiplier.  ([A1, 33.13] direction, `Covering`-API form.) -/
public theorem coveringKernel_image_of_universal (f₀ : Covering L₀ G)
    (hf₀ : IsUniversal.{__ch5_CoveringClassification_v, __ch5_CoveringClassification_u, __ch5_CoveringClassification_w} f₀) (g : Covering M G) :
    Subgroup.map (IsUniversal.lift hf₀ g).toMonoidHom f₀.toMonoidHom.ker = g.toMonoidHom.ker := by
  apply le_antisymm
  · intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
    rw [MonoidHom.mem_ker]
    change g ((IsUniversal.lift hf₀ g) x) = 1
    have hfac (z : L₀) : g ((IsUniversal.lift hf₀ g) z) = f₀ z := by
      simpa using (DFunLike.congr_fun (IsUniversal.lift_fac hf₀ g) z)
    rw [hfac x]
    exact MonoidHom.mem_ker.mp hx
  · intro y hy
    rw [MonoidHom.mem_ker] at hy
    obtain ⟨x, hx⟩ := (IsUniversal.lift hf₀ g).surjective y
    rw [Subgroup.mem_map]
    refine ⟨x, ?_, hx⟩
    rw [MonoidHom.mem_ker]
    change f₀ x = 1
    have hback (z : L₀) : f₀ z = g ((IsUniversal.lift hf₀ g) z) := by
      simpa using (DFunLike.congr_fun (IsUniversal.lift_fac hf₀ g) z).symm
    calc
      f₀ x = g ((IsUniversal.lift hf₀ g) x) := hback x
      _ = g y := congrArg g hx
      _ = 1 := hy

/-- Covering kernels never exceed the Schur multiplier in size. -/
public theorem coveringKernel_card_le_of_universal (f₀ : Covering L₀ G)
    (hf₀ : IsUniversal.{__ch5_CoveringClassification_v, __ch5_CoveringClassification_u, __ch5_CoveringClassification_w} f₀) (g : Covering M G) :
    Nat.card ↥g.toMonoidHom.ker ≤ Nat.card ↥f₀.toMonoidHom.ker := by
  let φ : ↥f₀.toMonoidHom.ker →* ↥g.toMonoidHom.ker :=
    ((IsUniversal.lift hf₀ g).toMonoidHom.comp f₀.toMonoidHom.ker.subtype).codRestrict
      g.toMonoidHom.ker (by
        intro x
        rw [MonoidHom.mem_ker]
        change g ((IsUniversal.lift hf₀ g) x.1) = 1
        have hfac (z : L₀) : g ((IsUniversal.lift hf₀ g) z) = f₀ z := by
          simpa using (DFunLike.congr_fun (IsUniversal.lift_fac hf₀ g) z)
        rw [hfac x.1]
        exact MonoidHom.mem_ker.mp x.2)
  have hsurj : Function.Surjective φ := by
    intro y
    have hmem : y.1 ∈ Subgroup.map (IsUniversal.lift hf₀ g).toMonoidHom f₀.toMonoidHom.ker := by
      rw [coveringKernel_image_of_universal f₀ hf₀ g]
      exact y.2
    rcases Subgroup.mem_map.mp hmem with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    change (IsUniversal.lift hf₀ g).toMonoidHom x = y.1
    exact hxy
  have : Fintype ↥f₀.toMonoidHom.ker := Fintype.ofFinite _
  have : Fintype ↥g.toMonoidHom.ker := Fintype.ofFinite _
  have hf : Fintype.card ↥g.toMonoidHom.ker ≤ Fintype.card ↥f₀.toMonoidHom.ker :=
    Fintype.card_le_of_surjective φ hsurj
  rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]

/-- If the Schur multiplier has size two, every covering kernel has size one
or two. -/
public theorem coveringKernel_card_eq_one_or_two (f₀ : Covering L₀ G)
    (hf₀ : IsUniversal.{__ch5_CoveringClassification_v, __ch5_CoveringClassification_u, __ch5_CoveringClassification_w} f₀) (hfK : Nat.card ↥f₀.toMonoidHom.ker = 2)
    (g : Covering M G) :
    Nat.card ↥g.toMonoidHom.ker = 1 ∨ Nat.card ↥g.toMonoidHom.ker = 2 := by
  have hle : Nat.card ↥g.toMonoidHom.ker ≤ 2 := by
    rw [← hfK]
    exact coveringKernel_card_le_of_universal f₀ hf₀ g
  have : Nonempty ↥g.toMonoidHom.ker := ⟨1⟩
  have hp : 0 < Nat.card ↥g.toMonoidHom.ker := Nat.card_pos
  omega

end KernelTransfer

section DoubleCover

variable {L₀ : Type __ch5_CoveringClassification_u} {G : Type __ch5_CoveringClassification_u}
variable [Group L₀] [Finite L₀] [IsQuasisimple L₀]
variable [Group G] [Finite G] [IsQuasisimple G]

/-- Two coverings of the same group are uniquely isomorphic over the base when
their universal lifts have the same kernel.  This is the quotient-level form
needed for a cyclic Schur multiplier: equal subgroups of the universal kernel
give the same covering quotient. -/
public theorem coveringIso_of_liftKernel_eq
    (f₀ : Covering L₀ G)
    (hf₁ : IsUniversal.{__ch5_CoveringClassification_u, __ch5_CoveringClassification_u, __ch5_CoveringClassification_v} f₀)
    (hf₂ : IsUniversal.{__ch5_CoveringClassification_u, __ch5_CoveringClassification_u, __ch5_CoveringClassification_w} f₀)
    {G₁ : Type __ch5_CoveringClassification_v} {G₂ : Type __ch5_CoveringClassification_w}
    [Group G₁] [Finite G₁] [IsQuasisimple G₁]
    [Group G₂] [Finite G₂] [IsQuasisimple G₂]
    (g₁ : Covering G₁ G) (g₂ : Covering G₂ G)
    (hker : (IsUniversal.lift hf₁ g₁).toMonoidHom.ker =
      (IsUniversal.lift hf₂ g₂).toMonoidHom.ker) :
    ∃! e : G₁ ≃* G₂, g₂.comp (Covering.ofMulEquiv e) = g₁ := by
  let h₁ : Covering L₀ G₁ := IsUniversal.lift hf₁ g₁
  let h₂ : Covering L₀ G₂ := IsUniversal.lift hf₂ g₂
  have hfac₁ : g₁.comp h₁ = f₀ := IsUniversal.lift_fac hf₁ g₁
  have hfac₂ : g₂.comp h₂ = f₀ := IsUniversal.lift_fac hf₂ g₂
  have hker' : h₁.toMonoidHom.ker = h₂.toMonoidHom.ker := by
    simpa [h₁, h₂] using hker
  let q₁ : L₀ ⧸ h₁.toMonoidHom.ker ≃* G₁ :=
    QuotientGroup.quotientKerEquivOfSurjective h₁.toMonoidHom h₁.surjective
  let q₂ : L₀ ⧸ h₂.toMonoidHom.ker ≃* G₂ :=
    QuotientGroup.quotientKerEquivOfSurjective h₂.toMonoidHom h₂.surjective
  let qeq : L₀ ⧸ h₁.toMonoidHom.ker ≃* L₀ ⧸ h₂.toMonoidHom.ker :=
    QuotientGroup.quotientMulEquivOfEq hker'
  let e : G₁ ≃* G₂ := q₁.symm.trans (qeq.trans q₂)
  have he_lift (x : L₀) : e (h₁ x) = h₂ x := by
    have hq₁ : q₁.symm (h₁ x) = QuotientGroup.mk x := by
      apply q₁.injective
      rw [q₁.apply_symm_apply]
      rfl
    calc
      e (h₁ x) = q₂ (qeq (q₁.symm (h₁ x))) := rfl
      _ = q₂ (qeq (QuotientGroup.mk x)) := by rw [hq₁]
      _ = q₂ (QuotientGroup.mk x) := by
        rw [QuotientGroup.quotientMulEquivOfEq_mk]
      _ = h₂ x := rfl
  refine ⟨e, ?_, ?_⟩
  · ext y
    obtain ⟨x, rfl⟩ := h₁.surjective y
    change g₂ (e (h₁ x)) = g₁ (h₁ x)
    rw [he_lift]
    have hfac₁pt : g₁ (h₁ x) = f₀ x := by
      simpa using DFunLike.congr_fun hfac₁ x
    have hfac₂pt : g₂ (h₂ x) = f₀ x := by
      simpa using DFunLike.congr_fun hfac₂ x
    exact hfac₂pt.trans hfac₁pt.symm
  · intro e' he'
    have hleft : g₂.comp ((Covering.ofMulEquiv e').comp h₁) = f₀ := by
      calc
        g₂.comp ((Covering.ofMulEquiv e').comp h₁) =
            (g₂.comp (Covering.ofMulEquiv e')).comp h₁ :=
          (Covering.comp_assoc g₂ (Covering.ofMulEquiv e') h₁).symm
        _ = g₁.comp h₁ := by rw [he']
        _ = f₀ := hfac₁
    have huniq : (Covering.ofMulEquiv e').comp h₁ = h₂ :=
      IsUniversal.hom_ext hf₂ g₂ hleft hfac₂
    have he'_lift (x : L₀) : e' (h₁ x) = h₂ x := by
      simpa using DFunLike.congr_fun huniq x
    ext y
    obtain ⟨x, rfl⟩ := h₁.surjective y
    exact (he'_lift x).trans (he_lift x).symm

/-- Two double covers of the same group are uniquely isomorphic over the base
(when a universal cover with kernel of order two exists). -/
public theorem coveringIso_of_card_two
    (f₀ : Covering L₀ G)
    (hf₁ : IsUniversal.{__ch5_CoveringClassification_u, __ch5_CoveringClassification_u, __ch5_CoveringClassification_v} f₀)
    (hf₂ : IsUniversal.{__ch5_CoveringClassification_u, __ch5_CoveringClassification_u, __ch5_CoveringClassification_w} f₀)
    (hfK : Nat.card ↥f₀.toMonoidHom.ker = 2)
    {G₁ : Type __ch5_CoveringClassification_v} {G₂ : Type __ch5_CoveringClassification_w}
    [Group G₁] [Finite G₁] [IsQuasisimple G₁]
    [Group G₂] [Finite G₂] [IsQuasisimple G₂]
    (g₁ : Covering G₁ G) (g₂ : Covering G₂ G)
    (hk₁ : Nat.card ↥g₁.toMonoidHom.ker = 2) (hk₂ : Nat.card ↥g₂.toMonoidHom.ker = 2) :
    ∃! e : G₁ ≃* G₂, g₂.comp (Covering.ofMulEquiv e) = g₁ := by
  let h₁ : Covering L₀ G₁ := IsUniversal.lift hf₁ g₁
  let h₂ : Covering L₀ G₂ := IsUniversal.lift hf₂ g₂
  have hfac₁ : g₁.comp h₁ = f₀ := IsUniversal.lift_fac hf₁ g₁
  have hfac₂ : g₂.comp h₂ = f₀ := IsUniversal.lift_fac hf₂ g₂
  have hcard₁ : Nat.card L₀ = Nat.card G₁ := by
    calc
      Nat.card L₀ = Nat.card G * 2 := by
        rw [__ch5_CoveringClassification_card_eq_mul_ker f₀.toMonoidHom f₀.surjective, hfK]
      _ = Nat.card G₁ := by
        rw [__ch5_CoveringClassification_card_eq_mul_ker g₁.toMonoidHom g₁.surjective, hk₁]
  have hcard₂ : Nat.card L₀ = Nat.card G₂ := by
    calc
      Nat.card L₀ = Nat.card G * 2 := by
        rw [__ch5_CoveringClassification_card_eq_mul_ker f₀.toMonoidHom f₀.surjective, hfK]
      _ = Nat.card G₂ := by
        rw [__ch5_CoveringClassification_card_eq_mul_ker g₂.toMonoidHom g₂.surjective, hk₂]
  have hbij₁ : Function.Bijective (h₁ : Covering L₀ G₁) := by
    have : Fintype L₀ := Fintype.ofFinite L₀
    have : Fintype G₁ := Fintype.ofFinite G₁
    exact (Fintype.bijective_iff_surjective_and_card (h₁ : Covering L₀ G₁)).2
      ⟨h₁.surjective, by
        have h₀ : Nat.card L₀ = Nat.card G₁ := hcard₁
        simpa [Nat.card_eq_fintype_card] using h₀⟩
  have hbij₂ : Function.Bijective (h₂ : Covering L₀ G₂) := by
    have : Fintype L₀ := Fintype.ofFinite L₀
    have : Fintype G₂ := Fintype.ofFinite G₂
    exact (Fintype.bijective_iff_surjective_and_card (h₂ : Covering L₀ G₂)).2
      ⟨h₂.surjective, by
        have h₀ : Nat.card L₀ = Nat.card G₂ := hcard₂
        simpa [Nat.card_eq_fintype_card] using h₀⟩
  let e₁ : L₀ ≃* G₁ := MulEquiv.ofBijective (h₁ : Covering L₀ G₁) hbij₁
  let e₂ : L₀ ≃* G₂ := MulEquiv.ofBijective (h₂ : Covering L₀ G₂) hbij₂
  have he₁ : g₁.comp (Covering.ofMulEquiv e₁) = f₀ := by
    ext x
    change g₁ (e₁ x) = f₀ x
    have hpt : g₁ (h₁ x) = f₀ x := by
      rw [← hfac₁]
      rfl
    simpa [e₁] using hpt
  have he₂ : g₂.comp (Covering.ofMulEquiv e₂) = f₀ := by
    ext x
    change g₂ (e₂ x) = f₀ x
    have hpt : g₂ (h₂ x) = f₀ x := by
      rw [← hfac₂]
      rfl
    simpa [e₂] using hpt
  let e : G₁ ≃* G₂ := e₁.symm.trans e₂
  refine ⟨e, ?_, ?_⟩
  · ext x
    change g₂ (e₂ (e₁.symm x)) = g₁ x
    have h₂pt (y : L₀) : g₂ (e₂ y) = f₀ y := by
      rw [← he₂]
      rfl
    have h₁pt (y : L₀) : f₀ y = g₁ (e₁ y) := by
      rw [← he₁]
      rfl
    calc
      g₂ (e₂ (e₁.symm x)) = f₀ (e₁.symm x) := h₂pt (e₁.symm x)
      _ = g₁ (e₁ (e₁.symm x)) := h₁pt (e₁.symm x)
      _ = g₁ x := by rw [e₁.apply_symm_apply]
  · intro e' he'
    ext x
    have hleft : g₂.comp ((Covering.ofMulEquiv e').comp h₁) = f₀ := by
      calc
        g₂.comp ((Covering.ofMulEquiv e').comp h₁) =
            (g₂.comp (Covering.ofMulEquiv e')).comp h₁ :=
          (Covering.comp_assoc g₂ (Covering.ofMulEquiv e') h₁).symm
        _ = g₁.comp h₁ := by rw [he']
        _ = f₀ := hfac₁
    have huniq : (Covering.ofMulEquiv e').comp h₁ = h₂ :=
      IsUniversal.hom_ext hf₂ g₂ hleft hfac₂
    have hptz (z : L₀) : e' (h₁ z) = h₂ z := by
      rw [← huniq]
      rfl
    calc
      e' x = e' (e₁ (e₁.symm x)) := congrArg e' (e₁.apply_symm_apply x).symm
      _ = e' (h₁ (e₁.symm x)) := rfl
      _ = h₂ (e₁.symm x) := hptz (e₁.symm x)
      _ = e₂ (e₁.symm x) := rfl

/-- A double cover is universal whenever a universal cover with kernel of
order two exists: `M(G) = C₂` forces every kernel-two cover to be the
universal one. -/
public theorem isUniversal_of_card_two (f₀ : Covering L₀ G) (hf₀ : IsUniversal.{__ch5_CoveringClassification_u, __ch5_CoveringClassification_u, __ch5_CoveringClassification_u} f₀)
    (hfK : Nat.card ↥f₀.toMonoidHom.ker = 2)
    {L : Type __ch5_CoveringClassification_u} [Group L] [Finite L] [IsQuasisimple L]
    (f : Covering L G) (hk : Nat.card ↥f.toMonoidHom.ker = 2) :
    IsUniversal.{__ch5_CoveringClassification_u, __ch5_CoveringClassification_u, __ch5_CoveringClassification_u} f := by
  rcases coveringIso_of_card_two f₀ hf₀ hf₀ hfK f f₀ hk hfK with ⟨e, he, _⟩
  unfold IsUniversal
  intro M _ _ _ g
  let h₀ : Covering L₀ M := IsUniversal.lift hf₀ g
  refine ⟨h₀.comp (Covering.ofMulEquiv e), ?_, ?_⟩
  · calc
      g.comp (h₀.comp (Covering.ofMulEquiv e)) =
          (g.comp h₀).comp (Covering.ofMulEquiv e) :=
        (Covering.comp_assoc g h₀ (Covering.ofMulEquiv e)).symm
      _ = f₀.comp (Covering.ofMulEquiv e) := by rw [IsUniversal.lift_fac hf₀ g]
      _ = f := he
  · intro h' hh'
    ext x
    have hleft : g.comp (h'.comp (Covering.ofMulEquiv e.symm)) = f₀ := by
      ext x
      change g (h' (e.symm x)) = f₀ x
      have hh'pt (y : L) : g (h' y) = f y := by
        rw [← hh']
        rfl
      have hept (z : L) : f₀ (e z) = f z := by
        rw [← he]
        rfl
      calc
        g (h' (e.symm x)) = f (e.symm x) := hh'pt (e.symm x)
        _ = f₀ (e (e.symm x)) := (hept (e.symm x)).symm
        _ = f₀ x := by rw [e.apply_symm_apply]
    have huniq : h'.comp (Covering.ofMulEquiv e.symm) = h₀ :=
      IsUniversal.hom_ext hf₀ g hleft (IsUniversal.lift_fac hf₀ g)
    have hptz (z : L₀) : h' (e.symm z) = h₀ z := by
      rw [← huniq]
      rfl
    calc
      h' x = h' (e.symm (e x)) := by rw [e.symm_apply_apply x]
      _ = h₀ (e x) := hptz (e x)

public theorem isUniversal_of_card_two_of_universal
    (f₀ : Covering L₀ G) (hf₀ : IsUniversal.{__ch5_CoveringClassification_u, __ch5_CoveringClassification_u, __ch5_CoveringClassification_u} f₀)
    (hf₀' : IsUniversal.{__ch5_CoveringClassification_u, __ch5_CoveringClassification_u, __ch5_CoveringClassification_w} f₀)
    (hfK : Nat.card ↥f₀.toMonoidHom.ker = 2)
    {L : Type __ch5_CoveringClassification_u} [Group L] [Finite L] [IsQuasisimple L]
    (f : Covering L G) (hk : Nat.card ↥f.toMonoidHom.ker = 2) :
    IsUniversal.{__ch5_CoveringClassification_u, __ch5_CoveringClassification_u, __ch5_CoveringClassification_w} f := by
  rcases coveringIso_of_card_two f₀ hf₀ hf₀ hfK f f₀ hk hfK with ⟨e, he, _⟩
  unfold IsUniversal
  intro M _ _ _ g
  let h₀ : Covering L₀ M := IsUniversal.lift hf₀' g
  refine ⟨h₀.comp (Covering.ofMulEquiv e), ?_, ?_⟩
  · calc
      g.comp (h₀.comp (Covering.ofMulEquiv e)) =
          (g.comp h₀).comp (Covering.ofMulEquiv e) :=
        (Covering.comp_assoc g h₀ (Covering.ofMulEquiv e)).symm
      _ = f₀.comp (Covering.ofMulEquiv e) := by
        rw [IsUniversal.lift_fac hf₀' g]
      _ = f := he
  · intro h' hh'
    ext x
    have hleft : g.comp (h'.comp (Covering.ofMulEquiv e.symm)) = f₀ := by
      ext x
      change g (h' (e.symm x)) = f₀ x
      have hh'pt (y : L) : g (h' y) = f y := by
        rw [← hh']
        rfl
      have hept (z : L) : f₀ (e z) = f z := by
        rw [← he]
        rfl
      calc
        g (h' (e.symm x)) = f (e.symm x) := hh'pt (e.symm x)
        _ = f₀ (e (e.symm x)) := (hept (e.symm x)).symm
        _ = f₀ x := by rw [e.apply_symm_apply]
    have huniq : h'.comp (Covering.ofMulEquiv e.symm) = h₀ :=
      IsUniversal.hom_ext hf₀' g hleft (IsUniversal.lift_fac hf₀' g)
    have hptz (z : L₀) : h' (e.symm z) = h₀ z := by
      rw [← huniq]
      rfl
    calc
      h' x = h' (e.symm (e x)) := by rw [e.symm_apply_apply x]
      _ = h₀ (e x) := hptz (e x)

end DoubleCover

end GLS3.Chapter5.Covering
/- END Theory.CoveringClassification -/

/- BEGIN Theory.KernelTwoOrderThreeLift -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

/-- An element of order three has an order-three lift through a central
extension with kernel of cardinality two. -/
public theorem exists_order_three_lift_of_ker_card_two
    {E G : Type*} [Group E] [Finite E] [Group G]
    (q : E →* G) (hq : Function.Surjective q)
    (hcenter : q.ker ≤ Subgroup.center E)
    (hcard : Nat.card q.ker = 2)
    (g : G) (hg : orderOf g = 3) :
    ∃ t : E, q t = g ∧ orderOf t = 3 := by
  obtain ⟨x, hx⟩ := hq g
  have hx3ker : x ^ 3 ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_pow, hx]
    simpa [hg] using pow_orderOf_eq_one g
  rcases DoubleCoverUniqueness.eq_one_or_eq_kernelInvolution
      q hcard hx3ker with hx3 | hx3
  · refine ⟨x, hx, ?_⟩
    have hdiv : orderOf x ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hx3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with h1 | h3
    · have hx1 : x = 1 := orderOf_eq_one_iff.mp h1
      have : g = 1 := by simpa [hx1] using hx.symm
      rw [this, orderOf_one] at hg
      omega
    · exact h3
  · let z : E := DoubleCoverUniqueness.kernelInvolution q hcard
    let t := z * x
    have hzker : z ∈ q.ker :=
      (DoubleCoverUniqueness.kernelInvolution q hcard).property
    have hzq : q z = 1 := MonoidHom.mem_ker.mp hzker
    have hzt : q t = g := by simp [t, hzq, hx]
    have hz2 : z ^ 2 = 1 :=
      DoubleCoverUniqueness.kernelInvolution_sq q hcard
    have hzx : Commute z x :=
      (Subgroup.mem_center_iff.mp (hcenter hzker) x).symm
    have ht3 : t ^ 3 = 1 := by
      change (z * x) ^ 3 = 1
      rw [hzx.mul_pow, hx3]
      calc
        z ^ 3 * z = (z ^ 2) ^ 2 := by group
        _ = 1 := by rw [hz2, one_pow]
    refine ⟨t, hzt, ?_⟩
    apply orderOf_eq_prime ht3
    intro ht1
    have hgone : g = 1 := by simpa [t, ht1] using hzt.symm
    rw [hgone, orderOf_one] at hg
    omega

end GLS3.Chapter5.SchurPresentation
/- END Theory.KernelTwoOrderThreeLift -/

/- BEGIN Theory.proposition_5_2_4_f -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

open scoped commutatorElement

private theorem __ch5_proposition_5_2_4_f_natCard_schurSymmetricProjection_ker (n : Nat) :
    Nat.card (schurSymmetricProjection n).ker = 2 := by
  rw [schurSymmetricProjection_ker_eq_zpowers, Nat.card_zpowers,
    orderOf_schurCentral]

private theorem __ch5_proposition_5_2_4_f_symmetricProjection_sq_eq_sq_of_apply_eq (n : Nat)
    {x y : SchurPresentedGroup n}
    (hxy : schurSymmetricProjection n x = schurSymmetricProjection n y) :
    x ^ 2 = y ^ 2 := by
  let k := x * y⁻¹
  have hk : k ∈ (schurSymmetricProjection n).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    change schurSymmetricProjection n x * (schurSymmetricProjection n y)⁻¹ = 1
    rw [hxy]
    simp
  have hk2 : k ^ 2 = 1 :=
    DoubleCoverUniqueness.ker_pow_two_eq_one (schurSymmetricProjection n)
      (__ch5_proposition_5_2_4_f_natCard_schurSymmetricProjection_ker n) hk
  have hkcenter : k ∈ Subgroup.center (SchurPresentedGroup n) := by
    rw [schurSymmetricProjection_ker_eq_zpowers] at hk
    exact (Subgroup.zpowers_le.mpr (schurCentral_mem_center n)) hk
  have hcomm : Commute k y :=
    (Subgroup.mem_center_iff.mp hkcenter y).symm
  have hxy' : x = k * y := by
    simp [k]
  calc
    x ^ 2 = (k * y) ^ 2 := by rw [hxy']
    _ = k ^ 2 * y ^ 2 := hcomm.mul_pow 2
    _ = y ^ 2 := by rw [hk2]; simp

private theorem __ch5_proposition_5_2_4_f_symmetricProjection_sq_eq_sq_of_conjugate_images (n : Nat)
    {x y : SchurPresentedGroup n} {c : Equiv.Perm (Fin (n + 5))}
    (hx : schurSymmetricProjection n x ^ 2 = 1)
    (hconj : c * schurSymmetricProjection n x * c⁻¹ =
      schurSymmetricProjection n y) :
    x ^ 2 = y ^ 2 := by
  obtain ⟨d, rfl⟩ := schurSymmetricProjection_surjective n c
  have himage : schurSymmetricProjection n (d * x * d⁻¹) =
      schurSymmetricProjection n y := by
    simpa only [map_mul, map_inv] using hconj
  have hsquares := __ch5_proposition_5_2_4_f_symmetricProjection_sq_eq_sq_of_apply_eq n himage
  have hxker : x ^ 2 ∈ (schurSymmetricProjection n).ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact hx
  have hxcenter : x ^ 2 ∈ Subgroup.center (SchurPresentedGroup n) := by
    rw [schurSymmetricProjection_ker_eq_zpowers] at hxker
    exact (Subgroup.zpowers_le.mpr (schurCentral_mem_center n)) hxker
  have hcomm : d * x ^ 2 = x ^ 2 * d :=
    Subgroup.mem_center_iff.mp hxcenter d
  calc
    x ^ 2 = (d * x * d⁻¹) ^ 2 := by
      rw [show (d * x * d⁻¹) ^ 2 = d * x ^ 2 * d⁻¹ by
        simp [pow_two, mul_assoc]]
      rw [hcomm]
      simp
    _ = y ^ 2 := hsquares

@[expose] public noncomputable def permutationLift (n : Nat)
    (sigma : Equiv.Perm (Fin (n + 5))) : SchurPresentedGroup n :=
  Classical.choose (schurSymmetricProjection_surjective n sigma)

public theorem permutationLift_projection (n : Nat)
    (sigma : Equiv.Perm (Fin (n + 5))) :
    schurSymmetricProjection n (permutationLift n sigma) = sigma :=
  Classical.choose_spec (schurSymmetricProjection_surjective n sigma)

public theorem permutationLift_swap_sq (n : Nat) {a b : Fin (n + 5)}
    (hab : a ≠ b) :
    permutationLift n (Equiv.swap a b) ^ 2 = schurCentral n := by
  let i : Fin (n + 4) := 0
  have hi : i.castSucc ≠ i.succ := ne_of_lt i.castSucc_lt_succ
  obtain ⟨c, hc⟩ := isConj_iff.mp (Equiv.Perm.isConj_swap hi hab)
  have hproj : schurSymmetricProjection n (adjacentLift n i) = adjacentSwap n i := by
    simpa only [adjacentLift] using schurSymmetricProjection_adjacent n i
  have hx : schurSymmetricProjection n (adjacentLift n i) ^ 2 = 1 := by
    rw [hproj]
    exact adjacentSwap_sq n i
  have hconj : c * schurSymmetricProjection n (adjacentLift n i) * c⁻¹ =
      schurSymmetricProjection n (permutationLift n (Equiv.swap a b)) := by
    rw [hproj, permutationLift_projection]
    exact hc
  calc
    permutationLift n (Equiv.swap a b) ^ 2 = adjacentLift n i ^ 2 :=
      (__ch5_proposition_5_2_4_f_symmetricProjection_sq_eq_sq_of_conjugate_images n hx hconj).symm
    _ = schurCentral n := by simpa [adjacentLift, pow_two] using schurAdjacent_sq n i

private theorem __ch5_proposition_5_2_4_f_permutationLift_swap_inv (n : Nat) {a b : Fin (n + 5)}
    (hab : a ≠ b) :
    (permutationLift n (Equiv.swap a b))⁻¹ =
      schurCentral n * permutationLift n (Equiv.swap a b) := by
  let x := permutationLift n (Equiv.swap a b)
  let z := schurCentral n
  have hx2 : x * x = z := by
    simpa [x, z, pow_two] using permutationLift_swap_sq n hab
  have hzx : Commute z x :=
    (Subgroup.mem_center_iff.mp (schurCentral_mem_center n) x).symm
  apply (eq_inv_of_mul_eq_one_right (a := x) (b := z * x) ?_).symm
  calc
    x * (z * x) = (x * z) * x := by rw [mul_assoc]
    _ = (z * x) * x := by rw [hzx.eq.symm]
    _ = z * (x * x) := by simp [mul_assoc]
    _ = z * z := by rw [hx2]
    _ = 1 := by simpa [z, pow_two] using schurCentral_sq n

public theorem permutationLift_disjoint_swaps_mul_sq (n : Nat)
    {a b c d : Fin (n + 5)} (hnodup : [a, b, c, d].Nodup) :
    (permutationLift n (Equiv.swap a b) *
      permutationLift n (Equiv.swap c d)) ^ 2 = schurCentral n := by
  have hab : a ≠ b := by
    intro h
    subst b
    simp at hnodup
  have hcd : c ≠ d := by
    intro h
    subst d
    simp at hnodup
  have hroot : 4 * 0 + 2 < n + 4 := by omega
  let root := rootBlockWord n 0 hroot
  let target := permutationLift n (Equiv.swap a b) *
    permutationLift n (Equiv.swap c d)
  have hct_target :
      (Equiv.swap a b * Equiv.swap c d).cycleType = {2, 2} :=
    Equiv.Perm.cycleType_swap_mul_swap_of_nodup hnodup
  have hct_root : (blockPerm n 0 hroot).cycleType = {2, 2} := by
    let r0 : Fin (n + 5) := ⟨0, by omega⟩
    let r1 : Fin (n + 5) := ⟨1, by omega⟩
    let r2 : Fin (n + 5) := ⟨2, by omega⟩
    let r3 : Fin (n + 5) := ⟨3, by omega⟩
    have hr : [r0, r1, r2, r3].Nodup := by
      simp [r0, r1, r2, r3, Fin.ext_iff]
    simpa [blockPerm, r0, r1, r2, r3] using
      (Equiv.Perm.cycleType_swap_mul_swap_of_nodup hr)
  obtain ⟨q, hq⟩ := isConj_iff.mp
    (Equiv.Perm.isConj_iff_cycleType_eq.mpr (hct_root.trans hct_target.symm))
  have hroot_proj : schurSymmetricProjection n root = blockPerm n 0 hroot := by
    simpa [root] using rootBlockWord_proj n 0 hroot
  have htarget_proj : schurSymmetricProjection n target =
      Equiv.swap a b * Equiv.swap c d := by
    simp [target, permutationLift_projection]
  have hroot_proj_sq : schurSymmetricProjection n root ^ 2 = 1 := by
    rw [← map_pow]
    change schurSymmetricProjection n (rootBlockWord n 0 hroot ^ 2) = 1
    rw [rootBlockWord_sq, schurSymmetricProjection_central]
  have hconj : q * schurSymmetricProjection n root * q⁻¹ =
      schurSymmetricProjection n target := by
    rw [hroot_proj, htarget_proj]
    exact hq
  calc
    target ^ 2 = root ^ 2 :=
      (__ch5_proposition_5_2_4_f_symmetricProjection_sq_eq_sq_of_conjugate_images n hroot_proj_sq hconj).symm
    _ = schurCentral n := by simpa [root] using rootBlockWord_sq n 0 hroot

public theorem permutationLift_disjoint_swaps_commutator (n : Nat)
    {a b c d : Fin (n + 5)} (hnodup : [a, b, c, d].Nodup) :
    permutationLift n (Equiv.swap a b) * permutationLift n (Equiv.swap c d) *
        (permutationLift n (Equiv.swap a b))⁻¹ *
        (permutationLift n (Equiv.swap c d))⁻¹ = schurCentral n := by
  have hab : a ≠ b := by
    intro h
    subst b
    simp at hnodup
  have hcd : c ≠ d := by
    intro h
    subst d
    simp at hnodup
  let x := permutationLift n (Equiv.swap a b)
  let y := permutationLift n (Equiv.swap c d)
  let z := schurCentral n
  have hxinv : x⁻¹ = z * x := by
    simpa [x, z] using __ch5_proposition_5_2_4_f_permutationLift_swap_inv n hab
  have hyinv : y⁻¹ = z * y := by
    simpa [y, z] using __ch5_proposition_5_2_4_f_permutationLift_swap_inv n hcd
  have hxy2 : (x * y) ^ 2 = z := by
    simpa [x, y, z] using permutationLift_disjoint_swaps_mul_sq n hnodup
  have hzx : Commute z x :=
    (Subgroup.mem_center_iff.mp (schurCentral_mem_center n) x).symm
  have hzy : Commute z y :=
    (Subgroup.mem_center_iff.mp (schurCentral_mem_center n) y).symm
  have hzxy : Commute z (x * y) := hzx.mul_right hzy
  have hzxyx : Commute z ((x * y) * x) := hzxy.mul_right hzx
  have hz2 : z * z = 1 := by
    simpa [z, pow_two] using schurCentral_sq n
  rw [show permutationLift n (Equiv.swap a b) = x by rfl,
    show permutationLift n (Equiv.swap c d) = y by rfl, hxinv, hyinv]
  calc
    x * y * (z * x) * (z * y) = ((x * y) * z) * x * (z * y) := by
      simp only [mul_assoc]
    _ = (z * (x * y)) * x * (z * y) := by rw [hzxy.eq]
    _ = z * ((x * y) * x) * (z * y) := by simp only [mul_assoc]
    _ = z * (((x * y) * x) * z) * y := by simp only [mul_assoc]
    _ = z * (z * ((x * y) * x)) * y := by rw [hzxyx.eq]
    _ = (z * z) * ((x * y) * x * y) := by simp only [mul_assoc]
    _ = (x * y) ^ 2 := by rw [hz2]; simp [pow_two, mul_assoc]
    _ = z := hxy2

private theorem __ch5_proposition_5_2_4_f_swapFactorsAux_support
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (l : List alpha) (f : Equiv.Perm alpha)
    (h : ∀ {x}, f x ≠ x → x ∈ l) :
    ∀ g ∈ (Equiv.Perm.swapFactorsAux l f h).1,
      g.support ≤ f.support := by
  induction l generalizing f with
  | nil =>
      simp [Equiv.Perm.swapFactorsAux]
  | cons x l ih =>
      unfold Equiv.Perm.swapFactorsAux
      split_ifs with hfx
      · exact ih f (fun {y} hy =>
          List.mem_of_ne_of_mem (fun hyx : y = x => by simp [hyx, hfx.symm] at hy) (h hy))
      · let q := Equiv.swap x (f x) * f
        have hqx : q x = x := by simp [q]
        have hswap_le : (Equiv.swap x (f x)).support ≤ f.support := by
          rw [Equiv.Perm.support_swap hfx]
          simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff,
            Equiv.Perm.mem_support]
          refine ⟨Ne.symm hfx, ?_⟩
          intro hfix
          exact hfx (f.injective hfix).symm
        have hq_le : q.support ≤ f.support :=
          (Equiv.Perm.support_mul_le (Equiv.swap x (f x)) f).trans
            (sup_le hswap_le le_rfl)
        let m := Equiv.Perm.swapFactorsAux l q (fun {y} hy => by
          have hy' : f y ≠ y ∧ y ≠ x :=
            Equiv.Perm.ne_and_ne_of_swap_mul_apply_ne_self hy
          exact List.mem_of_ne_of_mem hy'.2 (h hy'.1))
        intro g hg
        change g ∈ Equiv.swap x (f x) :: m.1 at hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact hswap_le
        · exact (ih q (fun {y} hy => by
            have hy' : f y ≠ y ∧ y ≠ x :=
              Equiv.Perm.ne_and_ne_of_swap_mul_apply_ne_self hy
            exact List.mem_of_ne_of_mem hy'.2 (h hy'.1)) g hg).trans hq_le

public theorem swapFactors_support {alpha : Type*} [Fintype alpha] [LinearOrder alpha]
    (f : Equiv.Perm alpha) :
    ∀ g ∈ (Equiv.Perm.swapFactors f).1, g.support ≤ f.support := by
  exact __ch5_proposition_5_2_4_f_swapFactorsAux_support ((@Finset.univ alpha _).sort (· ≤ ·)) f
    (fun {_} _ => (Finset.mem_sort _).2 (Finset.mem_univ _))

public theorem permutationLift_disjoint_swaps_twist (n : Nat)
    {a b c d : Fin (n + 5)} (hnodup : [a, b, c, d].Nodup) :
    permutationLift n (Equiv.swap a b) * permutationLift n (Equiv.swap c d) =
      schurCentral n * permutationLift n (Equiv.swap c d) *
        permutationLift n (Equiv.swap a b) := by
  have hcomm := permutationLift_disjoint_swaps_commutator n hnodup
  have h := congrArg (fun w : SchurPresentedGroup n =>
    w * permutationLift n (Equiv.swap c d) * permutationLift n (Equiv.swap a b)) hcomm
  simpa [mul_assoc] using h

private theorem __ch5_proposition_5_2_4_f_mul_listProd_eq_central_pow (n : Nat)
    (x : SchurPresentedGroup n) (ys : List (SchurPresentedGroup n))
    (hpair : ∀ y ∈ ys, x * y = schurCentral n * y * x) :
    x * ys.prod = schurCentral n ^ ys.length * ys.prod * x := by
  induction ys with
  | nil => simp
  | cons y ys ih =>
      have hxy := hpair y (by simp)
      have htail : ∀ t ∈ ys, x * t = schurCentral n * t * x := by
        intro t ht
        exact hpair t (by simp [ht])
      have ih' := ih htail
      have hyz : Commute y (schurCentral n) :=
        Subgroup.mem_center_iff.mp (schurCentral_mem_center n) y
      have hyzpow : Commute y (schurCentral n ^ ys.length) := hyz.pow_right _
      calc
        x * (y :: ys).prod = (x * y) * ys.prod := by simp [mul_assoc]
        _ = (schurCentral n * y * x) * ys.prod := by rw [hxy]
        _ = schurCentral n * y * (x * ys.prod) := by simp only [mul_assoc]
        _ = schurCentral n * y *
            (schurCentral n ^ ys.length * ys.prod * x) := by rw [ih']
        _ = (schurCentral n * schurCentral n ^ ys.length) *
            ((y :: ys).prod) * x := by
          calc
            schurCentral n * y *
                (schurCentral n ^ ys.length * ys.prod * x) =
              schurCentral n *
                ((y * schurCentral n ^ ys.length) * (ys.prod * x)) := by
                  simp only [mul_assoc]
            _ = schurCentral n *
                ((schurCentral n ^ ys.length * y) * (ys.prod * x)) := by
                  rw [hyzpow.eq]
            _ = (schurCentral n * schurCentral n ^ ys.length) *
                ((y :: ys).prod) * x := by
                  simp only [List.prod_cons, mul_assoc]
        _ = schurCentral n ^ (y :: ys).length * (y :: ys).prod * x := by
          simp [pow_succ', mul_assoc]

private theorem __ch5_proposition_5_2_4_f_listProd_mul_listProd_eq_central_pow (n : Nat)
    (xs ys : List (SchurPresentedGroup n))
    (hpair : ∀ x ∈ xs, ∀ y ∈ ys,
      x * y = schurCentral n * y * x) :
    xs.prod * ys.prod =
      schurCentral n ^ (xs.length * ys.length) * ys.prod * xs.prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hxpair : ∀ y ∈ ys, x * y = schurCentral n * y * x := by
        intro y hy
        exact hpair x (by simp) y hy
      have htail : ∀ t ∈ xs, ∀ y ∈ ys,
          t * y = schurCentral n * y * t := by
        intro t ht y hy
        exact hpair t (by simp [ht]) y hy
      have ih' := ih htail
      have hxmove := __ch5_proposition_5_2_4_f_mul_listProd_eq_central_pow n x ys hxpair
      have hzx : Commute (schurCentral n) x :=
        (Subgroup.mem_center_iff.mp (schurCentral_mem_center n) x).symm
      have hzpowx : Commute (schurCentral n ^ (xs.length * ys.length)) x :=
        hzx.pow_left _
      calc
        (x :: xs).prod * ys.prod = x * (xs.prod * ys.prod) := by
          simp only [List.prod_cons, mul_assoc]
        _ = x * (schurCentral n ^ (xs.length * ys.length) *
            ys.prod * xs.prod) := by rw [ih']
        _ = schurCentral n ^ (xs.length * ys.length) *
            (x * ys.prod) * xs.prod := by
          calc
            x * (schurCentral n ^ (xs.length * ys.length) *
                ys.prod * xs.prod) =
              (x * schurCentral n ^ (xs.length * ys.length)) *
                (ys.prod * xs.prod) := by simp only [mul_assoc]
            _ = (schurCentral n ^ (xs.length * ys.length) * x) *
                (ys.prod * xs.prod) := by rw [hzpowx.eq.symm]
            _ = schurCentral n ^ (xs.length * ys.length) *
                (x * ys.prod) * xs.prod := by simp only [mul_assoc]
        _ = schurCentral n ^ (xs.length * ys.length) *
            (schurCentral n ^ ys.length * ys.prod * x) * xs.prod := by
          rw [hxmove]
        _ = schurCentral n ^ ((x :: xs).length * ys.length) *
            ys.prod * (x :: xs).prod := by
          calc
            schurCentral n ^ (xs.length * ys.length) *
                (schurCentral n ^ ys.length * ys.prod * x) * xs.prod =
              (schurCentral n ^ (xs.length * ys.length) *
                schurCentral n ^ ys.length) * ys.prod * (x * xs.prod) := by
                  simp only [mul_assoc]
            _ = schurCentral n ^
                (xs.length * ys.length + ys.length) * ys.prod *
                  (x * xs.prod) := by rw [pow_add]
            _ = schurCentral n ^ ((x :: xs).length * ys.length) *
                ys.prod * (x :: xs).prod := by
                  simp only [List.length_cons, List.prod_cons]
                  congr 2
                  simp [Nat.add_mul]

@[expose] public noncomputable def permutationSectionLift (n : Nat)
    (sigma : Equiv.Perm (Fin (n + 5))) : SchurPresentedGroup n :=
  ((Equiv.Perm.swapFactors sigma).1.map (permutationLift n)).prod

public theorem permutationSectionLift_projection (n : Nat)
    (sigma : Equiv.Perm (Fin (n + 5))) :
    schurSymmetricProjection n (permutationSectionLift n sigma) = sigma := by
  rw [permutationSectionLift, map_list_prod]
  have hmap :
      List.map (schurSymmetricProjection n)
          (List.map (permutationLift n) (Equiv.Perm.swapFactors sigma).1) =
        (Equiv.Perm.swapFactors sigma).1 := by
    rw [List.map_map]
    simpa only [List.map_id_fun, id_eq] using
      (List.map_congr_left (l := (Equiv.Perm.swapFactors sigma).1)
        (f := schurSymmetricProjection n ∘ permutationLift n)
        (g := _root_.id) (fun g _ => permutationLift_projection n g))
  rw [hmap]
  exact (Equiv.Perm.swapFactors sigma).2.1

private theorem __ch5_proposition_5_2_4_f_disjoint_swap_factors_twist (n : Nat)
    {sigma tau : Equiv.Perm (Fin (n + 5))}
    (hdisjoint : Equiv.Perm.Disjoint sigma tau)
    {g h : Equiv.Perm (Fin (n + 5))}
    (hg : g ∈ (Equiv.Perm.swapFactors sigma).1)
    (hh : h ∈ (Equiv.Perm.swapFactors tau).1) :
    permutationLift n g * permutationLift n h =
      schurCentral n * permutationLift n h * permutationLift n g := by
  rcases (Equiv.Perm.swapFactors sigma).2.2 g hg with ⟨a, b, hab, rfl⟩
  rcases (Equiv.Perm.swapFactors tau).2.2 h hh with ⟨c, d, hcd, rfl⟩
  have hfactor_disjoint : Equiv.Perm.Disjoint (Equiv.swap a b) (Equiv.swap c d) :=
    hdisjoint.mono (swapFactors_support sigma _ hg) (swapFactors_support tau _ hh)
  have hsupp : Disjoint ({a, b} : Finset (Fin (n + 5))) ({c, d} : Finset (Fin (n + 5))) := by
    rw [← Equiv.Perm.support_swap hab, ← Equiv.Perm.support_swap hcd]
    exact hfactor_disjoint.disjoint_support
  have hac : a ≠ c := by
    intro e
    subst c
    exact (Finset.disjoint_left.mp hsupp (show a ∈ ({a, b} : Finset _) by simp))
      (show a ∈ ({a, d} : Finset _) by simp)
  have had : a ≠ d := by
    intro e
    subst d
    exact (Finset.disjoint_left.mp hsupp (show a ∈ ({a, b} : Finset _) by simp))
      (show a ∈ ({c, a} : Finset _) by simp)
  have hbc : b ≠ c := by
    intro e
    subst c
    exact (Finset.disjoint_left.mp hsupp (show b ∈ ({a, b} : Finset _) by simp))
      (show b ∈ ({b, d} : Finset _) by simp)
  have hbd : b ≠ d := by
    intro e
    subst d
    exact (Finset.disjoint_left.mp hsupp (show b ∈ ({a, b} : Finset _) by simp))
      (show b ∈ ({c, b} : Finset _) by simp)
  apply permutationLift_disjoint_swaps_twist n
  simp [hab, hcd, hac, had, hbc, hbd]

public theorem permutationSectionLift_disjoint_twist (n : Nat)
    {sigma tau : Equiv.Perm (Fin (n + 5))}
    (hdisjoint : Equiv.Perm.Disjoint sigma tau) :
    permutationSectionLift n sigma * permutationSectionLift n tau =
      schurCentral n ^ ((Equiv.Perm.swapFactors sigma).1.length *
        (Equiv.Perm.swapFactors tau).1.length) *
      permutationSectionLift n tau * permutationSectionLift n sigma := by
  change
    (List.map (permutationLift n) (Equiv.Perm.swapFactors sigma).1).prod *
        (List.map (permutationLift n) (Equiv.Perm.swapFactors tau).1).prod =
      schurCentral n ^ ((Equiv.Perm.swapFactors sigma).1.length *
        (Equiv.Perm.swapFactors tau).1.length) *
        (List.map (permutationLift n) (Equiv.Perm.swapFactors tau).1).prod *
        (List.map (permutationLift n) (Equiv.Perm.swapFactors sigma).1).prod
  simpa only [List.length_map] using
    (__ch5_proposition_5_2_4_f_listProd_mul_listProd_eq_central_pow n
      (List.map (permutationLift n) (Equiv.Perm.swapFactors sigma).1)
      (List.map (permutationLift n) (Equiv.Perm.swapFactors tau).1) (by
        intro x hx y hy
        rcases List.mem_map.mp hx with ⟨g, hg, rfl⟩
        rcases List.mem_map.mp hy with ⟨h, hh, rfl⟩
        exact __ch5_proposition_5_2_4_f_disjoint_swap_factors_twist n hdisjoint hg hh))

private theorem __ch5_proposition_5_2_4_f_twist_of_projection_eq (n : Nat)
    {x y sx sy c : SchurPresentedGroup n}
    (hx : schurSymmetricProjection n x = schurSymmetricProjection n sx)
    (hy : schurSymmetricProjection n y = schurSymmetricProjection n sy)
    (hc : c ∈ Subgroup.center (SchurPresentedGroup n))
    (htwist : sx * sy = c * sy * sx) :
    x * y = c * y * x := by
  let kx := x * sx⁻¹
  let ky := y * sy⁻¹
  have hkxker : kx ∈ (schurSymmetricProjection n).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hx]
    simp
  have hkyker : ky ∈ (schurSymmetricProjection n).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hy]
    simp
  have hkx : kx ∈ Subgroup.center (SchurPresentedGroup n) := by
    rw [schurSymmetricProjection_ker_eq_zpowers] at hkxker
    exact (Subgroup.zpowers_le.mpr (schurCentral_mem_center n)) hkxker
  have hky : ky ∈ Subgroup.center (SchurPresentedGroup n) := by
    rw [schurSymmetricProjection_ker_eq_zpowers] at hkyker
    exact (Subgroup.zpowers_le.mpr (schurCentral_mem_center n)) hkyker
  have hxeq : x = kx * sx := by simp [kx, mul_assoc]
  have hyeq : y = ky * sy := by simp [ky, mul_assoc]
  have hkx_sy : Commute kx sy :=
    (Subgroup.mem_center_iff.mp hkx sy).symm
  have hky_sx : Commute ky sx :=
    (Subgroup.mem_center_iff.mp hky sx).symm
  have hkx_ky : Commute kx ky :=
    (Subgroup.mem_center_iff.mp hkx ky).symm
  have hc_kx : Commute c kx :=
    (Subgroup.mem_center_iff.mp hc kx).symm
  have hc_ky : Commute c ky :=
    (Subgroup.mem_center_iff.mp hc ky).symm
  have hc_kxky : Commute c (kx * ky) := hc_kx.mul_right hc_ky
  have hkx_kysy : Commute kx (ky * sy) :=
    (Subgroup.mem_center_iff.mp hkx (ky * sy)).symm
  rw [hxeq, hyeq]
  calc
    (kx * sx) * (ky * sy) = kx * ky * (sx * sy) := by
      rw [mul_assoc kx sx (ky * sy), ← mul_assoc sx ky sy,
        hky_sx.eq.symm]
      simp only [mul_assoc]
    _ = kx * ky * (c * sy * sx) := by rw [htwist]
    _ = c * (ky * sy) * (kx * sx) := by
      calc
        kx * ky * (c * sy * sx) = (kx * ky) * c * (sy * sx) := by
          simp only [mul_assoc]
        _ = c * (kx * ky) * (sy * sx) := by rw [hc_kxky.eq]
        _ = c * (kx * (ky * sy)) * sx := by simp only [mul_assoc]
        _ = c * ((ky * sy) * kx) * sx := by rw [hkx_kysy.eq]
        _ = c * (ky * sy) * (kx * sx) := by simp only [mul_assoc]

private theorem __ch5_proposition_5_2_4_f_swapFactors_even_iff_mem_alternating
    {alpha : Type*} [Fintype alpha] [LinearOrder alpha]
    (sigma : Equiv.Perm alpha) :
    Even (Equiv.Perm.swapFactors sigma).1.length ↔
      sigma ∈ alternatingGroup alpha := by
  constructor
  · intro heven
    rw [← (Equiv.Perm.swapFactors sigma).2.1]
    exact (Equiv.Perm.prod_list_swap_mem_alternatingGroup_iff_even_length
      (Equiv.Perm.swapFactors sigma).2.2).2 heven
  · intro hmem
    rw [← (Equiv.Perm.swapFactors sigma).2.1] at hmem
    exact (Equiv.Perm.prod_list_swap_mem_alternatingGroup_iff_even_length
      (Equiv.Perm.swapFactors sigma).2.2).1 hmem

private theorem __ch5_proposition_5_2_4_f_pow_eq_one_of_even_of_sq_eq_one {G : Type*} [Group G]
    {z : G} (hz2 : z ^ 2 = 1) {m : Nat} (hm : Even m) : z ^ m = 1 := by
  rcases hm with ⟨k, rfl⟩
  rw [← two_mul, pow_mul, hz2, one_pow]

private theorem __ch5_proposition_5_2_4_f_pow_eq_self_of_odd_of_sq_eq_one {G : Type*} [Group G]
    {z : G} (hz2 : z ^ 2 = 1) {m : Nat} (hm : Odd m) : z ^ m = z := by
  rcases hm with ⟨k, rfl⟩
  rw [show 2 * k + 1 = 2 * k + 1 by rfl, pow_add, pow_mul, hz2, one_pow,
    one_mul, pow_one]

/-- The complete disjoint-support twist formula in the explicit Schur
symmetric double cover. Its exponent is the product of the two transposition
factorization lengths, hence records exactly the two permutation signs. -/
public theorem proposition_5_2_4_f_twist (n : Nat)
    (x y : SchurPresentedGroup n)
    (hdisjoint : Equiv.Perm.Disjoint
      (schurSymmetricProjection n x) (schurSymmetricProjection n y)) :
    x * y =
      schurCentral n ^
          ((Equiv.Perm.swapFactors (schurSymmetricProjection n x)).1.length *
            (Equiv.Perm.swapFactors (schurSymmetricProjection n y)).1.length) *
        y * x := by
  let sigma := schurSymmetricProjection n x
  let tau := schurSymmetricProjection n y
  let exponent := (Equiv.Perm.swapFactors sigma).1.length *
    (Equiv.Perm.swapFactors tau).1.length
  apply __ch5_proposition_5_2_4_f_twist_of_projection_eq n
      (sx := permutationSectionLift n sigma)
      (sy := permutationSectionLift n tau)
      (c := schurCentral n ^ exponent)
  · exact (permutationSectionLift_projection n sigma).symm
  · exact (permutationSectionLift_projection n tau).symm
  · exact (Subgroup.zpowers_le.mpr (schurCentral_mem_center n))
      (Subgroup.mem_zpowers_iff.mpr ⟨exponent, rfl⟩)
  · simpa [sigma, tau, exponent] using
      permutationSectionLift_disjoint_twist n hdisjoint

/-- Proposition 5.2.4(f)(1), explicit Schur-cover form: lifts of disjoint
permutations commute if at least one image is alternating. -/
public theorem proposition_5_2_4_f_1 (n : Nat)
    (x y : SchurPresentedGroup n)
    (hdisjoint : Equiv.Perm.Disjoint
      (schurSymmetricProjection n x) (schurSymmetricProjection n y))
    (heven : schurSymmetricProjection n x ∈ alternatingGroup (Fin (n + 5)) ∨
      schurSymmetricProjection n y ∈ alternatingGroup (Fin (n + 5))) :
    x * y * x⁻¹ * y⁻¹ = 1 := by
  let lx := (Equiv.Perm.swapFactors (schurSymmetricProjection n x)).1.length
  let ly := (Equiv.Perm.swapFactors (schurSymmetricProjection n y)).1.length
  have hexponent : Even (lx * ly) := by
    rcases heven with hx | hy
    · exact (__ch5_proposition_5_2_4_f_swapFactors_even_iff_mem_alternating
        (schurSymmetricProjection n x)).2 hx |>.mul_right ly
    · exact (__ch5_proposition_5_2_4_f_swapFactors_even_iff_mem_alternating
        (schurSymmetricProjection n y)).2 hy |>.mul_left lx
  have hzpow : schurCentral n ^ (lx * ly) = 1 :=
    __ch5_proposition_5_2_4_f_pow_eq_one_of_even_of_sq_eq_one (schurCentral_sq n) hexponent
  have htwist := proposition_5_2_4_f_twist n x y hdisjoint
  have hcomm : x * y = y * x := by
    simpa [lx, ly, hzpow] using htwist
  rw [hcomm]
  simp [mul_assoc]

/-- Proposition 5.2.4(f)(2), explicit Schur-cover form: if both disjoint
images are odd permutations, the lift commutator is the central involution. -/
public theorem proposition_5_2_4_f_2 (n : Nat)
    (x y : SchurPresentedGroup n)
    (hdisjoint : Equiv.Perm.Disjoint
      (schurSymmetricProjection n x) (schurSymmetricProjection n y))
    (hoddx : schurSymmetricProjection n x ∉ alternatingGroup (Fin (n + 5)))
    (hoddy : schurSymmetricProjection n y ∉ alternatingGroup (Fin (n + 5))) :
    x * y * x⁻¹ * y⁻¹ = schurCentral n := by
  let lx := (Equiv.Perm.swapFactors (schurSymmetricProjection n x)).1.length
  let ly := (Equiv.Perm.swapFactors (schurSymmetricProjection n y)).1.length
  have hlx : Odd lx := Nat.not_even_iff_odd.mp (by
    intro heven
    exact hoddx ((__ch5_proposition_5_2_4_f_swapFactors_even_iff_mem_alternating
      (schurSymmetricProjection n x)).1 heven))
  have hly : Odd ly := Nat.not_even_iff_odd.mp (by
    intro heven
    exact hoddy ((__ch5_proposition_5_2_4_f_swapFactors_even_iff_mem_alternating
      (schurSymmetricProjection n y)).1 heven))
  have hzpow : schurCentral n ^ (lx * ly) = schurCentral n :=
    __ch5_proposition_5_2_4_f_pow_eq_self_of_odd_of_sq_eq_one (schurCentral_sq n) (hlx.mul hly)
  have htwist := proposition_5_2_4_f_twist n x y hdisjoint
  have hrelation : x * y = schurCentral n * y * x := by
    simpa [lx, ly, hzpow] using htwist
  have h := congrArg (fun w : SchurPresentedGroup n => w * x⁻¹ * y⁻¹) hrelation
  simpa [mul_assoc] using h

/-- Proposition 5.2.4(f), both clauses, for arbitrary lifts in the explicit
Schur symmetric double cover. -/
public theorem proposition_5_2_4_f (n : Nat)
    (x y : SchurPresentedGroup n)
    (hdisjoint : Equiv.Perm.Disjoint
      (schurSymmetricProjection n x) (schurSymmetricProjection n y)) :
    (schurSymmetricProjection n x ∈ alternatingGroup (Fin (n + 5)) ∨
        schurSymmetricProjection n y ∈ alternatingGroup (Fin (n + 5)) →
      x * y * x⁻¹ * y⁻¹ = 1) ∧
    (schurSymmetricProjection n x ∉ alternatingGroup (Fin (n + 5)) →
      schurSymmetricProjection n y ∉ alternatingGroup (Fin (n + 5)) →
      x * y * x⁻¹ * y⁻¹ = schurCentral n) := by
  exact ⟨proposition_5_2_4_f_1 n x y hdisjoint,
    proposition_5_2_4_f_2 n x y hdisjoint⟩

end GLS3.Chapter5.SchurPresentation
/- END Theory.proposition_5_2_4_f -/

/- BEGIN Theory.A6StandardNineCoordinates -/
namespace GLS3.Chapter5

open SchurPresentation

/-- Every element of the standard elementary abelian subgroup of order nine
has coordinates in the displayed basis. -/
public theorem a6StandardNine_exists_zpow_coordinates
    (g : SchurPresentation.Theorem523BaseNine.a6StandardNine) :
    ∃ i j : ℤ, g.1 = SchurPresentation.Theorem523BaseNine.a6X ^ i * SchurPresentation.Theorem523BaseNine.a6Y ^ j := by
  let H : Subgroup (alternatingGroup (Fin 6)) := Subgroup.zpowers SchurPresentation.Theorem523BaseNine.a6X
  let J : Subgroup (alternatingGroup (Fin 6)) := Subgroup.zpowers SchurPresentation.Theorem523BaseNine.a6Y
  have hcomm : ∀ h : H, ∀ j : J, Commute (H.subtype h) (J.subtype j) := by
    intro h j
    change Commute (h : alternatingGroup (Fin 6)) (j : alternatingGroup (Fin 6))
    rcases h.2 with ⟨i, hi⟩
    rcases j.2 with ⟨k, hk⟩
    rw [← hi, ← hk]
    have hxy : Commute SchurPresentation.Theorem523BaseNine.a6X SchurPresentation.Theorem523BaseNine.a6Y :=
      SchurPresentation.Theorem523BaseNine.a6_commute
    exact hxy.zpow_zpow i k
  let product : H × J →* alternatingGroup (Fin 6) :=
    MonoidHom.noncommCoprod H.subtype J.subtype hcomm
  have hrange : product.range =
      SchurPresentation.Theorem523BaseNine.a6StandardNine := by
    change (MonoidHom.noncommCoprod H.subtype J.subtype hcomm).range = _
    rw [MonoidHom.noncommCoprod_range]
    rw [Subgroup.range_subtype, Subgroup.range_subtype,
      ← SchurPresentation.Theorem523BaseNine.a6StandardNine_eq]
  have hg : g.1 ∈ product.range := by
    rw [hrange]
    exact g.2
  obtain ⟨⟨h, j⟩, hij⟩ := hg
  rcases h.2 with ⟨i, hi⟩
  rcases j.2 with ⟨k, hk⟩
  refine ⟨i, k, ?_⟩
  calc
    g.1 = product (h, j) := hij.symm
    _ = h.1 * j.1 := rfl
    _ = SchurPresentation.Theorem523BaseNine.a6X ^ i *
        SchurPresentation.Theorem523BaseNine.a6Y ^ k :=
      congrArg₂ (· * ·) hi.symm hk.symm

end GLS3.Chapter5
/- END Theory.A6StandardNineCoordinates -/

/- BEGIN Theory.A7StandardNineCoordinates -/
namespace GLS3.Chapter5

open SchurPresentation

/-- Every element of the standard elementary abelian subgroup of order nine
in `A₇` has coordinates in the displayed basis. -/
public theorem a7StandardNine_exists_zpow_coordinates
    (g : SchurPresentation.Theorem523BaseNine.a7StandardNine) :
    ∃ i j : ℤ, g.1 = SchurPresentation.Theorem523BaseNine.a7X ^ i *
      SchurPresentation.Theorem523BaseNine.a7Y ^ j := by
  let H : Subgroup (alternatingGroup (Fin 7)) :=
    Subgroup.zpowers SchurPresentation.Theorem523BaseNine.a7X
  let J : Subgroup (alternatingGroup (Fin 7)) :=
    Subgroup.zpowers SchurPresentation.Theorem523BaseNine.a7Y
  have hcomm : ∀ h : H, ∀ j : J, Commute (H.subtype h) (J.subtype j) := by
    intro h j
    change Commute (h : alternatingGroup (Fin 7)) (j : alternatingGroup (Fin 7))
    rcases h.2 with ⟨i, hi⟩
    rcases j.2 with ⟨k, hk⟩
    rw [← hi, ← hk]
    exact SchurPresentation.Theorem523BaseNine.a7_commute.zpow_zpow i k
  let product : H × J →* alternatingGroup (Fin 7) :=
    MonoidHom.noncommCoprod H.subtype J.subtype hcomm
  have hrange : product.range =
      SchurPresentation.Theorem523BaseNine.a7StandardNine := by
    change (MonoidHom.noncommCoprod H.subtype J.subtype hcomm).range = _
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype,
      Subgroup.range_subtype,
      ← SchurPresentation.Theorem523BaseNine.a7StandardNine_eq]
  have hg : g.1 ∈ product.range := by
    rw [hrange]
    exact g.2
  obtain ⟨⟨h, j⟩, hij⟩ := hg
  rcases h.2 with ⟨i, hi⟩
  rcases j.2 with ⟨k, hk⟩
  refine ⟨i, k, ?_⟩
  calc
    g.1 = product (h, j) := hij.symm
    _ = h.1 * j.1 := rfl
    _ = SchurPresentation.Theorem523BaseNine.a7X ^ i *
        SchurPresentation.Theorem523BaseNine.a7Y ^ k :=
      congrArg₂ (· * ·) hi.symm hk.symm

end GLS3.Chapter5
/- END Theory.A7StandardNineCoordinates -/

/- BEGIN Theory.A7StandardNineReflectionNormalForm -/
noncomputable section

namespace GLS3.Chapter5

private abbrev __ch5_A7StandardNineReflectionNormalForm_Perm7 := Equiv.Perm (Fin 7)

@[reducible] private def __ch5_A7StandardNineReflectionNormalForm_a7StandardNineReflection : __ch5_A7StandardNineReflectionNormalForm_Perm7 :=
  Equiv.swap 0 1

private theorem __ch5_A7StandardNineReflectionNormalForm_a7StandardNineReflection_x :
    (MulAut.conjNormal (H := alternatingGroup (Fin 7))
      __ch5_A7StandardNineReflectionNormalForm_a7StandardNineReflection)
        SchurPresentation.Theorem523BaseNine.a7X =
      SchurPresentation.Theorem523BaseNine.a7X⁻¹ := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  fin_cases i <;> decide +kernel

private theorem __ch5_A7StandardNineReflectionNormalForm_a7StandardNineReflection_y :
    (MulAut.conjNormal (H := alternatingGroup (Fin 7))
      __ch5_A7StandardNineReflectionNormalForm_a7StandardNineReflection)
        SchurPresentation.Theorem523BaseNine.a7Y =
      SchurPresentation.Theorem523BaseNine.a7Y := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  fin_cases i <;> decide +kernel

/-- Every non-inner automorphism of `A₇` becomes the fixed reflection on the
standard `E₉` after left multiplication by an inner automorphism. -/
public theorem a7_noninner_standardNine_reflection_normalForm
    (β : MulAut (alternatingGroup (Fin 7)))
    (hβNoninner : ∀ g : alternatingGroup (Fin 7), β ≠ MulAut.conj g) :
    ∃ δ : alternatingGroup (Fin 7),
      let γ := MulAut.conj δ * β
      γ SchurPresentation.Theorem523BaseNine.a7X =
          SchurPresentation.Theorem523BaseNine.a7X⁻¹ ∧
        γ SchurPresentation.Theorem523BaseNine.a7Y =
          SchurPresentation.Theorem523BaseNine.a7Y := by
  obtain ⟨σ, hσ⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
      7 (by norm_num) (by norm_num)).2 β
  have hsign : σ.sign = -1 := by
    rcases Int.units_eq_one_or σ.sign with hone | hneg
    · let g : alternatingGroup (Fin 7) :=
        ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hone⟩
      exfalso
      apply hβNoninner g
      rw [← MulAut.conjNormal_val]
      exact hσ.symm
    · exact hneg
  let δPerm : __ch5_A7StandardNineReflectionNormalForm_Perm7 := __ch5_A7StandardNineReflectionNormalForm_a7StandardNineReflection * σ⁻¹
  have hδ : δPerm ∈ alternatingGroup (Fin 7) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    dsimp [δPerm, __ch5_A7StandardNineReflectionNormalForm_a7StandardNineReflection]
    rw [map_mul, map_inv, Equiv.Perm.sign_swap (by decide), hsign]
    all_goals decide
  let δ : alternatingGroup (Fin 7) := ⟨δPerm, hδ⟩
  refine ⟨δ, ?_⟩
  have hγ : MulAut.conj δ * β =
      MulAut.conjNormal (H := alternatingGroup (Fin 7))
        __ch5_A7StandardNineReflectionNormalForm_a7StandardNineReflection := by
    rw [← hσ]
    change MulAut.conjNormal (H := alternatingGroup (Fin 7)) δ.1 *
        MulAut.conjNormal (H := alternatingGroup (Fin 7)) σ = _
    rw [← map_mul]
    apply congrArg
      (MulAut.conjNormal (H := alternatingGroup (Fin 7)))
    dsimp [δ, δPerm]
    group
  rw [hγ]
  exact ⟨__ch5_A7StandardNineReflectionNormalForm_a7StandardNineReflection_x, __ch5_A7StandardNineReflectionNormalForm_a7StandardNineReflection_y⟩

end GLS3.Chapter5
/- END Theory.A7StandardNineReflectionNormalForm -/

/- BEGIN Theory.QuasisimpleSubnormalCentralizesNormalAbelian -/
namespace GLS3.Chapter5

/-- A quasisimple subnormal subgroup centralizes every normal abelian
subgroup. -/
public theorem commutator_eq_bot_of_isQuasisimple_isSubnormal_normal_abelian
    {G : Type*} [Group G] (R I : Subgroup G)
    [R.Normal] [IsMulCommutative R] [IsQuasisimple I]
    (hI : I.IsSubnormal) :
    ⁅R, I⁆ = ⊥ := by
  let M : Subgroup G := ⁅R, I⁆
  have hMleR : M ≤ R := Subgroup.commutator_le_left R I
  let : IsMulCommutative M := IsMulCommutative.of_comm fun a b => by
    let aR : R := ⟨a.1, hMleR a.2⟩
    let bR : R := ⟨b.1, hMleR b.2⟩
    apply Subtype.ext
    have hab := congrArg (fun z : R => z.1)
      (isMulCommutative_iff.mp (inferInstance : IsMulCommutative R) aR bR)
    simpa [aR, bR] using hab
  by_contra hMne
  exact not_isSubnormal_of_nontrivial_normal_abelian_le_commutator M I
    (Subgroup.normalizer_commutator_ge_right R I) hMne
    (by simpa [M] using commutator_le_iterated_of_isPerfect R I) hI

end GLS3.Chapter5
/- END Theory.QuasisimpleSubnormalCentralizesNormalAbelian -/

/- BEGIN Theory.CyclicFourCentralDecomposition -/
noncomputable section

namespace GLS3.Chapter5

/-- If the center is cyclic of order four, it is the central cyclic factor in
the extraspecial-or-kernel decomposition. -/
public theorem exists_cyclic_four_central_decomposition
    {P V : Type*} [Group P] [Finite P]
    [AddCommGroup V] [Module (ZMod 2) V]
    (hP : IsPGroup 2 P) (q : P →* Multiplicative V)
    (Z : Subgroup P) (hker : q.ker = Z)
    (hZcenter : Z ≤ Subgroup.center P) (hZcard : Nat.card Z = 2)
    (hcenterCyclic : IsCyclic (Subgroup.center P))
    (hcenterCard : Nat.card (Subgroup.center P) = 4) :
    ∃ Z1 R1 : Subgroup P,
      Z1 ⊔ R1 = ⊤ ∧
      (∀ z ∈ Z1, ∀ r ∈ R1, Commute z r) ∧
      Z ≤ R1 ∧
      (IsExtraspecialTwoSubgroup R1 ∨ R1 = Z) ∧
      Z ⊓ Z1 = (frattini Z1).map Z1.subtype ∧
      Nat.card Z1 = 4 ∧ IsCyclic Z1 := by
  let : IsCyclic (Subgroup.center P) := hcenterCyclic
  obtain ⟨R1, hcenterR1, hcenterInfR1, hR1⟩ :=
    exists_central_vector_quotient_factor hP q Z hker hZcenter hZcard
  have hZR1 : Z ≤ R1 := by
    rw [← hcenterInfR1]
    exact inf_le_right
  have hcomm : ∀ z ∈ Subgroup.center P, ∀ r ∈ R1, Commute z r := by
    intro z hz r _
    exact (Subgroup.mem_center_iff.mp hz r).symm
  have hZsubCard : Nat.card (Z.subgroupOf (Subgroup.center P)) = 2 := by
    rw [Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe hZcenter).toEquiv]
    exact hZcard
  have hfrattini : frattini (Subgroup.center P) =
      Z.subgroupOf (Subgroup.center P) :=
    frattini_eq_of_isCyclic_card_four
      (G := Subgroup.center P) (Z.subgroupOf (Subgroup.center P))
      hcenterCard hZsubCard
  have hinterFrattini : Z ⊓ Subgroup.center P =
      (frattini (Subgroup.center P)).map (Subgroup.center P).subtype := by
    rw [hfrattini, Subgroup.map_subgroupOf_eq_of_le hZcenter,
      inf_eq_left.mpr hZcenter]
  exact ⟨Subgroup.center P, R1, hcenterR1, hcomm, hZR1, hR1,
    hinterFrattini, hcenterCard, hcenterCyclic⟩

end GLS3.Chapter5
/- END Theory.CyclicFourCentralDecomposition -/

/- BEGIN Theory.KleinFourCentralDecomposition -/
noncomputable section

namespace GLS3.Chapter5

/-- If the center is an elementary abelian group of order four, split off a
central cyclic factor of order two from the extraspecial-or-kernel factor. -/
public theorem exists_klein_four_central_decomposition
    {P V W : Type*} [Group P] [Finite P]
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (hP : IsPGroup 2 P) (q : P →* Multiplicative V)
    (Z : Subgroup P) (hker : q.ker = Z)
    (hZcenter : Z ≤ Subgroup.center P) (hZcard : Nat.card Z = 2)
    (e : Subgroup.center P ≃* Multiplicative W)
    (hcenterCard : Nat.card (Subgroup.center P) = 4) :
    ∃ Z1 R1 : Subgroup P,
      Z1 ⊔ R1 = ⊤ ∧
      (∀ z ∈ Z1, ∀ r ∈ R1, Commute z r) ∧
      Z ≤ R1 ∧
      (IsExtraspecialTwoSubgroup R1 ∨ R1 = Z) ∧
      Z ⊓ Z1 = (frattini Z1).map Z1.subtype ∧
      Nat.card Z1 = 2 ∧ IsCyclic Z1 := by
  obtain ⟨Z1, hZZ1, hZinfZ1, hZ1center, hZ1card, hZ1cyclic⟩ :=
    exists_order_two_complement_subgroup
      (Subgroup.center P) Z hZcenter e hcenterCard hZcard
  obtain ⟨R1, hcenterR1, hcenterInfR1, hR1⟩ :=
    exists_central_vector_quotient_factor hP q Z hker hZcenter hZcard
  have hZR1 : Z ≤ R1 := by
    rw [← hcenterInfR1]
    exact inf_le_right
  have hsup : Z1 ⊔ R1 = ⊤ := by
    apply top_unique
    rw [← hcenterR1, ← hZZ1]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact hZR1.trans (le_sup_right : R1 ≤ Z1 ⊔ R1)
    · exact (le_sup_left : Z1 ≤ Z1 ⊔ R1)
    · exact (le_sup_right : R1 ≤ Z1 ⊔ R1)
  have hcomm : ∀ z ∈ Z1, ∀ r ∈ R1, Commute z r := by
    intro z hz r _
    exact (Subgroup.mem_center_iff.mp (hZ1center hz) r).symm
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfrattini : frattini Z1 = ⊥ :=
    frattini_eq_bot_of_prime_card hZ1card
  have hinterFrattini : Z ⊓ Z1 = (frattini Z1).map Z1.subtype := by
    rw [hfrattini, Subgroup.map_bot]
    exact hZinfZ1
  exact ⟨Z1, R1, hsup, hcomm, hZR1, hR1, hinterFrattini,
    hZ1card, hZ1cyclic⟩

end GLS3.Chapter5
/- END Theory.KleinFourCentralDecomposition -/

/- BEGIN Theory.OddCenterDecomposition -/
noncomputable section

namespace GLS3.Chapter5

/-- If the center is exactly the distinguished order-two subgroup, the
central cyclic factor is trivial. -/
public theorem exists_odd_center_decomposition
    {P V : Type*} [Group P] [Finite P]
    [AddCommGroup V] [Module (ZMod 2) V]
    (hP : IsPGroup 2 P) (q : P →* Multiplicative V)
    (Z : Subgroup P) (hker : q.ker = Z)
    (hcenter : Subgroup.center P = Z) (hZcard : Nat.card Z = 2) :
    ∃ Z1 R1 : Subgroup P,
      Z1 ⊔ R1 = ⊤ ∧
      (∀ z ∈ Z1, ∀ r ∈ R1, Commute z r) ∧
      Z ≤ R1 ∧
      (IsExtraspecialTwoSubgroup R1 ∨ R1 = Z) ∧
      Z ⊓ Z1 = (frattini Z1).map Z1.subtype ∧
      Nat.card Z1 = 1 ∧ IsCyclic Z1 := by
  have hZcenter : Z ≤ Subgroup.center P := hcenter ▸ le_rfl
  obtain ⟨R1, hcenterR1, hcenterInfR1, hR1⟩ :=
    exists_central_vector_quotient_factor hP q Z hker hZcenter hZcard
  have hZR1 : Z ≤ R1 := by
    rw [← hcenterInfR1]
    exact inf_le_right
  have hZR1sup : Z ⊔ R1 = ⊤ := by
    rw [← hcenter]
    exact hcenterR1
  have hR1top : R1 = ⊤ := by
    calc
      R1 = Z ⊔ R1 := (sup_eq_right.mpr hZR1).symm
      _ = ⊤ := hZR1sup
  have hcomm : ∀ z ∈ (⊥ : Subgroup P), ∀ r ∈ R1, Commute z r := by
    intro z hz r _
    rw [Subgroup.mem_bot.mp hz]
    exact Commute.one_left r
  refine ⟨⊥, R1, ?_, hcomm, hZR1, hR1, ?_, ?_, ?_⟩
  · simp [hR1top]
  · rw [inf_bot_eq]
    apply le_antisymm bot_le
    rintro x ⟨y, _, rfl⟩
    exact y.2
  · exact Subgroup.card_bot
  · infer_instance

end GLS3.Chapter5
/- END Theory.OddCenterDecomposition -/

/- BEGIN Theory.EvenInvolutionCycleRotationEmbedding -/
noncomputable section
namespace GLS3.Chapter5
universe __ch5_EvenInvolutionCycleRotationEmbedding_u

/-- Include the even involution-cycle rotations into the alternating group. -/
@[expose]
public noncomputable def evenInvolutionCycleRotationToAlternating
    {Ω : Type __ch5_EvenInvolutionCycleRotationEmbedding_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) :
    evenInvolutionCycleRotations x →* alternatingGroup Ω where
  toFun a := ⟨(cycleRotationToCentralizer x a.1).1,
    Equiv.Perm.mem_alternatingGroup.mpr
      ((mem_evenInvolutionCycleRotations x a.1).mp a.2)⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

public theorem evenInvolutionCycleRotationToAlternating_injective
    {Ω : Type __ch5_EvenInvolutionCycleRotationEmbedding_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) :
    Function.Injective (evenInvolutionCycleRotationToAlternating x) := by
  intro a b hab
  apply Subtype.ext
  apply cycleRotationToCentralizer_injective x
  apply Subtype.ext
  exact congrArg (fun q : alternatingGroup Ω => q.1) hab

/-- The concrete trace-zero rotation subgroup in the alternating group. -/
@[expose]
public noncomputable def involutionEvenRotationSubgroup
    {Ω : Type __ch5_EvenInvolutionCycleRotationEmbedding_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) : Subgroup (alternatingGroup Ω) :=
  (evenInvolutionCycleRotationToAlternating x).range

/-- The concrete even rotation subgroup has the expected trace-zero model. -/
public noncomputable def involutionEvenRotationSubgroupMulEquivTraceZero
    {Ω : Type __ch5_EvenInvolutionCycleRotationEmbedding_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2) (r : Nat)
    (e : x.cycleFactorsFinset ≃ Fin r) :
    involutionEvenRotationSubgroup x ≃*
      Multiplicative ↥(traceZeroTwoSubgroup r) :=
  (MonoidHom.ofInjective
      (evenInvolutionCycleRotationToAlternating_injective x)).symm.trans
    (evenInvolutionCycleRotations_mulEquiv_traceZero x hx r e)

end GLS3.Chapter5
/- END Theory.EvenInvolutionCycleRotationEmbedding -/

/- BEGIN Theory.InvolutionCyclePermutationEven -/
noncomputable section

namespace GLS3.Chapter5
universe __ch5_InvolutionCyclePermutationEven_u

private theorem __ch5_InvolutionCyclePermutationEven_involutionCyclePermutation_swap_sign
    {Ω : Type __ch5_InvolutionCyclePermutationEven_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2)
    (c d : x.cycleFactorsFinset) (hcd : c ≠ d) :
    Equiv.Perm.sign
      ((theorem_5_2_2_d_3_a x (by simpa [hx] using Nat.prime_two)).symm
        (Equiv.swap c d)).1.1 = 1 := by
  let e := theorem_5_2_2_d_3_a x (by simpa [hx] using Nat.prime_two)
  let l := e.symm (Equiv.swap c d)
  have hl2 : l ^ 2 = 1 := by
    apply e.injective
    simp [l, pow_two]
  have hlPerm2 : l.1.1 ^ 2 = 1 := by
    exact congrArg (fun z : cyclePermutationSubgroup x => z.1.1) hl2
  have hlsupport : l.1.1.support.card = 4 := by
    rcases l.2 with ⟨q, hq⟩
    rw [← hq]
    change (Equiv.Perm.Basis.ofPermHom
      (Classical.choice (Equiv.Perm.Basis.nonempty x))
      (cycleActionRangeToExplicitRange x q)).support.card = 4
    rw [Equiv.Perm.Basis.card_ofPermHom_support]
    have hqval : (q : Equiv.Perm x.cycleFactorsFinset) = Equiv.swap c d := by
      have hel := e.apply_symm_apply (Equiv.swap c d)
      let e1 := cycleActionRangeMulEquivCyclePermutationSubgroup x
      let e2 := cycleActionRangeMulEquivPermOfPrimeOrder x
        (by simpa [hx] using Nat.prime_two)
      have he1 : e1 q = l := by
        apply Subtype.ext
        exact hq
      have hqinv : e1.symm l = q := by
        rw [← he1]
        exact e1.symm_apply_apply q
      calc
        (q : Equiv.Perm x.cycleFactorsFinset) = e2 q := rfl
        _ = e2 (e1.symm l) := congrArg e2 hqinv.symm
        _ = e l := rfl
        _ = Equiv.swap c d := hel
    change ∑ c ∈ (q : Equiv.Perm x.cycleFactorsFinset).support,
        c.1.support.card = 4
    rw [hqval, Equiv.Perm.support_swap hcd]
    simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_singleton,
      hcd, not_false_eq_true]
    rw [cycleFactor_support_card_eq_orderOf_of_primeOrder x
        (by simpa [hx] using Nat.prime_two),
      cycleFactor_support_card_eq_orderOf_of_primeOrder x
        (by simpa [hx] using Nat.prime_two), hx]
  rw [Equiv.Perm.sign_of_pow_two_eq_one hlPerm2]
  have hdiff : Fintype.card Ω -
      Fintype.card (Function.fixedPoints l.1.1) = 4 := by
    rw [Equiv.Perm.card_fixedPoints, Equiv.Perm.sum_cycleType, hlsupport]
    have hle := l.1.1.support.card_le_univ
    rw [hlsupport] at hle
    omega
  rw [hdiff]
  norm_num

/-- Permuting the nontrivial 2-cycles of an involution moves points in pairs,
so the whole cycle-permuting complement consists of even permutations. -/
public theorem involutionCyclePermutation_sign
    {Ω : Type __ch5_InvolutionCyclePermutationEven_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2)
    (l : cyclePermutationSubgroup x) :
    Equiv.Perm.sign l.1.1 = 1 := by
  let e := theorem_5_2_2_d_3_a x (by simpa [hx] using Nat.prime_two)
  have hqsign : ∀ q : Equiv.Perm x.cycleFactorsFinset,
      Equiv.Perm.sign (e.symm q).1.1 = 1 := by
    intro q
    induction q using Equiv.Perm.swap_induction_on with
    | one => simp
    | swap_mul q c d hcd ih =>
        calc
          Equiv.Perm.sign (e.symm (Equiv.swap c d * q)).1.1 =
              Equiv.Perm.sign
                ((e.symm (Equiv.swap c d)).1.1 * (e.symm q).1.1) := by
            rw [map_mul]
            rfl
          _ = 1 := by
            rw [map_mul, __ch5_InvolutionCyclePermutationEven_involutionCyclePermutation_swap_sign x hx c d hcd,
              ih, one_mul]
  simpa using hqsign (e l)

end GLS3.Chapter5
/- END Theory.InvolutionCyclePermutationEven -/

/- BEGIN Theory.InvolutionTwoCycleRotationOrder -/
noncomputable section
namespace GLS3.Chapter5
universe __ch5_InvolutionTwoCycleRotationOrder_u

/-- The alternating permutation induced by rotating two distinct involution
cycles has order two. -/
public theorem involutionTwoCycleRotation_orderOf
    {Ω : Type __ch5_InvolutionTwoCycleRotationOrder_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2)
    (c d : x.cycleFactorsFinset) (hcd : c ≠ d) :
    let v : x.cycleFactorsFinset → Multiplicative (ZMod 2) :=
      fun k => if k = c ∨ k = d then Multiplicative.ofAdd 1 else 1
    let a := (involutionCycleRotationCoordinates x hx).symm v
    let aA : alternatingGroup Ω :=
      ⟨(cycleRotationToCentralizer x a).1,
        Equiv.Perm.mem_alternatingGroup.mpr
          (involutionTwoCycleRotation_sign x hx c d hcd)⟩
    orderOf aA = 2 := by
  dsimp only
  let hp : (orderOf x).Prime := by simpa [hx] using Nat.prime_two
  let v : x.cycleFactorsFinset → Multiplicative (ZMod 2) :=
    fun k => if k = c ∨ k = d then Multiplicative.ofAdd 1 else 1
  let a := (involutionCycleRotationCoordinates x hx).symm v
  let aA : alternatingGroup Ω :=
    ⟨(cycleRotationToCentralizer x a).1,
      Equiv.Perm.mem_alternatingGroup.mpr
        (involutionTwoCycleRotation_sign x hx c d hcd)⟩
  have ha2 : a ^ 2 = 1 := by
    simpa [hx] using cycleRotationGroup_pow_orderOf_eq_one_of_primeOrder x hp a
  have haA2 : aA ^ 2 = 1 := by
    apply Subtype.ext
    change (cycleRotationToCentralizer x a).1 ^ 2 = 1
    rw [cycleRotationToCentralizer_pow_coe x a 2, ha2, map_one]
    rfl
  have haCard : aA.1.support.card = 4 := by
    simpa [aA, a, v] using involutionTwoCycleRotation_support_card x hx c d hcd
  have haNe : aA ≠ 1 := by
    intro h
    have hval : aA.1 = 1 := congrArg Subtype.val h
    rw [hval] at haCard
    simp at haCard
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime haA2 haNe

end GLS3.Chapter5
/- END Theory.InvolutionTwoCycleRotationOrder -/

/- BEGIN Theory.InvolutionRotationDisjointTwoCycle -/
noncomputable section
namespace GLS3.Chapter5
universe __ch5_InvolutionRotationDisjointTwoCycle_u

/-- An involution-cycle rotation whose selected coordinates are trivial has
support disjoint from the rotation on exactly those two cycles. -/
public theorem involutionRotation_disjoint_twoCycleRotation
    {Ω : Type __ch5_InvolutionRotationDisjointTwoCycle_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2)
    (b : CycleRotationGroup x) (c d : x.cycleFactorsFinset)
    (hbc : (involutionCycleRotationCoordinates x hx) b c = 1)
    (hbd : (involutionCycleRotationCoordinates x hx) b d = 1) :
    let v : x.cycleFactorsFinset → Multiplicative (ZMod 2) :=
      fun k => if k = c ∨ k = d then Multiplicative.ofAdd 1 else 1
    let a := (involutionCycleRotationCoordinates x hx).symm v
    Equiv.Perm.Disjoint (cycleRotationToCentralizer x b).1
      (cycleRotationToCentralizer x a).1 := by
  dsimp only
  let hp : (orderOf x).Prime := by simpa [hx] using Nat.prime_two
  let E := involutionCycleRotationCoordinates x hx
  let v : x.cycleFactorsFinset → Multiplicative (ZMod 2) :=
    fun k => if k = c ∨ k = d then Multiplicative.ofAdd 1 else 1
  let a := E.symm v
  have hbc' : b c = 1 := by
    rw [involutionCycleRotationCoordinates_apply] at hbc
    apply ((zmodMulEquivOfGenerator (cycleFactorGenerator_generates c)
      (by simpa [hx] using
        cycleFactorZPowers_card_of_primeOrder x hp c)).symm).injective
    simpa using hbc
  have hbd' : b d = 1 := by
    rw [involutionCycleRotationCoordinates_apply] at hbd
    apply ((zmodMulEquivOfGenerator (cycleFactorGenerator_generates d)
      (by simpa [hx] using
        cycleFactorZPowers_card_of_primeOrder x hp d)).symm).injective
    simpa using hbd
  rw [Equiv.Perm.disjoint_iff_disjoint_support, Finset.disjoint_left]
  intro ω hωb hωa
  have hωunion : ω ∈ c.1.support ∪ d.1.support :=
    involutionTwoCycleRotation_support_le_union x hx c d hωa
  rw [Equiv.Perm.mem_support] at hωb
  apply hωb
  rcases Finset.mem_union.mp hωunion with hωc | hωd
  · obtain ⟨n, hn⟩ := (cycleCoordinateEquiv x hp c).surjective ⟨ω, hωc⟩
    have hnval := congrArg Subtype.val hn
    calc
      (cycleRotationToCentralizer x b).1 ω =
          (cycleRotationToCentralizer x b).1
            (cycleCoordinateEquiv x hp c n).1 := congrArg _ hnval.symm
      _ = (cycleCoordinateEquiv x hp c n).1 := by
        rw [cycleRotationToCentralizer_apply_cycleCoordinate x hp b c n, hbc']
        rfl
      _ = ω := hnval
  · obtain ⟨n, hn⟩ := (cycleCoordinateEquiv x hp d).surjective ⟨ω, hωd⟩
    have hnval := congrArg Subtype.val hn
    calc
      (cycleRotationToCentralizer x b).1 ω =
          (cycleRotationToCentralizer x b).1
            (cycleCoordinateEquiv x hp d n).1 := congrArg _ hnval.symm
      _ = (cycleCoordinateEquiv x hp d n).1 := by
        rw [cycleRotationToCentralizer_apply_cycleCoordinate x hp b d n, hbd']
        rfl
      _ = ω := hnval

end GLS3.Chapter5
/- END Theory.InvolutionRotationDisjointTwoCycle -/

/- BEGIN Theory.MultiplierBounds -/
/- Source: FreeCentralPresentation.lean -/

set_option maxHeartbeats 800000

namespace GLS3.Chapter5.SchurPresentation
universe __ch5_MultiplierBounds_w

open FreeCentralExtension
open scoped commutatorElement

/-- The free group on Suzuki's generators for `A_{n+5}`. -/
public abbrev AlternatingSuzukiFreeGroup (n : Nat) := FreeGroup (Fin (n + 3))

/-- Evaluation of the free Suzuki generators in the alternating group. -/
@[expose]
public def alternatingSuzukiMap (n : Nat) :
    AlternatingSuzukiFreeGroup n →* alternatingGroup (Fin (n + 5)) :=
  FreeGroup.lift (alternatingSuzukiGenerator n)

public theorem alternatingSuzukiMap_surjective (n : Nat) :
    Function.Surjective (alternatingSuzukiMap n) :=
  alternatingSuzukiGenerator_lift_surjective n

/-- The relator subgroup of Suzuki's presentation, defined intrinsically as
the kernel of evaluation. -/
@[expose]
public def alternatingSuzukiKernel (n : Nat) :
    Subgroup (AlternatingSuzukiFreeGroup n) :=
  (alternatingSuzukiMap n).ker

public instance alternatingSuzukiKernelNormal (n : Nat) :
    (alternatingSuzukiKernel n).Normal := by
  dsimp [alternatingSuzukiKernel]
  infer_instance

/-- The quotient by the full relator kernel is the alternating group. -/
@[expose]
public noncomputable def alternatingSuzukiQuotientEquiv (n : Nat) :
    AlternatingSuzukiFreeGroup n ⧸ alternatingSuzukiKernel n ≃*
      alternatingGroup (Fin (n + 5)) :=
  QuotientGroup.quotientKerEquivOfSurjective
    (alternatingSuzukiMap n) (alternatingSuzukiMap_surjective n)

@[simp]
public theorem alternatingSuzukiQuotientEquiv_mk (n : Nat)
    (x : AlternatingSuzukiFreeGroup n) :
    alternatingSuzukiQuotientEquiv n
      (QuotientGroup.mk' (alternatingSuzukiKernel n) x) =
        alternatingSuzukiMap n x := by
  rfl

/-- A1 33.4 / Suzuki 9.2's free central extension attached to the Suzuki
presentation of the alternating group. -/
public abbrev AlternatingFreeCentralGroup (n : Nat) :=
  AlternatingSuzukiFreeGroup n ⧸
    freeCentralKernel (alternatingSuzukiKernel n)

/-- The natural central extension from the presentation-level group to
`A_{n+5}`. -/
@[expose]
public noncomputable def alternatingFreeCentralProjection (n : Nat) :
    AlternatingFreeCentralGroup n →* alternatingGroup (Fin (n + 5)) :=
  (alternatingSuzukiQuotientEquiv n).toMonoidHom.comp
    (freeCentralProjection (alternatingSuzukiKernel n))

public theorem alternatingFreeCentralProjection_surjective (n : Nat) :
    Function.Surjective (alternatingFreeCentralProjection n) :=
  (alternatingSuzukiQuotientEquiv n).surjective.comp
    (freeCentralProjection_surjective (alternatingSuzukiKernel n))

public theorem alternatingFreeCentralProjection_ker_le_center (n : Nat) :
    (alternatingFreeCentralProjection n).ker ≤
      Subgroup.center (AlternatingFreeCentralGroup n) := by
  have hker : (alternatingFreeCentralProjection n).ker =
      (freeCentralProjection (alternatingSuzukiKernel n)).ker := by
    exact MonoidHom.ker_comp_of_injective
      (freeCentralProjection (alternatingSuzukiKernel n))
      (alternatingSuzukiQuotientEquiv n).toMonoidHom
      (alternatingSuzukiQuotientEquiv n).injective
  rw [hker]
  exact freeCentralProjection_ker_le_center (alternatingSuzukiKernel n)

/-- A1 33.4 takes the derived subgroup of the free central extension. -/
public abbrev AlternatingFreeCentralDerived (n : Nat) :=
  commutator (AlternatingFreeCentralGroup n)

/-- Restriction of the free central projection to its derived subgroup. -/
@[expose]
public noncomputable def alternatingFreeCentralDerivedProjection (n : Nat) :
    AlternatingFreeCentralDerived n →* alternatingGroup (Fin (n + 5)) :=
  (alternatingFreeCentralProjection n).comp
    (AlternatingFreeCentralDerived n).subtype

/-- A1 33.3: since the alternating group is perfect, the derived subgroup of
any central extension still maps onto it. -/
public theorem alternatingFreeCentralDerivedProjection_surjective (n : Nat) :
    Function.Surjective (alternatingFreeCentralDerivedProjection n) := by
  let E := AlternatingFreeCentralGroup n
  let f := alternatingFreeCentralProjection n
  have hfRange : f.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (alternatingFreeCentralProjection_surjective n)
  have hmap : (commutator E).map f = ⊤ := by
    rw [map_commutator_eq, hfRange]
    exact Group.IsPerfect.commutator_eq_top
  intro y
  have hy : y ∈ (commutator E).map f := by
    rw [hmap]
    trivial
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨⟨x, hx⟩, hxy⟩

public theorem alternatingFreeCentralDerivedProjection_ker_le_center (n : Nat) :
    (alternatingFreeCentralDerivedProjection n).ker ≤
      Subgroup.center (AlternatingFreeCentralDerived n) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have hx' : (x : AlternatingFreeCentralGroup n) ∈
      (alternatingFreeCentralProjection n).ker := by
    exact hx
  exact Subgroup.mem_center_iff.mp
    (alternatingFreeCentralProjection_ker_le_center n hx') y

public theorem ker_eq_center_of_surjective_of_center_eq_bot
    {E B : Type*} [Group E] [Group B]
    (f : E →* B) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center E)
    (hcenter : Subgroup.center B = ⊥) :
    f.ker = Subgroup.center E := by
  apply le_antisymm hker
  intro z hz
  rw [MonoidHom.mem_ker]
  have hfz : f z ∈ Subgroup.center B := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := hf y
    simpa only [map_mul] using congrArg f (Subgroup.mem_center_iff.mp hz x)
  rw [hcenter, Subgroup.mem_bot] at hfz
  exact hfz

private theorem __ch5_MultiplierBounds_commutatorElement_mul_center
    {E : Type*} [Group E] (kx ky dx dy : E)
    (hkx : kx ∈ Subgroup.center E) (hky : ky ∈ Subgroup.center E) :
    ⁅kx * dx, ky * dy⁆ = ⁅dx, dy⁆ := by
  have hkxComm (z : E) : Commute kx z := by
    change kx * z = z * kx
    exact (Subgroup.mem_center_iff.mp hkx z).symm
  have hkyComm (z : E) : Commute ky z := by
    change ky * z = z * ky
    exact (Subgroup.mem_center_iff.mp hky z).symm
  calc
    ⁅kx * dx, ky * dy⁆ =
        kx * ⁅dx, ky * dy⁆ * kx⁻¹ * ⁅kx, ky * dy⁆ :=
      commutatorElement_mul_left_eq_conj_mul kx dx (ky * dy)
    _ = ⁅dx, ky * dy⁆ := by
      rw [(hkxComm (ky * dy)).commutator_eq]
      simp [(hkxComm ⁅dx, ky * dy⁆).eq, mul_assoc]
    _ = ⁅dx, ky⁆ * ky * ⁅dx, dy⁆ * ky⁻¹ :=
      commutatorElement_mul_right_eq_mul_conj dx ky dy
    _ = ⁅dx, dy⁆ := by
      rw [(hkyComm dx).symm.commutator_eq]
      simp [(hkyComm ⁅dx, dy⁆).eq, mul_assoc]

/-- A1 33.3: the derived subgroup of a central extension of a perfect group
is itself perfect. -/
public theorem commutator_isPerfect_of_surjective_of_ker_le_center
    {E B : Type*} [Group E] [Group B] [Group.IsPerfect B]
    (f : E →* B) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center E) :
    Group.IsPerfect (commutator E) := by
  let D := commutator E
  have hmap : D.map f = ⊤ := by
    dsimp [D]
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf]
    exact Group.IsPerfect.commutator_eq_top
  have hdecomp (x : E) :
      ∃ k ∈ f.ker, ∃ d ∈ D, x = k * d := by
    have hx : f x ∈ D.map f := by
      rw [hmap]
      trivial
    obtain ⟨d, hd, hdx⟩ := hx
    refine ⟨x * d⁻¹, ?_, d, hd, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, map_inv, hdx]
      simp
    · simp
  change Group.IsPerfect D
  rw [Subgroup.isPerfect_iff]
  apply le_antisymm
  · exact Subgroup.commutator_le_left D D
  · dsimp [D]
    rw [commutator_eq_closure, Subgroup.closure_le]
    intro z hz
    obtain ⟨x, y, hxy⟩ := mem_commutatorSet_iff.mp hz
    obtain ⟨kx, hkx, dx, hdx, rfl⟩ := hdecomp x
    obtain ⟨ky, hky, dy, hdy, rfl⟩ := hdecomp y
    have hdx' : dx ∈ commutator E := by simpa [D] using hdx
    have hdy' : dy ∈ commutator E := by simpa [D] using hdy
    have hdx'' : dx ∈ Subgroup.closure (commutatorSet E) := by
      rw [← commutator_eq_closure]
      exact hdx'
    have hdy'' : dy ∈ Subgroup.closure (commutatorSet E) := by
      rw [← commutator_eq_closure]
      exact hdy'
    rw [← hxy, __ch5_MultiplierBounds_commutatorElement_mul_center kx ky dx dy (hker hkx) (hker hky)]
    exact Subgroup.commutator_mem_commutator hdx'' hdy''

/-- A1 33.9 in the form needed here: if a group has a finite central
quotient, then its derived subgroup is finite. -/
public theorem finite_commutator_of_surjective_of_ker_le_center
    {E B : Type*} [Group E] [Group B] [Finite B]
    (f : E →* B) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center E) :
    Finite (commutator E) := by
  let s : B → E := fun b => Classical.choose (hf b)
  have hs (b : B) : f (s b) = b := Classical.choose_spec (hf b)
  let φ : B × B → commutatorSet E := fun p =>
    ⟨⁅s p.1, s p.2⁆,
      commutator_mem_commutatorSet (s p.1) (s p.2)⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨z, hz⟩
    obtain ⟨x, y, hxy⟩ := mem_commutatorSet_iff.mp hz
    let kx := x * (s (f x))⁻¹
    let ky := y * (s (f y))⁻¹
    have hkx : kx ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      change f (x * (s (f x))⁻¹) = 1
      rw [map_mul, map_inv, hs]
      simp
    have hky : ky ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      change f (y * (s (f y))⁻¹) = 1
      rw [map_mul, map_inv, hs]
      simp
    have hx : x = kx * s (f x) := by simp [kx]
    have hy : y = ky * s (f y) := by simp [ky]
    refine ⟨(f x, f y), ?_⟩
    apply Subtype.ext
    change ⁅s (f x), s (f y)⁆ = z
    rw [← hxy]
    calc
      ⁅s (f x), s (f y)⁆ =
          ⁅kx * s (f x), ky * s (f y)⁆ :=
        (__ch5_MultiplierBounds_commutatorElement_mul_center kx ky (s (f x)) (s (f y))
          (hker hkx) (hker hky)).symm
      _ = ⁅x, y⁆ := by rw [← hx, ← hy]
  let : Finite (commutatorSet E) := Finite.of_surjective φ hφ
  infer_instance

public instance alternatingFreeCentralDerivedIsPerfect (n : Nat) :
    Group.IsPerfect (AlternatingFreeCentralDerived n) :=
  commutator_isPerfect_of_surjective_of_ker_le_center
    (alternatingFreeCentralProjection n)
    (alternatingFreeCentralProjection_surjective n)
    (alternatingFreeCentralProjection_ker_le_center n)

public instance alternatingFreeCentralDerivedFinite (n : Nat) :
    Finite (AlternatingFreeCentralDerived n) :=
  finite_commutator_of_surjective_of_ker_le_center
    (alternatingFreeCentralProjection n)
    (alternatingFreeCentralProjection_surjective n)
    (alternatingFreeCentralProjection_ker_le_center n)

public theorem alternatingFreeCentralDerivedProjection_ker_eq_center (n : Nat) :
    (alternatingFreeCentralDerivedProjection n).ker =
      Subgroup.center (AlternatingFreeCentralDerived n) := by
  apply ker_eq_center_of_surjective_of_center_eq_bot
    (alternatingFreeCentralDerivedProjection n)
    (alternatingFreeCentralDerivedProjection_surjective n)
    (alternatingFreeCentralDerivedProjection_ker_le_center n)
  exact alternatingGroup.center_eq_bot (by simp)

@[expose]
public noncomputable def alternatingFreeCentralDerivedCenterQuotientEquiv (n : Nat) :
    AlternatingFreeCentralDerived n ⧸
        Subgroup.center (AlternatingFreeCentralDerived n) ≃*
      alternatingGroup (Fin (n + 5)) :=
  (QuotientGroup.quotientMulEquivOfEq
      (alternatingFreeCentralDerivedProjection_ker_eq_center n).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (alternatingFreeCentralDerivedProjection n)
      (alternatingFreeCentralDerivedProjection_surjective n))

public instance alternatingFreeCentralDerivedIsQuasisimple (n : Nat) :
    IsQuasisimple (AlternatingFreeCentralDerived n) where
  toIsPerfect := alternatingFreeCentralDerivedIsPerfect n
  simple := by
    let : IsSimpleGroup (alternatingGroup (Fin (n + 5))) :=
      alternatingGroup.isSimpleGroup (by simp)
    exact (alternatingFreeCentralDerivedCenterQuotientEquiv n).isSimpleGroup

/-- A1 33.4's finite perfect universal-cover candidate, now packaged in the
project's covering API. -/
@[expose]
public noncomputable def alternatingFreeCentralCovering (n : Nat) :
    Covering (AlternatingFreeCentralDerived n)
      (alternatingGroup (Fin (n + 5))) where
  toMonoidHom := alternatingFreeCentralDerivedProjection n
  surjective := alternatingFreeCentralDerivedProjection_surjective n

/-- A1 33.4 uniqueness core: two maps from a perfect group to a central
extension that agree after projection are equal. -/
public theorem monoidHom_eq_of_isPerfect_of_comp_eq
    {L M B : Type*} [Group L] [Group.IsPerfect L] [Group M] [Group B]
    (g : M →* B) (hker : g.ker ≤ Subgroup.center M)
    (h₁ h₂ : L →* M) (hfac : g.comp h₁ = g.comp h₂) :
    h₁ = h₂ := by
  apply MonoidHom.eq_of_eqOn_dense
    (s := commutatorSet L)
  · rw [← commutator_eq_closure]
    exact Group.IsPerfect.commutator_eq_top
  · intro z hz
    obtain ⟨x, y, rfl⟩ := mem_commutatorSet_iff.mp hz
    have hfacx := congrArg (fun f : L →* B => f x) hfac
    have hfacy := congrArg (fun f : L →* B => f y) hfac
    let kx := h₁ x * (h₂ x)⁻¹
    let ky := h₁ y * (h₂ y)⁻¹
    have hkx : kx ∈ g.ker := by
      rw [MonoidHom.mem_ker]
      change g (h₁ x * (h₂ x)⁻¹) = 1
      rw [map_mul, map_inv]
      change g (h₁ x) * (g (h₂ x))⁻¹ = 1
      change g (h₁ x) = g (h₂ x) at hfacx
      rw [hfacx]
      simp
    have hky : ky ∈ g.ker := by
      rw [MonoidHom.mem_ker]
      change g (h₁ y * (h₂ y)⁻¹) = 1
      rw [map_mul, map_inv]
      change g (h₁ y) * (g (h₂ y))⁻¹ = 1
      change g (h₁ y) = g (h₂ y) at hfacy
      rw [hfacy]
      simp
    have hx : h₁ x = kx * h₂ x := by simp [kx]
    have hy : h₁ y = ky * h₂ y := by simp [ky]
    simp only [map_commutatorElement]
    rw [hx, hy, __ch5_MultiplierBounds_commutatorElement_mul_center kx ky (h₂ x) (h₂ y)
      (hker hkx) (hker hky)]

/-- A1 33.6: a morphism onto a perfect central extension is surjective. -/
public theorem surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
    {L M B : Type*} [Group L] [Group M] [Group.IsPerfect M] [Group B]
    (g : M →* B) (h : L →* M)
    (hcomp : Function.Surjective (g.comp h))
    (hker : g.ker ≤ Subgroup.center M) :
    Function.Surjective h := by
  have hdecomp (x : M) :
      ∃ k ∈ g.ker, ∃ l : L, x = k * h l := by
    obtain ⟨l, hl⟩ := hcomp (g x)
    refine ⟨x * (h l)⁻¹, ?_, l, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, map_inv]
      change g x * (g (h l))⁻¹ = 1
      change g (h l) = g x at hl
      rw [hl]
      simp
    · simp
  rw [← MonoidHom.range_eq_top]
  apply top_unique
  rw [← Group.IsPerfect.commutator_eq_top,
    commutator_eq_closure, Subgroup.closure_le]
  intro z hz
  obtain ⟨x, y, hxy⟩ := mem_commutatorSet_iff.mp hz
  obtain ⟨kx, hkx, lx, hx⟩ := hdecomp x
  obtain ⟨ky, hky, ly, hy⟩ := hdecomp y
  rw [← hxy, hx, hy,
    __ch5_MultiplierBounds_commutatorElement_mul_center kx ky (h lx) (h ly)
      (hker hkx) (hker hky), ← map_commutatorElement]
  exact ⟨⁅lx, ly⁆, rfl⟩

section Lift

variable {M : Type*} [Group M] [Finite M] [IsQuasisimple M]

/-- Choose lifts of Suzuki's generators through an arbitrary covering and
extend them freely. -/
@[expose]
public noncomputable def alternatingSuzukiFreeLift (n : Nat)
    (g : Covering M (alternatingGroup (Fin (n + 5)))) :
    AlternatingSuzukiFreeGroup n →* M :=
  FreeGroup.lift (DoubleCoverUniqueness.suzukiLift n g)

public theorem alternatingSuzukiFreeLift_fac (n : Nat)
    (g : Covering M (alternatingGroup (Fin (n + 5)))) :
    g.toMonoidHom.comp (alternatingSuzukiFreeLift n g) =
      alternatingSuzukiMap n := by
  ext i
  simp [alternatingSuzukiFreeLift, alternatingSuzukiMap,
    DoubleCoverUniqueness.suzukiLift_apply]

/-- Relators of the alternating group evaluate under arbitrary chosen lifts
into the central kernel of the covering. -/
public theorem alternatingSuzukiFreeLift_kernel_mem_center (n : Nat)
    (g : Covering M (alternatingGroup (Fin (n + 5))))
    {k : AlternatingSuzukiFreeGroup n} (hk : k ∈ alternatingSuzukiKernel n) :
    alternatingSuzukiFreeLift n g k ∈ Subgroup.center M := by
  apply g.ker_le_center
  rw [MonoidHom.mem_ker]
  have hfac := congrArg
    (fun f : AlternatingSuzukiFreeGroup n →*
      alternatingGroup (Fin (n + 5)) => f k)
    (alternatingSuzukiFreeLift_fac n g)
  simpa [alternatingSuzukiKernel, MonoidHom.mem_ker] using hfac.trans hk

/-- Suzuki 9.2(4): `[F,K]` is killed by every lift to a central extension. -/
public theorem freeCentralKernel_le_ker_alternatingSuzukiFreeLift (n : Nat)
    (g : Covering M (alternatingGroup (Fin (n + 5)))) :
    freeCentralKernel (alternatingSuzukiKernel n) ≤
      (alternatingSuzukiFreeLift n g).ker := by
  rw [freeCentralKernel, Subgroup.commutator_le]
  intro x _hx k hk
  rw [MonoidHom.mem_ker, map_commutatorElement]
  apply commutatorElement_eq_one_iff_commute.mpr
  change alternatingSuzukiFreeLift n g x * alternatingSuzukiFreeLift n g k =
    alternatingSuzukiFreeLift n g k * alternatingSuzukiFreeLift n g x
  exact (Subgroup.mem_center_iff.mp
    (alternatingSuzukiFreeLift_kernel_mem_center n g hk)
    (alternatingSuzukiFreeLift n g x))

/-- The free lift descends to the free central extension. -/
@[expose]
public noncomputable def alternatingFreeCentralLift (n : Nat)
    (g : Covering M (alternatingGroup (Fin (n + 5)))) :
    AlternatingFreeCentralGroup n →* M :=
  QuotientGroup.lift (freeCentralKernel (alternatingSuzukiKernel n))
    (alternatingSuzukiFreeLift n g)
    (freeCentralKernel_le_ker_alternatingSuzukiFreeLift n g)

public theorem alternatingFreeCentralLift_fac (n : Nat)
    (g : Covering M (alternatingGroup (Fin (n + 5)))) :
    g.toMonoidHom.comp (alternatingFreeCentralLift n g) =
      alternatingFreeCentralProjection n := by
  apply MonoidHom.ext
  intro x
  refine QuotientGroup.induction_on x ?_
  intro y
  have hfac := congrArg
    (fun f : AlternatingSuzukiFreeGroup n →*
      alternatingGroup (Fin (n + 5)) => f y)
    (alternatingSuzukiFreeLift_fac n g)
  change g (alternatingSuzukiFreeLift n g y) =
    alternatingSuzukiQuotientEquiv n
      (QuotientGroup.mk' (alternatingSuzukiKernel n) y)
  rw [alternatingSuzukiQuotientEquiv_mk]
  exact hfac

/-- Restriction of the descended lift to A1's derived universal candidate. -/
@[expose]
public noncomputable def alternatingFreeCentralDerivedLift (n : Nat)
    (g : Covering M (alternatingGroup (Fin (n + 5)))) :
    AlternatingFreeCentralDerived n →* M :=
  (alternatingFreeCentralLift n g).comp
    (AlternatingFreeCentralDerived n).subtype

public theorem alternatingFreeCentralDerivedLift_fac (n : Nat)
    (g : Covering M (alternatingGroup (Fin (n + 5)))) :
    g.toMonoidHom.comp (alternatingFreeCentralDerivedLift n g) =
      alternatingFreeCentralDerivedProjection n := by
  rw [alternatingFreeCentralDerivedLift,
    alternatingFreeCentralDerivedProjection, ← MonoidHom.comp_assoc,
    alternatingFreeCentralLift_fac]

public theorem alternatingFreeCentralDerivedLift_surjective (n : Nat)
    (g : Covering M (alternatingGroup (Fin (n + 5)))) :
    Function.Surjective (alternatingFreeCentralDerivedLift n g) := by
  apply surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
    g.toMonoidHom (alternatingFreeCentralDerivedLift n g)
  · rw [alternatingFreeCentralDerivedLift_fac]
    exact alternatingFreeCentralDerivedProjection_surjective n
  · exact g.ker_le_center

@[expose]
public noncomputable def alternatingFreeCentralCoveringLift (n : Nat)
    (g : Covering M (alternatingGroup (Fin (n + 5)))) :
    Covering (AlternatingFreeCentralDerived n) M where
  toMonoidHom := alternatingFreeCentralDerivedLift n g
  surjective := alternatingFreeCentralDerivedLift_surjective n g

public theorem alternatingFreeCentralCoveringLift_fac (n : Nat)
    (g : Covering M (alternatingGroup (Fin (n + 5)))) :
    g.comp (alternatingFreeCentralCoveringLift n g) =
      alternatingFreeCentralCovering n := by
  apply Covering.ext
  intro x
  have hfac := congrArg
    (fun f : AlternatingFreeCentralDerived n →*
      alternatingGroup (Fin (n + 5)) => f x)
    (alternatingFreeCentralDerivedLift_fac n g)
  exact hfac

public theorem alternatingFreeCentralDerivedLift_unique (n : Nat)
    (g : Covering M (alternatingGroup (Fin (n + 5))))
    (h : AlternatingFreeCentralDerived n →* M)
    (hh : g.toMonoidHom.comp h =
      alternatingFreeCentralDerivedProjection n) :
    h = alternatingFreeCentralDerivedLift n g := by
  apply monoidHom_eq_of_isPerfect_of_comp_eq
    g.toMonoidHom g.ker_le_center
  exact hh.trans (alternatingFreeCentralDerivedLift_fac n g).symm

end Lift

/-- A1 33.4: the derived subgroup of the free central extension is the
universal covering group of `A_{n+5}`. -/
public theorem alternatingFreeCentralCovering_isUniversal (n : Nat) :
    Covering.IsUniversal.{0, 0, __ch5_MultiplierBounds_w} (alternatingFreeCentralCovering n) := by
  intro M _instGroup _instFinite _instQuasisimple g
  refine ⟨alternatingFreeCentralCoveringLift n g,
    alternatingFreeCentralCoveringLift_fac n g, ?_⟩
  intro h hh
  apply Covering.ext
  intro x
  have hhom : h.toMonoidHom =
      (alternatingFreeCentralCoveringLift n g).toMonoidHom := by
    apply alternatingFreeCentralDerivedLift_unique n g h.toMonoidHom
    have hfac := congrArg
      (fun f : Covering (AlternatingFreeCentralDerived n)
        (alternatingGroup (Fin (n + 5))) => f.toMonoidHom) hh
    exact hfac
  exact DFunLike.congr_fun hhom x

end GLS3.Chapter5.SchurPresentation

/- Source: MultiplierBounds.lean -/

set_option maxHeartbeats 800000

namespace GLS3.Chapter5.SchurPresentation

open scoped commutatorElement

open RootFourSubgroup

/-- The standard double cover is a quotient of A1's universal covering, so
the Schur multiplier of every `A_{n+5}` has cardinality at least two. -/
public theorem two_le_natCard_ker_alternatingFreeCentralCovering (n : Nat) :
    2 ≤ Nat.card (alternatingFreeCentralCovering n).toMonoidHom.ker := by
  have hle := Covering.coveringKernel_card_le_of_universal
    (alternatingFreeCentralCovering n)
    (alternatingFreeCentralCovering_isUniversal n)
    (schurAlternatingCovering n)
  rw [natCard_ker_schurAlternatingCovering] at hle
  exact hle

/-- Stronger divisibility form of the same lower bound. -/
public theorem two_dvd_natCard_ker_alternatingFreeCentralCovering (n : Nat) :
    2 ∣ Nat.card (alternatingFreeCentralCovering n).toMonoidHom.ker := by
  let h := Covering.IsUniversal.lift
    (alternatingFreeCentralCovering_isUniversal n)
    (schurAlternatingCovering n)
  let φ : (alternatingFreeCentralCovering n).toMonoidHom.ker →*
      (schurAlternatingCovering n).toMonoidHom.ker :=
    (h.toMonoidHom.comp
      (alternatingFreeCentralCovering n).toMonoidHom.ker.subtype).codRestrict
      (schurAlternatingCovering n).toMonoidHom.ker (by
        intro x
        rw [MonoidHom.mem_ker]
        change schurAlternatingCovering n (h x.1) = 1
        have hfac (z : AlternatingFreeCentralDerived n) :
            schurAlternatingCovering n (h z) =
              alternatingFreeCentralCovering n z := by
          simpa [h] using DFunLike.congr_fun
            (Covering.IsUniversal.lift_fac
              (alternatingFreeCentralCovering_isUniversal n)
              (schurAlternatingCovering n)) z
        rw [hfac]
        exact MonoidHom.mem_ker.mp x.2)
  have hφ : Function.Surjective φ := by
    intro y
    have hy : y.1 ∈ Subgroup.map h.toMonoidHom
        (alternatingFreeCentralCovering n).toMonoidHom.ker := by
      rw [Covering.coveringKernel_image_of_universal
        (alternatingFreeCentralCovering n)
        (alternatingFreeCentralCovering_isUniversal n)
        (schurAlternatingCovering n)]
      exact y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy
  have hdvd := Subgroup.card_dvd_of_surjective φ hφ
  rw [natCard_ker_schurAlternatingCovering] at hdvd
  exact hdvd

/-- If `m < 2p`, then a factorial contains at most one factor of the prime
`p`. -/
private theorem __ch5_MultiplierBounds_prime_sq_not_dvd_factorial_of_lt_two_mul
    {m p : Nat} (hp : p.Prime) (hmpos : m ≠ 0) (hmp : m < 2 * p) :
    ¬ p ^ 2 ∣ m.factorial := by
  have hmpow : m < p ^ 2 := by
    calc
      m < 2 * p := hmp
      _ ≤ p * p := Nat.mul_le_mul_right p hp.two_le
      _ = p ^ 2 := by simp [pow_two]
  have hlog : Nat.log p m < 2 := Nat.log_lt_of_lt_pow hmpos hmpow
  rw [hp.pow_dvd_factorial_iff hlog]
  norm_num [Finset.sum_Ico_eq_sub]
  have hdiv : m / p < 2 := (Nat.div_lt_iff_lt_mul hp.pos).mpr hmp
  omega

/-- A1 33.16's local permutation-group input: when `m < 2p`, every Sylow
`p`-subgroup of `A_m` is cyclic. -/
public theorem isCyclic_sylow_alternatingGroup_of_lt_two_mul
    {m p : Nat} [Fact p.Prime] (hm : 5 ≤ m) (hmp : m < 2 * p)
    (P : Sylow p (alternatingGroup (Fin m))) : IsCyclic P := by
  let : Nontrivial (Fin m) :=
    Finite.one_lt_card_iff_nontrivial.mp (by simp; omega)
  have hp2fact : ¬ p ^ 2 ∣ m.factorial :=
    __ch5_MultiplierBounds_prime_sq_not_dvd_factorial_of_lt_two_mul
      (Fact.out : p.Prime) (by omega) hmp
  have hcardA_dvd : Nat.card (alternatingGroup (Fin m)) ∣ m.factorial := by
    refine ⟨2, ?_⟩
    rw [Nat.mul_comm, two_mul_nat_card_alternatingGroup, Nat.card_perm]
    simp
  obtain ⟨k, hPk⟩ := P.isPGroup'.exists_card_eq
  have hk : k ≤ 1 := by
    by_contra hknot
    have htwo : 2 ≤ k := by omega
    apply hp2fact
    have hp2P : p ^ 2 ∣ Nat.card P := by
      rw [hPk]
      exact pow_dvd_pow p htwo
    exact hp2P.trans
      ((Subgroup.card_subgroup_dvd_card
        (P : Subgroup (alternatingGroup (Fin m)))).trans hcardA_dvd)
  apply isCyclic_of_card_dvd_prime (p := p)
  rw [hPk]
  interval_cases k <;> simp

/-- A1 33.16 for A1's universal covering of `A_{n+5}`: every prime divisor
of its kernel satisfies `2p ≤ n+5`. -/
public theorem two_mul_prime_le_degree_of_dvd_natCard_ker_alternatingFreeCentralCovering
    (n p : Nat) [Fact p.Prime]
    (hpker : p ∣ Nat.card
      (alternatingFreeCentralCovering n).toMonoidHom.ker) :
    2 * p ≤ n + 5 := by
  by_contra hnot
  have hlt : n + 5 < 2 * p := by omega
  apply not_dvd_card_ker_of_isCyclic_sylow
    (alternatingFreeCentralCovering n).toMonoidHom
    (alternatingFreeCentralCovering n).surjective
    (alternatingFreeCentralCovering n).ker_le_center
    (fun P => isCyclic_sylow_alternatingGroup_of_lt_two_mul (by omega) hlt P)
  exact hpker

private theorem __ch5_MultiplierBounds_closure_pair_cases_of_sq_eq_one_of_commute
    {G : Type*} [Group G] (u v x : G)
    (hu : u * u = 1) (hv : v * v = 1) (huv : Commute u v)
    (hx : x ∈ Subgroup.closure ({u, v} : Set G)) :
    x = 1 ∨ x = u ∨ x = v ∨ x = u * v := by
  refine Subgroup.closure_induction (p := fun x _ => x = 1 ∨ x = u ∨ x = v ∨ x = u * v)
    (fun y hy => ?_) ?_ (fun y z _ _ hy hz => ?_) (fun y _ hy => ?_) hx
  · rcases hy with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inl rfl
  · rcases hy with hy | hy | hy | hy
    all_goals subst y
    · simpa using hz
    · rcases hz with hz | hz | hz | hz
      all_goals subst z
      · exact Or.inr (Or.inl (mul_one u))
      · exact Or.inl hu
      · exact Or.inr (Or.inr (Or.inr rfl))
      · right; right; left
        calc
          u * (u * v) = (u * u) * v := by rw [mul_assoc]
          _ = v := by rw [hu, one_mul]
    · rcases hz with hz | hz | hz | hz
      all_goals subst z
      · exact Or.inr (Or.inr (Or.inl (mul_one v)))
      · right; right; right
        exact huv.eq.symm
      · exact Or.inl hv
      · right; left
        calc
          v * (u * v) = (v * u) * v := by rw [mul_assoc]
          _ = (u * v) * v := by rw [huv.eq]
          _ = u * (v * v) := by rw [mul_assoc]
          _ = u := by rw [hv, mul_one]
    · rcases hz with hz | hz | hz | hz
      all_goals subst z
      · exact Or.inr (Or.inr (Or.inr (mul_one (u * v))))
      · right; right; left
        calc
          (u * v) * u = u * (v * u) := by rw [mul_assoc]
          _ = u * (u * v) := by rw [huv.eq]
          _ = (u * u) * v := by rw [mul_assoc]
          _ = v := by rw [hu, one_mul]
      · right; left
        calc
          (u * v) * v = u * (v * v) := by rw [mul_assoc]
          _ = u := by rw [hv, mul_one]
      · left
        calc
          (u * v) * (u * v) = u * (v * u) * v := by simp [mul_assoc]
          _ = u * (u * v) * v := by rw [huv.eq]
          _ = (u * u) * (v * v) := by simp [mul_assoc]
          _ = 1 := by rw [hu, hv, one_mul]
  · rcases hy with rfl | rfl | rfl | rfl
    · exact Or.inl (inv_one)
    · right; left
      exact (eq_inv_of_mul_eq_one_right hu).symm
    · right; right; left
      exact (eq_inv_of_mul_eq_one_right hv).symm
    · right; right; right
      rw [mul_inv_rev]
      have hui : u⁻¹ = u := (eq_inv_of_mul_eq_one_right hu).symm
      have hvi : v⁻¹ = v := (eq_inv_of_mul_eq_one_right hv).symm
      rw [hui, hvi, huv.eq]

private theorem __ch5_MultiplierBounds_card_closure_pair_le_four_of_sq_eq_one_of_commute
    {G : Type*} [Group G] (a b : G)
    (ha : a * a = 1) (hb : b * b = 1) (hab : Commute a b) :
    Nat.card (Subgroup.closure ({a, b} : Set G)) ≤ 4 := by
  let e : Fin 4 → Subgroup.closure ({a, b} : Set G) := fun i =>
    match i with
    | ⟨0, _⟩ => 1
    | ⟨1, _⟩ => ⟨a, Subgroup.subset_closure (by simp)⟩
    | ⟨2, _⟩ => ⟨b, Subgroup.subset_closure (by simp)⟩
    | ⟨3, _⟩ => ⟨a * b, Subgroup.mul_mem _
        (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))⟩
    | ⟨n + 4, hn⟩ => by omega
  have he : Function.Surjective e := by
    rintro ⟨x, hx⟩
    rcases __ch5_MultiplierBounds_closure_pair_cases_of_sq_eq_one_of_commute a b x ha hb hab hx with
      rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  simpa using Nat.card_le_card_of_surjective e he

private theorem __ch5_MultiplierBounds_sq_eq_sq_of_apply_eq_of_card_ker_two
    {H G : Type*} [Group H] [Finite H] [Group G]
    (f : H →* G) (hker : f.ker ≤ Subgroup.center H)
    (hcard : Nat.card f.ker = 2) {x y : H} (hxy : f x = f y) :
    x ^ 2 = y ^ 2 := by
  let k := x * y⁻¹
  have hk : k ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy]
    simp
  have hk2 : k ^ 2 = 1 := by
    have h := pow_card_eq_one' (x := (⟨k, hk⟩ : f.ker))
    rw [hcard] at h
    simpa using congrArg Subtype.val h
  have hkcenter : k ∈ Subgroup.center H := hker hk
  have hcomm : Commute k y :=
    (Subgroup.mem_center_iff.mp hkcenter y).symm
  have hxy' : x = k * y := by simp [k]
  calc
    x ^ 2 = (k * y) ^ 2 := by rw [hxy']
    _ = k ^ 2 * y ^ 2 := hcomm.mul_pow 2
    _ = y ^ 2 := by rw [hk2]; simp

private theorem __ch5_MultiplierBounds_first_mem_of_card_four_of_cases
    {G : Type*} [Group G] [Finite G]
    (V : Subgroup G) (a b c : G)
    (hcard : Nat.card V = 4)
    (hcases : ∀ x, x ∈ V → x = 1 ∨ x = a ∨ x = b ∨ x = c) :
    a ∈ V := by
  by_contra hnot
  have hsub : (V : Set G) ⊆ ({1, b, c} : Set G) := by
    intro x hxV
    rcases hcases x hxV with h1 | ha | hb | hc
    · simp [h1]
    · subst x
      exact (hnot hxV).elim
    · simp [hb]
    · simp [hc]
  have hVncard : (V : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  have htarget : ({1, b, c} : Set G).ncard ≤ 3 := by
    calc
      ({1, b, c} : Set G).ncard ≤ ({b, c} : Set G).ncard + 1 :=
        Set.ncard_insert_le 1 {b, c}
      _ ≤ (({c} : Set G).ncard + 1) + 1 :=
        Nat.add_le_add_right (Set.ncard_insert_le b {c}) 1
      _ ≤ 3 := by simp
  have := Set.ncard_le_ncard hsub
  omega

/-- In a perfect central extension of `A₅` with kernel of order two, lifts
of the two standard nontrivial generators of the root four-subgroup do not
commute. This is the local core of A1 33.17. -/
public theorem commutator_lifts_root_four_ne_one_of_card_ker_two
    {H : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    (f : H →* alternatingGroup (Fin 5))
    (hsurj : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hcard : Nat.card f.ker = 2)
    (u v : H)
    (hu : f u = (⟨rho1 0, rho1_mem_alternating 0⟩ : alternatingGroup (Fin 5)))
    (hv : f v = (⟨rho2 0, rho2_mem_alternating 0⟩ : alternatingGroup (Fin 5))) :
    ⁅u, v⁆ ≠ 1 := by
  let V := rootFourSubgroup 0
  let L : Subgroup H := V.comap f
  have hLcard : Nat.card L = 8 := by
    dsimp [L, V]
    rw [card_comap_mul f hsurj (rootFourSubgroup 0), rootFourSubgroup_card, hcard]
  have hLindex : L.index = 15 := by
    dsimp [L]
    rw [Subgroup.index_comap_of_surjective V hsurj]
    have h := (rootFourSubgroup 0).card_mul_index
    have hA5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup]
      norm_num
    rw [rootFourSubgroup_card, hA5] at h
    nlinarith
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLp : IsPGroup 2 L := by
    apply IsPGroup.of_card (n := 3)
    simpa using hLcard
  have hLindex2 : ¬ 2 ∣ L.index := by rw [hLindex]; norm_num
  let P : Sylow 2 H := hLp.toSylow hLindex2
  let K : Subgroup L := f.ker.comap L.subtype
  have hKfrattini : K ≤ frattini L := by
    intro x hx
    apply ker_comap_le_frattini_sylow P f hker
    exact hx
  let a1 : alternatingGroup (Fin 5) :=
    ⟨rho1 0, rho1_mem_alternating 0⟩
  let a2 : alternatingGroup (Fin 5) :=
    ⟨rho2 0, rho2_mem_alternating 0⟩
  let a3 : alternatingGroup (Fin 5) :=
    ⟨rho3 0, rho3_mem_alternating 0⟩
  have hVcases : ∀ x, x ∈ V → x = 1 ∨ x = a1 ∨ x = a2 ∨ x = a3 := by
    intro x hx
    rcases V_elements 0 hx with h | h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))
  have hVcard : Nat.card V = 4 := by
    simpa [V] using rootFourSubgroup_card 0
  have ha1V : a1 ∈ V :=
    __ch5_MultiplierBounds_first_mem_of_card_four_of_cases V a1 a2 a3 hVcard hVcases
  have ha2V : a2 ∈ V := by
    apply __ch5_MultiplierBounds_first_mem_of_card_four_of_cases V a2 a1 a3 hVcard
    intro x hx
    rcases hVcases x hx with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
  have huL : u ∈ L := by
    change f u ∈ V
    rw [hu]
    exact ha1V
  have hvL : v ∈ L := by
    change f v ∈ V
    rw [hv]
    exact ha2V
  let uL : L := ⟨u, huL⟩
  let vL : L := ⟨v, hvL⟩
  let wL : L := uL * vL
  let tauA : alternatingGroup (Fin 5) := schurAlternatingProjection 0 (g 0)
  obtain ⟨d, hd⟩ := hsurj tauA
  have hu2ker : u ^ 2 ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_pow, hu]
    apply Subtype.ext
    simpa [pow_two] using rho1_sq 0
  have hw2ker : (u * v) ^ 2 ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_pow, map_mul, hu, hv]
    apply Subtype.ext
    simpa [pow_two, rho1_mul_rho2] using rho3_sq 0
  have hu2center : u ^ 2 ∈ Subgroup.center H := hker hu2ker
  have hw2center : (u * v) ^ 2 ∈ Subgroup.center H := hker hw2ker
  have hconj_u_image : f (d * u * d⁻¹) = f (u * v) := by
    rw [map_mul, map_mul, map_inv, hd, hu, map_mul, hu, hv]
    apply Subtype.ext
    change tau 0 * rho1 0 * (tau 0)⁻¹ = rho1 0 * rho2 0
    rw [tau_conj_rho1, rho1_mul_rho2]
  have hconj_w_image : f (d * (u * v) * d⁻¹) = f v := by
    rw [map_mul, map_mul, map_inv, hd, map_mul, hu, hv]
    apply Subtype.ext
    change tau 0 * (rho1 0 * rho2 0) * (tau 0)⁻¹ = rho2 0
    rw [rho1_mul_rho2]
    all_goals decide
  have hu2w2 : u ^ 2 = (u * v) ^ 2 := by
    calc
      u ^ 2 = (d * u * d⁻¹) ^ 2 := by
        rw [show (d * u * d⁻¹) ^ 2 = d * u ^ 2 * d⁻¹ by
          simp [pow_two, mul_assoc]]
        have hc := Subgroup.mem_center_iff.mp hu2center d
        rw [hc]
        simp
      _ = (u * v) ^ 2 :=
        __ch5_MultiplierBounds_sq_eq_sq_of_apply_eq_of_card_ker_two f hker hcard hconj_u_image
  have hw2v2 : (u * v) ^ 2 = v ^ 2 := by
    calc
      (u * v) ^ 2 = (d * (u * v) * d⁻¹) ^ 2 := by
        rw [show (d * (u * v) * d⁻¹) ^ 2 = d * (u * v) ^ 2 * d⁻¹ by
          simp [pow_two, mul_assoc]]
        have hc := Subgroup.mem_center_iff.mp hw2center d
        rw [hc]
        simp
      _ = v ^ 2 :=
        __ch5_MultiplierBounds_sq_eq_sq_of_apply_eq_of_card_ker_two f hker hcard hconj_w_image
  intro huv_one
  have huv_comm : Commute u v := commutatorElement_eq_one_iff_commute.mp huv_one
  have hu2one : u ^ 2 = 1 := by
    have hs : u ^ 2 = u ^ 2 * u ^ 2 := by
      calc
        u ^ 2 = (u * v) ^ 2 := hu2w2
        _ = u ^ 2 * v ^ 2 := huv_comm.mul_pow 2
        _ = u ^ 2 * u ^ 2 := by rw [← hw2v2, ← hu2w2]
    have hs' := congrArg (fun x : H => (u ^ 2)⁻¹ * x) hs
    simpa [mul_assoc] using hs'.symm
  have hv2one : v ^ 2 = 1 := by rw [← hw2v2, ← hu2w2, hu2one]
  have huL2 : uL * uL = 1 := by
    apply Subtype.ext
    simpa [pow_two] using hu2one
  have hvL2 : vL * vL = 1 := by
    apply Subtype.ext
    simpa [pow_two] using hv2one
  have huvL : Commute uL vL := by
    exact Subtype.ext huv_comm.eq
  let A : Subgroup L := Subgroup.closure ({uL, vL} : Set L)
  have hAcard : Nat.card A ≤ 4 := by
    simpa [A] using __ch5_MultiplierBounds_card_closure_pair_le_four_of_sq_eq_one_of_commute
      uL vL huL2 hvL2 huvL
  have hAKtop : A ⊔ K = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hxV : f x.1 ∈ rootFourSubgroup 0 := x.2
    rcases V_elements 0 hxV with hx | hx | hx | hx
    · have hxK : x ∈ K := by
        rw [show K = f.ker.comap L.subtype by rfl, Subgroup.mem_comap,
          MonoidHom.mem_ker]
        apply Subtype.ext
        exact hx
      exact (le_sup_right : K ≤ A ⊔ K) hxK
    · have hdiffK : x * uL⁻¹ ∈ K := by
        rw [show K = f.ker.comap L.subtype by rfl, Subgroup.mem_comap,
          MonoidHom.mem_ker]
        change f (x.1 * u⁻¹) = 1
        rw [map_mul, map_inv, hu]
        apply Subtype.ext
        change (f x.1 : Equiv.Perm (Fin 5)) * (rho1 0)⁻¹ = 1
        rw [hx]
        simp
      have huA : uL ∈ A := Subgroup.subset_closure (by simp)
      rw [show x = (x * uL⁻¹) * uL by simp]
      exact (A ⊔ K).mul_mem
        ((le_sup_right : K ≤ A ⊔ K) hdiffK)
        ((le_sup_left : A ≤ A ⊔ K) huA)
    · have hdiffK : x * vL⁻¹ ∈ K := by
        rw [show K = f.ker.comap L.subtype by rfl, Subgroup.mem_comap,
          MonoidHom.mem_ker]
        change f (x.1 * v⁻¹) = 1
        rw [map_mul, map_inv, hv]
        apply Subtype.ext
        change (f x.1 : Equiv.Perm (Fin 5)) * (rho2 0)⁻¹ = 1
        rw [hx]
        simp
      have hvA : vL ∈ A := Subgroup.subset_closure (by simp)
      rw [show x = (x * vL⁻¹) * vL by simp]
      exact (A ⊔ K).mul_mem
        ((le_sup_right : K ≤ A ⊔ K) hdiffK)
        ((le_sup_left : A ≤ A ⊔ K) hvA)
    · have hdiffK : x * (uL * vL)⁻¹ ∈ K := by
        rw [show K = f.ker.comap L.subtype by rfl, Subgroup.mem_comap,
          MonoidHom.mem_ker]
        change f (x.1 * (u * v)⁻¹) = 1
        rw [map_mul, map_inv, map_mul, hu, hv]
        apply Subtype.ext
        change (f x.1 : Equiv.Perm (Fin 5)) * (rho1 0 * rho2 0)⁻¹ = 1
        rw [hx, rho1_mul_rho2]
        simp
      have huvA : uL * vL ∈ A := A.mul_mem
        (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
      rw [show x = (x * (uL * vL)⁻¹) * (uL * vL) by group]
      exact (A ⊔ K).mul_mem
        ((le_sup_right : K ≤ A ⊔ K) hdiffK)
        ((le_sup_left : A ≤ A ⊔ K) huvA)
  have hAFrattini : A ⊔ frattini L = ⊤ := by
    apply top_unique
    rw [← hAKtop]
    exact sup_le_sup le_rfl hKfrattini
  have hAtop : A = ⊤ := frattini_nongenerating hAFrattini
  have hAcard8 : Nat.card A = 8 := by
    rw [hAtop, Subgroup.card_top]
    exact hLcard
  omega

private theorem __ch5_MultiplierBounds_coatom_index_two_of_isTwoGroup
    {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup 2 G) (U : Subgroup G) (hU : IsCoatom U) :
    U.index = 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Group.IsNilpotent G := hG.isNilpotent
  have hMall : ∀ M : Subgroup G, IsCoatom M → M.Normal :=
    (Group.isNilpotent_of_finite_tfae (G := G)).out 0 2 |>.mp
      (show Group.IsNilpotent G from inferInstance)
  let : U.Normal := hMall U hU
  let Q := G ⧸ U
  let q : G →* Q := QuotientGroup.mk' U
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective U
  let : Nontrivial Q := QuotientGroup.nontrivial_iff.mpr hU.ne_top
  let : IsSimpleGroup Q := {
    toNontrivial := inferInstance
    eq_bot_or_eq_top_of_normal := by
      intro N _
      by_cases hN : N = ⊥
      · exact Or.inl hN
      · right
        have hcomap : U < N.comap q := by
          have hker : q.ker = U := QuotientGroup.ker_mk' U
          exact lt_of_le_of_lt hker.ge
            ((Subgroup.comap_lt_comap_of_surjective hq).mpr
              (bot_lt_iff_ne_bot.mpr hN))
        have htop : N.comap q = ⊤ := hU.2 _ hcomap
        apply Subgroup.comap_injective hq
        rw [htop, Subgroup.comap_top]
  }
  have hQp : IsPGroup 2 Q := hG.to_quotient U
  let : Group.IsNilpotent Q := hQp.isNilpotent
  let : CommGroup Q := inferInstance
  have hprime : (Nat.card Q).Prime := IsSimpleGroup.prime_card
  have h2dvd : 2 ∣ Nat.card Q := by
    rcases hQp.card_eq_or_dvd with hcard | hdvd
    · have hgt : 1 < Nat.card Q :=
        Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      omega
    · exact hdvd
  have hcardQ : Nat.card Q = 2 := by
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hprime).mp h2dvd).symm
  rw [Subgroup.index_eq_card]
  exact hcardQ

private theorem __ch5_MultiplierBounds_isTwoGroup_ker_alternatingFreeCentralCovering_zero :
    IsPGroup 2 (alternatingFreeCentralCovering 0).toMonoidHom.ker := by
  apply IsPGroup.of_card
  exact Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' (fun {q} hq hqker => by
    let : Fact q.Prime := ⟨hq⟩
    have hbound :=
      two_mul_prime_le_degree_of_dvd_natCard_ker_alternatingFreeCentralCovering
        0 q hqker
    have htwo := hq.two_le
    omega)

private theorem __ch5_MultiplierBounds_commutator_sq_eq_one_of_sq_mem_center_of_commutator_mem_center
    {G : Type*} [Group G] {u v : G}
    (hu_sq : u * u ∈ Subgroup.center G)
    (hz : ⁅u, v⁆ ∈ Subgroup.center G) :
    ⁅u, v⁆ * ⁅u, v⁆ = 1 := by
  have hsq_comm : Commute (u * u) v :=
    (Subgroup.mem_center_iff.mp hu_sq v).symm
  have hconj : u * ⁅u, v⁆ * u⁻¹ = ⁅u, v⁆ := by
    rw [Subgroup.mem_center_iff.mp hz u, mul_inv_cancel_right]
  have hcomm := hsq_comm.commutator_eq
  rw [commutatorElement_mul_left_eq_conj_mul, hconj] at hcomm
  exact hcomm

private theorem __ch5_MultiplierBounds_commutator_lifts_root_four_sq_eq_one
    {H : Type*} [Group H]
    (f : H →* alternatingGroup (Fin 5))
    (hker : f.ker ≤ Subgroup.center H)
    (u v : H)
    (hu : f u = (⟨rho1 0, rho1_mem_alternating 0⟩ : alternatingGroup (Fin 5)))
    (hv : f v = (⟨rho2 0, rho2_mem_alternating 0⟩ : alternatingGroup (Fin 5))) :
    ⁅u, v⁆ * ⁅u, v⁆ = 1 := by
  have hzker : ⁅u, v⁆ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement, hu, hv,
      commutatorElement_eq_one_iff_mul_comm]
    apply Subtype.ext
    change rho1 0 * rho2 0 = rho2 0 * rho1 0
    rw [rho1_mul_rho2, rho2_mul_rho1]
  have hu_sq_ker : u * u ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, hu]
    apply Subtype.ext
    exact rho1_sq 0
  exact __ch5_MultiplierBounds_commutator_sq_eq_one_of_sq_mem_center_of_commutator_mem_center
    (hker hu_sq_ker) (hker hzker)

private theorem __ch5_MultiplierBounds_exists_coatom_containing_zpowers_of_sq_eq_one_of_two_lt_card
    {G : Type*} [Group G] [Finite G] (z : G)
    (hz_sq : z * z = 1) (hcard : 2 < Nat.card G) :
    ∃ U : Subgroup G, IsCoatom U ∧ Subgroup.zpowers z ≤ U := by
  let Z := Subgroup.zpowers z
  have horder_dvd : orderOf z ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    simpa [pow_two] using hz_sq
  have hZcard_le : Nat.card Z ≤ 2 := by
    rw [show Nat.card Z = orderOf z by simp [Z, Nat.card_zpowers]]
    exact Nat.le_of_dvd (by norm_num) horder_dvd
  have hZne : Z ≠ ⊤ := by
    intro htop
    have hcard_eq : Nat.card Z = Nat.card G := by
      rw [htop, Subgroup.card_top]
    omega
  exact (eq_top_or_exists_le_coatom Z).resolve_left hZne

private theorem __ch5_MultiplierBounds_natCard_map_eq_index_of_subgroupOf_ker_eq
    {H Q : Type*} [Group H] [Finite H] [Group Q]
    (K : Subgroup H) (U : Subgroup K) (q : H →* Q)
    (hker : q.ker.subgroupOf K = U) :
    Nat.card (K.map q) = U.index := by
  let r := q.subgroupMap K
  have hrker : r.ker = U := by
    rw [show r = q.subgroupMap K by rfl, Subgroup.ker_subgroupMap, hker]
  calc
    Nat.card (K.map q) = Nat.card r.range := by
      rw [MonoidHom.range_eq_top.mpr (q.subgroupMap_surjective K), Subgroup.card_top]
    _ = r.ker.index := (Subgroup.index_ker r).symm
    _ = U.index := by rw [hrker]

private theorem __ch5_MultiplierBounds_map_le_center_of_le_center_of_surjective
    {H Q : Type*} [Group H] [Group Q]
    (q : H →* Q) (hq : Function.Surjective q)
    {K : Subgroup H} (hK : K ≤ Subgroup.center H) :
    K.map q ≤ Subgroup.center Q := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨a, rfl⟩ := hq y
  rw [← map_mul, ← map_mul]
  exact congrArg q (Subgroup.mem_center_iff.mp (hK hx) a)

/-- A1 33.17: the universal central covering of `A₅` has kernel of order
two. -/
public theorem natCard_ker_alternatingFreeCentralCovering_zero_eq_two :
    Nat.card (alternatingFreeCentralCovering 0).toMonoidHom.ker = 2 := by
  apply le_antisymm ?_ (two_le_natCard_ker_alternatingFreeCentralCovering 0)
  by_contra hnot
  have hcard_gt :
      2 < Nat.card (alternatingFreeCentralCovering 0).toMonoidHom.ker := by
    omega
  let f := (alternatingFreeCentralCovering 0).toMonoidHom
  let a1 : alternatingGroup (Fin 5) :=
    ⟨rho1 0, rho1_mem_alternating 0⟩
  let a2 : alternatingGroup (Fin 5) :=
    ⟨rho2 0, rho2_mem_alternating 0⟩
  obtain ⟨u, hu⟩ := (alternatingFreeCentralCovering 0).surjective a1
  obtain ⟨v, hv⟩ := (alternatingFreeCentralCovering 0).surjective a2
  have hu' : f u = a1 := hu
  have hv' : f v = a2 := hv
  let z := ⁅u, v⁆
  have hzker : z ∈ f.ker := by
    rw [MonoidHom.mem_ker, show z = ⁅u, v⁆ by rfl,
      map_commutatorElement, hu', hv']
    rw [commutatorElement_eq_one_iff_mul_comm]
    apply Subtype.ext
    change rho1 0 * rho2 0 = rho2 0 * rho1 0
    rw [rho1_mul_rho2, rho2_mul_rho1]
  have hz_sq : z * z = 1 := by
    exact __ch5_MultiplierBounds_commutator_lifts_root_four_sq_eq_one f
      (alternatingFreeCentralCovering 0).ker_le_center u v hu' hv'
  let zk : f.ker := ⟨z, hzker⟩
  have hzk_sq : zk * zk = 1 := by
    apply Subtype.ext
    exact hz_sq
  have hKp : IsPGroup 2 f.ker := by
    simpa [f] using __ch5_MultiplierBounds_isTwoGroup_ker_alternatingFreeCentralCovering_zero
  obtain ⟨U, hUcoatom, hZU⟩ :=
    __ch5_MultiplierBounds_exists_coatom_containing_zpowers_of_sq_eq_one_of_two_lt_card
      zk hzk_sq (by simpa [f] using hcard_gt)
  have hUindex : U.index = 2 :=
    __ch5_MultiplierBounds_coatom_index_two_of_isTwoGroup hKp U hUcoatom
  let X : Subgroup (AlternatingFreeCentralDerived 0) := U.map f.ker.subtype
  have hXker : X ≤ f.ker := by
    rintro x ⟨k, hk, rfl⟩
    exact k.2
  have hXcenter : X ≤ Subgroup.center (AlternatingFreeCentralDerived 0) :=
    hXker.trans (alternatingFreeCentralCovering 0).ker_le_center
  let : X.Normal := ⟨fun x hx a => by
    simpa [Subgroup.mem_center_iff.mp (hXcenter hx) a] using hx⟩
  let q : AlternatingFreeCentralDerived 0 →* AlternatingFreeCentralDerived 0 ⧸ X :=
    QuotientGroup.mk' X
  let fbar : (AlternatingFreeCentralDerived 0 ⧸ X) →* alternatingGroup (Fin 5) :=
    QuotientGroup.lift X f hXker
  have hqker : q.ker.subgroupOf f.ker = U := by
    rw [show q = QuotientGroup.mk' X by rfl, QuotientGroup.ker_mk']
    change Subgroup.comap f.ker.subtype (U.map f.ker.subtype) = U
    exact Subgroup.comap_map_eq_self_of_injective f.ker.subtype_injective U
  have hfbar_card : Nat.card fbar.ker = 2 := by
    rw [show fbar = QuotientGroup.lift X f hXker by rfl,
      QuotientGroup.ker_lift]
    exact (__ch5_MultiplierBounds_natCard_map_eq_index_of_subgroupOf_ker_eq f.ker U q hqker).trans hUindex
  have hfbar_surj : Function.Surjective fbar := by
    exact QuotientGroup.lift_surjective_of_surjective X f
      (alternatingFreeCentralCovering 0).surjective hXker
  have hfbar_center : fbar.ker ≤ Subgroup.center (AlternatingFreeCentralDerived 0 ⧸ X) := by
    rw [show fbar = QuotientGroup.lift X f hXker by rfl,
      QuotientGroup.ker_lift]
    exact __ch5_MultiplierBounds_map_le_center_of_le_center_of_surjective q
      (QuotientGroup.mk'_surjective X)
      (alternatingFreeCentralCovering 0).ker_le_center
  have hne : ⁅q u, q v⁆ ≠ 1 :=
    commutator_lifts_root_four_ne_one_of_card_ker_two
      fbar hfbar_surj hfbar_center hfbar_card (q u) (q v)
      (by simpa [fbar, q] using hu') (by simpa [fbar, q] using hv')
  have hzkU : zk ∈ U := hZU (by simp [zk])
  have hzX : z ∈ X := by
    exact ⟨zk, hzkU, rfl⟩
  have hqz : q z = 1 := by
    rw [← MonoidHom.mem_ker, show q = QuotientGroup.mk' X by rfl,
      QuotientGroup.ker_mk']
    exact hzX
  apply hne
  rw [← map_commutatorElement, show ⁅u, v⁆ = z by rfl, hqz]

/-- The standard double cover of `A₅` is universal. -/
public theorem schurAlternatingCovering_isUniversal_zero :
    Covering.IsUniversal.{0, 0, 0} (schurAlternatingCovering 0) := by
  exact Covering.isUniversal_of_card_two
    (alternatingFreeCentralCovering 0)
    (alternatingFreeCentralCovering_isUniversal 0)
    natCard_ker_alternatingFreeCentralCovering_zero_eq_two
    (schurAlternatingCovering 0)
    (natCard_ker_schurAlternatingCovering 0)

/-- Any two double covers of `A₅` are uniquely isomorphic over `A₅`. -/
public theorem coveringIso_alternatingGroup_five_of_card_two
    {G₁ G₂ : Type} [Group G₁] [Finite G₁] [IsQuasisimple G₁]
    [Group G₂] [Finite G₂] [IsQuasisimple G₂]
    (f₁ : Covering G₁ (alternatingGroup (Fin 5)))
    (f₂ : Covering G₂ (alternatingGroup (Fin 5)))
    (hk₁ : Nat.card f₁.toMonoidHom.ker = 2)
    (hk₂ : Nat.card f₂.toMonoidHom.ker = 2) :
    ∃! e : G₁ ≃* G₂, f₂.comp (Covering.ofMulEquiv e) = f₁ := by
  exact Covering.coveringIso_of_card_two
    (alternatingFreeCentralCovering 0)
    (alternatingFreeCentralCovering_isUniversal 0)
    (alternatingFreeCentralCovering_isUniversal 0)
    natCard_ker_alternatingFreeCentralCovering_zero_eq_two
    f₁ f₂ hk₁ hk₂

end GLS3.Chapter5.SchurPresentation
/- END Theory.MultiplierBounds -/

/- BEGIN Theory.AlternatingFourCentralExtensionSplit -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

open scoped Pointwise

/-- A central double extension of `A₄` splits when every lift of a nontrivial
Klein-four element has square one. -/
public theorem alternatingFour_kernel_isComplement'_of_root_lifts_sq_one
    {E : Type*} [Group E] [Finite E]
    (q : E →* alternatingGroup (Fin 4))
    (hq : Function.Surjective q)
    (hcenter : q.ker ≤ Subgroup.center E)
    (hcard : Nat.card q.ker = 2)
    (hsq : ∀ x : E, (q x).1.support.card = 4 → x ^ 2 = 1) :
    ∃ S : Subgroup E, q.ker.IsComplement' S := by
  let V := alternatingFourKlein
  let N : Subgroup E := V.comap q
  let : N.Normal := inferInstance
  have hNcard : Nat.card N = 8 := by
    have h := card_comap_mul q hq V
    rw [alternatingFourKlein_card, hcard] at h
    simpa [N, V] using h
  have hNsq (x : N) : x ^ 2 = 1 := by
    have hxV : q x.1 ∈ V := x.2
    simp only [V, alternatingFourKlein] at hxV
    rcases hxV with hx | hx | hx | hx
    · have hxker : x.1 ∈ q.ker := MonoidHom.mem_ker.mpr hx
      let xker : q.ker := ⟨x.1, hxker⟩
      have hord : orderOf xker ∣ 2 := by
        rw [← hcard]
        exact orderOf_dvd_natCard xker
      have hxker2 : xker ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hord
      apply Subtype.ext
      change x.1 ^ 2 = 1
      exact congrArg Subtype.val hxker2
    · apply Subtype.ext
      apply hsq x.1
      rw [hx]
      exact alternatingFourRootOne_support
    · apply Subtype.ext
      apply hsq x.1
      rw [hx]
      exact alternatingFourRootTwo_support
    · apply Subtype.ext
      apply hsq x.1
      rw [hx]
      exact alternatingFourRootProduct_support
  have hNcomm (x y : N) : x * y = y * x := by
    have hxInv : x⁻¹ = x :=
      inv_eq_iff_mul_eq_one.mpr (by simpa [pow_two] using hNsq x)
    have hyInv : y⁻¹ = y :=
      inv_eq_iff_mul_eq_one.mpr (by simpa [pow_two] using hNsq y)
    have hxyInv : (x * y)⁻¹ = x * y :=
      inv_eq_iff_mul_eq_one.mpr (by simpa [pow_two] using hNsq (x * y))
    calc
      x * y = (x * y)⁻¹ := hxyInv.symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [hxInv, hyInv]
  let : IsMulCommutative N := ⟨⟨hNcomm⟩⟩
  obtain ⟨t, htq, htorder⟩ :=
    exists_order_three_lift_of_ker_card_two q hq hcenter hcard
      alternatingFourThreeCycle alternatingFourThreeCycle_order
  let alpha : MulAut N := MulAut.conjNormal t
  let delta : N →* N :=
    { toFun := fun x => alpha x * x⁻¹
      map_one' := by simp
      map_mul' := by
        intro x y
        simp only [map_mul, mul_inv_rev]
        ac_rfl }
  let qN : N →* V :=
    (q.comp N.subtype).codRestrict V (fun x => x.2)
  have qN_val (z : N) : (qN z).1 = q z.1 := rfl
  have hqN : Function.Surjective qN := by
    intro v
    obtain ⟨x, hx⟩ := hq v.1
    have hxN : x ∈ N := by
      change q x ∈ V
      simp [hx]
    refine ⟨⟨x, hxN⟩, ?_⟩
    apply Subtype.ext
    change q x = v.1
    exact hx
  let beta : MulAut V := MulAut.conjNormal alternatingFourThreeCycle
  let deltaV : V →* V :=
    { toFun := fun x => beta x * x⁻¹
      map_one' := by simp
      map_mul' := by
        intro x y
        have : IsMulCommutative V := ⟨⟨fun x y => by
          dsimp [V] at x y ⊢
          exact alternatingFourKlein_comm x y⟩⟩
        simp only [map_mul, mul_inv_rev]
        ac_rfl }
  have hdeltaCompat (x : N) : qN (delta x) = deltaV (qN x) := by
    apply Subtype.ext
    change q (delta x).1 = (deltaV (qN x)).1
    simp [delta, deltaV, alpha, beta, qN, qN_val, htq]
  have hdeltaVinj : Function.Injective deltaV := by
    apply deltaV.ker_eq_bot_iff.mp
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hfix : alternatingFourThreeCycle * x.1 *
        alternatingFourThreeCycle⁻¹ = x.1 := by
      have h := MonoidHom.mem_ker.mp hx
      change beta x * x⁻¹ = 1 at h
      have : beta x = x := mul_inv_eq_one.mp h
      exact congrArg Subtype.val this
    have hxone := (alternatingFourThreeCycle_conj_fixed_iff x).mp hfix
    exact Subtype.ext hxone
  have hdeltaVsurj : Function.Surjective deltaV :=
    Finite.surjective_of_injective hdeltaVinj
  have hdeltaKer : delta.ker = q.ker.comap N.subtype := by
    ext x
    constructor
    · intro hx
      have hfix : alpha x = x := by
        have h := MonoidHom.mem_ker.mp hx
        change alpha x * x⁻¹ = 1 at h
        exact mul_inv_eq_one.mp h
      have hqfix : alternatingFourThreeCycle * (qN x).1 *
          alternatingFourThreeCycle⁻¹ = (qN x).1 := by
        calc
          alternatingFourThreeCycle * (qN x).1 * alternatingFourThreeCycle⁻¹ =
              q ((alpha x).1) := by
                simp [alpha, qN, qN_val, htq]
          _ = q x.1 := congrArg (fun z : N => q z.1) hfix
          _ = (qN x).1 := (qN_val x).symm
      have hqone := (alternatingFourThreeCycle_conj_fixed_iff (qN x)).mp hqfix
      exact MonoidHom.mem_ker.mpr hqone
    · intro hx
      have hxker : x.1 ∈ q.ker := hx
      have hxcenter : x.1 ∈ Subgroup.center E := hcenter hxker
      apply MonoidHom.mem_ker.mpr
      change alpha x * x⁻¹ = 1
      have htx : t * x.1 = x.1 * t :=
        Subgroup.mem_center_iff.mp hxcenter t
      apply Subtype.ext
      simp [alpha, htx]
  have hdeltaKerCard : Nat.card delta.ker = 2 := by
    rw [hdeltaKer]
    let e : q.ker.comap N.subtype ≃* q.ker :=
      { toFun := fun x => ⟨x.1.1, x.2⟩
        invFun := fun x => ⟨⟨x.1, by
          change q x.1 ∈ V
          rw [MonoidHom.mem_ker.mp x.2]
          exact V.one_mem⟩, x.2⟩
        left_inv := fun x => by ext; rfl
        right_inv := fun x => by ext; rfl
        map_mul' := fun _ _ => rfl }
    exact (Nat.card_congr e.toEquiv).trans hcard
  have hdeltaRangeCard : Nat.card delta.range = 4 := by
    have hmul := Subgroup.card_mul_index delta.ker
    rw [hdeltaKerCard, Subgroup.index_ker, hNcard] at hmul
    omega
  let R : Subgroup E := delta.range.map N.subtype
  have hRcard : Nat.card R = 4 := by
    change Nat.card (delta.range.map N.subtype) = 4
    rw [Subgroup.card_map_of_injective Subtype.val_injective]
    exact hdeltaRangeCard
  have hRmap : R.map q = V := by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      rcases hx with ⟨z, hz, rfl⟩
      exact z.2
    · intro v hv
      obtain ⟨w, hw⟩ := hdeltaVsurj ⟨v, hv⟩
      obtain ⟨x, hx⟩ := hqN w
      refine ⟨(delta x).1, ?_, ?_⟩
      · exact ⟨delta x, ⟨x, rfl⟩, rfl⟩
      · have hc := hdeltaCompat x
        rw [hx, hw] at hc
        exact congrArg Subtype.val hc
  have hRleN : R ≤ N := by
    rintro r ⟨x, hx, rfl⟩
    exact x.2
  have hNleNormalizer : N ≤ Subgroup.normalizer R := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff']
    intro r
    constructor
    · intro hrn
      have hrN : r ∈ N := by
        have hprodN : r * n ∈ N := hRleN hrn
        simpa using N.mul_mem hprodN (N.inv_mem hn)
      have hcomm := congrArg Subtype.val (hNcomm ⟨n, hn⟩ ⟨r, hrN⟩)
      change n * r = r * n at hcomm
      rw [hcomm]
      exact hrn
    · intro hnr
      have hrN : r ∈ N := by
        have hprodN : n * r ∈ N := hRleN hnr
        simpa using N.mul_mem (N.inv_mem hn) hprodN
      have hcomm := congrArg Subtype.val (hNcomm ⟨n, hn⟩ ⟨r, hrN⟩)
      change n * r = r * n at hcomm
      rw [← hcomm]
      exact hnr
  have htConj (r : E) (hr : r ∈ R) : t * r * t⁻¹ ∈ R := by
    rcases hr with ⟨x, ⟨z, rfl⟩, rfl⟩
    refine ⟨delta (alpha z), ⟨alpha z, rfl⟩, ?_⟩
    simp [delta, alpha]
    group
  have htNormalizer : t ∈ Subgroup.normalizer R := by
    rw [Subgroup.mem_normalizer_iff]
    intro r
    constructor
    · exact htConj r
    · intro hr
      have h2 := htConj (t * r * t⁻¹) hr
      have h3 := htConj (t * (t * r * t⁻¹) * t⁻¹) h2
      have ht3 : t ^ 3 = 1 := by
        rw [← htorder]
        exact pow_orderOf_eq_one t
      have hconj3 :
          t * (t * (t * r * t⁻¹) * t⁻¹) * t⁻¹ = r := by
        calc
          t * (t * (t * r * t⁻¹) * t⁻¹) * t⁻¹ =
              t ^ 3 * r * (t ^ 3)⁻¹ := by
            simp [pow_three]
            group
          _ = r := by rw [ht3]; simp
      simpa [hconj3] using h3
  let T : Subgroup E := Subgroup.zpowers t
  have hTleNormalizer : T ≤ Subgroup.normalizer R := by
    exact Subgroup.zpowers_le.mpr htNormalizer
  have hNTtop : N ⊔ T = ⊤ := by
    have hmapN : N.map q = V := by
      change (V.comap q).map q = V
      apply Subgroup.map_comap_eq_self
      rw [MonoidHom.range_eq_top.mpr hq]
      exact le_top
    have hmapT : T.map q = Subgroup.zpowers alternatingFourThreeCycle := by
      apply le_antisymm
      · rintro y ⟨x, ⟨k, rfl⟩, rfl⟩
        exact ⟨k, by simp [map_zpow, htq]⟩
      · rintro y ⟨k, rfl⟩
        exact ⟨t ^ k, ⟨k, rfl⟩, by simp [map_zpow, htq]⟩
    have hmapTop : (N ⊔ T).map q = ⊤ := by
      rw [Subgroup.map_sup, hmapN, hmapT,
        alternatingFourKlein_sup_threeCycle]
    apply top_unique
    intro g _
    have hqg : q g ∈ (N ⊔ T).map q := by rw [hmapTop]; trivial
    obtain ⟨y, hy, hqy⟩ := hqg
    let k := g * y⁻¹
    have hkker : k ∈ q.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hqy]
      simp
    have hkN : k ∈ N := by
      change q k ∈ V
      rw [MonoidHom.mem_ker.mp hkker]
      exact V.one_mem
    have : g = k * y := by simp [k]
    rw [this]
    exact (N ⊔ T).mul_mem ((le_sup_left : N ≤ N ⊔ T) hkN) hy
  let : R.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    apply top_unique
    rw [← hNTtop]
    exact sup_le hNleNormalizer hTleNormalizer
  have hTcard : Nat.card T = 3 := by
    simpa [T] using (Nat.card_zpowers t).trans htorder
  have hinter : R ⊓ T = ⊥ := by
    apply Disjoint.eq_bot
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hRcard, hTcard]
    all_goals decide
  let S := R ⊔ T
  have hScard : Nat.card S = 12 := by
    have hrel : R.relIndex T = 3 := by
      rw [← Subgroup.inf_relIndex_right, hinter,
        Subgroup.relIndex_bot_left, hTcard]
    have hmul := Subgroup.relIndex_mul_relIndex
      (⊥ : Subgroup E) R S bot_le le_sup_left
    rw [Subgroup.relIndex_bot_left, hRcard,
      Subgroup.relIndex_sup_left, hrel,
      Subgroup.relIndex_bot_left] at hmul
    omega
  have hSmap : S.map q = ⊤ := by
    change (R ⊔ T).map q = ⊤
    have hmapT : T.map q = Subgroup.zpowers alternatingFourThreeCycle := by
      apply le_antisymm
      · rintro y ⟨x, ⟨k, rfl⟩, rfl⟩
        exact ⟨k, by simp [map_zpow, htq]⟩
      · rintro y ⟨k, rfl⟩
        exact ⟨t ^ k, ⟨k, rfl⟩, by simp [map_zpow, htq]⟩
    rw [Subgroup.map_sup, hRmap, hmapT,
      alternatingFourKlein_sup_threeCycle]
  have hdisj : Disjoint q.ker S := by
    rw [Subgroup.disjoint_def]
    intro x hxker hxS
    have htargetCard : Nat.card (alternatingGroup (Fin 4)) = 12 :=
      alternatingGroup.card_of_card_eq_four (by simp)
    let qs : S →* alternatingGroup (Fin 4) := q.comp S.subtype
    have hqsSurj : Function.Surjective qs := by
      intro y
      have hy : y ∈ S.map q := by rw [hSmap]; trivial
      obtain ⟨x, hx, hqx⟩ := hy
      exact ⟨⟨x, hx⟩, hqx⟩
    have hqsInj : Function.Injective qs := by
      let : Fintype S := Fintype.ofFinite _
      let : Fintype (alternatingGroup (Fin 4)) := Fintype.ofFinite _
      exact ((Fintype.bijective_iff_surjective_and_card qs).2 ⟨hqsSurj, by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
          hScard, htargetCard]⟩).1
    have hxone : (⟨x, hxS⟩ : S) = 1 := by
      apply hqsInj
      simp [qs, MonoidHom.mem_ker.mp hxker]
    exact congrArg Subtype.val hxone
  have hmul : (q.ker : Set E) * (S : Set E) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hqx : q x ∈ S.map q := by rw [hSmap]; trivial
    obtain ⟨s, hsS, hqs⟩ := hqx
    let k := x * s⁻¹
    have hk : k ∈ q.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hqs]
      simp
    exact Set.mem_mul.mpr ⟨k, hk, s, hsS, by simp [k]⟩
  exact ⟨S, Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul⟩

end GLS3.Chapter5.SchurPresentation
/- END Theory.AlternatingFourCentralExtensionSplit -/

/- BEGIN Theory.CentralInvolutionDisjointSupport -/
noncomputable section

namespace GLS3.Chapter5

open scoped commutatorElement
universe __ch5_CentralInvolutionDisjointSupport_u __ch5_CentralInvolutionDisjointSupport_v

@[expose]
public noncomputable def permutationLiftOfSurjective
    {G : Type __ch5_CentralInvolutionDisjointSupport_u} {Ω : Type __ch5_CentralInvolutionDisjointSupport_v} [Group G]
    (f : G →* Equiv.Perm Ω) (hf : Function.Surjective f)
    (σ : Equiv.Perm Ω) : G :=
  Classical.choose (hf σ)

public theorem permutationLiftOfSurjective_apply
    {G : Type __ch5_CentralInvolutionDisjointSupport_u} {Ω : Type __ch5_CentralInvolutionDisjointSupport_v} [Group G]
    (f : G →* Equiv.Perm Ω) (hf : Function.Surjective f)
    (σ : Equiv.Perm Ω) :
    f (permutationLiftOfSurjective f hf σ) = σ :=
  Classical.choose_spec (hf σ)

private theorem __ch5_CentralInvolutionDisjointSupport_mul_listProd_eq_central_pow
    {G : Type __ch5_CentralInvolutionDisjointSupport_u} [Group G] (z x : G) (ys : List G)
    (hz : z ∈ Subgroup.center G)
    (hpair : ∀ y ∈ ys, x * y = z * y * x) :
    x * ys.prod = z ^ ys.length * ys.prod * x := by
  induction ys with
  | nil => simp
  | cons y ys ih =>
      have hxy := hpair y (by simp)
      have htail : ∀ t ∈ ys, x * t = z * t * x := by
        intro t ht
        exact hpair t (by simp [ht])
      have ih' := ih htail
      have hyz : Commute y z := Subgroup.mem_center_iff.mp hz y
      have hyzpow : Commute y (z ^ ys.length) := hyz.pow_right _
      calc
        x * (y :: ys).prod = (x * y) * ys.prod := by simp [mul_assoc]
        _ = (z * y * x) * ys.prod := by rw [hxy]
        _ = z * y * (x * ys.prod) := by simp only [mul_assoc]
        _ = z * y * (z ^ ys.length * ys.prod * x) := by rw [ih']
        _ = (z * z ^ ys.length) * ((y :: ys).prod) * x := by
          calc
            z * y * (z ^ ys.length * ys.prod * x) =
                z * ((y * z ^ ys.length) * (ys.prod * x)) := by
              simp only [mul_assoc]
            _ = z * ((z ^ ys.length * y) * (ys.prod * x)) := by
              rw [hyzpow.eq]
            _ = (z * z ^ ys.length) * ((y :: ys).prod) * x := by
              simp only [List.prod_cons, mul_assoc]
        _ = z ^ (y :: ys).length * (y :: ys).prod * x := by
          simp [pow_succ', mul_assoc]

private theorem __ch5_CentralInvolutionDisjointSupport_listProd_mul_listProd_eq_central_pow
    {G : Type __ch5_CentralInvolutionDisjointSupport_u} [Group G] (z : G) (xs ys : List G)
    (hz : z ∈ Subgroup.center G)
    (hpair : ∀ x ∈ xs, ∀ y ∈ ys, x * y = z * y * x) :
    xs.prod * ys.prod = z ^ (xs.length * ys.length) * ys.prod * xs.prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hxpair : ∀ y ∈ ys, x * y = z * y * x := by
        intro y hy
        exact hpair x (by simp) y hy
      have htail : ∀ t ∈ xs, ∀ y ∈ ys, t * y = z * y * t := by
        intro t ht y hy
        exact hpair t (by simp [ht]) y hy
      have ih' := ih htail
      have hxmove := __ch5_CentralInvolutionDisjointSupport_mul_listProd_eq_central_pow z x ys hz hxpair
      have hzx : Commute z x := (Subgroup.mem_center_iff.mp hz x).symm
      have hzpowx : Commute (z ^ (xs.length * ys.length)) x := hzx.pow_left _
      calc
        (x :: xs).prod * ys.prod = x * (xs.prod * ys.prod) := by
          simp only [List.prod_cons, mul_assoc]
        _ = x * (z ^ (xs.length * ys.length) * ys.prod * xs.prod) := by rw [ih']
        _ = z ^ (xs.length * ys.length) * (x * ys.prod) * xs.prod := by
          calc
            x * (z ^ (xs.length * ys.length) * ys.prod * xs.prod) =
                (x * z ^ (xs.length * ys.length)) * (ys.prod * xs.prod) := by
              simp only [mul_assoc]
            _ = (z ^ (xs.length * ys.length) * x) * (ys.prod * xs.prod) := by
              rw [hzpowx.eq.symm]
            _ = z ^ (xs.length * ys.length) * (x * ys.prod) * xs.prod := by
              simp only [mul_assoc]
        _ = z ^ (xs.length * ys.length) *
            (z ^ ys.length * ys.prod * x) * xs.prod := by rw [hxmove]
        _ = z ^ ((x :: xs).length * ys.length) * ys.prod * (x :: xs).prod := by
          calc
            z ^ (xs.length * ys.length) *
                (z ^ ys.length * ys.prod * x) * xs.prod =
              (z ^ (xs.length * ys.length) * z ^ ys.length) *
                ys.prod * (x * xs.prod) := by simp only [mul_assoc]
            _ = z ^ (xs.length * ys.length + ys.length) *
                ys.prod * (x * xs.prod) := by rw [pow_add]
            _ = z ^ ((x :: xs).length * ys.length) *
                ys.prod * (x :: xs).prod := by
              simp only [List.length_cons, List.prod_cons]
              congr 2
              simp [Nat.add_mul]

@[expose]
public noncomputable def permutationSectionLiftOfSurjective
    {G : Type __ch5_CentralInvolutionDisjointSupport_u} {Ω : Type __ch5_CentralInvolutionDisjointSupport_v} [Group G] [Fintype Ω] [LinearOrder Ω]
    (f : G →* Equiv.Perm Ω) (hf : Function.Surjective f)
    (σ : Equiv.Perm Ω) : G :=
  (List.map (permutationLiftOfSurjective f hf)
    (Equiv.Perm.swapFactors σ).1).prod

public theorem permutationSectionLiftOfSurjective_apply
    {G : Type __ch5_CentralInvolutionDisjointSupport_u} {Ω : Type __ch5_CentralInvolutionDisjointSupport_v} [Group G] [Fintype Ω] [LinearOrder Ω]
    (f : G →* Equiv.Perm Ω) (hf : Function.Surjective f)
    (σ : Equiv.Perm Ω) :
    f (permutationSectionLiftOfSurjective f hf σ) = σ := by
  rw [permutationSectionLiftOfSurjective, map_list_prod, List.map_map]
  simpa [Function.comp_def, permutationLiftOfSurjective_apply] using
    (Equiv.Perm.swapFactors σ).2.1

private theorem __ch5_CentralInvolutionDisjointSupport_disjoint_swap_factors_twist
    {G : Type __ch5_CentralInvolutionDisjointSupport_u} {Ω : Type __ch5_CentralInvolutionDisjointSupport_v} [Group G] [Fintype Ω] [LinearOrder Ω]
    (f : G →* Equiv.Perm Ω) (hf : Function.Surjective f) (z : G)
    (hswap : ∀ {a b c d : Ω}, [a, b, c, d].Nodup →
      permutationLiftOfSurjective f hf (Equiv.swap a b) *
          permutationLiftOfSurjective f hf (Equiv.swap c d) =
        z * permutationLiftOfSurjective f hf (Equiv.swap c d) *
          permutationLiftOfSurjective f hf (Equiv.swap a b))
    {σ τ g h : Equiv.Perm Ω} (hdisjoint : Equiv.Perm.Disjoint σ τ)
    (hg : g ∈ (Equiv.Perm.swapFactors σ).1)
    (hh : h ∈ (Equiv.Perm.swapFactors τ).1) :
    permutationLiftOfSurjective f hf g * permutationLiftOfSurjective f hf h =
      z * permutationLiftOfSurjective f hf h *
        permutationLiftOfSurjective f hf g := by
  obtain ⟨a, b, hab, rfl⟩ := (Equiv.Perm.swapFactors σ).2.2 _ hg
  obtain ⟨c, d, hcd, rfl⟩ := (Equiv.Perm.swapFactors τ).2.2 _ hh
  have hsigma := SchurPresentation.swapFactors_support σ (Equiv.swap a b) hg
  have htau := SchurPresentation.swapFactors_support τ (Equiv.swap c d) hh
  have hfactorDisjoint : Equiv.Perm.Disjoint
      (Equiv.swap a b) (Equiv.swap c d) :=
    hdisjoint.mono hsigma htau
  have hsupp : Disjoint ({a, b} : Finset Ω) ({c, d} : Finset Ω) := by
    rw [← Equiv.Perm.support_swap hab, ← Equiv.Perm.support_swap hcd]
    exact hfactorDisjoint.disjoint_support
  have hac : a ≠ c := by
    intro e
    subst c
    exact (Finset.disjoint_left.mp hsupp
      (show a ∈ ({a, b} : Finset Ω) by simp))
      (show a ∈ ({a, d} : Finset Ω) by simp)
  have had : a ≠ d := by
    intro e
    subst d
    exact (Finset.disjoint_left.mp hsupp
      (show a ∈ ({a, b} : Finset Ω) by simp))
      (show a ∈ ({c, a} : Finset Ω) by simp)
  have hbc : b ≠ c := by
    intro e
    subst c
    exact (Finset.disjoint_left.mp hsupp
      (show b ∈ ({a, b} : Finset Ω) by simp))
      (show b ∈ ({b, d} : Finset Ω) by simp)
  have hbd : b ≠ d := by
    intro e
    subst d
    exact (Finset.disjoint_left.mp hsupp
      (show b ∈ ({a, b} : Finset Ω) by simp))
      (show b ∈ ({c, b} : Finset Ω) by simp)
  exact hswap (by simp [hab, hcd, hac, had, hbc, hbd])

private theorem __ch5_CentralInvolutionDisjointSupport_sq_eq_sq_of_apply_eq
    {G : Type __ch5_CentralInvolutionDisjointSupport_u} {Q : Type __ch5_CentralInvolutionDisjointSupport_v} [Group G] [Group Q]
    (f : G →* Q) (hkerCenter : f.ker ≤ Subgroup.center G)
    (hkerSq : ∀ k ∈ f.ker, k ^ 2 = 1) {x y : G} (hxy : f x = f y) :
    x ^ 2 = y ^ 2 := by
  let k := x * y⁻¹
  have hk : k ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy]
    simp
  have hk2 : k ^ 2 = 1 := hkerSq k hk
  have hkcenter : k ∈ Subgroup.center G := hkerCenter hk
  have hcomm : Commute k y :=
    (Subgroup.mem_center_iff.mp hkcenter y).symm
  have hxeq : x = k * y := by simp [k]
  calc
    x ^ 2 = (k * y) ^ 2 := by rw [hxeq]
    _ = k ^ 2 * y ^ 2 := hcomm.mul_pow 2
    _ = y ^ 2 := by rw [hk2]; simp

private theorem __ch5_CentralInvolutionDisjointSupport_sq_eq_sq_of_conjugate_images
    {G : Type __ch5_CentralInvolutionDisjointSupport_u} {Q : Type __ch5_CentralInvolutionDisjointSupport_v} [Group G] [Group Q]
    (f : G →* Q) (hf : Function.Surjective f)
    (hkerCenter : f.ker ≤ Subgroup.center G)
    (hkerSq : ∀ k ∈ f.ker, k ^ 2 = 1)
    {x y : G} {c : Q} (hx : f x ^ 2 = 1)
    (hconj : c * f x * c⁻¹ = f y) : x ^ 2 = y ^ 2 := by
  obtain ⟨d, rfl⟩ := hf c
  have himage : f (d * x * d⁻¹) = f y := by
    simpa only [map_mul, map_inv] using hconj
  have hsquares := __ch5_CentralInvolutionDisjointSupport_sq_eq_sq_of_apply_eq f hkerCenter hkerSq himage
  have hxker : x ^ 2 ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact hx
  have hxcenter : x ^ 2 ∈ Subgroup.center G := hkerCenter hxker
  have hcomm : d * x ^ 2 = x ^ 2 * d :=
    Subgroup.mem_center_iff.mp hxcenter d
  calc
    x ^ 2 = (d * x * d⁻¹) ^ 2 := by
      rw [show (d * x * d⁻¹) ^ 2 = d * x ^ 2 * d⁻¹ by
        simp [pow_two, mul_assoc]]
      rw [hcomm]
      simp
    _ = y ^ 2 := hsquares

/-- In a central extension with elementary kernel, the root-involution square
calculation forces the nontrivial twist between arbitrary lifts of disjoint
transpositions. -/
public theorem disjointSwapLift_twist_of_root_sq
    {G : Type __ch5_CentralInvolutionDisjointSupport_u} {Ω : Type __ch5_CentralInvolutionDisjointSupport_v} [Group G] [Fintype Ω] [LinearOrder Ω]
    (f : G →* Equiv.Perm Ω) (hf : Function.Surjective f) (z : G)
    (hzCenter : z ∈ Subgroup.center G)
    (hkerCenter : f.ker ≤ Subgroup.center G)
    (hkerSq : ∀ k ∈ f.ker, k ^ 2 = 1)
    (hrootSq : ∀ w : G, (f w).cycleType = {2, 2} → w ^ 2 = z)
    {a b c d : Ω} (hnodup : [a, b, c, d].Nodup) :
    permutationLiftOfSurjective f hf (Equiv.swap a b) *
        permutationLiftOfSurjective f hf (Equiv.swap c d) =
      z * permutationLiftOfSurjective f hf (Equiv.swap c d) *
        permutationLiftOfSurjective f hf (Equiv.swap a b) := by
  have _ := hzCenter
  have hab : a ≠ b := by
    intro h
    subst b
    simp at hnodup
  have hcd : c ≠ d := by
    intro h
    subst d
    simp at hnodup
  let x := permutationLiftOfSurjective f hf (Equiv.swap a b)
  let y := permutationLiftOfSurjective f hf (Equiv.swap c d)
  have hxproj : f x = Equiv.swap a b := permutationLiftOfSurjective_apply f hf _
  have hyproj : f y = Equiv.swap c d := permutationLiftOfSurjective_apply f hf _
  obtain ⟨q, hq⟩ := isConj_iff.mp (Equiv.Perm.isConj_swap hab hcd)
  have hxsqImage : f x ^ 2 = 1 := by
    rw [hxproj]
    simp [pow_two]
  have hsquares : x ^ 2 = y ^ 2 :=
    __ch5_CentralInvolutionDisjointSupport_sq_eq_sq_of_conjugate_images f hf hkerCenter hkerSq hxsqImage (by
      rw [hxproj, hyproj]
      exact hq)
  let t := x ^ 2
  have htker : t ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_pow, hxproj]
    simp [pow_two]
  have htCenter : t ∈ Subgroup.center G := hkerCenter htker
  have ht2 : t ^ 2 = 1 := hkerSq t htker
  have hx2 : x * x = t := by simp [t, pow_two]
  have hy2 : y * y = t := by simpa [t, pow_two] using hsquares.symm
  have hxinv : x⁻¹ = t * x := by
    apply (eq_inv_of_mul_eq_one_right (a := x) (b := t * x) ?_).symm
    calc
      x * (t * x) = (x * t) * x := by rw [mul_assoc]
      _ = (t * x) * x := by
        rw [Subgroup.mem_center_iff.mp htCenter x]
      _ = t * (x * x) := by simp only [mul_assoc]
      _ = t * t := by rw [hx2]
      _ = 1 := by simpa [pow_two] using ht2
  have hyinv : y⁻¹ = t * y := by
    apply (eq_inv_of_mul_eq_one_right (a := y) (b := t * y) ?_).symm
    calc
      y * (t * y) = (y * t) * y := by rw [mul_assoc]
      _ = (t * y) * y := by
        rw [Subgroup.mem_center_iff.mp htCenter y]
      _ = t * (y * y) := by simp only [mul_assoc]
      _ = t * t := by rw [hy2]
      _ = 1 := by simpa [pow_two] using ht2
  have hxy2 : (x * y) ^ 2 = z := by
    apply hrootSq
    rw [map_mul, hxproj, hyproj]
    exact Equiv.Perm.cycleType_swap_mul_swap_of_nodup hnodup
  have hcomm : x * y * x⁻¹ * y⁻¹ = z := by
    rw [hxinv, hyinv]
    have htxy : Commute t (x * y) :=
      (Subgroup.mem_center_iff.mp htCenter (x * y)).symm
    have htxyx : Commute t ((x * y) * x) :=
      (Subgroup.mem_center_iff.mp htCenter ((x * y) * x)).symm
    calc
      x * y * (t * x) * (t * y) = ((x * y) * t) * x * (t * y) := by
        simp only [mul_assoc]
      _ = (t * (x * y)) * x * (t * y) := by rw [htxy.eq]
      _ = t * ((x * y) * x) * (t * y) := by simp only [mul_assoc]
      _ = t * (((x * y) * x) * t) * y := by simp only [mul_assoc]
      _ = t * (t * ((x * y) * x)) * y := by rw [htxyx.eq]
      _ = (t * t) * ((x * y) * x * y) := by simp only [mul_assoc]
      _ = (x * y) ^ 2 := by rw [show t * t = 1 by simpa [pow_two] using ht2]; simp [pow_two, mul_assoc]
      _ = z := hxy2
  have h := congrArg (fun w : G => w * y * x) hcomm
  simpa [mul_assoc] using h

/-- A central twist relation for lifts of disjoint transpositions propagates
to arbitrary disjoint-support permutations. -/
public theorem disjointSupport_twist_of_swap_twist
    {G : Type __ch5_CentralInvolutionDisjointSupport_u} {Ω : Type __ch5_CentralInvolutionDisjointSupport_v} [Group G] [Fintype Ω] [LinearOrder Ω]
    (f : G →* Equiv.Perm Ω) (hf : Function.Surjective f) (z : G)
    (hz : z ∈ Subgroup.center G) (hker : f.ker ≤ Subgroup.center G)
    (hswap : ∀ {a b c d : Ω}, [a, b, c, d].Nodup →
      permutationLiftOfSurjective f hf (Equiv.swap a b) *
          permutationLiftOfSurjective f hf (Equiv.swap c d) =
        z * permutationLiftOfSurjective f hf (Equiv.swap c d) *
          permutationLiftOfSurjective f hf (Equiv.swap a b))
    (x y : G) (hdisjoint : Equiv.Perm.Disjoint (f x) (f y)) :
    x * y = z ^ ((Equiv.Perm.swapFactors (f x)).1.length *
        (Equiv.Perm.swapFactors (f y)).1.length) * y * x := by
  let sx := permutationSectionLiftOfSurjective f hf (f x)
  let sy := permutationSectionLiftOfSurjective f hf (f y)
  have hsx : f sx = f x := permutationSectionLiftOfSurjective_apply f hf (f x)
  have hsy : f sy = f y := permutationSectionLiftOfSurjective_apply f hf (f y)
  let kx := x * sx⁻¹
  let ky := y * sy⁻¹
  have hkx : kx ∈ Subgroup.center G := by
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hsx]
    simp
  have hky : ky ∈ Subgroup.center G := by
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hsy]
    simp
  have hsection : sx * sy = z ^ ((Equiv.Perm.swapFactors (f x)).1.length *
      (Equiv.Perm.swapFactors (f y)).1.length) * sy * sx := by
    change
      (List.map (permutationLiftOfSurjective f hf)
        (Equiv.Perm.swapFactors (f x)).1).prod *
      (List.map (permutationLiftOfSurjective f hf)
        (Equiv.Perm.swapFactors (f y)).1).prod = _
    dsimp only [sx, sy, permutationSectionLiftOfSurjective]
    simpa only [List.length_map] using
      (__ch5_CentralInvolutionDisjointSupport_listProd_mul_listProd_eq_central_pow z
        (List.map (permutationLiftOfSurjective f hf)
          (Equiv.Perm.swapFactors (f x)).1)
        (List.map (permutationLiftOfSurjective f hf)
          (Equiv.Perm.swapFactors (f y)).1) hz (by
          intro a ha b hb
          rcases List.mem_map.mp ha with ⟨g, hg, rfl⟩
          rcases List.mem_map.mp hb with ⟨h, hh, rfl⟩
          exact __ch5_CentralInvolutionDisjointSupport_disjoint_swap_factors_twist f hf z hswap hdisjoint hg hh))
  have hx : x = kx * sx := by simp [kx, mul_assoc]
  have hy : y = ky * sy := by simp [ky, mul_assoc]
  have hcenterPow : z ^ ((Equiv.Perm.swapFactors (f x)).1.length *
      (Equiv.Perm.swapFactors (f y)).1.length) ∈ Subgroup.center G :=
    (Subgroup.center G).pow_mem hz _
  have hc_kxky : Commute
      (z ^ ((Equiv.Perm.swapFactors (f x)).1.length *
        (Equiv.Perm.swapFactors (f y)).1.length)) (kx * ky) :=
    (Subgroup.mem_center_iff.mp hcenterPow (kx * ky)).symm
  have hkx_kysy : Commute kx (ky * sy) :=
    (Subgroup.mem_center_iff.mp hkx (ky * sy)).symm
  calc
    x * y = (kx * sx) * (ky * sy) := by rw [← hx, ← hy]
    _ = kx * ky * (sx * sy) := by
      calc
        (kx * sx) * (ky * sy) = kx * (sx * ky) * sy := by simp only [mul_assoc]
        _ = kx * (ky * sx) * sy := by
          rw [(Subgroup.mem_center_iff.mp hky sx).symm]
        _ = kx * ky * (sx * sy) := by simp only [mul_assoc]
    _ = kx * ky *
        (z ^ ((Equiv.Perm.swapFactors (f x)).1.length *
          (Equiv.Perm.swapFactors (f y)).1.length) * sy * sx) := by rw [hsection]
    _ = z ^ ((Equiv.Perm.swapFactors (f x)).1.length *
          (Equiv.Perm.swapFactors (f y)).1.length) *
        (ky * sy) * (kx * sx) := by
      calc
        kx * ky * (z ^ ((Equiv.Perm.swapFactors (f x)).1.length *
            (Equiv.Perm.swapFactors (f y)).1.length) * sy * sx) =
          (kx * ky) * z ^ ((Equiv.Perm.swapFactors (f x)).1.length *
            (Equiv.Perm.swapFactors (f y)).1.length) * (sy * sx) := by
              simp only [mul_assoc]
        _ = z ^ ((Equiv.Perm.swapFactors (f x)).1.length *
            (Equiv.Perm.swapFactors (f y)).1.length) * (kx * ky) *
              (sy * sx) := by rw [hc_kxky.eq]
        _ = z ^ ((Equiv.Perm.swapFactors (f x)).1.length *
            (Equiv.Perm.swapFactors (f y)).1.length) *
              (kx * (ky * sy)) * sx := by simp only [mul_assoc]
        _ = z ^ ((Equiv.Perm.swapFactors (f x)).1.length *
            (Equiv.Perm.swapFactors (f y)).1.length) *
              ((ky * sy) * kx) * sx := by rw [hkx_kysy.eq]
        _ = z ^ ((Equiv.Perm.swapFactors (f x)).1.length *
            (Equiv.Perm.swapFactors (f y)).1.length) *
              (ky * sy) * (kx * sx) := by simp only [mul_assoc]
    _ = z ^ ((Equiv.Perm.swapFactors (f x)).1.length *
          (Equiv.Perm.swapFactors (f y)).1.length) * y * x := by
      rw [← hx, ← hy]



private theorem __ch5_CentralInvolutionDisjointSupport_swapFactors_even_iff_mem_alternating
    {Ω : Type __ch5_CentralInvolutionDisjointSupport_v} [Fintype Ω] [LinearOrder Ω] (σ : Equiv.Perm Ω) :
    Even (Equiv.Perm.swapFactors σ).1.length ↔ σ ∈ alternatingGroup Ω := by
  constructor
  · intro heven
    rw [← (Equiv.Perm.swapFactors σ).2.1]
    exact (Equiv.Perm.prod_list_swap_mem_alternatingGroup_iff_even_length
      (Equiv.Perm.swapFactors σ).2.2).2 heven
  · intro hmem
    rw [← (Equiv.Perm.swapFactors σ).2.1] at hmem
    exact (Equiv.Perm.prod_list_swap_mem_alternatingGroup_iff_even_length
      (Equiv.Perm.swapFactors σ).2.2).1 hmem

private theorem __ch5_CentralInvolutionDisjointSupport_pow_eq_one_of_even_of_sq_eq_one
    {G : Type __ch5_CentralInvolutionDisjointSupport_u} [Group G] {z : G} (hz2 : z ^ 2 = 1)
    {m : Nat} (hm : Even m) : z ^ m = 1 := by
  rcases hm with ⟨k, rfl⟩
  rw [← two_mul, pow_mul, hz2, one_pow]

private theorem __ch5_CentralInvolutionDisjointSupport_pow_eq_self_of_odd_of_sq_eq_one
    {G : Type __ch5_CentralInvolutionDisjointSupport_u} [Group G] {z : G} (hz2 : z ^ 2 = 1)
    {m : Nat} (hm : Odd m) : z ^ m = z := by
  rcases hm with ⟨k, rfl⟩
  rw [show 2 * k + 1 = 2 * k + 1 by rfl, pow_add, pow_mul, hz2,
    one_pow, one_mul, pow_one]

/-- Proposition 5.2.4(f) for a surjective symmetric-group extension with
central elementary kernel and the root-involution square calculation. -/
public theorem proposition_5_2_4_f_general_symmetric
    {G : Type __ch5_CentralInvolutionDisjointSupport_u} {Ω : Type __ch5_CentralInvolutionDisjointSupport_v} [Group G] [Fintype Ω] [LinearOrder Ω]
    (f : G →* Equiv.Perm Ω) (hf : Function.Surjective f) (z : G)
    (hzCenter : z ∈ Subgroup.center G) (hz2 : z ^ 2 = 1)
    (hkerCenter : f.ker ≤ Subgroup.center G)
    (hkerSq : ∀ k ∈ f.ker, k ^ 2 = 1)
    (hrootSq : ∀ w : G, (f w).cycleType = {2, 2} → w ^ 2 = z)
    (x y : G) (hdisjoint : Equiv.Perm.Disjoint (f x) (f y)) :
    (f x ∈ alternatingGroup Ω ∨ f y ∈ alternatingGroup Ω →
      x * y * x⁻¹ * y⁻¹ = 1) ∧
    (f x ∉ alternatingGroup Ω → f y ∉ alternatingGroup Ω →
      x * y * x⁻¹ * y⁻¹ = z) := by
  have hswap : ∀ {a b c d : Ω}, [a, b, c, d].Nodup →
      permutationLiftOfSurjective f hf (Equiv.swap a b) *
          permutationLiftOfSurjective f hf (Equiv.swap c d) =
        z * permutationLiftOfSurjective f hf (Equiv.swap c d) *
          permutationLiftOfSurjective f hf (Equiv.swap a b) := by
    intro a b c d hnodup
    exact disjointSwapLift_twist_of_root_sq f hf z hzCenter hkerCenter
      hkerSq hrootSq hnodup
  have htwist := disjointSupport_twist_of_swap_twist f hf z hzCenter
    hkerCenter hswap x y hdisjoint
  let lx := (Equiv.Perm.swapFactors (f x)).1.length
  let ly := (Equiv.Perm.swapFactors (f y)).1.length
  constructor
  · intro heven
    have hexponent : Even (lx * ly) := by
      rcases heven with hx | hy
      · exact (__ch5_CentralInvolutionDisjointSupport_swapFactors_even_iff_mem_alternating (f x)).2 hx |>.mul_right ly
      · exact (__ch5_CentralInvolutionDisjointSupport_swapFactors_even_iff_mem_alternating (f y)).2 hy |>.mul_left lx
    have hzpow : z ^ (lx * ly) = 1 :=
      __ch5_CentralInvolutionDisjointSupport_pow_eq_one_of_even_of_sq_eq_one hz2 hexponent
    have hcomm : x * y = y * x := by
      simpa [lx, ly, hzpow] using htwist
    rw [hcomm]
    simp [mul_assoc]
  · intro hoddx hoddy
    have hlx : Odd lx := Nat.not_even_iff_odd.mp (by
      intro heven
      exact hoddx ((__ch5_CentralInvolutionDisjointSupport_swapFactors_even_iff_mem_alternating (f x)).1 heven))
    have hly : Odd ly := Nat.not_even_iff_odd.mp (by
      intro heven
      exact hoddy ((__ch5_CentralInvolutionDisjointSupport_swapFactors_even_iff_mem_alternating (f y)).1 heven))
    have hzpow : z ^ (lx * ly) = z :=
      __ch5_CentralInvolutionDisjointSupport_pow_eq_self_of_odd_of_sq_eq_one hz2 (hlx.mul hly)
    have hrelation : x * y = z * y * x := by
      simpa [lx, ly, hzpow] using htwist
    have h := congrArg (fun w : G => w * x⁻¹ * y⁻¹) hrelation
    simpa [mul_assoc] using h

end GLS3.Chapter5
/- END Theory.CentralInvolutionDisjointSupport -/

/- BEGIN Theory.QuasisimpleRelativeSubnormalCentralizesRelativeNormalAbelian -/
namespace GLS3.Chapter5

/-- A quasisimple subgroup subnormal in `C` centralizes an abelian subgroup
normal in `C`. -/
public theorem commutator_eq_bot_of_isQuasisimple_relative_subnormal_normal_abelian
    {G : Type*} [Group G] (R I C : Subgroup G)
    [IsMulCommutative R] [IsQuasisimple I]
    (hRle : R ≤ C) (hRnormal : (R.subgroupOf C).Normal)
    (hIle : I ≤ C) (hIsubnormal : (I.subgroupOf C).IsSubnormal) :
    ⁅R, I⁆ = ⊥ := by
  let R0 : Subgroup C := R.subgroupOf C
  let I0 : Subgroup C := I.subgroupOf C
  let : R0.Normal := hRnormal
  let : IsMulCommutative R0 := IsMulCommutative.of_comm fun a b => by
    let aR : R := ⟨a.1.1, a.2⟩
    let bR : R := ⟨b.1.1, b.2⟩
    apply Subtype.ext
    apply Subtype.ext
    have hab := congrArg Subtype.val
      (isMulCommutative_iff.mp (inferInstance : IsMulCommutative R) aR bR)
    simpa [aR, bR] using hab
  let : IsQuasisimple I0 := isQuasisimple_subgroupOf I C hIle
  have hcomm0 : ⁅R0, I0⁆ = ⊥ :=
    commutator_eq_bot_of_isQuasisimple_isSubnormal_normal_abelian
      R0 I0 hIsubnormal
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro i hi
  let r0 : R0 := ⟨⟨r, hRle hr⟩, hr⟩
  let i0 : I0 := ⟨⟨i, hIle hi⟩, hi⟩
  have hrcentral : r0.1 ∈ Subgroup.centralizer (I0 : Set C) := by
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm0) r0.2
  have hri := Subgroup.mem_centralizer_iff.mp hrcentral i0.1 i0.2
  exact congrArg (fun z : C => z.1) hri

end GLS3.Chapter5
/- END Theory.QuasisimpleRelativeSubnormalCentralizesRelativeNormalAbelian -/

/- BEGIN Theory.EvenInvolutionFullRotation -/
noncomputable section
namespace GLS3.Chapter5
universe __ch5_EvenInvolutionFullRotation_u

private noncomputable def involutionFullRotation
    {Ω : Type __ch5_EvenInvolutionFullRotation_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) : CycleRotationGroup x :=
  fun c => cycleFactorGenerator c

private theorem __ch5_EvenInvolutionFullRotation_involutionFullRotation_toPerm
    {Ω : Type __ch5_EvenInvolutionFullRotation_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2) :
    (cycleRotationToCentralizer x (involutionFullRotation x)).1 = x := by
  apply Equiv.ext
  intro ω
  by_cases hω : x ω = ω
  · let fixed : Function.fixedPoints x := ⟨ω, hω⟩
    calc
      (cycleRotationToCentralizer x (involutionFullRotation x)).1 ω = ω :=
        cycleRotationToCentralizer_apply_fixed x (involutionFullRotation x) fixed
      _ = x ω := hω.symm
  · have hωsupp : ω ∈ x.support := Equiv.Perm.mem_support.mpr hω
    have hc : x.cycleOf ω ∈ x.cycleFactorsFinset :=
      Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hωsupp
    let c : x.cycleFactorsFinset := ⟨x.cycleOf ω, hc⟩
    have hωc : ω ∈ c.1.support := by
      change ω ∈ (x.cycleOf ω).support
      rw [Equiv.Perm.mem_support, Equiv.Perm.cycleOf_apply_self]
      exact hω
    obtain ⟨n, hn⟩ :=
      (cycleCoordinateEquiv x (by simpa [hx] using Nat.prime_two) c).surjective
        ⟨ω, hωc⟩
    have happ := cycleRotationToCentralizer_apply_cycleCoordinate x
      (by simpa [hx] using Nat.prime_two) (involutionFullRotation x) c n
    rw [congrArg Subtype.val hn] at happ
    change (cycleRotationToCentralizer x (involutionFullRotation x)).1 ω =
      c.1 ω at happ
    rw [happ]
    exact Equiv.Perm.cycleOf_apply_self x ω

/-- If an involution has an even number of nontrivial cycles, rotating every
cycle once is an even rotation; its permutation is the original involution and
all trace-zero coordinates are one. -/
public theorem exists_evenInvolutionFullRotation
    {Ω : Type __ch5_EvenInvolutionFullRotation_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2)
    (r : Nat) (e : x.cycleFactorsFinset ≃ Fin r) (hr : Even r) :
    ∃ w : evenInvolutionCycleRotations x,
      (cycleRotationToCentralizer x w.1).1 = x ∧
      (Multiplicative.toAdd
        (evenInvolutionCycleRotations_mulEquiv_traceZero x hx r e w)).1 =
          fun _ => 1 := by
  let a := involutionFullRotation x
  have hcoord : ∀ c,
      involutionCycleRotationCoordinates x hx a c =
        Multiplicative.ofAdd (1 : ZMod 2) := by
    intro c
    rw [involutionCycleRotationCoordinates_apply]
    have hprime : (orderOf x).Prime := by simpa [hx] using Nat.prime_two
    have hfactorCard : Nat.card (Subgroup.zpowers c.1) = 2 := by
      simpa [hx] using cycleFactorZPowers_card_of_primeOrder x hprime c
    exact zmodMulEquivOfGenerator_symm_apply_generator
      (cycleFactorGenerator_generates c) hfactorCard
  have haEven : a ∈ evenInvolutionCycleRotations x := by
    rw [mem_evenInvolutionCycleRotations,
      involutionCycleRotation_sign x hx a]
    simp_rw [hcoord]
    have hallmem := (traceZeroTwoSubgroup_allOne_mem_iff_even r).mpr hr
    rw [mem_traceZeroTwoSubgroup] at hallmem
    change (-1 : ℤˣ) ^ (∑ _ : x.cycleFactorsFinset, (1 : ZMod 2)) = 1
    have hsumReindex : (∑ _ : x.cycleFactorsFinset, (1 : ZMod 2)) =
        ∑ _ : Fin r, (1 : ZMod 2) := by
      simpa using e.sum_comp (fun _ : Fin r => (1 : ZMod 2))
    have hsum : (∑ _ : x.cycleFactorsFinset, (1 : ZMod 2)) = 0 :=
      hsumReindex.trans hallmem
    rw [hsum]
    simp
  let w : evenInvolutionCycleRotations x := ⟨a, haEven⟩
  refine ⟨w, __ch5_EvenInvolutionFullRotation_involutionFullRotation_toPerm x hx, ?_⟩
  funext i
  rw [evenInvolutionCycleRotations_mulEquiv_traceZero_apply]
  exact congrArg Multiplicative.toAdd (hcoord (e.symm i))

end GLS3.Chapter5
/- END Theory.EvenInvolutionFullRotation -/

/- BEGIN Theory.TraceZeroRotationPreimageQuotient -/
noncomputable section
namespace GLS3.Chapter5.SchurPresentation

open GLS3.Chapter5

/-- The full preimage of the concrete trace-zero rotation subgroup has the
natural quotient onto its trace-zero coordinate module. -/
public theorem traceZeroRotationPreimage_quotient_data
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n : Nat) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (x : Equiv.Perm (Fin (n + 5))) (hx : orderOf x = 2)
    (r : Nat) (e : x.cycleFactorsFinset ≃ Fin r) :
    let Rbar := involutionEvenRotationSubgroup x
    let R := Rbar.comap f.toMonoidHom
    ∃ q : R →* Multiplicative ↥(traceZeroTwoSubgroup r),
      Function.Surjective q ∧
      q.ker = f.toMonoidHom.ker.comap R.subtype ∧
      Nat.card q.ker = 2 ∧ IsPGroup 2 R := by
  dsimp only
  let Rbar := involutionEvenRotationSubgroup x
  let R := Rbar.comap f.toMonoidHom
  let eR := involutionEvenRotationSubgroupMulEquivTraceZero x hx r e
  let p : R →* Rbar :=
    (f.toMonoidHom.comp R.subtype).codRestrict Rbar (fun z => z.2)
  let q : R →* Multiplicative ↥(traceZeroTwoSubgroup r) :=
    eR.toMonoidHom.comp p
  have hpSurj : Function.Surjective p := by
    intro z
    obtain ⟨g, hg⟩ := f.surjective z.1
    change f g = z.1 at hg
    refine ⟨⟨g, ?_⟩, ?_⟩
    · change f g ∈ Rbar
      rw [hg]
      exact z.2
    · apply Subtype.ext
      change f g = z.1
      exact hg
  have hqSurj : Function.Surjective q := eR.surjective.comp hpSurj
  have hqKer : q.ker = f.toMonoidHom.ker.comap R.subtype := by
    ext z
    constructor
    · intro hz
      have hpz : p z = 1 := by
        apply eR.injective
        simpa [q] using MonoidHom.mem_ker.mp hz
      exact MonoidHom.mem_ker.mpr (congrArg Subtype.val hpz)
    · intro hz
      have hpz : p z = 1 := by
        apply Subtype.ext
        change f.toMonoidHom z.1 = 1
        exact MonoidHom.mem_ker.mp hz
      exact MonoidHom.mem_ker.mpr (by simp [q, hpz])
  have hkerR : f.toMonoidHom.ker ≤ R := by
    intro z hz
    change f.toMonoidHom z ∈ Rbar
    rw [MonoidHom.mem_ker.mp hz]
    exact Rbar.one_mem
  have hcardKer : Nat.card q.ker = 2 := by
    rw [hqKer]
    have heq : f.toMonoidHom.ker.comap R.subtype =
        f.toMonoidHom.ker.subgroupOf R := by
      rfl
    rw [heq, Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe hkerR).toEquiv]
    exact hcard
  have hkerP : IsPGroup 2 f.toMonoidHom.ker := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by simpa using hcard⟩
  have hRbarP : IsPGroup 2 Rbar := by
    have hM : IsPGroup 2 (Multiplicative ↥(traceZeroTwoSubgroup r)) := by
      intro z
      refine ⟨1, ?_⟩
      change z ^ 2 = 1
      rw [pow_two]
      ext i
      change (((Multiplicative.toAdd z : traceZeroTwoSubgroup r) :
          Fin r → ZMod 2) i) +
          (((Multiplicative.toAdd z : traceZeroTwoSubgroup r) :
          Fin r → ZMod 2) i) = 0
      exact CharTwo.add_self_eq_zero _
    exact hM.of_equiv eR.symm
  have hRP : IsPGroup 2 R := hRbarP.comap_of_ker_isPGroup f.toMonoidHom hkerP
  exact ⟨q, hqSurj, hqKer, hcardKer, hRP⟩

end GLS3.Chapter5.SchurPresentation
/- END Theory.TraceZeroRotationPreimageQuotient -/

/- BEGIN Theory.FixedPointPermutationSign -/
noncomputable section

namespace GLS3.Chapter5
universe __ch5_FixedPointPermutationSign_u

/-- Extending a permutation of the fixed points by the identity on the moved
points preserves its sign. -/
public theorem fixedPointPermutation_sign
    {Ω : Type __ch5_FixedPointPermutationSign_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (i : fixedPointPermutationSubgroup x) :
    Equiv.Perm.sign i.1.1 =
      Equiv.Perm.sign ((theorem_5_2_2_d_4 x) i) := by
  let e := theorem_5_2_2_d_4 x
  let __ch5_FixedPointPermutationSign_u := e i
  have hi : i = e.symm __ch5_FixedPointPermutationSign_u := by simp [__ch5_FixedPointPermutationSign_u]
  rw [hi, e.apply_symm_apply]
  dsimp [e, theorem_5_2_2_d_4, fixedPointPermMulEquivSubgroup]
  change Equiv.Perm.sign ((fixedPointPermToCentralizer x __ch5_FixedPointPermutationSign_u).1) =
    Equiv.Perm.sign __ch5_FixedPointPermutationSign_u
  rw [fixedPointPermToCentralizer_coe, Equiv.Perm.sign_ofSubtype]

end GLS3.Chapter5
/- END Theory.FixedPointPermutationSign -/

/- BEGIN Theory.InvolutionCyclePermutationSupport -/
noncomputable section

namespace GLS3.Chapter5
universe __ch5_InvolutionCyclePermutationSupport_u

/-- Under the natural cycle-permutation complement for an involution, every
moved nontrivial cycle contributes exactly two moved points. -/
public theorem involutionCyclePermutation_support_card_eq_two_mul
    {Ω : Type __ch5_InvolutionCyclePermutationSupport_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2)
    (l : cyclePermutationSubgroup x) :
    let e := theorem_5_2_2_d_3_a x (by simpa [hx] using Nat.prime_two)
    l.1.1.support.card = 2 * (e l).support.card := by
  dsimp only
  let hp : (orderOf x).Prime := by simpa [hx] using Nat.prime_two
  let e := theorem_5_2_2_d_3_a x hp
  rcases l.2 with ⟨q, hq⟩
  rw [← hq]
  change (Equiv.Perm.Basis.ofPermHom
    (Classical.choice (Equiv.Perm.Basis.nonempty x))
    (cycleActionRangeToExplicitRange x q)).support.card =
      2 * (e l).support.card
  rw [Equiv.Perm.Basis.card_ofPermHom_support]
  have hqval : (q : Equiv.Perm x.cycleFactorsFinset) = e l := by
    let e1 := cycleActionRangeMulEquivCyclePermutationSubgroup x
    let e2 := cycleActionRangeMulEquivPermOfPrimeOrder x hp
    have he1 : e1 q = l := by
      apply Subtype.ext
      exact hq
    have hqinv : e1.symm l = q := by
      rw [← he1]
      exact e1.symm_apply_apply q
    calc
      (q : Equiv.Perm x.cycleFactorsFinset) = e2 q := rfl
      _ = e2 (e1.symm l) := congrArg e2 hqinv.symm
      _ = e l := rfl
  change ∑ c ∈ (q : Equiv.Perm x.cycleFactorsFinset).support,
      c.1.support.card = 2 * (e l).support.card
  rw [hqval]
  simp_rw [cycleFactor_support_card_eq_orderOf_of_primeOrder x hp, hx]
  simp [Nat.mul_comm]

end GLS3.Chapter5
/- END Theory.InvolutionCyclePermutationSupport -/

/- BEGIN Theory.InvolutionCycleSwapSupport -/
noncomputable section
namespace GLS3.Chapter5
universe __ch5_InvolutionCycleSwapSupport_u

/-- Swapping two nontrivial cycles of an involution in the standard complement moves exactly the four points on those cycles. -/
public theorem involutionCycleSwap_support_card
    {Ω : Type __ch5_InvolutionCycleSwapSupport_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2)
    (c d : x.cycleFactorsFinset) (hcd : c ≠ d) :
    let e := theorem_5_2_2_d_3_a x (by simpa [hx] using Nat.prime_two)
    let l := e.symm (Equiv.swap c d)
    l.1.1.support.card = 4 := by
  dsimp only
  let hp : (orderOf x).Prime := by simpa [hx] using Nat.prime_two
  let e := theorem_5_2_2_d_3_a x hp
  let l := e.symm (Equiv.swap c d)
  rcases l.2 with ⟨q, hq⟩
  rw [← hq]
  change (Equiv.Perm.Basis.ofPermHom
    (Classical.choice (Equiv.Perm.Basis.nonempty x))
    (cycleActionRangeToExplicitRange x q)).support.card = 4
  rw [Equiv.Perm.Basis.card_ofPermHom_support]
  have hqval : (q : Equiv.Perm x.cycleFactorsFinset) = Equiv.swap c d := by
    have hel := e.apply_symm_apply (Equiv.swap c d)
    let e1 := cycleActionRangeMulEquivCyclePermutationSubgroup x
    let e2 := cycleActionRangeMulEquivPermOfPrimeOrder x hp
    have he1 : e1 q = l := by
      apply Subtype.ext
      exact hq
    have hqinv : e1.symm l = q := by
      rw [← he1]
      exact e1.symm_apply_apply q
    calc
      (q : Equiv.Perm x.cycleFactorsFinset) = e2 q := rfl
      _ = e2 (e1.symm l) := congrArg e2 hqinv.symm
      _ = e l := rfl
      _ = Equiv.swap c d := hel
  change ∑ c ∈ (q : Equiv.Perm x.cycleFactorsFinset).support,
      c.1.support.card = 4
  rw [hqval, Equiv.Perm.support_swap hcd]
  simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_singleton,
    hcd, not_false_eq_true]
  rw [cycleFactor_support_card_eq_orderOf_of_primeOrder x hp,
    cycleFactor_support_card_eq_orderOf_of_primeOrder x hp, hx]

end GLS3.Chapter5
/- END Theory.InvolutionCycleSwapSupport -/

/- BEGIN Theory.CoveringQuotientActionNoninner -/
noncomputable section

namespace GLS3.Chapter5

/-- A compatible action on the base of a covering cannot be inner when the
automorphism upstairs is non-inner. -/
public theorem coveringQuotientAction_noninner_of_noninner
    {K A : Type*} [Group K] [Finite K] [IsQuasisimple K]
    [Group A] [Finite A] [IsQuasisimple A]
    (f : Covering K A)
    (x : MulAut K) (β : MulAut A)
    (hcompat : ∀ k : K, f (x k) = β (f k))
    (hxNoninner : ∀ k : K, x ≠ MulAut.conj k) :
    ∀ a : A, β ≠ MulAut.conj a := by
  intro a hβ
  obtain ⟨k, hk⟩ := f.surjective a
  change f k = a at hk
  apply hxNoninner k
  apply MulEquiv.ext
  have hhom : x.toMonoidHom = (MulAut.conj k).toMonoidHom := by
    apply SchurPresentation.monoidHom_eq_of_isPerfect_of_comp_eq
      f.toMonoidHom f.ker_le_center
    apply MonoidHom.ext
    intro z
    calc
      f (x z) = β (f z) := hcompat z
      _ = a * f z * a⁻¹ := by rw [hβ]; rfl
      _ = f (k * z * k⁻¹) := by rw [map_mul, map_inv, map_mul, hk]
      _ = f ((MulAut.conj k) z) := rfl
  intro z
  exact DFunLike.congr_fun hhom z

end GLS3.Chapter5
/- END Theory.CoveringQuotientActionNoninner -/

/- BEGIN Theory.ProjectionKernelComplementDerived -/
noncomputable section

namespace GLS3.Chapter5.SchurPresentation

/-- If the derived restriction of a surjection onto a perfect group has
trivial kernel, then the original kernel and the derived subgroup are
complementary. -/
public theorem projectionKernel_isComplement'_commutator_of_derivedKernel_eq_bot
    {E B : Type*} [Group E] [Group B] [Group.IsPerfect B]
    (f : E →* B) (hf : Function.Surjective f)
    (hker : (f.comp (_root_.commutator E).subtype).ker = ⊥) :
    f.ker.IsComplement' (_root_.commutator E) := by
  let D := _root_.commutator E
  let fD := f.comp D.subtype
  have hfD : Function.Surjective fD := by
    have hmap : D.map f = ⊤ := by
      dsimp [D]
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf]
      exact Group.IsPerfect.commutator_eq_top
    intro y
    have hy : y ∈ D.map f := by rw [hmap]; trivial
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, hxy⟩
  have hdisj : Disjoint f.ker D := by
    rw [Subgroup.disjoint_def]
    intro x hxK hxD
    let d : D := ⟨x, hxD⟩
    have hdker : d ∈ fD.ker := by
      rw [MonoidHom.mem_ker]
      exact MonoidHom.mem_ker.mp hxK
    have hd1 : d = 1 := by
      rw [hker] at hdker
      exact Subgroup.mem_bot.mp hdker
    exact congrArg Subtype.val hd1
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj
  rw [Set.eq_univ_iff_forall]
  intro x
  obtain ⟨d, hd⟩ := hfD (f x)
  change f (d : E) = f x at hd
  apply Set.mem_mul.mpr
  refine ⟨x * (d : E)⁻¹, ?_, d, d.2, ?_⟩
  · change f (x * (d : E)⁻¹) = 1
    rw [map_mul, map_inv, hd]
    simp
  · simp

end GLS3.Chapter5.SchurPresentation
/- END Theory.ProjectionKernelComplementDerived -/
