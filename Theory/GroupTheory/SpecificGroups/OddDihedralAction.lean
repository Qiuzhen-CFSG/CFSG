module

public import Theory.GroupTheory.DihedralTwoCore
public import Mathlib.Algebra.Group.PUnit

/-!
# Faithful actions of odd-dihedral groups

A nonabelian dihedral group with odd rotation order has trivial two-core:
the existing product theorem makes that core central, and the model center
is trivial. Thus any action whose kernel is a two-group is faithful, and
its image remains noncommutative. In particular no assertion that an
odd-dihedral image consists of inner automorphisms is needed.

Source: Aschbacher–Smith, proof of 2.5.21, printed p.567, mixed-action
calculation. The literal action consumer is PSL2PairSource.MixedAction.
-/

public section

open Subgroup
namespace Theory.GroupTheory

/-- A nonabelian odd-dihedral group has trivial two-core. -/
theorem odd_dihedral_twoCore_eq_bot {D : Type*} [Group D] [Finite D]
    {n : ℕ} (hn : Odd n) (hne : n ≠ 1) (e : D ≃* DihedralGroup n) :
    pCore 2 D = ⊥ := by
  let eprod : D ≃* DihedralGroup n × PUnit.{1} :=
    { toFun := fun a => (e a, PUnit.unit)
      invFun := fun a => e.symm a.1
      left_inv := e.symm_apply_apply
      right_inv := by rintro ⟨a, b⟩; simp
      map_mul' := by intros; ext; simp }
  have h := dihedralProduct_twoCore_le_center D PUnit.{1} n hn ⟨eprod⟩
  apply bot_unique
  intro a ha
  have hc : e a ∈ center (DihedralGroup n) := (centerCongr e ⟨a, h ha⟩).property
  rw [DihedralGroup.center_eq_bot_of_odd_ne_one hn hne, mem_bot] at hc
  exact mem_bot.mpr (e.injective (hc.trans e.map_one.symm))

/-- A two-group kernel cannot hide any part of a nonabelian odd-dihedral action. -/
theorem odd_dihedral_injective_of_two_kernel
    {D A : Type*} [Group D] [Finite D] [Group A]
    {n : ℕ} (hn : Odd n) (hne : n ≠ 1) (e : D ≃* DihedralGroup n)
    (f : D →* A) (hk : IsPGroup 2 f.ker) : Function.Injective f := by
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply bot_unique
  have hle : f.ker ≤ pCore 2 D := le_sSup ⟨inferInstance, hk⟩
  rwa [odd_dihedral_twoCore_eq_bot hn hne e] at hle

/-- A faithful odd-dihedral image is noncommutative, even in an outer
 automorphism group. -/
theorem odd_dihedral_range_not_commutative
    {D A : Type*} [Group D] [Group A]
    {n : ℕ} (hn : Odd n) (hne : n ≠ 1) (e : D ≃* DihedralGroup n)
    (f : D →* A) (hf : Function.Injective f) : ¬ IsMulCommutative f.range := by
  intro hc
  apply DihedralGroup.not_commutative hne (by intro h; exact hn.not_two_dvd_nat (by rw [h]))
  apply IsMulCommutative.of_comm
  intro a b
  apply e.symm.injective
  apply hf
  have hh := congrArg (fun y : f.range => y.val)
    (hc.is_comm.comm (f.rangeRestrict (e.symm a)) (f.rangeRestrict (e.symm b)))
  change f (e.symm a) * f (e.symm b) = f (e.symm b) * f (e.symm a) at hh
  simpa only [map_mul] using hh

end Theory.GroupTheory

end
