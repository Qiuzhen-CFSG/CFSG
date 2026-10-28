module

public import Theory.GroupTheory.PGroup.FrattiniActionImage
public import Mathlib.GroupTheory.IsPerfect

/-!
# Perfect actions on Frattini quotients

A perfect group acting nontrivially on a finite p-group also acts nontrivially
on its Frattini quotient. Otherwise its original image lies in Burnside's
Frattini automorphism kernel, so is both a p-group and perfect, hence trivial.

This supplies the nontriviality step in Aschbacher–Smith, A.1.29,
*The Classification of Quasithin Groups*, printed p.27.
-/

open Subgroup

namespace MonoidHom
/-- A nontrivial perfect action on a finite p-group stays nontrivial on its Frattini quotient. -/
public theorem frattini_comp_ne_one_of_isPerfect
    {A P : Type*} [Group A] [Group P] [Finite P] [Group.IsPerfect A]
    {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P) (a : A →* MulAut P) (ha : a ≠ 1) :
    (quotientAut (frattini P)).comp a ≠ 1 := by
  intro h
  have hi : IsPGroup p ((quotientAut (frattini P)).comp a).range := by
    rw [h, MonoidHom.range_one]
    exact IsPGroup.of_subsingleton _ _
  have hp := a.isPGroup_range_of_frattini_range hP hi
  let : Group.IsNilpotent a.range := hp.isNilpotent
  let : Group.IsPerfect a.range := Group.IsPerfect.range a
  have hs : Subsingleton a.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent a.range inferInstance
  apply ha
  apply MonoidHom.ext
  intro x
  exact congrArg Subtype.val (Subsingleton.elim (a.rangeRestrict x) 1)
end MonoidHom

