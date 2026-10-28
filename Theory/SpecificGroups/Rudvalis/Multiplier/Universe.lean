module

public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary
public import Mathlib.Algebra.Group.Shrink

/-!
# The Rudvalis central-cover bound in every universe

Shrink the finite source of a perfect central cover to a small carrier,
apply the native kernel bound, and transport the literal kernel back. This
supplies arbitrary ambient groups in the original14.7.68 application.
Source: Aschbacher–Smith I.1.3 and14.7.68, printed pp.407 and1071.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace Rudvalis.Multiplier

theorem cover_kernel_card_le_two_any_universe
    {E : Type*} [Group E] [Finite E] (c : PerfectCentralCovering.Cover E Model) :
    Nat.card c.toMonoidHom.ker ≤ 2 := by
  let s : Shrink.{0} E ≃* E := Shrink.mulEquiv
  let : Finite (Shrink.{0} E) := Finite.of_equiv E s.symm.toEquiv
  let g := c.toMonoidHom.comp s.toMonoidHom
  let : Group.IsPerfect E := c.isPerfect
  let : Group.IsPerfect (Shrink.{0} E) :=
    Group.IsPerfect.ofSurjective (f := s.symm.toMonoidHom) s.symm.surjective
  have hgc : g.ker ≤ center (Shrink.{0} E) := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply s.injective
    simpa only [map_mul,MulEquiv.coe_toMonoidHom] using
      mem_center_iff.mp (c.ker_le_center hx) (s y)
  let gc : PerfectCentralCovering.Cover (Shrink.{0} E) Model :=
    { toMonoidHom := g, surjective := c.surjective.comp s.surjective,
      isPerfect := inferInstance, ker_le_center := hgc }
  have hc := kernel_card_le_two gc
  change Nat.card g.ker ≤ 2 at hc
  rw [show g.ker = c.toMonoidHom.ker.map s.symm.toMonoidHom from
    MonoidHom.ker_comp_mulEquiv c.toMonoidHom s,card_map_of_injective s.symm.injective] at hc
  exact hc
end Rudvalis.Multiplier
