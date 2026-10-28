module

public import Theory.Representation.NormalPSubgroupKernel
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Elementary subgroups in the central quotient of a faithful simple action

A central element of p-power order acts trivially on a simple representation
in characteristic p. Faithfulness therefore makes the quotient by the center
injective on every elementary abelian p-subgroup. This permits elementary
subgroup order bounds to pass from the central quotient to the original cover.

This is the central-kernel step in the defining-characteristic reductions of
Guralnick--Malle, *Classification of 2F-modules, II*, Sections 3 and 8.
No algebraic closure or absolute irreducibility is required.
-/

public section
namespace Representation
open Subgroup

variable {F G V : Type*} [Field F] [Group G] [Finite G]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {p : ℕ} [Fact p.Prime] [CharP F p]
  (ρ : Representation F G V) [IsIrreducible ρ]

/-- Central elements killed by the p-th power are trivial in a faithful simple action. -/
theorem central_eq_one_of_pow_prime (hf : Function.Injective ρ)
    {x : G} (hc : x ∈ center G) (hx : x ^ p = 1) : x = 1 := by
  have hZ : zpowers x ≤ center G := zpowers_le.mpr hc
  let : (zpowers x).Normal := ⟨fun n hn g => by
    rw [mem_center_iff.mp (hZ hn) g, mul_inv_cancel_right]
    exact hn⟩
  let : IsElementaryAbelian p (zpowers x) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one hx
  have hk := normal_p_subgroup_le_ker ρ (zpowers x)
    (IsElementaryAbelian.isPGroup p (zpowers x)) (mem_zpowers x)
  exact hf (hk.trans (map_one ρ).symm)

/-- The literal central quotient is injective on each elementary subgroup. -/
theorem centralQuotient_elementary_injective (hf : Function.Injective ρ)
    (A : Subgroup G) [IsElementaryAbelian p A] :
    Function.Injective ((QuotientGroup.mk' (center G)).comp A.subtype) := by
  apply (((QuotientGroup.mk' (center G)).comp A.subtype).ker_eq_bot_iff).mp
  apply le_bot_iff.mp
  intro a ha
  apply Subtype.ext
  apply central_eq_one_of_pow_prime ρ hf
  · exact (QuotientGroup.eq_one_iff (a : G)).mp ha
  · exact elemPow_eq_one_of_isElementaryAbelian (a : G) a.property

/-- Projecting an elementary subgroup preserves its actual order. -/
theorem card_map_centralQuotient (hf : Function.Injective ρ)
    (A : Subgroup G) [IsElementaryAbelian p A] :
    Nat.card (A.map (QuotientGroup.mk' (center G))) = Nat.card A := by
  let f := (QuotientGroup.mk' (center G)).comp A.subtype
  have h : Nat.card A = Nat.card f.range := Nat.card_congr
    (MonoidHom.ofInjective (centralQuotient_elementary_injective ρ hf A)).toEquiv
  simpa only [f, MonoidHom.range_comp, Subgroup.range_subtype] using h.symm

end Representation
