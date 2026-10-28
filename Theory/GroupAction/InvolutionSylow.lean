module
public import Mathlib.GroupTheory.Sylow

/-!
# An invariant Sylow subgroup for an involution

An automorphism whose square is one acts through a two-group on the odd
number of Sylow 2-subgroups. Orbit counting supplies a fixed Sylow subgroup.
This elementary alignment is used by the graph-cocycle calculation in the
symplectic E.1.14 generation argument.
-/

open Subgroup
namespace MulAut
public theorem exists_fixed_sylow_two {G : Type*} [Group G] [Finite G]
    (a : MulAut G) (ha : a ^ 2 = 1) : ∃ S : Sylow 2 G, a • S = S := by
  let A := Subgroup.zpowers a
  have hp : IsPGroup 2 A := IsPGroup.of_card_dvd_pow (n := 1) (by
    simpa only [A, Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one ha)
  obtain ⟨S, hS⟩ := hp.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 G)
    (not_dvd_card_sylow 2 G)
  exact ⟨S, (MulAction.mem_fixedPoints.mp hS) ⟨a, mem_zpowers a⟩⟩

end MulAut
