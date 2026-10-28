module
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
/-!
# Commutator bounds checked on generating sets

Modulo a normal target subgroup, pairwise commuting generators have
commuting generated subgroups. This allows a finite family of word
identities to certify a lower-central bound without enumerating the group.
The Rudvalis Sylow calculation for Aschbacher--Smith 15.1.22 is a consumer.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Theory.GroupTheory
variable {G I J : Type*} [Group G]
theorem commutator_closures_le_normal (a : I → G) (b : J → G)
    (N : Subgroup G) [N.Normal] (h : ∀ i j, ⁅a i,b j⁆ ∈ N) :
    ⁅closure (Set.range a), closure (Set.range b)⁆ ≤ N := by
  let q := QuotientGroup.mk' N
  rw [←QuotientGroup.ker_mk' N]
  apply (Subgroup.map_eq_bot_iff _).mp
  rw [map_commutator]
  apply commutator_eq_bot_iff_le_centralizer.mpr
  rw [MonoidHom.map_closure, MonoidHom.map_closure, centralizer_closure]
  apply (closure_le _).mpr
  rintro _ ⟨_,⟨i,rfl⟩,rfl⟩ _ ⟨_,⟨j,rfl⟩,rfl⟩
  apply Eq.symm
  apply commutatorElement_eq_one_iff_mul_comm.mp
  rw [←map_commutatorElement]
  exact (QuotientGroup.eq_one_iff _).mpr (h i j)
end Theory.GroupTheory
