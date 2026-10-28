module

public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Checks
public import Theory.SpecificGroups.Held.Automorphisms.Reduction
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# A fixed involutory automorphism of the concrete Held group

The explicit ATLAS implementer normalizes Held because it sends both
standard generators into Held. Finiteness upgrades containment to equality.
Its fifth power induces an automorphism of order two, as witnessed by its
nontrivial action on the second generator. The subgroup to be analyzed is
therefore the literal fixed subgroup of an explicitly constructed action.

The quasisimple covering structure and coverage of all outer involutions
are separate obligations; neither follows just from the generator checks.
Source: ATLAS `HeG1-a2W1` and GLS3 Table 5.3p, the outer `2C` row.
-/

@[expose] public section
namespace Held.OuterInvolution

open Subgroup

/-- The checked implementer belongs to the full permutation normalizer. -/
theorem implementer_mem_normalizer :
    implementer ∈ normalizer (permutationGroup : Set (Equiv.Perm (Fin 2058))) := by
  rw [mem_normalizer_iff_map_conj_eq]
  apply eq_of_le_of_card_ge
  · rw [permutationGroup, MonoidHom.map_closure, closure_le]
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with rfl | hx
    · change implementer * atlasA * implementer⁻¹ ∈ closure {atlasA, atlasB}
      rw [conj_a]
      exact subset_closure (Set.mem_insert _ _)
    · rw [Set.mem_singleton_iff] at hx
      subst x
      change implementer * atlasB * implementer⁻¹ ∈ closure {atlasA, atlasB}
      rw [conj_b]
      have ha : atlasA ∈ closure ({atlasA, atlasB} : Set (Equiv.Perm (Fin 2058))) :=
        subset_closure (Set.mem_insert _ _)
      have hb : atlasB ∈ closure ({atlasA, atlasB} : Set (Equiv.Perm (Fin 2058))) :=
        subset_closure (Set.mem_insert_of_mem _ rfl)
      exact mul_mem (mul_mem (inv_mem (pow_mem (mul_mem ha (pow_mem hb 2)) 2)) hb)
        (pow_mem (mul_mem ha (pow_mem hb 2)) 2)
  · exact (Nat.card_congr ((MulAut.conj implementer).subgroupMap permutationGroup).toEquiv).le

/-- The fifth power of the ATLAS implementer, inside the full normalizer. -/
def representative : normalizer (permutationGroup : Set (Equiv.Perm (Fin 2058))) :=
  ⟨implementer ^ 5, pow_mem implementer_mem_normalizer 5⟩

/-- The induced automorphism of the literal Held carrier. -/
def action : MulAut He := permutationGroup.normalizerMonoidHom representative

theorem representative_sq : representative ^ 2 = 1 := by
  apply Subtype.ext
  change (implementer ^ 5) ^ 2 = 1
  rw [← pow_mul]
  exact tenth_power

theorem action_sq : action ^ 2 = 1 := by
  rw [action, ← map_pow, representative_sq, map_one]

/-- The action is nontrivial on the second distinguished generator. -/
theorem action_b_ne : action b ≠ b := by
  intro h
  have he := congrArg (fun x : He => representation x 0) h
  have hn : (implementer ^ 5 * atlasB * (implementer ^ 5)⁻¹) 0 ≠ atlasB 0 := by
    decide +kernel
  exact hn he

theorem action_order : orderOf action = 2 :=
  orderOf_eq_prime action_sq (fun h => action_b_ne (by rw [h]; rfl))

end Held.OuterInvolution
