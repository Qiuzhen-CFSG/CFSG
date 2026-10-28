module
public import Theory.SpecificGroups.SymmetricFive.OddLocal
public import Theory.GroupTheory.CoprimeQuotientSubgroups
/-!
# Cubic Sylow subgroups of two-kernel five-point groups

A map to S₅ with two-group kernel is injective on every Sylow three-group.
Its image is an odd subgroup of S₅, hence cyclic. This supplies the rank-one
bound on all quotient actions used to exclude the two-factor B.6.9 row.
Source: Aschbacher–Smith C.1.26, p.132, in the application 14.7.68(2), p.1071.
-/
public section
open Subgroup
namespace SymmetricFive
variable {G : Type*} [Group G] [Finite G]
theorem cyclic_three_sylow_of_two_kernel
    (f : G →* Equiv.Perm (Fin 5)) (hf : IsPGroup 2 f.ker)
    (P : Sylow 3 G) : IsCyclic P := by
  have hc : Nat.Coprime 3 (Nat.card f.ker) := by
    obtain ⟨n, hn⟩ := hf.exists_card_eq
    rw [hn]
    exact (show Nat.Coprime 3 2 by decide).pow_right n
  have hi := injective_comp_subtype_of_coprime_ker f hc (P : Subgroup G) P.isPGroup'
  let E := (P : Subgroup G).map f
  have hE : IsPGroup 3 E := P.isPGroup'.map f
  obtain ⟨n, hn⟩ := hE.exists_card_eq
  have ho : Odd (Nat.card E) := hn ▸ (show Odd 3 by decide).pow
  have he : IsCyclic E := by
    rcases SymmetricFive.odd_subgroup_card E ho with h | h | h
    · have : Subsingleton E := (Nat.card_eq_one_iff_unique.mp h).1
      infer_instance
    · exact isCyclic_of_prime_card h
    · let : Fact (Nat.Prime 5) := ⟨by decide⟩
      exact isCyclic_of_prime_card h
  let := he
  exact isCyclic_of_injective (f.subgroupMap (P : Subgroup G))
    (fun x y h => hi (congrArg Subtype.val h))

end SymmetricFive
