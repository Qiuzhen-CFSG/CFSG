module

public import Theory.Character.ClassFunction
public import Theory.Character.FiniteOrderTrace

/-!
# Character values and representation kernels

For a finite group, an element lies in the kernel of a complex representation
exactly when its character value equals its degree. The finite-order trace
criterion proves the nontrivial implication. Thus a nonconstant character
which equals its degree on a subgroup gives a proper normal overgroup.

The degree-one specialization is the final kernel step in Brauer,
*Some applications of the theory of blocks of characters of finite groups. II*,
J. Algebra 1 (1964), §VI, p.319.
-/

public section

namespace Representation

variable {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The character detects the kernel of a finite-group complex representation. -/
theorem mem_ker_iff_character_eq_degree (ρ : Representation ℂ G V) (g : G) :
    g ∈ ρ.ker ↔ ρ.character g = ρ.character 1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hg
    simp [character, hg]
  · intro hg
    apply finite_order_end_eq_one_of_trace_eq_finrank (ρ g) (orderOf_pos g).ne'
    · rw [← map_pow, pow_orderOf_eq_one, map_one]
    · rw [char_one] at hg
      exact hg

end Representation

namespace IsCharacter

variable {G : Type*} [Group G] [Finite G] {χ : ClassFunction G}

/-- A character constant at its degree on `H`, but not on `G`, supplies a
proper normal subgroup containing `H`. -/
theorem exists_proper_normal_overgroup (hχ : IsCharacter χ) (H : Subgroup G)
    (hne : χ ≠ fun _ => χ 1) (hH : ∀ g ∈ H, χ g = χ 1) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊤ ∧ H ≤ N := by
  obtain ⟨n, ρ, rfl⟩ := hχ
  refine ⟨ρ.ker, inferInstance, ?_, ?_⟩
  · intro htop
    apply hne
    funext g
    exact (ρ.mem_ker_iff_character_eq_degree g).mp (htop ▸ Subgroup.mem_top g)
  · intro g hg
    exact (ρ.mem_ker_iff_character_eq_degree g).mpr (hH g hg)

/-- A nonprincipal degree-one character equal to one on `H` has a proper
normal kernel containing `H`. Irreducibility is not needed separately. -/
theorem exists_proper_normal_overgroup_of_degree_one (hχ : IsCharacter χ)
    (H : Subgroup G) (hdegree : χ 1 = 1) (hne : χ ≠ 1)
    (hH : ∀ g ∈ H, g ≠ 1 → χ g = 1) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊤ ∧ H ≤ N := by
  apply hχ.exists_proper_normal_overgroup H
  · intro heq
    apply hne
    funext g
    simpa only [hdegree, Pi.one_apply] using congrFun heq g
  · intro g hg
    by_cases h : g = 1
    · rw [h]
    · rw [hH g hg h, hdegree]

end IsCharacter
