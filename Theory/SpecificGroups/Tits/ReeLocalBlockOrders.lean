module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics
public import Theory.SpecificGroups.Tits.FiniteSimple

/-!
# The order of the first marked Tits parabolic

The local presentation gives the upper bound 10240. The certified ambient
coset cover and the known order of the Parrott group give the matching lower
bound. The checked Parrott–Atlas isomorphism maps this subgroup onto the
first marked parabolic, as verified on all ten presentation generators.

This calculation needs neither an identification of the two-core nor the
disputed first-parabolic invariants in F.1.12(I)(9). Its prime divisors are
used in the local-block argument of Aschbacher–Smith 2.3.9(7), printed p.526.
Source: Parrott, A Characterization of the Tits' Simple Group (1972), §5,
p.683, and the certified comparison in `Theory.SpecificGroups.Tits.FiniteSimple`.
-/

@[expose] public section

namespace Tits.ReeLocalBlockOrders

open Subgroup ExceptionalParabolics

/-- Exact order of the subgroup generated without the second reflection. -/
theorem r1_card : Nat.card parrottR1Subgroup = 10240 := by
  have hu := parrottR1Subgroup_finite_card_le.2
  have hl := parrottAmbientR1CosetCover.finite_card_le.2
  rw [parrottGroup_card] at hl
  omega

/-- The checked presentation isomorphism preserves the first marked parabolic. -/
theorem first_map :
    parrottR1Subgroup.map parrottFiniteImageEquiv.toMonoidHom = first := by
  rw [parrottR1Subgroup, MonoidHom.map_closure]
  have hmem (i : ParrottGenerator) (hi : i ≠ .r8) :
      atlas1600ParrottAssignment i ∈ Subgroup.closure
        (parrottFiniteImageEquiv.toMonoidHom ''
          (parrottGenerator '' {i | i ≠ .r8})) :=
    Subgroup.subset_closure
      ⟨_, ⟨i, hi, rfl⟩, parrottFiniteImageEquiv_generator i⟩
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro x ⟨y, ⟨i, hi, rfl⟩, rfl⟩
    change parrottFiniteImageEquiv (parrottGenerator i) ∈ first
    rw [parrottFiniteImageEquiv_generator]
    cases i with
    | r1 => exact reflection_mem_first
    | r8 => exact (hi rfl).elim
    | s1 | s2 | s3 | s4 | s5 | s6 | s7 | s8 =>
      apply sylow_le_first
      rw [S, atlas1600SylowTwoSubgroup_eq]
      exact Subgroup.subset_closure (by simp)
  · apply sup_le
    · rw [S, atlas1600SylowTwoSubgroup_eq]
      apply (closure_le _).mpr
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact hmem _ (by decide)
    · apply (closure_le _).mpr
      rintro x (rfl : x = atlas1600ParrottAssignment .r1)
      apply Subgroup.subset_closure
      exact ⟨_, ⟨.r1, by decide, rfl⟩, parrottFiniteImageEquiv_generator .r1⟩

/-- Exact order of the first concrete Atlas parabolic. -/
theorem first_card : Nat.card first = 10240 := by
  rw [← first_map, Subgroup.card_map_of_injective
    (f := parrottFiniteImageEquiv.toMonoidHom) parrottFiniteImageEquiv.injective]
  exact r1_card
end Tits.ReeLocalBlockOrders

end
