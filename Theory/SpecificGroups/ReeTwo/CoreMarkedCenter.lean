module

public import Theory.SpecificGroups.ReeTwo.CoreRootConjugacy

/-!
# The characteristic marked center of the Ree core

The last root is the square of the middle root. Every automorphism sends the
middle root into the affine tail described in `CoreRootConjugacy`; squaring
any element of that tail gives the same last root. Thus all core automorphisms
fix the mark, which is also central by the coordinate multiplication.

Source: direct calculation in Shinoda (1975), (2.3), pp.81–82, using the
verified coordinates in `Core`.
-/

namespace ReeTwo.Core

/-- Every core automorphism preserves the marked last root. -/
public theorem aut_root_nine (a : MulAut Core) : a (root 9) = root 9 := by
  have hs : root 2 ^ 2 = root 9 := by decide +kernel
  rw [← hs, map_pow, hs]
  obtain ⟨h0, h1, h2, h3, h4⟩ := aut_root_two_head a
  rw [pow_two]
  change mul (a (root 2)) (a (root 2)) = ⟨0,0,0,0,0,0,0,0,0,1⟩
  apply Core.ext <;> simp [mul, h0, h1, h2, h3, h4]
  all_goals ring_nf
  all_goals reduce_mod_char

/-- The last root is central in the core. -/
public theorem root_nine_mem_center : root 9 ∈ Subgroup.center Core := by
  apply Subgroup.mem_center_iff.mpr
  intro x
  change mul x (root 9) = mul (root 9) x
  apply Core.ext <;> simp [mul, root, ofCoords]
  ring

end ReeTwo.Core
