module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.LocalGeometry.PermutationOvergroups.Sylow

/-!
# The inversion test for the seven-point image

An element centralizing one of the disjoint cycles (0 1 2), (4 5 6),
and inverting the other, is odd. An image containing A₇ and this element
is therefore all of S₇. The finite test concerns literal permutations;
its application to L₀ and L₁,+ still requires the marked residual calculation.

Source: Aschbacher–Smith, 13.8.24, printed p.958 (1 March 2004 manuscript).
-/

@[expose] public section
open Equiv Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection

/-- An order-three element on the four-point block. -/
def cycle012 : S7 := swap 0 1 * swap 1 2
/-- The distinguished order-three element on the three-point block. -/
def cycle456 : S7 := swap 4 5 * swap 5 6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
private theorem fourThree_inversion_test : ∀ x : FourThree,
    ((fourThreeHom x * cycle012 * (fourThreeHom x)⁻¹ = cycle012 ∧
      fourThreeHom x * cycle456 * (fourThreeHom x)⁻¹ = cycle456⁻¹) ∨
    (fourThreeHom x * cycle456 * (fourThreeHom x)⁻¹ = cycle456 ∧
      fourThreeHom x * cycle012 * (fourThreeHom x)⁻¹ = cycle012⁻¹)) →
    (fourThreeHom x).sign ≠ 1 := by
  decide +kernel

/-- Centralizing either marked cycle and inverting the other forces odd sign
for an element of the local partition stabilizer. -/
theorem odd_of_centralizes_and_inverts (t : S7) (htP : t ∈ fourThreeStabilizer)
    (ht : (t * cycle012 * t⁻¹ = cycle012 ∧ t * cycle456 * t⁻¹ = cycle456⁻¹) ∨
      (t * cycle456 * t⁻¹ = cycle456 ∧ t * cycle012 * t⁻¹ = cycle012⁻¹)) :
    t.sign ≠ 1 := by
  obtain ⟨x, rfl⟩ := htP
  exact fourThree_inversion_test x ht

/-- The image is all of S₇ once the source inversion produces the indicated
permutation. Surjectivity is a conclusion, not an assumption on the marking. -/
theorem surjective_of_centralizes_and_inverts {J : Type*} [Group J]
    (φ : J →* S7) (hAlt : alternatingGroup (Fin 7) ≤ φ.range)
    (t : J) (htP : φ t ∈ fourThreeStabilizer)
    (ht : (φ t * cycle012 * (φ t)⁻¹ = cycle012 ∧
        φ t * cycle456 * (φ t)⁻¹ = cycle456⁻¹) ∨
      (φ t * cycle456 * (φ t)⁻¹ = cycle456 ∧
        φ t * cycle012 * (φ t)⁻¹ = cycle012⁻¹)) : Function.Surjective φ := by
  rcases LocalGeometry.PermutationOvergroups.ambient_cases φ.range hAlt with h | h
  · exact MonoidHom.range_eq_top.mp h
  · have hm : φ t ∈ alternatingGroup (Fin 7) := h ▸ (show φ t ∈ φ.range from ⟨t, rfl⟩)
    exact (odd_of_centralizes_and_inverts (φ t) htP ht (Equiv.Perm.mem_alternatingGroup.mp hm)).elim

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection
