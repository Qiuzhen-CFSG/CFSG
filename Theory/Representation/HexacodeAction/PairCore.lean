module

public import Theory.Representation.HexacodeAction.PairGeometry
public import Theory.Representation.BinaryPermutation.SixPairsQuadratic.Cosets
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# Two-subgroups in the hexacode pair stabilizer

The cubic coordinate kernel is disjoint from every two-subgroup. In the
even stabilizer of the pair {4,5}, every nontrivial normal subgroup contains
the Klein four on the complementary letters. For the latter calculation,
commutators with the two standard double transpositions reach that four-group;
a three-cycle permutes its three nonidentity elements. The finite permutation
identities below are checked by the kernel.

These are model calculations for the alternative pair-section argument in
Aschbacher–Smith 13.8.21(2), printed p.956 (PDF p.973). The underlying hexacode
and coordinate kernel are the attributed ATLAS constructions in the imports.
-/

public section
namespace Representation.Hexacode
open Atlas.Codes

/-- The actual coordinate map is faithful on every two-subgroup of the hexacode group. -/
theorem coordinate_injective_on_two_subgroup (Q : Subgroup HexAutomorphisms)
    (hQ : IsPGroup 2 Q) : Function.Injective (hexCoordinateSixHom.comp Q.subtype) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply Subgroup.injective_comp_subtype_of_coprime_ker hexCoordinateSixHom _ Q hQ
  rw [hexCoordinateSix_kernel, Nat.card_zpowers, hexZ_order]
  decide

end Representation.Hexacode

namespace BinaryPermutation.SixPairsQuadratic

private def kleinNonidentity (g : Equiv.Perm (Fin 6)) : Prop :=
  g = first ∨ g = second ∨ g = first * second

private instance (g : Equiv.Perm (Fin 6)) : Decidable (kleinNonidentity g) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private theorem pair_normal_check : ∀ g : Equiv.Perm (Fin 6),
    Equiv.Perm.sign g = 1 → pairPerm g basePair = basePair → g ≠ 1 →
    kleinNonidentity g ∨
      kleinNonidentity (g * (first * g⁻¹ * first⁻¹)) ∨
      kleinNonidentity (g * (second * g⁻¹ * second⁻¹)) := by
  decide +kernel

private abbrev cycle : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2

/-- A nontrivial subgroup of the even pair stabilizer, normalized by that
entire stabilizer, contains the two standard Klein four generators. -/
theorem basePair_normal_contains_klein (Q : Subgroup (Equiv.Perm (Fin 6)))
    (heven : Q ≤ alternatingGroup (Fin 6))
    (hfix : ∀ g ∈ Q, pairPerm g basePair = basePair)
    (hnormal : ∀ g : Equiv.Perm (Fin 6), Equiv.Perm.sign g = 1 →
      pairPerm g basePair = basePair → ∀ x ∈ Q, g * x * g⁻¹ ∈ Q)
    (hne : ∃ g ∈ Q, g ≠ 1) : first ∈ Q ∧ second ∈ Q := by
  obtain ⟨g,hg,hgne⟩ := hne
  have hfirst (x) (hx : x ∈ Q) : first * x * first⁻¹ ∈ Q :=
    hnormal first (by decide +kernel) (by decide +kernel) x hx
  have hsecond (x) (hx : x ∈ Q) : second * x * second⁻¹ ∈ Q :=
    hnormal second (by decide +kernel) (by decide +kernel) x hx
  have hy : ∃ y ∈ Q, kleinNonidentity y := by
    rcases pair_normal_check g (heven hg) (hfix g hg) hgne with h | h | h
    · exact ⟨g,hg,h⟩
    · exact ⟨_,Q.mul_mem hg (hfirst _ (Q.inv_mem hg)),h⟩
    · exact ⟨_,Q.mul_mem hg (hsecond _ (Q.inv_mem hg)),h⟩
  have hc (x) (hx : x ∈ Q) : cycle * x * cycle⁻¹ ∈ Q :=
    hnormal cycle (by decide +kernel) (by decide +kernel) x hx
  have hcf : cycle * first * cycle⁻¹ = first * second := by decide +kernel
  have hcs : cycle * second * cycle⁻¹ = first := by decide +kernel
  have hct : cycle * (first * second) * cycle⁻¹ = second := by decide +kernel
  obtain ⟨y,hy,heq | heq | heq⟩ := hy
  · subst y
    refine ⟨hy, ?_⟩
    have ht : first * second ∈ Q := hcf ▸ hc first hy
    exact hct ▸ hc _ ht
  · subst y
    exact ⟨hcs ▸ hc second hy,hy⟩
  · subst y
    have hs : second ∈ Q := hct ▸ hc _ hy
    exact ⟨hcs ▸ hc second hs,hs⟩

end BinaryPermutation.SixPairsQuadratic
