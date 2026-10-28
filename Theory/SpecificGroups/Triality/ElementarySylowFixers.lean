module

public import Theory.SpecificGroups.Triality.ParabolicOuterTwo.Extensions
public import Theory.SpecificGroups.Triality.RadicalCoordinates.Centers
public import Theory.GroupAction.ElementarySylowFixerBound

/-!
# Elementary Sylow fixers of the genuine group ³D₄(2)

The unipotent Sylow subgroup has center of order two. The outer automorphism
group has odd order, so every involution of the automorphism group is inner.
Consequently an elementary abelian group fixing a Sylow two-subgroup pointwise
has order at most two. This uses the genuine graph-field carrier throughout.

Source: Aschbacher--Smith 15.1.22(**),(4), printed p.1099; the underlying
root-group and automorphism results are cited in the imported modules.
-/

public section
namespace Triality.Standard
open Subgroup Parabolics Theory.GroupAction

/-- The center of every Sylow two-subgroup of ³D₄(2) has order two. -/
theorem binary_two_sylow_center_card
    (S : Sylow 2 (BinaryCarrier 1 Nat.zero_lt_one)) : Nat.card (center S) = 2 := by
  let P := binaryParameters 1 Nat.zero_lt_one
  let U := unipotentSylow P rfl
  have hU : Nat.card (center U) = 2 := by
    change Nat.card (center (unipotent P)) = 2
    simpa [P, Parameters.q, binaryParameters] using
      RadicalCoordinates.Centers.card_center_unipotent P rfl
  exact (Nat.card_congr (centerCongr (S.equiv U)).toEquiv).trans hU

/-- Elementary pointwise Sylow fixers have order at most two, despite the
nontrivial odd outer automorphisms of ³D₄(2). -/
theorem binary_two_elementary_sylow_fixer_card_le_two
    (S : Sylow 2 (BinaryCarrier 1 Nat.zero_lt_one))
    (A : Subgroup (MulAut (BinaryCarrier 1 Nat.zero_lt_one)))
    [IsElementaryAbelian 2 A]
    (hfix : ∀ a ∈ A, ∀ x ∈ S, a x = x) : Nat.card A ≤ 2 := by
  let : IsCyclic (center S) := isCyclic_of_prime_card (binary_two_sylow_center_card S)
  apply elementary_sylow_fixer_card_le_two_of_inner S
    (binaryCarrier_center_eq_bot 1 Nat.zero_lt_one) _ A hfix
  intro a ha _
  have hp : IsPGroup 2 (zpowers a) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    simpa only [Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one ha
  obtain ⟨g, hg⟩ := ParabolicOuterTwo.twoSubgroup_le_inner_at_two
    (zpowers a) hp (mem_zpowers a)
  exact ⟨g, hg.symm⟩

end Triality.Standard
