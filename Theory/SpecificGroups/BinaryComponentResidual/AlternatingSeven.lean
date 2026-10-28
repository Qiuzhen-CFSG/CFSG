module

public import Theory.SpecificGroups.BinaryComponentResidual
public import Theory.Alternating.Aut

/-!
# Cubic-residual facts for the actual alternating group A₇

The odd-prime rank formula gives three-rank two. Conjugation realizes all
automorphisms by S₇, so the outer group is a quotient of S₇/A₇ and is a
two-group. Together with centerlessness these are precisely the facts used
in the ordinary A₇-block branch of original 15.1.25.

Source: GLS3 5.2.1; Aschbacher--Smith A.3.18 and 15.1.25, pp.51--52,1102.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.BinaryComponentResidual

theorem alternatingSeven : Facts (alternatingGroup (Fin 7)) := by
  refine ⟨alternatingGroup.center_eq_bot (by simp), ?_, ?_⟩
  · rw [GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 7 3 Nat.prime_three (by decide)]
  · let A := alternatingGroup (Fin 7)
    have htwo : IsPGroup 2 (Equiv.Perm (Fin 7) ⧸ A) := by
      apply IsPGroup.of_card (n := 1)
      rw [← A.index_eq_card, alternatingGroup.index_eq_two]
      rfl
    apply htwo.of_surjective (MulAut.outerAction A)
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup A) x
    obtain ⟨σ, rfl⟩ :=
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
        (by decide) (by decide)).surjective a
    exact ⟨QuotientGroup.mk' A σ, rfl⟩

end Theory.SpecificGroups.BinaryComponentResidual
