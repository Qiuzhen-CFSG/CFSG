module

public import CFSG.Quasithin.MainConverse.AlternatingSections.NineReduction.Primitive.SimpleRecognition.ActionBasics

/-!
# The order reduction for three-point rigidity in degree nine

In a triple-transitive action on nine points, every pointwise stabilizer
of three distinct points has index `9 * 8 * 7 = 504`. Thus the required
bound on fixed points of elements of the simple normal subgroup is
equivalent to that subgroup having order 504.

This module proves the orbit–stabilizer reduction. The remaining group
theory must establish the order alternatives 504 and 1512 and exclude
1512 for the simple subgroup. In particular, no trivial-stabilizer
assertion is made for the semilinear overgroup of order 1512.

Application: condition K in the alternating case of Aschbacher–Smith,
*The Classification of Quasithin Groups*, `refs/quasithin.pdf`, printed
pp.4 and 482. These are conditional reductions, not the completed
primitive-simple recognition theorem.
-/

namespace CFSG.Quasithin.MainConverse.NineReduction

open MulAction

private theorem triple_ncard (a b c : Fin 9)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Set (Fin 9)).ncard = 3 := by
  simp [hab, hac, hbc]

/-- The exact order formula for the three-point stabilizer in the subgroup
action used by degree-nine recognition. -/
public theorem nine_subgroup_card_eq_triple_fixing
    (H : Subgroup (alternatingGroup (Fin 9))) (N : Subgroup H)
    (hthree : IsMultiplyPretransitive N (Fin 9) 3)
    (a b c : Fin 9) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    504 * Nat.card (fixingSubgroup N ({a, b, c} : Set (Fin 9))) = Nat.card N := by
  have hs := triple_ncard a b c hab hac hbc
  have hi := IsMultiplyPretransitive.index_of_fixingSubgroup_eq
    (G := N) ({a, b, c} : Set (Fin 9)) (hs ▸ hthree)
  norm_num [hs, Nat.choose, Nat.factorial] at hi
  simpa only [hi] using (fixingSubgroup N ({a, b, c} : Set (Fin 9))).index_mul_card

/-- Triple transitivity reduces the fixed-point bound to the order 504.
The order equality is a remaining input, not a consequence of this lemma's
action hypotheses alone. -/
public theorem nine_subgroup_fixed_triple_bound_iff_card
    (H : Subgroup (alternatingGroup (Fin 9))) (N : Subgroup H)
    (hthree : IsMultiplyPretransitive N (Fin 9) 3) :
    (∀ g : N, g ≠ 1 → ∀ a b c : Fin 9,
      a ≠ b → a ≠ c → b ≠ c →
      ¬ (g • a = a ∧ g • b = b ∧ g • c = c)) ↔ Nat.card N = 504 := by
  constructor
  · intro hfixed
    have hD : fixingSubgroup N ({0, 1, 2} : Set (Fin 9)) = ⊥ := by
      apply le_bot_iff.mp
      intro g hg
      apply Subgroup.mem_bot.mpr
      by_contra hne
      apply hfixed g hne 0 1 2 (by decide) (by decide) (by decide)
      simpa only [mem_fixingSubgroup_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
        forall_eq_or_imp, forall_eq] using hg
    have hc := nine_subgroup_card_eq_triple_fixing H N hthree 0 1 2
      (by decide) (by decide) (by decide)
    simpa [hD] using hc.symm
  · intro hcard g hne a b c hab hac hbc hfix
    have hc := nine_subgroup_card_eq_triple_fixing H N hthree a b c hab hac hbc
    rw [hcard] at hc
    have hD : fixingSubgroup N ({a, b, c} : Set (Fin 9)) = ⊥ :=
      Subgroup.card_eq_one.mp (by omega)
    apply hne
    apply Subgroup.mem_bot.mp
    rw [← hD]
    simpa only [mem_fixingSubgroup_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      forall_eq_or_imp, forall_eq] using hfix

end CFSG.Quasithin.MainConverse.NineReduction
