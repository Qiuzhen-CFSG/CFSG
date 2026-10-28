module

public import CFSG.Quasithin.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Supplying proper-K by induction on group order

Every simple section of a proper subgroup of a finite group has strictly
smaller order than the ambient group. Thus the smaller-simple-group induction
hypothesis supplies exactly the proper-K input of the quasithin theorem.
No classification of the proper subgroups of individual known models is needed
for this step.

The final theorem packages strong induction for any class of groups: a proof
that every finite simple group with proper K-subgroups belongs to K suffices
to classify all finite simple groups. Its induction step remains an explicit
premise; this module does not prove that step or the quasithin classification.

Source: the proper-K hypothesis of Aschbacher–Smith, *The Classification of
Quasithin Groups*, §0.1, printed pp. 4 and 482. The proof uses subgroup order
monotonicity, the cardinality bound for a surjection, and strong induction.
-/

public section

namespace CFSG.Quasithin

universe u

/-- Classification of smaller simple groups supplies the proper-K hypothesis. -/
theorem hasProperKSubgroups_of_smaller_simple
    (K : GroupClass.{u}) (G : Type u) [Group G] [Finite G]
    (hsmaller : ∀ (S : Type u) [Group S] [Finite S] [IsSimpleGroup S],
      Nat.card S < Nat.card G → K S) : HasProperKSubgroups K G := by
  intro U hU S _ hS V f hf
  let : IsSimpleGroup S := hS
  let : Finite S := Finite.of_surjective f hf
  apply hsmaller S
  have hUcard : Nat.card U < Nat.card G :=
    lt_of_le_of_ne U.card_le_card_group (fun h => hU (U.eq_top_of_card_eq h))
  exact lt_of_le_of_lt ((Nat.card_le_card_of_surjective f hf).trans
    V.card_le_card_group) hUcard

/-- The exact input to quasithin classification at a simple induction step. -/
theorem isSimpleQTKE_of_smaller_simple
    (K : GroupClass.{u}) (G : Type u) [Group G] [Finite G] [IsSimpleGroup G]
    (hsmaller : ∀ (S : Type u) [Group S] [Finite S] [IsSimpleGroup S],
      Nat.card S < Nat.card G → K S)
    (hna : ¬ IsMulCommutative G) (hqt : IsQuasithin G)
    (he : IsEvenCharacteristic G) : IsSimpleQTKE K G :=
  ⟨⟨hqt, hasProperKSubgroups_of_smaller_simple K G hsmaller, he⟩,
    inferInstance, hna⟩

/-- Strong induction reduces membership of every finite simple group in K to
the case where its proper subgroups are K-groups. The premise must be supplied
by the complete classification argument, including all its cases. -/
theorem simple_mem_of_properK_induction
    (K : GroupClass.{u})
    (step : ∀ (S : Type u) [Group S] [Finite S] [IsSimpleGroup S],
      HasProperKSubgroups K S → K S)
    (G : Type u) [Group G] [Finite G] [IsSimpleGroup G] : K G := by
  have hcard : ∀ n : ℕ, ∀ (S : Type u) [Group S] [Finite S] [IsSimpleGroup S],
      Nat.card S = n → K S := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S _ _ _ hS
      apply step S
      apply hasProperKSubgroups_of_smaller_simple K S
      intro T _ _ _ hT
      exact ih (Nat.card T) (hS ▸ hT) T rfl
  exact hcard (Nat.card G) G rfl

end CFSG.Quasithin
