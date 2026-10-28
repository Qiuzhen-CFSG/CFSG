module
public import Theory.GroupAction.SubgroupCentralizerCongruence
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Sylow

/-!
# Elementary sections normalized by a subgroup with a nine-factor

Suppose every involution centralizer in a finite group has order prime to
nine. A subgroup whose order is divisible by nine normalizes an elementary
two-subgroup only if its order is congruent to one modulo three. Indeed,
a Sylow three-subgroup of the normalizer acts on the elementary subgroup.
Any nonidentity fixed point would be an involution with centralizer order
divisible by nine. Orbit counting therefore leaves precisely one fixed point.

This gives the full original-action obstruction for the Ru row in
Aschbacher--Smith, proof of 12.6.12, printed pp.825--826. It uses the literal
ambient centralizers and normalized elementary subgroup.
-/

public section
open Subgroup

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A nine-factor in the normalizing subgroup forces the elementary order to be one modulo three. -/
theorem elementary_card_mod_three_of_involution_centralizers
    (hcentral : ∀ t : G, orderOf t = 2 → ¬ 9 ∣ Nat.card (centralizer ({t} : Set G)))
    (B E : Subgroup G) [IsElementaryAbelian 2 E]
    (hB : 9 ∣ Nat.card B) (hn : B ≤ normalizer (E : Set G)) :
    Nat.card E % 3 = 1 := by
  let P : Sylow 3 B := Classical.choice inferInstance
  let A := (P : Subgroup B).map B.subtype
  have hA : IsPGroup 3 A := P.isPGroup'.map B.subtype
  have hAB : A ≤ B := map_subtype_le _
  have h9 : 9 ∣ Nat.card A := by
    rw [card_map_of_injective B.subtype_injective]
    exact P.pow_dvd_card_of_pow_dvd_card (n := 2) hB
  have hC : E ⊓ centralizer (A : Set G) = ⊥ := by
    apply bot_unique
    rintro t ⟨htE,htA⟩
    change t = 1
    by_contra ht
    have ho : orderOf t = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian _ htE) ht
    have hAt : A ≤ centralizer ({t} : Set G) := by
      intro a ha
      exact mem_centralizer_singleton_iff.mpr (htA a ha)
    exact hcentral t ho (h9.trans (card_dvd_of_le hAt))
  have hm := card_modEq_card_inf_centralizer A E hA (hAB.trans hn)
  rw [hC,card_bot] at hm
  exact hm
end Subgroup
