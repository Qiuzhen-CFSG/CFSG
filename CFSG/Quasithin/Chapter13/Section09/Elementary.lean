module

public import CFSG.Quasithin.Chapter13.Section09.SourceSetup
public import CFSG.Quasithin.Chapter1.Section01
public import Theory.SpecificGroups.Alternating.FourPairCore

/-!
# Initial consequences of the symmetric wreath configuration

The local subgroup has order 1152 and its Sylow two-subgroup has order 128.
Its two-core is nontrivial, and maximality among two-locals identifies the
normalizer of that core with the original subgroup. The latter is the first
normalizer equality in 13.9.2(4); the fusion assertions remain separate.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, setup for
13.9.1 and proof of 13.9.2, printed pp.969–970 (PDF pp.986–987).
-/

public section

namespace CFSG.Quasithin.Chapter13.Section09.Configuration

open Subgroup

variable {G : Type*} [Group G] (d : Configuration G)

theorem card_local : Nat.card d.M = 1152 :=
  (Nat.card_congr d.model.toEquiv).trans AlternatingFourPair.symmetric_wreath_card

theorem card_sylow [Finite G] : Nat.card d.T = 128 := by
  have hcard := (d.T.subtype d.sylow_le).card_eq_multiplicity
  have heq : Nat.card (d.T.subtype d.sylow_le) = Nat.card d.T :=
    Nat.card_congr (subgroupOfEquivOfLe d.sylow_le).toEquiv
  rw [heq, d.card_local] at hcard
  apply hcard.trans
  rw [show 1152 = 2 ^ 7 * 9 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 9)]
  norm_num

theorem twoCore_ne_bot : d.M.pCoreIn 2 ≠ ⊥ :=
  Chapter1.mem_H_of_isTwoLocal d.maximal.1

/-- The normalizer equality in 13.9.2(4), for the literal ambient two-core. -/
theorem normalizer_twoCore : normalizer (d.M.pCoreIn 2 : Set G) = d.M := by
  have hMN : d.M ≤ normalizer (d.M.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using (pCore 2 d.M).le_normalizer_map d.M.subtype
  exact le_antisymm
    (d.maximal.2 ⟨d.M.pCoreIn 2, d.twoCore_ne_bot,
      isPGroup_pCoreIn 2 d.M, rfl⟩ hMN) hMN

end CFSG.Quasithin.Chapter13.Section09.Configuration
