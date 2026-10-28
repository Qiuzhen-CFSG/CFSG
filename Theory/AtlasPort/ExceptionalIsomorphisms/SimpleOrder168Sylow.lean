module

/-
Adapted from Atlas/GroupTheory/SimpleOrder168Sylow.lean,
revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917, by Gerald Höhn
and the ATLAS contributors. ATLAS Research and Attribution License 1.0
applies; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Changes: Lean 4.33 module boundaries, narrow imports, and CFSG order APIs.
-/

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Simple
set_option warningAsError false

@[expose] public section

/-!
# The faithful Sylow-seven action at order 168

Sylow congruence and divisibility leave one or eight Sylow seven-subgroups.
Simplicity rules out one, and the transitive action on the eight subgroups
has trivial kernel because it is nontrivial. This supplies the abstract
count and faithfulness used for the concrete Singer-subgroup action.
-/


namespace Atlas.GroupTheory
open MulAction
local instance simpleOrder168SylowPrime1 : Fact (Nat.Prime 7) := ⟨by decide⟩

variable {G : Type*} [Group G] [Finite G]

theorem sylow_seven_card_of_168 (hG : Nat.card G = 168) (P : Sylow 7 G) :
    Nat.card P = 7 := by
  rw [Sylow.card_eq_multiplicity, hG]
  rw [show 168 = 7 * 24 from rfl,
    Nat.factorization_mul_apply_of_coprime (by decide : Nat.Coprime 7 24),
    (by decide : Nat.Prime 7).factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 24)]
  norm_num

theorem simple_order_168_sylow_seven_count [IsSimpleGroup G]
    (hG : Nat.card G = 168) : Nat.card (Sylow 7 G) = 8 := by
  let P : Sylow 7 G := Classical.choice inferInstance
  have hp := sylow_seven_card_of_168 hG P
  have hi : P.index = 24 := by
    have h := P.toSubgroup.card_mul_index
    rw [hp, hG] at h
    omega
  have hd := P.card_dvd_index
  rw [hi] at hd
  have hm : Nat.card (Sylow 7 G) % 7 = 1 := card_sylow_modEq_one 7 G
  have hb : Nat.card (Sylow 7 G) ≤ 24 := Nat.le_of_dvd (by decide) hd
  have hc : Nat.card (Sylow 7 G) = 1 ∨ Nat.card (Sylow 7 G) = 8 := by
    interval_cases h : Nat.card (Sylow 7 G) <;> omega
  rcases hc with hc | hc
  · have : Subsingleton (Sylow 7 G) := (Nat.card_eq_one_iff_unique.mp hc).1
    rcases (P.normal_of_subsingleton).eq_bot_or_eq_top with he | he
    · rw [show Nat.card P = Nat.card P.toSubgroup from rfl, he, Subgroup.card_bot] at hp
      omega
    · rw [show Nat.card P = Nat.card P.toSubgroup from rfl, he, Subgroup.card_top, hG] at hp
      omega
  · exact hc

theorem simple_order_168_sylow_seven_normalizer_card [IsSimpleGroup G]
    (hG : Nat.card G = 168) (P : Sylow 7 G) :
    Nat.card (Subgroup.normalizer (P : Set G)) = 21 := by
  have hi := P.card_eq_index_normalizer
  rw [simple_order_168_sylow_seven_count hG] at hi
  have hh := (Subgroup.normalizer (P : Set G)).card_mul_index
  rw [← hi, hG] at hh
  omega

theorem simple_order_168_sylow_seven_action_injective [IsSimpleGroup G]
    (hG : Nat.card G = 168) :
    Function.Injective (MulAction.toPermHom G (Sylow 7 G)) := by
  let f := MulAction.toPermHom G (Sylow 7 G)
  apply f.ker_eq_bot_iff.mp
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hs : Subsingleton (Sylow 7 G) := ⟨fun P Q => by
      obtain ⟨g, hg⟩ := exists_smul_eq G P Q
      have hmem : g ∈ f.ker := by rw [h]; trivial
      have he : f g = 1 := hmem
      have hf := congrArg (fun z : Equiv.Perm (Sylow 7 G) => z P) he
      exact hf.symm.trans hg⟩
    have hc := Nat.card_eq_one_iff_unique.mpr ⟨hs, inferInstance⟩
    have hd := simple_order_168_sylow_seven_count hG
    omega

end Atlas.GroupTheory
