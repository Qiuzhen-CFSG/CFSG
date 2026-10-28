module
public import Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings.TwoKernel
public import Theory.SpecificGroups.Alternating.EightFourNormalizer

/-!
# Sylow normalizer indices of the actual A6 sections in A8

Every embedded A6 is an even pointwise pair stabilizer. Its normalizer
contains A6 and has order at most 720, so its order divides 720. A two-core
section with quotient A6 has trivial two-core in A8. Its normalizer therefore
meets a Sylow two-subgroup in order at most sixteen, giving index at least four.

The consumer excludes the binary-four canonical component at the original
preferred nonsingular point, whose relative Sylow index is at most two.
Source: Aschbacher--Smith 12.6.18, printed p.827, combined manuscript
of 1 March 2004. All embeddings and two-core quotients are retained.
-/

public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings

/-- The normalizer of every actual A6 embedding has order dividing 720. -/
theorem six_normalizer_card_dvd (A : Subgroup A8) (e : A ≃* A6) :
    Nat.card (normalizer (A : Set A8)) ∣ 720 := by
  let f := A.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := A.subtype_injective.comp e.symm.injective
  have hr : f.range = A := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.symm.surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  have hb := normalizer_card_le f hf
  rw [hr] at hb
  have hd : 360 ∣ Nat.card (normalizer (A : Set A8)) := by
    have hc : Nat.card A = 360 := (Nat.card_congr e.toEquiv).trans card_A6
    exact hc ▸ card_dvd_of_le A.le_normalizer
  obtain ⟨n,hn⟩ := hd
  have hp : 0 < Nat.card (normalizer (A : Set A8)) := Nat.card_pos
  have he : n = 1 ∨ n = 2 := by omega
  rcases he with rfl | rfl <;> norm_num [hn]

/-- Every A6 two-core section has normalizer index at least four in a Sylow of A8. -/
theorem six_section_sylow_index_ge_four (A : Subgroup A8)
    (e : (A ⧸ pCore 2 A) ≃* A6) (S : Sylow 2 A8) :
    4 ≤ (normalizer (A : Set A8)).relIndex (S : Subgroup A8) := by
  obtain ⟨a⟩ := six_section_image (MonoidHom.id A8)
    (by rw [MonoidHom.ker_id]; exact IsPGroup.of_card (n := 0) (by simp)) A e
  let a' : A ≃* A6 := (A.equivMapOfInjective (MonoidHom.id A8) Function.injective_id).trans a
  let N := normalizer (A : Set A8)
  let P := (S : Subgroup A8)
  have hc : Nat.card P = 64 := by
    have hh := AlternatingEight.sylow_image_card S
    rwa [card_map_of_injective A8.subtype_injective] at hh
  have hd : Nat.card (N ⊓ P : Subgroup A8) ∣ 16 := by
    have h64 : Nat.card (N ⊓ P : Subgroup A8) ∣ 64 :=
      hc ▸ card_dvd_of_le (show N ⊓ P ≤ P from inf_le_right)
    have h720 : Nat.card (N ⊓ P : Subgroup A8) ∣ 720 :=
      (card_dvd_of_le (show N ⊓ P ≤ N from inf_le_left)).trans (six_normalizer_card_dvd A a')
    exact Nat.dvd_gcd h64 h720
  have hb := Nat.le_of_dvd (by decide : 0 < 16) hd
  have hm : Nat.card (N ⊓ P : Subgroup A8) * N.relIndex P = 64 := by
    simpa only [relIndex_bot_left,inf_relIndex_right,hc] using
      relIndex_mul_relIndex (⊥ : Subgroup A8) (N ⊓ P) P bot_le inf_le_right
  change 4 ≤ N.relIndex P
  by_contra hn
  have hi : N.relIndex P ≤ 3 := by omega
  have hh := Nat.mul_le_mul hb hi
  rw [hm] at hh
  norm_num at hh
end Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings
