module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.Push

/-!
# Generation by noncommuting subgroups in S₃

For any noncommuting pair of permutations on three letters, words of
length at most three cover the group. The finite word check is verified
by the kernel. Thus two subgroups with nontrivial commutator generate S₃.

Source application: Aschbacher–Smith, *The Classification of Quasithin
Groups*, Theorem 15.3.1, printed p.1155 (PDF p.1172).
-/

public section
namespace Subgroup

private theorem s3_words : ∀ a b x : Equiv.Perm (Fin 3), a * b ≠ b * a →
    x = 1 ∨ x = a ∨ x = b ∨ x = a * b ∨ x = b * a ∨
      x = a * a ∨ x = b * b ∨ x = a * b * a := by decide +kernel

/-- Two noncentralizing subgroups of S₃ generate S₃. -/
theorem sup_eq_top_of_symmetricThree_commutator_ne_bot (A B : Subgroup (Equiv.Perm (Fin 3)))
    (hne : ⁅A,B⁆ ≠ ⊥) : A ⊔ B = ⊤ := by
  classical
  have hn : ¬ A ≤ centralizer (B : Set (Equiv.Perm (Fin 3))) := by
    simpa only [← commutator_eq_bot_iff_le_centralizer] using hne
  obtain ⟨a, ha, hna⟩ := SetLike.not_le_iff_exists.mp hn
  change ¬ ∀ b ∈ B, b * a = a * b at hna
  push Not at hna
  obtain ⟨b, hb, hab⟩ := hna
  have haK : a ∈ A ⊔ B := (le_sup_left : A ≤ A ⊔ B) ha
  have hbK : b ∈ A ⊔ B := (le_sup_right : B ≤ A ⊔ B) hb
  apply top_unique
  intro x _
  rcases s3_words a b x (Ne.symm hab) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact haK
  · exact hbK
  · exact mul_mem haK hbK
  · exact mul_mem hbK haK
  · exact mul_mem haK haK
  · exact mul_mem hbK hbK
  · exact mul_mem (mul_mem haK hbK) haK
end Subgroup
