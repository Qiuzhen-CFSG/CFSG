module
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags

/-!
# Cubic centralizers in the six-letter point stabilizer

A nonidentity cubic in the alternating group on the first four letters has
centralizer of order six in the stabilizer of {4,5}. Its two-elements are
therefore the identity and the complementary transposition (45).

The finite certificate ranges over 48 point-stabilizer words and the eight
cubics on four letters. The two-group conclusion then follows from injectivity
of cubing in a two-group; it does not enumerate ambient two-subgroups.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, 3.3.31,
printed p.602, the assertion about the centralizer of B modulo Q.
-/

public section
open Subgroup Equiv
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags
private def fourWords : List S := permsOfList [0, 1, 2, 3]
private def pointWords : List S := fourWords ++ fourWords.map (fun g => swap45 * g)

private theorem mem_fourWords {g : S} (h4 : g 4 = 4) (h5 : g 5 = 5) : g ∈ fourWords := by
  apply mem_permsOfList_of_mem
  intro x hx
  fin_cases x <;> simp_all

private theorem mem_pointWords {g : S} (h : g ∈ H1) : g ∈ pointWords := by
  rcases mem_H1_cases h with h | h
  · exact List.mem_append_left _ (mem_fourWords h.1 h.2)
  · apply List.mem_append_right
    apply List.mem_map.mpr
    refine ⟨swap45 * g, mem_fourWords ?_ ?_, ?_⟩
    · simp [swap45, Equiv.Perm.mul_apply, h.1]
    · simp [swap45, Equiv.Perm.mul_apply, h.2]
    · simp [swap45, ← mul_assoc]

private def cubicWords : List S := fourWords.filter (fun c => c ∈ K ∧ c ^ 3 = 1 ∧ c ≠ 1)

private theorem cubicCentralizer_cert : pointWords.all (fun g => cubicWords.all (fun c =>
    decide (c * g = g * c → g ^ 6 = 1 ∧ (g ^ 2 = 1 → g = 1 ∨ g = swap45)))) = true := by
  decide +kernel

theorem twoGroup_inf_cubic_centralizer_le (P : Subgroup S)
    (hP : IsPGroup 2 P) (hPH : P ≤ H1) {c : S}
    (hcK : c ∈ K) (hc3 : c ^ 3 = 1) (hcne : c ≠ 1) :
    P ⊓ centralizer ({c} : Set S) ≤ zpowers swap45 := by
  have hcert : ∀ g ∈ pointWords, ∀ c ∈ cubicWords,
      c * g = g * c → g ^ 6 = 1 ∧ (g ^ 2 = 1 → g = 1 ∨ g = swap45) := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using cubicCentralizer_cert
  have hcW : c ∈ cubicWords := List.mem_filter.mpr
    ⟨mem_fourWords hcK.1.1 hcK.1.2, by simp only [decide_eq_true_eq]; exact ⟨hcK, hc3, hcne⟩⟩
  rintro g ⟨hgP, hgc⟩
  have hr := hcert g (mem_pointWords (hPH hgP)) c hcW (hgc c (by simp))
  have hg6 : (⟨g, hgP⟩ : P) ^ 6 = 1 := Subtype.ext hr.1
  have hg2 : g ^ 2 = 1 := by
    have he : (⟨g, hgP⟩ : P) ^ 2 = 1 := by
      apply (hP.powEquiv (by decide : Nat.Coprime 2 3)).injective
      change ((⟨g, hgP⟩ : P) ^ 2) ^ 3 = (1 : P) ^ 3
      rw [← pow_mul, hg6, one_pow]
    exact congrArg Subtype.val he
  rcases hr.2 hg2 with rfl | rfl
  · exact one_mem _
  · exact mem_zpowers _
end Theory.SpecificGroups.SymmetricSix.BinaryFlags
