module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.Profiles.Collection
public import Mathlib.Data.List.GetD

/-!
# Certification adapters for the full centralizers

A finite list of right-coset representatives covers the presented group if it
contains the identity and is closed, modulo the candidate subgroup, under
right multiplication by every canonical generator. Positive normal forms
suffice for the induction, so no normality or index assumption is needed.

If the candidate centralizes the family and only the identity representative
centralizes it, this cover proves equality with the full centralizer. The
concrete checks use the proved relation rewriter; the order hypothesis is used
only to separate distinct normal forms in the noncentralizing representatives.

Source context: Kleidman–Wilson (1988), pp. 484–510; the literal masks and
inverse-conjugation convention are in `SylowNormalEights/source/README.md`.
-/

@[expose] public section

namespace Janko4.LocalStructure.SylowNormalEights.Presentation.Profiles.FullCentralizers

def representatives (i : Fin 3) : Fin 8 → Fin (2 ^ 21) :=
  ![![0, 4, 32, 36, 256, 260, 288, 292],
    ![0, 32, 128, 160, 4096, 4128, 4224, 4256],
    ![0, 32, 128, 160, 4096, 4128, 4224, 4256]] i

@[simp] theorem normalForm_zero : normalForm 0 = 1 := by
  change wordValue (maskWord 0) = 1
  rfl

@[simp] theorem representatives_zero (i : Fin 3) : representatives i 0 = 0 := by
  fin_cases i <;> rfl

def familyMask (i : Fin 3) : Fin 3 → Fin (2 ^ 21) :=
  ![![262144, 524288, 1048576], ![131072, 524288, 1048576],
    ![393216, 524288, 1048576]] i

theorem normalForm_familyMask (i k : Fin 3) :
    normalForm (familyMask i k) = familyGenerator i k := by
  rw [← wordValue_maskWord]
  fin_cases i <;> fin_cases k
  · exact mul_one _
  · exact mul_one _
  · exact mul_one _
  · exact mul_one _
  · exact mul_one _
  · exact mul_one _
  · exact congrArg (generator 17 * ·) (mul_one (generator 18))
  · exact mul_one _
  · exact mul_one _

private theorem cover_of_steps (C : Subgroup Carrier) (r : Fin 8 → Carrier) (h0 : r 0 = 1)
    (hs : ∀ a g, ∃ b, r a * generator g * (r b)⁻¹ ∈ C)
    (x : Carrier) : ∃ a, x * (r a)⁻¹ ∈ C := by
  have hw (w : List (Fin 21)) : ∀ y : Carrier,
      (∃ a, y * (r a)⁻¹ ∈ C) → ∃ b, y * wordValue w * (r b)⁻¹ ∈ C := by
    induction w with
    | nil => intro y hy; simpa only [wordValue_nil, mul_one] using hy
    | cons g w ih =>
      rintro y ⟨a, ha⟩
      obtain ⟨b, hb⟩ := hs a g
      have hy : y * generator g * (r b)⁻¹ ∈ C := by
        have h := C.mul_mem ha hb
        simpa only [mul_assoc, inv_mul_cancel_left] using h
      simpa only [wordValue_cons, mul_assoc] using ih (y * generator g) ⟨b, hy⟩
  obtain ⟨m, rfl⟩ := normalForm_surjective x
  simpa only [wordValue_maskWord, one_mul] using
    hw (maskWord m) 1 ⟨0, by simpa only [h0, inv_one, mul_one] using C.one_mem⟩

theorem eq_of_steps_and_separation (i : Fin 3)
    (hle : centralizerCandidate i ≤ Subgroup.centralizer (family i : Set Carrier))
    (hs : ∀ a g, ∃ b, normalForm (representatives i a) * generator g *
      (normalForm (representatives i b))⁻¹ ∈ centralizerCandidate i)
    (hsep : ∀ a, normalForm (representatives i a) ∈
      Subgroup.centralizer (family i : Set Carrier) → a = 0) :
    centralizerCandidate i = Subgroup.centralizer (family i : Set Carrier) := by
  apply le_antisymm hle
  intro x hx
  obtain ⟨a, ha⟩ := cover_of_steps (centralizerCandidate i)
    (fun a => normalForm (representatives i a)) (by simp) hs x
  have hr : normalForm (representatives i a) ∈
      Subgroup.centralizer (family i : Set Carrier) := by
    have h := (Subgroup.centralizer (family i : Set Carrier)).mul_mem
      ((Subgroup.centralizer (family i : Set Carrier)).inv_mem (hle ha)) hx
    simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] using h
  have he := hsep a hr
  simpa only [he, representatives_zero, normalForm_zero, inv_one, mul_one] using ha

private theorem masks_mem (i : Fin 3) (w : List (Fin (2^21)))
    (hw : ∀ m ∈ w, m ∈ centralizerMasks i) :
    wordValue (w.flatMap maskWord) ∈ centralizerCandidate i := by
  induction w with
  | nil => exact (centralizerCandidate i).one_mem
  | cons m w ih =>
    rw [List.flatMap_cons, wordValue_append, wordValue_maskWord]
    apply (centralizerCandidate i).mul_mem
    · exact Subgroup.subset_closure (List.mem_map.mpr ⟨m, hw m List.mem_cons_self, rfl⟩)
    · exact ih (fun m hm => hw m (List.mem_cons_of_mem _ hm))

theorem step_of_collect (i : Fin 3) (r t c : Fin (2^21)) (g : Fin 21)
    (w : List (Fin (2^21))) (n₁ n₂ : ℕ)
    (hm : w.Forall (fun m => m ∈ centralizerMasks i))
    (h₁ : collect n₁ (maskWord r ++ [g]) = maskWord c)
    (h₂ : collect n₂ (w.flatMap maskWord ++ maskWord t) = maskWord c) :
    normalForm r * generator g * (normalForm t)⁻¹ ∈ centralizerCandidate i := by
  have he := (wordValue_eq_of_collect n₁ _ _ h₁).trans
    (wordValue_eq_of_collect n₂ _ _ h₂).symm
  simp only [wordValue_append, wordValue_maskWord, wordValue_cons, wordValue_nil, mul_one] at he
  rw [he, mul_inv_cancel_right]
  exact masks_mem i w (List.forall_iff_forall_mem.mp hm)

theorem commute_of_collect (a b c : Fin (2 ^ 21)) (n₁ n₂ : ℕ)
    (h₁ : collect n₁ (maskWord a ++ maskWord b) = maskWord c)
    (h₂ : collect n₂ (maskWord b ++ maskWord a) = maskWord c) :
    Commute (normalForm a) (normalForm b) :=
  (normalForm_mul_of_collect a b c n₁ h₁).trans
    (normalForm_mul_of_collect b a c n₂ h₂).symm

theorem not_centralizes_of_collect (hcard : Nat.card Carrier = 2 ^ 21)
    (i : Fin 3) (r : Fin (2 ^ 21)) (k : Fin 3)
    (a b : Fin (2 ^ 21)) (n₁ n₂ : ℕ) (hne : a ≠ b)
    (h₁ : collect n₁ (maskWord r ++ maskWord (familyMask i k)) = maskWord a)
    (h₂ : collect n₂ (maskWord (familyMask i k) ++ maskWord r) = maskWord b) :
    normalForm r ∉ Subgroup.centralizer (family i : Set Carrier) := by
  intro h
  have hc := Subgroup.mem_centralizer_iff.mp h (familyGenerator i k)
    (Subgroup.subset_closure (Set.mem_range_self k))
  rw [← normalForm_familyMask i k] at hc
  exact hne ((normalForm_bijective_of_card hcard).injective
    ((normalForm_mul_of_collect r (familyMask i k) a n₁ h₁).symm.trans
      (hc.symm.trans (normalForm_mul_of_collect (familyMask i k) r b n₂ h₂))))

theorem candidate_le_of_commute (i : Fin 3)
    (hc : ∀ a : Fin 18, ∀ k : Fin 3,
      Commute (normalForm ((centralizerMasks i).getD a 0)) (familyGenerator i k)) :
    centralizerCandidate i ≤ Subgroup.centralizer (family i : Set Carrier) := by
  apply (Subgroup.closure_le _).mpr
  intro x hx
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
  obtain ⟨a, ha⟩ := List.mem_iff_get.mp hm
  have hlen : (centralizerMasks i).length = 18 := by fin_cases i <;> rfl
  let a' : Fin 18 := ⟨a.val, by simpa only [hlen] using a.isLt⟩
  have hm' : (centralizerMasks i).getD a' 0 = m :=
    (List.getD_eq_get _ _ a).trans ha
  rw [family, Subgroup.centralizer_closure]
  apply Subgroup.mem_centralizer_iff.mpr
  rintro y ⟨k, rfl⟩
  rw [← hm']
  exact (hc a' k).eq.symm

end Janko4.LocalStructure.SylowNormalEights.Presentation.Profiles.FullCentralizers
