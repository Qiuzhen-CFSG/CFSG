module

public import Theory.SpecificGroups.Tits.ThreeSylowContainment.Check0000
public import Theory.SpecificGroups.Tits.ThreeSylowContainment.Check0256
public import Theory.SpecificGroups.Tits.ThreeSylowContainment.Check0512
public import Theory.SpecificGroups.Tits.ThreeSylowContainment.Check0768
public import Theory.SpecificGroups.Tits.ThreeSylowContainment.Check1024
public import Theory.SpecificGroups.Tits.ThreeSylowContainment.Check1280
public import Theory.SpecificGroups.Tits.ThreeSylowContainment.Check1536
public import Theory.SpecificGroups.Tits.ThreeSylowContainment.Check1792
public import Theory.SpecificGroups.Tits.ThreeSylowContainment.Check2048
public import Theory.SpecificGroups.Tits.ThreeSylowContainment.Check2304
public import Theory.SpecificGroups.Tits.ThreeSylowContainment.Check2560
public import Theory.SpecificGroups.Tits.ThreeSylowContainment.Check2816
public import Theory.SpecificGroups.Tits.ThreeSylowContainment.Check3072
public import Theory.SpecificGroups.Tits.ThreeSylowContainment.Check3328
public import Theory.SpecificGroups.Tits.ThreeSylowContainment.Check3584
public import Theory.SpecificGroups.Tits.ThreeSylowContainment.Check3840
public import Theory.SpecificGroups.Tits.ThreeSylowContainment.Check4096
public import Theory.SpecificGroups.Tits.ThreeSylowContainment.Check4352
public import Theory.SpecificGroups.Tits.ThreeSylowContainment.Check4608

/-!
# Kernel verification of the Sylow-overgroup point witnesses

The simultaneous traversal checks all 4717 stored representative words against
their witness rows, and all five rotation exponents in each row. The resulting
existence theorem also treats out-of-range indices, whose default word is empty.

Source: the original Parrott coset words and point maps cited in `Data`.
-/

namespace Tits.ThreeSylowContainment.Certificate
open Theory.GroupTheory.CosetEnumeration

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
private theorem checked : List.Forall₂ (fun w row => testRow w row = true)
    R1Certificate.input.reps.toList rows := by
  exact List.rel_append
    (List.rel_append
      (List.rel_append (List.rel_append check0000 check0256)
        (List.rel_append check0512 check0768))
      (List.rel_append (List.rel_append check1024 check1280)
        (List.rel_append check1536 (List.rel_append check1792 check2048))))
    (List.rel_append
      (List.rel_append (List.rel_append check2304 check2560)
        (List.rel_append check2816 (List.rel_append check3072 check3328)))
      (List.rel_append (List.rel_append check3584 check3840)
        (List.rel_append check4096 (List.rel_append check4352 check4608))))

private theorem row_of_mem {words : List (Word ParrottGenerator)}
    {rs : List (Fin 5 → ℕ)}
    (h : List.Forall₂ (fun w row => testRow w row = true) words rs)
    (w : Word ParrottGenerator) (hw : w ∈ words) :
    ∃ row, testRow w row = true := by
  induction h with
  | nil => simp at hw
  | @cons a b l₁ l₂ hab hl ih =>
    rcases List.mem_cons.mp hw with rfl | hw
    · exact ⟨b, hab⟩
    · exact ih hw

/-- Every stored word, paired with any rotation exponent, has a checked witness. -/
public theorem representative_test (i : ℕ) (j : Fin 5) :
    ∃ c, test (R1Certificate.input.reps.getD i []) j c = true := by
  have hw : R1Certificate.input.reps.getD i [] ∈ R1Certificate.input.reps.toList := by
    by_cases hi : i < R1Certificate.input.reps.size
    · rw [← Array.getElem_eq_getD (h := hi) []]
      exact Array.getElem_mem_toList hi
    · simp only [Array.getD, hi, ↓reduceDIte]
      change [] ∈ [] :: _
      exact List.mem_cons_self
  obtain ⟨row, hr⟩ := row_of_mem checked _ hw
  exact ⟨row j, List.all_eq_true.mp hr j (List.mem_finRange j)⟩

end Tits.ThreeSylowContainment.Certificate
