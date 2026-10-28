module

public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check0000
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check0128
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check0256
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check0384
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check0512
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check0640
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check0768
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check0896
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check1024
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check1152
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check1280
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check1408
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check1536
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check1664
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check1792
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check1920
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check2048
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check2176
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check2304
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check2432
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check2560
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check2688
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check2816
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check2944
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check3072
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check3200
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check3328
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check3456
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check3584
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check3712
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check3840
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check3968
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check4096
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check4224
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check4352
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check4480
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.DoubleCosetCover.Check4608

/-!
# Assembling the double-coset kernel checks

The bounded slices traverse all 4717 immutable words. Each word has witnesses
for every one of the five first-parabolic rotations. Out-of-range indices
also have witnesses, because the default empty word occurs in the table.

Source: Parrott (1972), section 5, p.683; see `Rows` for the candidate data.
-/

namespace Tits.ConverseLocalCoverage.DoubleCosetCertificate
open Theory.GroupTheory.CosetEnumeration

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
private theorem checked : List.Forall₂ (fun w row => testRow w row = true)
    R1Certificate.input.reps.toList rows := by
  exact (List.rel_append (List.rel_append (List.rel_append (List.rel_append (List.rel_append check0000 check0128) (List.rel_append check0256 check0384)) (List.rel_append (List.rel_append check0512 check0640) (List.rel_append check0768 (List.rel_append check0896 check1024)))) (List.rel_append (List.rel_append (List.rel_append check1152 check1280) (List.rel_append check1408 check1536)) (List.rel_append (List.rel_append check1664 check1792) (List.rel_append check1920 (List.rel_append check2048 check2176))))) (List.rel_append (List.rel_append (List.rel_append (List.rel_append check2304 check2432) (List.rel_append check2560 check2688)) (List.rel_append (List.rel_append check2816 check2944) (List.rel_append check3072 (List.rel_append check3200 check3328)))) (List.rel_append (List.rel_append (List.rel_append check3456 check3584) (List.rel_append check3712 (List.rel_append check3840 check3968))) (List.rel_append (List.rel_append check4096 check4224) (List.rel_append check4352 (List.rel_append check4480 check4608))))))

private theorem row_of_mem {words : List (Word ParrottGenerator)} {rs : List Nat}
    (h : List.Forall₂ (fun w row => testRow w row = true) words rs)
    (w : Word ParrottGenerator) (hw : w ∈ words) :
    ∃ row, testRow w row = true := by
  induction h with
  | nil => simp at hw
  | @cons a b l₁ l₂ hab hl ih =>
    rcases List.mem_cons.mp hw with rfl | hw
    · exact ⟨b, hab⟩
    · exact ih hw

/-- Every stored word and rotation exponent has a kernel-checked factorization. -/
public theorem representative_test (i : Nat) (j : Fin 5) :
    ∃ c, test (R1Certificate.input.reps.getD i []) j c = true := by
  have hw : R1Certificate.input.reps.getD i [] ∈ R1Certificate.input.reps.toList := by
    by_cases hi : i < R1Certificate.input.reps.size
    · rw [← Array.getElem_eq_getD (h := hi) []]
      exact Array.getElem_mem_toList hi
    · simp only [Array.getD, hi, ↓reduceDIte]
      change [] ∈ [] :: _
      exact List.mem_cons_self
  obtain ⟨row, hr⟩ := row_of_mem checked _ hw
  exact ⟨rowWitness row j, List.all_eq_true.mp hr j (List.mem_finRange j)⟩

end Tits.ConverseLocalCoverage.DoubleCosetCertificate

