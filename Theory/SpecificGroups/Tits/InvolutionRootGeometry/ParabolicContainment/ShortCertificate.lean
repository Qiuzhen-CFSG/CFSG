module

public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.ParabolicContainment.ShortChecks

/-!
# Assemble the short-root coset tests

The bounded kernel checks cover every stored word. This module assembles
those slices and interprets their direct point tests as equations for the
original marked permutations, including the empty out-of-range word.
Source: Parrott (1972), §5, p.683; see `ShortTest` and `ShortChecks`.
-/

namespace Tits.InvolutionRootGeometry.ParabolicContainment.Certificate

private theorem checked_step {α : Type*} (f : α → Bool) (l : List α) (n : ℕ)
    (hhead : (l.drop n |>.take 256).all f = true)
    (htail : (l.drop (n + 256)).all f = true) : (l.drop n).all f = true := by
  have hs := List.all_append (f := f) (xs := (l.drop n).take 256)
    (ys := (l.drop n).drop 256)
  rw [List.take_append_drop, List.drop_drop] at hs
  rw [hs, hhead]
  simpa only [Bool.true_and, Nat.add_comm] using htail

set_option maxRecDepth 30000 in
private theorem empty_tail : Tits.R1Certificate.input.reps.toList.drop 4864 = [] := by
  rfl

private theorem checked : Tits.R1Certificate.input.reps.toList.all pointTest = true := by
  have htail : (Tits.R1Certificate.input.reps.toList.drop 4864).all pointTest = true := by
    rw [empty_tail]
    rfl
  have h4608 := checked_step pointTest Tits.R1Certificate.input.reps.toList 4608 check4608 htail
  have h4352 := checked_step pointTest Tits.R1Certificate.input.reps.toList 4352 check4352 h4608
  have h4096 := checked_step pointTest Tits.R1Certificate.input.reps.toList 4096 check4096 h4352
  have h3840 := checked_step pointTest Tits.R1Certificate.input.reps.toList 3840 check3840 h4096
  have h3584 := checked_step pointTest Tits.R1Certificate.input.reps.toList 3584 check3584 h3840
  have h3328 := checked_step pointTest Tits.R1Certificate.input.reps.toList 3328 check3328 h3584
  have h3072 := checked_step pointTest Tits.R1Certificate.input.reps.toList 3072 check3072 h3328
  have h2816 := checked_step pointTest Tits.R1Certificate.input.reps.toList 2816 check2816 h3072
  have h2560 := checked_step pointTest Tits.R1Certificate.input.reps.toList 2560 check2560 h2816
  have h2304 := checked_step pointTest Tits.R1Certificate.input.reps.toList 2304 check2304 h2560
  have h2048 := checked_step pointTest Tits.R1Certificate.input.reps.toList 2048 check2048 h2304
  have h1792 := checked_step pointTest Tits.R1Certificate.input.reps.toList 1792 check1792 h2048
  have h1536 := checked_step pointTest Tits.R1Certificate.input.reps.toList 1536 check1536 h1792
  have h1280 := checked_step pointTest Tits.R1Certificate.input.reps.toList 1280 check1280 h1536
  have h1024 := checked_step pointTest Tits.R1Certificate.input.reps.toList 1024 check1024 h1280
  have h768 := checked_step pointTest Tits.R1Certificate.input.reps.toList 768 check0768 h1024
  have h512 := checked_step pointTest Tits.R1Certificate.input.reps.toList 512 check0512 h768
  have h256 := checked_step pointTest Tits.R1Certificate.input.reps.toList 256 check0256 h512
  have h0 := checked_step pointTest Tits.R1Certificate.input.reps.toList 0 check0000 h256
  exact h0

set_option maxRecDepth 30000 in
/-- Every actual representative passing a short-root conjugacy test uses only
second-parabolic generators, with zero first-parabolic rotation exponent. -/
public theorem representative_test (i : ℕ) (j : Fin 5) :
    (inSecond (R1Certificate.input.reps.getD i []) j ||
      (List.finRange 4).all (separates (R1Certificate.input.reps.getD i []) j)) = true := by
  have hw : R1Certificate.input.reps.getD i [] ∈ R1Certificate.input.reps.toList := by
    by_cases hi : i < R1Certificate.input.reps.size
    · rw [← Array.getElem_eq_getD (h := hi) []]
      exact Array.getElem_mem_toList hi
    · simp only [Array.getD, hi, ↓reduceDIte]
      change [] ∈ [] :: _
      exact List.mem_cons_self
  have h := List.all_eq_true.mp checked _ hw
  have hj := List.all_eq_true.mp h j (List.mem_finRange j)
  have he : pointSeparates (R1Certificate.input.reps.getD i []) j =
      separates (R1Certificate.input.reps.getD i []) j :=
    funext (pointSeparates_eq _ j)
  rw [he] at hj
  exact hj

end Tits.InvolutionRootGeometry.ParabolicContainment.Certificate
