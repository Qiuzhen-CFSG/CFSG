module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ActionClassification.S3Normalization.BinaryMatrices

/-!
# A basis certificate for the cubic operator

For a nonidentity operator of order three with a nonzero fixed vector, choose
independent fixed vectors `f, g`, and a nonzero moving vector `a = u + T u`.
Put `b = T a`. The columns `a + f, b + f, a + b + f, g` form a basis in which
`T` cycles the first three coordinates. The finite certificate below verifies
both invertibility and the intertwining equation for every binary matrix
satisfying the stated hypotheses. All computations are checked by the kernel;
no basis-existence or representation-classification assumption is used.

This elementary coordinate argument supports the independent action reduction
for Huppert–Blackburn, *Finite Groups III*, XII.1.18(b), p.314.
-/

namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification.S3Normalization
open BinaryMatrices

private def findCode (p : Code → Bool) : Code := ((List.finRange 16).find? p).getD 0
public def cyclicBasis (m : Mat) : Mat :=
  let f := findCode (fun v => decide (v ≠ 0 ∧ app m v = v))
  let g := findCode (fun v => decide (v ≠ 0 ∧ v ≠ f ∧ app m v = v))
  let u := findCode (fun v => decide (v ≠ app m v))
  let a := u ^^^ app m u
  let b := app m a
  (a ^^^ f, b ^^^ f, a ^^^ b ^^^ f, g)

-- Separate declaration checks bound the kernel's evaluation cache.
private def CubicCase (a : Code) : Prop := ∀ b c d : Code,
    let m : Mat := (a,b,c,d)
    comp m (comp m m) = ident → m ≠ ident →
    (∃ v : Code, v ≠ 0 ∧ app m v = v) →
    trivialKernel (cyclicBasis m) ∧
      comp m (cyclicBasis m) = comp (cyclicBasis m) cubic

private instance (a : Code) : Decidable (CubicCase a) :=
  inferInstanceAs (Decidable (∀ _ _ _ : Code, _))

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem cubic_case_0 : CubicCase 0 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem cubic_case_1 : CubicCase 1 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem cubic_case_2 : CubicCase 2 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem cubic_case_3 : CubicCase 3 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem cubic_case_4 : CubicCase 4 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem cubic_case_5 : CubicCase 5 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem cubic_case_6 : CubicCase 6 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem cubic_case_7 : CubicCase 7 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem cubic_case_8 : CubicCase 8 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem cubic_case_9 : CubicCase 9 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem cubic_case_10 : CubicCase 10 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem cubic_case_11 : CubicCase 11 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem cubic_case_12 : CubicCase 12 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem cubic_case_13 : CubicCase 13 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem cubic_case_14 : CubicCase 14 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem cubic_case_15 : CubicCase 15 := by decide +kernel

public theorem cubic_certificate : ∀ a b c d : Code,
    let m : Mat := (a,b,c,d)
    comp m (comp m m) = ident → m ≠ ident →
    (∃ v : Code, v ≠ 0 ∧ app m v = v) →
    trivialKernel (cyclicBasis m) ∧
      comp m (cyclicBasis m) = comp (cyclicBasis m) cubic := by
  intro a
  have h : CubicCase a := by
    fin_cases a
    · exact cubic_case_0
    · exact cubic_case_1
    · exact cubic_case_2
    · exact cubic_case_3
    · exact cubic_case_4
    · exact cubic_case_5
    · exact cubic_case_6
    · exact cubic_case_7
    · exact cubic_case_8
    · exact cubic_case_9
    · exact cubic_case_10
    · exact cubic_case_11
    · exact cubic_case_12
    · exact cubic_case_13
    · exact cubic_case_14
    · exact cubic_case_15
  exact h

end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ActionClassification.S3Normalization
