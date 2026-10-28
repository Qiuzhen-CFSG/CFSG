module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.Seeds

/-!
# Trivial centralizer of the two fixed degree-24 lifts

In each 12-point orbit, two short words have just one common fixed point.
Every point is the image of one of these two base points under a checked word.
A permutation commuting with the two lifts therefore fixes all 24 points.
All finite assertions below are checked by the kernel; no enumeration of the
full symmetric group or external group identification is used.
Source coordinates: ATLAS M12d2G1-p24B0, as recorded in `Extension.Seeds`.
-/

public section
namespace Sporadic.Mathieu.M12ExceptionalExtension
set_option maxRecDepth 100000
set_option maxHeartbeats 30000

private theorem commute_evaluate {G : Type*} [Group G] {g a b : G}
    (ha : Commute g a) (hb : Commute g b) (w : List Bool) :
    Commute g (evaluate a b w) := by
  induction w with
  | nil => exact Commute.one_right g
  | cons c w ih => exact (by cases c <;> assumption : Commute g (if c then b else a)).mul_right ih

private theorem commute_fixes {X : Type*} (g w : Equiv.Perm X)
    (hc : Commute g w) (x : X) (hx : w x = x) : w (g x) = g x := by
  have h := congrArg (fun p : Equiv.Perm X => p x) hc.eq
  simpa only [Equiv.Perm.mul_apply, hx] using h.symm

private def fixedWord4_0 := evaluate innerAPerm innerBPerm [true, false, true]
private def fixedWord4_1 := evaluate innerAPerm innerBPerm [true, false, true, false, true, false, true, true, false]

private theorem unique_fixed_4 : ∀ i : Fin 24,
    fixedWord4_0 i = i → fixedWord4_1 i = i → i = 4 := by decide +kernel

private theorem fixes_4 (g : Equiv.Perm (Fin 24))
    (ha : Commute g innerAPerm) (hb : Commute g innerBPerm) : g 4 = 4 := by
  apply unique_fixed_4
  · exact commute_fixes g fixedWord4_0 (commute_evaluate ha hb _) 4 (by decide +kernel)
  · exact commute_fixes g fixedWord4_1 (commute_evaluate ha hb _) 4 (by decide +kernel)

private def fixedWord1_0 := evaluate innerAPerm innerBPerm [true, false]
private def fixedWord1_1 := evaluate innerAPerm innerBPerm [false, true, false, true, true, false, true, false, true]

private theorem unique_fixed_1 : ∀ i : Fin 24,
    fixedWord1_0 i = i → fixedWord1_1 i = i → i = 1 := by decide +kernel

private theorem fixes_1 (g : Equiv.Perm (Fin 24))
    (ha : Commute g innerAPerm) (hb : Commute g innerBPerm) : g 1 = 1 := by
  apply unique_fixed_1
  · exact commute_fixes g fixedWord1_0 (commute_evaluate ha hb _) 1 (by decide +kernel)
  · exact commute_fixes g fixedWord1_1 (commute_evaluate ha hb _) 1 (by decide +kernel)

private def orbitWord : Fin 24 → List Bool := ![[true, true, false, true, false],
  [],
  [true],
  [false],
  [],
  [true],
  [false, true, false, true, false],
  [true, false, true],
  [true, true, false, true, true, false, true],
  [true, true, false, true, true, false, true, true, false, true],
  [true, false, true, false, true, false],
  [true, false, true, false],
  [false, true],
  [false, true, true, false, true],
  [true, false, true, true, false, true, true, false, true],
  [false, true, false],
  [true, true, false, true, false, true, false],
  [true, false],
  [true, false, true, true, false, true],
  [true, true, false, true],
  [false],
  [true, true, false],
  [false, true, true, false, true, true, false, true],
  [false, true]]

private def orbitBase : Fin 24 → Fin 24 := ![4,1,1,1,4,4,4,1,1,1,4,4,4,1,1,4,4,4,1,1,4,4,1,1]

private theorem orbit_word_check : ∀ i : Fin 24,
    evaluate innerAPerm innerBPerm (orbitWord i) (orbitBase i) = i := by decide +kernel

/-- The two literal lifts have trivial centralizer in the whole symmetric group. -/
theorem centralizer_lifts_trivial (g : Equiv.Perm (Fin 24))
    (ha : Commute g innerAPerm) (hb : Commute g innerBPerm) : g = 1 := by
  have h4 := fixes_4 g ha hb
  have h1 := fixes_1 g ha hb
  have hbase (i : Fin 24) : g (orbitBase i) = orbitBase i := by
    have h : ∀ i : Fin 24, orbitBase i = 4 ∨ orbitBase i = 1 := by decide +kernel
    rcases h i with hi | hi
    · rw [hi, h4]
    · rw [hi, h1]
  apply Equiv.ext
  intro i
  have h := congrArg (fun p : Equiv.Perm (Fin 24) => p (orbitBase i))
    (commute_evaluate ha hb (orbitWord i)).eq
  simp only [Equiv.Perm.mul_apply] at h
  rw [hbase, orbit_word_check] at h
  exact h

end Sporadic.Mathieu.M12ExceptionalExtension
