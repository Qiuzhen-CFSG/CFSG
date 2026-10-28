module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.UpperBound.PositiveRewriting
public import Mathlib.Tactic.FinCases

/-!
# Child relations in the parent abstract presentations

Each proof substitutes the named child words and cancels adjacent involutions.
It then replaces a subword using a cyclic conjugate of a parent relator or its
reverse. The 30 traces in `source/lift_traces.json` each have at most nine steps.
All concrete checks reduce in Lean's kernel; permutation identities and recorded
orders supply no premises. See `../source/README.md` for the discovery source.
-/

public section
namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.UpperBoundChain
open Subgroup.CosetWordCertificate

theorem level0_involution (a : Fin 3) :
    (PresentedGroup.of a : Level0) * PresentedGroup.of a = 1 := by
  fin_cases a
  · have h : eval (PresentedGroup.of : Fin 3 → Level0) [( 0, true), (0, true)] = 1 :=
      level0_relator 1
    simpa [eval_cons] using h
  · have h : eval (PresentedGroup.of : Fin 3 → Level0) [( 1, true), (1, true)] = 1 :=
      level0_relator 2
    simpa [eval_cons] using h
  · have h : eval (PresentedGroup.of : Fin 3 → Level0) [( 2, true), (2, true)] = 1 :=
      level0_relator 0
    simpa [eval_cons] using h

theorem level1_involution (a : Fin 7) :
    (PresentedGroup.of a : Level1) * PresentedGroup.of a = 1 := by
  fin_cases a
  · have h : eval (PresentedGroup.of : Fin 7 → Level1) [( 0, true), (0, true)] = 1 :=
      level1_relator 1
    simpa [eval_cons] using h
  · have h : eval (PresentedGroup.of : Fin 7 → Level1) [( 1, true), (1, true)] = 1 :=
      level1_relator 6
    simpa [eval_cons] using h
  · have h : eval (PresentedGroup.of : Fin 7 → Level1) [( 2, true), (2, true)] = 1 :=
      level1_relator 2
    simpa [eval_cons] using h
  · have h : eval (PresentedGroup.of : Fin 7 → Level1) [( 3, true), (3, true)] = 1 :=
      level1_relator 3
    simpa [eval_cons] using h
  · have h : eval (PresentedGroup.of : Fin 7 → Level1) [( 4, true), (4, true)] = 1 :=
      level1_relator 0
    simpa [eval_cons] using h
  · have h : eval (PresentedGroup.of : Fin 7 → Level1) [( 5, true), (5, true)] = 1 :=
      level1_relator 4
    simpa [eval_cons] using h
  · have h : eval (PresentedGroup.of : Fin 7 → Level1) [( 6, true), (6, true)] = 1 :=
      level1_relator 5
    simpa [eval_cons] using h

private theorem relation0_0 :
    eval level0Generator (level1Relator 0) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 3 → Level0)
    (level0ChildWord i)) (level1Relator 0) = 1
  rw [← eval_substitute]
  have hs : substitute level0ChildWord (level1Relator 0) =
      positive [2, 0, 2, 0, 2, 2, 0, 2, 0, 2] := by decide
  rw [hs, ← eval_positive_reduce _ level0_involution]
  have hn : positiveReduce ([2, 0, 2, 0, 2, 2, 0, 2, 0, 2] : List (Fin 3)) = [] := by decide
  rw [hn]
  calc
    _ = 1 := eval_nil _

private theorem relation0_1 :
    eval level0Generator (level1Relator 1) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 3 → Level0)
    (level0ChildWord i)) (level1Relator 1) = 1
  rw [← eval_substitute]
  have hs : substitute level0ChildWord (level1Relator 1) =
      positive [0, 0] := by decide
  rw [hs, ← eval_positive_reduce _ level0_involution]
  have hn : positiveReduce ([0, 0] : List (Fin 3)) = [] := by decide
  rw [hn]
  calc
    _ = 1 := eval_nil _

private theorem relation0_2 :
    eval level0Generator (level1Relator 2) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 3 → Level0)
    (level0ChildWord i)) (level1Relator 2) = 1
  rw [← eval_substitute]
  have hs : substitute level0ChildWord (level1Relator 2) =
      positive [0, 2, 2, 0, 2, 2] := by decide
  rw [hs, ← eval_positive_reduce _ level0_involution]
  have hn : positiveReduce ([0, 2, 2, 0, 2, 2] : List (Fin 3)) = [] := by decide
  rw [hn]
  calc
    _ = 1 := eval_nil _

private theorem relation0_3 :
    eval level0Generator (level1Relator 3) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 3 → Level0)
    (level0ChildWord i)) (level1Relator 3) = 1
  rw [← eval_substitute]
  have hs : substitute level0ChildWord (level1Relator 3) =
      positive [0, 0] := by decide
  rw [hs, ← eval_positive_reduce _ level0_involution]
  have hn : positiveReduce ([0, 0] : List (Fin 3)) = [] := by decide
  rw [hn]
  calc
    _ = 1 := eval_nil _

private theorem relation0_4 :
    eval level0Generator (level1Relator 4) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 3 → Level0)
    (level0ChildWord i)) (level1Relator 4) = 1
  rw [← eval_substitute]
  have hs : substitute level0ChildWord (level1Relator 4) =
      positive [2, 1, 0, 1, 0, 1, 0, 2, 2, 1, 0, 1, 0, 1, 0, 2] := by decide
  rw [hs, ← eval_positive_reduce _ level0_involution]
  have hn : positiveReduce ([2, 1, 0, 1, 0, 1, 0, 2, 2, 1, 0, 1, 0, 1, 0, 2] : List (Fin 3)) = [2, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2] := by decide
  rw [hn]
  calc
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive []) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] [2] [1, 0, 1, 0, 1, 0] [0, 1, 0, 1, 0, 1] [1, 0, 1, 0, 1, 0, 2]
        [2, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2] [] true 11
        (level0_relator 4) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation0_5 :
    eval level0Generator (level1Relator 5) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 3 → Level0)
    (level0ChildWord i)) (level1Relator 5) = 1
  rw [← eval_substitute]
  have hs : substitute level0ChildWord (level1Relator 5) =
      positive [1, 1, 2, 0, 2, 0, 1, 2, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 1, 2, 0, 2, 0, 1, 2, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2] := by decide
  rw [hs, ← eval_positive_reduce _ level0_involution]
  have hn : positiveReduce ([1, 1, 2, 0, 2, 0, 1, 2, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 1, 2, 0, 2, 0, 1, 2, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2] : List (Fin 3)) = [2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2] := by decide
  rw [hn]
  calc
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive [0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2]) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [1, 0, 1, 2, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2, 1, 0] [] [2, 0, 2, 1, 0, 1, 0, 1, 2, 0] [0, 2, 1, 0, 1, 0, 1, 2, 0, 2] [2, 0, 1, 0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2]
        [2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2] [0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2] true 14
        (level0_relator 6) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive [0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2]) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [1, 0, 1, 2, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2, 1, 0] [0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1] [0, 2, 1, 0, 1, 0, 1, 2, 0, 2] [2, 0, 2, 1, 0, 1, 0, 1, 2, 0] [0, 1, 0, 1, 0, 1, 2]
        [0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2] [0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2] true 15
        (level0_relator 6) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive [0, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2, 1, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2]) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [1, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2] [0] [2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0] [1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2, 1] [2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2]
        [0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2] [0, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2, 1, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2] true 12
        (level0_relator 9) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive []) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [1, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2] [] [0, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2, 1] [2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2] [2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2]
        [0, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2, 1, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2] [] true 25
        (level0_relator 9) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation0_6 :
    eval level0Generator (level1Relator 6) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 3 → Level0)
    (level0ChildWord i)) (level1Relator 6) = 1
  rw [← eval_substitute]
  have hs : substitute level0ChildWord (level1Relator 6) =
      positive [1, 1] := by decide
  rw [hs, ← eval_positive_reduce _ level0_involution]
  have hn : positiveReduce ([1, 1] : List (Fin 3)) = [] := by decide
  rw [hn]
  calc
    _ = 1 := eval_nil _

private theorem relation0_7 :
    eval level0Generator (level1Relator 7) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 3 → Level0)
    (level0ChildWord i)) (level1Relator 7) = 1
  rw [← eval_substitute]
  have hs : substitute level0ChildWord (level1Relator 7) =
      positive [0, 0] := by decide
  rw [hs, ← eval_positive_reduce _ level0_involution]
  have hn : positiveReduce ([0, 0] : List (Fin 3)) = [] := by decide
  rw [hn]
  calc
    _ = 1 := eval_nil _

private theorem relation0_8 :
    eval level0Generator (level1Relator 8) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 3 → Level0)
    (level0ChildWord i)) (level1Relator 8) = 1
  rw [← eval_substitute]
  have hs : substitute level0ChildWord (level1Relator 8) =
      positive [0, 0, 2, 2] := by decide
  rw [hs, ← eval_positive_reduce _ level0_involution]
  have hn : positiveReduce ([0, 0, 2, 2] : List (Fin 3)) = [] := by decide
  rw [hn]
  calc
    _ = 1 := eval_nil _

private theorem relation0_9 :
    eval level0Generator (level1Relator 9) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 3 → Level0)
    (level0ChildWord i)) (level1Relator 9) = 1
  rw [← eval_substitute]
  have hs : substitute level0ChildWord (level1Relator 9) =
      positive [1, 1, 2, 0, 2, 0, 1, 2, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 2, 1, 0, 1, 0, 1, 0, 2, 1, 1, 2, 0, 2, 0, 1, 2, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 2, 1, 0, 1, 0, 1, 0, 2] := by decide
  rw [hs, ← eval_positive_reduce _ level0_involution]
  have hn : positiveReduce ([1, 1, 2, 0, 2, 0, 1, 2, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 2, 1, 0, 1, 0, 1, 0, 2, 1, 1, 2, 0, 2, 0, 1, 2, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 2, 1, 0, 1, 0, 1, 0, 2] : List (Fin 3)) = [2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0] := by decide
  rw [hn]
  calc
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive []) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [1, 0, 1, 2, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2, 1, 0] [] [2, 0, 2, 1, 0, 1, 0, 1, 2, 0] [0, 2, 1, 0, 1, 0, 1, 2, 0, 2] [2, 0, 2, 1, 0, 1, 0, 1, 2, 0]
        [2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0] [] true 14
        (level0_relator 6) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation0_10 :
    eval level0Generator (level1Relator 10) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 3 → Level0)
    (level0ChildWord i)) (level1Relator 10) = 1
  rw [← eval_substitute]
  have hs : substitute level0ChildWord (level1Relator 10) =
      positive [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] := by decide
  rw [hs, ← eval_positive_reduce _ level0_involution]
  have hn : positiveReduce ([0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] : List (Fin 3)) = [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] := by decide
  rw [hn]
  calc
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive []) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] [] [0, 2, 0, 2, 0, 2] [2, 0, 2, 0, 2, 0] [0, 2, 0, 2, 0, 2]
        [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] [] true 11
        (level0_relator 5) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation0_11 :
    eval level0Generator (level1Relator 11) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 3 → Level0)
    (level0ChildWord i)) (level1Relator 11) = 1
  rw [← eval_substitute]
  have hs : substitute level0ChildWord (level1Relator 11) =
      positive [1, 1, 2, 0, 2, 0, 1, 2, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 2, 0, 2, 0, 2, 1, 1, 2, 0, 2, 0, 1, 2, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 2, 0, 2, 0, 2] := by decide
  rw [hs, ← eval_positive_reduce _ level0_involution]
  have hn : positiveReduce ([1, 1, 2, 0, 2, 0, 1, 2, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 2, 0, 2, 0, 2, 1, 1, 2, 0, 2, 0, 1, 2, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 2, 0, 2, 0, 2] : List (Fin 3)) = [2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2] := by decide
  rw [hn]
  calc
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive [2, 0, 2, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2]) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] [2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2] [0, 1, 0, 1, 0, 1] [1, 0, 1, 0, 1, 0] [0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2]
        [2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2] [2, 0, 2, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2] true 10
        (level0_relator 4) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive []) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] [2, 0, 2] [1, 0, 1, 0, 1, 0] [0, 1, 0, 1, 0, 1] [1, 0, 1, 0, 1, 0, 2, 0, 2]
        [2, 0, 2, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2] [] true 11
        (level0_relator 4) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation0_12 :
    eval level0Generator (level1Relator 12) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 3 → Level0)
    (level0ChildWord i)) (level1Relator 12) = 1
  rw [← eval_substitute]
  have hs : substitute level0ChildWord (level1Relator 12) =
      positive [2, 1, 0, 1, 0, 1, 0, 2, 0, 2, 1, 0, 1, 0, 1, 0, 2, 1, 1, 2, 0, 2, 0, 1, 2, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 2, 0, 2, 0, 2] := by decide
  rw [hs, ← eval_positive_reduce _ level0_involution]
  have hn : positiveReduce ([2, 1, 0, 1, 0, 1, 0, 2, 0, 2, 1, 0, 1, 0, 1, 0, 2, 1, 1, 2, 0, 2, 0, 1, 2, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 2, 0, 2, 0, 2] : List (Fin 3)) = [2, 1, 0, 1, 0, 1, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2] := by decide
  rw [hn]
  calc
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive [2, 1, 0, 1, 0, 1, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2]) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] [2, 1, 0, 1, 0, 1, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2] [0, 1, 0, 1, 0, 1] [1, 0, 1, 0, 1, 0] [0, 2, 0, 2]
        [2, 1, 0, 1, 0, 1, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2] [2, 1, 0, 1, 0, 1, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2] true 10
        (level0_relator 4) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive [2, 1, 0, 1, 0, 1, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 1, 2, 0]) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [1, 0, 1, 2, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2, 1, 0] [2, 1, 0, 1, 0, 1, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1] [2, 0, 2, 1, 0, 1, 0, 1, 2, 0] [0, 2, 1, 0, 1, 0, 1, 2, 0, 2] [2]
        [2, 1, 0, 1, 0, 1, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2] [2, 1, 0, 1, 0, 1, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 1, 2, 0] true 14
        (level0_relator 6) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive [2, 1, 0, 1, 0, 1, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0]) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] [2, 1, 0, 1, 0, 1, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2] [1, 0, 1, 0, 1, 0] [0, 1, 0, 1, 0, 1] [2, 1, 0, 1, 0, 1, 2, 0]
        [2, 1, 0, 1, 0, 1, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 1, 2, 0] [2, 1, 0, 1, 0, 1, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0] true 11
        (level0_relator 4) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive [2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0]) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [1, 0, 1, 2, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2, 1, 0] [2, 1, 0, 1, 0, 1] [0, 2, 0, 2, 1, 0, 1, 0, 1, 2] [2, 1, 0, 1, 0, 1, 2, 0, 2, 0] [0, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0]
        [2, 1, 0, 1, 0, 1, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0] [2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0] true 13
        (level0_relator 6) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive [1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2, 1, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0]) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [1, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2] [] [2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0] [1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2, 1] [2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0]
        [2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0] [1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2, 1, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0] true 12
        (level0_relator 9) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive []) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [1, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2] [] [1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2, 1, 2] [0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1] [1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0]
        [1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2, 1, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0] [] true 26
        (level0_relator 9) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation0_13 :
    eval level0Generator (level1Relator 13) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 3 → Level0)
    (level0ChildWord i)) (level1Relator 13) = 1
  rw [← eval_substitute]
  have hs : substitute level0ChildWord (level1Relator 13) =
      positive [1, 1, 1, 2, 0, 2, 0, 1, 2, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2] := by decide
  rw [hs, ← eval_positive_reduce _ level0_involution]
  have hn : positiveReduce ([1, 1, 1, 2, 0, 2, 0, 1, 2, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2] : List (Fin 3)) = [1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2] := by decide
  rw [hn]
  calc
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive [1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1]) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [1, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2] [1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0] [1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 1, 2] [2, 1, 0, 1, 0, 1, 2, 0, 1, 2, 0, 2, 0] [0, 2, 0, 2]
        [1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2] [1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1] false 9
        (level0_relator 9) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive []) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [1, 0, 1, 2, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2, 1, 0] [1] [2, 0, 2, 1, 0, 1, 0, 1, 2, 0] [0, 2, 1, 0, 1, 0, 1, 2, 0, 2] [2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1]
        [1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1] [] true 14
        (level0_relator 6) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation0_14 :
    eval level0Generator (level1Relator 14) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 3 → Level0)
    (level0ChildWord i)) (level1Relator 14) = 1
  rw [← eval_substitute]
  have hs : substitute level0ChildWord (level1Relator 14) =
      positive [1, 0, 1, 1, 2, 0, 2, 0, 1, 2, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 0, 1, 0, 1, 1, 2, 0, 2, 0, 1, 2, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 0] := by decide
  rw [hs, ← eval_positive_reduce _ level0_involution]
  have hn : positiveReduce ([1, 0, 1, 1, 2, 0, 2, 0, 1, 2, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 0, 1, 0, 1, 1, 2, 0, 2, 0, 1, 2, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 0] : List (Fin 3)) = [1, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 0] := by decide
  rw [hn]
  calc
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive [1, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 0]) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [1, 0, 1, 2, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2, 1, 0] [1, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 0, 1] [0, 2, 0, 2, 1, 0, 1, 0, 1, 2] [2, 1, 0, 1, 0, 1, 2, 0, 2, 0] [0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 0]
        [1, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 0] [1, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 0] true 13
        (level0_relator 6) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive [1, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 0, 1, 0, 1, 2, 0, 2, 0, 2, 1, 0]) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [1, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2] [1, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 0, 1] [2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1] [0, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2] [2, 0, 2, 0, 2, 0]
        [1, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 0] [1, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 0, 1, 0, 1, 2, 0, 2, 0, 2, 1, 0] false 2
        (level0_relator 9) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive [1, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 0, 1, 0, 1, 2, 0, 2, 0, 2, 1, 0]) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [1, 0, 1, 2, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2, 1, 0] [1] [0, 2, 0, 2, 1, 0, 1, 0, 1, 2] [2, 1, 0, 1, 0, 1, 2, 0, 2, 0] [0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 0, 1, 0, 1, 2, 0, 2, 0, 2, 1, 0]
        [1, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 0, 1, 0, 1, 2, 0, 2, 0, 2, 1, 0] [1, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 0, 1, 0, 1, 2, 0, 2, 0, 2, 1, 0] true 13
        (level0_relator 6) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive [1, 0, 1, 2, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2, 1, 0]) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [1, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2] [1] [2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1] [0, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2] [2, 0, 2, 0, 2, 0, 1, 0, 1, 2, 0, 2, 0, 2, 1, 0]
        [1, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 0, 1, 0, 1, 2, 0, 2, 0, 2, 1, 0] [1, 0, 1, 2, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2, 1, 0] false 2
        (level0_relator 9) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive []) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [1, 0, 1, 2, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2, 1, 0] [] [1, 0, 1, 2, 0, 2, 0, 2, 1, 0] [0, 1, 2, 0, 2, 0, 2, 1, 0, 1] [1, 0, 1, 2, 0, 2, 0, 2, 1, 0]
        [1, 0, 1, 2, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2, 1, 0] [] true 19
        (level0_relator 6) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation0_15 :
    eval level0Generator (level1Relator 15) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 3 → Level0)
    (level0ChildWord i)) (level1Relator 15) = 1
  rw [← eval_substitute]
  have hs : substitute level0ChildWord (level1Relator 15) =
      positive [1, 1, 2, 0, 2, 0, 1, 2, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 1, 1, 2, 0, 2, 0, 1, 2, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 2, 1, 0, 1, 0, 1, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 2, 0, 2, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1] := by decide
  rw [hs, ← eval_positive_reduce _ level0_involution]
  have hn : positiveReduce ([1, 1, 2, 0, 2, 0, 1, 2, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 1, 1, 2, 0, 2, 0, 1, 2, 0, 0, 0, 0, 2, 1, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 2, 1, 0, 1, 0, 1, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 2, 0, 2, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1] : List (Fin 3)) = [2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1] := by decide
  rw [hn]
  calc
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive [0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1]) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [1, 0, 1, 2, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2, 1, 0] [] [2, 0, 2, 1, 0, 1, 0, 1, 2, 0] [0, 2, 1, 0, 1, 0, 1, 2, 0, 2] [2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1]
        [2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1] [0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1] true 14
        (level0_relator 6) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive [1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1]) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [1, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2] [] [0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2] [1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2, 1] [1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1]
        [0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1] [1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1] false 1
        (level0_relator 9) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive [1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1]) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] [1, 2, 0, 2, 0, 2, 1, 2, 0, 2] [0, 1, 0, 1, 0, 1] [1, 0, 1, 0, 1, 0] [0, 2, 1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1]
        [1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1] [1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1] true 10
        (level0_relator 4) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive [1, 2, 0, 2, 0, 2, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 2, 0, 2, 1, 2, 1, 2, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1]) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [0, 2, 0, 2, 1, 0, 2, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 1, 0, 1, 0, 2, 1, 2] [1, 2, 0, 2, 0, 2, 1, 2, 0] [2, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 1, 0, 1] [1, 0, 2, 0, 1, 2, 0, 2, 0, 2, 1, 2, 0] [0, 1, 2, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1]
        [1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1] [1, 2, 0, 2, 0, 2, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 2, 0, 2, 1, 2, 1, 2, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1] false 9
        (level0_relator 8) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive [1, 2, 0, 2, 0, 2, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 2, 0, 2, 1, 2, 1, 2, 0, 1, 2, 1, 2, 1, 2, 0, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 0, 1]) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [0, 2, 0, 2, 1, 0, 2, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 1, 0, 1, 0, 2, 1, 2] [1, 2, 0, 2, 0, 2, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 2, 0, 2, 1, 2, 1, 2, 0, 1, 2, 1] [0, 1, 0, 1, 2, 0, 2, 1, 2, 1, 0, 1, 0, 1] [2, 1, 2, 0, 2, 0, 2, 1, 0, 2, 0, 1, 2] [0, 2, 0, 1]
        [1, 2, 0, 2, 0, 2, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 2, 0, 2, 1, 2, 1, 2, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1] [1, 2, 0, 2, 0, 2, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 2, 0, 2, 1, 2, 1, 2, 0, 1, 2, 1, 2, 1, 2, 0, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 0, 1] true 3
        (level0_relator 8) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive [1, 2, 0, 2, 0, 2, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 2, 0, 2, 1, 2, 1, 2, 0, 2, 1, 2, 1, 0, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 0, 1]) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [2, 1, 2, 1, 2, 1, 2, 1, 2, 1] [1, 2, 0, 2, 0, 2, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 2, 0, 2, 1, 2, 1, 2, 0] [1, 2, 1, 2, 1] [2, 1, 2, 1, 2] [2, 0, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 0, 1]
        [1, 2, 0, 2, 0, 2, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 2, 0, 2, 1, 2, 1, 2, 0, 1, 2, 1, 2, 1, 2, 0, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 0, 1] [1, 2, 0, 2, 0, 2, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 2, 0, 2, 1, 2, 1, 2, 0, 2, 1, 2, 1, 0, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 0, 1] true 8
        (level0_relator 3) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive [1, 2, 0, 2, 0, 2, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 2, 0, 1, 2, 1, 2, 1, 0, 2, 1, 2, 1, 0, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 0, 1]) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [2, 1, 2, 1, 2, 1, 2, 1, 2, 1] [1, 2, 0, 2, 0, 2, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 2, 0] [2, 1, 2, 1, 2] [1, 2, 1, 2, 1] [0, 2, 1, 2, 1, 0, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 0, 1]
        [1, 2, 0, 2, 0, 2, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 2, 0, 2, 1, 2, 1, 2, 0, 2, 1, 2, 1, 0, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 0, 1] [1, 2, 0, 2, 0, 2, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 2, 0, 1, 2, 1, 2, 1, 0, 2, 1, 2, 1, 0, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 0, 1] true 9
        (level0_relator 3) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive [1, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1]) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [2, 1, 0, 2, 1, 2, 1, 0, 2, 0, 2, 1, 0, 2, 0, 1, 0, 2, 0, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 2, 0, 1, 2, 1] [1, 2, 0, 2, 0, 2] [1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 2, 0, 1, 2, 1, 2, 1] [0, 2, 0, 1, 0, 2, 0, 1, 2, 0, 2, 0, 1, 2, 1, 2, 0] [0, 2, 1, 2, 1, 0, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 0, 1]
        [1, 2, 0, 2, 0, 2, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 2, 0, 1, 2, 1, 2, 1, 0, 2, 1, 2, 1, 0, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 0, 1] [1, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1] false 19
        (level0_relator 10) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive []) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2] [1] [2, 0, 2, 0, 2, 0] [0, 2, 0, 2, 0, 2] [2, 0, 2, 0, 2, 0, 1]
        [1, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1] [] true 10
        (level0_relator 5) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation0_16 :
    eval level0Generator (level1Relator 16) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 3 → Level0)
    (level0ChildWord i)) (level1Relator 16) = 1
  rw [← eval_substitute]
  have hs : substitute level0ChildWord (level1Relator 16) =
      positive [1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2, 2, 1, 0, 1, 0, 1, 0, 2, 2, 0, 2, 0, 2] := by decide
  rw [hs, ← eval_positive_reduce _ level0_involution]
  have hn : positiveReduce ([1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2, 2, 1, 0, 1, 0, 1, 0, 2, 2, 0, 2, 0, 2] : List (Fin 3)) = [1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2] := by decide
  rw [hn]
  calc
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive [1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2]) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [1, 0, 1, 2, 0, 2, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2, 1, 0] [1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1] [0, 2, 1, 0, 1, 0, 1, 2, 0, 2] [2, 0, 2, 1, 0, 1, 0, 1, 2, 0] [0, 1, 0, 1, 0, 1, 2, 0, 2]
        [1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2] [1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2] true 15
        (level0_relator 6) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive [1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2, 1, 2]) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [1, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2] [1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0] [2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0] [1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2, 1] [2]
        [1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 2] [1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2, 1, 2] true 12
        (level0_relator 9) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive []) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [1, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2] [] [1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 1] [2, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2] [2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2, 1, 2]
        [1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 0, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2, 1, 2] [] true 13
        (level0_relator 9) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation0_17 :
    eval level0Generator (level1Relator 17) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 3 → Level0)
    (level0ChildWord i)) (level1Relator 17) = 1
  rw [← eval_substitute]
  have hs : substitute level0ChildWord (level1Relator 17) =
      positive [1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 2, 0, 2, 0, 2, 2, 1, 0, 1, 0, 1, 0, 2, 2, 0, 2, 0, 2] := by decide
  rw [hs, ← eval_positive_reduce _ level0_involution]
  have hn : positiveReduce ([1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 2, 0, 2, 0, 2, 2, 1, 0, 1, 0, 1, 0, 2, 2, 0, 2, 0, 2] : List (Fin 3)) = [1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2] := by decide
  rw [hn]
  calc
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive [1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2]) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 2, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2] [1, 0, 2, 1, 0, 1, 0, 1] [0, 2, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 2, 1, 0, 1] [2, 0, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 2, 0, 1, 0] [0, 1, 0, 2, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2]
        [1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2] [1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2] true 10
        (level0_relator 11) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive [1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2]) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] [1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 2] [0, 1, 0, 1, 0, 1] [1, 0, 1, 0, 1, 0] [0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2]
        [1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2] [1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2] true 10
        (level0_relator 4) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive [1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 2]) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] [1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 2, 1, 0, 1, 0, 1, 2] [0, 1, 0, 1, 0, 1] [1, 0, 1, 0, 1, 0] [2, 0, 2]
        [1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2] [1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 2] true 10
        (level0_relator 4) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive [1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 0, 1, 0, 1, 0, 2, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2]) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [1, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2] [1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 0, 1, 0, 1] [2, 0, 2, 1, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0] [0, 2, 1, 2, 0, 2, 0, 2, 1, 2, 1, 0, 1] [1, 0, 1, 0, 2, 0, 2]
        [1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 2] [1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 0, 1, 0, 1, 0, 2, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2] false 24
        (level0_relator 9) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive [1, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2]) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] [1, 0, 2, 1, 0, 1, 0, 1, 2] [0, 1, 0, 1, 0, 1] [1, 0, 1, 0, 1, 0] [0, 2, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2]
        [1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 0, 1, 0, 1, 0, 2, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2] [1, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2] true 10
        (level0_relator 4) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 3 → Level0) (positive []) :=
      positive_rewrite_step PresentedGroup.of level0_involution
        [1, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2] [] [1, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1] [2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2, 1, 2] [2, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2]
        [1, 0, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 0, 2, 0, 2, 1, 2, 0, 2, 0, 2] [] false 0
        (level0_relator 9) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation1_0 :
    eval level1Generator (level2Relator 0) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 7 → Level1)
    (level1ChildWord i)) (level2Relator 0) = 1
  rw [← eval_substitute]
  have hs : substitute level1ChildWord (level2Relator 0) =
      positive [4, 4] := by decide
  rw [hs, ← eval_positive_reduce _ level1_involution]
  have hn : positiveReduce ([4, 4] : List (Fin 7)) = [] := by decide
  rw [hn]
  calc
    _ = 1 := eval_nil _

private theorem relation1_1 :
    eval level1Generator (level2Relator 1) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 7 → Level1)
    (level1ChildWord i)) (level2Relator 1) = 1
  rw [← eval_substitute]
  have hs : substitute level1ChildWord (level2Relator 1) =
      positive [0, 0] := by decide
  rw [hs, ← eval_positive_reduce _ level1_involution]
  have hn : positiveReduce ([0, 0] : List (Fin 7)) = [] := by decide
  rw [hn]
  calc
    _ = 1 := eval_nil _

private theorem relation1_2 :
    eval level1Generator (level2Relator 2) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 7 → Level1)
    (level1ChildWord i)) (level2Relator 2) = 1
  rw [← eval_substitute]
  have hs : substitute level1ChildWord (level2Relator 2) =
      positive [2, 2] := by decide
  rw [hs, ← eval_positive_reduce _ level1_involution]
  have hn : positiveReduce ([2, 2] : List (Fin 7)) = [] := by decide
  rw [hn]
  calc
    _ = 1 := eval_nil _

private theorem relation1_3 :
    eval level1Generator (level2Relator 3) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 7 → Level1)
    (level1ChildWord i)) (level2Relator 3) = 1
  rw [← eval_substitute]
  have hs : substitute level1ChildWord (level2Relator 3) =
      positive [3, 3] := by decide
  rw [hs, ← eval_positive_reduce _ level1_involution]
  have hn : positiveReduce ([3, 3] : List (Fin 7)) = [] := by decide
  rw [hn]
  calc
    _ = 1 := eval_nil _

private theorem relation1_4 :
    eval level1Generator (level2Relator 4) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 7 → Level1)
    (level1ChildWord i)) (level2Relator 4) = 1
  rw [← eval_substitute]
  have hs : substitute level1ChildWord (level2Relator 4) =
      positive [5, 5] := by decide
  rw [hs, ← eval_positive_reduce _ level1_involution]
  have hn : positiveReduce ([5, 5] : List (Fin 7)) = [] := by decide
  rw [hn]
  calc
    _ = 1 := eval_nil _

private theorem relation1_5 :
    eval level1Generator (level2Relator 5) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 7 → Level1)
    (level1ChildWord i)) (level2Relator 5) = 1
  rw [← eval_substitute]
  have hs : substitute level1ChildWord (level2Relator 5) =
      positive [6, 6] := by decide
  rw [hs, ← eval_positive_reduce _ level1_involution]
  have hn : positiveReduce ([6, 6] : List (Fin 7)) = [] := by decide
  rw [hn]
  calc
    _ = 1 := eval_nil _

private theorem relation1_6 :
    eval level1Generator (level2Relator 6) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 7 → Level1)
    (level1ChildWord i)) (level2Relator 6) = 1
  rw [← eval_substitute]
  have hs : substitute level1ChildWord (level2Relator 6) =
      positive [0, 3] := by decide
  rw [hs, ← eval_positive_reduce _ level1_involution]
  have hn : positiveReduce ([0, 3] : List (Fin 7)) = [0, 3] := by decide
  rw [hn]
  calc
    _ = eval (PresentedGroup.of : Fin 7 → Level1) (positive []) :=
      positive_rewrite_step PresentedGroup.of level1_involution
        [0, 3] [] [0] [3] [3]
        [0, 3] [] true 1
        (level1_relator 7) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation1_7 :
    eval level1Generator (level2Relator 7) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 7 → Level1)
    (level1ChildWord i)) (level2Relator 7) = 1
  rw [← eval_substitute]
  have hs : substitute level1ChildWord (level2Relator 7) =
      positive [0, 2] := by decide
  rw [hs, ← eval_positive_reduce _ level1_involution]
  have hn : positiveReduce ([0, 2] : List (Fin 7)) = [0, 2] := by decide
  rw [hn]
  calc
    _ = eval (PresentedGroup.of : Fin 7 → Level1) (positive []) :=
      positive_rewrite_step PresentedGroup.of level1_involution
        [0, 2] [] [0] [2] [2]
        [0, 2] [] true 1
        (level1_relator 8) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation1_8 :
    eval level1Generator (level2Relator 8) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 7 → Level1)
    (level1ChildWord i)) (level2Relator 8) = 1
  rw [← eval_substitute]
  have hs : substitute level1ChildWord (level2Relator 8) =
      positive [6, 5, 6, 5] := by decide
  rw [hs, ← eval_positive_reduce _ level1_involution]
  have hn : positiveReduce ([6, 5, 6, 5] : List (Fin 7)) = [6, 5, 6, 5] := by decide
  rw [hn]
  calc
    _ = eval (PresentedGroup.of : Fin 7 → Level1) (positive []) :=
      positive_rewrite_step PresentedGroup.of level1_involution
        [6, 5, 6, 5] [] [6, 5] [5, 6] [6, 5]
        [6, 5, 6, 5] [] true 3
        (level1_relator 9) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation1_9 :
    eval level1Generator (level2Relator 9) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 7 → Level1)
    (level1ChildWord i)) (level2Relator 9) = 1
  rw [← eval_substitute]
  have hs : substitute level1ChildWord (level2Relator 9) =
      positive [6, 4, 6, 4] := by decide
  rw [hs, ← eval_positive_reduce _ level1_involution]
  have hn : positiveReduce ([6, 4, 6, 4] : List (Fin 7)) = [6, 4, 6, 4] := by decide
  rw [hn]
  calc
    _ = eval (PresentedGroup.of : Fin 7 → Level1) (positive []) :=
      positive_rewrite_step PresentedGroup.of level1_involution
        [6, 4, 6, 4] [] [6, 4] [4, 6] [6, 4]
        [6, 4, 6, 4] [] true 3
        (level1_relator 11) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation1_10 :
    eval level1Generator (level2Relator 10) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 7 → Level1)
    (level1ChildWord i)) (level2Relator 10) = 1
  rw [← eval_substitute]
  have hs : substitute level1ChildWord (level2Relator 10) =
      positive [0, 4, 0, 4] := by decide
  rw [hs, ← eval_positive_reduce _ level1_involution]
  have hn : positiveReduce ([0, 4, 0, 4] : List (Fin 7)) = [0, 4, 0, 4] := by decide
  rw [hn]
  calc
    _ = eval (PresentedGroup.of : Fin 7 → Level1) (positive []) :=
      positive_rewrite_step PresentedGroup.of level1_involution
        [0, 4, 0, 4] [] [0, 4] [4, 0] [0, 4]
        [0, 4, 0, 4] [] true 3
        (level1_relator 10) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation1_11 :
    eval level1Generator (level2Relator 11) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 7 → Level1)
    (level1ChildWord i)) (level2Relator 11) = 1
  rw [← eval_substitute]
  have hs : substitute level1ChildWord (level2Relator 11) =
      positive [5, 0, 6, 5, 4] := by decide
  rw [hs, ← eval_positive_reduce _ level1_involution]
  have hn : positiveReduce ([5, 0, 6, 5, 4] : List (Fin 7)) = [5, 0, 6, 5, 4] := by decide
  rw [hn]
  calc
    _ = eval (PresentedGroup.of : Fin 7 → Level1) (positive [5, 0, 5, 6, 4]) :=
      positive_rewrite_step PresentedGroup.of level1_involution
        [6, 5, 6, 5] [5, 0] [6, 5] [5, 6] [4]
        [5, 0, 6, 5, 4] [5, 0, 5, 6, 4] true 3
        (level1_relator 9) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 7 → Level1) (positive []) :=
      positive_rewrite_step PresentedGroup.of level1_involution
        [5, 0, 5, 6, 4] [] [5, 0, 5] [4, 6] [6, 4]
        [5, 0, 5, 6, 4] [] false 0
        (level1_relator 12) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

/-- Every child defining relator holds in its parent presentation. -/
theorem liftedRelations01 : LiftedRelations01 := by
  intro i
  fin_cases i
  · exact relation0_0
  · exact relation0_1
  · exact relation0_2
  · exact relation0_3
  · exact relation0_4
  · exact relation0_5
  · exact relation0_6
  · exact relation0_7
  · exact relation0_8
  · exact relation0_9
  · exact relation0_10
  · exact relation0_11
  · exact relation0_12
  · exact relation0_13
  · exact relation0_14
  · exact relation0_15
  · exact relation0_16
  · exact relation0_17

/-- Every child defining relator holds in its parent presentation. -/
theorem liftedRelations12 : LiftedRelations12 := by
  intro i
  fin_cases i
  · exact relation1_0
  · exact relation1_1
  · exact relation1_2
  · exact relation1_3
  · exact relation1_4
  · exact relation1_5
  · exact relation1_6
  · exact relation1_7
  · exact relation1_8
  · exact relation1_9
  · exact relation1_10
  · exact relation1_11

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.UpperBoundChain
