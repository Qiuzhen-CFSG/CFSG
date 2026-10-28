module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.PresentationBound.StabilizerBound.Rewriting
public import Mathlib.Tactic.FinCases

/-!
# Certified lifting of the recursive stabilizer relations

Each proof substitutes the named child words, then replaces subwords by a
cyclic conjugate of a parent defining relator or its inverse. Every syntactic
check uses kernel reduction. The 71 traces are retained in `source/lift_traces.json`;
`source/generate_relations.py` reproduces this file. No permutation identities
or externally computed orders occur among the hypotheses.
-/

public section
namespace Janko4.Cardinality.QuotientCount.UpperBound.PresentationBound.StabilizerChain
open Subgroup.CosetWordCertificate

private theorem relation1_0 :
    eval level1Generator (level2Relator 0) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 10 → Level1)
    (level1ChildWord i)) (level2Relator 0) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level1ChildWord (level2Relator 0)) =
      [(8, true), (8, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 0)
        [] [(8, true)] [(8, false)] [(8, true)]
        [(8, true), (8, true)] [] false 0
        (level1_relator 0) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation1_1 :
    eval level1Generator (level2Relator 1) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 10 → Level1)
    (level1ChildWord i)) (level2Relator 1) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level1ChildWord (level2Relator 1)) =
      [(4, false), (2, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 1)
        [] [(4, false)] [(2, false)] [(2, true)]
        [(4, false), (2, true)] [] false 0
        (level1_relator 1) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation1_2 :
    eval level1Generator (level2Relator 2) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 10 → Level1)
    (level1ChildWord i)) (level2Relator 2) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level1ChildWord (level2Relator 2)) =
      [(7, true), (7, true), (7, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 2)
        [] [(7, true), (7, true)] [(7, false)] [(7, true)]
        [(7, true), (7, true), (7, true)] [] false 0
        (level1_relator 2) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation1_3 :
    eval level1Generator (level2Relator 3) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 10 → Level1)
    (level1ChildWord i)) (level2Relator 3) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level1ChildWord (level2Relator 3)) =
      [(9, true), (9, true), (9, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 3)
        [] [(9, true), (9, true)] [(9, false)] [(9, true)]
        [(9, true), (9, true), (9, true)] [] false 0
        (level1_relator 3) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation1_4 :
    eval level1Generator (level2Relator 4) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 10 → Level1)
    (level1ChildWord i)) (level2Relator 4) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level1ChildWord (level2Relator 4)) =
      [(2, true), (4, true), (2, true), (4, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 4)
        [] [(2, true), (4, true)] [(4, false), (2, false)] [(2, true), (4, true)]
        [(2, true), (4, true), (2, true), (4, true)] [] false 0
        (level1_relator 4) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation1_5 :
    eval level1Generator (level2Relator 5) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 10 → Level1)
    (level1ChildWord i)) (level2Relator 5) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level1ChildWord (level2Relator 5)) =
      [(7, true), (5, false), (6, false), (6, false)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 5)
        [] [(7, true), (5, false)] [(6, true), (6, true)] [(6, false), (6, false)]
        [(7, true), (5, false), (6, false), (6, false)] [] false 0
        (level1_relator 5) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation1_6 :
    eval level1Generator (level2Relator 6) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 10 → Level1)
    (level1ChildWord i)) (level2Relator 6) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level1ChildWord (level2Relator 6)) =
      [(9, true), (7, false), (9, true), (7, false)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 6)
        [] [(9, true), (7, false)] [(7, true), (9, false)] [(9, true), (7, false)]
        [(9, true), (7, false), (9, true), (7, false)] [] false 0
        (level1_relator 6) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation1_7 :
    eval level1Generator (level2Relator 7) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 10 → Level1)
    (level1ChildWord i)) (level2Relator 7) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level1ChildWord (level2Relator 7)) =
      [(6, true), (6, true), (6, true), (7, true), (5, false)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [(6, false), (6, false), (7, true), (5, false)] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 7)
        [] [(6, true), (6, true), (6, true)] [(6, false), (6, false)] [(7, true), (5, false)]
        [(6, true), (6, true), (6, true), (7, true), (5, false)] [(6, false), (6, false), (7, true), (5, false)] false 0
        (level1_relator 7) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 5)
        [] [(6, false), (6, false)] [(5, true), (7, false)] [(7, true), (5, false)]
        [(6, false), (6, false), (7, true), (5, false)] [] false 2
        (level1_relator 5) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation1_8 :
    eval level1Generator (level2Relator 8) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 10 → Level1)
    (level1ChildWord i)) (level2Relator 8) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level1ChildWord (level2Relator 8)) =
      [(8, true), (6, false), (8, true), (9, false), (2, true), (4, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [(2, true), (4, true), (2, true), (4, true)] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 9)
        [] [(8, true), (6, false), (8, true)] [(2, true), (4, true), (9, true)] [(9, false), (2, true), (4, true)]
        [(8, true), (6, false), (8, true), (9, false), (2, true), (4, true)] [(2, true), (4, true), (2, true), (4, true)] false 0
        (level1_relator 9) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 4)
        [] [(2, true), (4, true)] [(4, false), (2, false)] [(2, true), (4, true)]
        [(2, true), (4, true), (2, true), (4, true)] [] false 0
        (level1_relator 4) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation1_9 :
    eval level1Generator (level2Relator 9) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 10 → Level1)
    (level1ChildWord i)) (level2Relator 9) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level1ChildWord (level2Relator 9)) =
      [(9, false), (7, true), (8, true), (7, false), (9, true), (8, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [(8, false), (7, false), (9, true), (7, false), (9, true), (8, true)] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 10)
        [] [(9, false), (7, true), (8, true)] [(8, false), (7, false), (9, true)] [(7, false), (9, true), (8, true)]
        [(9, false), (7, true), (8, true), (7, false), (9, true), (8, true)] [(8, false), (7, false), (9, true), (7, false), (9, true), (8, true)] false 0
        (level1_relator 10) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 6)
        [(8, false)] [(7, false), (9, true)] [(9, false), (7, true)] [(7, false), (9, true), (8, true)]
        [(8, false), (7, false), (9, true), (7, false), (9, true), (8, true)] [] false 1
        (level1_relator 6) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation1_10 :
    eval level1Generator (level2Relator 10) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 10 → Level1)
    (level1ChildWord i)) (level2Relator 10) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level1ChildWord (level2Relator 10)) =
      [(7, true), (9, false), (8, true), (9, true), (7, false), (8, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [(8, false), (9, true), (7, false), (9, true), (7, false), (8, true)] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 11)
        [] [(7, true), (9, false), (8, true)] [(8, false), (9, true), (7, false)] [(9, true), (7, false), (8, true)]
        [(7, true), (9, false), (8, true), (9, true), (7, false), (8, true)] [(8, false), (9, true), (7, false), (9, true), (7, false), (8, true)] false 0
        (level1_relator 11) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 6)
        [(8, false)] [(9, true), (7, false)] [(7, true), (9, false)] [(9, true), (7, false), (8, true)]
        [(8, false), (9, true), (7, false), (9, true), (7, false), (8, true)] [] false 0
        (level1_relator 6) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation1_11 :
    eval level1Generator (level2Relator 11) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 10 → Level1)
    (level1ChildWord i)) (level2Relator 11) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level1ChildWord (level2Relator 11)) =
      [(8, true), (9, true), (2, true), (4, true), (7, false), (5, false)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [(8, true), (9, true), (4, false), (2, false), (7, false), (5, false)] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 4)
        [(8, true), (9, true)] [(2, true), (4, true)] [(4, false), (2, false)] [(7, false), (5, false)]
        [(8, true), (9, true), (2, true), (4, true), (7, false), (5, false)] [(8, true), (9, true), (4, false), (2, false), (7, false), (5, false)] false 0
        (level1_relator 4) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 12)
        [] [(8, true), (9, true), (4, false)] [(5, true), (7, true), (2, true)] [(2, false), (7, false), (5, false)]
        [(8, true), (9, true), (4, false), (2, false), (7, false), (5, false)] [] false 0
        (level1_relator 12) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation1_12 :
    eval level1Generator (level2Relator 12) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 10 → Level1)
    (level1ChildWord i)) (level2Relator 12) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level1ChildWord (level2Relator 12)) =
      [(6, false), (2, true), (4, true), (9, true), (6, false), (8, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [(6, false), (4, false), (2, false), (9, true), (6, false), (8, true)] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 4)
        [(6, false)] [(2, true), (4, true)] [(4, false), (2, false)] [(9, true), (6, false), (8, true)]
        [(6, false), (2, true), (4, true), (9, true), (6, false), (8, true)] [(6, false), (4, false), (2, false), (9, true), (6, false), (8, true)] false 0
        (level1_relator 4) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 8)
        [] [(6, false), (4, false), (2, false)] [(8, false), (6, true), (9, false)] [(9, true), (6, false), (8, true)]
        [(6, false), (4, false), (2, false), (9, true), (6, false), (8, true)] [] false 0
        (level1_relator 8) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation1_13 :
    eval level1Generator (level2Relator 13) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 10 → Level1)
    (level1ChildWord i)) (level2Relator 13) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level1ChildWord (level2Relator 13)) =
      [(9, false), (2, true), (3, true), (9, false), (2, true), (3, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 14)
        [] [(9, false), (2, true), (3, true)] [(3, false), (2, false), (9, true)] [(9, false), (2, true), (3, true)]
        [(9, false), (2, true), (3, true), (9, false), (2, true), (3, true)] [] false 0
        (level1_relator 14) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation1_14 :
    eval level1Generator (level2Relator 14) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 10 → Level1)
    (level1ChildWord i)) (level2Relator 14) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level1ChildWord (level2Relator 14)) =
      [(8, true), (7, false), (8, true), (7, false), (8, true), (7, false)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 15)
        [] [(8, true), (7, false), (8, true)] [(7, true), (8, false), (7, true)] [(7, false), (8, true), (7, false)]
        [(8, true), (7, false), (8, true), (7, false), (8, true), (7, false)] [] false 0
        (level1_relator 15) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation1_15 :
    eval level1Generator (level2Relator 15) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 10 → Level1)
    (level1ChildWord i)) (level2Relator 15) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level1ChildWord (level2Relator 15)) =
      [(2, true), (4, true), (8, true), (7, false), (9, true), (5, true), (6, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [(2, true), (4, true), (8, false), (7, false), (9, true), (5, true), (6, true)] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 0)
        [(2, true), (4, true)] [(8, true)] [(8, false)] [(7, false), (9, true), (5, true), (6, true)]
        [(2, true), (4, true), (8, true), (7, false), (9, true), (5, true), (6, true)] [(2, true), (4, true), (8, false), (7, false), (9, true), (5, true), (6, true)] false 0
        (level1_relator 0) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [(2, true), (4, true), (9, false), (7, true), (8, true), (5, true), (6, true)] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 10)
        [(2, true), (4, true)] [(8, false), (7, false), (9, true)] [(9, false), (7, true), (8, true)] [(5, true), (6, true)]
        [(2, true), (4, true), (8, false), (7, false), (9, true), (5, true), (6, true)] [(2, true), (4, true), (9, false), (7, true), (8, true), (5, true), (6, true)] true 0
        (level1_relator 10) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 16)
        [] [(2, true), (4, true), (9, false), (7, true)] [(6, false), (5, false), (8, false)] [(8, true), (5, true), (6, true)]
        [(2, true), (4, true), (9, false), (7, true), (8, true), (5, true), (6, true)] [] false 0
        (level1_relator 16) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation1_16 :
    eval level1Generator (level2Relator 16) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 10 → Level1)
    (level1ChildWord i)) (level2Relator 16) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level1ChildWord (level2Relator 16)) =
      [(8, true), (7, false), (2, true), (3, true), (7, false), (2, true), (3, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 17)
        [] [(8, true), (7, false), (2, true), (3, true)] [(3, false), (2, false), (7, true)] [(7, false), (2, true), (3, true)]
        [(8, true), (7, false), (2, true), (3, true), (7, false), (2, true), (3, true)] [] false 0
        (level1_relator 17) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation1_17 :
    eval level1Generator (level2Relator 17) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 10 → Level1)
    (level1ChildWord i)) (level2Relator 17) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level1ChildWord (level2Relator 17)) =
      [(5, false), (5, false), (9, false), (2, false), (7, true), (6, false), (2, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 18)
        [] [(5, false), (5, false), (9, false), (2, false)] [(2, false), (6, true), (7, false)] [(7, true), (6, false), (2, true)]
        [(5, false), (5, false), (9, false), (2, false), (7, true), (6, false), (2, true)] [] false 0
        (level1_relator 18) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation1_18 :
    eval level1Generator (level2Relator 18) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 10 → Level1)
    (level1ChildWord i)) (level2Relator 18) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level1ChildWord (level2Relator 18)) =
      [(2, false), (7, false), (9, true), (8, true), (2, false), (5, true), (2, true), (7, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [(2, false), (7, false), (9, true), (8, false), (2, false), (5, true), (2, true), (7, true)] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 0)
        [(2, false), (7, false), (9, true)] [(8, true)] [(8, false)] [(2, false), (5, true), (2, true), (7, true)]
        [(2, false), (7, false), (9, true), (8, true), (2, false), (5, true), (2, true), (7, true)] [(2, false), (7, false), (9, true), (8, false), (2, false), (5, true), (2, true), (7, true)] false 0
        (level1_relator 0) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [(2, false), (8, true), (9, false), (7, true), (2, false), (5, true), (2, true), (7, true)] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 10)
        [(2, false)] [(7, false), (9, true), (8, false)] [(8, true), (9, false), (7, true)] [(2, false), (5, true), (2, true), (7, true)]
        [(2, false), (7, false), (9, true), (8, false), (2, false), (5, true), (2, true), (7, true)] [(2, false), (8, true), (9, false), (7, true), (2, false), (5, true), (2, true), (7, true)] true 1
        (level1_relator 10) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 20)
        [] [(2, false), (8, true), (9, false), (7, true)] [(7, false), (2, false), (5, false), (2, true)] [(2, false), (5, true), (2, true), (7, true)]
        [(2, false), (8, true), (9, false), (7, true), (2, false), (5, true), (2, true), (7, true)] [] false 0
        (level1_relator 20) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation1_19 :
    eval level1Generator (level2Relator 19) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 10 → Level1)
    (level1ChildWord i)) (level2Relator 19) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level1ChildWord (level2Relator 19)) =
      [(9, false), (8, true), (2, true), (5, false), (3, false), (9, true), (3, true), (3, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 21)
        [] [(9, false), (8, true), (2, true), (5, false)] [(3, false), (3, false), (9, false), (3, true)] [(3, false), (9, true), (3, true), (3, true)]
        [(9, false), (8, true), (2, true), (5, false), (3, false), (9, true), (3, true), (3, true)] [] false 0
        (level1_relator 21) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation1_20 :
    eval level1Generator (level2Relator 20) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 10 → Level1)
    (level1ChildWord i)) (level2Relator 20) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level1ChildWord (level2Relator 20)) =
      [(9, false), (7, false), (8, true), (2, true), (5, false), (7, false), (5, true), (2, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 22)
        [] [(9, false), (7, false), (8, true), (2, true)] [(2, false), (5, false), (7, true), (5, true)] [(5, false), (7, false), (5, true), (2, true)]
        [(9, false), (7, false), (8, true), (2, true), (5, false), (7, false), (5, true), (2, true)] [] false 0
        (level1_relator 22) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation1_21 :
    eval level1Generator (level2Relator 21) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 10 → Level1)
    (level1ChildWord i)) (level2Relator 21) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level1ChildWord (level2Relator 21)) =
      [(8, true), (2, true), (5, false), (4, false), (3, true), (7, false), (2, false), (5, true), (3, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 24)
        [] [(8, true), (2, true), (5, false), (4, false), (3, true)] [(3, false), (5, false), (2, true), (7, true)] [(7, false), (2, false), (5, true), (3, true)]
        [(8, true), (2, true), (5, false), (4, false), (3, true), (7, false), (2, false), (5, true), (3, true)] [] false 0
        (level1_relator 24) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation1_22 :
    eval level1Generator (level2Relator 22) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 10 → Level1)
    (level1ChildWord i)) (level2Relator 22) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level1ChildWord (level2Relator 22)) =
      [(5, false), (7, true), (9, false), (2, false), (5, false), (6, false), (3, true), (9, true), (7, false), (3, false)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [(3, true), (9, true), (7, false), (9, true), (7, false), (3, false)] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 26)
        [] [(5, false), (7, true), (9, false), (2, false), (5, false)] [(3, true), (9, true), (7, false), (3, false), (6, true)] [(6, false), (3, true), (9, true), (7, false), (3, false)]
        [(5, false), (7, true), (9, false), (2, false), (5, false), (6, false), (3, true), (9, true), (7, false), (3, false)] [(3, true), (9, true), (7, false), (9, true), (7, false), (3, false)] false 0
        (level1_relator 26) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 6)
        [(3, true)] [(9, true), (7, false)] [(7, true), (9, false)] [(9, true), (7, false), (3, false)]
        [(3, true), (9, true), (7, false), (9, true), (7, false), (3, false)] [] false 0
        (level1_relator 6) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation1_23 :
    eval level1Generator (level2Relator 23) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 10 → Level1)
    (level1ChildWord i)) (level2Relator 23) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level1ChildWord (level2Relator 23)) =
      [(7, false), (8, true), (9, false), (5, false), (2, true), (5, false), (2, true), (4, true), (6, false), (2, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [(2, false), (6, true), (2, true), (4, true), (2, true), (4, true), (6, false), (2, true)] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 28)
        [] [(7, false), (8, true), (9, false), (5, false), (2, true)] [(2, false), (6, true), (2, true), (4, true), (5, true)] [(5, false), (2, true), (4, true), (6, false), (2, true)]
        [(7, false), (8, true), (9, false), (5, false), (2, true), (5, false), (2, true), (4, true), (6, false), (2, true)] [(2, false), (6, true), (2, true), (4, true), (2, true), (4, true), (6, false), (2, true)] false 0
        (level1_relator 28) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 4)
        [(2, false), (6, true)] [(2, true), (4, true)] [(4, false), (2, false)] [(2, true), (4, true), (6, false), (2, true)]
        [(2, false), (6, true), (2, true), (4, true), (2, true), (4, true), (6, false), (2, true)] [] false 0
        (level1_relator 4) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation1_24 :
    eval level1Generator (level2Relator 24) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 10 → Level1)
    (level1ChildWord i)) (level2Relator 24) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level1ChildWord (level2Relator 24)) =
      [(9, false), (8, true), (9, false), (5, false), (2, false), (8, true), (3, true), (5, false), (2, true), (3, false)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 29)
        [] [(9, false), (8, true), (9, false), (5, false), (2, false)] [(3, true), (2, false), (5, true), (3, false), (8, false)] [(8, true), (3, true), (5, false), (2, true), (3, false)]
        [(9, false), (8, true), (9, false), (5, false), (2, false), (8, true), (3, true), (5, false), (2, true), (3, false)] [] false 0
        (level1_relator 29) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation1_25 :
    eval level1Generator (level2Relator 25) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 10 → Level1)
    (level1ChildWord i)) (level2Relator 25) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level1ChildWord (level2Relator 25)) =
      [(6, false), (2, true), (5, true), (8, true), (6, false), (8, true), (7, false), (3, false), (8, true), (6, false), (3, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [(6, false), (2, true), (5, true), (2, true), (4, true), (9, true), (7, false), (3, false), (8, true), (6, false), (3, true)] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 9)
        [(6, false), (2, true), (5, true)] [(8, true), (6, false), (8, true)] [(2, true), (4, true), (9, true)] [(7, false), (3, false), (8, true), (6, false), (3, true)]
        [(6, false), (2, true), (5, true), (8, true), (6, false), (8, true), (7, false), (3, false), (8, true), (6, false), (3, true)] [(6, false), (2, true), (5, true), (2, true), (4, true), (9, true), (7, false), (3, false), (8, true), (6, false), (3, true)] false 0
        (level1_relator 9) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 31)
        [] [(6, false), (2, true), (5, true), (2, true), (4, true), (9, true)] [(3, false), (6, true), (8, false), (3, true), (7, true)] [(7, false), (3, false), (8, true), (6, false), (3, true)]
        [(6, false), (2, true), (5, true), (2, true), (4, true), (9, true), (7, false), (3, false), (8, true), (6, false), (3, true)] [] false 0
        (level1_relator 31) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation1_26 :
    eval level1Generator (level2Relator 26) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 10 → Level1)
    (level1ChildWord i)) (level2Relator 26) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level1ChildWord (level2Relator 26)) =
      [(9, false), (7, false), (9, false), (6, false), (2, false), (6, true), (9, false), (3, false), (7, false), (2, false), (3, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 33)
        [] [(9, false), (7, false), (9, false), (6, false), (2, false), (6, true)] [(3, false), (2, true), (7, true), (3, true), (9, true)] [(9, false), (3, false), (7, false), (2, false), (3, true)]
        [(9, false), (7, false), (9, false), (6, false), (2, false), (6, true), (9, false), (3, false), (7, false), (2, false), (3, true)] [] false 0
        (level1_relator 33) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation1_27 :
    eval level1Generator (level2Relator 27) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 10 → Level1)
    (level1ChildWord i)) (level2Relator 27) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level1ChildWord (level2Relator 27)) =
      [(7, true), (5, false), (2, true), (5, false), (5, false), (9, true), (8, true), (7, false), (3, true), (6, true), (7, false), (3, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [(7, true), (5, false), (6, false), (6, false)] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 35)
        [(7, true), (5, false)] [(2, true), (5, false), (5, false), (9, true), (8, true), (7, false)] [(6, false), (6, false), (3, false), (7, true), (6, false), (3, false)] [(3, true), (6, true), (7, false), (3, true)]
        [(7, true), (5, false), (2, true), (5, false), (5, false), (9, true), (8, true), (7, false), (3, true), (6, true), (7, false), (3, true)] [(7, true), (5, false), (6, false), (6, false)] false 2
        (level1_relator 35) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 5)
        [] [(7, true), (5, false)] [(6, true), (6, true)] [(6, false), (6, false)]
        [(7, true), (5, false), (6, false), (6, false)] [] false 0
        (level1_relator 5) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation1_28 :
    eval level1Generator (level2Relator 28) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 10 → Level1)
    (level1ChildWord i)) (level2Relator 28) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level1ChildWord (level2Relator 28)) =
      [(8, true), (9, false), (4, false), (2, false), (5, true), (7, true), (2, false), (8, true), (3, false), (9, false), (5, false), (3, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [(8, true), (9, false), (4, false), (2, false), (6, true), (8, false), (6, true), (8, false)] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 38)
        [(8, true), (9, false), (4, false), (2, false)] [(5, true), (7, true), (2, false), (8, true), (3, false), (9, false)] [(6, true), (8, false), (6, true), (8, false), (3, false), (5, true)] [(5, false), (3, true)]
        [(8, true), (9, false), (4, false), (2, false), (5, true), (7, true), (2, false), (8, true), (3, false), (9, false), (5, false), (3, true)] [(8, true), (9, false), (4, false), (2, false), (6, true), (8, false), (6, true), (8, false)] false 4
        (level1_relator 38) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [(6, true), (8, false), (6, true), (8, false), (6, true), (8, false)] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 9)
        [] [(8, true), (9, false), (4, false)] [(6, true), (8, false), (2, true)] [(2, false), (6, true), (8, false), (6, true), (8, false)]
        [(8, true), (9, false), (4, false), (2, false), (6, true), (8, false), (6, true), (8, false)] [(6, true), (8, false), (6, true), (8, false), (6, true), (8, false)] false 2
        (level1_relator 9) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [(4, false), (2, false), (9, true), (8, false), (6, true), (8, false)] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 8)
        [] [(6, true), (8, false), (6, true)] [(4, false), (2, false), (9, true)] [(8, false), (6, true), (8, false)]
        [(6, true), (8, false), (6, true), (8, false), (6, true), (8, false)] [(4, false), (2, false), (9, true), (8, false), (6, true), (8, false)] true 5
        (level1_relator 8) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [(4, false), (2, false), (4, false), (2, false)] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 9)
        [(4, false), (2, false)] [(9, true), (8, false), (6, true)] [(4, false), (2, false), (8, true)] [(8, false)]
        [(4, false), (2, false), (9, true), (8, false), (6, true), (8, false)] [(4, false), (2, false), (4, false), (2, false)] true 2
        (level1_relator 9) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 10 → Level1) [] :=
      rewrite_step PresentedGroup.of (stabilizerRelator 4)
        [] [(4, false), (2, false)] [(2, true), (4, true)] [(4, false), (2, false)]
        [(4, false), (2, false), (4, false), (2, false)] [] true 0
        (level1_relator 4) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation2_0 :
    eval level2Generator (level3Relator 0) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 8 → Level2)
    (level2ChildWord i)) (level3Relator 0) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level2ChildWord (level3Relator 0)) =
      [(6, true), (6, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [] :=
      rewrite_step PresentedGroup.of (level2Relator 0)
        [] [(6, true)] [(6, false)] [(6, true)]
        [(6, true), (6, true)] [] false 0
        (level2_relator 0) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation2_1 :
    eval level2Generator (level3Relator 1) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 8 → Level2)
    (level2ChildWord i)) (level3Relator 1) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level2ChildWord (level3Relator 1)) =
      [(0, true), (2, true), (0, true), (2, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [] :=
      rewrite_step PresentedGroup.of (level2Relator 4)
        [] [(0, true), (2, true)] [(2, false), (0, false)] [(0, true), (2, true)]
        [(0, true), (2, true), (0, true), (2, true)] [] false 0
        (level2_relator 4) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation2_2 :
    eval level2Generator (level3Relator 2) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 8 → Level2)
    (level2ChildWord i)) (level3Relator 2) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level2ChildWord (level3Relator 2)) =
      [(0, true), (0, true), (0, true), (2, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [(0, true), (2, true), (0, true), (2, true)] :=
      rewrite_step PresentedGroup.of (level2Relator 1)
        [(0, true)] [(0, true)] [(2, true)] [(0, true), (2, true)]
        [(0, true), (0, true), (0, true), (2, true)] [(0, true), (2, true), (0, true), (2, true)] false 1
        (level2_relator 1) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [] :=
      rewrite_step PresentedGroup.of (level2Relator 4)
        [] [(0, true), (2, true)] [(2, false), (0, false)] [(0, true), (2, true)]
        [(0, true), (2, true), (0, true), (2, true)] [] false 0
        (level2_relator 4) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation2_3 :
    eval level2Generator (level3Relator 3) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 8 → Level2)
    (level2ChildWord i)) (level3Relator 3) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level2ChildWord (level3Relator 3)) =
      [(5, true), (5, true), (5, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [] :=
      rewrite_step PresentedGroup.of (level2Relator 2)
        [] [(5, true), (5, true)] [(5, false)] [(5, true)]
        [(5, true), (5, true), (5, true)] [] false 0
        (level2_relator 2) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation2_4 :
    eval level2Generator (level3Relator 4) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 8 → Level2)
    (level2ChildWord i)) (level3Relator 4) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level2ChildWord (level3Relator 4)) =
      [(7, true), (7, true), (7, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [] :=
      rewrite_step PresentedGroup.of (level2Relator 3)
        [] [(7, true), (7, true)] [(7, false)] [(7, true)]
        [(7, true), (7, true), (7, true)] [] false 0
        (level2_relator 3) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation2_5 :
    eval level2Generator (level3Relator 5) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 8 → Level2)
    (level2ChildWord i)) (level3Relator 5) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level2ChildWord (level3Relator 5)) =
      [(5, true), (3, false), (4, false), (4, false)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [] :=
      rewrite_step PresentedGroup.of (level2Relator 5)
        [] [(5, true), (3, false)] [(4, true), (4, true)] [(4, false), (4, false)]
        [(5, true), (3, false), (4, false), (4, false)] [] false 0
        (level2_relator 5) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation2_6 :
    eval level2Generator (level3Relator 6) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 8 → Level2)
    (level2ChildWord i)) (level3Relator 6) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level2ChildWord (level3Relator 6)) =
      [(7, true), (5, false), (7, true), (5, false)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [] :=
      rewrite_step PresentedGroup.of (level2Relator 6)
        [] [(7, true), (5, false)] [(5, true), (7, false)] [(7, true), (5, false)]
        [(7, true), (5, false), (7, true), (5, false)] [] false 0
        (level2_relator 6) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation2_7 :
    eval level2Generator (level3Relator 7) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 8 → Level2)
    (level2ChildWord i)) (level3Relator 7) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level2ChildWord (level3Relator 7)) =
      [(4, true), (4, true), (4, true), (5, true), (3, false)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [] :=
      rewrite_step PresentedGroup.of (level2Relator 7)
        [] [(4, true), (4, true), (4, true)] [(3, true), (5, false)] [(5, true), (3, false)]
        [(4, true), (4, true), (4, true), (5, true), (3, false)] [] false 0
        (level2_relator 7) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation2_8 :
    eval level2Generator (level3Relator 8) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 8 → Level2)
    (level2ChildWord i)) (level3Relator 8) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level2ChildWord (level3Relator 8)) =
      [(6, true), (7, false), (0, true), (2, true), (6, true), (4, false)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [] :=
      rewrite_step PresentedGroup.of (level2Relator 8)
        [] [(6, true), (7, false), (0, true)] [(4, true), (6, false), (2, false)] [(2, true), (6, true), (4, false)]
        [(6, true), (7, false), (0, true), (2, true), (6, true), (4, false)] [] false 2
        (level2_relator 8) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation2_9 :
    eval level2Generator (level3Relator 9) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 8 → Level2)
    (level2ChildWord i)) (level3Relator 9) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level2ChildWord (level3Relator 9)) =
      [(6, true), (7, true), (0, true), (2, true), (5, false), (3, false)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [] :=
      rewrite_step PresentedGroup.of (level2Relator 11)
        [] [(6, true), (7, true), (0, true)] [(3, true), (5, true), (2, false)] [(2, true), (5, false), (3, false)]
        [(6, true), (7, true), (0, true), (2, true), (5, false), (3, false)] [] false 0
        (level2_relator 11) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation2_10 :
    eval level2Generator (level3Relator 10) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 8 → Level2)
    (level2ChildWord i)) (level3Relator 10) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level2ChildWord (level3Relator 10)) =
      [(4, false), (0, true), (2, true), (7, true), (4, false), (6, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [] :=
      rewrite_step PresentedGroup.of (level2Relator 12)
        [] [(4, false), (0, true), (2, true)] [(6, false), (4, true), (7, false)] [(7, true), (4, false), (6, true)]
        [(4, false), (0, true), (2, true), (7, true), (4, false), (6, true)] [] false 0
        (level2_relator 12) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation2_11 :
    eval level2Generator (level3Relator 11) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 8 → Level2)
    (level2ChildWord i)) (level3Relator 11) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level2ChildWord (level3Relator 11)) =
      [(7, false), (5, true), (6, true), (0, true), (2, true), (4, false), (3, false)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [(7, false), (5, true), (6, true), (2, false), (0, false), (4, false), (3, false)] :=
      rewrite_step PresentedGroup.of (level2Relator 4)
        [(7, false), (5, true), (6, true)] [(0, true), (2, true)] [(2, false), (0, false)] [(4, false), (3, false)]
        [(7, false), (5, true), (6, true), (0, true), (2, true), (4, false), (3, false)] [(7, false), (5, true), (6, true), (2, false), (0, false), (4, false), (3, false)] false 0
        (level2_relator 4) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [(7, false), (5, true), (6, true), (6, true), (5, false), (7, true)] :=
      rewrite_step PresentedGroup.of (level2Relator 15)
        [(7, false), (5, true), (6, true)] [(2, false), (0, false), (4, false), (3, false)] [(6, true), (5, false), (7, true)] []
        [(7, false), (5, true), (6, true), (2, false), (0, false), (4, false), (3, false)] [(7, false), (5, true), (6, true), (6, true), (5, false), (7, true)] true 5
        (level2_relator 15) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [] :=
      rewrite_step PresentedGroup.of (level2Relator 0)
        [(7, false), (5, true)] [(6, true)] [(6, false)] [(6, true), (5, false), (7, true)]
        [(7, false), (5, true), (6, true), (6, true), (5, false), (7, true)] [] false 0
        (level2_relator 0) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation2_12 :
    eval level2Generator (level3Relator 12) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 8 → Level2)
    (level2ChildWord i)) (level3Relator 12) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level2ChildWord (level3Relator 12)) =
      [(0, true), (2, true), (7, false), (5, true), (6, true), (3, true), (4, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [(0, true), (2, true), (5, false), (7, true), (6, true), (3, true), (4, true)] :=
      rewrite_step PresentedGroup.of (level2Relator 6)
        [(0, true), (2, true)] [(7, false), (5, true)] [(5, false), (7, true)] [(6, true), (3, true), (4, true)]
        [(0, true), (2, true), (7, false), (5, true), (6, true), (3, true), (4, true)] [(0, true), (2, true), (5, false), (7, true), (6, true), (3, true), (4, true)] true 1
        (level2_relator 6) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [(0, true), (2, true), (6, false), (5, false), (7, true), (3, true), (4, true)] :=
      rewrite_step PresentedGroup.of (level2Relator 9)
        [(0, true), (2, true)] [(5, false), (7, true), (6, true)] [(6, false), (5, false), (7, true)] [(3, true), (4, true)]
        [(0, true), (2, true), (5, false), (7, true), (6, true), (3, true), (4, true)] [(0, true), (2, true), (6, false), (5, false), (7, true), (3, true), (4, true)] false 3
        (level2_relator 9) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [(0, true), (2, true), (6, false), (6, false), (2, false), (0, false)] :=
      rewrite_step PresentedGroup.of (level2Relator 15)
        [(0, true), (2, true), (6, false)] [(5, false), (7, true), (3, true), (4, true)] [(6, false), (2, false), (0, false)] []
        [(0, true), (2, true), (6, false), (5, false), (7, true), (3, true), (4, true)] [(0, true), (2, true), (6, false), (6, false), (2, false), (0, false)] false 3
        (level2_relator 15) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [] :=
      rewrite_step PresentedGroup.of (level2Relator 0)
        [(0, true), (2, true)] [(6, false)] [(6, true)] [(6, false), (2, false), (0, false)]
        [(0, true), (2, true), (6, false), (6, false), (2, false), (0, false)] [] true 0
        (level2_relator 0) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation2_13 :
    eval level2Generator (level3Relator 13) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 8 → Level2)
    (level2ChildWord i)) (level3Relator 13) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level2ChildWord (level3Relator 13)) =
      [(0, true), (2, true), (7, true), (5, true), (0, true), (2, true), (4, true), (3, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [(0, true), (2, true), (7, true), (5, true), (2, false), (0, false), (4, true), (3, true)] :=
      rewrite_step PresentedGroup.of (level2Relator 4)
        [(0, true), (2, true), (7, true), (5, true)] [(0, true)] [(2, false), (0, false), (2, false)] [(2, true), (4, true), (3, true)]
        [(0, true), (2, true), (7, true), (5, true), (0, true), (2, true), (4, true), (3, true)] [(0, true), (2, true), (7, true), (5, true), (2, false), (0, false), (4, true), (3, true)] false 0
        (level2_relator 4) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [(0, true), (2, true), (7, true), (5, true), (2, false), (0, false), (4, false), (5, true)] :=
      rewrite_step PresentedGroup.of (level2Relator 5)
        [(0, true), (2, true), (7, true), (5, true), (2, false), (0, false)] [(4, true)] [(4, false), (5, true), (3, false)] [(3, true)]
        [(0, true), (2, true), (7, true), (5, true), (2, false), (0, false), (4, true), (3, true)] [(0, true), (2, true), (7, true), (5, true), (2, false), (0, false), (4, false), (5, true)] true 1
        (level2_relator 5) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [(0, true), (2, true), (7, true), (5, true), (6, true), (5, false), (7, true), (3, true), (5, true)] :=
      rewrite_step PresentedGroup.of (level2Relator 15)
        [(0, true), (2, true), (7, true), (5, true)] [(2, false), (0, false), (4, false)] [(6, true), (5, false), (7, true), (3, true)] [(5, true)]
        [(0, true), (2, true), (7, true), (5, true), (2, false), (0, false), (4, false), (5, true)] [(0, true), (2, true), (7, true), (5, true), (6, true), (5, false), (7, true), (3, true), (5, true)] true 5
        (level2_relator 15) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [(0, true), (2, true), (7, true), (7, true), (6, false), (3, true), (5, true)] :=
      rewrite_step PresentedGroup.of (level2Relator 9)
        [(0, true), (2, true), (7, true)] [(5, true), (6, true)] [(7, true), (6, false), (7, false), (5, true)] [(5, false), (7, true), (3, true), (5, true)]
        [(0, true), (2, true), (7, true), (5, true), (6, true), (5, false), (7, true), (3, true), (5, true)] [(0, true), (2, true), (7, true), (7, true), (6, false), (3, true), (5, true)] false 1
        (level2_relator 9) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [(0, true), (2, true), (7, false), (6, false), (3, true), (5, true)] :=
      rewrite_step PresentedGroup.of (level2Relator 3)
        [(0, true), (2, true)] [(7, true)] [(7, false), (7, false)] [(7, true), (6, false), (3, true), (5, true)]
        [(0, true), (2, true), (7, true), (7, true), (6, false), (3, true), (5, true)] [(0, true), (2, true), (7, false), (6, false), (3, true), (5, true)] false 0
        (level2_relator 3) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [(0, true), (2, true), (0, true), (2, true)] :=
      rewrite_step PresentedGroup.of (level2Relator 11)
        [(0, true), (2, true)] [(7, false), (6, false)] [(0, true), (2, true), (5, false), (3, false)] [(3, true), (5, true)]
        [(0, true), (2, true), (7, false), (6, false), (3, true), (5, true)] [(0, true), (2, true), (0, true), (2, true)] true 4
        (level2_relator 11) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [] :=
      rewrite_step PresentedGroup.of (level2Relator 4)
        [] [(0, true)] [(2, false), (0, false), (2, false)] [(2, true), (0, true), (2, true)]
        [(0, true), (2, true), (0, true), (2, true)] [] false 0
        (level2_relator 4) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation2_14 :
    eval level2Generator (level3Relator 14) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 8 → Level2)
    (level2ChildWord i)) (level3Relator 14) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level2ChildWord (level3Relator 14)) =
      [(5, true), (7, false), (6, true), (7, true), (5, false), (6, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [] :=
      rewrite_step PresentedGroup.of (level2Relator 10)
        [] [(5, true), (7, false), (6, true)] [(6, false), (5, true), (7, false)] [(7, true), (5, false), (6, true)]
        [(5, true), (7, false), (6, true), (7, true), (5, false), (6, true)] [] false 0
        (level2_relator 10) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation2_15 :
    eval level2Generator (level3Relator 15) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 8 → Level2)
    (level2ChildWord i)) (level3Relator 15) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level2ChildWord (level3Relator 15)) =
      [(6, true), (5, false), (6, true), (5, false), (6, true), (5, false)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [] :=
      rewrite_step PresentedGroup.of (level2Relator 14)
        [] [(6, true), (5, false), (6, true)] [(5, true), (6, false), (5, true)] [(5, false), (6, true), (5, false)]
        [(6, true), (5, false), (6, true), (5, false), (6, true), (5, false)] [] false 0
        (level2_relator 14) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation2_16 :
    eval level2Generator (level3Relator 16) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 8 → Level2)
    (level2ChildWord i)) (level3Relator 16) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level2ChildWord (level3Relator 16)) =
      [(3, false), (3, false), (7, false), (0, false), (5, true), (4, false), (0, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [] :=
      rewrite_step PresentedGroup.of (level2Relator 17)
        [] [(3, false), (3, false), (7, false), (0, false)] [(0, false), (4, true), (5, false)] [(5, true), (4, false), (0, true)]
        [(3, false), (3, false), (7, false), (0, false), (5, true), (4, false), (0, true)] [] false 0
        (level2_relator 17) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation2_17 :
    eval level2Generator (level3Relator 17) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 8 → Level2)
    (level2ChildWord i)) (level3Relator 17) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level2ChildWord (level3Relator 17)) =
      [(0, false), (6, true), (7, false), (5, true), (0, false), (3, true), (0, true), (5, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [(0, false), (6, false), (7, false), (5, true), (0, false), (3, true), (0, true), (5, true)] :=
      rewrite_step PresentedGroup.of (level2Relator 0)
        [(0, false)] [(6, true)] [(6, false)] [(7, false), (5, true), (0, false), (3, true), (0, true), (5, true)]
        [(0, false), (6, true), (7, false), (5, true), (0, false), (3, true), (0, true), (5, true)] [(0, false), (6, false), (7, false), (5, true), (0, false), (3, true), (0, true), (5, true)] false 0
        (level2_relator 0) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [(0, false), (7, false), (5, true), (6, true), (0, false), (3, true), (0, true), (5, true)] :=
      rewrite_step PresentedGroup.of (level2Relator 9)
        [(0, false)] [(6, false), (7, false), (5, true)] [(7, false), (5, true), (6, true)] [(0, false), (3, true), (0, true), (5, true)]
        [(0, false), (6, false), (7, false), (5, true), (0, false), (3, true), (0, true), (5, true)] [(0, false), (7, false), (5, true), (6, true), (0, false), (3, true), (0, true), (5, true)] true 0
        (level2_relator 9) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [(0, false), (7, false), (5, true), (7, false), (5, true), (0, true)] :=
      rewrite_step PresentedGroup.of (level2Relator 18)
        [(0, false), (7, false), (5, true)] [(6, true), (0, false), (3, true), (0, true)] [(7, false), (5, true), (0, true), (5, false)] [(5, true)]
        [(0, false), (7, false), (5, true), (6, true), (0, false), (3, true), (0, true), (5, true)] [(0, false), (7, false), (5, true), (7, false), (5, true), (0, true)] false 3
        (level2_relator 18) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [] :=
      rewrite_step PresentedGroup.of (level2Relator 6)
        [(0, false)] [(7, false), (5, true)] [(5, false), (7, true)] [(7, false), (5, true), (0, true)]
        [(0, false), (7, false), (5, true), (7, false), (5, true), (0, true)] [] true 1
        (level2_relator 6) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation2_18 :
    eval level2Generator (level3Relator 18) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 8 → Level2)
    (level2ChildWord i)) (level3Relator 18) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level2ChildWord (level3Relator 18)) =
      [(7, false), (5, false), (6, true), (0, true), (3, false), (5, false), (3, true), (0, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [] :=
      rewrite_step PresentedGroup.of (level2Relator 20)
        [] [(7, false), (5, false), (6, true), (0, true)] [(0, false), (3, false), (5, true), (3, true)] [(3, false), (5, false), (3, true), (0, true)]
        [(7, false), (5, false), (6, true), (0, true), (3, false), (5, false), (3, true), (0, true)] [] false 0
        (level2_relator 20) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation2_19 :
    eval level2Generator (level3Relator 19) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 8 → Level2)
    (level2ChildWord i)) (level3Relator 19) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level2ChildWord (level3Relator 19)) =
      [(5, false), (6, true), (7, false), (3, false), (0, true), (3, false), (0, true), (2, true), (4, false), (0, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 8 → Level2) [] :=
      rewrite_step PresentedGroup.of (level2Relator 23)
        [] [(5, false), (6, true), (7, false), (3, false), (0, true)] [(0, false), (4, true), (2, false), (0, false), (3, true)] [(3, false), (0, true), (2, true), (4, false), (0, true)]
        [(5, false), (6, true), (7, false), (3, false), (0, true), (3, false), (0, true), (2, true), (4, false), (0, true)] [] false 0
        (level2_relator 23) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation3_0 :
    eval level3Generator (level4Relator 0) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 7 → Level3)
    (level3ChildWord i)) (level4Relator 0) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level3ChildWord (level4Relator 0)) =
      [(5, true), (5, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [] :=
      rewrite_step PresentedGroup.of (level3Relator 0)
        [] [(5, true)] [(5, false)] [(5, true)]
        [(5, true), (5, true)] [] false 0
        (level3_relator 0) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation3_1 :
    eval level3Generator (level4Relator 1) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 7 → Level3)
    (level3ChildWord i)) (level4Relator 1) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level3ChildWord (level4Relator 1)) =
      [(0, true), (0, true), (0, true), (0, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [(1, false), (0, true), (0, true)] :=
      rewrite_step PresentedGroup.of (level3Relator 2)
        [] [(0, true), (0, true)] [(1, false)] [(0, true), (0, true)]
        [(0, true), (0, true), (0, true), (0, true)] [(1, false), (0, true), (0, true)] false 0
        (level3_relator 2) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [(1, false), (1, false)] :=
      rewrite_step PresentedGroup.of (level3Relator 2)
        [(1, false)] [(0, true), (0, true)] [(1, false)] []
        [(1, false), (0, true), (0, true)] [(1, false), (1, false)] false 0
        (level3_relator 2) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [] :=
      rewrite_step PresentedGroup.of (level3Relator 1)
        [] [(1, false)] [(1, true)] [(1, false)]
        [(1, false), (1, false)] [] true 0
        (level3_relator 1) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation3_2 :
    eval level3Generator (level4Relator 2) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 7 → Level3)
    (level3ChildWord i)) (level4Relator 2) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level3ChildWord (level4Relator 2)) =
      [(4, true), (4, true), (4, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [] :=
      rewrite_step PresentedGroup.of (level3Relator 3)
        [] [(4, true), (4, true)] [(4, false)] [(4, true)]
        [(4, true), (4, true), (4, true)] [] false 0
        (level3_relator 3) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation3_3 :
    eval level3Generator (level4Relator 3) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 7 → Level3)
    (level3ChildWord i)) (level4Relator 3) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level3ChildWord (level4Relator 3)) =
      [(6, true), (6, true), (6, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [] :=
      rewrite_step PresentedGroup.of (level3Relator 4)
        [] [(6, true), (6, true)] [(6, false)] [(6, true)]
        [(6, true), (6, true), (6, true)] [] false 0
        (level3_relator 4) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation3_4 :
    eval level3Generator (level4Relator 4) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 7 → Level3)
    (level3ChildWord i)) (level4Relator 4) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level3ChildWord (level4Relator 4)) =
      [(4, true), (2, false), (3, false), (3, false)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [] :=
      rewrite_step PresentedGroup.of (level3Relator 5)
        [] [(4, true), (2, false)] [(3, true), (3, true)] [(3, false), (3, false)]
        [(4, true), (2, false), (3, false), (3, false)] [] false 0
        (level3_relator 5) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation3_5 :
    eval level3Generator (level4Relator 5) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 7 → Level3)
    (level3ChildWord i)) (level4Relator 5) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level3ChildWord (level4Relator 5)) =
      [(6, true), (4, false), (6, true), (4, false)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [] :=
      rewrite_step PresentedGroup.of (level3Relator 6)
        [] [(6, true), (4, false)] [(4, true), (6, false)] [(6, true), (4, false)]
        [(6, true), (4, false), (6, true), (4, false)] [] false 0
        (level3_relator 6) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation3_6 :
    eval level3Generator (level4Relator 6) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 7 → Level3)
    (level3ChildWord i)) (level4Relator 6) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level3ChildWord (level4Relator 6)) =
      [(3, true), (3, true), (3, true), (3, true), (3, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [(2, true), (4, false), (3, true), (3, true)] :=
      rewrite_step PresentedGroup.of (level3Relator 7)
        [] [(3, true), (3, true), (3, true)] [(2, true), (4, false)] [(3, true), (3, true)]
        [(3, true), (3, true), (3, true), (3, true), (3, true)] [(2, true), (4, false), (3, true), (3, true)] false 0
        (level3_relator 7) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [] :=
      rewrite_step PresentedGroup.of (level3Relator 5)
        [] [(2, true), (4, false)] [(3, false), (3, false)] [(3, true), (3, true)]
        [(2, true), (4, false), (3, true), (3, true)] [] true 2
        (level3_relator 5) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation3_7 :
    eval level3Generator (level4Relator 7) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 7 → Level3)
    (level3ChildWord i)) (level4Relator 7) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level3ChildWord (level4Relator 7)) =
      [(5, true), (6, false), (0, true), (0, true), (5, true), (3, false)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [(5, true), (6, false), (1, false), (5, true), (3, false)] :=
      rewrite_step PresentedGroup.of (level3Relator 2)
        [(5, true), (6, false)] [(0, true), (0, true)] [(1, false)] [(5, true), (3, false)]
        [(5, true), (6, false), (0, true), (0, true), (5, true), (3, false)] [(5, true), (6, false), (1, false), (5, true), (3, false)] false 0
        (level3_relator 2) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [(5, true), (6, false), (1, true), (5, true), (3, false)] :=
      rewrite_step PresentedGroup.of (level3Relator 1)
        [(5, true), (6, false)] [(1, false)] [(1, true)] [(5, true), (3, false)]
        [(5, true), (6, false), (1, false), (5, true), (3, false)] [(5, true), (6, false), (1, true), (5, true), (3, false)] true 0
        (level3_relator 1) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [] :=
      rewrite_step PresentedGroup.of (level3Relator 8)
        [] [(5, true), (6, false), (1, true)] [(3, true), (5, false)] [(5, true), (3, false)]
        [(5, true), (6, false), (1, true), (5, true), (3, false)] [] false 0
        (level3_relator 8) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation3_8 :
    eval level3Generator (level4Relator 8) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 7 → Level3)
    (level3ChildWord i)) (level4Relator 8) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level3ChildWord (level4Relator 8)) =
      [(5, true), (6, true), (0, true), (0, true), (4, false), (2, false)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [(5, true), (6, true), (1, false), (4, false), (2, false)] :=
      rewrite_step PresentedGroup.of (level3Relator 2)
        [(5, true), (6, true)] [(0, true), (0, true)] [(1, false)] [(4, false), (2, false)]
        [(5, true), (6, true), (0, true), (0, true), (4, false), (2, false)] [(5, true), (6, true), (1, false), (4, false), (2, false)] false 0
        (level3_relator 2) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [(5, true), (6, true), (1, true), (4, false), (2, false)] :=
      rewrite_step PresentedGroup.of (level3Relator 1)
        [(5, true), (6, true)] [(1, false)] [(1, true)] [(4, false), (2, false)]
        [(5, true), (6, true), (1, false), (4, false), (2, false)] [(5, true), (6, true), (1, true), (4, false), (2, false)] true 0
        (level3_relator 1) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [] :=
      rewrite_step PresentedGroup.of (level3Relator 9)
        [] [(5, true), (6, true), (1, true)] [(2, true), (4, true)] [(4, false), (2, false)]
        [(5, true), (6, true), (1, true), (4, false), (2, false)] [] false 0
        (level3_relator 9) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation3_9 :
    eval level3Generator (level4Relator 9) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 7 → Level3)
    (level3ChildWord i)) (level4Relator 9) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level3ChildWord (level4Relator 9)) =
      [(3, false), (0, true), (0, true), (6, true), (3, false), (5, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [(3, false), (1, false), (6, true), (3, false), (5, true)] :=
      rewrite_step PresentedGroup.of (level3Relator 2)
        [(3, false)] [(0, true), (0, true)] [(1, false)] [(6, true), (3, false), (5, true)]
        [(3, false), (0, true), (0, true), (6, true), (3, false), (5, true)] [(3, false), (1, false), (6, true), (3, false), (5, true)] false 0
        (level3_relator 2) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [(3, false), (1, false), (1, false), (3, true)] :=
      rewrite_step PresentedGroup.of (level3Relator 10)
        [(3, false), (1, false)] [(6, true), (3, false), (5, true)] [(1, false), (3, true)] []
        [(3, false), (1, false), (6, true), (3, false), (5, true)] [(3, false), (1, false), (1, false), (3, true)] false 2
        (level3_relator 10) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [] :=
      rewrite_step PresentedGroup.of (level3Relator 1)
        [(3, false)] [(1, false)] [(1, true)] [(1, false), (3, true)]
        [(3, false), (1, false), (1, false), (3, true)] [] true 0
        (level3_relator 1) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation3_10 :
    eval level3Generator (level4Relator 10) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 7 → Level3)
    (level3ChildWord i)) (level4Relator 10) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level3ChildWord (level4Relator 10)) =
      [(6, true), (4, true), (0, true), (0, true), (3, false), (4, true), (0, true), (0, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [(6, true), (4, true), (1, false), (3, false), (4, true), (0, true), (0, true)] :=
      rewrite_step PresentedGroup.of (level3Relator 2)
        [(6, true), (4, true)] [(0, true), (0, true)] [(1, false)] [(3, false), (4, true), (0, true), (0, true)]
        [(6, true), (4, true), (0, true), (0, true), (3, false), (4, true), (0, true), (0, true)] [(6, true), (4, true), (1, false), (3, false), (4, true), (0, true), (0, true)] false 0
        (level3_relator 2) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [(6, true), (4, true), (1, false), (3, false), (4, true), (1, false)] :=
      rewrite_step PresentedGroup.of (level3Relator 2)
        [(6, true), (4, true), (1, false), (3, false), (4, true)] [(0, true), (0, true)] [(1, false)] []
        [(6, true), (4, true), (1, false), (3, false), (4, true), (0, true), (0, true)] [(6, true), (4, true), (1, false), (3, false), (4, true), (1, false)] false 0
        (level3_relator 2) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [(6, true), (4, true), (1, true), (3, false), (4, true), (1, false)] :=
      rewrite_step PresentedGroup.of (level3Relator 1)
        [(6, true), (4, true)] [(1, false)] [(1, true)] [(3, false), (4, true), (1, false)]
        [(6, true), (4, true), (1, false), (3, false), (4, true), (1, false)] [(6, true), (4, true), (1, true), (3, false), (4, true), (1, false)] true 0
        (level3_relator 1) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [(1, false), (2, false), (3, false), (3, false), (4, true), (1, false)] :=
      rewrite_step PresentedGroup.of (level3Relator 13)
        [] [(6, true), (4, true), (1, true)] [(1, false), (2, false), (3, false)] [(3, false), (4, true), (1, false)]
        [(6, true), (4, true), (1, true), (3, false), (4, true), (1, false)] [(1, false), (2, false), (3, false), (3, false), (4, true), (1, false)] false 1
        (level3_relator 13) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [(1, false), (1, false)] :=
      rewrite_step PresentedGroup.of (level3Relator 5)
        [(1, false)] [(2, false), (3, false)] [(4, false), (3, true)] [(3, false), (4, true), (1, false)]
        [(1, false), (2, false), (3, false), (3, false), (4, true), (1, false)] [(1, false), (1, false)] false 1
        (level3_relator 5) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [] :=
      rewrite_step PresentedGroup.of (level3Relator 1)
        [] [(1, false)] [(1, true)] [(1, false)]
        [(1, false), (1, false)] [] true 0
        (level3_relator 1) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation3_11 :
    eval level3Generator (level4Relator 11) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 7 → Level3)
    (level3ChildWord i)) (level4Relator 11) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level3ChildWord (level4Relator 11)) =
      [(4, true), (6, false), (5, true), (4, true), (6, false), (5, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [(4, true), (6, false), (4, true), (6, false)] :=
      rewrite_step PresentedGroup.of (level3Relator 14)
        [(4, true), (6, false)] [(5, true), (4, true), (6, false)] [(4, true), (6, false), (5, false)] [(5, true)]
        [(4, true), (6, false), (5, true), (4, true), (6, false), (5, true)] [(4, true), (6, false), (4, true), (6, false)] false 5
        (level3_relator 14) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [] :=
      rewrite_step PresentedGroup.of (level3Relator 6)
        [] [(4, true), (6, false)] [(6, true), (4, false)] [(4, true), (6, false)]
        [(4, true), (6, false), (4, true), (6, false)] [] true 0
        (level3_relator 6) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation3_12 :
    eval level3Generator (level4Relator 12) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 7 → Level3)
    (level3ChildWord i)) (level4Relator 12) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level3ChildWord (level4Relator 12)) =
      [(4, false), (6, true), (5, true), (0, true), (0, true), (3, false), (2, false)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [(4, false), (6, true), (5, true), (1, false), (3, false), (2, false)] :=
      rewrite_step PresentedGroup.of (level3Relator 2)
        [(4, false), (6, true), (5, true)] [(0, true), (0, true)] [(1, false)] [(3, false), (2, false)]
        [(4, false), (6, true), (5, true), (0, true), (0, true), (3, false), (2, false)] [(4, false), (6, true), (5, true), (1, false), (3, false), (2, false)] false 0
        (level3_relator 2) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [(4, false), (6, true), (5, true), (1, true), (3, false), (2, false)] :=
      rewrite_step PresentedGroup.of (level3Relator 1)
        [(4, false), (6, true), (5, true)] [(1, false)] [(1, true)] [(3, false), (2, false)]
        [(4, false), (6, true), (5, true), (1, false), (3, false), (2, false)] [(4, false), (6, true), (5, true), (1, true), (3, false), (2, false)] true 0
        (level3_relator 1) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [(4, false), (6, true), (4, false), (6, true)] :=
      rewrite_step PresentedGroup.of (level3Relator 11)
        [(4, false), (6, true)] [(5, true), (1, true), (3, false)] [(4, false), (6, true), (2, true)] [(2, false)]
        [(4, false), (6, true), (5, true), (1, true), (3, false), (2, false)] [(4, false), (6, true), (4, false), (6, true)] false 2
        (level3_relator 11) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [] :=
      rewrite_step PresentedGroup.of (level3Relator 6)
        [] [(4, false), (6, true)] [(6, false), (4, true)] [(4, false), (6, true)]
        [(4, false), (6, true), (4, false), (6, true)] [] false 1
        (level3_relator 6) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation3_13 :
    eval level3Generator (level4Relator 13) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 7 → Level3)
    (level3ChildWord i)) (level4Relator 13) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level3ChildWord (level4Relator 13)) =
      [(2, true), (3, true), (0, true), (0, true), (2, true), (3, true), (0, true), (0, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [(2, true), (3, true), (1, false), (2, true), (3, true), (0, true), (0, true)] :=
      rewrite_step PresentedGroup.of (level3Relator 2)
        [(2, true), (3, true)] [(0, true), (0, true)] [(1, false)] [(2, true), (3, true), (0, true), (0, true)]
        [(2, true), (3, true), (0, true), (0, true), (2, true), (3, true), (0, true), (0, true)] [(2, true), (3, true), (1, false), (2, true), (3, true), (0, true), (0, true)] false 0
        (level3_relator 2) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [(2, true), (3, true), (1, false), (2, true), (3, true), (1, false)] :=
      rewrite_step PresentedGroup.of (level3Relator 2)
        [(2, true), (3, true), (1, false), (2, true), (3, true)] [(0, true), (0, true)] [(1, false)] []
        [(2, true), (3, true), (1, false), (2, true), (3, true), (0, true), (0, true)] [(2, true), (3, true), (1, false), (2, true), (3, true), (1, false)] false 0
        (level3_relator 2) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [(6, false), (4, true), (5, true), (2, true), (3, true), (1, false)] :=
      rewrite_step PresentedGroup.of (level3Relator 11)
        [] [(2, true), (3, true), (1, false)] [(6, false), (4, true), (5, true)] [(2, true), (3, true), (1, false)]
        [(2, true), (3, true), (1, false), (2, true), (3, true), (1, false)] [(6, false), (4, true), (5, true), (2, true), (3, true), (1, false)] true 0
        (level3_relator 11) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [(1, false), (1, false)] :=
      rewrite_step PresentedGroup.of (level3Relator 12)
        [] [(6, false), (4, true), (5, true)] [(1, false), (3, false), (2, false)] [(2, true), (3, true), (1, false)]
        [(6, false), (4, true), (5, true), (2, true), (3, true), (1, false)] [(1, false), (1, false)] false 1
        (level3_relator 12) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [] :=
      rewrite_step PresentedGroup.of (level3Relator 1)
        [] [(1, false)] [(1, true)] [(1, false)]
        [(1, false), (1, false)] [] true 0
        (level3_relator 1) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation3_14 :
    eval level3Generator (level4Relator 14) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 7 → Level3)
    (level3ChildWord i)) (level4Relator 14) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level3ChildWord (level4Relator 14)) =
      [(5, true), (4, false), (5, true), (4, false), (5, true), (4, false)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 7 → Level3) [] :=
      rewrite_step PresentedGroup.of (level3Relator 15)
        [] [(5, true), (4, false), (5, true)] [(4, true), (5, false), (4, true)] [(4, false), (5, true), (4, false)]
        [(5, true), (4, false), (5, true), (4, false), (5, true), (4, false)] [] false 0
        (level3_relator 15) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation4_0 :
    eval level4Generator (level5Relator 0) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 6 → Level4)
    (level4ChildWord i)) (level5Relator 0) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level4ChildWord (level5Relator 0)) =
      [(4, true), (4, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 6 → Level4) [] :=
      rewrite_step PresentedGroup.of (level4Relator 0)
        [] [(4, true)] [(4, false)] [(4, true)]
        [(4, true), (4, true)] [] false 0
        (level4_relator 0) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation4_1 :
    eval level4Generator (level5Relator 1) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 6 → Level4)
    (level4ChildWord i)) (level5Relator 1) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level4ChildWord (level5Relator 1)) =
      [(3, true), (3, true), (3, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 6 → Level4) [] :=
      rewrite_step PresentedGroup.of (level4Relator 2)
        [] [(3, true), (3, true)] [(3, false)] [(3, true)]
        [(3, true), (3, true), (3, true)] [] false 0
        (level4_relator 2) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation4_2 :
    eval level4Generator (level5Relator 2) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 6 → Level4)
    (level4ChildWord i)) (level5Relator 2) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level4ChildWord (level5Relator 2)) =
      [(5, true), (5, true), (5, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 6 → Level4) [] :=
      rewrite_step PresentedGroup.of (level4Relator 3)
        [] [(5, true), (5, true)] [(5, false)] [(5, true)]
        [(5, true), (5, true), (5, true)] [] false 0
        (level4_relator 3) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation4_3 :
    eval level4Generator (level5Relator 3) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 6 → Level4)
    (level4ChildWord i)) (level5Relator 3) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level4ChildWord (level5Relator 3)) =
      [(5, true), (3, false), (5, true), (3, false)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 6 → Level4) [] :=
      rewrite_step PresentedGroup.of (level4Relator 5)
        [] [(5, true), (3, false)] [(3, true), (5, false)] [(5, true), (3, false)]
        [(5, true), (3, false), (5, true), (3, false)] [] false 0
        (level4_relator 5) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation4_4 :
    eval level4Generator (level5Relator 4) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 6 → Level4)
    (level4ChildWord i)) (level5Relator 4) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level4ChildWord (level5Relator 4)) =
      [(5, false), (3, true), (4, true), (5, false), (3, true), (4, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 6 → Level4) [(5, false), (3, true), (4, false), (5, false), (3, true), (4, true)] :=
      rewrite_step PresentedGroup.of (level4Relator 0)
        [(5, false), (3, true)] [(4, true)] [(4, false)] [(5, false), (3, true), (4, true)]
        [(5, false), (3, true), (4, true), (5, false), (3, true), (4, true)] [(5, false), (3, true), (4, false), (5, false), (3, true), (4, true)] false 0
        (level4_relator 0) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 6 → Level4) [(5, false), (3, true), (0, true), (2, false), (1, false), (4, true)] :=
      rewrite_step PresentedGroup.of (level4Relator 12)
        [(5, false), (3, true)] [(4, false), (5, false), (3, true)] [(0, true), (2, false), (1, false)] [(4, true)]
        [(5, false), (3, true), (4, false), (5, false), (3, true), (4, true)] [(5, false), (3, true), (0, true), (2, false), (1, false), (4, true)] true 3
        (level4_relator 12) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 6 → Level4) [(5, false), (5, false), (0, false), (3, false), (1, false), (4, true)] :=
      rewrite_step PresentedGroup.of (level4Relator 10)
        [(5, false)] [(3, true), (0, true), (2, false)] [(5, false), (0, false), (3, false)] [(1, false), (4, true)]
        [(5, false), (3, true), (0, true), (2, false), (1, false), (4, true)] [(5, false), (5, false), (0, false), (3, false), (1, false), (4, true)] false 1
        (level4_relator 10) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 6 → Level4) [(5, true), (0, false), (3, false), (1, false), (4, true)] :=
      rewrite_step PresentedGroup.of (level4Relator 3)
        [] [(5, false), (5, false)] [(5, true)] [(0, false), (3, false), (1, false), (4, true)]
        [(5, false), (5, false), (0, false), (3, false), (1, false), (4, true)] [(5, true), (0, false), (3, false), (1, false), (4, true)] true 0
        (level4_relator 3) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 6 → Level4) [(5, true), (0, false), (0, false), (5, false)] :=
      rewrite_step PresentedGroup.of (level4Relator 8)
        [(5, true), (0, false)] [(3, false), (1, false), (4, true)] [(0, false), (5, false)] []
        [(5, true), (0, false), (3, false), (1, false), (4, true)] [(5, true), (0, false), (0, false), (5, false)] false 3
        (level4_relator 8) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 6 → Level4) [] :=
      rewrite_step PresentedGroup.of (level4Relator 1)
        [(5, true)] [(0, false)] [(0, true)] [(0, false), (5, false)]
        [(5, true), (0, false), (0, false), (5, false)] [] true 0
        (level4_relator 1) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation4_5 :
    eval level4Generator (level5Relator 5) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 6 → Level4)
    (level4ChildWord i)) (level5Relator 5) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level4ChildWord (level5Relator 5)) =
      [(3, true), (5, false), (4, true), (5, true), (3, false), (4, true)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 6 → Level4) [(4, false), (5, true), (3, false), (5, true), (3, false), (4, true)] :=
      rewrite_step PresentedGroup.of (level4Relator 11)
        [] [(3, true), (5, false), (4, true)] [(4, false), (5, true), (3, false)] [(5, true), (3, false), (4, true)]
        [(3, true), (5, false), (4, true), (5, true), (3, false), (4, true)] [(4, false), (5, true), (3, false), (5, true), (3, false), (4, true)] false 0
        (level4_relator 11) (by decide) (by decide) (by decide)
    _ = eval (PresentedGroup.of : Fin 6 → Level4) [] :=
      rewrite_step PresentedGroup.of (level4Relator 5)
        [(4, false)] [(5, true), (3, false)] [(3, true), (5, false)] [(5, true), (3, false), (4, true)]
        [(4, false), (5, true), (3, false), (5, true), (3, false), (4, true)] [] false 0
        (level4_relator 5) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

private theorem relation4_6 :
    eval level4Generator (level5Relator 6) = 1 := by
  change eval (fun i => eval (PresentedGroup.of : Fin 6 → Level4)
    (level4ChildWord i)) (level5Relator 6) = 1
  rw [← eval_substitute, ← eval_reduce]
  have hs : reduce (substitute level4ChildWord (level5Relator 6)) =
      [(4, true), (3, false), (4, true), (3, false), (4, true), (3, false)] := by decide
  rw [hs]
  calc
    _ = eval (PresentedGroup.of : Fin 6 → Level4) [] :=
      rewrite_step PresentedGroup.of (level4Relator 14)
        [] [(4, true), (3, false), (4, true)] [(3, true), (4, false), (3, true)] [(3, false), (4, true), (3, false)]
        [(4, true), (3, false), (4, true), (3, false), (4, true), (3, false)] [] false 0
        (level4_relator 14) (by decide) (by decide) (by decide)
    _ = 1 := eval_nil _

/-- All next-stage relations hold in the parent abstract presentation. -/
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
  · exact relation1_12
  · exact relation1_13
  · exact relation1_14
  · exact relation1_15
  · exact relation1_16
  · exact relation1_17
  · exact relation1_18
  · exact relation1_19
  · exact relation1_20
  · exact relation1_21
  · exact relation1_22
  · exact relation1_23
  · exact relation1_24
  · exact relation1_25
  · exact relation1_26
  · exact relation1_27
  · exact relation1_28

/-- All next-stage relations hold in the parent abstract presentation. -/
theorem liftedRelations23 : LiftedRelations23 := by
  intro i
  fin_cases i
  · exact relation2_0
  · exact relation2_1
  · exact relation2_2
  · exact relation2_3
  · exact relation2_4
  · exact relation2_5
  · exact relation2_6
  · exact relation2_7
  · exact relation2_8
  · exact relation2_9
  · exact relation2_10
  · exact relation2_11
  · exact relation2_12
  · exact relation2_13
  · exact relation2_14
  · exact relation2_15
  · exact relation2_16
  · exact relation2_17
  · exact relation2_18
  · exact relation2_19

/-- All next-stage relations hold in the parent abstract presentation. -/
theorem liftedRelations34 : LiftedRelations34 := by
  intro i
  fin_cases i
  · exact relation3_0
  · exact relation3_1
  · exact relation3_2
  · exact relation3_3
  · exact relation3_4
  · exact relation3_5
  · exact relation3_6
  · exact relation3_7
  · exact relation3_8
  · exact relation3_9
  · exact relation3_10
  · exact relation3_11
  · exact relation3_12
  · exact relation3_13
  · exact relation3_14

/-- All next-stage relations hold in the parent abstract presentation. -/
theorem liftedRelations45 : LiftedRelations45 := by
  intro i
  fin_cases i
  · exact relation4_0
  · exact relation4_1
  · exact relation4_2
  · exact relation4_3
  · exact relation4_4
  · exact relation4_5
  · exact relation4_6

end Janko4.Cardinality.QuotientCount.UpperBound.PresentationBound.StabilizerChain
