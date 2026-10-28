module

public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassA.CheckPart00
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassA.CheckPart01
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassA.CheckPart02
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassA.CheckPart03
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassA.CheckPart04
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassA.CheckPart05
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassA.CheckPart06
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassA.CheckPart07
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassA.CheckPart08
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassA.CheckPart09
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassA.CheckPart10
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassA.CheckPart11
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassA.CheckPart12
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassA.CheckPart13
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassA.CheckPart14
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassA.CheckPart15
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassA.CheckPart16
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassA.CheckPart17
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassA.CheckPart18
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassA.CheckPart19
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassA.CheckPart20
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassA.CheckPart21
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassA.CheckPart22
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassA.CheckPart23
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassA.CheckPart24
import Mathlib.Tactic.FinCases

/-!
# Complete first-class certificate

The 400 checked blocks cover all 24990 rows. The final blocks wrap modulo
24990; this duplicates some checks and leaves no uncovered final interval.
Each block contains both four-point generator edges and both source-pair tests.
Source: `Held/Model/Source/HeG1-P1.M` and the retained degree-2058 tables.
-/

namespace Held.Realization.MarkedConjugacy.NormalizedPairs.ClassA

private theorem allParts (q : Fin 25) (r : Fin 16) :
    checkBlock (16*q.val+r.val) = true := by
  fin_cases q
  · exact part00 r
  · exact part01 r
  · exact part02 r
  · exact part03 r
  · exact part04 r
  · exact part05 r
  · exact part06 r
  · exact part07 r
  · exact part08 r
  · exact part09 r
  · exact part10 r
  · exact part11 r
  · exact part12 r
  · exact part13 r
  · exact part14 r
  · exact part15 r
  · exact part16 r
  · exact part17 r
  · exact part18 r
  · exact part19 r
  · exact part20 r
  · exact part21 r
  · exact part22 r
  · exact part23 r
  · exact part24 r

public theorem allBlocks (b : Fin 400) : checkBlock b.val = true := by
  have hq : b.val / 16 < 25 := by omega
  have h := allParts ⟨b.val / 16, hq⟩ ⟨b.val % 16, Nat.mod_lt _ (by decide)⟩
  have hb : 16 * (b.val / 16) + b.val % 16 = b.val := by omega
  simpa only [hb] using h

end Held.Realization.MarkedConjugacy.NormalizedPairs.ClassA
