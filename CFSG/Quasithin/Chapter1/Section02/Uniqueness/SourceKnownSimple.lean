module

public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.Source
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# Known-simple source assembly for 1.2.7

The conditional uniqueness deduction in `Uniqueness.Source` keeps the genuine
Theorems A and C as explicit universal inputs.  The completed known-simple
A/C source is already available, so this leaf discharges those callbacks and
exports the literal Chapter 1 conclusion used by downstream source consumers.

Source: Aschbacher--Smith, Theorem 1.2.7, printed p.506.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02
universe u

variable {G : Type u} [Group G] [Finite G]

/-- Theorem 1.2.7 for the complete `KnownSimple` catalogue. -/
theorem nonsolvable_uniqueness_knownSimple
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {L : Subgroup G}
    (hL : L ∈ LStar G (T : Subgroup G)) :
    NonsolvableUniquenessConclusion T L :=
  nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    hG T hL

end CFSG.Quasithin.Chapter1.Section02
