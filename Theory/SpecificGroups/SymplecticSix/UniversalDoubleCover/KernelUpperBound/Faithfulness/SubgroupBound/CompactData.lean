module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.Faithfulness.SubgroupBound.SchreierData

/-!
# Eight retained generators for the subgroup calculation

These are the eight edge indices and 51 relators left after 64 elementary
single-occurrence eliminations of the Schreier presentation. The elimination
trace is retained in `source/schreier.json`. This module publishes only the
literal data: their validity in `RawPresentation` and generation of that group
remain proof obligations, independent of bounding `CompactPresentation`.

Source: ATLAS `S62G1-P1.M`, via the reproducible extraction in `source/`.
-/

@[expose] public section
namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.Faithfulness.SubgroupBound
open Subgroup.CosetWordCertificate

def compactIndex (i : Fin 8) : Edge :=
  match i.val with
  | 0 => (4, true)
  | 1 => (19, false)
  | 2 => (21, false)
  | 3 => (22, true)
  | 4 => (25, false)
  | 5 => (33, false)
  | 6 => (34, false)
  | _ => (34, true)

def compactRelator (i : Fin 51) : Word (Fin 8) :=
  match i.val with
  | 0 => [(6, false), (6, false)]
  | 1 => [(4, false), (4, false)]
  | 2 => [(2, false), (2, false)]
  | 3 => [(1, false), (1, false)]
  | 4 => [(7, false), (0, false), (0, false)]
  | 5 => [(6, false), (2, false), (6, false), (2, false)]
  | 6 => [(4, false), (2, false), (4, false), (2, false)]
  | 7 => [(4, false), (1, true), (4, false), (1, true)]
  | 8 => [(2, false), (1, false), (2, false), (1, false)]
  | 9 => [(7, false), (1, false), (7, true), (5, true), (2, false), (5, false)]
  | 10 => [(7, false), (6, false), (7, true), (3, true), (7, false), (1, true), (7, true), (3, false)]
  | 11 => [(7, false), (1, false), (7, true), (3, false), (1, false), (4, false), (0, true), (2, true)]
  | 12 => [(7, false), (1, false), (7, true), (2, false), (7, false), (1, false), (7, true), (2, false)]
  | 13 => [(7, false), (1, false), (7, true), (4, true), (7, false), (1, false), (7, true), (4, true)]
  | 14 => [(7, false), (1, true), (2, true), (5, true), (0, true), (2, true), (3, true), (4, false)]
  | 15 => [(4, false), (3, false), (2, false), (3, true), (4, false), (3, false), (2, false), (3, true)]
  | 16 => [(5, false), (4, true), (3, false), (2, false), (1, false), (0, false), (0, false), (4, true), (0, false)]
  | 17 => [(7, false), (6, false), (7, true), (3, false), (1, false), (3, true), (7, false), (1, true), (0, true), (1, true)]
  | 18 => [(7, false), (6, false), (7, true), (1, false), (2, false), (0, false), (4, false), (0, true), (2, true), (1, true)]
  | 19 => [(7, false), (6, false), (7, true), (0, false), (5, false), (7, false), (6, false), (7, true), (5, true), (0, true)]
  | 20 => [(7, false), (0, false), (4, false), (0, true), (7, true), (5, true), (0, true), (1, true), (0, false), (5, false)]
  | 21 => [(5, false), (3, false), (1, false), (3, true), (5, true), (0, true), (3, false), (1, false), (3, true), (0, false)]
  | 22 => [(5, false), (4, true), (3, false), (3, false), (2, false), (0, false), (5, false), (4, true), (3, false), (2, false), (0, false)]
  | 23 => [(7, false), (1, false), (7, true), (3, false), (1, false), (2, false), (0, false), (4, false), (0, true), (2, true), (1, true), (3, true)]
  | 24 => [(7, false), (0, false), (4, true), (0, false), (2, false), (5, false), (7, false), (0, false), (4, true), (0, false), (2, false), (5, false)]
  | 25 => [(6, false), (0, false), (4, false), (0, true), (6, false), (0, false), (4, false), (0, true), (6, false), (0, false), (4, false), (0, true)]
  | 26 => [(6, false), (0, false), (4, true), (0, true), (2, true), (0, true), (1, false), (0, false), (2, false), (0, false), (4, false), (0, true)]
  | 27 => [(5, false), (4, false), (5, true), (0, true), (2, false), (0, false), (5, false), (4, false), (5, true), (0, true), (2, false), (0, false)]
  | 28 => [(4, false), (0, true), (0, true), (2, false), (0, false), (0, false), (4, false), (0, true), (0, true), (2, false), (0, false), (0, false)]
  | 29 => [(4, false), (0, true), (0, true), (1, true), (0, false), (0, false), (4, false), (0, true), (0, true), (1, true), (0, false), (0, false)]
  | 30 => [(4, false), (0, true), (2, true), (0, false), (4, false), (0, true), (2, true), (0, false), (4, false), (0, true), (2, true), (0, false)]
  | 31 => [(7, false), (1, false), (7, true), (3, false), (1, false), (3, true), (7, false), (1, true), (7, true), (4, false), (0, true), (2, true), (0, false), (4, true)]
  | 32 => [(5, false), (3, false), (1, false), (3, true), (5, true), (2, true), (0, false), (4, true), (0, true), (1, true), (0, false), (4, false), (0, true), (2, false)]
  | 33 => [(5, false), (3, false), (1, true), (3, true), (4, false), (3, false), (1, false), (3, true), (5, true), (2, true), (0, false), (4, false), (0, true), (2, false)]
  | 34 => [(5, false), (4, true), (3, false), (2, false), (3, true), (4, false), (5, true), (0, true), (2, true), (3, true), (4, false), (3, false), (2, false), (0, false)]
  | 35 => [(7, false), (6, false), (0, false), (4, true), (0, true), (2, true), (0, false), (0, false), (4, false), (0, true), (2, false), (5, false), (3, false), (1, true), (3, true)]
  | 36 => [(7, false), (6, false), (7, true), (3, false), (1, false), (3, true), (5, true), (0, true), (1, true), (3, true), (7, false), (1, true), (7, true), (5, true), (0, true)]
  | 37 => [(7, false), (6, false), (0, false), (4, true), (0, true), (2, false), (0, false), (4, false), (0, true), (6, true), (7, true), (5, true), (0, true), (2, false), (0, false), (5, false)]
  | 38 => [(7, false), (1, true), (0, false), (0, false), (4, false), (0, true), (2, false), (0, false), (4, true), (0, true), (0, true), (1, false), (7, true), (3, false), (1, true), (3, true)]
  | 39 => [(5, false), (3, false), (1, false), (3, true), (5, true), (0, false), (4, false), (0, true), (5, false), (3, false), (1, false), (3, true), (5, true), (0, false), (4, false), (0, true)]
  | 40 => [(7, false), (6, false), (0, false), (4, true), (2, false), (0, true), (3, false), (1, false), (3, true), (4, false), (5, true), (0, true), (2, true), (3, true), (4, false), (5, true), (0, true), (2, true)]
  | 41 => [(7, false), (6, false), (7, true), (3, false), (1, true), (3, true), (7, false), (6, false), (7, true), (3, false), (1, true), (3, true), (7, false), (6, false), (7, true), (3, false), (1, true), (3, true)]
  | 42 => [(7, false), (1, false), (7, true), (3, false), (3, false), (1, false), (2, true), (3, true), (4, false), (7, false), (1, false), (7, true), (3, false), (3, false), (1, false), (2, true), (3, true), (4, false)]
  | 43 => [(7, false), (1, false), (7, true), (3, false), (1, true), (3, true), (7, false), (1, false), (7, true), (3, false), (1, true), (3, true), (7, false), (1, false), (7, true), (3, false), (1, true), (3, true)]
  | 44 => [(5, false), (3, false), (1, false), (3, true), (5, true), (2, false), (5, false), (3, false), (1, false), (3, true), (5, true), (2, false), (5, false), (3, false), (1, false), (3, true), (5, true), (2, false)]
  | 45 => [(7, false), (6, false), (2, true), (1, false), (7, true), (5, true), (0, true), (1, false), (0, false), (0, false), (4, false), (0, true), (5, false), (3, false), (1, true), (3, true), (5, true), (0, true), (0, true)]
  | 46 => [(7, false), (6, false), (0, false), (4, false), (0, true), (6, true), (7, true), (3, false), (1, true), (3, true), (7, false), (6, false), (0, false), (4, false), (0, true), (6, true), (7, true), (3, false), (1, true), (3, true)]
  | 47 => [(7, false), (6, false), (7, true), (3, false), (1, false), (3, true), (7, false), (6, true), (7, true), (1, false), (7, false), (6, false), (7, true), (3, false), (1, false), (3, true), (7, false), (6, true), (7, true), (1, false)]
  | 48 => [(7, false), (6, false), (7, true), (3, false), (1, false), (3, true), (7, false), (1, false), (7, true), (3, false), (1, true), (3, true), (7, false), (6, false), (7, true), (3, false), (1, false), (3, true), (7, false), (1, false), (7, true), (3, false), (1, true), (3, true)]
  | 49 => [(7, false), (6, false), (7, true), (3, false), (1, false), (3, true), (5, true), (2, true), (5, false), (3, false), (1, true), (3, true), (7, false), (6, false), (7, true), (3, false), (1, false), (3, true), (5, true), (2, true), (5, false), (3, false), (1, true), (3, true)]
  | _ => [(5, false), (4, true), (3, false), (2, false), (0, false), (5, false), (4, true), (3, false), (2, false), (0, false), (5, false), (4, true), (3, false), (2, false), (0, false), (5, false), (4, true), (3, false), (2, false), (0, false), (5, false), (4, true), (3, false), (2, false), (0, false), (5, false), (4, true), (3, false), (2, false), (0, false), (5, false), (4, true), (3, false), (2, false), (0, false)]

/-- A candidate smaller presentation. No identification or order is assumed. -/
def CompactPresentation :=
  PresentedGroup (Set.range (fun i => FreeGroup.mk (compactRelator i)))

instance : Group CompactPresentation := inferInstanceAs (Group (PresentedGroup _))

/-- The prescribed images of the eight retained edge generators. -/
def compactImage (i : Fin 8) : RawPresentation := PresentedGroup.of (compactIndex i)

end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.Faithfulness.SubgroupBound
