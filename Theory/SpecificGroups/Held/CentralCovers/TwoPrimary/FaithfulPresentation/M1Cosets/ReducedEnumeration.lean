module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.ReducedData
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

/-!
# Checked residual coset enumeration

Each intermediate fact is an equality modulo the actual subgroup. Defining
edges use literal representative words; scans cancel previously proved paths
from a relator loop; mergers compose empty-word equalities. The final loops
show that every one of the 17 generators belongs to the subgroup containing
the first three, provided all 49 displayed words evaluate to one.

The certificate is generated from the untrusted retained Felsch trace by
`source/emit_enumeration.py`. Lean checks ordinary proof terms with the sound
rules from `Theory.GroupTheory.CosetEnumeration`.
-/

namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.Reduced
open Theory.GroupTheory.CosetEnumeration
variable {G : Type*} [Group G] {g : Fin 17 → G} {H : Subgroup G}

private theorem fact0 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(0, true)] 0).Valid g H input :=
  Fact.valid_subgroup h (0, true) (by decide +kernel)

private theorem fact1 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [] 0).Valid g H input :=
  Fact.valid_refl g H input 0

private theorem fact3 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(0, false)] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [(0, true)], 0⟩) (fact0 h)

private theorem fact4 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(1, true)] 0).Valid g H input :=
  Fact.valid_subgroup h (1, true) (by decide +kernel)

private theorem fact6 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(1, false)] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [(1, true)], 0⟩) (fact4 h)

private theorem fact7 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(2, true)] 0).Valid g H input :=
  Fact.valid_subgroup h (2, true) (by decide +kernel)

private theorem fact9 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(2, false)] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [(2, true)], 0⟩) (fact7 h)

private theorem fact12 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(0, true), (2, true)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(0, true)], 0⟩) (k := ⟨0, [(2, true)], 0⟩) (fact0 h) (fact7 h) rfl

private theorem fact14 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(0, true), (2, true), (8, true)] 0).Valid g H input :=
  Fact.valid_relator h 0 (relator 4)
    (Array.mem_ofFn.mpr ⟨4, rfl⟩) true 0

private theorem fact15 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(8, true)] 0).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(0, true), (2, true)], 0⟩) (k := ⟨0, [(0, true), (2, true), (8, true)], 0⟩) (fact12 h) (fact14 h) rfl [(8, true)] rfl

private theorem fact16 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(8, false)] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [(8, true)], 0⟩) (fact15 h)

private theorem fact17 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(8, false)] 0).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [], 0⟩) (k := ⟨0, [(8, false)], 0⟩) (fact1 h) (fact16 h) rfl [(8, false)] rfl

private theorem fact18 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(8, true)] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [(8, false)], 0⟩) (fact17 h)

private theorem fact20 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(8, false)] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [(8, true)], 0⟩) (fact18 h)

private theorem fact21 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(3, true)] 1).Valid g H input :=
  Fact.valid_define g H input 0 (3, true) 1 (by decide +kernel)

private theorem fact25 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(3, false)] 2).Valid g H input :=
  Fact.valid_define g H input 0 (3, false) 2 (by decide +kernel)

private theorem fact28 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 2 [(3, true)] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [(3, false)], 2⟩) (fact25 h)

private theorem fact32 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(0, true), (8, true)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(0, true)], 0⟩) (k := ⟨0, [(8, true)], 0⟩) (fact0 h) (fact18 h) rfl

private theorem fact34 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(3, false), (6, false), (8, false), (0, false)] 0).Valid g H input :=
  Fact.valid_relator h 0 (relator 13)
    (Array.mem_ofFn.mpr ⟨13, rfl⟩) false 2

private theorem fact35 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 2 [(6, false), (8, false), (0, false)] 0).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(3, false)], 2⟩) (k := ⟨0, [(3, false), (6, false), (8, false), (0, false)], 0⟩) (fact25 h) (fact34 h) rfl [(6, false), (8, false), (0, false)] rfl

private theorem fact36 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(0, true), (8, true), (6, true)] 2).Valid g H input :=
  Fact.valid_reverse (f := ⟨2, [(6, false), (8, false), (0, false)], 0⟩) (fact35 h)

private theorem fact37 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(6, true)] 2).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(0, true), (8, true)], 0⟩) (k := ⟨0, [(0, true), (8, true), (6, true)], 2⟩) (fact32 h) (fact36 h) rfl [(6, true)] rfl

private theorem fact38 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 2 [(6, false)] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [(6, true)], 2⟩) (fact37 h)

private theorem fact40 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(6, true)] 2).Valid g H input :=
  Fact.valid_reverse (f := ⟨2, [(6, false)], 0⟩) (fact38 h)

private theorem fact41 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(4, true)] 3).Valid g H input :=
  Fact.valid_define g H input 0 (4, true) 3 (by decide +kernel)

private theorem fact43 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 3 [] 3).Valid g H input :=
  Fact.valid_refl g H input 3

private theorem fact44 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 3 [(4, false)] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [(4, true)], 3⟩) (fact41 h)

private theorem fact45 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(4, false)] 4).Valid g H input :=
  Fact.valid_define g H input 0 (4, false) 4 (by decide +kernel)

private theorem fact47 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [] 4).Valid g H input :=
  Fact.valid_refl g H input 4

private theorem fact48 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(4, true)] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [(4, false)], 4⟩) (fact45 h)

private theorem fact52 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(8, false), (1, true)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(8, false)], 0⟩) (k := ⟨0, [(1, true)], 0⟩) (fact20 h) (fact4 h) rfl

private theorem fact54 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(8, false), (1, true), (4, true)] 3).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(8, false), (1, true)], 0⟩) (k := ⟨0, [(4, true)], 3⟩) (fact52 h) (fact41 h) rfl

private theorem fact56 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(4, false), (9, false), (4, false), (1, false), (8, true)] 0).Valid g H input :=
  Fact.valid_relator h 0 (relator 21)
    (Array.mem_ofFn.mpr ⟨21, rfl⟩) false 4

private theorem fact57 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(9, false), (4, false), (1, false), (8, true)] 0).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(4, false)], 4⟩) (k := ⟨0, [(4, false), (9, false), (4, false), (1, false), (8, true)], 0⟩) (fact45 h) (fact56 h) rfl [(9, false), (4, false), (1, false), (8, true)] rfl

private theorem fact58 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(8, false), (1, true), (4, true), (9, true)] 4).Valid g H input :=
  Fact.valid_reverse (f := ⟨4, [(9, false), (4, false), (1, false), (8, true)], 0⟩) (fact57 h)

private theorem fact59 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 3 [(9, true)] 4).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(8, false), (1, true), (4, true)], 3⟩) (k := ⟨0, [(8, false), (1, true), (4, true), (9, true)], 4⟩) (fact54 h) (fact58 h) rfl [(9, true)] rfl

private theorem fact60 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(9, false)] 3).Valid g H input :=
  Fact.valid_reverse (f := ⟨3, [(9, true)], 4⟩) (fact59 h)

private theorem fact62 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 3 [(9, true)] 4).Valid g H input :=
  Fact.valid_reverse (f := ⟨4, [(9, false)], 3⟩) (fact60 h)

private theorem fact63 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(5, true)] 5).Valid g H input :=
  Fact.valid_define g H input 0 (5, true) 5 (by decide +kernel)

private theorem fact65 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 5 [] 5).Valid g H input :=
  Fact.valid_refl g H input 5

private theorem fact66 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 5 [(5, false)] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [(5, true)], 5⟩) (fact63 h)

private theorem fact67 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(5, false)] 6).Valid g H input :=
  Fact.valid_define g H input 0 (5, false) 6 (by decide +kernel)

private theorem fact71 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(6, false)] 7).Valid g H input :=
  Fact.valid_define g H input 0 (6, false) 7 (by decide +kernel)

private theorem fact75 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(7, true)] 8).Valid g H input :=
  Fact.valid_define g H input 0 (7, true) 8 (by decide +kernel)

private theorem fact83 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(9, true)] 10).Valid g H input :=
  Fact.valid_define g H input 0 (9, true) 10 (by decide +kernel)

private theorem fact87 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(9, false)] 11).Valid g H input :=
  Fact.valid_define g H input 0 (9, false) 11 (by decide +kernel)

private theorem fact90 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 11 [(9, true)] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [(9, false)], 11⟩) (fact87 h)

private theorem fact91 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(10, true)] 12).Valid g H input :=
  Fact.valid_define g H input 0 (10, true) 12 (by decide +kernel)

private theorem fact95 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(10, false)] 13).Valid g H input :=
  Fact.valid_define g H input 0 (10, false) 13 (by decide +kernel)

private theorem fact99 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(11, true)] 14).Valid g H input :=
  Fact.valid_define g H input 0 (11, true) 14 (by decide +kernel)

private theorem fact102 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [(11, false)] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [(11, true)], 14⟩) (fact99 h)

private theorem fact106 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(8, true), (4, false)] 4).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(8, true)], 0⟩) (k := ⟨0, [(4, false)], 4⟩) (fact18 h) (fact45 h) rfl

private theorem fact108 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(11, true), (0, false), (4, true), (8, false)] 0).Valid g H input :=
  Fact.valid_relator h 0 (relator 11)
    (Array.mem_ofFn.mpr ⟨11, rfl⟩) true 3

private theorem fact109 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [(0, false), (4, true), (8, false)] 0).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(11, true)], 14⟩) (k := ⟨0, [(11, true), (0, false), (4, true), (8, false)], 0⟩) (fact99 h) (fact108 h) rfl [(0, false), (4, true), (8, false)] rfl

private theorem fact110 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(8, true), (4, false), (0, true)] 14).Valid g H input :=
  Fact.valid_reverse (f := ⟨14, [(0, false), (4, true), (8, false)], 0⟩) (fact109 h)

private theorem fact111 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true)] 14).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(8, true), (4, false)], 4⟩) (k := ⟨0, [(8, true), (4, false), (0, true)], 14⟩) (fact106 h) (fact110 h) rfl [(0, true)] rfl

private theorem fact112 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [(0, false)] 4).Valid g H input :=
  Fact.valid_reverse (f := ⟨4, [(0, true)], 14⟩) (fact111 h)

private theorem fact114 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true)] 14).Valid g H input :=
  Fact.valid_reverse (f := ⟨14, [(0, false)], 4⟩) (fact112 h)

private theorem fact118 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(1, false), (0, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(1, false)], 0⟩) (k := ⟨0, [(0, false)], 0⟩) (fact6 h) (fact3 h) rfl

private theorem fact120 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(1, false), (0, false), (9, false)] 11).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(1, false), (0, false)], 0⟩) (k := ⟨0, [(9, false)], 11⟩) (fact118 h) (fact87 h) rfl

private theorem fact122 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(11, true), (4, true), (9, true), (0, true), (1, true)] 0).Valid g H input :=
  Fact.valid_relator h 0 (relator 18)
    (Array.mem_ofFn.mpr ⟨18, rfl⟩) true 4

private theorem fact123 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [(4, true), (9, true), (0, true), (1, true)] 0).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(11, true)], 14⟩) (k := ⟨0, [(11, true), (4, true), (9, true), (0, true), (1, true)], 0⟩) (fact99 h) (fact122 h) rfl [(4, true), (9, true), (0, true), (1, true)] rfl

private theorem fact124 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(1, false), (0, false), (9, false), (4, false)] 14).Valid g H input :=
  Fact.valid_reverse (f := ⟨14, [(4, true), (9, true), (0, true), (1, true)], 0⟩) (fact123 h)

private theorem fact125 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 11 [(4, false)] 14).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(1, false), (0, false), (9, false)], 11⟩) (k := ⟨0, [(1, false), (0, false), (9, false), (4, false)], 14⟩) (fact120 h) (fact124 h) rfl [(4, false)] rfl

private theorem fact126 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [(4, true)] 11).Valid g H input :=
  Fact.valid_reverse (f := ⟨11, [(4, false)], 14⟩) (fact125 h)

private theorem fact128 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 11 [(4, false)] 14).Valid g H input :=
  Fact.valid_reverse (f := ⟨14, [(4, true)], 11⟩) (fact126 h)

private theorem fact132 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(1, false), (4, true)] 3).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(1, false)], 0⟩) (k := ⟨0, [(4, true)], 3⟩) (fact6 h) (fact41 h) rfl

private theorem fact134 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(1, false), (4, true), (9, true)] 4).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(1, false), (4, true)], 3⟩) (k := ⟨3, [(9, true)], 4⟩) (fact132 h) (fact62 h) rfl

private theorem fact136 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(11, true), (0, true), (9, false), (4, false), (1, true)] 0).Valid g H input :=
  Fact.valid_relator h 0 (relator 19)
    (Array.mem_ofFn.mpr ⟨19, rfl⟩) true 4

private theorem fact137 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [(0, true), (9, false), (4, false), (1, true)] 0).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(11, true)], 14⟩) (k := ⟨0, [(11, true), (0, true), (9, false), (4, false), (1, true)], 0⟩) (fact99 h) (fact136 h) rfl [(0, true), (9, false), (4, false), (1, true)] rfl

private theorem fact138 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(1, false), (4, true), (9, true), (0, false)] 14).Valid g H input :=
  Fact.valid_reverse (f := ⟨14, [(0, true), (9, false), (4, false), (1, true)], 0⟩) (fact137 h)

private theorem fact139 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, false)] 14).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(1, false), (4, true), (9, true)], 4⟩) (k := ⟨0, [(1, false), (4, true), (9, true), (0, false)], 14⟩) (fact134 h) (fact138 h) rfl [(0, false)] rfl

private theorem fact140 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [(0, true)] 4).Valid g H input :=
  Fact.valid_reverse (f := ⟨4, [(0, false)], 14⟩) (fact139 h)

private theorem fact142 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, false)] 14).Valid g H input :=
  Fact.valid_reverse (f := ⟨14, [(0, true)], 4⟩) (fact140 h)

private theorem fact146 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(1, true), (8, true)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(1, true)], 0⟩) (k := ⟨0, [(8, true)], 0⟩) (fact4 h) (fact18 h) rfl

private theorem fact148 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(1, true), (8, true), (2, true)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(1, true), (8, true)], 0⟩) (k := ⟨0, [(2, true)], 0⟩) (fact146 h) (fact7 h) rfl

private theorem fact150 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(1, true), (8, true), (2, true), (7, true)] 8).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(1, true), (8, true), (2, true)], 0⟩) (k := ⟨0, [(7, true)], 8⟩) (fact148 h) (fact75 h) rfl

private theorem fact152 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(11, true), (16, false), (7, false), (2, false), (8, false), (1, false)] 0).Valid g H input :=
  Fact.valid_relator h 0 (relator 24)
    (Array.mem_ofFn.mpr ⟨24, rfl⟩) false 5

private theorem fact153 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [(16, false), (7, false), (2, false), (8, false), (1, false)] 0).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(11, true)], 14⟩) (k := ⟨0, [(11, true), (16, false), (7, false), (2, false), (8, false), (1, false)], 0⟩) (fact99 h) (fact152 h) rfl [(16, false), (7, false), (2, false), (8, false), (1, false)] rfl

private theorem fact154 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(1, true), (8, true), (2, true), (7, true), (16, true)] 14).Valid g H input :=
  Fact.valid_reverse (f := ⟨14, [(16, false), (7, false), (2, false), (8, false), (1, false)], 0⟩) (fact153 h)

private theorem fact155 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 8 [(16, true)] 14).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(1, true), (8, true), (2, true), (7, true)], 8⟩) (k := ⟨0, [(1, true), (8, true), (2, true), (7, true), (16, true)], 14⟩) (fact150 h) (fact154 h) rfl [(16, true)] rfl

private theorem fact156 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [(16, false)] 8).Valid g H input :=
  Fact.valid_reverse (f := ⟨8, [(16, true)], 14⟩) (fact155 h)

private theorem fact158 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 8 [(16, true)] 14).Valid g H input :=
  Fact.valid_reverse (f := ⟨14, [(16, false)], 8⟩) (fact156 h)

private theorem fact159 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(11, false)] 15).Valid g H input :=
  Fact.valid_define g H input 0 (11, false) 15 (by decide +kernel)

private theorem fact162 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 15 [(11, true)] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [(11, false)], 15⟩) (fact159 h)

private theorem fact166 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(1, true), (11, true)] 14).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(1, true)], 0⟩) (k := ⟨0, [(11, true)], 14⟩) (fact4 h) (fact99 h) rfl

private theorem fact168 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(11, false), (1, false), (11, false), (1, false)] 0).Valid g H input :=
  Fact.valid_relator h 0 (relator 9)
    (Array.mem_ofFn.mpr ⟨9, rfl⟩) false 0

private theorem fact169 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 15 [(1, false), (11, false), (1, false)] 0).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(11, false)], 15⟩) (k := ⟨0, [(11, false), (1, false), (11, false), (1, false)], 0⟩) (fact159 h) (fact168 h) rfl [(1, false), (11, false), (1, false)] rfl

private theorem fact170 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(1, true), (11, true), (1, true)] 15).Valid g H input :=
  Fact.valid_reverse (f := ⟨15, [(1, false), (11, false), (1, false)], 0⟩) (fact169 h)

private theorem fact171 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [(1, true)] 15).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(1, true), (11, true)], 14⟩) (k := ⟨0, [(1, true), (11, true), (1, true)], 15⟩) (fact166 h) (fact170 h) rfl [(1, true)] rfl

private theorem fact172 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 15 [(1, false)] 14).Valid g H input :=
  Fact.valid_reverse (f := ⟨14, [(1, true)], 15⟩) (fact171 h)

private theorem fact178 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(1, false), (11, true)] 14).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(1, false)], 0⟩) (k := ⟨0, [(11, true)], 14⟩) (fact6 h) (fact99 h) rfl

private theorem fact180 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(11, false), (1, true), (11, false), (1, true)] 0).Valid g H input :=
  Fact.valid_relator h 0 (relator 10)
    (Array.mem_ofFn.mpr ⟨10, rfl⟩) false 0

private theorem fact181 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 15 [(1, true), (11, false), (1, true)] 0).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(11, false)], 15⟩) (k := ⟨0, [(11, false), (1, true), (11, false), (1, true)], 0⟩) (fact159 h) (fact180 h) rfl [(1, true), (11, false), (1, true)] rfl

private theorem fact182 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(1, false), (11, true), (1, false)] 15).Valid g H input :=
  Fact.valid_reverse (f := ⟨15, [(1, true), (11, false), (1, true)], 0⟩) (fact181 h)

private theorem fact183 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [(1, false)] 15).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(1, false), (11, true)], 14⟩) (k := ⟨0, [(1, false), (11, true), (1, false)], 15⟩) (fact178 h) (fact182 h) rfl [(1, false)] rfl

private theorem fact184 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 15 [(1, true)] 14).Valid g H input :=
  Fact.valid_reverse (f := ⟨14, [(1, false)], 15⟩) (fact183 h)

private theorem fact190 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(0, false), (4, true)] 3).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(0, false)], 0⟩) (k := ⟨0, [(4, true)], 3⟩) (fact3 h) (fact41 h) rfl

private theorem fact192 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(11, false), (8, true), (4, false), (0, true)] 0).Valid g H input :=
  Fact.valid_relator h 0 (relator 11)
    (Array.mem_ofFn.mpr ⟨11, rfl⟩) false 0

private theorem fact193 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 15 [(8, true), (4, false), (0, true)] 0).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(11, false)], 15⟩) (k := ⟨0, [(11, false), (8, true), (4, false), (0, true)], 0⟩) (fact159 h) (fact192 h) rfl [(8, true), (4, false), (0, true)] rfl

private theorem fact194 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(0, false), (4, true), (8, false)] 15).Valid g H input :=
  Fact.valid_reverse (f := ⟨15, [(8, true), (4, false), (0, true)], 0⟩) (fact193 h)

private theorem fact195 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 3 [(8, false)] 15).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(0, false), (4, true)], 3⟩) (k := ⟨0, [(0, false), (4, true), (8, false)], 15⟩) (fact190 h) (fact194 h) rfl [(8, false)] rfl

private theorem fact196 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 15 [(8, true)] 3).Valid g H input :=
  Fact.valid_reverse (f := ⟨3, [(8, false)], 15⟩) (fact195 h)

private theorem fact198 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 3 [(8, false)] 15).Valid g H input :=
  Fact.valid_reverse (f := ⟨15, [(8, true)], 3⟩) (fact196 h)

private theorem fact199 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(12, true)] 16).Valid g H input :=
  Fact.valid_define g H input 0 (12, true) 16 (by decide +kernel)

private theorem fact206 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(0, false), (1, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(0, false)], 0⟩) (k := ⟨0, [(1, false)], 0⟩) (fact3 h) (fact6 h) rfl

private theorem fact208 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(0, false), (1, false), (0, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(0, false), (1, false)], 0⟩) (k := ⟨0, [(0, false)], 0⟩) (fact206 h) (fact3 h) rfl

private theorem fact210 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(0, false), (1, false), (0, false), (11, false)] 15).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(0, false), (1, false), (0, false)], 0⟩) (k := ⟨0, [(11, false)], 15⟩) (fact208 h) (fact159 h) rfl

private theorem fact212 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(0, false), (1, false), (0, false), (11, false), (1, false)] 14).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(0, false), (1, false), (0, false), (11, false)], 15⟩) (k := ⟨15, [(1, false)], 14⟩) (fact210 h) (fact172 h) rfl

private theorem fact214 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(12, true), (12, true), (1, true), (11, true), (0, true), (1, true), (0, true)] 0).Valid g H input :=
  Fact.valid_relator h 0 (relator 33)
    (Array.mem_ofFn.mpr ⟨33, rfl⟩) true 5

private theorem fact215 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 16 [(12, true), (1, true), (11, true), (0, true), (1, true), (0, true)] 0).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(12, true)], 16⟩) (k := ⟨0, [(12, true), (12, true), (1, true), (11, true), (0, true), (1, true), (0, true)], 0⟩) (fact199 h) (fact214 h) rfl [(12, true), (1, true), (11, true), (0, true), (1, true), (0, true)] rfl

private theorem fact216 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(0, false), (1, false), (0, false), (11, false), (1, false), (12, false)] 16).Valid g H input :=
  Fact.valid_reverse (f := ⟨16, [(12, true), (1, true), (11, true), (0, true), (1, true), (0, true)], 0⟩) (fact215 h)

private theorem fact217 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [(12, false)] 16).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(0, false), (1, false), (0, false), (11, false), (1, false)], 14⟩) (k := ⟨0, [(0, false), (1, false), (0, false), (11, false), (1, false), (12, false)], 16⟩) (fact212 h) (fact216 h) rfl [(12, false)] rfl

private theorem fact218 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 16 [(12, true)] 14).Valid g H input :=
  Fact.valid_reverse (f := ⟨14, [(12, false)], 16⟩) (fact217 h)

private theorem fact220 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [(12, false)] 16).Valid g H input :=
  Fact.valid_reverse (f := ⟨16, [(12, true)], 14⟩) (fact218 h)

private theorem fact221 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(12, false)] 17).Valid g H input :=
  Fact.valid_define g H input 0 (12, false) 17 (by decide +kernel)

private theorem fact224 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 17 [(12, true)] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [(12, false)], 17⟩) (fact221 h)

private theorem fact225 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(13, true)] 18).Valid g H input :=
  Fact.valid_define g H input 0 (13, true) 18 (by decide +kernel)

private theorem fact233 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(14, true)] 20).Valid g H input :=
  Fact.valid_define g H input 0 (14, true) 20 (by decide +kernel)

private theorem fact236 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 20 [(14, false)] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [(14, true)], 20⟩) (fact233 h)

private theorem fact237 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(14, false)] 21).Valid g H input :=
  Fact.valid_define g H input 0 (14, false) 21 (by decide +kernel)

private theorem fact240 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 21 [(14, true)] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [(14, false)], 21⟩) (fact237 h)

private theorem fact254 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(2, true), (14, true)] 20).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(2, true)], 0⟩) (k := ⟨0, [(14, true)], 20⟩) (fact7 h) (fact233 h) rfl

private theorem fact256 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(14, false), (2, false), (14, false), (2, false)] 0).Valid g H input :=
  Fact.valid_relator h 0 (relator 7)
    (Array.mem_ofFn.mpr ⟨7, rfl⟩) false 0

private theorem fact257 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 21 [(2, false), (14, false), (2, false)] 0).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(14, false)], 21⟩) (k := ⟨0, [(14, false), (2, false), (14, false), (2, false)], 0⟩) (fact237 h) (fact256 h) rfl [(2, false), (14, false), (2, false)] rfl

private theorem fact258 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(2, true), (14, true), (2, true)] 21).Valid g H input :=
  Fact.valid_reverse (f := ⟨21, [(2, false), (14, false), (2, false)], 0⟩) (fact257 h)

private theorem fact259 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 20 [(2, true)] 21).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(2, true), (14, true)], 20⟩) (k := ⟨0, [(2, true), (14, true), (2, true)], 21⟩) (fact254 h) (fact258 h) rfl [(2, true)] rfl

private theorem fact260 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 21 [(2, false)] 20).Valid g H input :=
  Fact.valid_reverse (f := ⟨20, [(2, true)], 21⟩) (fact259 h)

private theorem fact262 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 20 [(2, true)] 21).Valid g H input :=
  Fact.valid_reverse (f := ⟨21, [(2, false)], 20⟩) (fact260 h)

private theorem fact266 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(2, false), (14, true)] 20).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(2, false)], 0⟩) (k := ⟨0, [(14, true)], 20⟩) (fact9 h) (fact233 h) rfl

private theorem fact268 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(14, false), (2, true), (14, false), (2, true)] 0).Valid g H input :=
  Fact.valid_relator h 0 (relator 8)
    (Array.mem_ofFn.mpr ⟨8, rfl⟩) false 0

private theorem fact269 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 21 [(2, true), (14, false), (2, true)] 0).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(14, false)], 21⟩) (k := ⟨0, [(14, false), (2, true), (14, false), (2, true)], 0⟩) (fact237 h) (fact268 h) rfl [(2, true), (14, false), (2, true)] rfl

private theorem fact270 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(2, false), (14, true), (2, false)] 21).Valid g H input :=
  Fact.valid_reverse (f := ⟨21, [(2, true), (14, false), (2, true)], 0⟩) (fact269 h)

private theorem fact271 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 20 [(2, false)] 21).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(2, false), (14, true)], 20⟩) (k := ⟨0, [(2, false), (14, true), (2, false)], 21⟩) (fact266 h) (fact270 h) rfl [(2, false)] rfl

private theorem fact272 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 21 [(2, true)] 20).Valid g H input :=
  Fact.valid_reverse (f := ⟨20, [(2, false)], 21⟩) (fact271 h)

private theorem fact274 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 20 [(2, false)] 21).Valid g H input :=
  Fact.valid_reverse (f := ⟨21, [(2, true)], 20⟩) (fact272 h)

private theorem fact275 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(15, true)] 22).Valid g H input :=
  Fact.valid_define g H input 0 (15, true) 22 (by decide +kernel)

private theorem fact279 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(15, false)] 23).Valid g H input :=
  Fact.valid_define g H input 0 (15, false) 23 (by decide +kernel)

private theorem fact283 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(16, true)] 24).Valid g H input :=
  Fact.valid_define g H input 0 (16, true) 24 (by decide +kernel)

private theorem fact287 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(16, false)] 25).Valid g H input :=
  Fact.valid_define g H input 0 (16, false) 25 (by decide +kernel)

private theorem fact294 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(7, true), (16, true)] 14).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(7, true)], 8⟩) (k := ⟨8, [(16, true)], 14⟩) (fact75 h) (fact158 h) rfl

private theorem fact296 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(16, false), (7, false), (16, false), (7, false)] 0).Valid g H input :=
  Fact.valid_relator h 0 (relator 6)
    (Array.mem_ofFn.mpr ⟨6, rfl⟩) false 0

private theorem fact297 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 25 [(7, false), (16, false), (7, false)] 0).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(16, false)], 25⟩) (k := ⟨0, [(16, false), (7, false), (16, false), (7, false)], 0⟩) (fact287 h) (fact296 h) rfl [(7, false), (16, false), (7, false)] rfl

private theorem fact298 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(7, true), (16, true), (7, true)] 25).Valid g H input :=
  Fact.valid_reverse (f := ⟨25, [(7, false), (16, false), (7, false)], 0⟩) (fact297 h)

private theorem fact299 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [(7, true)] 25).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(7, true), (16, true)], 14⟩) (k := ⟨0, [(7, true), (16, true), (7, true)], 25⟩) (fact294 h) (fact298 h) rfl [(7, true)] rfl

private theorem fact300 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 25 [(7, false)] 14).Valid g H input :=
  Fact.valid_reverse (f := ⟨14, [(7, true)], 25⟩) (fact299 h)

private theorem fact306 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(8, true), (1, true)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(8, true)], 0⟩) (k := ⟨0, [(1, true)], 0⟩) (fact18 h) (fact4 h) rfl

private theorem fact308 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(8, true), (1, true), (0, true)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(8, true), (1, true)], 0⟩) (k := ⟨0, [(0, true)], 0⟩) (fact306 h) (fact0 h) rfl

private theorem fact310 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(8, true), (1, true), (0, true), (6, false)] 7).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(8, true), (1, true), (0, true)], 0⟩) (k := ⟨0, [(6, false)], 7⟩) (fact308 h) (fact71 h) rfl

private theorem fact312 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(16, false), (14, false), (6, true), (0, false), (1, false), (8, false)] 0).Valid g H input :=
  Fact.valid_relator h 0 (relator 23)
    (Array.mem_ofFn.mpr ⟨23, rfl⟩) false 0

private theorem fact313 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 25 [(14, false), (6, true), (0, false), (1, false), (8, false)] 0).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(16, false)], 25⟩) (k := ⟨0, [(16, false), (14, false), (6, true), (0, false), (1, false), (8, false)], 0⟩) (fact287 h) (fact312 h) rfl [(14, false), (6, true), (0, false), (1, false), (8, false)] rfl

private theorem fact314 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(8, true), (1, true), (0, true), (6, false), (14, true)] 25).Valid g H input :=
  Fact.valid_reverse (f := ⟨25, [(14, false), (6, true), (0, false), (1, false), (8, false)], 0⟩) (fact313 h)

private theorem fact315 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 7 [(14, true)] 25).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(8, true), (1, true), (0, true), (6, false)], 7⟩) (k := ⟨0, [(8, true), (1, true), (0, true), (6, false), (14, true)], 25⟩) (fact310 h) (fact314 h) rfl [(14, true)] rfl

private theorem fact316 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 25 [(14, false)] 7).Valid g H input :=
  Fact.valid_reverse (f := ⟨7, [(14, true)], 25⟩) (fact315 h)

private theorem fact711 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 2 [(10, true)] 71).Valid g H input :=
  Fact.valid_define g H input 2 (10, true) 71 (by decide +kernel)

private theorem fact714 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 71 [(10, false)] 2).Valid g H input :=
  Fact.valid_reverse (f := ⟨2, [(10, true)], 71⟩) (fact711 h)

private theorem fact732 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 2 [(3, true), (1, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨2, [(3, true)], 0⟩) (k := ⟨0, [(1, false)], 0⟩) (fact28 h) (fact6 h) rfl

private theorem fact734 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 2 [(3, true), (1, false), (16, true)] 24).Valid g H input :=
  Fact.valid_trans (f := ⟨2, [(3, true), (1, false)], 0⟩) (k := ⟨0, [(16, true)], 24⟩) (fact732 h) (fact283 h) rfl

private theorem fact736 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 2 [(10, true), (2, true), (16, false), (1, true), (3, false)] 2).Valid g H input :=
  Fact.valid_relator h 2 (relator 17)
    (Array.mem_ofFn.mpr ⟨17, rfl⟩) false 3

private theorem fact737 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 71 [(2, true), (16, false), (1, true), (3, false)] 2).Valid g H input :=
  Fact.valid_cancel (f := ⟨2, [(10, true)], 71⟩) (k := ⟨2, [(10, true), (2, true), (16, false), (1, true), (3, false)], 2⟩) (fact711 h) (fact736 h) rfl [(2, true), (16, false), (1, true), (3, false)] rfl

private theorem fact738 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 2 [(3, true), (1, false), (16, true), (2, false)] 71).Valid g H input :=
  Fact.valid_reverse (f := ⟨71, [(2, true), (16, false), (1, true), (3, false)], 2⟩) (fact737 h)

private theorem fact739 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 24 [(2, false)] 71).Valid g H input :=
  Fact.valid_cancel (f := ⟨2, [(3, true), (1, false), (16, true)], 24⟩) (k := ⟨2, [(3, true), (1, false), (16, true), (2, false)], 71⟩) (fact734 h) (fact738 h) rfl [(2, false)] rfl

private theorem fact740 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 71 [(2, true)] 24).Valid g H input :=
  Fact.valid_reverse (f := ⟨24, [(2, false)], 71⟩) (fact739 h)

private theorem fact742 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 24 [(2, false)] 71).Valid g H input :=
  Fact.valid_reverse (f := ⟨71, [(2, true)], 24⟩) (fact740 h)

private theorem fact837 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 3 [(0, true)] 85).Valid g H input :=
  Fact.valid_define g H input 3 (0, true) 85 (by decide +kernel)

private theorem fact843 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 3 [(0, true), (0, true)] 3).Valid g H input :=
  Fact.valid_relator h 3 (relator 2)
    (Array.mem_ofFn.mpr ⟨2, rfl⟩) true 0

private theorem fact844 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 85 [(0, true)] 3).Valid g H input :=
  Fact.valid_cancel (f := ⟨3, [(0, true)], 85⟩) (k := ⟨3, [(0, true), (0, true)], 3⟩) (fact837 h) (fact843 h) rfl [(0, true)] rfl

private theorem fact845 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 3 [(0, false)] 85).Valid g H input :=
  Fact.valid_reverse (f := ⟨85, [(0, true)], 3⟩) (fact844 h)

private theorem fact846 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 3 [(0, false)] 85).Valid g H input :=
  Fact.valid_cancel (f := ⟨3, [], 3⟩) (k := ⟨3, [(0, false)], 85⟩) (fact43 h) (fact845 h) rfl [(0, false)] rfl

private theorem fact847 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 85 [(0, true)] 3).Valid g H input :=
  Fact.valid_reverse (f := ⟨3, [(0, false)], 85⟩) (fact846 h)

private theorem fact849 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 3 [(0, false)] 85).Valid g H input :=
  Fact.valid_reverse (f := ⟨85, [(0, true)], 3⟩) (fact847 h)

private theorem fact884 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 3 [(2, true)] 87).Valid g H input :=
  Fact.valid_define g H input 3 (2, true) 87 (by decide +kernel)

private theorem fact900 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 3 [(2, true), (8, true), (0, true)] 3).Valid g H input :=
  Fact.valid_relator h 3 (relator 4)
    (Array.mem_ofFn.mpr ⟨4, rfl⟩) true 1

private theorem fact901 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 87 [(8, true), (0, true)] 3).Valid g H input :=
  Fact.valid_cancel (f := ⟨3, [(2, true)], 87⟩) (k := ⟨3, [(2, true), (8, true), (0, true)], 3⟩) (fact884 h) (fact900 h) rfl [(8, true), (0, true)] rfl

private theorem fact902 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 3 [(0, false), (8, false)] 87).Valid g H input :=
  Fact.valid_reverse (f := ⟨87, [(8, true), (0, true)], 3⟩) (fact901 h)

private theorem fact903 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 85 [(8, false)] 87).Valid g H input :=
  Fact.valid_cancel (f := ⟨3, [(0, false)], 85⟩) (k := ⟨3, [(0, false), (8, false)], 87⟩) (fact849 h) (fact902 h) rfl [(8, false)] rfl

private theorem fact904 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 87 [(8, true)] 85).Valid g H input :=
  Fact.valid_reverse (f := ⟨85, [(8, false)], 87⟩) (fact903 h)

private theorem fact906 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 85 [(8, false)] 87).Valid g H input :=
  Fact.valid_reverse (f := ⟨87, [(8, true)], 85⟩) (fact904 h)

private theorem fact943 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 3 [(8, true)] 97).Valid g H input :=
  Fact.valid_define g H input 3 (8, true) 97 (by decide +kernel)

private theorem fact960 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 3 [(8, true), (0, false), (2, false)] 3).Valid g H input :=
  Fact.valid_relator h 3 (relator 5)
    (Array.mem_ofFn.mpr ⟨5, rfl⟩) true 2

private theorem fact961 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 97 [(0, false), (2, false)] 3).Valid g H input :=
  Fact.valid_cancel (f := ⟨3, [(8, true)], 97⟩) (k := ⟨3, [(8, true), (0, false), (2, false)], 3⟩) (fact943 h) (fact960 h) rfl [(0, false), (2, false)] rfl

private theorem fact962 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 3 [(2, true), (0, true)] 97).Valid g H input :=
  Fact.valid_reverse (f := ⟨97, [(0, false), (2, false)], 3⟩) (fact961 h)

private theorem fact963 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 87 [(0, true)] 97).Valid g H input :=
  Fact.valid_cancel (f := ⟨3, [(2, true)], 87⟩) (k := ⟨3, [(2, true), (0, true)], 97⟩) (fact884 h) (fact962 h) rfl [(0, true)] rfl

private theorem fact964 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 97 [(0, false)] 87).Valid g H input :=
  Fact.valid_reverse (f := ⟨87, [(0, true)], 97⟩) (fact963 h)

private theorem fact1033 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 3 [(16, false)] 112).Valid g H input :=
  Fact.valid_define g H input 3 (16, false) 112 (by decide +kernel)

private theorem fact1036 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 112 [(16, true)] 3).Valid g H input :=
  Fact.valid_reverse (f := ⟨3, [(16, false)], 112⟩) (fact1033 h)

private theorem fact1037 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, true)] 113).Valid g H input :=
  Fact.valid_define g H input 4 (1, true) 113 (by decide +kernel)

private theorem fact1043 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, true), (1, true)] 4).Valid g H input :=
  Fact.valid_relator h 4 (relator 1)
    (Array.mem_ofFn.mpr ⟨1, rfl⟩) true 0

private theorem fact1044 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 113 [(1, true)] 4).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(1, true)], 113⟩) (k := ⟨4, [(1, true), (1, true)], 4⟩) (fact1037 h) (fact1043 h) rfl [(1, true)] rfl

private theorem fact1045 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false)] 113).Valid g H input :=
  Fact.valid_reverse (f := ⟨113, [(1, true)], 4⟩) (fact1044 h)

private theorem fact1046 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false)] 113).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [], 4⟩) (k := ⟨4, [(1, false)], 113⟩) (fact47 h) (fact1045 h) rfl [(1, false)] rfl

private theorem fact1047 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 113 [(1, true)] 4).Valid g H input :=
  Fact.valid_reverse (f := ⟨4, [(1, false)], 113⟩) (fact1046 h)

private theorem fact1049 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false)] 113).Valid g H input :=
  Fact.valid_reverse (f := ⟨113, [(1, true)], 4⟩) (fact1047 h)

private theorem fact1053 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(9, false), (4, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(9, false)], 3⟩) (k := ⟨3, [(4, false)], 0⟩) (fact60 h) (fact44 h) rfl

private theorem fact1055 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(9, false), (4, false), (8, true)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(9, false), (4, false)], 0⟩) (k := ⟨0, [(8, true)], 0⟩) (fact1053 h) (fact18 h) rfl

private theorem fact1057 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(9, false), (4, false), (8, true), (1, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(9, false), (4, false), (8, true)], 0⟩) (k := ⟨0, [(1, false)], 0⟩) (fact1055 h) (fact6 h) rfl

private theorem fact1059 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(9, false), (4, false), (8, true), (1, false), (0, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(9, false), (4, false), (8, true), (1, false)], 0⟩) (k := ⟨0, [(0, false)], 0⟩) (fact1057 h) (fact3 h) rfl

private theorem fact1061 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(9, false), (4, false), (8, true), (1, false), (0, false), (14, true)] 20).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(9, false), (4, false), (8, true), (1, false), (0, false)], 0⟩) (k := ⟨0, [(14, true)], 20⟩) (fact1059 h) (fact233 h) rfl

private theorem fact1063 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, true), (16, true), (14, false), (0, true), (1, true), (8, false), (4, true), (9, true)] 4).Valid g H input :=
  Fact.valid_relator h 4 (relator 37)
    (Array.mem_ofFn.mpr ⟨37, rfl⟩) true 6

private theorem fact1064 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 113 [(16, true), (14, false), (0, true), (1, true), (8, false), (4, true), (9, true)] 4).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(1, true)], 113⟩) (k := ⟨4, [(1, true), (16, true), (14, false), (0, true), (1, true), (8, false), (4, true), (9, true)], 4⟩) (fact1037 h) (fact1063 h) rfl [(16, true), (14, false), (0, true), (1, true), (8, false), (4, true), (9, true)] rfl

private theorem fact1065 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(9, false), (4, false), (8, true), (1, false), (0, false), (14, true), (16, false)] 113).Valid g H input :=
  Fact.valid_reverse (f := ⟨113, [(16, true), (14, false), (0, true), (1, true), (8, false), (4, true), (9, true)], 4⟩) (fact1064 h)

private theorem fact1066 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 20 [(16, false)] 113).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(9, false), (4, false), (8, true), (1, false), (0, false), (14, true)], 20⟩) (k := ⟨4, [(9, false), (4, false), (8, true), (1, false), (0, false), (14, true), (16, false)], 113⟩) (fact1061 h) (fact1065 h) rfl [(16, false)] rfl

private theorem fact1067 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 113 [(16, true)] 20).Valid g H input :=
  Fact.valid_reverse (f := ⟨20, [(16, false)], 113⟩) (fact1066 h)

private theorem fact1069 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 20 [(16, false)] 113).Valid g H input :=
  Fact.valid_reverse (f := ⟨113, [(16, true)], 20⟩) (fact1067 h)

private theorem fact1070 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(2, true)] 114).Valid g H input :=
  Fact.valid_define g H input 4 (2, true) 114 (by decide +kernel)

private theorem fact1073 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 114 [(2, false)] 4).Valid g H input :=
  Fact.valid_reverse (f := ⟨4, [(2, true)], 114⟩) (fact1070 h)

private theorem fact1076 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(2, true), (2, true)] 4).Valid g H input :=
  Fact.valid_relator h 4 (relator 0)
    (Array.mem_ofFn.mpr ⟨0, rfl⟩) true 0

private theorem fact1077 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 114 [(2, true)] 4).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(2, true)], 114⟩) (k := ⟨4, [(2, true), (2, true)], 4⟩) (fact1070 h) (fact1076 h) rfl [(2, true)] rfl

private theorem fact1078 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(2, false)] 114).Valid g H input :=
  Fact.valid_reverse (f := ⟨114, [(2, true)], 4⟩) (fact1077 h)

private theorem fact1079 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(2, false)] 114).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [], 4⟩) (k := ⟨4, [(2, false)], 114⟩) (fact47 h) (fact1078 h) rfl [(2, false)] rfl

private theorem fact1080 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 114 [(2, true)] 4).Valid g H input :=
  Fact.valid_reverse (f := ⟨4, [(2, false)], 114⟩) (fact1079 h)

private theorem fact1082 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(2, false)] 114).Valid g H input :=
  Fact.valid_reverse (f := ⟨114, [(2, true)], 4⟩) (fact1080 h)

private theorem fact1086 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(2, true), (8, true), (0, true)] 4).Valid g H input :=
  Fact.valid_relator h 4 (relator 4)
    (Array.mem_ofFn.mpr ⟨4, rfl⟩) true 1

private theorem fact1087 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 114 [(8, true), (0, true)] 4).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(2, true)], 114⟩) (k := ⟨4, [(2, true), (8, true), (0, true)], 4⟩) (fact1070 h) (fact1086 h) rfl [(8, true), (0, true)] rfl

private theorem fact1088 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, false), (8, false)] 114).Valid g H input :=
  Fact.valid_reverse (f := ⟨114, [(8, true), (0, true)], 4⟩) (fact1087 h)

private theorem fact1089 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [(8, false)] 114).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(0, false)], 14⟩) (k := ⟨4, [(0, false), (8, false)], 114⟩) (fact142 h) (fact1088 h) rfl [(8, false)] rfl

private theorem fact1090 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 114 [(8, true)] 14).Valid g H input :=
  Fact.valid_reverse (f := ⟨14, [(8, false)], 114⟩) (fact1089 h)

private theorem fact1096 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(9, false), (4, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(9, false)], 3⟩) (k := ⟨3, [(4, false)], 0⟩) (fact60 h) (fact44 h) rfl

private theorem fact1098 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(9, false), (4, false), (14, false)] 21).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(9, false), (4, false)], 0⟩) (k := ⟨0, [(14, false)], 21⟩) (fact1096 h) (fact237 h) rfl

private theorem fact1100 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(9, false), (4, false), (14, false), (2, false)] 20).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(9, false), (4, false), (14, false)], 21⟩) (k := ⟨21, [(2, false)], 20⟩) (fact1098 h) (fact260 h) rfl

private theorem fact1102 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(9, false), (4, false), (14, false), (2, false), (16, false)] 113).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(9, false), (4, false), (14, false), (2, false)], 20⟩) (k := ⟨20, [(16, false)], 113⟩) (fact1100 h) (fact1069 h) rfl

private theorem fact1104 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(2, true), (7, true), (16, true), (2, true), (14, true), (4, true), (9, true)] 4).Valid g H input :=
  Fact.valid_relator h 4 (relator 31)
    (Array.mem_ofFn.mpr ⟨31, rfl⟩) true 4

private theorem fact1105 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 114 [(7, true), (16, true), (2, true), (14, true), (4, true), (9, true)] 4).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(2, true)], 114⟩) (k := ⟨4, [(2, true), (7, true), (16, true), (2, true), (14, true), (4, true), (9, true)], 4⟩) (fact1070 h) (fact1104 h) rfl [(7, true), (16, true), (2, true), (14, true), (4, true), (9, true)] rfl

private theorem fact1106 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(9, false), (4, false), (14, false), (2, false), (16, false), (7, false)] 114).Valid g H input :=
  Fact.valid_reverse (f := ⟨114, [(7, true), (16, true), (2, true), (14, true), (4, true), (9, true)], 4⟩) (fact1105 h)

private theorem fact1107 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 113 [(7, false)] 114).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(9, false), (4, false), (14, false), (2, false), (16, false)], 113⟩) (k := ⟨4, [(9, false), (4, false), (14, false), (2, false), (16, false), (7, false)], 114⟩) (fact1102 h) (fact1106 h) rfl [(7, false)] rfl

private theorem fact1108 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 114 [(7, true)] 113).Valid g H input :=
  Fact.valid_reverse (f := ⟨113, [(7, false)], 114⟩) (fact1107 h)

private theorem fact1110 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 113 [(7, false)] 114).Valid g H input :=
  Fact.valid_reverse (f := ⟨114, [(7, true)], 113⟩) (fact1108 h)

private theorem fact1115 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(3, false)] 116).Valid g H input :=
  Fact.valid_define g H input 4 (3, false) 116 (by decide +kernel)

private theorem fact1122 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, true), (16, true)] 20).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(1, true)], 113⟩) (k := ⟨113, [(16, true)], 20⟩) (fact1037 h) (fact1067 h) rfl

private theorem fact1124 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, true), (16, true), (2, true)] 21).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(1, true), (16, true)], 20⟩) (k := ⟨20, [(2, true)], 21⟩) (fact1122 h) (fact262 h) rfl

private theorem fact1126 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(3, false), (10, true), (2, false), (16, false), (1, false)] 4).Valid g H input :=
  Fact.valid_relator h 4 (relator 16)
    (Array.mem_ofFn.mpr ⟨16, rfl⟩) false 2

private theorem fact1127 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 116 [(10, true), (2, false), (16, false), (1, false)] 4).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(3, false)], 116⟩) (k := ⟨4, [(3, false), (10, true), (2, false), (16, false), (1, false)], 4⟩) (fact1115 h) (fact1126 h) rfl [(10, true), (2, false), (16, false), (1, false)] rfl

private theorem fact1128 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, true), (16, true), (2, true), (10, false)] 116).Valid g H input :=
  Fact.valid_reverse (f := ⟨116, [(10, true), (2, false), (16, false), (1, false)], 4⟩) (fact1127 h)

private theorem fact1129 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 21 [(10, false)] 116).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(1, true), (16, true), (2, true)], 21⟩) (k := ⟨4, [(1, true), (16, true), (2, true), (10, false)], 116⟩) (fact1124 h) (fact1128 h) rfl [(10, false)] rfl

private theorem fact1130 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 116 [(10, true)] 21).Valid g H input :=
  Fact.valid_reverse (f := ⟨21, [(10, false)], 116⟩) (fact1129 h)

private theorem fact1132 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 21 [(10, false)] 116).Valid g H input :=
  Fact.valid_reverse (f := ⟨116, [(10, true)], 21⟩) (fact1130 h)

private theorem fact1137 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(5, true)] 118).Valid g H input :=
  Fact.valid_define g H input 4 (5, true) 118 (by decide +kernel)

private theorem fact1140 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 118 [(5, false)] 4).Valid g H input :=
  Fact.valid_reverse (f := ⟨4, [(5, true)], 118⟩) (fact1137 h)

private theorem fact1157 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(7, false)] 123).Valid g H input :=
  Fact.valid_define g H input 4 (7, false) 123 (by decide +kernel)

private theorem fact1185 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(8, false)] 125).Valid g H input :=
  Fact.valid_define g H input 4 (8, false) 125 (by decide +kernel)

private theorem fact1188 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(8, true)] 4).Valid g H input :=
  Fact.valid_reverse (f := ⟨4, [(8, false)], 125⟩) (fact1185 h)

private theorem fact1192 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(8, false), (2, false), (0, false)] 4).Valid g H input :=
  Fact.valid_relator h 4 (relator 4)
    (Array.mem_ofFn.mpr ⟨4, rfl⟩) false 0

private theorem fact1193 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(2, false), (0, false)] 4).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(8, false)], 125⟩) (k := ⟨4, [(8, false), (2, false), (0, false)], 4⟩) (fact1185 h) (fact1192 h) rfl [(2, false), (0, false)] rfl

private theorem fact1194 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true), (2, true)] 125).Valid g H input :=
  Fact.valid_reverse (f := ⟨125, [(2, false), (0, false)], 4⟩) (fact1193 h)

private theorem fact1195 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [(2, true)] 125).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(0, true)], 14⟩) (k := ⟨4, [(0, true), (2, true)], 125⟩) (fact114 h) (fact1194 h) rfl [(2, true)] rfl

private theorem fact1196 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(2, false)] 14).Valid g H input :=
  Fact.valid_reverse (f := ⟨14, [(2, true)], 125⟩) (fact1195 h)

private theorem fact1202 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(8, false), (2, true), (0, true)] 4).Valid g H input :=
  Fact.valid_relator h 4 (relator 5)
    (Array.mem_ofFn.mpr ⟨5, rfl⟩) false 0

private theorem fact1203 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(2, true), (0, true)] 4).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(8, false)], 125⟩) (k := ⟨4, [(8, false), (2, true), (0, true)], 4⟩) (fact1185 h) (fact1202 h) rfl [(2, true), (0, true)] rfl

private theorem fact1204 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, false), (2, false)] 125).Valid g H input :=
  Fact.valid_reverse (f := ⟨125, [(2, true), (0, true)], 4⟩) (fact1203 h)

private theorem fact1205 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [(2, false)] 125).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(0, false)], 14⟩) (k := ⟨4, [(0, false), (2, false)], 125⟩) (fact142 h) (fact1204 h) rfl [(2, false)] rfl

private theorem fact1206 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(2, true)] 14).Valid g H input :=
  Fact.valid_reverse (f := ⟨14, [(2, false)], 125⟩) (fact1205 h)

private theorem fact1208 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [(2, false)] 125).Valid g H input :=
  Fact.valid_reverse (f := ⟨125, [(2, true)], 14⟩) (fact1206 h)

private theorem fact1212 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(9, false), (4, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(9, false)], 3⟩) (k := ⟨3, [(4, false)], 0⟩) (fact60 h) (fact44 h) rfl

private theorem fact1214 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(9, false), (4, false), (7, true)] 8).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(9, false), (4, false)], 0⟩) (k := ⟨0, [(7, true)], 8⟩) (fact1212 h) (fact75 h) rfl

private theorem fact1216 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(9, false), (4, false), (7, true), (16, true)] 14).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(9, false), (4, false), (7, true)], 8⟩) (k := ⟨8, [(16, true)], 14⟩) (fact1214 h) (fact158 h) rfl

private theorem fact1218 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(8, false), (8, false), (16, false), (7, false), (4, true), (9, true)] 4).Valid g H input :=
  Fact.valid_relator h 4 (relator 25)
    (Array.mem_ofFn.mpr ⟨25, rfl⟩) false 4

private theorem fact1219 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(8, false), (16, false), (7, false), (4, true), (9, true)] 4).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(8, false)], 125⟩) (k := ⟨4, [(8, false), (8, false), (16, false), (7, false), (4, true), (9, true)], 4⟩) (fact1185 h) (fact1218 h) rfl [(8, false), (16, false), (7, false), (4, true), (9, true)] rfl

private theorem fact1220 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(9, false), (4, false), (7, true), (16, true), (8, true)] 125).Valid g H input :=
  Fact.valid_reverse (f := ⟨125, [(8, false), (16, false), (7, false), (4, true), (9, true)], 4⟩) (fact1219 h)

private theorem fact1221 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [(8, true)] 125).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(9, false), (4, false), (7, true), (16, true)], 14⟩) (k := ⟨4, [(9, false), (4, false), (7, true), (16, true), (8, true)], 125⟩) (fact1216 h) (fact1220 h) rfl [(8, true)] rfl

private theorem fact1222 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(8, false)] 14).Valid g H input :=
  Fact.valid_reverse (f := ⟨14, [(8, true)], 125⟩) (fact1221 h)

private theorem fact1224 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [(8, true)] 125).Valid g H input :=
  Fact.valid_reverse (f := ⟨125, [(8, false)], 14⟩) (fact1222 h)

private theorem fact1228 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(3, false), (10, true)] 21).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(3, false)], 116⟩) (k := ⟨116, [(10, true)], 21⟩) (fact1115 h) (fact1130 h) rfl

private theorem fact1230 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(3, false), (10, true), (14, true)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(3, false), (10, true)], 21⟩) (k := ⟨21, [(14, true)], 0⟩) (fact1228 h) (fact240 h) rfl

private theorem fact1232 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(3, false), (10, true), (14, true), (11, false)] 15).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(3, false), (10, true), (14, true)], 0⟩) (k := ⟨0, [(11, false)], 15⟩) (fact1230 h) (fact159 h) rfl

private theorem fact1234 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(8, false), (7, true), (11, true), (14, false), (10, false), (3, true)] 4).Valid g H input :=
  Fact.valid_relator h 4 (relator 28)
    (Array.mem_ofFn.mpr ⟨28, rfl⟩) false 3

private theorem fact1235 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(7, true), (11, true), (14, false), (10, false), (3, true)] 4).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(8, false)], 125⟩) (k := ⟨4, [(8, false), (7, true), (11, true), (14, false), (10, false), (3, true)], 4⟩) (fact1185 h) (fact1234 h) rfl [(7, true), (11, true), (14, false), (10, false), (3, true)] rfl

private theorem fact1236 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(3, false), (10, true), (14, true), (11, false), (7, false)] 125).Valid g H input :=
  Fact.valid_reverse (f := ⟨125, [(7, true), (11, true), (14, false), (10, false), (3, true)], 4⟩) (fact1235 h)

private theorem fact1237 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 15 [(7, false)] 125).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(3, false), (10, true), (14, true), (11, false)], 15⟩) (k := ⟨4, [(3, false), (10, true), (14, true), (11, false), (7, false)], 125⟩) (fact1232 h) (fact1236 h) rfl [(7, false)] rfl

private theorem fact1238 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(7, true)] 15).Valid g H input :=
  Fact.valid_reverse (f := ⟨15, [(7, false)], 125⟩) (fact1237 h)

private theorem fact1240 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 15 [(7, false)] 125).Valid g H input :=
  Fact.valid_reverse (f := ⟨125, [(7, true)], 15⟩) (fact1238 h)

private theorem fact1244 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(9, false), (4, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(9, false)], 3⟩) (k := ⟨3, [(4, false)], 0⟩) (fact60 h) (fact44 h) rfl

private theorem fact1246 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(9, false), (4, false), (8, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(9, false), (4, false)], 0⟩) (k := ⟨0, [(8, false)], 0⟩) (fact1244 h) (fact20 h) rfl

private theorem fact1248 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(9, false), (4, false), (8, false), (16, false)] 25).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(9, false), (4, false), (8, false)], 0⟩) (k := ⟨0, [(16, false)], 25⟩) (fact1246 h) (fact287 h) rfl

private theorem fact1250 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(9, false), (4, false), (8, false), (16, false), (7, false)] 14).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(9, false), (4, false), (8, false), (16, false)], 25⟩) (k := ⟨25, [(7, false)], 14⟩) (fact1248 h) (fact300 h) rfl

private theorem fact1252 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(8, false), (14, true), (7, true), (16, true), (8, true), (4, true), (9, true)] 4).Valid g H input :=
  Fact.valid_relator h 4 (relator 30)
    (Array.mem_ofFn.mpr ⟨30, rfl⟩) true 3

private theorem fact1253 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(14, true), (7, true), (16, true), (8, true), (4, true), (9, true)] 4).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(8, false)], 125⟩) (k := ⟨4, [(8, false), (14, true), (7, true), (16, true), (8, true), (4, true), (9, true)], 4⟩) (fact1185 h) (fact1252 h) rfl [(14, true), (7, true), (16, true), (8, true), (4, true), (9, true)] rfl

private theorem fact1254 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(9, false), (4, false), (8, false), (16, false), (7, false), (14, false)] 125).Valid g H input :=
  Fact.valid_reverse (f := ⟨125, [(14, true), (7, true), (16, true), (8, true), (4, true), (9, true)], 4⟩) (fact1253 h)

private theorem fact1255 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [(14, false)] 125).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(9, false), (4, false), (8, false), (16, false), (7, false)], 14⟩) (k := ⟨4, [(9, false), (4, false), (8, false), (16, false), (7, false), (14, false)], 125⟩) (fact1250 h) (fact1254 h) rfl [(14, false)] rfl

private theorem fact1256 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(14, true)] 14).Valid g H input :=
  Fact.valid_reverse (f := ⟨14, [(14, false)], 125⟩) (fact1255 h)

private theorem fact1258 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [(14, false)] 125).Valid g H input :=
  Fact.valid_reverse (f := ⟨125, [(14, true)], 14⟩) (fact1256 h)

private theorem fact1262 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(9, false), (4, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(9, false)], 3⟩) (k := ⟨3, [(4, false)], 0⟩) (fact60 h) (fact44 h) rfl

private theorem fact1264 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(9, false), (4, false), (16, false)] 25).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(9, false), (4, false)], 0⟩) (k := ⟨0, [(16, false)], 25⟩) (fact1262 h) (fact287 h) rfl

private theorem fact1266 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(9, false), (4, false), (16, false), (7, false)] 14).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(9, false), (4, false), (16, false)], 25⟩) (k := ⟨25, [(7, false)], 14⟩) (fact1264 h) (fact300 h) rfl

private theorem fact1268 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(9, false), (4, false), (16, false), (7, false), (2, false)] 125).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(9, false), (4, false), (16, false), (7, false)], 14⟩) (k := ⟨14, [(2, false)], 125⟩) (fact1266 h) (fact1208 h) rfl

private theorem fact1270 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(8, false), (0, true), (2, true), (7, true), (16, true), (4, true), (9, true)] 4).Valid g H input :=
  Fact.valid_relator h 4 (relator 32)
    (Array.mem_ofFn.mpr ⟨32, rfl⟩) true 2

private theorem fact1271 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(0, true), (2, true), (7, true), (16, true), (4, true), (9, true)] 4).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(8, false)], 125⟩) (k := ⟨4, [(8, false), (0, true), (2, true), (7, true), (16, true), (4, true), (9, true)], 4⟩) (fact1185 h) (fact1270 h) rfl [(0, true), (2, true), (7, true), (16, true), (4, true), (9, true)] rfl

private theorem fact1272 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(9, false), (4, false), (16, false), (7, false), (2, false), (0, false)] 125).Valid g H input :=
  Fact.valid_reverse (f := ⟨125, [(0, true), (2, true), (7, true), (16, true), (4, true), (9, true)], 4⟩) (fact1271 h)

private theorem fact1273 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(0, false)] 125).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(9, false), (4, false), (16, false), (7, false), (2, false)], 125⟩) (k := ⟨4, [(9, false), (4, false), (16, false), (7, false), (2, false), (0, false)], 125⟩) (fact1268 h) (fact1272 h) rfl [(0, false)] rfl

private theorem fact1274 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(0, true)] 125).Valid g H input :=
  Fact.valid_reverse (f := ⟨125, [(0, false)], 125⟩) (fact1273 h)

private theorem fact1276 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(0, false)] 125).Valid g H input :=
  Fact.valid_reverse (f := ⟨125, [(0, true)], 125⟩) (fact1274 h)

private theorem fact1280 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, false), (8, true)] 125).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(0, false)], 14⟩) (k := ⟨14, [(8, true)], 125⟩) (fact142 h) (fact1224 h) rfl

private theorem fact1282 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, false), (8, true), (2, false)] 14).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(0, false), (8, true)], 125⟩) (k := ⟨125, [(2, false)], 14⟩) (fact1280 h) (fact1196 h) rfl

private theorem fact1284 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, false), (8, true), (2, false), (0, false)] 4).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(0, false), (8, true), (2, false)], 14⟩) (k := ⟨14, [(0, false)], 4⟩) (fact1282 h) (fact112 h) rfl

private theorem fact1286 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, false), (8, true), (2, false), (0, false), (3, false)] 116).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(0, false), (8, true), (2, false), (0, false)], 4⟩) (k := ⟨4, [(3, false)], 116⟩) (fact1284 h) (fact1115 h) rfl

private theorem fact1288 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(8, false), (6, true), (3, true), (0, true), (2, true), (8, false), (0, true)] 4).Valid g H input :=
  Fact.valid_relator h 4 (relator 36)
    (Array.mem_ofFn.mpr ⟨36, rfl⟩) false 2

private theorem fact1289 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(6, true), (3, true), (0, true), (2, true), (8, false), (0, true)] 4).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(8, false)], 125⟩) (k := ⟨4, [(8, false), (6, true), (3, true), (0, true), (2, true), (8, false), (0, true)], 4⟩) (fact1185 h) (fact1288 h) rfl [(6, true), (3, true), (0, true), (2, true), (8, false), (0, true)] rfl

private theorem fact1290 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, false), (8, true), (2, false), (0, false), (3, false), (6, false)] 125).Valid g H input :=
  Fact.valid_reverse (f := ⟨125, [(6, true), (3, true), (0, true), (2, true), (8, false), (0, true)], 4⟩) (fact1289 h)

private theorem fact1291 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 116 [(6, false)] 125).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(0, false), (8, true), (2, false), (0, false), (3, false)], 116⟩) (k := ⟨4, [(0, false), (8, true), (2, false), (0, false), (3, false), (6, false)], 125⟩) (fact1286 h) (fact1290 h) rfl [(6, false)] rfl

private theorem fact1292 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(6, true)] 116).Valid g H input :=
  Fact.valid_reverse (f := ⟨116, [(6, false)], 125⟩) (fact1291 h)

private theorem fact1294 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 116 [(6, false)] 125).Valid g H input :=
  Fact.valid_reverse (f := ⟨125, [(6, true)], 116⟩) (fact1292 h)

private theorem fact1323 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(11, false)] 130).Valid g H input :=
  Fact.valid_define g H input 4 (11, false) 130 (by decide +kernel)

private theorem fact1326 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 130 [(11, true)] 4).Valid g H input :=
  Fact.valid_reverse (f := ⟨4, [(11, false)], 130⟩) (fact1323 h)

private theorem fact1330 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, false), (4, true)] 11).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(0, false)], 14⟩) (k := ⟨14, [(4, true)], 11⟩) (fact142 h) (fact126 h) rfl

private theorem fact1332 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(11, false), (8, true), (4, false), (0, true)] 4).Valid g H input :=
  Fact.valid_relator h 4 (relator 11)
    (Array.mem_ofFn.mpr ⟨11, rfl⟩) false 0

private theorem fact1333 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 130 [(8, true), (4, false), (0, true)] 4).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(11, false)], 130⟩) (k := ⟨4, [(11, false), (8, true), (4, false), (0, true)], 4⟩) (fact1323 h) (fact1332 h) rfl [(8, true), (4, false), (0, true)] rfl

private theorem fact1334 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, false), (4, true), (8, false)] 130).Valid g H input :=
  Fact.valid_reverse (f := ⟨130, [(8, true), (4, false), (0, true)], 4⟩) (fact1333 h)

private theorem fact1335 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 11 [(8, false)] 130).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(0, false), (4, true)], 11⟩) (k := ⟨4, [(0, false), (4, true), (8, false)], 130⟩) (fact1330 h) (fact1334 h) rfl [(8, false)] rfl

private theorem fact1336 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 130 [(8, true)] 11).Valid g H input :=
  Fact.valid_reverse (f := ⟨11, [(8, false)], 130⟩) (fact1335 h)

private theorem fact1338 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 11 [(8, false)] 130).Valid g H input :=
  Fact.valid_reverse (f := ⟨130, [(8, true)], 11⟩) (fact1336 h)

private theorem fact1360 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(4, true), (0, true)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(4, true)], 0⟩) (k := ⟨0, [(0, true)], 0⟩) (fact48 h) (fact0 h) rfl

private theorem fact1362 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(4, true), (0, true), (8, true)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(4, true), (0, true)], 0⟩) (k := ⟨0, [(8, true)], 0⟩) (fact1360 h) (fact18 h) rfl

private theorem fact1364 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(4, true), (0, true), (8, true), (9, false)] 11).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(4, true), (0, true), (8, true)], 0⟩) (k := ⟨0, [(9, false)], 11⟩) (fact1362 h) (fact87 h) rfl

private theorem fact1366 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(4, true), (0, true), (8, true), (9, false), (8, false)] 130).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(4, true), (0, true), (8, true), (9, false)], 11⟩) (k := ⟨11, [(8, false)], 130⟩) (fact1364 h) (fact1338 h) rfl

private theorem fact1368 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(11, false), (1, false), (8, true), (9, true), (8, false), (0, false), (4, false)] 4).Valid g H input :=
  Fact.valid_relator h 4 (relator 35)
    (Array.mem_ofFn.mpr ⟨35, rfl⟩) false 0

private theorem fact1369 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 130 [(1, false), (8, true), (9, true), (8, false), (0, false), (4, false)] 4).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(11, false)], 130⟩) (k := ⟨4, [(11, false), (1, false), (8, true), (9, true), (8, false), (0, false), (4, false)], 4⟩) (fact1323 h) (fact1368 h) rfl [(1, false), (8, true), (9, true), (8, false), (0, false), (4, false)] rfl

private theorem fact1370 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(4, true), (0, true), (8, true), (9, false), (8, false), (1, true)] 130).Valid g H input :=
  Fact.valid_reverse (f := ⟨130, [(1, false), (8, true), (9, true), (8, false), (0, false), (4, false)], 4⟩) (fact1369 h)

private theorem fact1371 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 130 [(1, true)] 130).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(4, true), (0, true), (8, true), (9, false), (8, false)], 130⟩) (k := ⟨4, [(4, true), (0, true), (8, true), (9, false), (8, false), (1, true)], 130⟩) (fact1366 h) (fact1370 h) rfl [(1, true)] rfl

private theorem fact1372 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 130 [(1, false)] 130).Valid g H input :=
  Fact.valid_reverse (f := ⟨130, [(1, true)], 130⟩) (fact1371 h)

private theorem fact1377 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 130 [(11, true), (4, true)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨130, [(11, true)], 4⟩) (k := ⟨4, [(4, true)], 0⟩) (fact1326 h) (fact48 h) rfl

private theorem fact1379 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 130 [(11, true), (4, true), (9, true)] 10).Valid g H input :=
  Fact.valid_trans (f := ⟨130, [(11, true), (4, true)], 0⟩) (k := ⟨0, [(9, true)], 10⟩) (fact1377 h) (fact83 h) rfl

private theorem fact1382 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 130 [(11, true), (4, true), (9, true), (0, true), (1, true)] 130).Valid g H input :=
  Fact.valid_relator h 130 (relator 18)
    (Array.mem_ofFn.mpr ⟨18, rfl⟩) true 4

private theorem fact1383 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 10 [(0, true), (1, true)] 130).Valid g H input :=
  Fact.valid_cancel (f := ⟨130, [(11, true), (4, true), (9, true)], 10⟩) (k := ⟨130, [(11, true), (4, true), (9, true), (0, true), (1, true)], 130⟩) (fact1379 h) (fact1382 h) rfl [(0, true), (1, true)] rfl

private theorem fact1384 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 130 [(1, false), (0, false)] 10).Valid g H input :=
  Fact.valid_reverse (f := ⟨10, [(0, true), (1, true)], 130⟩) (fact1383 h)

private theorem fact1385 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 130 [(0, false)] 10).Valid g H input :=
  Fact.valid_cancel (f := ⟨130, [(1, false)], 130⟩) (k := ⟨130, [(1, false), (0, false)], 10⟩) (fact1372 h) (fact1384 h) rfl [(0, false)] rfl

private theorem fact1386 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 10 [(0, true)] 130).Valid g H input :=
  Fact.valid_reverse (f := ⟨130, [(0, false)], 10⟩) (fact1385 h)

private theorem fact1407 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(12, false)] 132).Valid g H input :=
  Fact.valid_define g H input 4 (12, false) 132 (by decide +kernel)

private theorem fact1419 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(14, true)] 135).Valid g H input :=
  Fact.valid_define g H input 4 (14, true) 135 (by decide +kernel)

private theorem fact1426 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true), (4, true)] 11).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(0, true)], 14⟩) (k := ⟨14, [(4, true)], 11⟩) (fact114 h) (fact126 h) rfl

private theorem fact1428 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true), (4, true), (9, true)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(0, true), (4, true)], 11⟩) (k := ⟨11, [(9, true)], 0⟩) (fact1426 h) (fact90 h) rfl

private theorem fact1430 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true), (4, true), (9, true), (4, true)] 3).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(0, true), (4, true), (9, true)], 0⟩) (k := ⟨0, [(4, true)], 3⟩) (fact1428 h) (fact41 h) rfl

private theorem fact1432 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true), (4, true), (9, true), (4, true), (9, true)] 4).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(0, true), (4, true), (9, true), (4, true)], 3⟩) (k := ⟨3, [(9, true)], 4⟩) (fact1430 h) (fact62 h) rfl

private theorem fact1434 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true), (4, true), (9, true), (4, true), (9, true), (14, true)] 135).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(0, true), (4, true), (9, true), (4, true), (9, true)], 4⟩) (k := ⟨4, [(14, true)], 135⟩) (fact1432 h) (fact1419 h) rfl

private theorem fact1436 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(14, true), (0, false), (14, false), (9, false), (4, false), (9, false), (4, false), (0, false)] 4).Valid g H input :=
  Fact.valid_relator h 4 (relator 38)
    (Array.mem_ofFn.mpr ⟨38, rfl⟩) false 6

private theorem fact1437 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 135 [(0, false), (14, false), (9, false), (4, false), (9, false), (4, false), (0, false)] 4).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(14, true)], 135⟩) (k := ⟨4, [(14, true), (0, false), (14, false), (9, false), (4, false), (9, false), (4, false), (0, false)], 4⟩) (fact1419 h) (fact1436 h) rfl [(0, false), (14, false), (9, false), (4, false), (9, false), (4, false), (0, false)] rfl

private theorem fact1438 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true), (4, true), (9, true), (4, true), (9, true), (14, true), (0, true)] 135).Valid g H input :=
  Fact.valid_reverse (f := ⟨135, [(0, false), (14, false), (9, false), (4, false), (9, false), (4, false), (0, false)], 4⟩) (fact1437 h)

private theorem fact1439 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 135 [(0, true)] 135).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(0, true), (4, true), (9, true), (4, true), (9, true), (14, true)], 135⟩) (k := ⟨4, [(0, true), (4, true), (9, true), (4, true), (9, true), (14, true), (0, true)], 135⟩) (fact1434 h) (fact1438 h) rfl [(0, true)] rfl

private theorem fact1440 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 135 [(0, false)] 135).Valid g H input :=
  Fact.valid_reverse (f := ⟨135, [(0, true)], 135⟩) (fact1439 h)

private theorem fact1465 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(16, true)] 139).Valid g H input :=
  Fact.valid_define g H input 4 (16, true) 139 (by decide +kernel)

private theorem fact1473 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 5 [(0, true)] 141).Valid g H input :=
  Fact.valid_define g H input 5 (0, true) 141 (by decide +kernel)

private theorem fact1475 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 141 [] 141).Valid g H input :=
  Fact.valid_refl g H input 141

private theorem fact1479 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 5 [(0, true), (0, true)] 5).Valid g H input :=
  Fact.valid_relator h 5 (relator 2)
    (Array.mem_ofFn.mpr ⟨2, rfl⟩) true 0

private theorem fact1480 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 141 [(0, true)] 5).Valid g H input :=
  Fact.valid_cancel (f := ⟨5, [(0, true)], 141⟩) (k := ⟨5, [(0, true), (0, true)], 5⟩) (fact1473 h) (fact1479 h) rfl [(0, true)] rfl

private theorem fact1481 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 5 [(0, false)] 141).Valid g H input :=
  Fact.valid_reverse (f := ⟨141, [(0, true)], 5⟩) (fact1480 h)

private theorem fact1482 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 5 [(0, false)] 141).Valid g H input :=
  Fact.valid_cancel (f := ⟨5, [], 5⟩) (k := ⟨5, [(0, false)], 141⟩) (fact65 h) (fact1481 h) rfl [(0, false)] rfl

private theorem fact1483 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 141 [(0, true)] 5).Valid g H input :=
  Fact.valid_reverse (f := ⟨5, [(0, false)], 141⟩) (fact1482 h)

private theorem fact1488 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 141 [(0, true), (5, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨141, [(0, true)], 5⟩) (k := ⟨5, [(5, false)], 0⟩) (fact1483 h) (fact66 h) rfl

private theorem fact1490 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 141 [(0, true), (5, false), (8, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨141, [(0, true), (5, false)], 0⟩) (k := ⟨0, [(8, false)], 0⟩) (fact1488 h) (fact20 h) rfl

private theorem fact1492 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 141 [(0, true), (5, false), (8, false), (9, true)] 10).Valid g H input :=
  Fact.valid_trans (f := ⟨141, [(0, true), (5, false), (8, false)], 0⟩) (k := ⟨0, [(9, true)], 10⟩) (fact1490 h) (fact83 h) rfl

private theorem fact1494 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 141 [(0, true), (5, false), (8, false), (9, true), (0, true)] 130).Valid g H input :=
  Fact.valid_trans (f := ⟨141, [(0, true), (5, false), (8, false), (9, true)], 10⟩) (k := ⟨10, [(0, true)], 130⟩) (fact1492 h) (fact1386 h) rfl

private theorem fact1496 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 141 [(0, true), (5, false), (8, false), (9, true), (0, true), (11, true)] 4).Valid g H input :=
  Fact.valid_trans (f := ⟨141, [(0, true), (5, false), (8, false), (9, true), (0, true)], 130⟩) (k := ⟨130, [(11, true)], 4⟩) (fact1494 h) (fact1326 h) rfl

private theorem fact1498 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 141 [(0, true), (5, false), (8, false), (9, true), (0, true), (11, true), (1, true)] 113).Valid g H input :=
  Fact.valid_trans (f := ⟨141, [(0, true), (5, false), (8, false), (9, true), (0, true), (11, true)], 4⟩) (k := ⟨4, [(1, true)], 113⟩) (fact1496 h) (fact1037 h) rfl

private theorem fact1500 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 141 [(0, true), (5, false), (8, false), (9, true), (0, true), (11, true), (1, true), (5, true)] 141).Valid g H input :=
  Fact.valid_relator h 141 (relator 39)
    (Array.mem_ofFn.mpr ⟨39, rfl⟩) true 2

private theorem fact1501 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 113 [(5, true)] 141).Valid g H input :=
  Fact.valid_cancel (f := ⟨141, [(0, true), (5, false), (8, false), (9, true), (0, true), (11, true), (1, true)], 113⟩) (k := ⟨141, [(0, true), (5, false), (8, false), (9, true), (0, true), (11, true), (1, true), (5, true)], 141⟩) (fact1498 h) (fact1500 h) rfl [(5, true)] rfl

private theorem fact1502 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 141 [(5, false)] 113).Valid g H input :=
  Fact.valid_reverse (f := ⟨113, [(5, true)], 141⟩) (fact1501 h)

private theorem fact1503 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 141 [(5, false)] 113).Valid g H input :=
  Fact.valid_cancel (f := ⟨141, [], 141⟩) (k := ⟨141, [(5, false)], 113⟩) (fact1475 h) (fact1502 h) rfl [(5, false)] rfl

private theorem fact1504 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 113 [(5, true)] 141).Valid g H input :=
  Fact.valid_reverse (f := ⟨141, [(5, false)], 113⟩) (fact1503 h)

private theorem fact1506 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 141 [(5, false)] 113).Valid g H input :=
  Fact.valid_reverse (f := ⟨113, [(5, true)], 141⟩) (fact1504 h)

private theorem fact1647 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 5 [(11, false)] 160).Valid g H input :=
  Fact.valid_define g H input 5 (11, false) 160 (by decide +kernel)

private theorem fact1650 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 160 [(11, true)] 5).Valid g H input :=
  Fact.valid_reverse (f := ⟨5, [(11, false)], 160⟩) (fact1647 h)

private theorem fact1654 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 5 [(5, false), (1, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨5, [(5, false)], 0⟩) (k := ⟨0, [(1, false)], 0⟩) (fact66 h) (fact6 h) rfl

private theorem fact1656 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 5 [(5, false), (1, false), (0, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨5, [(5, false), (1, false)], 0⟩) (k := ⟨0, [(0, false)], 0⟩) (fact1654 h) (fact3 h) rfl

private theorem fact1658 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 5 [(5, false), (1, false), (0, false), (10, true)] 12).Valid g H input :=
  Fact.valid_trans (f := ⟨5, [(5, false), (1, false), (0, false)], 0⟩) (k := ⟨0, [(10, true)], 12⟩) (fact1656 h) (fact91 h) rfl

private theorem fact1660 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 5 [(11, false), (7, false), (10, false), (0, true), (1, true), (5, true)] 5).Valid g H input :=
  Fact.valid_relator h 5 (relator 29)
    (Array.mem_ofFn.mpr ⟨29, rfl⟩) false 0

private theorem fact1661 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 160 [(7, false), (10, false), (0, true), (1, true), (5, true)] 5).Valid g H input :=
  Fact.valid_cancel (f := ⟨5, [(11, false)], 160⟩) (k := ⟨5, [(11, false), (7, false), (10, false), (0, true), (1, true), (5, true)], 5⟩) (fact1647 h) (fact1660 h) rfl [(7, false), (10, false), (0, true), (1, true), (5, true)] rfl

private theorem fact1662 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 5 [(5, false), (1, false), (0, false), (10, true), (7, true)] 160).Valid g H input :=
  Fact.valid_reverse (f := ⟨160, [(7, false), (10, false), (0, true), (1, true), (5, true)], 5⟩) (fact1661 h)

private theorem fact1663 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 12 [(7, true)] 160).Valid g H input :=
  Fact.valid_cancel (f := ⟨5, [(5, false), (1, false), (0, false), (10, true)], 12⟩) (k := ⟨5, [(5, false), (1, false), (0, false), (10, true), (7, true)], 160⟩) (fact1658 h) (fact1662 h) rfl [(7, true)] rfl

private theorem fact1664 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 160 [(7, false)] 12).Valid g H input :=
  Fact.valid_reverse (f := ⟨12, [(7, true)], 160⟩) (fact1663 h)

private theorem fact1666 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 12 [(7, true)] 160).Valid g H input :=
  Fact.valid_reverse (f := ⟨160, [(7, false)], 12⟩) (fact1664 h)

private theorem fact1701 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 5 [(15, true)] 167).Valid g H input :=
  Fact.valid_define g H input 5 (15, true) 167 (by decide +kernel)

private theorem fact1703 (_ : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 167 [] 167).Valid g H input :=
  Fact.valid_refl g H input 167

private theorem fact1704 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 167 [(15, false)] 5).Valid g H input :=
  Fact.valid_reverse (f := ⟨5, [(15, true)], 167⟩) (fact1701 h)

private theorem fact1708 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 5 [(5, false), (9, false)] 11).Valid g H input :=
  Fact.valid_trans (f := ⟨5, [(5, false)], 0⟩) (k := ⟨0, [(9, false)], 11⟩) (fact66 h) (fact87 h) rfl

private theorem fact1710 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 5 [(5, false), (9, false), (4, false)] 14).Valid g H input :=
  Fact.valid_trans (f := ⟨5, [(5, false), (9, false)], 11⟩) (k := ⟨11, [(4, false)], 14⟩) (fact1708 h) (fact128 h) rfl

private theorem fact1712 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 5 [(5, false), (9, false), (4, false), (14, false)] 125).Valid g H input :=
  Fact.valid_trans (f := ⟨5, [(5, false), (9, false), (4, false)], 14⟩) (k := ⟨14, [(14, false)], 125⟩) (fact1710 h) (fact1258 h) rfl

private theorem fact1714 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 5 [(15, true), (16, true), (14, true), (4, true), (9, true), (5, true)] 5).Valid g H input :=
  Fact.valid_relator h 5 (relator 22)
    (Array.mem_ofFn.mpr ⟨22, rfl⟩) true 4

private theorem fact1715 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 167 [(16, true), (14, true), (4, true), (9, true), (5, true)] 5).Valid g H input :=
  Fact.valid_cancel (f := ⟨5, [(15, true)], 167⟩) (k := ⟨5, [(15, true), (16, true), (14, true), (4, true), (9, true), (5, true)], 5⟩) (fact1701 h) (fact1714 h) rfl [(16, true), (14, true), (4, true), (9, true), (5, true)] rfl

private theorem fact1716 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 5 [(5, false), (9, false), (4, false), (14, false), (16, false)] 167).Valid g H input :=
  Fact.valid_reverse (f := ⟨167, [(16, true), (14, true), (4, true), (9, true), (5, true)], 5⟩) (fact1715 h)

private theorem fact1717 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(16, false)] 167).Valid g H input :=
  Fact.valid_cancel (f := ⟨5, [(5, false), (9, false), (4, false), (14, false)], 125⟩) (k := ⟨5, [(5, false), (9, false), (4, false), (14, false), (16, false)], 167⟩) (fact1712 h) (fact1716 h) rfl [(16, false)] rfl

private theorem fact1718 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 167 [(16, true)] 125).Valid g H input :=
  Fact.valid_reverse (f := ⟨125, [(16, false)], 167⟩) (fact1717 h)

private theorem fact1720 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(16, false)] 167).Valid g H input :=
  Fact.valid_reverse (f := ⟨167, [(16, true)], 125⟩) (fact1718 h)

private theorem fact1723 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 5 [(15, true), (16, true)] 125).Valid g H input :=
  Fact.valid_trans (f := ⟨5, [(15, true)], 167⟩) (k := ⟨167, [(16, true)], 125⟩) (fact1701 h) (fact1718 h) rfl

private theorem fact1725 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 5 [(15, true), (16, true), (7, true)] 15).Valid g H input :=
  Fact.valid_trans (f := ⟨5, [(15, true), (16, true)], 125⟩) (k := ⟨125, [(7, true)], 15⟩) (fact1723 h) (fact1238 h) rfl

private theorem fact1727 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 5 [(15, true), (16, true), (7, true), (11, true)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨5, [(15, true), (16, true), (7, true)], 15⟩) (k := ⟨15, [(11, true)], 0⟩) (fact1725 h) (fact162 h) rfl

private theorem fact1729 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 5 [(15, true), (16, true), (7, true), (11, true), (8, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨5, [(15, true), (16, true), (7, true), (11, true)], 0⟩) (k := ⟨0, [(8, false)], 0⟩) (fact1727 h) (fact20 h) rfl

private theorem fact1731 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 5 [(15, true), (16, true), (7, true), (11, true), (8, false), (4, true)] 3).Valid g H input :=
  Fact.valid_trans (f := ⟨5, [(15, true), (16, true), (7, true), (11, true), (8, false)], 0⟩) (k := ⟨0, [(4, true)], 3⟩) (fact1729 h) (fact41 h) rfl

private theorem fact1733 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 5 [(15, true), (16, true), (7, true), (11, true), (8, false), (4, true), (9, true)] 4).Valid g H input :=
  Fact.valid_trans (f := ⟨5, [(15, true), (16, true), (7, true), (11, true), (8, false), (4, true)], 3⟩) (k := ⟨3, [(9, true)], 4⟩) (fact1731 h) (fact62 h) rfl

private theorem fact1735 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 5 [(15, true), (16, true), (7, true), (11, true), (8, false), (4, true), (9, true), (5, true)] 118).Valid g H input :=
  Fact.valid_trans (f := ⟨5, [(15, true), (16, true), (7, true), (11, true), (8, false), (4, true), (9, true)], 4⟩) (k := ⟨4, [(5, true)], 118⟩) (fact1733 h) (fact1137 h) rfl

private theorem fact1738 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 5 [(15, true), (16, true), (7, true), (11, true), (8, false), (4, true), (9, true), (5, true), (0, false)] 5).Valid g H input :=
  Fact.valid_relator h 5 (relator 40)
    (Array.mem_ofFn.mpr ⟨40, rfl⟩) true 7

private theorem fact1739 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 118 [(0, false)] 5).Valid g H input :=
  Fact.valid_cancel (f := ⟨5, [(15, true), (16, true), (7, true), (11, true), (8, false), (4, true), (9, true), (5, true)], 118⟩) (k := ⟨5, [(15, true), (16, true), (7, true), (11, true), (8, false), (4, true), (9, true), (5, true), (0, false)], 5⟩) (fact1735 h) (fact1738 h) rfl [(0, false)] rfl

private theorem fact1740 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 5 [(0, true)] 118).Valid g H input :=
  Fact.valid_reverse (f := ⟨118, [(0, false)], 5⟩) (fact1739 h)

private theorem fact1741 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 141 [] 118).Valid g H input :=
  Fact.valid_cancel (f := ⟨5, [(0, true)], 141⟩) (k := ⟨5, [(0, true)], 118⟩) (fact1473 h) (fact1740 h) rfl [] rfl

private theorem fact1742 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 118 [] 141).Valid g H input :=
  Fact.valid_reverse (f := ⟨141, [], 118⟩) (fact1741 h)

private theorem fact1744 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 141 [] 118).Valid g H input :=
  Fact.valid_reverse (f := ⟨118, [], 141⟩) (fact1742 h)

private theorem fact1753 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 118 [] 141).Valid g H input :=
  Fact.valid_reverse (f := ⟨141, [], 118⟩) (fact1744 h)

private theorem fact1754 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 118 [(5, false)] 113).Valid g H input :=
  Fact.valid_trans (f := ⟨118, [], 141⟩) (k := ⟨141, [(5, false)], 113⟩) (fact1753 h) (fact1506 h) rfl

private theorem fact1756 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [] 113).Valid g H input :=
  Fact.valid_cancel (f := ⟨118, [(5, false)], 4⟩) (k := ⟨118, [(5, false)], 113⟩) (fact1140 h) (fact1754 h) rfl [] rfl

private theorem fact1795 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 113 [] 4).Valid g H input :=
  Fact.valid_reverse (f := ⟨4, [], 113⟩) (fact1756 h)

private theorem fact1811 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [] 113).Valid g H input :=
  Fact.valid_reverse (f := ⟨113, [], 4⟩) (fact1795 h)

private theorem fact1812 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(7, false)] 114).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [], 113⟩) (k := ⟨113, [(7, false)], 114⟩) (fact1811 h) (fact1110 h) rfl

private theorem fact1814 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 123 [] 114).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(7, false)], 123⟩) (k := ⟨4, [(7, false)], 114⟩) (fact1157 h) (fact1812 h) rfl [] rfl

private theorem fact1819 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [] 113).Valid g H input :=
  Fact.valid_reverse (f := ⟨113, [], 4⟩) (fact1795 h)

private theorem fact1820 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(16, true)] 20).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [], 113⟩) (k := ⟨113, [(16, true)], 20⟩) (fact1819 h) (fact1067 h) rfl

private theorem fact1822 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 139 [] 20).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(16, true)], 139⟩) (k := ⟨4, [(16, true)], 20⟩) (fact1465 h) (fact1820 h) rfl [] rfl

private theorem fact1832 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, true)] 4).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(1, true)], 113⟩) (k := ⟨113, [], 4⟩) (fact1037 h) (fact1795 h) rfl

private theorem fact1838 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false)] 4).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(1, false)], 113⟩) (k := ⟨113, [], 4⟩) (fact1049 h) (fact1795 h) rfl

private theorem fact1997 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 20 [] 139).Valid g H input :=
  Fact.valid_reverse (f := ⟨139, [], 20⟩) (fact1822 h)

private theorem fact1998 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 139 [] 20).Valid g H input :=
  Fact.valid_reverse (f := ⟨20, [], 139⟩) (fact1997 h)

private theorem fact2094 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 114 [] 123).Valid g H input :=
  Fact.valid_reverse (f := ⟨123, [], 114⟩) (fact1814 h)

private theorem fact2095 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 123 [] 114).Valid g H input :=
  Fact.valid_reverse (f := ⟨114, [], 123⟩) (fact2094 h)

private theorem fact2118 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 114 [(7, true)] 4).Valid g H input :=
  Fact.valid_trans (f := ⟨114, [(7, true)], 113⟩) (k := ⟨113, [], 4⟩) (fact1108 h) (fact1795 h) rfl

private theorem fact2139 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 167 [(16, true), (7, true)] 15).Valid g H input :=
  Fact.valid_trans (f := ⟨167, [(16, true)], 125⟩) (k := ⟨125, [(7, true)], 15⟩) (fact1718 h) (fact1238 h) rfl

private theorem fact2141 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 167 [(16, true), (7, true), (1, false)] 14).Valid g H input :=
  Fact.valid_trans (f := ⟨167, [(16, true), (7, true)], 15⟩) (k := ⟨15, [(1, false)], 14⟩) (fact2139 h) (fact172 h) rfl

private theorem fact2143 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 167 [(16, true), (7, true), (1, false), (0, false)] 4).Valid g H input :=
  Fact.valid_trans (f := ⟨167, [(16, true), (7, true), (1, false)], 14⟩) (k := ⟨14, [(0, false)], 4⟩) (fact2141 h) (fact112 h) rfl

private theorem fact2145 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(16, true)] 20).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(16, true)], 139⟩) (k := ⟨139, [], 20⟩) (fact1465 h) (fact1998 h) rfl

private theorem fact2146 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 167 [(16, true), (7, true), (1, false), (0, false), (16, true)] 20).Valid g H input :=
  Fact.valid_trans (f := ⟨167, [(16, true), (7, true), (1, false), (0, false)], 4⟩) (k := ⟨4, [(16, true)], 20⟩) (fact2143 h) (fact2145 h) rfl

private theorem fact2148 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 167 [(16, true), (7, true), (1, false), (0, false), (16, true), (14, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨167, [(16, true), (7, true), (1, false), (0, false), (16, true)], 20⟩) (k := ⟨20, [(14, false)], 0⟩) (fact2146 h) (fact236 h) rfl

private theorem fact2150 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 167 [(16, true), (7, true), (1, false), (0, false), (16, true), (14, false), (0, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨167, [(16, true), (7, true), (1, false), (0, false), (16, true), (14, false)], 0⟩) (k := ⟨0, [(0, false)], 0⟩) (fact2148 h) (fact3 h) rfl

private theorem fact2152 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 167 [(16, true), (7, true), (1, false), (0, false), (16, true), (14, false), (0, false), (1, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨167, [(16, true), (7, true), (1, false), (0, false), (16, true), (14, false), (0, false)], 0⟩) (k := ⟨0, [(1, false)], 0⟩) (fact2150 h) (fact6 h) rfl

private theorem fact2154 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 167 [(16, true), (7, true), (1, false), (0, false), (16, true), (14, false), (0, false), (1, false), (2, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨167, [(16, true), (7, true), (1, false), (0, false), (16, true), (14, false), (0, false), (1, false)], 0⟩) (k := ⟨0, [(2, false)], 0⟩) (fact2152 h) (fact9 h) rfl

private theorem fact2156 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 167 [(16, true), (7, true), (1, false), (0, false), (16, true), (14, false), (0, false), (1, false), (2, false), (1, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨167, [(16, true), (7, true), (1, false), (0, false), (16, true), (14, false), (0, false), (1, false), (2, false)], 0⟩) (k := ⟨0, [(1, false)], 0⟩) (fact2154 h) (fact6 h) rfl

private theorem fact2158 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 167 [(16, true), (7, true), (1, false), (0, false), (16, true), (14, false), (0, false), (1, false), (2, false), (1, false), (10, true)] 12).Valid g H input :=
  Fact.valid_trans (f := ⟨167, [(16, true), (7, true), (1, false), (0, false), (16, true), (14, false), (0, false), (1, false), (2, false), (1, false)], 0⟩) (k := ⟨0, [(10, true)], 12⟩) (fact2156 h) (fact91 h) rfl

private theorem fact2160 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 167 [(16, true), (7, true), (1, false), (0, false), (16, true), (14, false), (0, false), (1, false), (2, false), (1, false), (10, true), (14, true)] 167).Valid g H input :=
  Fact.valid_relator h 167 (relator 46)
    (Array.mem_ofFn.mpr ⟨46, rfl⟩) true 11

private theorem fact2161 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 12 [(14, true)] 167).Valid g H input :=
  Fact.valid_cancel (f := ⟨167, [(16, true), (7, true), (1, false), (0, false), (16, true), (14, false), (0, false), (1, false), (2, false), (1, false), (10, true)], 12⟩) (k := ⟨167, [(16, true), (7, true), (1, false), (0, false), (16, true), (14, false), (0, false), (1, false), (2, false), (1, false), (10, true), (14, true)], 167⟩) (fact2158 h) (fact2160 h) rfl [(14, true)] rfl

private theorem fact2162 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 167 [(14, false)] 12).Valid g H input :=
  Fact.valid_reverse (f := ⟨12, [(14, true)], 167⟩) (fact2161 h)

private theorem fact2163 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 167 [(14, false)] 12).Valid g H input :=
  Fact.valid_cancel (f := ⟨167, [], 167⟩) (k := ⟨167, [(14, false)], 12⟩) (fact1703 h) (fact2162 h) rfl [(14, false)] rfl

private theorem fact2164 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 12 [(14, true)] 167).Valid g H input :=
  Fact.valid_reverse (f := ⟨167, [(14, false)], 12⟩) (fact2163 h)

private theorem fact2166 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 167 [(14, false)] 12).Valid g H input :=
  Fact.valid_reverse (f := ⟨12, [(14, true)], 167⟩) (fact2164 h)

private theorem fact2169 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(16, false), (14, false)] 12).Valid g H input :=
  Fact.valid_trans (f := ⟨125, [(16, false)], 167⟩) (k := ⟨167, [(14, false)], 12⟩) (fact1720 h) (fact2166 h) rfl

private theorem fact2172 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(8, true), (1, true)] 4).Valid g H input :=
  Fact.valid_trans (f := ⟨125, [(8, true)], 4⟩) (k := ⟨4, [(1, true)], 4⟩) (fact1188 h) (fact1832 h) rfl

private theorem fact2174 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(8, true), (1, true), (0, true)] 14).Valid g H input :=
  Fact.valid_trans (f := ⟨125, [(8, true), (1, true)], 4⟩) (k := ⟨4, [(0, true)], 14⟩) (fact2172 h) (fact114 h) rfl

private theorem fact2176 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(16, false), (14, false), (6, true), (0, false), (1, false), (8, false)] 125).Valid g H input :=
  Fact.valid_relator h 125 (relator 23)
    (Array.mem_ofFn.mpr ⟨23, rfl⟩) false 0

private theorem fact2177 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 12 [(6, true), (0, false), (1, false), (8, false)] 125).Valid g H input :=
  Fact.valid_cancel (f := ⟨125, [(16, false), (14, false)], 12⟩) (k := ⟨125, [(16, false), (14, false), (6, true), (0, false), (1, false), (8, false)], 125⟩) (fact2169 h) (fact2176 h) rfl [(6, true), (0, false), (1, false), (8, false)] rfl

private theorem fact2178 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(8, true), (1, true), (0, true), (6, false)] 12).Valid g H input :=
  Fact.valid_reverse (f := ⟨12, [(6, true), (0, false), (1, false), (8, false)], 125⟩) (fact2177 h)

private theorem fact2179 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [(6, false)] 12).Valid g H input :=
  Fact.valid_cancel (f := ⟨125, [(8, true), (1, true), (0, true)], 14⟩) (k := ⟨125, [(8, true), (1, true), (0, true), (6, false)], 12⟩) (fact2174 h) (fact2178 h) rfl [(6, false)] rfl

private theorem fact2180 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 12 [(6, true)] 14).Valid g H input :=
  Fact.valid_reverse (f := ⟨14, [(6, false)], 12⟩) (fact2179 h)

private theorem fact2185 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(16, false), (14, false)] 12).Valid g H input :=
  Fact.valid_trans (f := ⟨125, [(16, false)], 167⟩) (k := ⟨167, [(14, false)], 12⟩) (fact1720 h) (fact2166 h) rfl

private theorem fact2187 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(16, false), (14, false), (6, true)] 14).Valid g H input :=
  Fact.valid_trans (f := ⟨125, [(16, false), (14, false)], 12⟩) (k := ⟨12, [(6, true)], 14⟩) (fact2185 h) (fact2180 h) rfl

private theorem fact2189 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(16, false), (14, false), (6, true), (11, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨125, [(16, false), (14, false), (6, true)], 14⟩) (k := ⟨14, [(11, false)], 0⟩) (fact2187 h) (fact102 h) rfl

private theorem fact2191 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(16, false), (14, false), (6, true), (11, false), (11, false)] 15).Valid g H input :=
  Fact.valid_trans (f := ⟨125, [(16, false), (14, false), (6, true), (11, false)], 0⟩) (k := ⟨0, [(11, false)], 15⟩) (fact2189 h) (fact159 h) rfl

private theorem fact2193 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(16, false), (14, false), (6, true), (11, false), (11, false), (8, true)] 3).Valid g H input :=
  Fact.valid_trans (f := ⟨125, [(16, false), (14, false), (6, true), (11, false), (11, false)], 15⟩) (k := ⟨15, [(8, true)], 3⟩) (fact2191 h) (fact196 h) rfl

private theorem fact2195 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(16, false), (14, false), (6, true), (11, false), (11, false), (8, true), (16, false)] 112).Valid g H input :=
  Fact.valid_trans (f := ⟨125, [(16, false), (14, false), (6, true), (11, false), (11, false), (8, true)], 3⟩) (k := ⟨3, [(16, false)], 112⟩) (fact2193 h) (fact1033 h) rfl

private theorem fact2198 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(0, false), (14, true)] 14).Valid g H input :=
  Fact.valid_trans (f := ⟨125, [(0, false)], 125⟩) (k := ⟨125, [(14, true)], 14⟩) (fact1276 h) (fact1256 h) rfl

private theorem fact2200 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(0, false), (14, true), (8, true)] 125).Valid g H input :=
  Fact.valid_trans (f := ⟨125, [(0, false), (14, true)], 14⟩) (k := ⟨14, [(8, true)], 125⟩) (fact2198 h) (fact1224 h) rfl

private theorem fact2202 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(0, false), (14, true), (8, true), (14, true)] 14).Valid g H input :=
  Fact.valid_trans (f := ⟨125, [(0, false), (14, true), (8, true)], 125⟩) (k := ⟨125, [(14, true)], 14⟩) (fact2200 h) (fact1256 h) rfl

private theorem fact2204 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(0, false), (14, true), (8, true), (14, true), (0, false)] 4).Valid g H input :=
  Fact.valid_trans (f := ⟨125, [(0, false), (14, true), (8, true), (14, true)], 14⟩) (k := ⟨14, [(0, false)], 4⟩) (fact2202 h) (fact112 h) rfl

private theorem fact2206 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(0, false), (14, true), (8, true), (14, true), (0, false), (14, true)] 135).Valid g H input :=
  Fact.valid_trans (f := ⟨125, [(0, false), (14, true), (8, true), (14, true), (0, false)], 4⟩) (k := ⟨4, [(14, true)], 135⟩) (fact2204 h) (fact1419 h) rfl

private theorem fact2208 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(0, false), (14, true), (8, true), (14, true), (0, false), (14, true), (0, false)] 135).Valid g H input :=
  Fact.valid_trans (f := ⟨125, [(0, false), (14, true), (8, true), (14, true), (0, false), (14, true)], 135⟩) (k := ⟨135, [(0, false)], 135⟩) (fact2206 h) (fact1440 h) rfl

private theorem fact2210 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(16, false), (14, false), (6, true), (11, false), (11, false), (8, true), (16, false), (11, true), (0, true), (14, false), (0, true), (14, false), (8, false), (14, false), (0, true)] 125).Valid g H input :=
  Fact.valid_relator h 125 (relator 48)
    (Array.mem_ofFn.mpr ⟨48, rfl⟩) false 0

private theorem fact2211 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 112 [(11, true), (0, true), (14, false), (0, true), (14, false), (8, false), (14, false), (0, true)] 125).Valid g H input :=
  Fact.valid_cancel (f := ⟨125, [(16, false), (14, false), (6, true), (11, false), (11, false), (8, true), (16, false)], 112⟩) (k := ⟨125, [(16, false), (14, false), (6, true), (11, false), (11, false), (8, true), (16, false), (11, true), (0, true), (14, false), (0, true), (14, false), (8, false), (14, false), (0, true)], 125⟩) (fact2195 h) (fact2210 h) rfl [(11, true), (0, true), (14, false), (0, true), (14, false), (8, false), (14, false), (0, true)] rfl

private theorem fact2212 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(0, false), (14, true), (8, true), (14, true), (0, false), (14, true), (0, false), (11, false)] 112).Valid g H input :=
  Fact.valid_reverse (f := ⟨112, [(11, true), (0, true), (14, false), (0, true), (14, false), (8, false), (14, false), (0, true)], 125⟩) (fact2211 h)

private theorem fact2213 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 135 [(11, false)] 112).Valid g H input :=
  Fact.valid_cancel (f := ⟨125, [(0, false), (14, true), (8, true), (14, true), (0, false), (14, true), (0, false)], 135⟩) (k := ⟨125, [(0, false), (14, true), (8, true), (14, true), (0, false), (14, true), (0, false), (11, false)], 112⟩) (fact2208 h) (fact2212 h) rfl [(11, false)] rfl

private theorem fact2214 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 112 [(11, true)] 135).Valid g H input :=
  Fact.valid_reverse (f := ⟨135, [(11, false)], 112⟩) (fact2213 h)

private theorem fact2216 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 135 [(11, false)] 112).Valid g H input :=
  Fact.valid_reverse (f := ⟨112, [(11, true)], 135⟩) (fact2214 h)

private theorem fact2220 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false), (0, false)] 14).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(1, false)], 4⟩) (k := ⟨4, [(0, false)], 14⟩) (fact1838 h) (fact142 h) rfl

private theorem fact2222 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false), (0, false), (11, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(1, false), (0, false)], 14⟩) (k := ⟨14, [(11, false)], 0⟩) (fact2220 h) (fact102 h) rfl

private theorem fact2224 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false), (0, false), (11, false), (1, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(1, false), (0, false), (11, false)], 0⟩) (k := ⟨0, [(1, false)], 0⟩) (fact2222 h) (fact6 h) rfl

private theorem fact2226 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false), (0, false), (11, false), (1, false), (12, false)] 17).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(1, false), (0, false), (11, false), (1, false)], 0⟩) (k := ⟨0, [(12, false)], 17⟩) (fact2224 h) (fact221 h) rfl

private theorem fact2228 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true), (12, true), (12, true), (1, true), (11, true), (0, true), (1, true)] 4).Valid g H input :=
  Fact.valid_relator h 4 (relator 33)
    (Array.mem_ofFn.mpr ⟨33, rfl⟩) true 4

private theorem fact2229 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [(12, true), (12, true), (1, true), (11, true), (0, true), (1, true)] 4).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(0, true)], 14⟩) (k := ⟨4, [(0, true), (12, true), (12, true), (1, true), (11, true), (0, true), (1, true)], 4⟩) (fact114 h) (fact2228 h) rfl [(12, true), (12, true), (1, true), (11, true), (0, true), (1, true)] rfl

private theorem fact2230 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false), (0, false), (11, false), (1, false), (12, false), (12, false)] 14).Valid g H input :=
  Fact.valid_reverse (f := ⟨14, [(12, true), (12, true), (1, true), (11, true), (0, true), (1, true)], 4⟩) (fact2229 h)

private theorem fact2231 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 17 [(12, false)] 14).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(1, false), (0, false), (11, false), (1, false), (12, false)], 17⟩) (k := ⟨4, [(1, false), (0, false), (11, false), (1, false), (12, false), (12, false)], 14⟩) (fact2226 h) (fact2230 h) rfl [(12, false)] rfl

private theorem fact2232 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [(12, true)] 17).Valid g H input :=
  Fact.valid_reverse (f := ⟨17, [(12, false)], 14⟩) (fact2231 h)

private theorem fact2237 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true), (12, true)] 17).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(0, true)], 14⟩) (k := ⟨14, [(12, true)], 17⟩) (fact114 h) (fact2232 h) rfl

private theorem fact2240 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(16, true)] 20).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(16, true)], 139⟩) (k := ⟨139, [], 20⟩) (fact1465 h) (fact1998 h) rfl

private theorem fact2241 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false), (16, true)] 20).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(1, false)], 4⟩) (k := ⟨4, [(16, true)], 20⟩) (fact1838 h) (fact2240 h) rfl

private theorem fact2243 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false), (16, true), (14, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(1, false), (16, true)], 20⟩) (k := ⟨20, [(14, false)], 0⟩) (fact2241 h) (fact236 h) rfl

private theorem fact2245 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false), (16, true), (14, false), (8, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(1, false), (16, true), (14, false)], 0⟩) (k := ⟨0, [(8, false)], 0⟩) (fact2243 h) (fact20 h) rfl

private theorem fact2247 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false), (16, true), (14, false), (8, false), (4, true)] 3).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(1, false), (16, true), (14, false), (8, false)], 0⟩) (k := ⟨0, [(4, true)], 3⟩) (fact2245 h) (fact41 h) rfl

private theorem fact2249 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false), (16, true), (14, false), (8, false), (4, true), (0, false)] 85).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(1, false), (16, true), (14, false), (8, false), (4, true)], 3⟩) (k := ⟨3, [(0, false)], 85⟩) (fact2247 h) (fact849 h) rfl

private theorem fact2251 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true), (12, true), (7, false), (0, true), (4, false), (8, true), (14, true), (16, false), (1, true)] 4).Valid g H input :=
  Fact.valid_relator h 4 (relator 41)
    (Array.mem_ofFn.mpr ⟨41, rfl⟩) false 2

private theorem fact2252 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 17 [(7, false), (0, true), (4, false), (8, true), (14, true), (16, false), (1, true)] 4).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(0, true), (12, true)], 17⟩) (k := ⟨4, [(0, true), (12, true), (7, false), (0, true), (4, false), (8, true), (14, true), (16, false), (1, true)], 4⟩) (fact2237 h) (fact2251 h) rfl [(7, false), (0, true), (4, false), (8, true), (14, true), (16, false), (1, true)] rfl

private theorem fact2253 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false), (16, true), (14, false), (8, false), (4, true), (0, false), (7, true)] 17).Valid g H input :=
  Fact.valid_reverse (f := ⟨17, [(7, false), (0, true), (4, false), (8, true), (14, true), (16, false), (1, true)], 4⟩) (fact2252 h)

private theorem fact2254 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 85 [(7, true)] 17).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(1, false), (16, true), (14, false), (8, false), (4, true), (0, false)], 85⟩) (k := ⟨4, [(1, false), (16, true), (14, false), (8, false), (4, true), (0, false), (7, true)], 17⟩) (fact2249 h) (fact2253 h) rfl [(7, true)] rfl

private theorem fact2255 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 17 [(7, false)] 85).Valid g H input :=
  Fact.valid_reverse (f := ⟨85, [(7, true)], 17⟩) (fact2254 h)

private theorem fact2260 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true), (11, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(0, true)], 14⟩) (k := ⟨14, [(11, false)], 0⟩) (fact114 h) (fact102 h) rfl

private theorem fact2262 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true), (11, false), (0, true)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(0, true), (11, false)], 0⟩) (k := ⟨0, [(0, true)], 0⟩) (fact2260 h) (fact0 h) rfl

private theorem fact2264 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true), (11, false), (0, true), (4, true)] 3).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(0, true), (11, false), (0, true)], 0⟩) (k := ⟨0, [(4, true)], 3⟩) (fact2262 h) (fact41 h) rfl

private theorem fact2266 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true), (11, false), (0, true), (4, true), (0, true)] 85).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(0, true), (11, false), (0, true), (4, true)], 3⟩) (k := ⟨3, [(0, true)], 85⟩) (fact2264 h) (fact837 h) rfl

private theorem fact2269 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false), (14, true)] 135).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(1, false)], 4⟩) (k := ⟨4, [(14, true)], 135⟩) (fact1838 h) (fact1419 h) rfl

private theorem fact2271 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false), (14, true), (11, false)] 112).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(1, false), (14, true)], 135⟩) (k := ⟨135, [(11, false)], 112⟩) (fact2269 h) (fact2216 h) rfl

private theorem fact2273 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false), (14, true), (11, false), (16, true)] 3).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(1, false), (14, true), (11, false)], 112⟩) (k := ⟨112, [(16, true)], 3⟩) (fact2271 h) (fact1036 h) rfl

private theorem fact2275 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true), (11, false), (0, true), (4, true), (0, true), (16, false), (11, true), (14, false), (1, true)] 4).Valid g H input :=
  Fact.valid_relator h 4 (relator 42)
    (Array.mem_ofFn.mpr ⟨42, rfl⟩) false 4

private theorem fact2276 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 85 [(16, false), (11, true), (14, false), (1, true)] 4).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(0, true), (11, false), (0, true), (4, true), (0, true)], 85⟩) (k := ⟨4, [(0, true), (11, false), (0, true), (4, true), (0, true), (16, false), (11, true), (14, false), (1, true)], 4⟩) (fact2266 h) (fact2275 h) rfl [(16, false), (11, true), (14, false), (1, true)] rfl

private theorem fact2277 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false), (14, true), (11, false), (16, true)] 85).Valid g H input :=
  Fact.valid_reverse (f := ⟨85, [(16, false), (11, true), (14, false), (1, true)], 4⟩) (fact2276 h)

private theorem fact2278 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 3 [] 85).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(1, false), (14, true), (11, false), (16, true)], 3⟩) (k := ⟨4, [(1, false), (14, true), (11, false), (16, true)], 85⟩) (fact2273 h) (fact2277 h) rfl [] rfl

private theorem fact2279 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 85 [] 3).Valid g H input :=
  Fact.valid_reverse (f := ⟨3, [], 85⟩) (fact2278 h)

private theorem fact2281 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 3 [] 85).Valid g H input :=
  Fact.valid_reverse (f := ⟨85, [], 3⟩) (fact2279 h)

private theorem fact2282 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 85 [] 3).Valid g H input :=
  Fact.valid_reverse (f := ⟨3, [], 85⟩) (fact2281 h)

private theorem fact2305 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 3 [] 85).Valid g H input :=
  Fact.valid_reverse (f := ⟨85, [], 3⟩) (fact2282 h)

private theorem fact2306 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 3 [(8, false)] 87).Valid g H input :=
  Fact.valid_trans (f := ⟨3, [], 85⟩) (k := ⟨85, [(8, false)], 87⟩) (fact2305 h) (fact906 h) rfl

private theorem fact2308 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 15 [] 87).Valid g H input :=
  Fact.valid_cancel (f := ⟨3, [(8, false)], 15⟩) (k := ⟨3, [(8, false)], 87⟩) (fact198 h) (fact2306 h) rfl [] rfl

private theorem fact2483 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 87 [] 15).Valid g H input :=
  Fact.valid_reverse (f := ⟨15, [], 87⟩) (fact2308 h)

private theorem fact2566 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 17 [(7, false)] 3).Valid g H input :=
  Fact.valid_trans (f := ⟨17, [(7, false)], 85⟩) (k := ⟨85, [], 3⟩) (fact2255 h) (fact2282 h) rfl

private theorem fact2591 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true), (12, true)] 17).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(0, true)], 14⟩) (k := ⟨14, [(12, true)], 17⟩) (fact114 h) (fact2232 h) rfl

private theorem fact2593 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true), (12, true), (7, false)] 3).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(0, true), (12, true)], 17⟩) (k := ⟨17, [(7, false)], 3⟩) (fact2591 h) (fact2566 h) rfl

private theorem fact2595 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true), (12, true), (7, false), (8, true)] 97).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(0, true), (12, true), (7, false)], 3⟩) (k := ⟨3, [(8, true)], 97⟩) (fact2593 h) (fact943 h) rfl

private theorem fact2598 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(7, false)] 114).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(7, false)], 123⟩) (k := ⟨123, [], 114⟩) (fact1157 h) (fact2095 h) rfl

private theorem fact2599 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false), (7, false)] 114).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(1, false)], 4⟩) (k := ⟨4, [(7, false)], 114⟩) (fact1838 h) (fact2598 h) rfl

private theorem fact2601 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false), (7, false), (2, false)] 4).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(1, false), (7, false)], 114⟩) (k := ⟨114, [(2, false)], 4⟩) (fact2599 h) (fact1073 h) rfl

private theorem fact2603 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false), (7, false), (2, false), (8, false)] 125).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(1, false), (7, false), (2, false)], 4⟩) (k := ⟨4, [(8, false)], 125⟩) (fact2601 h) (fact1185 h) rfl

private theorem fact2605 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true), (12, true), (7, false), (8, true), (9, false), (8, true), (2, true), (7, true), (1, true)] 4).Valid g H input :=
  Fact.valid_relator h 4 (relator 43)
    (Array.mem_ofFn.mpr ⟨43, rfl⟩) true 7

private theorem fact2606 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 97 [(9, false), (8, true), (2, true), (7, true), (1, true)] 4).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(0, true), (12, true), (7, false), (8, true)], 97⟩) (k := ⟨4, [(0, true), (12, true), (7, false), (8, true), (9, false), (8, true), (2, true), (7, true), (1, true)], 4⟩) (fact2595 h) (fact2605 h) rfl [(9, false), (8, true), (2, true), (7, true), (1, true)] rfl

private theorem fact2607 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false), (7, false), (2, false), (8, false), (9, true)] 97).Valid g H input :=
  Fact.valid_reverse (f := ⟨97, [(9, false), (8, true), (2, true), (7, true), (1, true)], 4⟩) (fact2606 h)

private theorem fact2608 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(9, true)] 97).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(1, false), (7, false), (2, false), (8, false)], 125⟩) (k := ⟨4, [(1, false), (7, false), (2, false), (8, false), (9, true)], 97⟩) (fact2603 h) (fact2607 h) rfl [(9, true)] rfl

private theorem fact2609 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 97 [(9, false)] 125).Valid g H input :=
  Fact.valid_reverse (f := ⟨125, [(9, true)], 97⟩) (fact2608 h)

private theorem fact2611 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [(9, true)] 97).Valid g H input :=
  Fact.valid_reverse (f := ⟨97, [(9, false)], 125⟩) (fact2609 h)

private theorem fact2614 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true), (12, true)] 17).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(0, true)], 14⟩) (k := ⟨14, [(12, true)], 17⟩) (fact114 h) (fact2232 h) rfl

private theorem fact2616 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true), (12, true), (7, false)] 3).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(0, true), (12, true)], 17⟩) (k := ⟨17, [(7, false)], 3⟩) (fact2614 h) (fact2566 h) rfl

private theorem fact2618 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 3 [(2, true)] 15).Valid g H input :=
  Fact.valid_trans (f := ⟨3, [(2, true)], 87⟩) (k := ⟨87, [], 15⟩) (fact884 h) (fact2483 h) rfl

private theorem fact2619 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true), (12, true), (7, false), (2, true)] 15).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(0, true), (12, true), (7, false)], 3⟩) (k := ⟨3, [(2, true)], 15⟩) (fact2616 h) (fact2618 h) rfl

private theorem fact2621 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true), (12, true), (7, false), (2, true), (1, true)] 14).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(0, true), (12, true), (7, false), (2, true)], 15⟩) (k := ⟨15, [(1, true)], 14⟩) (fact2619 h) (fact184 h) rfl

private theorem fact2623 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true), (12, true), (7, false), (2, true), (1, true), (0, true)] 4).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(0, true), (12, true), (7, false), (2, true), (1, true)], 14⟩) (k := ⟨14, [(0, true)], 4⟩) (fact2621 h) (fact140 h) rfl

private theorem fact2625 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true), (12, true), (7, false), (2, true), (1, true), (0, true), (12, false)] 132).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(0, true), (12, true), (7, false), (2, true), (1, true), (0, true)], 4⟩) (k := ⟨4, [(12, false)], 132⟩) (fact2623 h) (fact1407 h) rfl

private theorem fact2627 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(7, false)] 114).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(7, false)], 123⟩) (k := ⟨123, [], 114⟩) (fact1157 h) (fact2095 h) rfl

private theorem fact2629 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(7, false), (8, true)] 14).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(7, false)], 114⟩) (k := ⟨114, [(8, true)], 14⟩) (fact2627 h) (fact1090 h) rfl

private theorem fact2631 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(7, false), (8, true), (2, false)] 125).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(7, false), (8, true)], 14⟩) (k := ⟨14, [(2, false)], 125⟩) (fact2629 h) (fact1208 h) rfl

private theorem fact2633 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(7, false), (8, true), (2, false), (9, true)] 97).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(7, false), (8, true), (2, false)], 125⟩) (k := ⟨125, [(9, true)], 97⟩) (fact2631 h) (fact2611 h) rfl

private theorem fact2635 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true), (12, true), (7, false), (2, true), (1, true), (0, true), (12, false), (9, false), (2, true), (8, false), (7, true)] 4).Valid g H input :=
  Fact.valid_relator h 4 (relator 44)
    (Array.mem_ofFn.mpr ⟨44, rfl⟩) false 5

private theorem fact2636 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 132 [(9, false), (2, true), (8, false), (7, true)] 4).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(0, true), (12, true), (7, false), (2, true), (1, true), (0, true), (12, false)], 132⟩) (k := ⟨4, [(0, true), (12, true), (7, false), (2, true), (1, true), (0, true), (12, false), (9, false), (2, true), (8, false), (7, true)], 4⟩) (fact2625 h) (fact2635 h) rfl [(9, false), (2, true), (8, false), (7, true)] rfl

private theorem fact2637 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(7, false), (8, true), (2, false), (9, true)] 132).Valid g H input :=
  Fact.valid_reverse (f := ⟨132, [(9, false), (2, true), (8, false), (7, true)], 4⟩) (fact2636 h)

private theorem fact2638 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 97 [] 132).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(7, false), (8, true), (2, false), (9, true)], 97⟩) (k := ⟨4, [(7, false), (8, true), (2, false), (9, true)], 132⟩) (fact2633 h) (fact2637 h) rfl [] rfl

private theorem fact2639 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 132 [] 97).Valid g H input :=
  Fact.valid_reverse (f := ⟨97, [], 132⟩) (fact2638 h)

private theorem fact2641 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 97 [] 132).Valid g H input :=
  Fact.valid_reverse (f := ⟨132, [], 97⟩) (fact2639 h)

private theorem fact2642 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 132 [] 97).Valid g H input :=
  Fact.valid_reverse (f := ⟨97, [], 132⟩) (fact2641 h)

private theorem fact2651 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 97 [(0, false)] 15).Valid g H input :=
  Fact.valid_trans (f := ⟨97, [(0, false)], 87⟩) (k := ⟨87, [], 15⟩) (fact964 h) (fact2483 h) rfl

private theorem fact2675 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true), (12, false)] 16).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(0, true)], 14⟩) (k := ⟨14, [(12, false)], 16⟩) (fact114 h) (fact220 h) rfl

private theorem fact2678 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false), (2, false)] 114).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(1, false)], 4⟩) (k := ⟨4, [(2, false)], 114⟩) (fact1838 h) (fact1082 h) rfl

private theorem fact2680 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false), (2, false), (7, true)] 4).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(1, false), (2, false)], 114⟩) (k := ⟨114, [(7, true)], 4⟩) (fact2678 h) (fact2118 h) rfl

private theorem fact2682 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(12, false)] 97).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(12, false)], 132⟩) (k := ⟨132, [], 97⟩) (fact1407 h) (fact2642 h) rfl

private theorem fact2683 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false), (2, false), (7, true), (12, false)] 97).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(1, false), (2, false), (7, true)], 4⟩) (k := ⟨4, [(12, false)], 97⟩) (fact2680 h) (fact2682 h) rfl

private theorem fact2685 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false), (2, false), (7, true), (12, false), (0, false)] 15).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(1, false), (2, false), (7, true), (12, false)], 97⟩) (k := ⟨97, [(0, false)], 15⟩) (fact2683 h) (fact2651 h) rfl

private theorem fact2687 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false), (2, false), (7, true), (12, false), (0, false), (7, false)] 125).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(1, false), (2, false), (7, true), (12, false), (0, false)], 15⟩) (k := ⟨15, [(7, false)], 125⟩) (fact2685 h) (fact1240 h) rfl

private theorem fact2689 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false), (2, false), (7, true), (12, false), (0, false), (7, false), (8, true)] 4).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(1, false), (2, false), (7, true), (12, false), (0, false), (7, false)], 125⟩) (k := ⟨125, [(8, true)], 4⟩) (fact2687 h) (fact1188 h) rfl

private theorem fact2691 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false), (2, false), (7, true), (12, false), (0, false), (7, false), (8, true), (2, false)] 114).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(1, false), (2, false), (7, true), (12, false), (0, false), (7, false), (8, true)], 4⟩) (k := ⟨4, [(2, false)], 114⟩) (fact2689 h) (fact1082 h) rfl

private theorem fact2693 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true), (12, false), (9, false), (2, true), (8, false), (7, true), (0, true), (12, true), (7, false), (2, true), (1, true)] 4).Valid g H input :=
  Fact.valid_relator h 4 (relator 44)
    (Array.mem_ofFn.mpr ⟨44, rfl⟩) false 10

private theorem fact2694 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 16 [(9, false), (2, true), (8, false), (7, true), (0, true), (12, true), (7, false), (2, true), (1, true)] 4).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(0, true), (12, false)], 16⟩) (k := ⟨4, [(0, true), (12, false), (9, false), (2, true), (8, false), (7, true), (0, true), (12, true), (7, false), (2, true), (1, true)], 4⟩) (fact2675 h) (fact2693 h) rfl [(9, false), (2, true), (8, false), (7, true), (0, true), (12, true), (7, false), (2, true), (1, true)] rfl

private theorem fact2695 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false), (2, false), (7, true), (12, false), (0, false), (7, false), (8, true), (2, false), (9, true)] 16).Valid g H input :=
  Fact.valid_reverse (f := ⟨16, [(9, false), (2, true), (8, false), (7, true), (0, true), (12, true), (7, false), (2, true), (1, true)], 4⟩) (fact2694 h)

private theorem fact2696 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 114 [(9, true)] 16).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(1, false), (2, false), (7, true), (12, false), (0, false), (7, false), (8, true), (2, false)], 114⟩) (k := ⟨4, [(1, false), (2, false), (7, true), (12, false), (0, false), (7, false), (8, true), (2, false), (9, true)], 16⟩) (fact2691 h) (fact2695 h) rfl [(9, true)] rfl

private theorem fact2697 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 16 [(9, false)] 114).Valid g H input :=
  Fact.valid_reverse (f := ⟨114, [(9, true)], 16⟩) (fact2696 h)

private theorem fact2702 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true), (12, false)] 16).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(0, true)], 14⟩) (k := ⟨14, [(12, false)], 16⟩) (fact114 h) (fact220 h) rfl

private theorem fact2704 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true), (12, false), (9, false)] 114).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(0, true), (12, false)], 16⟩) (k := ⟨16, [(9, false)], 114⟩) (fact2702 h) (fact2697 h) rfl

private theorem fact2706 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true), (12, false), (9, false), (8, true)] 14).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(0, true), (12, false), (9, false)], 114⟩) (k := ⟨114, [(8, true)], 14⟩) (fact2704 h) (fact1090 h) rfl

private theorem fact2708 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true), (12, false), (9, false), (8, true), (12, false)] 16).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(0, true), (12, false), (9, false), (8, true)], 14⟩) (k := ⟨14, [(12, false)], 16⟩) (fact2706 h) (fact220 h) rfl

private theorem fact2711 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false), (2, false)] 114).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(1, false)], 4⟩) (k := ⟨4, [(2, false)], 114⟩) (fact1838 h) (fact1082 h) rfl

private theorem fact2713 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false), (2, false), (7, true)] 4).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(1, false), (2, false)], 114⟩) (k := ⟨114, [(7, true)], 4⟩) (fact2711 h) (fact2118 h) rfl

private theorem fact2715 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false), (2, false), (7, true), (2, false)] 114).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(1, false), (2, false), (7, true)], 4⟩) (k := ⟨4, [(2, false)], 114⟩) (fact2713 h) (fact1082 h) rfl

private theorem fact2717 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false), (2, false), (7, true), (2, false), (7, true)] 4).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(1, false), (2, false), (7, true), (2, false)], 114⟩) (k := ⟨114, [(7, true)], 4⟩) (fact2715 h) (fact2118 h) rfl

private theorem fact2719 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false), (2, false), (7, true), (2, false), (7, true), (0, false)] 14).Valid g H input :=
  Fact.valid_trans (f := ⟨4, [(1, false), (2, false), (7, true), (2, false), (7, true)], 4⟩) (k := ⟨4, [(0, false)], 14⟩) (fact2717 h) (fact142 h) rfl

private theorem fact2721 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(0, true), (12, false), (9, false), (8, true), (12, false), (0, true), (7, false), (2, true), (7, false), (2, true), (1, true)] 4).Valid g H input :=
  Fact.valid_relator h 4 (relator 45)
    (Array.mem_ofFn.mpr ⟨45, rfl⟩) false 10

private theorem fact2722 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 16 [(0, true), (7, false), (2, true), (7, false), (2, true), (1, true)] 4).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(0, true), (12, false), (9, false), (8, true), (12, false)], 16⟩) (k := ⟨4, [(0, true), (12, false), (9, false), (8, true), (12, false), (0, true), (7, false), (2, true), (7, false), (2, true), (1, true)], 4⟩) (fact2708 h) (fact2721 h) rfl [(0, true), (7, false), (2, true), (7, false), (2, true), (1, true)] rfl

private theorem fact2723 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [(1, false), (2, false), (7, true), (2, false), (7, true), (0, false)] 16).Valid g H input :=
  Fact.valid_reverse (f := ⟨16, [(0, true), (7, false), (2, true), (7, false), (2, true), (1, true)], 4⟩) (fact2722 h)

private theorem fact2724 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [] 16).Valid g H input :=
  Fact.valid_cancel (f := ⟨4, [(1, false), (2, false), (7, true), (2, false), (7, true), (0, false)], 14⟩) (k := ⟨4, [(1, false), (2, false), (7, true), (2, false), (7, true), (0, false)], 16⟩) (fact2719 h) (fact2723 h) rfl [] rfl

private theorem fact2725 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 16 [] 14).Valid g H input :=
  Fact.valid_reverse (f := ⟨14, [], 16⟩) (fact2724 h)

private theorem fact2727 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [] 16).Valid g H input :=
  Fact.valid_reverse (f := ⟨16, [], 14⟩) (fact2725 h)

private theorem fact2728 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 16 [] 14).Valid g H input :=
  Fact.valid_reverse (f := ⟨14, [], 16⟩) (fact2727 h)

private theorem fact2798 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [(12, false)] 14).Valid g H input :=
  Fact.valid_trans (f := ⟨14, [(12, false)], 16⟩) (k := ⟨16, [], 14⟩) (fact220 h) (fact2728 h) rfl

private theorem fact2800 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [(12, true)] 14).Valid g H input :=
  Fact.valid_reverse (f := ⟨14, [(12, false)], 14⟩) (fact2798 h)

private theorem fact2801 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 17 [] 14).Valid g H input :=
  Fact.valid_cancel (f := ⟨14, [(12, true)], 17⟩) (k := ⟨14, [(12, true)], 14⟩) (fact2232 h) (fact2800 h) rfl [] rfl

private theorem fact2813 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [] 17).Valid g H input :=
  Fact.valid_reverse (f := ⟨17, [], 14⟩) (fact2801 h)

private theorem fact2814 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 17 [] 14).Valid g H input :=
  Fact.valid_reverse (f := ⟨14, [], 17⟩) (fact2813 h)

private theorem fact2817 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [] 17).Valid g H input :=
  Fact.valid_reverse (f := ⟨17, [], 14⟩) (fact2814 h)

private theorem fact2818 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [(12, true)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨14, [], 17⟩) (k := ⟨17, [(12, true)], 0⟩) (fact2817 h) (fact224 h) rfl

private theorem fact2820 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [(12, true)] 14).Valid g H input :=
  Fact.valid_trans (f := ⟨14, [(12, true)], 17⟩) (k := ⟨17, [], 14⟩) (fact2232 h) (fact2814 h) rfl

private theorem fact2821 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [] 0).Valid g H input :=
  Fact.valid_cancel (f := ⟨14, [(12, true)], 14⟩) (k := ⟨14, [(12, true)], 0⟩) (fact2820 h) (fact2818 h) rfl [] rfl

private theorem fact2922 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [] 14).Valid g H input :=
  Fact.valid_reverse (f := ⟨14, [], 0⟩) (fact2821 h)

private theorem fact2923 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 14 [] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [], 14⟩) (fact2922 h)

private theorem fact3091 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(11, true)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(11, true)], 14⟩) (k := ⟨14, [], 0⟩) (fact99 h) (fact2923 h) rfl

private theorem fact3093 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(11, false)] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [(11, true)], 0⟩) (fact3091 h)

private theorem fact3094 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 15 [] 0).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(11, false)], 15⟩) (k := ⟨0, [(11, false)], 0⟩) (fact159 h) (fact3093 h) rfl [] rfl

private theorem fact3100 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 16 [] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨16, [], 14⟩) (k := ⟨14, [], 0⟩) (fact2728 h) (fact2923 h) rfl

private theorem fact3101 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(12, true)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(12, true)], 16⟩) (k := ⟨16, [], 0⟩) (fact199 h) (fact3100 h) rfl

private theorem fact3157 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [] 15).Valid g H input :=
  Fact.valid_reverse (f := ⟨15, [], 0⟩) (fact3094 h)

private theorem fact3158 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 15 [] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [], 15⟩) (fact3157 h)

private theorem fact3189 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [] 15).Valid g H input :=
  Fact.valid_reverse (f := ⟨15, [], 0⟩) (fact3158 h)

private theorem fact3190 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(8, true)] 3).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [], 15⟩) (k := ⟨15, [(8, true)], 3⟩) (fact3189 h) (fact196 h) rfl

private theorem fact3192 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [] 3).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(8, true)], 0⟩) (k := ⟨0, [(8, true)], 3⟩) (fact18 h) (fact3190 h) rfl [] rfl

private theorem fact3291 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(11, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(11, false)], 15⟩) (k := ⟨15, [], 0⟩) (fact159 h) (fact3158 h) rfl

private theorem fact3371 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 3 [] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [], 3⟩) (fact3192 h)

private theorem fact3552 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(4, true)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(4, true)], 3⟩) (k := ⟨3, [], 0⟩) (fact41 h) (fact3371 h) rfl

private theorem fact3554 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(4, false)] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [(4, true)], 0⟩) (fact3552 h)

private theorem fact3555 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [] 0).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(4, false)], 4⟩) (k := ⟨0, [(4, false)], 0⟩) (fact45 h) (fact3554 h) rfl [] rfl

private theorem fact3682 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [] 4).Valid g H input :=
  Fact.valid_reverse (f := ⟨4, [], 0⟩) (fact3555 h)

private theorem fact3683 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 4 [] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [], 4⟩) (fact3682 h)

private theorem fact3821 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [] 4).Valid g H input :=
  Fact.valid_reverse (f := ⟨4, [], 0⟩) (fact3683 h)

private theorem fact3822 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(16, true)] 139).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [], 4⟩) (k := ⟨4, [(16, true)], 139⟩) (fact3821 h) (fact1465 h) rfl

private theorem fact3823 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(16, true)] 20).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(16, true)], 139⟩) (k := ⟨139, [], 20⟩) (fact3822 h) (fact1998 h) rfl

private theorem fact3825 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 24 [] 20).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(16, true)], 24⟩) (k := ⟨0, [(16, true)], 20⟩) (fact283 h) (fact3823 h) rfl [] rfl

private theorem fact4010 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 25 [(7, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨25, [(7, false)], 14⟩) (k := ⟨14, [], 0⟩) (fact300 h) (fact2923 h) rfl

private theorem fact4012 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(7, true)] 25).Valid g H input :=
  Fact.valid_reverse (f := ⟨25, [(7, false)], 0⟩) (fact4010 h)

private theorem fact4013 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 8 [] 25).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(7, true)], 8⟩) (k := ⟨0, [(7, true)], 25⟩) (fact75 h) (fact4012 h) rfl [] rfl

private theorem fact4025 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 25 [] 8).Valid g H input :=
  Fact.valid_reverse (f := ⟨8, [], 25⟩) (fact4013 h)

private theorem fact4030 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 8 [] 25).Valid g H input :=
  Fact.valid_reverse (f := ⟨25, [], 8⟩) (fact4025 h)

private theorem fact4031 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 8 [(14, false)] 7).Valid g H input :=
  Fact.valid_trans (f := ⟨8, [], 25⟩) (k := ⟨25, [(14, false)], 7⟩) (fact4030 h) (fact316 h) rfl

private theorem fact4059 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 20 [] 24).Valid g H input :=
  Fact.valid_reverse (f := ⟨24, [], 20⟩) (fact3825 h)

private theorem fact4060 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 24 [] 20).Valid g H input :=
  Fact.valid_reverse (f := ⟨20, [], 24⟩) (fact4059 h)

private theorem fact4065 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 20 [] 24).Valid g H input :=
  Fact.valid_reverse (f := ⟨24, [], 20⟩) (fact4060 h)

private theorem fact4066 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 20 [(2, false)] 71).Valid g H input :=
  Fact.valid_trans (f := ⟨20, [], 24⟩) (k := ⟨24, [(2, false)], 71⟩) (fact4065 h) (fact742 h) rfl

private theorem fact4068 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 21 [] 71).Valid g H input :=
  Fact.valid_cancel (f := ⟨20, [(2, false)], 21⟩) (k := ⟨20, [(2, false)], 71⟩) (fact274 h) (fact4066 h) rfl [] rfl

private theorem fact4111 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 71 [] 21).Valid g H input :=
  Fact.valid_reverse (f := ⟨21, [], 71⟩) (fact4068 h)

private theorem fact4131 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 21 [] 71).Valid g H input :=
  Fact.valid_reverse (f := ⟨71, [], 21⟩) (fact4111 h)

private theorem fact4132 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 21 [(10, false)] 2).Valid g H input :=
  Fact.valid_trans (f := ⟨21, [], 71⟩) (k := ⟨71, [(10, false)], 2⟩) (fact4131 h) (fact714 h) rfl

private theorem fact4134 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 116 [] 2).Valid g H input :=
  Fact.valid_cancel (f := ⟨21, [(10, false)], 116⟩) (k := ⟨21, [(10, false)], 2⟩) (fact1132 h) (fact4132 h) rfl [] rfl

private theorem fact4177 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 2 [] 116).Valid g H input :=
  Fact.valid_reverse (f := ⟨116, [], 2⟩) (fact4134 h)

private theorem fact4178 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 116 [] 2).Valid g H input :=
  Fact.valid_reverse (f := ⟨2, [], 116⟩) (fact4177 h)

private theorem fact4184 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 2 [] 116).Valid g H input :=
  Fact.valid_reverse (f := ⟨116, [], 2⟩) (fact4178 h)

private theorem fact4185 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 2 [(6, false)] 125).Valid g H input :=
  Fact.valid_trans (f := ⟨2, [], 116⟩) (k := ⟨116, [(6, false)], 125⟩) (fact4184 h) (fact1294 h) rfl

private theorem fact4187 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [] 125).Valid g H input :=
  Fact.valid_cancel (f := ⟨2, [(6, false)], 0⟩) (k := ⟨2, [(6, false)], 125⟩) (fact38 h) (fact4185 h) rfl [] rfl

private theorem fact4367 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 125 [] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [], 125⟩) (fact4187 h)

private theorem fact4416 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [] 125).Valid g H input :=
  Fact.valid_reverse (f := ⟨125, [], 0⟩) (fact4367 h)

private theorem fact4417 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(14, true)] 14).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [], 125⟩) (k := ⟨125, [(14, true)], 14⟩) (fact4416 h) (fact1256 h) rfl

private theorem fact4418 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(14, true)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(14, true)], 14⟩) (k := ⟨14, [], 0⟩) (fact4417 h) (fact2923 h) rfl

private theorem fact4420 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 20 [] 0).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(14, true)], 20⟩) (k := ⟨0, [(14, true)], 0⟩) (fact233 h) (fact4418 h) rfl [] rfl

private theorem fact4421 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [] 125).Valid g H input :=
  Fact.valid_reverse (f := ⟨125, [], 0⟩) (fact4367 h)

private theorem fact4422 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(16, false)] 167).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [], 125⟩) (k := ⟨125, [(16, false)], 167⟩) (fact4421 h) (fact1720 h) rfl

private theorem fact4424 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(16, false)] 8).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(16, false)], 25⟩) (k := ⟨25, [], 8⟩) (fact287 h) (fact4025 h) rfl

private theorem fact4425 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 8 [] 167).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(16, false)], 8⟩) (k := ⟨0, [(16, false)], 167⟩) (fact4424 h) (fact4422 h) rfl [] rfl

private theorem fact4555 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(16, true)] 20).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(16, true)], 24⟩) (k := ⟨24, [], 20⟩) (fact283 h) (fact4060 h) rfl

private theorem fact4560 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(16, false)] 8).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(16, false)], 25⟩) (k := ⟨25, [], 8⟩) (fact287 h) (fact4025 h) rfl

private theorem fact4599 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 167 [] 8).Valid g H input :=
  Fact.valid_reverse (f := ⟨8, [], 167⟩) (fact4425 h)

private theorem fact4600 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 8 [] 167).Valid g H input :=
  Fact.valid_reverse (f := ⟨167, [], 8⟩) (fact4599 h)

private theorem fact4601 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 8 [(14, false)] 12).Valid g H input :=
  Fact.valid_trans (f := ⟨8, [], 167⟩) (k := ⟨167, [(14, false)], 12⟩) (fact4600 h) (fact2166 h) rfl

private theorem fact4603 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 7 [] 12).Valid g H input :=
  Fact.valid_cancel (f := ⟨8, [(14, false)], 7⟩) (k := ⟨8, [(14, false)], 12⟩) (fact4031 h) (fact4601 h) rfl [] rfl

private theorem fact4604 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 8 [] 167).Valid g H input :=
  Fact.valid_reverse (f := ⟨167, [], 8⟩) (fact4599 h)

private theorem fact4605 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 8 [(15, false)] 5).Valid g H input :=
  Fact.valid_trans (f := ⟨8, [], 167⟩) (k := ⟨167, [(15, false)], 5⟩) (fact4604 h) (fact1704 h) rfl

private theorem fact4635 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 12 [] 7).Valid g H input :=
  Fact.valid_reverse (f := ⟨7, [], 12⟩) (fact4603 h)

private theorem fact4641 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 7 [] 12).Valid g H input :=
  Fact.valid_reverse (f := ⟨12, [], 7⟩) (fact4635 h)

private theorem fact4642 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 7 [(7, true)] 160).Valid g H input :=
  Fact.valid_trans (f := ⟨7, [], 12⟩) (k := ⟨12, [(7, true)], 160⟩) (fact4641 h) (fact1666 h) rfl

private theorem fact4697 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [] 20).Valid g H input :=
  Fact.valid_reverse (f := ⟨20, [], 0⟩) (fact4420 h)

private theorem fact4698 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 20 [] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [], 20⟩) (fact4697 h)

private theorem fact4806 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(10, true)] 7).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(10, true)], 12⟩) (k := ⟨12, [], 7⟩) (fact91 h) (fact4635 h) rfl

private theorem fact4839 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(14, true)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(14, true)], 20⟩) (k := ⟨20, [], 0⟩) (fact233 h) (fact4698 h) rfl

private theorem fact4856 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(16, true)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(16, true)], 20⟩) (k := ⟨20, [], 0⟩) (fact4555 h) (fact4698 h) rfl

private theorem fact4858 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(16, false)] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [(16, true)], 0⟩) (fact4856 h)

private theorem fact4859 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 8 [] 0).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(16, false)], 8⟩) (k := ⟨0, [(16, false)], 0⟩) (fact4560 h) (fact4858 h) rfl [] rfl

private theorem fact4866 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [] 8).Valid g H input :=
  Fact.valid_reverse (f := ⟨8, [], 0⟩) (fact4859 h)

private theorem fact4867 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 8 [] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [], 8⟩) (fact4866 h)

private theorem fact4872 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [] 8).Valid g H input :=
  Fact.valid_reverse (f := ⟨8, [], 0⟩) (fact4867 h)

private theorem fact4873 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(14, false)] 7).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [], 8⟩) (k := ⟨8, [(14, false)], 7⟩) (fact4872 h) (fact4031 h) rfl

private theorem fact4875 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 21 [] 7).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(14, false)], 21⟩) (k := ⟨0, [(14, false)], 7⟩) (fact237 h) (fact4873 h) rfl [] rfl

private theorem fact4876 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [] 8).Valid g H input :=
  Fact.valid_reverse (f := ⟨8, [], 0⟩) (fact4867 h)

private theorem fact4877 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(15, false)] 5).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [], 8⟩) (k := ⟨8, [(15, false)], 5⟩) (fact4876 h) (fact4605 h) rfl

private theorem fact4879 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 23 [] 5).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(15, false)], 23⟩) (k := ⟨0, [(15, false)], 5⟩) (fact279 h) (fact4877 h) rfl [] rfl

private theorem fact4941 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(7, true)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(7, true)], 8⟩) (k := ⟨8, [], 0⟩) (fact75 h) (fact4867 h) rfl

private theorem fact4999 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(14, false)] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [(14, true)], 0⟩) (fact4839 h)

private theorem fact5000 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 21 [] 0).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(14, false)], 21⟩) (k := ⟨0, [(14, false)], 0⟩) (fact237 h) (fact4999 h) rfl [] rfl

private theorem fact5019 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(16, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(16, false)], 8⟩) (k := ⟨8, [], 0⟩) (fact4560 h) (fact4867 h) rfl

private theorem fact5029 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [] 21).Valid g H input :=
  Fact.valid_reverse (f := ⟨21, [], 0⟩) (fact5000 h)

private theorem fact5030 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 21 [] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [], 21⟩) (fact5029 h)

private theorem fact5056 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [] 21).Valid g H input :=
  Fact.valid_reverse (f := ⟨21, [], 0⟩) (fact5030 h)

private theorem fact5057 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(10, false)] 116).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [], 21⟩) (k := ⟨21, [(10, false)], 116⟩) (fact5056 h) (fact1132 h) rfl

private theorem fact5058 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(10, false)] 2).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(10, false)], 116⟩) (k := ⟨116, [], 2⟩) (fact5057 h) (fact4178 h) rfl

private theorem fact5060 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 13 [] 2).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(10, false)], 13⟩) (k := ⟨0, [(10, false)], 2⟩) (fact95 h) (fact5058 h) rfl [] rfl

private theorem fact5425 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 2 [] 13).Valid g H input :=
  Fact.valid_reverse (f := ⟨13, [], 2⟩) (fact5060 h)

private theorem fact5426 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 13 [] 2).Valid g H input :=
  Fact.valid_reverse (f := ⟨2, [], 13⟩) (fact5425 h)

private theorem fact5641 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 5 [] 23).Valid g H input :=
  Fact.valid_reverse (f := ⟨23, [], 5⟩) (fact4879 h)

private theorem fact5642 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 23 [] 5).Valid g H input :=
  Fact.valid_reverse (f := ⟨5, [], 23⟩) (fact5641 h)

private theorem fact5810 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [] 21).Valid g H input :=
  Fact.valid_reverse (f := ⟨21, [], 0⟩) (fact5030 h)

private theorem fact5811 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [] 7).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [], 21⟩) (k := ⟨21, [], 7⟩) (fact5810 h) (fact4875 h) rfl

private theorem fact5812 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 7 [] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [], 7⟩) (fact5811 h)

private theorem fact5829 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [] 7).Valid g H input :=
  Fact.valid_reverse (f := ⟨7, [], 0⟩) (fact5812 h)

private theorem fact5830 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(7, true)] 160).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [], 7⟩) (k := ⟨7, [(7, true)], 160⟩) (fact5829 h) (fact4642 h) rfl

private theorem fact5832 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [] 160).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(7, true)], 0⟩) (k := ⟨0, [(7, true)], 160⟩) (fact4941 h) (fact5830 h) rfl [] rfl

private theorem fact5900 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(6, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(6, false)], 7⟩) (k := ⟨7, [], 0⟩) (fact71 h) (fact5812 h) rfl

private theorem fact5929 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(10, true)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(10, true)], 7⟩) (k := ⟨7, [], 0⟩) (fact4806 h) (fact5812 h) rfl

private theorem fact5931 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(10, false)] 2).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(10, false)], 13⟩) (k := ⟨13, [], 2⟩) (fact95 h) (fact5426 h) rfl

private theorem fact5932 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(10, false)] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [(10, true)], 0⟩) (fact5929 h)

private theorem fact5933 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 2 [] 0).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(10, false)], 2⟩) (k := ⟨0, [(10, false)], 0⟩) (fact5931 h) (fact5932 h) rfl [] rfl

private theorem fact5976 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(15, false)] 5).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(15, false)], 23⟩) (k := ⟨23, [], 5⟩) (fact279 h) (fact5642 h) rfl

private theorem fact6002 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [] 2).Valid g H input :=
  Fact.valid_reverse (f := ⟨2, [], 0⟩) (fact5933 h)

private theorem fact6003 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 2 [] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [], 2⟩) (fact6002 h)

private theorem fact6172 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(3, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(3, false)], 2⟩) (k := ⟨2, [], 0⟩) (fact25 h) (fact6003 h) rfl

private theorem fact6174 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(3, true)] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [(3, false)], 0⟩) (fact6172 h)

private theorem fact6175 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 1 [] 0).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(3, true)], 1⟩) (k := ⟨0, [(3, true)], 0⟩) (fact21 h) (fact6174 h) rfl [] rfl

private theorem fact6193 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(6, true)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(6, true)], 2⟩) (k := ⟨2, [], 0⟩) (fact40 h) (fact6003 h) rfl

private theorem fact6310 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [] 1).Valid g H input :=
  Fact.valid_reverse (f := ⟨1, [], 0⟩) (fact6175 h)

private theorem fact6311 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 1 [] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [], 1⟩) (fact6310 h)

private theorem fact6474 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(3, true)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(3, true)], 1⟩) (k := ⟨1, [], 0⟩) (fact21 h) (fact6311 h) rfl

private theorem fact8622 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 11 [(4, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨11, [(4, false)], 14⟩) (k := ⟨14, [], 0⟩) (fact128 h) (fact2923 h) rfl

private theorem fact8624 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(4, true)] 11).Valid g H input :=
  Fact.valid_reverse (f := ⟨11, [(4, false)], 0⟩) (fact8622 h)

private theorem fact8625 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [] 11).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(4, true)], 0⟩) (k := ⟨0, [(4, true)], 11⟩) (fact3552 h) (fact8624 h) rfl [] rfl

private theorem fact8638 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 11 [] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [], 11⟩) (fact8625 h)

private theorem fact8728 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(9, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(9, false)], 11⟩) (k := ⟨11, [], 0⟩) (fact87 h) (fact8638 h) rfl

private theorem fact8730 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(9, true)] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [(9, false)], 0⟩) (fact8728 h)

private theorem fact8731 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 10 [] 0).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(9, true)], 10⟩) (k := ⟨0, [(9, true)], 0⟩) (fact83 h) (fact8730 h) rfl [] rfl

private theorem fact8803 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [] 10).Valid g H input :=
  Fact.valid_reverse (f := ⟨10, [], 0⟩) (fact8731 h)

private theorem fact8804 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 10 [] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [], 10⟩) (fact8803 h)

private theorem fact8892 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(9, true)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(9, true)], 10⟩) (k := ⟨10, [], 0⟩) (fact83 h) (fact8804 h) rfl

private theorem fact16262 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 160 [] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [], 160⟩) (fact5832 h)

private theorem fact16269 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [] 160).Valid g H input :=
  Fact.valid_reverse (f := ⟨160, [], 0⟩) (fact16262 h)

private theorem fact16270 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(11, true)] 5).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [], 160⟩) (k := ⟨160, [(11, true)], 5⟩) (fact16269 h) (fact1650 h) rfl

private theorem fact16272 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [] 5).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(11, true)], 0⟩) (k := ⟨0, [(11, true)], 5⟩) (fact3091 h) (fact16270 h) rfl [] rfl

private theorem fact16444 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 5 [] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [], 5⟩) (fact16272 h)

private theorem fact16612 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(5, true)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(5, true)], 5⟩) (k := ⟨5, [], 0⟩) (fact63 h) (fact16444 h) rfl

private theorem fact16697 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(15, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(15, false)], 5⟩) (k := ⟨5, [], 0⟩) (fact5976 h) (fact16444 h) rfl

private theorem fact16699 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(15, true)] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [(15, false)], 0⟩) (fact16697 h)

private theorem fact16700 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 22 [] 0).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(15, true)], 22⟩) (k := ⟨0, [(15, true)], 0⟩) (fact275 h) (fact16699 h) rfl [] rfl

private theorem fact16712 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [] 22).Valid g H input :=
  Fact.valid_reverse (f := ⟨22, [], 0⟩) (fact16700 h)

private theorem fact16713 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 22 [] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [], 22⟩) (fact16712 h)

private theorem fact16760 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(5, false)] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [(5, true)], 0⟩) (fact16612 h)

private theorem fact16761 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 6 [] 0).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(5, false)], 6⟩) (k := ⟨0, [(5, false)], 0⟩) (fact67 h) (fact16760 h) rfl [] rfl

private theorem fact16839 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(15, true)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(15, true)], 22⟩) (k := ⟨22, [], 0⟩) (fact275 h) (fact16713 h) rfl

private theorem fact16879 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [] 6).Valid g H input :=
  Fact.valid_reverse (f := ⟨6, [], 0⟩) (fact16761 h)

private theorem fact16880 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 6 [] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [], 6⟩) (fact16879 h)

private theorem fact16931 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(5, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(5, false)], 6⟩) (k := ⟨6, [], 0⟩) (fact67 h) (fact16880 h) rfl

private theorem fact28740 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(0, true), (9, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(0, true)], 0⟩) (k := ⟨0, [(9, false)], 0⟩) (fact0 h) (fact8728 h) rfl

private theorem fact28742 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(0, true), (9, false), (5, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(0, true), (9, false)], 0⟩) (k := ⟨0, [(5, false)], 0⟩) (fact28740 h) (fact16931 h) rfl

private theorem fact28744 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(0, true), (9, false), (5, false), (9, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(0, true), (9, false), (5, false)], 0⟩) (k := ⟨0, [(9, false)], 0⟩) (fact28742 h) (fact8728 h) rfl

private theorem fact28746 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(0, true), (9, false), (5, false), (9, false), (5, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(0, true), (9, false), (5, false), (9, false)], 0⟩) (k := ⟨0, [(5, false)], 0⟩) (fact28744 h) (fact16931 h) rfl

private theorem fact28748 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(0, true), (9, false), (5, false), (9, false), (5, false), (6, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(0, true), (9, false), (5, false), (9, false), (5, false)], 0⟩) (k := ⟨0, [(6, false)], 0⟩) (fact28746 h) (fact5900 h) rfl

private theorem fact28750 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(0, true), (9, false), (5, false), (9, false), (5, false), (6, false), (13, true)] 18).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(0, true), (9, false), (5, false), (9, false), (5, false), (6, false)], 0⟩) (k := ⟨0, [(13, true)], 18⟩) (fact28748 h) (fact225 h) rfl

private theorem fact28753 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(8, true), (9, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(8, true)], 0⟩) (k := ⟨0, [(9, false)], 0⟩) (fact18 h) (fact8728 h) rfl

private theorem fact28755 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(8, true), (9, false), (11, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(8, true), (9, false)], 0⟩) (k := ⟨0, [(11, false)], 0⟩) (fact28753 h) (fact3291 h) rfl

private theorem fact28757 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(8, true), (9, false), (11, false), (1, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(8, true), (9, false), (11, false)], 0⟩) (k := ⟨0, [(1, false)], 0⟩) (fact28755 h) (fact6 h) rfl

private theorem fact28759 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(8, true), (9, false), (11, false), (1, false), (16, false)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(8, true), (9, false), (11, false), (1, false)], 0⟩) (k := ⟨0, [(16, false)], 0⟩) (fact28757 h) (fact5019 h) rfl

private theorem fact28761 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(0, true), (9, false), (5, false), (9, false), (5, false), (6, false), (13, true), (16, true), (1, true), (11, true), (9, true), (8, false)] 0).Valid g H input :=
  Fact.valid_relator h 0 (relator 47)
    (Array.mem_ofFn.mpr ⟨47, rfl⟩) true 4

private theorem fact28762 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 18 [(16, true), (1, true), (11, true), (9, true), (8, false)] 0).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(0, true), (9, false), (5, false), (9, false), (5, false), (6, false), (13, true)], 18⟩) (k := ⟨0, [(0, true), (9, false), (5, false), (9, false), (5, false), (6, false), (13, true), (16, true), (1, true), (11, true), (9, true), (8, false)], 0⟩) (fact28750 h) (fact28761 h) rfl [(16, true), (1, true), (11, true), (9, true), (8, false)] rfl

private theorem fact28763 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(8, true), (9, false), (11, false), (1, false), (16, false)] 18).Valid g H input :=
  Fact.valid_reverse (f := ⟨18, [(16, true), (1, true), (11, true), (9, true), (8, false)], 0⟩) (fact28762 h)

private theorem fact28764 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [] 18).Valid g H input :=
  Fact.valid_cancel (f := ⟨0, [(8, true), (9, false), (11, false), (1, false), (16, false)], 0⟩) (k := ⟨0, [(8, true), (9, false), (11, false), (1, false), (16, false)], 18⟩) (fact28759 h) (fact28763 h) rfl [] rfl

private theorem fact28765 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 18 [] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [], 18⟩) (fact28764 h)

private theorem fact28767 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [] 18).Valid g H input :=
  Fact.valid_reverse (f := ⟨18, [], 0⟩) (fact28765 h)

private theorem fact28768 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 18 [] 0).Valid g H input :=
  Fact.valid_reverse (f := ⟨0, [], 18⟩) (fact28767 h)

private theorem fact28878 (h : Models g H input) :
    (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(13, true)] 0).Valid g H input :=
  Fact.valid_trans (f := ⟨0, [(13, true)], 18⟩) (k := ⟨18, [], 0⟩) (fact225 h) (fact28768 h) rfl

/-- All 17 generators lie in the subgroup once the 49 residual relations
hold and the first three generators lie in it. -/
public theorem generators_mem (h : Models g H input) (a : Fin 17) : g a ∈ H := by
  have he : (Theory.GroupTheory.CosetEnumeration.Fact.mk 0 [(a, true)] 0).Valid g H input := by
    fin_cases a
    · exact fact0 h
    · exact fact4 h
    · exact fact7 h
    · exact fact6474 h
    · exact fact3552 h
    · exact fact16612 h
    · exact fact6193 h
    · exact fact4941 h
    · exact fact18 h
    · exact fact8892 h
    · exact fact5929 h
    · exact fact3091 h
    · exact fact3101 h
    · exact fact28878 h
    · exact fact4839 h
    · exact fact16839 h
    · exact fact4856 h
  obtain ⟨u, hu, he⟩ := he
  have hz : representative g input 0 = 1 := by
    change eval g (input.reps.getD 0 []) = 1
    rw [h.zero, eval_nil]
  change representative g input 0 * eval g [(a, true)] = u * representative g input 0 at he
  rw [hz, one_mul, mul_one, eval_singleton] at he
  have hg : g a = u := he
  rw [hg]
  exact hu

/-- Membership follows from the explicit relations and three subgroup inputs. -/
public theorem generators_mem_of_relators
    (hr : ∀ r : Fin 49, eval g (relator r) = 1)
    (hs : g 0 ∈ H ∧ g 1 ∈ H ∧ g 2 ∈ H) (a : Fin 17) : g a ∈ H := by
  apply generators_mem (g := g) (H := H) _ a
  refine ⟨by decide +kernel, ?_, ?_⟩
  · intro w hw
    obtain ⟨i, rfl⟩ := Array.mem_ofFn.mp hw
    exact hr i
  · intro b hb
    simp only [input, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hs.1
    · exact hs.2.1
    · exact hs.2.2

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.Reduced
