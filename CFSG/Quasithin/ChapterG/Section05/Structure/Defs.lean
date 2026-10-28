module

public import CFSG.Quasithin.ChapterG.Section05.Basic
public import Theory.Representation.BinaryDuadStructure.NaturalCover
public import Theory.Representation.SubrepresentationRadical

/-!
# Literal layers and the independent middle-cover input for G.5.3

The radical layers use intersections of maximal subrepresentations of each
restricted action, embedded in the original fifteen-point module. The middle
section is the actual quotient D/C. `MiddleCoverData` is an explicit input
for the separate radical argument; it must be constructed using the opposite
marked natural action before final source assembly.

Source: Aschbacher–Smith, G.5.3(2)–(5), printed pp.343–345.
-/

@[expose] public section

open Theory.SpecificGroups.SymmetricSix BinaryPermutation BinaryDuadModule

namespace CFSG.Quasithin.ChapterG.Section05.Structure
open BinaryDuadStructure

/-- The literal even core with its restricted fifteen-point action. -/
noncomputable def coreSubrepresentation : Subrepresentation action where
  toSubmodule := U0
  apply_mem_toSubmodule g _ hu := core_invariant Omega (MulAction.toPermHom A6 Duad g) hu

/-- Radicals of successively restricted actions, embedded in the original U. -/
noncomputable abbrev radicalLayer (n : ℕ) : Subrepresentation action :=
  Representation.ModuleRadical.series coreSubrepresentation n

@[simp] theorem radicalLayer_zero : radicalLayer 0 = coreSubrepresentation := rfl

theorem radicalLayer_le_core (n : ℕ) : radicalLayer n ≤ coreSubrepresentation :=
  Representation.ModuleRadical.series_antitone coreSubrepresentation (Nat.zero_le n)

noncomputable abbrev MiddleRelations := naturalSubmodule.toSubmodule.comap lineComplementSpan.subtype
abbrev MiddleQuotient := lineComplementSpan ⧸ MiddleRelations

/-- The source section D/C, carrying the quotient of the restricted original action. -/
noncomputable def middleAction : Representation (ZMod 2) G MiddleQuotient :=
  BinaryDuadModule.lineComplementSubrepresentation.toRepresentation.quotient MiddleRelations
    (fun g _ hu => naturalSubmodule.apply_mem_toSubmodule g hu)

theorem middleQuotient_finrank : Module.finrank (ZMod 2) MiddleQuotient = 5 :=
  BinaryDuadModule.lineComplementSpan_quotient_complement_finrank

/-- Independent input to the radical-series argument. A separate construction
must supply the opposite marked natural action and this covering; this record
is not an assertion of G.5.3(5). -/
structure MiddleCoverData where
  oppositeAction : Representation (ZMod 2) G NaturalModule
  irreducible : oppositeAction.IsIrreducible
  selfDual : Nonempty (oppositeAction.Equiv oppositeAction.dual)
  distinct : ¬ Nonempty (Representation.Equiv naturalAction oppositeAction)
  projection : middleAction.IntertwiningMap oppositeAction
  isCover : Representation.OneCohomology.IsCover projection

end CFSG.Quasithin.ChapterG.Section05.Structure
