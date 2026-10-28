module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation

/-!
# The subsystem actions in the original representation consumer

Apply the literal subgroup transport to discharge the ordered-pair and
repeated-node clauses of `ofPairActions`. The second constructor also assembles
the disconnected pairs from commuting rank-one actions. The source presentation,
three adjacent actions, and source intersections remain explicit mathematical
inputs. Source: GLS3 §§2.6, 2.9 and Aschbacher--Smith A.2.17, printed p.39.
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
open WordDescent

variable (F : Type*) [Field F]
  (hpresentation : (coverEvaluation F).ker = pairRelationSubgroup F)
  (ρ01 : PairAction F 0 1) (ρ02 : PairAction F 0 2) (ρ03 : PairAction F 0 3)
  (ρ12 : PairAction F 1 2) (ρ13 : PairAction F 1 3) (ρ23 : PairAction F 2 3)

/-- The finite-case construction applied to the actual cover-action consumer. -/
def ofSixPairActions : Cover F →* (complementSpace F ≃ₗ[F] complementSpace F) :=
  ofPairActions F hpresentation
    (fun i j => (pairActionsOfSix F ρ01 ρ02 ρ03 ρ12 ρ13 ρ23 i j).hom)
    (fun i j => (pairActionsOfSix F ρ01 ρ02 ρ03 ρ12 ρ13 ρ23 i j).map_generator)

@[simp] theorem ofSixPairActions_simple (s : Bool) (i : Fin 4) (t : F) :
    ofSixPairActions F hpresentation ρ01 ρ02 ρ03 ρ12 ρ13 ρ23 (coverSimple F s i t) =
      eigenspaceAction F (-1) (f4Simple F s i t) :=
  ofPairActions_simple F hpresentation _ _ s i t

/-- The source intersections and three adjacent actions discharge every local
action input to `ofPairActions`; the presentation is an independent premise. -/
def ofAdjacentPairActions
    (hd : ∀ (i j : Fin 4), DisconnectedPair i j →
      Disjoint (pairSubgroup F i i) (pairSubgroup F j j)) :
    Cover F →* (complementSpace F ≃ₗ[F] complementSpace F) :=
  ofPairActions F hpresentation
    (fun i j => (pairActionsOfAdjacent F ρ01 ρ12 ρ23 hd i j).hom)
    (fun i j => (pairActionsOfAdjacent F ρ01 ρ12 ρ23 hd i j).map_generator)

@[simp] theorem ofAdjacentPairActions_simple
    (hd : ∀ (i j : Fin 4), DisconnectedPair i j →
      Disjoint (pairSubgroup F i i) (pairSubgroup F j j))
    (s : Bool) (i : Fin 4) (t : F) :
    ofAdjacentPairActions F hpresentation ρ01 ρ12 ρ23 hd (coverSimple F s i t) =
      eigenspaceAction F (-1) (f4Simple F s i t) :=
  ofPairActions_simple F hpresentation _ _ s i t

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
