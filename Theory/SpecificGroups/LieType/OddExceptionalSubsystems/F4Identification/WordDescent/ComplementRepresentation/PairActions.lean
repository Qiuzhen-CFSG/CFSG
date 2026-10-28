module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.LocalWords
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.Coordinates
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.Transport
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.Orthogonality

/-!
# Assembly of the six distinct-node complementary actions

There are six unordered pairs of distinct F4 simple roots. Restriction along
the literal subgroup inclusions supplies all reversed pairs and all repeated
nodes. Thus no separate rank-one construction is needed for the diagonal
cases, and no agreement assumptions on different pair actions are needed.

The disconnected pairs are constructed from the rank-one restrictions of the
two end-pair actions, provided their two source subgroups have trivial
intersection. Both source and target commutation are proved in `Orthogonality`.
Thus only three adjacent actions and three concrete source intersections remain
explicit. These are the subsystem mathematics of GLS3 §§2.2--2.6, used for the
inclusions in Aschbacher--Smith A.2.17, printed p.39. `PairActions.Application`
connects this assembly to the existing `ofPairActions` consumer.
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
open WordDescent

variable (F : Type*) [Field F]

/-- All sixteen ordered pairs, including repeated nodes, from the six distinct
unordered pairs. This is conditional assembly, not the construction of its inputs. -/
def pairActionsOfSix
    (ρ01 : PairAction F 0 1) (ρ02 : PairAction F 0 2) (ρ03 : PairAction F 0 3)
    (ρ12 : PairAction F 1 2) (ρ13 : PairAction F 1 3) (ρ23 : PairAction F 2 3)
    (i j : Fin 4) : PairAction F i j := by
  apply Classical.choice
  fin_cases i <;> fin_cases j
  · exact ⟨ρ01.repeatLeft⟩
  · exact ⟨ρ01⟩
  · exact ⟨ρ02⟩
  · exact ⟨ρ03⟩
  · exact ⟨ρ01.reverse⟩
  · exact ⟨ρ01.repeatRight⟩
  · exact ⟨ρ12⟩
  · exact ⟨ρ13⟩
  · exact ⟨ρ02.reverse⟩
  · exact ⟨ρ12.reverse⟩
  · exact ⟨ρ23.repeatLeft⟩
  · exact ⟨ρ23⟩
  · exact ⟨ρ03.reverse⟩
  · exact ⟨ρ13.reverse⟩
  · exact ⟨ρ23.reverse⟩
  · exact ⟨ρ23.repeatRight⟩

/-- The exact family of marked homomorphisms required by `ofPairActions`.
Reversal only exchanges the node selector; it preserves the sign and parameter. -/
theorem exists_pairActions_of_six
    (ρ01 : PairAction F 0 1) (ρ02 : PairAction F 0 2) (ρ03 : PairAction F 0 3)
    (ρ12 : PairAction F 1 2) (ρ13 : PairAction F 1 3) (ρ23 : PairAction F 2 3) :
    ∃ ρ : ∀ i j : Fin 4,
        pairSubgroup F i j →* (complementSpace F ≃ₗ[F] complementSpace F),
      ∀ (i j : Fin 4) (s k : Bool) (t : F),
        ρ i j (pairGenerator F i j s k t) =
          eigenspaceAction F (-1) (f4Simple F s (pairNode i j k) t) :=
  ⟨fun i j => (pairActionsOfSix F ρ01 ρ02 ρ03 ρ12 ρ13 ρ23 i j).hom,
    fun i j => (pairActionsOfSix F ρ01 ρ02 ρ03 ρ12 ρ13 ρ23 i j).map_generator⟩

/-- Assemble disconnected pairs by multiplying commuting rank-one actions,
then supply reversed and repeated pairs by literal subgroup restriction.
The adjacent actions and source intersections remain explicit obligations. -/
def pairActionsOfAdjacent
    (ρ01 : PairAction F 0 1) (ρ12 : PairAction F 1 2) (ρ23 : PairAction F 2 3)
    (hd : ∀ (i j : Fin 4), DisconnectedPair i j →
      Disjoint (pairSubgroup F i i) (pairSubgroup F j j)) :
    ∀ i j : Fin 4, PairAction F i j :=
  pairActionsOfSix F ρ01
    (disconnectedPairActionOfDisjoint F (Or.inl ⟨rfl, rfl⟩)
      (hd 0 2 (Or.inl ⟨rfl, rfl⟩)) ρ01.repeatLeft ρ23.repeatLeft)
    (disconnectedPairActionOfDisjoint F (Or.inr (Or.inl ⟨rfl, rfl⟩))
      (hd 0 3 (Or.inr (Or.inl ⟨rfl, rfl⟩))) ρ01.repeatLeft ρ23.repeatRight)
    ρ12
    (disconnectedPairActionOfDisjoint F (Or.inr (Or.inr ⟨rfl, rfl⟩))
      (hd 1 3 (Or.inr (Or.inr ⟨rfl, rfl⟩))) ρ01.repeatRight ρ23.repeatRight)
    ρ23

/-- The literal local-homomorphism contract follows from the three adjacent
constructions and the independent rank-one intersection calculation. -/
theorem exists_pairActions_of_adjacent_and_disjoint
    (ρ01 : PairAction F 0 1) (ρ12 : PairAction F 1 2) (ρ23 : PairAction F 2 3)
    (hd : ∀ (i j : Fin 4), DisconnectedPair i j →
      Disjoint (pairSubgroup F i i) (pairSubgroup F j j)) :
    ∃ ρ : ∀ i j : Fin 4,
        pairSubgroup F i j →* (complementSpace F ≃ₗ[F] complementSpace F),
      ∀ (i j : Fin 4) (s k : Bool) (t : F),
        ρ i j (pairGenerator F i j s k t) =
          eigenspaceAction F (-1) (f4Simple F s (pairNode i j k) t) :=
  ⟨fun i j => (pairActionsOfAdjacent F ρ01 ρ12 ρ23 hd i j).hom,
    fun i j => (pairActionsOfAdjacent F ρ01 ρ12 ρ23 hd i j).map_generator⟩

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
