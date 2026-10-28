module

public import Theory.SpecificGroups.G2Five.AtlasBoundCertificate.SchreierData
public import Theory.SpecificGroups.G2Five.AtlasBoundCertificate.SchreierRawEdgeCodes
public import Theory.SpecificGroups.G2Five.AtlasBoundCertificate.SchreierRawChoices
public import Theory.SpecificGroups.G2Five.AtlasBoundCertificate.SchreierCollapseCodes

/-!
# The unreduced Schreier alphabet

The 3909 labels are the two protected subgroup words and the non-tree edges,
in the original point-order numbering of `SchreierSource/README.md`. Their
zero-based Lean indices are one less than the signed integers in the trace.
Vertices, in contrast, use the BFS numbering of `SchreierData`.

This interface separates the elementary tree/inverse-edge proof from the
short-relation collapse. `RawRelations` records unreduced words, so a replay
must justify any free or cyclic cancellation it uses. None of these definitions
assumes that the permutation representation is faithful.
-/

@[expose] public section
namespace G2Five.AtlasPresentation.SchreierBoundData
open Subgroup.CosetWordCertificate

abbrev RawAlphabet := Fin 3909

def decodeRawEdge (c : Nat) : Word RawAlphabet :=
  if c = 0 then [] else [(⟨((c - 1) / 2) % 3909, Nat.mod_lt _ (by decide)⟩, c % 2 == 1)]

def rawEdgeWord (i : Nat) (a : Letter Bool) : Word RawAlphabet :=
  decodeRawEdge (rawEdgeCodes (4 * i + originalCode a))

def rawTrace (i : Nat) : Word Bool → Word RawAlphabet
  | [] => []
  | a :: w => rawEdgeWord i a ++ rawTrace (next i a) w

def rawProtectedLabel (b : Bool) : RawAlphabet :=
  ⟨if b then 1 else 0, by cases b <;> decide⟩

def RawRelations {G : Type*} [Group G] (x : RawAlphabet → G) : Prop :=
  (∀ (i : Fin 3906) (r : Fin 22),
    eval x (rawTrace i (boundLetters (word r))) = 1) ∧
  (∀ b : Bool, eval x (rawTrace 0 (boundLetters (boundWord b))) = x (rawProtectedLabel b))

/-- The canonical oriented non-tree edges, together with the protected words. -/
def rawGenerators (k : RawAlphabet) : Model :=
  if k.val = 0 then boundGenerator false else
  if k.val = 1 then boundGenerator true else
    let c := rawChoices k.val
    let i := c / 4
    let a := originalLetter (c % 4)
    edgeElement representative BoundCertificate.generators i (liftLetter a) (next i a)

theorem rawGenerators_protected (b : Bool) :
    rawGenerators (rawProtectedLabel b) = boundGenerator b := by
  cases b <;> rfl

def RawEdgeSound : Prop := ∀ (i : Fin 3906) (a : Letter Bool),
  eval rawGenerators (rawEdgeWord i a) =
    edgeElement representative BoundCertificate.generators i (liftLetter a) (next i a)

/-- The recorded signed collapse assignment, without any assertion of soundness. -/
def collapseWord (k : RawAlphabet) : Word ReducedAlphabet :=
  decodeEdge (collapseCodes k.val)

/-- Select reduced generators in any interpretation of the raw alphabet, using
exactly the same edges and signs as `reducedGenerators`. -/
def collapseGenerators {G : Type*} [Group G] (x : RawAlphabet → G)
    (k : ReducedAlphabet) : G :=
  if k.val = 0 then x (rawProtectedLabel false) else
  if k.val = 1 then x (rawProtectedLabel true) else
    let c := choices k.val
    let i := c.1 / 4
    let a := originalLetter (c.1 % 4)
    let y := eval x (rawEdgeWord i a)
    if c.2 = 0 then y else y⁻¹

/-- Finite relator endpoints, a table property independent of group soundness. -/
def RelatorLoops : Prop := ∀ (i : Fin 3906) (r : Fin 22),
  traceEnd next i (boundLetters (word r)) = i

def ProtectedLoops : Prop := ∀ b : Bool,
  traceEnd next 0 (boundLetters (boundWord b)) = 0

end G2Five.AtlasPresentation.SchreierBoundData
