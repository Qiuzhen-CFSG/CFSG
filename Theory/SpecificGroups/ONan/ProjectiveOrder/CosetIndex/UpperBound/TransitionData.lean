module

public import Theory.SpecificGroups.ONan.ProjectiveOrder.CosetIndex.UpperBound.TransitionData.Encoding
public import Theory.SpecificGroups.ONan.ProjectiveOrder.CosetIndex.UpperBound.TransitionData.Tables

/-!
# Complete numerical input for the O'Nan coset upper bound

The 122760 representatives follow the saved breadth-first tree. Every positive
ambient-generator transition has a destination, a signed local factor word,
and a central unit scalar. Representatives and factors use shared prefix trees.
Tree transitions retain the empty local word and scalar one.

`C_root` and `C_localFactor` certify the root and the local alphabet. This module
makes no assertion of the full matrix identities: those are exactly the
remaining `MatrixCosetData.Valid.transition` obligations for `C`.

The reproducible producer and independent 45-dimensional numerical replay are
in `TransitionData/source/`. External replay is evidence about the data, not a
Lean proof. Sources and attribution: `refs/original/onan/` and
`ProjectiveOrder/source/`.
-/

namespace ONan.OrderCertificate.UpperBound.TransitionData

open Subgroup.CosetWordCertificate

/-- Parent in the breadth-first representative tree. -/
@[expose] public def representativeParent (i : Nat) : Nat := rows i % 2 ^ 17

/-- Ambient-generator code on an edge of the representative tree. -/
@[expose] public def representativeLetter (i : Nat) : Nat := rows i / 2 ^ 17 % 2

/-- Decode an ambient letter; all representative letters have positive sign. -/
@[expose] public def positiveAmbientLetter (n : Nat) : Letter (Fin 4) :=
  (if n % 2 = 0 then 0 else 1, true)

/-- Representative reconstructed from its prefix tree. -/
@[expose] public def representative (i : Fin 122760) : Word (Fin 4) :=
  prefixWord representativeParent representativeLetter positiveAmbientLetter
    representativeFuel i.val

/-- The position, zero or one, of a positive ambient generator. -/
@[expose] public def generatorIndex (a : Bool) : Nat := if a then 1 else 0

/-- The raw destination number (the producer and replay check its range). -/
@[expose] public def destinationIndex (i : Nat) (a : Bool) : Nat :=
  rows i / 2 ^ (18 + 17 * generatorIndex a) % 2 ^ 17

/-- Positive transition destination. -/
@[expose] public def destination (i : Fin 122760) (a : Bool) : Fin 122760 :=
  ⟨destinationIndex i.val a % 122760, Nat.mod_lt _ (by decide)⟩

/-- Shared local-word prefix at a positive transition. -/
@[expose] public def factorIndex (i : Nat) (a : Bool) : Nat :=
  rows i / 2 ^ (52 + 20 * generatorIndex a) % 2 ^ 20

/-- Parent of a shared local-word prefix. -/
@[expose] public def factorParent (i : Nat) : Nat := prefixes i / 4

/-- Signed local-letter code at a shared prefix node. -/
@[expose] public def factorLetter (i : Nat) : Nat := prefixes i % 4

/-- Signed factor word in the two specified local generators. -/
@[expose] public def factor (i : Fin 122760) (a : Bool) : Word (Fin 4) :=
  prefixWord factorParent factorLetter localLetter factorFuel (factorIndex i.val a)

/-- Scalar codes 0, 1, 2 stand for the units 1, 2, 4 in the field. -/
@[expose] public def scalarCode (i : Nat) (a : Bool) : Nat :=
  rows i / 2 ^ (92 + 2 * generatorIndex a) % 4

/-- Decode the three central scalars occurring in the numerical witnesses. -/
@[expose] public def scalarUnit (n : Nat) : (ZMod 7)ˣ :=
  if n = 0 then 1 else if n = 1 then ⟨2, 4, by decide, by decide⟩
  else ⟨4, 2, by decide, by decide⟩

/-- Complete untrusted matrix-coset data; no transition equation is assumed. -/
@[expose] public def C : MatrixCosetData where
  representative := representative
  initial := 0
  destination := destination
  factor := factor
  scalar i a := scalarUnit (scalarCode i.val a)

/-- The distinguished representative is the empty word. -/
public theorem C_root : C.representative C.initial = [] := by rfl

/-- Every factor uses only the two specified local generators, in either sign. -/
public theorem C_localFactor (i : Fin 122760) (a : Bool) (b : Letter (Fin 4))
    (hb : b ∈ C.factor i a) : allowed b = true :=
  prefixWord_allowed factorParent factorLetter factorFuel (factorIndex i.val a) b hb

end ONan.OrderCertificate.UpperBound.TransitionData
