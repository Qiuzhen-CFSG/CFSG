module
public import Theory.SpecificGroups.Triality.RootPresentationRecognition.WeylAction

/-!
# Signed D₄ root tables for the triality presentation

Kernel-checked tables compute both simple reflections on every signed folded
root. The arm reflection shifts the orbit origins of C and D in opposite
directions. All tables are connected to the actual D₄ root enumeration and
reflection action. The final pairing calculation verifies the six torus
characters against the actual simple coroots in the tuple (t,F(t),F²(t),u).

Source: GLS3 2.4.4, 2.4.7–8, with the published `FoldedRoots` orbit order.
-/

@[expose] public noncomputable section
namespace Triality.Standard.RootPresentationRecognition.RootTable
open Parabolics Parabolics.RankOneMatrices ConcreteBruhat PositiveCoordinates
open PositiveCoordinates.SumExchangeData RadicalCoordinates.LeviCommutators
open Theory.AlgebraicGroup.StandardRootSystem

/-- Both signs in the same 24-element D₄ root enumeration. -/
def signedIndex (s : Bool) (i : Fin 12) : Fin 24 :=
  if s then positiveIndex i else negativeIndex (positiveIndex i)

def armIndex (i : Fin 24) : Fin 24 :=
  reflectionTable 0 (reflectionTable 2 (reflectionTable 3 i))

def armShortTarget (s : Bool) (i j : Fin 3) : Fin 24 :=
  if i = 0 then signedIndex (!s) (shortPosition 0 j)
  else if i = 1 then signedIndex s (shortPosition 2 (j+1))
  else signedIndex s (shortPosition 1 (j+2))

def centralLongTarget (s : Bool) (i : Fin 3) : Fin 24 :=
  if i = 0 then signedIndex (!s) (longPosition 0)
  else signedIndex s (longPosition (![0,2,1] i))

/-- In the literal orbit order, C rotates one place forward and D one place
backward under the arm reflection. -/
theorem arms_short_index (s : Bool) (i j : Fin 3) :
    armIndex (signedIndex s (shortPosition i j)) = armShortTarget s i j := by
  revert s i j
  decide +kernel

theorem arms_long_index (s : Bool) (i : Fin 3) :
    armIndex (signedIndex s (longPosition i)) = signedIndex s (longPosition (![1,0,2] i)) := by
  revert s i
  decide +kernel

theorem central_short_index (s : Bool) (i j : Fin 3) :
    reflectionTable 1 (signedIndex s (shortPosition i j)) =
      signedIndex s (shortPosition (![1,0,2] i) j) := by
  revert s i j
  decide +kernel

theorem central_long_index (s : Bool) (i : Fin 3) :
    reflectionTable 1 (signedIndex s (longPosition i)) = centralLongTarget s i := by
  revert s i
  decide +kernel

private theorem arms_enumeration (i : Fin 24) :
    (foldedRootReflection .arms).val (rootEnumeration i) = rootEnumeration (armIndex i) := by
  change rootReflection 0 (rootReflection 2 (rootReflection 3 _)) = _
  rw [rootReflection,rootReflection,rootReflection,
    ← rootEnumeration_reflectionTable,← rootEnumeration_reflectionTable,
    ← rootEnumeration_reflectionTable]
  rfl

private theorem central_enumeration (i : Fin 24) :
    (foldedRootReflection .central).val (rootEnumeration i) =
      rootEnumeration (reflectionTable 1 i) := by
  change rootReflection 1 _ = _
  rw [rootReflection,← rootEnumeration_reflectionTable]

/-- The checked finite table acts on actual D₄ roots, on both signs. -/
theorem arms_short (s : Bool) (i j : Fin 3) :
    (foldedRootReflection .arms).val (rootEnumeration (signedIndex s (shortPosition i j))) =
      rootEnumeration (armShortTarget s i j) := by
  rw [arms_enumeration,arms_short_index]

theorem arms_long (s : Bool) (i : Fin 3) :
    (foldedRootReflection .arms).val (rootEnumeration (signedIndex s (longPosition i))) =
      rootEnumeration (signedIndex s (longPosition (![1,0,2] i))) := by
  rw [arms_enumeration,arms_long_index]

theorem central_short (s : Bool) (i j : Fin 3) :
    (foldedRootReflection .central).val (rootEnumeration (signedIndex s (shortPosition i j))) =
      rootEnumeration (signedIndex s (shortPosition (![1,0,2] i) j)) := by
  rw [central_enumeration,central_short_index]

theorem central_long (s : Bool) (i : Fin 3) :
    (foldedRootReflection .central).val (rootEnumeration (signedIndex s (longPosition i))) =
      rootEnumeration (centralLongTarget s i) := by
  rw [central_enumeration,central_long_index]

/-- One representative of each folded positive root, in the A,B,C,D,E,F order. -/
def origin : Fin 6 → Fin 12 := ![0,3,4,7,10,11]

/-- The four simple-coroot exponents in the tuple (t,F(t),F²(t),u). -/
def weight : Fin 6 → Fin 4 → ℤ :=
  ![![2,0,0,-1], ![-1,-1,-1,2], ![1,-1,-1,1],
    ![1,1,-1,0], ![1,1,1,-1], ![0,0,0,1]]

/-- Verification against the actual root pairing, not a family tag. -/
theorem pairing (i : Fin 6) (j : Fin 4) :
    (typeDRootPairing 2).pairingIn ℤ (rootIndex (origin i))
      (typeDSimpleRootIndex 2 (![0,2,3,1] j)) = weight i j := by
  have hd : (∑ k : Fin 4, rootCoords (simpleIndex (![0,2,3,1] j)) k *
      rootCoords (positiveIndex (origin i)) k) = weight i j := by
    revert i j
    decide +kernel
  apply Int.cast_injective (α := ℝ)
  change (algebraMap ℤ ℝ) _ = (weight i j : ℝ)
  rw [RootPairing.algebraMap_pairingIn, typeDRootPairing_pairing,
    ← rootEnumeration_positiveIndex, ← rootEnumeration_simpleIndex]
  change (∑ k : Fin 4, _ * _) = _
  simp only [← typeDRootPairing_root_val,rootCoords_spec]
  simpa only [Int.cast_sum,Int.cast_mul] using congrArg (fun z : ℤ => (z : ℝ)) hd

end Triality.Standard.RootPresentationRecognition.RootTable
