module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityCensusNodes
public import Theory.GroupTheory.FrattiniNormalizerWitnessGenerators

/-!
# Generator actions for the excluded small parity census nodes

For each of the 97 proposed exclusions, its displayed conjugating element has
all generator displacements in the embedded Frattini subgroup. Each displacement
is a checked product of squares of words in the defining generators. Consequently,
once the element is proved outside the subgroup, it is a Frattini normalizer
witness. This module does not assert the outside-membership certificates.

Source: the root words of `SmallParityCensusNodes`, in the Shinoda (1975), (2.3)
model. External calculation selected the short square words; every identity is
verified by Lean's kernel. The conjugating words already use Lean's orientation.
-/

namespace ReeTwo.SylowModel
open Theory.GroupTheory

/-- Positions with proposed Frattini exclusions, omitting large nodes and candidates. -/
@[expose] public def smallParityCensusWitnessIndex (i : Fin 97) : Fin 131 :=
  ![15, 16, 17, 18, 19, 21, 24, 26, 27, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 46, 47, 48, 49, 51, 52, 53, 54, 55, 56, 57, 58, 59, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 79, 80, 82, 83, 84, 85, 86, 87, 88, 90, 91, 92, 93, 94, 95, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 117, 118, 119, 120, 122, 123, 126, 127, 128, 129, 130] i

/-- The proposed outside elements in Lean's left-conjugation convention. -/
@[expose] public def smallParityCensusWitness (i : Fin 97) : SylowModel :=
  (#[
    root 3 * root 8,
    root 3 * root 8,
    root 3 * root 8,
    rootOne,
    root 2 * root 3 * root 4 * root 5 * root 6,
    root 2 * root 3 * root 4 * root 9,
    root 2 * root 3 * root 4 * root 5 * root 6,
    rootOne,
    root 2 * root 3 * root 4 * root 5 * root 6,
    root 2 * root 4 * root 5 * root 6 * root 9,
    root 3 * root 8,
    root 2 * root 4 * root 9,
    root 3 * root 8,
    root 3 * root 8,
    root 3 * root 8,
    rootOne * root 2 * root 3 * root 5 * root 7,
    rootOne,
    rootOne * root 2 * root 3 * root 9,
    root 3 * root 8,
    root 2 * root 3 * root 4 * root 9,
    root 2 * root 3 * root 4 * root 9,
    root 2 * root 3 * root 4 * root 5 * root 6,
    root 2 * root 3 * root 4 * root 5 * root 6,
    root 6,
    root 6,
    root 5 * root 6 * root 7,
    rootOne * root 2 * root 3 * root 9,
    rootOne ^ 2,
    rootOne ^ 2,
    root 4 * root 7 * root 8,
    root 4 * root 7 * root 8,
    root 4 * root 7 * root 8,
    root 4 * root 7 * root 8,
    root 2 * root 3 * root 4 * root 5 * root 6,
    root 4 * root 7 * root 8,
    root 2 * root 3 * root 4 * root 5 * root 6,
    root 4 * root 7 * root 8,
    root 4 * root 7 * root 8,
    root 2 * root 4 * root 9,
    root 4 * root 7 * root 8,
    root 2 * root 4 * root 9,
    root 3 * root 6 * root 8 * root 9,
    root 2 * root 3 * root 4 * root 5 * root 6,
    rootOne ^ 2,
    root 3 * root 8,
    root 3 * root 8,
    rootOne * root 2 * root 3 * root 9,
    rootOne ^ 2,
    rootOne * root 2 * root 3 * root 5 * root 7,
    rootOne * root 6 * root 7 * root 8 * root 9,
    rootOne ^ 2,
    rootOne ^ 2,
    root 2 * root 3 * root 5 * root 6 * root 7,
    root 2 * root 3 * root 4 * root 5 * root 6,
    root 6,
    root 4 * root 7 * root 8,
    root 4 * root 7 * root 8,
    root 4 * root 7 * root 8,
    root 4 * root 7 * root 8,
    root 4 * root 5 * root 6 * root 8,
    rootOne ^ 3 * root 2 * root 3 * root 9,
    rootOne ^ 2,
    root 4 * root 7 * root 8,
    rootOne ^ 2,
    root 4 * root 7 * root 8,
    rootOne ^ 2,
    root 6,
    root 2 * root 4 * root 9,
    root 2 * root 4 * root 9,
    root 3 * root 8,
    root 3 * root 8,
    rootOne * root 2 * root 3 * root 6 * root 7 * root 8 * root 9,
    rootOne * root 2 * root 3 * root 5 * root 7,
    root 4 * root 7 * root 8,
    root 4 * root 7 * root 8,
    root 7 * root 8,
    root 4 * root 7 * root 8,
    root 4 * root 7 * root 8,
    root 7 * root 8,
    root 4 * root 7 * root 8,
    root 4 * root 7 * root 8,
    root 4 * root 7 * root 8,
    root 7 * root 8,
    root 4 * root 7 * root 8,
    root 7 * root 8,
    root 7 * root 8,
    root 4 * root 7 * root 8,
    root 7 * root 8,
    root 3 * root 8,
    root 3 * root 7,
    root 7 * root 8,
    root 4 * root 7 * root 8,
    root 4 * root 7 * root 8,
    root 4 * root 7 * root 8,
    root 4 * root 7 * root 8,
    root 8 * root 9,
    root 8 * root 9] : Array SylowModel).getD i.val 1

@[expose] public def SmallParityCensusWitnessData.generatorBlock0 : Array (Fin 9 → SylowModel) :=
  #[
    ![rootOne ^ 3, rootOne ^ 2, root 5 * root 8, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8 * root 9, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8, root 9],
    ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 7 * root 8 * root 9, root 4 * root 5 * root 7 * root 9, root 4 * root 9, root 6 * root 9, root 7 * root 8 * root 9, root 8 * root 9, root 9],
    ![rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2 * root 1 * root 3 * root 5 * root 7, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 4 * root 5, root 4 * root 9, root 6 * root 8, root 7 * root 8, root 8 * root 9, root 9],
    ![rootOne ^ 3 * root 3 * root 4, rootOne ^ 2 * root 4 * root 8, root 5 * root 8, root 2 * root 3 * root 4 * root 7 * root 9, root 4 * root 9, root 6 * root 7 * root 8, root 7 * root 8, root 8, root 9],
    ![root 3, rootOne ^ 3, root 5 * root 8, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8],
    ![root 3, rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8],
    ![root 3 * root 5 * root 8, rootOne ^ 3, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8],
    ![root 3 * root 5 * root 8, rootOne ^ 3 * root 5 * root 8, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8],
    ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 4 * root 6 * root 7, root 4 * root 5 * root 7 * root 9, root 6 * root 7, root 7 * root 9, root 8, root 9],
    ![rootOne ^ 3, root 5 * root 8, rootOne ^ 2, root 4 * root 8, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8, root 8],
    ![rootOne ^ 3, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4 * root 8, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8, root 8],
    ![rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 8, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8, root 8],
    ![rootOne ^ 3 * root 5 * root 8, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4 * root 8, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8, root 8],
    ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 4 * root 7, root 4 * root 5 * root 7 * root 9, root 6 * root 8 * root 9, root 7 * root 8, root 8 * root 9, root 9, root 9],
    ![rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2 * root 1 * root 3 * root 5 * root 7, root 4 * root 7 * root 9, root 4 * root 5, root 6, root 7 * root 8 * root 9, root 8 * root 9, root 9, root 9],
    ![rootOne ^ 3 * root 3 * root 4, root 5 * root 8, rootOne ^ 2 * root 4 * root 8, root 4 * root 7, root 6 * root 7 * root 8, root 7 * root 8, root 9, root 8, root 8]]

@[expose] public def SmallParityCensusWitnessData.generatorBlock1 : Array (Fin 9 → SylowModel) :=
  #[
    ![rootOne ^ 3 * root 3 * root 4, root 2 * root 3 * root 4 * root 7 * root 9, rootOne ^ 2 * root 4 * root 8, root 4 * root 7, root 6 * root 7 * root 8, root 7 * root 8, root 9, root 8, root 8],
    ![rootOne ^ 3 * root 3 * root 4, root 2 * root 3 * root 4 * root 5 * root 7 * root 8, rootOne ^ 2 * root 4 * root 8, root 4 * root 7, root 6 * root 7 * root 8, root 7 * root 8, root 9, root 8, root 8],
    ![rootOne ^ 3 * root 3 * root 4 * root 5 * root 8, root 2 * root 3 * root 4 * root 7 * root 9, rootOne ^ 2 * root 4 * root 8, root 4 * root 7, root 6 * root 7 * root 8, root 7 * root 8, root 9, root 8, root 8],
    ![root 3, rootOne ^ 3, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8, root 8],
    ![root 3, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8, root 8],
    ![root 3 * root 5 * root 8, rootOne ^ 3, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8, root 8],
    ![root 3 * root 5 * root 8, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8, root 8],
    ![root 3, rootOne ^ 3, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4, root 7, root 9, root 8, root 8],
    ![root 3 * root 6 * root 7 * root 8, rootOne ^ 3, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4, root 7, root 9, root 8, root 8],
    ![root 2 * root 4 * root 5 * root 9, rootOne ^ 3, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8, root 8],
    ![root 2 * root 4 * root 5 * root 9, rootOne ^ 3 * root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8, root 8],
    ![root 3, rootOne ^ 3 * root 5 * root 8, root 2 * root 3 * root 4 * root 7, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7, root 9, root 8, root 8],
    ![root 3 * root 6 * root 7 * root 8, rootOne ^ 3 * root 5 * root 8, root 2 * root 3 * root 4 * root 7, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7, root 9, root 8, root 8],
    ![root 2 * root 4 * root 8, rootOne ^ 3, root 5 * root 8, rootOne ^ 2, root 6 * root 7 * root 8, root 8 * root 9, root 7 * root 8 * root 9, root 8, root 8],
    ![root 2 * root 4 * root 8, rootOne ^ 3, root 4 * root 5 * root 8 * root 9, rootOne ^ 2, root 6 * root 7 * root 8, root 8 * root 9, root 7 * root 8 * root 9, root 8, root 8],
    ![root 2 * root 8, rootOne ^ 3, root 5 * root 8, rootOne ^ 2, root 6 * root 7 * root 8, root 8 * root 9, root 7 * root 8 * root 9, root 8, root 8]]

@[expose] public def SmallParityCensusWitnessData.generatorBlock2 : Array (Fin 9 → SylowModel) :=
  #[
    ![root 2 * root 8, rootOne ^ 3, root 4 * root 5 * root 8 * root 9, rootOne ^ 2, root 6 * root 7 * root 8, root 8 * root 9, root 7 * root 8 * root 9, root 8, root 8],
    ![root 2 * root 4 * root 8, rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 8 * root 9, root 8, root 8],
    ![root 2 * root 4 * root 8, rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 9, rootOne ^ 2, root 4 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 8 * root 9, root 8, root 8],
    ![root 2 * root 4 * root 6 * root 7, rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 8 * root 9, root 8, root 8],
    ![root 2 * root 4 * root 6 * root 7, rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 9, rootOne ^ 2, root 4 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 8 * root 9, root 8, root 8],
    ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 6, root 4 * root 5 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9, root 9],
    ![rootOne ^ 3, root 4 * root 8, rootOne ^ 2, root 6 * root 7 * root 8, root 9, root 7 * root 8 * root 9, root 8, root 8, root 8],
    ![rootOne ^ 3, root 4 * root 5 * root 9, rootOne ^ 2, root 6 * root 7 * root 8, root 9, root 7 * root 8 * root 9, root 8, root 8, root 8],
    ![rootOne ^ 3 * root 5 * root 8, root 4 * root 8, rootOne ^ 2, root 6 * root 7 * root 8, root 9, root 7 * root 8 * root 9, root 8, root 8, root 8],
    ![rootOne ^ 3, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4 * root 8, root 7 * root 9, root 9, root 8, root 8, root 8],
    ![rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 8 * root 9, root 8, root 8, root 8],
    ![rootOne ^ 3 * root 5 * root 8, root 2 * root 3 * root 4 * root 7, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 8, root 7 * root 9, root 9, root 8, root 8, root 8],
    ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 6 * root 8 * root 9, root 4 * root 5 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9, root 9, root 9],
    ![rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2 * root 1 * root 3 * root 5 * root 7, root 6, root 4 * root 5, root 7 * root 8 * root 9, root 8 * root 9, root 9, root 9, root 9],
    ![rootOne ^ 3 * root 3 * root 4, root 4 * root 7, rootOne ^ 2 * root 4 * root 8, root 6 * root 7 * root 8, root 9, root 7 * root 8, root 8, root 8, root 8],
    ![rootOne ^ 3 * root 3 * root 4, root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2 * root 4 * root 8, root 6 * root 7 * root 8, root 9, root 7 * root 8, root 8, root 8, root 8]]

@[expose] public def SmallParityCensusWitnessData.generatorBlock3 : Array (Fin 9 → SylowModel) :=
  #[
    ![rootOne ^ 3 * root 3 * root 4 * root 5 * root 8, root 4 * root 7, rootOne ^ 2 * root 4 * root 8, root 6 * root 7 * root 8, root 9, root 7 * root 8, root 8, root 8, root 8],
    ![rootOne ^ 3 * root 3 * root 4, root 2 * root 3 * root 4 * root 7 * root 9, rootOne ^ 2 * root 4 * root 8, root 4 * root 7, root 7 * root 9, root 8 * root 9, root 8, root 8, root 8],
    ![rootOne ^ 3 * root 3 * root 4, root 2 * root 3 * root 4 * root 5 * root 6, rootOne ^ 2 * root 4 * root 8, root 4 * root 6 * root 8 * root 9, root 9, root 7, root 8, root 8, root 8],
    ![rootOne ^ 3 * root 3 * root 4 * root 5 * root 8, root 2 * root 3 * root 4 * root 7 * root 9, rootOne ^ 2 * root 4 * root 6 * root 7, root 4 * root 7, root 7 * root 9, root 8 * root 9, root 8, root 8, root 8],
    ![root 3 * root 5 * root 8, rootOne ^ 3, rootOne ^ 2, root 4 * root 6 * root 7 * root 8 * root 9, root 9, root 7 * root 8 * root 9, root 8, root 8, root 8],
    ![root 3 * root 5 * root 8, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 6 * root 7 * root 8, root 9, root 7 * root 8, root 8, root 8, root 8],
    ![root 2 * root 4 * root 8, rootOne ^ 3 * root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4, root 7, root 9, root 8, root 8, root 8],
    ![root 2 * root 4 * root 8, rootOne ^ 3, root 6 * root 7 * root 8, rootOne ^ 2, root 7 * root 8 * root 9, root 8 * root 9, root 8, root 8, root 8],
    ![root 2 * root 4 * root 8, rootOne ^ 3, root 4 * root 6 * root 7 * root 8, rootOne ^ 2, root 7 * root 8 * root 9, root 8 * root 9, root 8, root 8, root 8],
    ![root 2 * root 8, rootOne ^ 3, root 6 * root 7 * root 8, rootOne ^ 2, root 7 * root 8 * root 9, root 8 * root 9, root 8, root 8, root 8],
    ![root 2 * root 8, rootOne ^ 3, root 4 * root 6 * root 7 * root 8, rootOne ^ 2, root 7 * root 8 * root 9, root 8 * root 9, root 8, root 8, root 8],
    ![root 2 * root 4 * root 5 * root 9, rootOne ^ 3, rootOne ^ 2, root 6 * root 7 * root 8, root 8 * root 9, root 7 * root 8 * root 9, root 8, root 8, root 8],
    ![root 2 * root 4 * root 5 * root 9, rootOne ^ 3 * root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2 * root 4 * root 6 * root 8 * root 9, root 6 * root 8 * root 9, root 8 * root 9, root 7, root 8, root 8, root 8],
    ![root 2 * root 4 * root 8, rootOne ^ 3 * root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7, root 9, root 8, root 8, root 8],
    ![root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, root 6 * root 7 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8 * root 9, root 8, root 8, root 8],
    ![root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, root 4 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8 * root 9, root 8, root 8, root 8]]

@[expose] public def SmallParityCensusWitnessData.generatorBlock4 : Array (Fin 9 → SylowModel) :=
  #[
    ![root 2 * root 8 * root 9, rootOne ^ 3 * root 5 * root 8, root 6 * root 7 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8 * root 9, root 8, root 8, root 8],
    ![root 2 * root 8 * root 9, rootOne ^ 3 * root 5 * root 8, root 4 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8 * root 9, root 8, root 8, root 8],
    ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 4 * root 5 * root 7 * root 9, root 8 * root 9, root 9, root 9, root 9],
    ![rootOne ^ 3, root 4 * root 8, root 9, rootOne ^ 2, root 7 * root 8 * root 9, root 8, root 8, root 8, root 8],
    ![rootOne ^ 3 * root 5 * root 8, root 4 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 9, root 7 * root 8 * root 9, root 8, root 8, root 8, root 8],
    ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 7 * root 8, root 4 * root 5 * root 7 * root 9, root 8 * root 9, root 9, root 9, root 9, root 9],
    ![rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2 * root 1 * root 3 * root 5 * root 7, root 7 * root 8 * root 9, root 4 * root 5, root 8 * root 9, root 9, root 9, root 9, root 9],
    ![rootOne ^ 3 * root 3 * root 4, root 4 * root 7, root 9, rootOne ^ 2 * root 4 * root 8, root 7 * root 8, root 8, root 8, root 8, root 8],
    ![rootOne ^ 3 * root 3 * root 4 * root 5 * root 8, root 4 * root 7, rootOne ^ 2 * root 4 * root 6 * root 7, root 8 * root 9, root 7 * root 8, root 8, root 8, root 8, root 8],
    ![root 3, rootOne ^ 3, root 9, rootOne ^ 2, root 4, root 8, root 8, root 8, root 8],
    ![root 3, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 9, root 8, root 8, root 8, root 8],
    ![root 3 * root 6 * root 7 * root 8, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 7 * root 8, root 8 * root 9, root 8, root 8, root 8, root 8],
    ![root 2 * root 4 * root 8, rootOne ^ 3, root 4, rootOne ^ 2, root 8 * root 9, root 8, root 8, root 8, root 8],
    ![root 2 * root 4 * root 8, rootOne ^ 3, root 7, rootOne ^ 2, root 8 * root 9, root 8, root 8, root 8, root 8],
    ![root 2 * root 4 * root 8, rootOne ^ 3, root 4 * root 7, rootOne ^ 2, root 8 * root 9, root 8, root 8, root 8, root 8],
    ![root 2 * root 8, rootOne ^ 3, root 7, rootOne ^ 2, root 8 * root 9, root 8, root 8, root 8, root 8]]

@[expose] public def SmallParityCensusWitnessData.generatorBlock5 : Array (Fin 9 → SylowModel) :=
  #[
    ![root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, root 4 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8, root 8 * root 9, root 8, root 8, root 8, root 8],
    ![root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, root 7, rootOne ^ 2 * root 6 * root 7 * root 8, root 8 * root 9, root 8, root 8, root 8, root 8],
    ![root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, root 4 * root 7 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8, root 8 * root 9, root 8, root 8, root 8, root 8],
    ![root 2 * root 8 * root 9, rootOne ^ 3 * root 5 * root 8, root 7, rootOne ^ 2 * root 6 * root 7 * root 8, root 8 * root 9, root 8, root 8, root 8, root 8],
    ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 8, root 4 * root 5 * root 7 * root 9, root 9, root 9, root 9, root 9],
    ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 6 * root 8, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 8, root 4 * root 5 * root 7 * root 9, root 9, root 9, root 9, root 9],
    ![rootOne ^ 3 * root 5 * root 8, root 4 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 9, root 8, root 8, root 8, root 8, root 8],
    ![rootOne ^ 3 * root 5 * root 8, root 4 * root 7 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8, root 9, root 8, root 8, root 8, root 8, root 8],
    ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 8 * root 9, root 4 * root 5 * root 7 * root 9, root 9, root 9, root 9, root 9, root 9],
    ![rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2 * root 1 * root 3 * root 5 * root 7, root 8 * root 9, root 4 * root 5, root 9, root 9, root 9, root 9, root 9],
    ![rootOne ^ 3 * root 3 * root 4 * root 5 * root 8, root 4 * root 7, rootOne ^ 2 * root 4 * root 6 * root 7, root 8 * root 9, root 8, root 8, root 8, root 8, root 8],
    ![rootOne ^ 3 * root 3 * root 4 * root 5 * root 8, root 4 * root 8, rootOne ^ 2 * root 4 * root 6 * root 7, root 8 * root 9, root 8, root 8, root 8, root 8, root 8],
    ![root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 8 * root 9, root 8, root 8, root 8, root 8, root 8],
    ![root 2 * root 4 * root 8, rootOne ^ 3 * root 4 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 8 * root 9, root 8, root 8, root 8, root 8, root 8],
    ![root 2 * root 8 * root 9, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 8 * root 9, root 8, root 8, root 8, root 8, root 8],
    ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 4 * root 5 * root 7 * root 9, root 9, root 9, root 9, root 9, root 9, root 9]]

@[expose] public def SmallParityCensusWitnessData.generatorBlock6 : Array (Fin 9 → SylowModel) :=
  #[
    ![rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2 * root 1 * root 3 * root 5 * root 7, root 4 * root 5, root 9, root 9, root 9, root 9, root 9, root 9]]

/-- Ordered defining generators, padded by repetition of the final generator. -/
@[expose] public def smallParityCensusWitnessGenerator (i : Fin 97) : Fin 9 → SylowModel :=
  ((#[SmallParityCensusWitnessData.generatorBlock0, SmallParityCensusWitnessData.generatorBlock1, SmallParityCensusWitnessData.generatorBlock2, SmallParityCensusWitnessData.generatorBlock3, SmallParityCensusWitnessData.generatorBlock4, SmallParityCensusWitnessData.generatorBlock5, SmallParityCensusWitnessData.generatorBlock6] : Array (Array (Fin 9 → SylowModel))).getD
    (i.val / 16) #[]).getD (i.val % 16) (fun _ => 1)

private theorem range_4 {α : Type*} (a0 a1 a2 a3 : α) :
    Set.range ![a0, a1, a2, a3, a3, a3, a3, a3, a3] = {a0, a1, a2, a3} := by
  ext x
  simp [eq_comm, or_comm, or_left_comm]

private theorem range_5 {α : Type*} (a0 a1 a2 a3 a4 : α) :
    Set.range ![a0, a1, a2, a3, a4, a4, a4, a4, a4] = {a0, a1, a2, a3, a4} := by
  ext x
  simp [eq_comm, or_comm, or_left_comm]

private theorem range_6 {α : Type*} (a0 a1 a2 a3 a4 a5 : α) :
    Set.range ![a0, a1, a2, a3, a4, a5, a5, a5, a5] = {a0, a1, a2, a3, a4, a5} := by
  ext x
  simp [eq_comm, or_comm, or_left_comm]

private theorem range_7 {α : Type*} (a0 a1 a2 a3 a4 a5 a6 : α) :
    Set.range ![a0, a1, a2, a3, a4, a5, a6, a6, a6] = {a0, a1, a2, a3, a4, a5, a6} := by
  ext x
  simp [eq_comm, or_comm, or_left_comm]

private theorem range_8 {α : Type*} (a0 a1 a2 a3 a4 a5 a6 a7 : α) :
    Set.range ![a0, a1, a2, a3, a4, a5, a6, a7, a7] = {a0, a1, a2, a3, a4, a5, a6, a7} := by
  ext x
  simp [eq_comm, or_comm, or_left_comm]

private theorem range_9 {α : Type*} (a0 a1 a2 a3 a4 a5 a6 a7 a8 : α) :
    Set.range ![a0, a1, a2, a3, a4, a5, a6, a7, a8] = {a0, a1, a2, a3, a4, a5, a6, a7, a8} := by
  ext x
  simp [eq_comm, or_comm, or_left_comm]

private theorem generator_closure_0 :
    smallParityCensusNode (smallParityCensusWitnessIndex 0) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 0)) :=
  congrArg Subgroup.closure (range_9 _ _ _ _ _ _ _ _ _).symm

private theorem generator_closure_1 :
    smallParityCensusNode (smallParityCensusWitnessIndex 1) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 1)) :=
  congrArg Subgroup.closure (range_9 _ _ _ _ _ _ _ _ _).symm

private theorem generator_closure_2 :
    smallParityCensusNode (smallParityCensusWitnessIndex 2) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 2)) :=
  congrArg Subgroup.closure (range_9 _ _ _ _ _ _ _ _ _).symm

private theorem generator_closure_3 :
    smallParityCensusNode (smallParityCensusWitnessIndex 3) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 3)) :=
  congrArg Subgroup.closure (range_9 _ _ _ _ _ _ _ _ _).symm

private theorem generator_closure_4 :
    smallParityCensusNode (smallParityCensusWitnessIndex 4) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 4)) :=
  congrArg Subgroup.closure (range_9 _ _ _ _ _ _ _ _ _).symm

private theorem generator_closure_5 :
    smallParityCensusNode (smallParityCensusWitnessIndex 5) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 5)) :=
  congrArg Subgroup.closure (range_9 _ _ _ _ _ _ _ _ _).symm

private theorem generator_closure_6 :
    smallParityCensusNode (smallParityCensusWitnessIndex 6) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 6)) :=
  congrArg Subgroup.closure (range_9 _ _ _ _ _ _ _ _ _).symm

private theorem generator_closure_7 :
    smallParityCensusNode (smallParityCensusWitnessIndex 7) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 7)) :=
  congrArg Subgroup.closure (range_9 _ _ _ _ _ _ _ _ _).symm

private theorem generator_closure_8 :
    smallParityCensusNode (smallParityCensusWitnessIndex 8) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 8)) :=
  congrArg Subgroup.closure (range_9 _ _ _ _ _ _ _ _ _).symm

private theorem generator_closure_9 :
    smallParityCensusNode (smallParityCensusWitnessIndex 9) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 9)) :=
  congrArg Subgroup.closure (range_8 _ _ _ _ _ _ _ _).symm

private theorem generator_closure_10 :
    smallParityCensusNode (smallParityCensusWitnessIndex 10) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 10)) :=
  congrArg Subgroup.closure (range_8 _ _ _ _ _ _ _ _).symm

private theorem generator_closure_11 :
    smallParityCensusNode (smallParityCensusWitnessIndex 11) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 11)) :=
  congrArg Subgroup.closure (range_8 _ _ _ _ _ _ _ _).symm

private theorem generator_closure_12 :
    smallParityCensusNode (smallParityCensusWitnessIndex 12) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 12)) :=
  congrArg Subgroup.closure (range_8 _ _ _ _ _ _ _ _).symm

private theorem generator_closure_13 :
    smallParityCensusNode (smallParityCensusWitnessIndex 13) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 13)) :=
  congrArg Subgroup.closure (range_8 _ _ _ _ _ _ _ _).symm

private theorem generator_closure_14 :
    smallParityCensusNode (smallParityCensusWitnessIndex 14) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 14)) :=
  congrArg Subgroup.closure (range_8 _ _ _ _ _ _ _ _).symm

private theorem generator_closure_15 :
    smallParityCensusNode (smallParityCensusWitnessIndex 15) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 15)) :=
  congrArg Subgroup.closure (range_8 _ _ _ _ _ _ _ _).symm

private theorem generator_closure_16 :
    smallParityCensusNode (smallParityCensusWitnessIndex 16) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 16)) :=
  congrArg Subgroup.closure (range_8 _ _ _ _ _ _ _ _).symm

private theorem generator_closure_17 :
    smallParityCensusNode (smallParityCensusWitnessIndex 17) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 17)) :=
  congrArg Subgroup.closure (range_8 _ _ _ _ _ _ _ _).symm

private theorem generator_closure_18 :
    smallParityCensusNode (smallParityCensusWitnessIndex 18) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 18)) :=
  congrArg Subgroup.closure (range_8 _ _ _ _ _ _ _ _).symm

private theorem generator_closure_19 :
    smallParityCensusNode (smallParityCensusWitnessIndex 19) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 19)) :=
  congrArg Subgroup.closure (range_8 _ _ _ _ _ _ _ _).symm

private theorem generator_closure_20 :
    smallParityCensusNode (smallParityCensusWitnessIndex 20) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 20)) :=
  congrArg Subgroup.closure (range_8 _ _ _ _ _ _ _ _).symm

private theorem generator_closure_21 :
    smallParityCensusNode (smallParityCensusWitnessIndex 21) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 21)) :=
  congrArg Subgroup.closure (range_8 _ _ _ _ _ _ _ _).symm

private theorem generator_closure_22 :
    smallParityCensusNode (smallParityCensusWitnessIndex 22) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 22)) :=
  congrArg Subgroup.closure (range_8 _ _ _ _ _ _ _ _).symm

private theorem generator_closure_23 :
    smallParityCensusNode (smallParityCensusWitnessIndex 23) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 23)) :=
  congrArg Subgroup.closure (range_8 _ _ _ _ _ _ _ _).symm

private theorem generator_closure_24 :
    smallParityCensusNode (smallParityCensusWitnessIndex 24) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 24)) :=
  congrArg Subgroup.closure (range_8 _ _ _ _ _ _ _ _).symm

private theorem generator_closure_25 :
    smallParityCensusNode (smallParityCensusWitnessIndex 25) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 25)) :=
  congrArg Subgroup.closure (range_8 _ _ _ _ _ _ _ _).symm

private theorem generator_closure_26 :
    smallParityCensusNode (smallParityCensusWitnessIndex 26) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 26)) :=
  congrArg Subgroup.closure (range_8 _ _ _ _ _ _ _ _).symm

private theorem generator_closure_27 :
    smallParityCensusNode (smallParityCensusWitnessIndex 27) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 27)) :=
  congrArg Subgroup.closure (range_8 _ _ _ _ _ _ _ _).symm

private theorem generator_closure_28 :
    smallParityCensusNode (smallParityCensusWitnessIndex 28) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 28)) :=
  congrArg Subgroup.closure (range_8 _ _ _ _ _ _ _ _).symm

private theorem generator_closure_29 :
    smallParityCensusNode (smallParityCensusWitnessIndex 29) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 29)) :=
  congrArg Subgroup.closure (range_8 _ _ _ _ _ _ _ _).symm

private theorem generator_closure_30 :
    smallParityCensusNode (smallParityCensusWitnessIndex 30) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 30)) :=
  congrArg Subgroup.closure (range_8 _ _ _ _ _ _ _ _).symm

private theorem generator_closure_31 :
    smallParityCensusNode (smallParityCensusWitnessIndex 31) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 31)) :=
  congrArg Subgroup.closure (range_8 _ _ _ _ _ _ _ _).symm

private theorem generator_closure_32 :
    smallParityCensusNode (smallParityCensusWitnessIndex 32) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 32)) :=
  congrArg Subgroup.closure (range_8 _ _ _ _ _ _ _ _).symm

private theorem generator_closure_33 :
    smallParityCensusNode (smallParityCensusWitnessIndex 33) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 33)) :=
  congrArg Subgroup.closure (range_8 _ _ _ _ _ _ _ _).symm

private theorem generator_closure_34 :
    smallParityCensusNode (smallParityCensusWitnessIndex 34) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 34)) :=
  congrArg Subgroup.closure (range_8 _ _ _ _ _ _ _ _).symm

private theorem generator_closure_35 :
    smallParityCensusNode (smallParityCensusWitnessIndex 35) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 35)) :=
  congrArg Subgroup.closure (range_8 _ _ _ _ _ _ _ _).symm

private theorem generator_closure_36 :
    smallParityCensusNode (smallParityCensusWitnessIndex 36) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 36)) :=
  congrArg Subgroup.closure (range_8 _ _ _ _ _ _ _ _).symm

private theorem generator_closure_37 :
    smallParityCensusNode (smallParityCensusWitnessIndex 37) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 37)) :=
  congrArg Subgroup.closure (range_8 _ _ _ _ _ _ _ _).symm

private theorem generator_closure_38 :
    smallParityCensusNode (smallParityCensusWitnessIndex 38) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 38)) :=
  congrArg Subgroup.closure (range_7 _ _ _ _ _ _ _).symm

private theorem generator_closure_39 :
    smallParityCensusNode (smallParityCensusWitnessIndex 39) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 39)) :=
  congrArg Subgroup.closure (range_7 _ _ _ _ _ _ _).symm

private theorem generator_closure_40 :
    smallParityCensusNode (smallParityCensusWitnessIndex 40) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 40)) :=
  congrArg Subgroup.closure (range_7 _ _ _ _ _ _ _).symm

private theorem generator_closure_41 :
    smallParityCensusNode (smallParityCensusWitnessIndex 41) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 41)) :=
  congrArg Subgroup.closure (range_7 _ _ _ _ _ _ _).symm

private theorem generator_closure_42 :
    smallParityCensusNode (smallParityCensusWitnessIndex 42) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 42)) :=
  congrArg Subgroup.closure (range_7 _ _ _ _ _ _ _).symm

private theorem generator_closure_43 :
    smallParityCensusNode (smallParityCensusWitnessIndex 43) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 43)) :=
  congrArg Subgroup.closure (range_7 _ _ _ _ _ _ _).symm

private theorem generator_closure_44 :
    smallParityCensusNode (smallParityCensusWitnessIndex 44) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 44)) :=
  congrArg Subgroup.closure (range_7 _ _ _ _ _ _ _).symm

private theorem generator_closure_45 :
    smallParityCensusNode (smallParityCensusWitnessIndex 45) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 45)) :=
  congrArg Subgroup.closure (range_7 _ _ _ _ _ _ _).symm

private theorem generator_closure_46 :
    smallParityCensusNode (smallParityCensusWitnessIndex 46) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 46)) :=
  congrArg Subgroup.closure (range_7 _ _ _ _ _ _ _).symm

private theorem generator_closure_47 :
    smallParityCensusNode (smallParityCensusWitnessIndex 47) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 47)) :=
  congrArg Subgroup.closure (range_7 _ _ _ _ _ _ _).symm

private theorem generator_closure_48 :
    smallParityCensusNode (smallParityCensusWitnessIndex 48) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 48)) :=
  congrArg Subgroup.closure (range_7 _ _ _ _ _ _ _).symm

private theorem generator_closure_49 :
    smallParityCensusNode (smallParityCensusWitnessIndex 49) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 49)) :=
  congrArg Subgroup.closure (range_7 _ _ _ _ _ _ _).symm

private theorem generator_closure_50 :
    smallParityCensusNode (smallParityCensusWitnessIndex 50) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 50)) :=
  congrArg Subgroup.closure (range_7 _ _ _ _ _ _ _).symm

private theorem generator_closure_51 :
    smallParityCensusNode (smallParityCensusWitnessIndex 51) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 51)) :=
  congrArg Subgroup.closure (range_7 _ _ _ _ _ _ _).symm

private theorem generator_closure_52 :
    smallParityCensusNode (smallParityCensusWitnessIndex 52) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 52)) :=
  congrArg Subgroup.closure (range_7 _ _ _ _ _ _ _).symm

private theorem generator_closure_53 :
    smallParityCensusNode (smallParityCensusWitnessIndex 53) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 53)) :=
  congrArg Subgroup.closure (range_7 _ _ _ _ _ _ _).symm

private theorem generator_closure_54 :
    smallParityCensusNode (smallParityCensusWitnessIndex 54) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 54)) :=
  congrArg Subgroup.closure (range_7 _ _ _ _ _ _ _).symm

private theorem generator_closure_55 :
    smallParityCensusNode (smallParityCensusWitnessIndex 55) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 55)) :=
  congrArg Subgroup.closure (range_7 _ _ _ _ _ _ _).symm

private theorem generator_closure_56 :
    smallParityCensusNode (smallParityCensusWitnessIndex 56) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 56)) :=
  congrArg Subgroup.closure (range_7 _ _ _ _ _ _ _).symm

private theorem generator_closure_57 :
    smallParityCensusNode (smallParityCensusWitnessIndex 57) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 57)) :=
  congrArg Subgroup.closure (range_7 _ _ _ _ _ _ _).symm

private theorem generator_closure_58 :
    smallParityCensusNode (smallParityCensusWitnessIndex 58) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 58)) :=
  congrArg Subgroup.closure (range_7 _ _ _ _ _ _ _).symm

private theorem generator_closure_59 :
    smallParityCensusNode (smallParityCensusWitnessIndex 59) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 59)) :=
  congrArg Subgroup.closure (range_7 _ _ _ _ _ _ _).symm

private theorem generator_closure_60 :
    smallParityCensusNode (smallParityCensusWitnessIndex 60) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 60)) :=
  congrArg Subgroup.closure (range_7 _ _ _ _ _ _ _).symm

private theorem generator_closure_61 :
    smallParityCensusNode (smallParityCensusWitnessIndex 61) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 61)) :=
  congrArg Subgroup.closure (range_7 _ _ _ _ _ _ _).symm

private theorem generator_closure_62 :
    smallParityCensusNode (smallParityCensusWitnessIndex 62) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 62)) :=
  congrArg Subgroup.closure (range_7 _ _ _ _ _ _ _).symm

private theorem generator_closure_63 :
    smallParityCensusNode (smallParityCensusWitnessIndex 63) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 63)) :=
  congrArg Subgroup.closure (range_7 _ _ _ _ _ _ _).symm

private theorem generator_closure_64 :
    smallParityCensusNode (smallParityCensusWitnessIndex 64) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 64)) :=
  congrArg Subgroup.closure (range_7 _ _ _ _ _ _ _).symm

private theorem generator_closure_65 :
    smallParityCensusNode (smallParityCensusWitnessIndex 65) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 65)) :=
  congrArg Subgroup.closure (range_7 _ _ _ _ _ _ _).symm

private theorem generator_closure_66 :
    smallParityCensusNode (smallParityCensusWitnessIndex 66) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 66)) :=
  congrArg Subgroup.closure (range_7 _ _ _ _ _ _ _).symm

private theorem generator_closure_67 :
    smallParityCensusNode (smallParityCensusWitnessIndex 67) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 67)) :=
  congrArg Subgroup.closure (range_6 _ _ _ _ _ _).symm

private theorem generator_closure_68 :
    smallParityCensusNode (smallParityCensusWitnessIndex 68) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 68)) :=
  congrArg Subgroup.closure (range_6 _ _ _ _ _ _).symm

private theorem generator_closure_69 :
    smallParityCensusNode (smallParityCensusWitnessIndex 69) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 69)) :=
  congrArg Subgroup.closure (range_6 _ _ _ _ _ _).symm

private theorem generator_closure_70 :
    smallParityCensusNode (smallParityCensusWitnessIndex 70) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 70)) :=
  congrArg Subgroup.closure (range_6 _ _ _ _ _ _).symm

private theorem generator_closure_71 :
    smallParityCensusNode (smallParityCensusWitnessIndex 71) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 71)) :=
  congrArg Subgroup.closure (range_6 _ _ _ _ _ _).symm

private theorem generator_closure_72 :
    smallParityCensusNode (smallParityCensusWitnessIndex 72) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 72)) :=
  congrArg Subgroup.closure (range_6 _ _ _ _ _ _).symm

private theorem generator_closure_73 :
    smallParityCensusNode (smallParityCensusWitnessIndex 73) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 73)) :=
  congrArg Subgroup.closure (range_6 _ _ _ _ _ _).symm

private theorem generator_closure_74 :
    smallParityCensusNode (smallParityCensusWitnessIndex 74) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 74)) :=
  congrArg Subgroup.closure (range_6 _ _ _ _ _ _).symm

private theorem generator_closure_75 :
    smallParityCensusNode (smallParityCensusWitnessIndex 75) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 75)) :=
  congrArg Subgroup.closure (range_6 _ _ _ _ _ _).symm

private theorem generator_closure_76 :
    smallParityCensusNode (smallParityCensusWitnessIndex 76) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 76)) :=
  congrArg Subgroup.closure (range_6 _ _ _ _ _ _).symm

private theorem generator_closure_77 :
    smallParityCensusNode (smallParityCensusWitnessIndex 77) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 77)) :=
  congrArg Subgroup.closure (range_6 _ _ _ _ _ _).symm

private theorem generator_closure_78 :
    smallParityCensusNode (smallParityCensusWitnessIndex 78) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 78)) :=
  congrArg Subgroup.closure (range_6 _ _ _ _ _ _).symm

private theorem generator_closure_79 :
    smallParityCensusNode (smallParityCensusWitnessIndex 79) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 79)) :=
  congrArg Subgroup.closure (range_6 _ _ _ _ _ _).symm

private theorem generator_closure_80 :
    smallParityCensusNode (smallParityCensusWitnessIndex 80) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 80)) :=
  congrArg Subgroup.closure (range_6 _ _ _ _ _ _).symm

private theorem generator_closure_81 :
    smallParityCensusNode (smallParityCensusWitnessIndex 81) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 81)) :=
  congrArg Subgroup.closure (range_6 _ _ _ _ _ _).symm

private theorem generator_closure_82 :
    smallParityCensusNode (smallParityCensusWitnessIndex 82) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 82)) :=
  congrArg Subgroup.closure (range_6 _ _ _ _ _ _).symm

private theorem generator_closure_83 :
    smallParityCensusNode (smallParityCensusWitnessIndex 83) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 83)) :=
  congrArg Subgroup.closure (range_6 _ _ _ _ _ _).symm

private theorem generator_closure_84 :
    smallParityCensusNode (smallParityCensusWitnessIndex 84) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 84)) :=
  congrArg Subgroup.closure (range_6 _ _ _ _ _ _).symm

private theorem generator_closure_85 :
    smallParityCensusNode (smallParityCensusWitnessIndex 85) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 85)) :=
  congrArg Subgroup.closure (range_6 _ _ _ _ _ _).symm

private theorem generator_closure_86 :
    smallParityCensusNode (smallParityCensusWitnessIndex 86) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 86)) :=
  congrArg Subgroup.closure (range_5 _ _ _ _ _).symm

private theorem generator_closure_87 :
    smallParityCensusNode (smallParityCensusWitnessIndex 87) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 87)) :=
  congrArg Subgroup.closure (range_5 _ _ _ _ _).symm

private theorem generator_closure_88 :
    smallParityCensusNode (smallParityCensusWitnessIndex 88) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 88)) :=
  congrArg Subgroup.closure (range_5 _ _ _ _ _).symm

private theorem generator_closure_89 :
    smallParityCensusNode (smallParityCensusWitnessIndex 89) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 89)) :=
  congrArg Subgroup.closure (range_5 _ _ _ _ _).symm

private theorem generator_closure_90 :
    smallParityCensusNode (smallParityCensusWitnessIndex 90) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 90)) :=
  congrArg Subgroup.closure (range_5 _ _ _ _ _).symm

private theorem generator_closure_91 :
    smallParityCensusNode (smallParityCensusWitnessIndex 91) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 91)) :=
  congrArg Subgroup.closure (range_5 _ _ _ _ _).symm

private theorem generator_closure_92 :
    smallParityCensusNode (smallParityCensusWitnessIndex 92) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 92)) :=
  congrArg Subgroup.closure (range_5 _ _ _ _ _).symm

private theorem generator_closure_93 :
    smallParityCensusNode (smallParityCensusWitnessIndex 93) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 93)) :=
  congrArg Subgroup.closure (range_5 _ _ _ _ _).symm

private theorem generator_closure_94 :
    smallParityCensusNode (smallParityCensusWitnessIndex 94) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 94)) :=
  congrArg Subgroup.closure (range_5 _ _ _ _ _).symm

private theorem generator_closure_95 :
    smallParityCensusNode (smallParityCensusWitnessIndex 95) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 95)) :=
  congrArg Subgroup.closure (range_4 _ _ _ _).symm

set_option maxRecDepth 2048 in
private theorem generator_closure_96 :
    smallParityCensusNode (smallParityCensusWitnessIndex 96) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator 96)) :=
  congrArg Subgroup.closure (range_4 _ _ _ _).symm

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- The certificate generators recover the exact existing census node. -/
public theorem smallParityCensusWitnessGenerator_closure (i : Fin 97) :
    smallParityCensusNode (smallParityCensusWitnessIndex i) =
      Subgroup.closure (Set.range (smallParityCensusWitnessGenerator i)) := by
  fin_cases i
  · exact generator_closure_0
  · exact generator_closure_1
  · exact generator_closure_2
  · exact generator_closure_3
  · exact generator_closure_4
  · exact generator_closure_5
  · exact generator_closure_6
  · exact generator_closure_7
  · exact generator_closure_8
  · exact generator_closure_9
  · exact generator_closure_10
  · exact generator_closure_11
  · exact generator_closure_12
  · exact generator_closure_13
  · exact generator_closure_14
  · exact generator_closure_15
  · exact generator_closure_16
  · exact generator_closure_17
  · exact generator_closure_18
  · exact generator_closure_19
  · exact generator_closure_20
  · exact generator_closure_21
  · exact generator_closure_22
  · exact generator_closure_23
  · exact generator_closure_24
  · exact generator_closure_25
  · exact generator_closure_26
  · exact generator_closure_27
  · exact generator_closure_28
  · exact generator_closure_29
  · exact generator_closure_30
  · exact generator_closure_31
  · exact generator_closure_32
  · exact generator_closure_33
  · exact generator_closure_34
  · exact generator_closure_35
  · exact generator_closure_36
  · exact generator_closure_37
  · exact generator_closure_38
  · exact generator_closure_39
  · exact generator_closure_40
  · exact generator_closure_41
  · exact generator_closure_42
  · exact generator_closure_43
  · exact generator_closure_44
  · exact generator_closure_45
  · exact generator_closure_46
  · exact generator_closure_47
  · exact generator_closure_48
  · exact generator_closure_49
  · exact generator_closure_50
  · exact generator_closure_51
  · exact generator_closure_52
  · exact generator_closure_53
  · exact generator_closure_54
  · exact generator_closure_55
  · exact generator_closure_56
  · exact generator_closure_57
  · exact generator_closure_58
  · exact generator_closure_59
  · exact generator_closure_60
  · exact generator_closure_61
  · exact generator_closure_62
  · exact generator_closure_63
  · exact generator_closure_64
  · exact generator_closure_65
  · exact generator_closure_66
  · exact generator_closure_67
  · exact generator_closure_68
  · exact generator_closure_69
  · exact generator_closure_70
  · exact generator_closure_71
  · exact generator_closure_72
  · exact generator_closure_73
  · exact generator_closure_74
  · exact generator_closure_75
  · exact generator_closure_76
  · exact generator_closure_77
  · exact generator_closure_78
  · exact generator_closure_79
  · exact generator_closure_80
  · exact generator_closure_81
  · exact generator_closure_82
  · exact generator_closure_83
  · exact generator_closure_84
  · exact generator_closure_85
  · exact generator_closure_86
  · exact generator_closure_87
  · exact generator_closure_88
  · exact generator_closure_89
  · exact generator_closure_90
  · exact generator_closure_91
  · exact generator_closure_92
  · exact generator_closure_93
  · exact generator_closure_94
  · exact generator_closure_95
  · exact generator_closure_96

private def displacementWords (i : Fin 97) (j : Fin 9) : List (List (Fin 9)) :=
  ((#[
    ![[[0, 2], [0, 2, 1, 3]], [], [], [[2, 3]], [], [[2, 4]], [], [], []],
    ![[[1, 3]], [[3]], [[2, 5]], [], [], [[3]], [], [], []],
    ![[[0, 5, 0]], [], [[2, 5]], [], [], [[3]], [], [], []],
    ![[[0, 2], [3, 0, 2]], [], [[0], [0, 2]], [[0, 2], [0, 2, 3, 4]], [], [[1, 3]], [[1, 5]], [], []],
    ![[[0, 2, 3]], [[1], [0, 2, 1, 6]], [[2, 4]], [[0, 2, 3]], [[0, 5]], [[2, 4]], [], [], []],
    ![[[2]], [[1], [0, 1]], [[0, 2, 4]], [], [[0]], [[0, 2, 4]], [], [], []],
    ![[[2, 5]], [[1], [0, 1, 6]], [], [[2]], [[0, 4]], [[0, 2, 4]], [], [], []],
    ![[[0, 1], [3, 1]], [[0, 1], [2, 1, 6]], [[1], [2, 1, 5]], [], [], [[2, 4]], [[0]], [], []],
    ![[[0], [1, 4, 5]], [[0], [1, 7]], [[0], [3, 0, 2]], [[0, 1, 2, 4]], [[0, 1, 2, 4]], [[4]], [], [], []],
    ![[[0], [0, 2, 1]], [[1, 3]], [[0, 1, 0]], [[0, 1], [0, 1, 3]], [], [], [], [], []],
    ![[[0, 1], [4, 0]], [[1, 4]], [], [], [[1], [1, 4]], [], [], [], []],
    ![[], [[1, 4]], [], [[2, 4]], [], [], [], [], []],
    ![[[0], [0, 1, 4]], [[1, 4]], [], [], [[0], [0, 3, 5]], [], [], [], []],
    ![[[1, 3]], [[3]], [], [], [[3]], [], [], [], []],
    ![[[0, 4, 0]], [], [], [], [[3]], [], [], [], []],
    ![[[0], [0, 1, 5]], [[0], [0, 1]], [[1, 2]], [[1, 3]], [[1, 2]], [[2, 4]], [], [], []],
    ![[[0, 4], [1, 4, 0]], [[0, 4], [0, 1, 4]], [], [[2, 4]], [[1, 2]], [[2, 4]], [], [], []],
    ![[[1, 3, 4]], [[0], [0, 1, 5]], [[2, 4]], [], [[1, 3, 4]], [[2, 4]], [], [], []],
    ![[[0], [0, 1]], [[1, 4]], [], [], [[0], [0, 3]], [], [], [], []],
    ![[[0, 1], [0, 4, 1]], [[1], [0, 1]], [], [[0]], [[0, 2, 4]], [], [], [], []],
    ![[[1], [1, 2, 3]], [[1], [0, 1, 5]], [], [[0]], [[0, 1, 1]], [], [], [], []],
    ![[[0, 2, 3]], [[1], [0, 1, 5]], [[0, 2]], [[0, 3]], [[0], [0, 3]], [], [], [], []],
    ![[[0, 2, 3]], [[1], [0, 1]], [[0, 2]], [[0, 3]], [[0], [0, 3]], [], [], [], []],
    ![[[0, 2, 4]], [[2]], [[0, 2, 4]], [[0]], [], [], [], [], []],
    ![[[0, 3]], [[2]], [[0, 3]], [[0], [0, 3]], [], [], [], [], []],
    ![[[0, 3]], [[1], [0, 1, 5]], [[0, 2]], [[0, 3]], [], [], [], [], []],
    ![[[0, 1], [1, 2]], [[0, 1], [1, 3]], [], [[0]], [[0, 2, 3]], [[0]], [], [], []],
    ![[], [[2, 4]], [], [[0]], [], [], [], [], []],
    ![[[3]], [[2, 4]], [], [[3]], [], [], [], [], []],
    ![[[0, 2]], [[0, 2]], [[0, 3, 4]], [], [], [], [], [], []],
    ![[[3, 4]], [[3, 4]], [[2]], [], [], [], [], [], []],
    ![[[3, 4]], [[3, 4]], [[0]], [], [], [], [], [], []],
    ![[[0, 2]], [[0, 2]], [[0]], [], [], [], [], [], []],
    ![[[0, 2, 3]], [[1], [0, 2, 1]], [[0, 4]], [[0, 2, 3]], [[0, 2]], [], [], [], []],
    ![[[3, 4]], [[3, 4]], [[0]], [], [], [], [], [], []],
    ![[[2]], [[0, 1], [2, 1]], [[0, 3]], [[0], [2, 4]], [[3, 4]], [], [], [], []],
    ![[[0, 2]], [[0, 2]], [[0]], [], [], [], [], [], []],
    ![[[0], [1, 6]], [[0], [1, 6]], [[0], [1, 1, 0]], [], [[4]], [], [], [], []],
    ![[], [[2, 3]], [], [], [], [], [], [], []],
    ![[[2, 3]], [[1]], [], [], [], [], [], [], []],
    ![[[0], [0, 1, 5]], [[0, 0]], [], [], [], [], [], [], []],
    ![[[0], [0, 1]], [[1]], [[0], [0, 4]], [], [], [], [], [], []],
    ![[[0], [1], [0, 1, 2]], [[1, 2], [2, 3]], [[0], [3, 0]], [[2, 3]], [], [], [], [], []],
    ![[[1, 3]], [], [[2]], [], [], [], [], [], []],
    ![[[1, 3]], [[3]], [[3]], [], [], [], [], [], []],
    ![[[0, 2, 0]], [], [[3]], [], [], [], [], [], []],
    ![[[0], [0, 3]], [], [[2, 3]], [[0], [0, 3]], [], [[2, 3]], [], [], []],
    ![[], [[1, 2]], [], [[2, 3]], [], [], [], [], []],
    ![[[0, 0]], [[0], [0, 1]], [[0], [2, 0]], [[0], [2, 0]], [], [[0, 0]], [], [], []],
    ![[[0], [1], [0, 1, 2]], [[0], [0, 1]], [[0], [0, 3]], [[0], [0, 3]], [[0], [0, 3]], [], [], [], []],
    ![[], [[1]], [], [[2, 3]], [], [], [], [], []],
    ![[[1, 3]], [], [[2]], [], [], [], [], [], []],
    ![[[0, 2]], [[1], [0, 1]], [[0, 2]], [[0]], [], [], [], [], []],
    ![[[0, 2, 3]], [[1], [0, 1]], [[0, 2, 3]], [[0]], [], [], [], [], []],
    ![[], [[0], [1], [1, 0]], [[0], [0, 3]], [], [], [], [], [], []],
    ![[[2, 3]], [[2, 3]], [], [], [], [], [], [], []],
    ![[[2, 3]], [[2, 3]], [], [], [], [], [], [], []],
    ![[[2, 3]], [[2, 3]], [], [], [], [], [], [], []],
    ![[[2, 3]], [[2, 3]], [], [], [], [], [], [], []],
    ![[[0]], [[1], [0, 1]], [[0, 2]], [], [], [], [], [], []],
    ![[[1], [0, 1]], [[1], [1, 0]], [[0, 2]], [[0, 2, 3]], [], [[0]], [], [], []],
    ![[], [[1], [0, 1, 3]], [[2]], [], [], [], [], [], []],
    ![[[3]], [[0]], [], [], [], [], [], [], []],
    ![[], [[0], [1], [1, 2]], [[3]], [[3]], [], [], [], [], []],
    ![[[3]], [[0, 3]], [], [], [], [], [], [], []],
    ![[], [[1], [0, 1, 2]], [[3]], [[3]], [], [], [], [], []],
    ![[[0], [1, 4]], [[0], [1]], [[0, 1, 2]], [], [], [], [], [], []],
    ![[], [[0], [0, 4]], [], [], [], [], [], [], []],
    ![[[0], [0, 1, 2]], [[2]], [], [], [], [], [], [], []],
    ![[[1, 2]], [[3]], [], [], [], [], [], [], []],
    ![[[0], [2, 0]], [], [], [], [], [], [], [], []],
    ![[[0], [0, 1]], [], [], [], [[0], [0, 1]], [], [], [], []],
    ![[[2]], [[0], [0, 1]], [], [], [[2]], [], [], [], []],
    ![[], [[0]], [], [], [], [], [], [], []],
    ![[], [[0], [0, 2]], [], [], [], [], [], [], []],
    ![[], [[2]], [], [], [], [], [], [], []],
    ![[[0], [0, 2]], [[0], [0, 2]], [], [], [], [], [], [], []],
    ![[[1], [1, 2]], [[1], [1, 2]], [], [], [], [], [], [], []],
    ![[], [[0], [0, 2]], [], [], [], [], [], [], []],
    ![[[1], [1, 2]], [[1], [1, 2]], [], [], [], [], [], [], []],
    ![[[3]], [[0]], [], [], [], [], [], [], []],
    ![[[3]], [[0]], [], [], [], [], [], [], []],
    ![[], [[3]], [], [], [], [], [], [], []],
    ![[[3]], [[0, 3]], [], [], [], [], [], [], []],
    ![[[1, 0, 2]], [[1, 0, 2]], [[4]], [], [], [], [], [], []],
    ![[[1, 0, 2]], [[1, 0, 2]], [[4]], [], [], [], [], [], []],
    ![[[0], [0, 1]], [], [], [], [], [], [], [], []],
    ![[[2]], [], [], [], [], [], [], [], []],
    ![[[1, 3]], [[3]], [], [], [], [], [], [], []],
    ![[[1, 3]], [[3]], [], [], [], [], [], [], []],
    ![[[2]], [], [], [], [], [], [], [], []],
    ![[[0], [0, 1]], [], [], [], [], [], [], [], []],
    ![[[2]], [[0]], [], [], [], [], [], [], []],
    ![[[2]], [[0]], [], [], [], [], [], [], []],
    ![[[2]], [[0, 2]], [], [], [], [], [], [], []],
    ![[[2]], [], [], [], [], [], [], [], []],
    ![[[2]], [], [], [], [], [], [], [], []]] : Array (Fin 9 → List (List (Fin 9)))).getD i.val (fun _ => [])) j

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem displacementWords_valid : ∀ (i : Fin 97) (j : Fin 9),
    (smallParityCensusWitnessGenerator i j)⁻¹ *
      (smallParityCensusWitness i * smallParityCensusWitnessGenerator i j *
        (smallParityCensusWitness i)⁻¹) =
      ((displacementWords i j).map
        (fun w => evalWord (smallParityCensusWitnessGenerator i) w ^ 2)).prod := by
  decide +kernel

/-- Checked square words certify all Frattini actions; only nonmembership remains. -/
public theorem smallParityCensusWitness_of_not_mem (i : Fin 97)
    (hout : smallParityCensusWitness i ∉ smallParityCensusNode (smallParityCensusWitnessIndex i)) :
    (smallParityCensusNode (smallParityCensusWitnessIndex i)).HasFrattiniNormalizerWitness := by
  apply Subgroup.hasFrattiniNormalizerWitness_of_square_word_displacements
    (smallParityCensusNode (smallParityCensusWitnessIndex i))
    ((IsPGroup.of_card (n := 12) card).to_subgroup _)
    (smallParityCensusWitnessGenerator i) (smallParityCensusWitnessGenerator_closure i)
    (smallParityCensusWitness i) hout (displacementWords i)
  exact displacementWords_valid i

end ReeTwo.SylowModel
