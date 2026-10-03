module

public import Theory.SpecificGroups.ReeTwo.Characters
public import Theory.GroupTheory.NormalizerPCoreWitness

/-!
# Representatives for the small even Ree two candidate calculation

These 59 subgroups are specified by root generators. The diagnostic labels
are retained only to identify the corresponding source words. No census,
order, centricity or automorphism property is asserted by these definitions.
Those are separate proof obligations.

The words use the verified convention of Shinoda (1975), (2.3), pp. 81–82:
the twelve successive generators are `rootOne`, `rootOne ^ 2`, and `root i`
for i = 0,...,9. The core character is the sum of the coordinates for
`root 1`, `root 2`, and `root 3`.
-/

namespace ReeTwo.SylowModel

/-- Labels of the fixed root-word representatives. -/
@[expose] public def smallEvenCandidateLabel (i : Fin 59) : ℕ :=
  ![28, 32, 36, 37, 46, 47, 55, 85, 87, 107, 125, 127, 132, 140, 147, 148, 149, 150, 163, 164, 165, 166, 170, 171, 213, 222, 224, 234, 253, 266, 269, 310, 311, 312, 342, 349, 384, 394, 396, 414, 415, 416, 419, 491, 588, 675, 792, 803, 805, 810, 816, 820, 831, 849, 855, 856, 869, 871, 873] i

/-- The proposed representatives that require small even core-character
exclusion. Exhaustiveness is not part of this definition. -/
@[expose] public def smallEvenCandidate (i : Fin 59) : Subgroup SylowModel :=
  Subgroup.closure
    (![({rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel),
      {rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3 * root 4 * root 7 * root 8, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9},
      {root 0, rootOne ^ 2 * root 0 * root 3, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9},
      {root 3, rootOne ^ 2, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9},
      {root 0 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9},
      {root 3, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9},
      {root 3, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8, root 4 * root 7 * root 8 * root 9, root 6 * root 8, root 7 * root 8 * root 9, root 8, root 9},
      {root 0, rootOne ^ 2 * root 0 * root 3, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9},
      {root 0, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9},
      {root 0, root 0 * root 2 * root 5 * root 6 * root 9, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9},
      {root 0, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 4 * root 7 * root 8, root 5 * root 6 * root 7, root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9},
      {root 0, root 0 * root 3 * root 5 * root 6 * root 7, root 4 * root 7 * root 8, root 5 * root 6 * root 7, root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9},
      {root 3, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 5 * root 8, root 6 * root 8, root 7, root 8, root 9},
      {root 3, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 4 * root 5 * root 8 * root 9, root 6 * root 8, root 7, root 8 * root 9, root 9},
      {root 0, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 2 * root 3 * root 4 * root 7, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 8, root 9},
      {root 0, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 4 * root 7 * root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 8, root 9},
      {root 0, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 2 * root 3 * root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 8, root 9},
      {root 0, root 0 * root 1 * root 4 * root 6, root 4 * root 7 * root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 8, root 9},
      {root 0, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9},
      {root 0, root 0 * root 3 * root 5 * root 6 * root 9, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9},
      {root 0, root 0 * root 3 * root 5 * root 6 * root 9, root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9},
      {root 0 * root 2 * root 3 * root 4 * root 7, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9},
      {root 0, root 0 * root 2 * root 5 * root 6 * root 9, root 1 * root 3 * root 4 * root 5 * root 6 * root 8, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9},
      {root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9},
      {rootOne ^ 2 * root 0 * root 3, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9},
      {rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 0 * root 2 * root 4 * root 5 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9},
      {root 0 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9},
      {root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9},
      {root 0, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 7, root 8 * root 9, root 7 * root 9, root 9},
      {root 3, root 4 * root 7 * root 8, root 5 * root 6 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9},
      {root 2 * root 4 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 5 * root 6 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9},
      {root 0, root 0 * root 2 * root 5 * root 6 * root 9, root 6 * root 7 * root 8 * root 9, root 5, root 7, root 8, root 9},
      {root 0, root 0 * root 3 * root 4 * root 5 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 5, root 7, root 8, root 9},
      {root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 4 * root 7 * root 8, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7 * root 8, root 7 * root 9, root 8, root 9},
      {root 3, rootOne ^ 2, root 4 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9},
      {root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9},
      {root 3, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8, root 6 * root 8, root 7, root 8, root 9},
      {root 3, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 4 * root 5 * root 8 * root 9, root 6 * root 8, root 7, root 8 * root 9, root 9},
      {root 2 * root 4 * root 8, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 4 * root 5 * root 8 * root 9, root 6 * root 8, root 7, root 8 * root 9, root 9},
      {root 0, root 0 * root 1 * root 4 * root 6, root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 9},
      {root 0 * root 2 * root 3 * root 4 * root 7, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 9},
      {root 0 * root 2 * root 3 * root 4 * root 7, root 0 * root 1 * root 4 * root 6, root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 9},
      {root 0 * root 4 * root 7 * root 8, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 9},
      {rootOne ^ 2 * root 0 * root 3, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 8, root 9, root 7 * root 9},
      {root 2 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 5 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9},
      {root 3, rootOne ^ 2, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9},
      {rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 8, root 9, root 7 * root 9},
      {root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 2 * root 3 * root 4 * root 8, root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 9},
      {root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 9, root 8, root 7 * root 9},
      {root 3, root 5 * root 7 * root 8, root 7 * root 9, root 8, root 9},
      {rootOne ^ 2 * root 2 * root 4 * root 5 * root 7 * root 9, root 8 * root 9, root 2 * root 3 * root 4 * root 7 * root 8, root 7 * root 9, root 9},
      {root 0 * root 2 * root 3 * root 4 * root 5 * root 8 * root 9, rootOne ^ 2 * root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 2 * root 3 * root 4 * root 8 * root 9, root 9, root 7 * root 9},
      {root 0 * root 3 * root 5 * root 6 * root 7, root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 9},
      {root 2 * root 5 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9},
      {root 1 * root 5 * root 6 * root 7 * root 8 * root 9, root 8, root 6 * root 8, root 5 * root 9, root 9},
      {root 3, root 1 * root 3 * root 5 * root 7 * root 8 * root 9, root 5 * root 8, root 8, root 9},
      {root 0 * root 2 * root 3 * root 4 * root 7, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 6 * root 8, root 5 * root 7 * root 8 * root 9, root 9},
      {root 0 * root 2 * root 3 * root 4 * root 7, root 0 * root 1 * root 2 * root 3 * root 6 * root 7 * root 8 * root 9, root 6 * root 8, root 5 * root 7 * root 8 * root 9, root 9},
      {root 0 * root 4 * root 8 * root 9, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 5 * root 7 * root 8 * root 9, root 6 * root 7 * root 9, root 9}] i)

/-- The exceptional representative with diagnostic label 37. -/
@[expose] public def smallEvenExceptional : Subgroup SylowModel :=
  smallEvenCandidate 3

/-- The remaining coverage obligation. A subgroup that survives the
Frattini-action obstruction, is centric and small, lies in the parity kernel,
and is not contained in the core-character kernel, is conjugate to a listed
representative. This definition does not assert coverage. -/
@[expose] public def SmallEvenFrattiniCensus : Prop :=
  ∀ U : Subgroup SylowModel,
    Subgroup.centralizer (U : Set SylowModel) ≤ U →
    Nat.card U < 1024 → U ≤ character.ker → ¬ U ≤ coreCharacter.ker →
    (∀ g : Subgroup.normalizer (U : Set SylowModel),
      Subgroup.quotientAut (frattini U) (U.normalizerMonoidHom g) = 1 →
      (g : SylowModel) ∈ U) →
    ∃ (i : Fin 59) (g : SylowModel),
      U = (smallEvenCandidate i).map (MulAut.conj g).toMonoidHom

end ReeTwo.SylowModel
