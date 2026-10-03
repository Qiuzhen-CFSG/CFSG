module

public import Theory.SpecificGroups.ReeTwo.Sylow

/-!
# Small Ree two subgroups outside the parity kernel

These nineteen subgroups are specified by root generators for use in a
centric subgroup census. Fourteen are proposed for exclusion by their full
automorphism groups; the other five are proposed for a characteristic
Frattini-action witness. These definitions assert neither coverage nor any
automorphism property. Both are separate proof obligations.

Source: the verified Shinoda (1975), (2.3), pp. 81–82, root model. The
exploratory labels are retained to match the saved census. Its twelve-letter
words use `rootOne`, `rootOne ^ 2`, then `root 0` through `root 9`.
-/

namespace ReeTwo.SylowModel

/-- Representatives with diagnostic labels 68, 70, 71, 73, 76, 194, 199, 209, 457, 458, 459, 460, 471, 478. -/
@[expose] public def smallParityTwoCandidate (i : Fin 14) : Subgroup SylowModel :=
  Subgroup.closure
    (![({root 3, rootOne ^ 3, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel),
      ({root 3, rootOne ^ 3 * root 5 * root 8, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel),
      ({root 2 * root 4 * root 8, rootOne ^ 3, root 5 * root 8, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel),
      ({root 2 * root 4 * root 8, rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel),
      ({rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 4 * root 6 * root 7, root 4 * root 5 * root 7 * root 9, root 6 * root 7, root 7 * root 9, root 8, root 9} : Set SylowModel),
      ({root 2 * root 4 * root 8, rootOne ^ 3, root 6 * root 7 * root 8, rootOne ^ 2, root 4, root 7, root 9, root 8} : Set SylowModel),
      ({root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, root 6 * root 7 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7, root 9, root 8} : Set SylowModel),
      ({rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 6, root 4 * root 5 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel),
      ({root 3, rootOne ^ 3, rootOne ^ 2, root 4, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel),
      ({root 3 * root 6 * root 7 * root 8, rootOne ^ 3, rootOne ^ 2, root 4, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel),
      ({root 3, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel),
      ({root 3 * root 6 * root 7 * root 8, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel),
      ({root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7, root 9, root 8} : Set SylowModel),
      ({rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 4 * root 5 * root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel)] i)

/-- Representatives with diagnostic labels 463, 882, 887, 890, 891. -/
@[expose] public def smallParityOddCandidate (i : Fin 5) : Subgroup SylowModel :=
  Subgroup.closure
    (![({root 2 * root 4 * root 8, rootOne ^ 3, rootOne ^ 2, root 4, root 7, root 9, root 8} : Set SylowModel),
      ({rootOne ^ 3, root 4 * root 8, root 9, rootOne ^ 2, root 8} : Set SylowModel),
      ({rootOne ^ 3 * root 3 * root 4, root 4 * root 8, root 9, rootOne ^ 2 * root 4 * root 8, root 8} : Set SylowModel),
      ({root 2 * root 4 * root 8, rootOne ^ 3, rootOne ^ 2, root 8 * root 9, root 8} : Set SylowModel),
      ({root 2 * root 8, rootOne ^ 3, rootOne ^ 2, root 8 * root 9, root 8} : Set SylowModel)] i)

/-- The combined family, with the fourteen two-group candidates first. -/
@[expose] public def smallParityCandidate (i : Fin 19) : Subgroup SylowModel :=
  Fin.addCases (m := 14) (n := 5) smallParityTwoCandidate smallParityOddCandidate i

end ReeTwo.SylowModel
