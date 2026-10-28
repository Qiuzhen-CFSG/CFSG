module
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarOrder.Core
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarData

/-!
# Literal Figure 1/2 permutations

The coordinates of the printed MOG are numbered row by row, from zero.
`mogToStar` converts these coordinates to the certified native 24-star action.
The six involutions are, in order, the common first generator of Figure 2,
the second and third generators of (b), the second and third generators of
(d), and the permutation part of the second generator of Figure 1(b)/(c).
The signs in Figure 1(c) are cocode entries and are not permutation entries.

The word witnesses express these exact permutations in the native star
quotient. GAP discovers the words; Lean checks the permutation equations.
Source: Kleidman--Wilson, *The Maximal Subgroups of J4* (1988), Figures 1
and 2, printed pp.486 and 490. Native star coordinates and ATLAS attribution
are inherited from `Image.StarData`.
-/

set_option maxRecDepth 10000
@[expose] public section
namespace Janko4.LocalStructure.ElementaryEightGeometry
open Cardinality.QuotientCount.Image Theory.GroupTheory

def mogToStar : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 5, 12, 11, 19, 20, 14, 8, 13, 21, 18, 10, 7, 16, 6, 23, 9, 22, 15, 17]
  invFun := ![0, 1, 2, 3, 4, 5, 18, 16, 11, 20, 15, 7, 6, 12, 10, 22, 17, 23, 14, 8, 9, 13, 21, 19]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def mogPermutationTable : Fin 6 → Fin 24 → Fin 24 :=
  ![![0, 1, 3, 2, 5, 4, 6, 7, 9, 8, 11, 10, 12, 13, 15, 14, 17, 16, 18, 19, 21, 20, 23, 22], ![0, 1, 2, 3, 11, 10, 6, 7, 8, 9, 5, 4, 13, 12, 15, 14, 22, 23, 19, 18, 21, 20, 16, 17], ![0, 1, 2, 3, 17, 16, 7, 6, 9, 8, 22, 23, 12, 13, 14, 15, 5, 4, 19, 18, 21, 20, 10, 11], ![0, 1, 9, 8, 4, 5, 6, 7, 3, 2, 10, 11, 13, 12, 20, 21, 17, 16, 19, 18, 14, 15, 23, 22], ![0, 1, 15, 14, 4, 5, 7, 6, 20, 21, 11, 10, 12, 13, 3, 2, 16, 17, 19, 18, 8, 9, 23, 22], ![1, 0, 3, 2, 4, 5, 7, 6, 9, 8, 10, 11, 13, 12, 15, 14, 16, 17, 19, 18, 21, 20, 22, 23]]

def mogPermutation (i : Fin 6) : Equiv.Perm (Fin 24) where
  toFun := mogPermutationTable i
  invFun := mogPermutationTable i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

def permutationTable : Fin 6 → Fin 24 → Fin 24 :=
  ![![0, 1, 3, 2, 5, 4, 6, 16, 14, 22, 18, 11, 12, 13, 8, 17, 7, 15, 10, 20, 19, 21, 9, 23], ![0, 1, 2, 3, 8, 14, 23, 15, 4, 22, 18, 11, 12, 21, 5, 7, 17, 16, 10, 19, 20, 13, 9, 6], ![0, 1, 2, 3, 16, 7, 23, 5, 17, 22, 10, 12, 11, 13, 15, 14, 4, 8, 18, 20, 19, 21, 9, 6], ![0, 1, 20, 19, 4, 5, 23, 16, 8, 18, 22, 11, 12, 21, 14, 17, 7, 15, 9, 3, 2, 13, 10, 6], ![0, 1, 10, 18, 4, 5, 23, 7, 14, 19, 2, 12, 11, 13, 8, 17, 16, 15, 3, 9, 22, 21, 20, 6], ![1, 0, 3, 2, 4, 5, 23, 7, 8, 22, 18, 12, 11, 21, 14, 15, 16, 17, 10, 20, 19, 13, 9, 6]]

def permutation (i : Fin 6) : Equiv.Perm (Fin 24) where
  toFun := permutationTable i
  invFun := permutationTable i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

theorem mogToStar_permutation (i : Fin 6) :
    (MulAut.conj mogToStar) (mogPermutation i) = permutation i := by
  revert i
  decide +kernel

def alphabet : Fin 4 → Equiv.Perm (Fin 24) := ![starX, starY, starX⁻¹, starY⁻¹]

def word : Fin 6 → List (Fin 4) :=
  ![[2, 1, 2, 3, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 2, 1, 2, 3, 2, 1, 2, 3, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1], [2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 2, 1, 2, 3, 2, 1, 2, 3, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1], [2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 2, 1, 2, 3, 2, 1, 2, 3, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1], [2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 1, 0, 3, 0, 3, 0, 3, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 1, 0, 3, 0, 1, 0, 3, 0, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1], [1, 2, 3, 2, 1, 2, 3, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 1, 0, 3, 0, 3, 0, 3, 0, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 2, 1, 2, 3, 2, 1, 2, 3, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1], [2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 2, 1, 2, 1, 2, 1, 2, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 2, 1, 2, 3, 2, 1, 2, 3, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1]]

end Janko4.LocalStructure.ElementaryEightGeometry
