module

public import Theory.Representation.BinaryNaturalDual.FourActors.Model
public import Theory.Representation.BinaryNaturalDual.FourActors.PermutationCatalogue.Representatives
public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.TreeSylow
/-!
# Binary-tree checks for elementary subgroups of order sixteen

The binary-tree Sylow subgroup is `D₈ wr C₂`, in its existing 128 permutation
normal forms. A square-one element interchanging the two four-point blocks has
only twelve square-one elements in its centralizer. Inside the block-preserving
base, commutation with an element interchanging the two pairs of a block forces
the lower pair swaps to agree. These two local choices put an elementary
subgroup in one of the four products of Klein groups. Interchanging the two
four-point blocks identifies the two mixed choices.

The checks range only over the existing 128 normal forms and sixteen words in
each representative, never over all subgroups or all permutations of eight
points. The parent module supplies the subgroup, cardinality and Sylow arguments.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.3(3),
printed pp.391–392, PDF pp.402–403.
-/

@[expose] public section

open Equiv Subgroup
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
open BinaryNaturalDual.FourActors BinaryNaturalDual.FourActors.PermutationCatalogue

namespace BinaryNaturalDual.FourActors.PermutationCatalogue.Exhaustion

def involutionCentralizer (i : Fin 128) : Finset (Fin 128) :=
  Finset.univ.filter (fun j => treeWord j ^ 2 = 1 ∧
    treeWord i * treeWord j = treeWord j * treeWord i)

theorem outer_centralizer_bound : ∀ i : Fin 128, 64 ≤ i.val → treeWord i ^ 2 = 1 →
    (involutionCentralizer i).card ≤ 12 := by
  decide +kernel

def compatible (l r : Bool) (i : Fin 128) : Prop :=
  (if l then i.val % 2 = i.val / 2 % 2 else i.val / 16 % 2 = 0) ∧
  (if r then i.val / 4 % 2 = i.val / 8 % 2 else i.val / 32 % 2 = 0)
instance (l r : Bool) (i : Fin 128) : Decidable (compatible l r i) :=
  inferInstanceAs (Decidable (_ ∧ _))

def classIndex (l r : Bool) : Fin 3 :=
  if l then if r then 0 else 2 else if r then 2 else 1

def blockConjugator (l r : Bool) : S :=
  if l && !r then treeGenerator 6 else 1

theorem left_control : ∀ i j : Fin 128, i.val < 64 → j.val < 64 →
    treeWord i ^ 2 = 1 → i.val / 16 % 2 = 1 →
    treeWord i * treeWord j = treeWord j * treeWord i →
    j.val % 2 = j.val / 2 % 2 := by
  decide +kernel

theorem right_control : ∀ i j : Fin 128, i.val < 64 → j.val < 64 →
    treeWord i ^ 2 = 1 → i.val / 32 % 2 = 1 →
    treeWord i * treeWord j = treeWord j * treeWord i →
    j.val / 4 % 2 = j.val / 8 % 2 := by
  decide +kernel

theorem compatible_conjugate : ∀ (l r : Bool) (i : Fin 128),
    i.val < 64 → compatible l r i →
    ∃ v : Binary, word (classIndex l r) v =
      (MulAut.conj (blockConjugator l r)) (treeWord i) := by
  decide +kernel

end BinaryNaturalDual.FourActors.PermutationCatalogue.Exhaustion
