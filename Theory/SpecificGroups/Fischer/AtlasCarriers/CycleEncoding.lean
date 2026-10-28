module

public import Mathlib.GroupTheory.Perm.List
public import Mathlib.GroupTheory.Perm.Finite
public import Mathlib.Algebra.Group.Subgroup.Lattice

/-!
# Decimal cycle tables for the Fischer permutation carriers

The numerical tables are stored in blocks of semicolon-separated cycles,
with comma-separated zero-based decimal letters within each cycle. This keeps
large ATLAS tables as data rather than elaborating hundreds of thousands of
individual `Fin` literals. `source/encode.py` checks the syntax, bounds,
disjointness, and exact round trip to the retained ATLAS GAP files.

The decoder reads decimal digits by the usual recurrence `v ↦ 10*v + digit`.
On the checked source data every character between separators is a decimal
digit and every letter is below the degree, so modular reduction changes no
entry. Permutations are constructed as products
of `List.formPerm` cycles, whose group laws are proved in Mathlib. Inverting
this product converts the source right action to a left action.

Source: R. A. Wilson et al., ATLAS of Finite Group Representations;
the three exact representation identifiers and download hashes are retained
in `source/README.md` and `source/manifest.json`.
-/

@[expose] public section

namespace Sporadic.Fischer.AtlasCarriers

/-- Decode semicolon-separated cycles of comma-separated decimal letters. -/
def decodeCycleBlocks (n : ℕ) [NeZero n] (blocks : List String) : List (List (Fin n)) :=
  blocks.flatMap fun block =>
    (block.toList.splitOn ';').map fun cycle =>
      (cycle.splitOn ',').map fun entry =>
        Fin.ofNat n (entry.foldl (fun value c => 10 * value + (c.toNat - '0'.toNat)) 0)

/-- Turn a published right-action cycle table into a left-action permutation. -/
def permutationFromCycleBlocks (n : ℕ) [NeZero n] (blocks : List String) :
    Equiv.Perm (Fin n) :=
  ((decodeCycleBlocks n blocks).map List.formPerm).prod⁻¹

end Sporadic.Fischer.AtlasCarriers
