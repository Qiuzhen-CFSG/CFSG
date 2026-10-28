module

public import Theory.GroupTheory.CosetWordCertificate.RelatorScan

/-!
# Exact four-generator local-amalgam relators

Generators0,1 are shared endpoint generators, generator2 is ell, generator3 is n.
The first13 words are the linear-side relations; the next13 are the hexad-side
relations with their third letter replaced by generator3. The final word is
(ell^-1*n^-1*ell*n)^2, the square of the GAP commutator. The source group must
supply these literal relations with simultaneous generator markings.
-/

@[expose] public section
namespace Theory.SpecificGroups.MathieuAmalgamCompletion
open Subgroup.CosetWordCertificate

/-- Signed finite-generator decoding, positive letters having even code. -/
def decode (a : Nat) : Letter (Fin 4) :=
  (⟨(a / 2) % 4, Nat.mod_lt _ (by decide)⟩, a % 2 == 0)

/-- The exact thirteen linear, thirteen hexad, and one mixed relation. -/
def relator : Fin 27 → Word (Fin 4) := fun i =>
  (match i.val with
  | 0 => [4, 4, 4]
  | 1 => [0, 0, 0]
  | 2 => [2, 2, 2, 2]
  | 3 => [1, 3, 1, 3, 1, 3, 1, 3, 1, 3]
  | 4 => [4, 1, 4, 0, 3, 5, 2, 1, 2, 0, 3, 3, 1, 2]
  | 5 => [2, 5, 3, 1, 5, 1, 5, 2, 5, 3, 1, 5, 1, 5]
  | 6 => [0, 3, 1, 2, 0, 3, 1, 2, 4, 0, 4, 0, 2, 4]
  | 7 => [4, 1, 5, 1, 3, 5, 2, 2, 0, 3, 3, 1, 2, 0, 3]
  | 8 => [0, 4, 0, 2, 4, 3, 0, 2, 1, 4, 0, 4, 0, 2, 5]
  | 9 => [1, 4, 0, 4, 0, 2, 4, 1, 4, 0, 4, 0, 2, 4, 3, 3]
  | 10 => [3, 5, 2, 5, 2, 2, 0, 2, 1, 2, 1, 2, 5, 3, 1, 5, 1]
  | 11 => [4, 3, 0, 5, 0, 4, 0, 2, 4, 1, 3, 1, 5, 3, 1, 5, 1, 5, 0]
  | 12 => [4, 2, 2, 0, 5, 3, 1, 2, 0, 3, 1, 3, 3, 0, 3, 3, 1, 3, 3]
  | 13 => [6, 6, 6]
  | 14 => [0, 0, 0]
  | 15 => [2, 2, 2, 2]
  | 16 => [3, 0, 2, 2, 0, 3, 3, 0, 3]
  | 17 => [1, 3, 3, 6, 1, 7, 1, 6, 1, 7]
  | 18 => [2, 6, 1, 3, 0, 3, 6, 0, 7, 0]
  | 19 => [2, 6, 1, 2, 6, 1, 2, 6, 1, 2, 6, 1]
  | 20 => [2, 6, 2, 0, 2, 2, 0, 2, 1, 2, 1, 6, 1]
  | 21 => [0, 6, 1, 6, 2, 1, 2, 1, 6, 1, 7, 3, 0, 3]
  | 22 => [0, 2, 1, 3, 0, 6, 1, 7, 3, 0, 6, 1, 3, 0, 3]
  | 23 => [2, 0, 3, 1, 3, 0, 3, 0, 2, 0, 3, 1, 3, 0, 3, 0]
  | 24 => [7, 3, 6, 0, 7, 1, 2, 0, 3, 7, 3, 6, 0, 7, 1, 2, 0, 3]
  | 25 => [6, 1, 7, 2, 6, 0, 6, 1, 7, 2, 6, 0, 6, 1, 7, 2, 6, 0]
  | 26 => [5, 7, 4, 6, 5, 7, 4, 6]
  | _ => []).map decode

end Theory.SpecificGroups.MathieuAmalgamCompletion
