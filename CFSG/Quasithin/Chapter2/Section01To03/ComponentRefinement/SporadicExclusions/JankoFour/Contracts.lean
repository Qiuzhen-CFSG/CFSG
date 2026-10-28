module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Interface
public import Theory.Mathieu.M24.TwoLocalExtensions

/-!
# The Mathieu-local route to the J4 block cover

The concrete E2048.M24 subgroup has a nontrivial self-centralizing two-core.
Adjoining the supplied Sylow subgroup to suitable conjugate local factors
should give groups with a normal series of shape 2-group / M24^n / 2-group.
The middle factor here is an actual direct power of the fixed Mathieu carrier;
the normal two-kernels and the outer two-group are retained.

This interface separates two mathematical assertions needed for the J4 case
of Aschbacher–Smith 2.3.9(7), printed p.526: construction and generation of
the local family, and exclusion of subnormal chi-zero blocks in these
extensions. It asserts neither of those missing results. In particular it
is not an inhabitant of `CentralizerBlockCover`.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.JankoFour

open Subgroup

variable {G : Type*} [Group G]

/-- The geometric part of the proposed J4 local family. Every member
contains the actual S, is inside LS, and has a nontrivial self-centralizing
two-core. Its normal series retains the actual Mathieu factors and kernels. -/
structure MathieuLocalCover (L S : Subgroup G) (z : G) where
  locals : Set (Subgroup G)
  generated : L ≤ centralizer ({z} : Set G) ⊔ sSup locals
  within : ∀ K ∈ locals, K ≤ L ⊔ S
  even : ∀ K ∈ locals, K ∈ Chapter1.HeOver G (S : Set G)
  layers : ∀ K ∈ locals, Sporadic.Mathieu.HasMathieuTwoLayer K

end CFSG.Quasithin.Chapter2.ComponentRefinement.JankoFour

end
