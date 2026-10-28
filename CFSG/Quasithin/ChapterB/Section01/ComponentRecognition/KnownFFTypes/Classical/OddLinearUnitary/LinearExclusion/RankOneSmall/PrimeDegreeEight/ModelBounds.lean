module

public import CFSG.Quasithin.ClassicalModels
public import Theory.ElementaryAbelian.Basic

/-!
# The two model generation inputs for the small prime PSL₂ degree bound

The group is the actual matrix PSL₂ carrier and the actors are subgroups of
its full automorphism group. Conjugators belong to PSL₂, so they lift to any
specified central cover. Both inner and diagonal actors are included. The
prime-field restriction removes field automorphisms.

These are explicit outstanding group-theoretic inputs, not asserted generation
theorems. Their consumer in `PrimeDegreeEight` handles the original binary
representation and all cover transport. Source: Guralnick--Malle,
*Classification of 2F-modules I*, Proposition 4.1, manuscript pp.8--9;
Aschbacher--Smith K.2, printed p.453.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight
open Subgroup
open scoped MatrixGroups

/-- Generation by a specified number of inner conjugates of an elementary
actor of the specified order, inside the actual automorphism group. -/
def ActorGeneration (S : Type*) [Group S] (m n : ℕ) : Prop :=
  ∀ A : Subgroup (MulAut S), IsElementaryAbelian 2 A → Nat.card A = m →
    ∃ c : Fin n → S, (MulAut.conj : S →* MulAut S).range ≤
      ⨆ i, A.map (MulAut.conj (MulAut.conj (c i))).toMonoidHom

/-- The cyclic-actor calculation required at precisely the four prime parameters. -/
def CyclicModelGeneration : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (q : ℕ),
    (q = 13 ∨ q = 17 ∨ q = 19 ∨ q = 23) → Nat.card F = q →
      ActorGeneration PSL(2, F) 2 4

/-- Two conjugates of every four-group generate at least the inner PSL₂.
A four-group may contain diagonal automorphisms; containment in PSL₂ is not assumed. -/
def FourGroupModelGeneration : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (q : ℕ),
    (q = 13 ∨ q = 17 ∨ q = 19 ∨ q = 23) → Nat.card F = q →
      ActorGeneration PSL(2, F) 4 2

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight
