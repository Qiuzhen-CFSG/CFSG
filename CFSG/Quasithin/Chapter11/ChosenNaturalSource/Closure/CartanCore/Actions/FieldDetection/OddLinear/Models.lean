module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.LinearThree
public import Theory.SpecificGroups.SL2.EvenBorelResidual.FieldInvolution

/-!
# Actual quotient markings for the odd-degree sieve

The surviving linear case of A.3.15 supplies a marking of the literal
I/O₂(I), and an original Cartan element acting as a nonidentity odd-order
coefficient automorphism. This interface records that mathematical output;
it does not assert its existence or contain a Borel-movement conclusion.
The source sieve and the simultaneous Sylow/subfield construction are
separate producers. Source: Aschbacher--Smith 11.5.6(3), printed p.781.
-/

@[expose] public section
open Subgroup
open scoped MatrixGroups
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- A genuine projective linear quotient with its literal field actor.
The intended ranks are two and three. No choice of a subfield subgroup,
invariant Borel or normalizer lifts is part of these data. -/
structure LinearFieldMarking (I : Subgroup G) (d : ℕ) where
  field : BinaryField
  model : (I ⧸ pCore 2 I) ≃* PSL(d, field.Carrier)
  actor : normalizer (I : Set G)
  actor_mem : (actor : G) ∈ E.X
  coefficient : field.Carrier ≃+* field.Carrier
  odd_order : Odd (orderOf coefficient)
  nontrivial : coefficient ≠ 1
  action : ∀ z, model (coreQuotientAction I actor z) =
    Atlas.fieldEquivPSL d coefficient (model z)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear
