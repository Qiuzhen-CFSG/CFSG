module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Realization.Actors

/-!
# An actual order-seven word in the canonical SU₃(5) group

The word a³bab in the two previously realized actors is checked in the
polynomial-coordinate field of order 25. Its seventh power is the identity
and its (0,0) entry is not one. The existing group equivalence then transports
its order and word identity to the literal canonical group. This fixes the
actor used in the degree-20 spectral certificates.

Source application: Guralnick–Malle, *Classification of 2F-modules I*,
Proposition 4.3, pp.10–11; Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public section

open Matrix
open Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors.Realization
open BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five.Embedding
namespace Representation.SU3.FiveSmallModules.SevenRestriction.SmallFactors.Trivial

def tableSeven : TableGroup := tableActor 0 ^ 3 * tableActor 1 * tableActor 0 * tableActor 1

def sevenMatrix : Matrix (Fin 3) (Fin 3) F25 :=
  !![⟨3,3⟩,⟨1,1⟩,⟨4,1⟩;⟨0,2⟩,⟨3,2⟩,⟨0,1⟩;⟨3,2⟩,⟨1,1⟩,⟨4,4⟩]

theorem tableSeven_matrix : ((tableSeven.val : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) = sevenMatrix := by
  change (tableActorMatrix 0)^3 * tableActorMatrix 1 * tableActorMatrix 0 * tableActorMatrix 1 = _
  decide +kernel

theorem sevenMatrix_pow : sevenMatrix ^ 7 = 1 := by decide +kernel

theorem tableSeven_order : orderOf tableSeven = 7 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply orderOf_eq_prime
  · apply Subtype.ext
    apply Units.ext
    change (((tableSeven.val : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25))^7 = 1
    rw [tableSeven_matrix, sevenMatrix_pow]
  · intro h
    have he := congrArg (fun x : TableGroup => (x.val : Matrix (Fin 3) (Fin 3) F25)) h
    rw [tableSeven_matrix] at he
    have hh := congrFun (congrFun he 0) 0
    change (⟨3,3⟩ : F25) = 1 at hh
    exact (by decide : (⟨3,3⟩ : F25) ≠ 1) hh

noncomputable def sevenActor := canonicalEquiv tableSeven

theorem sevenActor_order : orderOf sevenActor = 7 :=
  (canonicalEquiv.orderOf_eq tableSeven).trans tableSeven_order

theorem sevenActor_word : sevenActor = actor 0 ^ 3 * actor 1 * actor 0 * actor 1 := by
  simp only [sevenActor, tableSeven, map_mul, map_pow, actor]
end Representation.SU3.FiveSmallModules.SevenRestriction.SmallFactors.Trivial
