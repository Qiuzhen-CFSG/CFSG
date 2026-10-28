module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Pointwise fixers of alternating four-subgroups of A₆

An embedded A₄ contains an involution. Its pointwise fixer lies in the
stabilizer of that involution in Aut(A₆), whose order is 32.
The subgroup is retained literally, with no choice of a conjugacy class.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, proof of 13.9.1, printed p.974,
the terminal A₆ centralizer inspection.
-/

public section
namespace AlternatingSix
open Subgroup ShadowLocal

/-- The full automorphism group fixes an embedded A₄ pointwise through a two-group. -/
theorem alternatingFour_fixer_isPGroup (U : Subgroup (alternatingGroup (Fin 6)))
    (eU : U ≃* alternatingGroup (Fin 4)) :
    IsPGroup 2 (fixingSubgroup (MulAut (alternatingGroup (Fin 6)))
      (U : Set (alternatingGroup (Fin 6)))) := by
  have hcard : Nat.card U = 12 := by
    rw [Nat.card_congr eU.toEquiv, Nat.card_eq_fintype_card]
    decide
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 (by rw [hcard]; decide)
  have ht' : orderOf (t : A6) = 2 := (orderOf_injective U.subtype U.subtype_injective t).trans ht
  have hp : IsPGroup 2 (centralizer ({MulAut.conj (t : A6)} : Set AutA6)) :=
    IsPGroup.of_card (n := 5) (inner_involution_centralizer_card t ht')
  apply hp.to_le
  intro α hα
  rw [centralizer_inner_eq_stabilizer, MulAction.mem_stabilizer_iff]
  exact (mem_fixingSubgroup_iff _).mp hα t t.property

end AlternatingSix
