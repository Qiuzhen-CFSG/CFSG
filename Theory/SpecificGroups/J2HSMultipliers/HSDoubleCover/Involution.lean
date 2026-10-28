module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.GeneratorCover
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound.Base
public import Mathlib.GroupTheory.Perm.Support

/-!
# A fixed-point-free involution in the degree-100 Higman–Sims action

The literal word `(a * b²)⁵` in the published ATLAS generators is an
involution moving all 100 points, hence a product of 50 disjoint transpositions.
The checks use the existing packed tables, already identified with the actual
ATLAS generators. All finite calculations are checked by Lean's kernel.
This supplies the odd number of four-point blocks needed for the central
square in `HSDoubleCover.lean`.

Source: ATLAS HSG1-p100B0, with action conventions and attribution in
`LeechRelated/AtlasCarriers/HS.lean`; Aschbacher–Smith I.1.3(1), printed p.407.
-/

public section
namespace Theory.SpecificGroups.J2HSMultipliers.HS
open Sporadic.LeechRelated.HS
open Sporadic.LeechRelated.HS.OrderCertificate

@[expose] def involution : Carrier := (generatorAElement * generatorBElement ^ 2) ^ 5

private def fastInvolution : Equiv.Perm (Fin 100) := (p0 * p1 ^ 2) ^ 5

private theorem involution_perm : (involution : Equiv.Perm (Fin 100)) = fastInvolution := by
  change (generatorA * generatorB ^ 2) ^ 5 = _
  rw [← a_eq_generator, ← b_eq_generator]
  rfl

theorem involution_square : involution ^ 2 = 1 := by
  apply Subtype.ext
  change (involution : Equiv.Perm (Fin 100)) ^ 2 = 1
  rw [involution_perm]
  apply Equiv.ext
  apply allFin
  decide +kernel

theorem involution_fixedPointFree (i : Fin 100) :
    (involution : Equiv.Perm (Fin 100)) i ≠ i := by
  rw [involution_perm]
  have h : ∀ i : Fin 100, fastInvolution i ≠ i := by
    apply allFin
    decide +kernel
  exact h i

theorem involution_support_card :
    (involution : Equiv.Perm (Fin 100)).support.card = 100 := by
  have h : (involution : Equiv.Perm (Fin 100)).support = Finset.univ := by
    ext i
    simp only [Finset.mem_univ, iff_true, Equiv.Perm.mem_support]
    exact involution_fixedPointFree i
  rw [h]
  simp

end Theory.SpecificGroups.J2HSMultipliers.HS
