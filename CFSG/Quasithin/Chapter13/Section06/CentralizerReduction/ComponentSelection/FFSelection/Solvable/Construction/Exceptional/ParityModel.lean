module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# A common concrete model for the remaining outer calculation

This is the parity-matched subgroup of the genuine permutation groups
S₆ and S₃. Both projections are literal coordinate projections; the cubic
is their specified kernel. The pending source-action comparison must
construct the relation between this model and the original offender
representation. These definitions assert no classification or model
identification.

The finite Sylow calculation and the source-action comparison use this
same carrier. Source: Aschbacher–Smith, B.5.6(4) and the natural S₆
calculation in the proof of B.5.7, printed pp.105–106.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional.SixPoint
open Subgroup

/-- The literal parity-matched subgroup of S₆ × S₃. -/
def paritySubgroup : Subgroup (Equiv.Perm (Fin 6) × Equiv.Perm (Fin 3)) where
  carrier := {g | Equiv.Perm.sign g.1 = Equiv.Perm.sign g.2}
  one_mem' := by simp
  mul_mem' ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, ha, hb]
  inv_mem' ha := by
    simp only [Set.mem_ofPred_eq] at *
    simp only [Prod.fst_inv, Prod.snd_inv, map_inv, ha]

abbrev Actor := paritySubgroup

/-- The actual six-point projection. -/
def firstProjection : Actor →* Equiv.Perm (Fin 6) :=
  (MonoidHom.fst _ _).comp paritySubgroup.subtype

/-- The actual three-point projection, used on the cubic moved plane. -/
def secondProjection : Actor →* Equiv.Perm (Fin 3) :=
  (MonoidHom.snd _ _).comp paritySubgroup.subtype

/-- The standard cubic factor is the literal kernel of the first projection. -/
def cubic : Subgroup Actor := firstProjection.ker

@[simp] theorem parity (g : Actor) :
    Equiv.Perm.sign (firstProjection g) = Equiv.Perm.sign (secondProjection g) := g.property

/-- Both projections jointly distinguish elements of the actual actor. -/
theorem projections_injective (x y : Actor)
    (hfirst : firstProjection x = firstProjection y)
    (hsecond : secondProjection x = secondProjection y) : x = y :=
  Subtype.ext (Prod.ext hfirst hsecond)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional.SixPoint
