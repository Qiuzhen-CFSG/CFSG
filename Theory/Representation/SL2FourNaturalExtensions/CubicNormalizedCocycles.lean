module

public import Theory.Representation.SL2FourNaturalOrbits.Model
public import Theory.Representation.SL2NaturalFirstCohomology
public import Theory.Representation.FirstCohomology
import Mathlib.Tactic.Abel

/-!
# Natural endpoint cocycles fixing a prescribed cubic actor

Every natural cocycle can be changed by an explicit principal cocycle to
vanish on a specified element whose cube is one. Applying this normalization
to the square-root cocycle gives representatives of all four cohomology
classes with the same prescribed vanishing. These representatives supply
the displacement cocycles for endpoint automorphisms fixing that actor.
-/

@[expose] public section

namespace Representation.SL2FourNaturalExtensions
open SL2FourNatural OneCohomology

/-- The defining-field representation used for natural endpoint cocycles. -/
abbrev naturalCocycleRep : Representation F SL V := specialLinearNatural 2

/-- Add the principal correction determined by the chosen cubic actor. -/
def normalizedCocycle (a : SL) (f : cocycles naturalCocycleRep) :
    cocycles naturalCocycleRep :=
  f + principal naturalCocycleRep (naturalCocycleRep a (f.val a))

/-- The correction kills the cocycle value at the prescribed actor. -/
theorem normalizedCocycle_at (a : SL) (ha : a ^ 3 = 1)
    (f : cocycles naturalCocycleRep) : (normalizedCocycle a f).val a = 0 := by
  have h1 : f.val 1 = 0 := by
    have h := f.property 1 1
    simpa using h.symm
  have hnorm := f.property a (a * a)
  rw [f.property a a, map_add] at hnorm
  have ha' : a * (a * a) = 1 := by simpa only [pow_succ, pow_zero, one_mul,
    mul_assoc] using ha
  rw [ha', h1] at hnorm
  change f.val a +
    (naturalCocycleRep a (naturalCocycleRep a (f.val a)) -
      naturalCocycleRep a (f.val a)) = 0
  have hsub (v w : V) : v - w = v + w := by
    funext i
    exact CharTwo.sub_eq_add (v i) (w i)
  rw [hsub]
  calc
    _ = (naturalCocycleRep a (naturalCocycleRep a (f.val a)) +
        naturalCocycleRep a (f.val a)) + f.val a := by abel
    _ = 0 := hnorm.symm

/-- The normalization preserves the entire cohomology class. -/
theorem normalizedCocycle_class (a : SL) (f : cocycles naturalCocycleRep) :
    classMap naturalCocycleRep (normalizedCocycle a f) =
      classMap naturalCocycleRep f := by
  rw [normalizedCocycle, map_add,
    (classMap_eq_zero_iff _ _).mpr ⟨naturalCocycleRep a (f.val a), rfl⟩, add_zero]

/-- Representatives of all four classes normalized at the same actor. -/
noncomputable def cubicCocycle (a : SL) (k : F) : cocycles naturalCocycleRep :=
  normalizedCocycle a (k • SL2NaturalH1.sqrtCocycle)

/-- Every member of the family vanishes at the prescribed cubic actor. -/
theorem cubicCocycle_at (a : SL) (ha : a ^ 3 = 1) (k : F) :
    (cubicCocycle a k).val a = 0 :=
  normalizedCocycle_at a ha _

/-- The field parameter is exactly the original first-cohomology parameter. -/
theorem cubicCocycle_class (a : SL) (k : F) :
    classMap naturalCocycleRep (cubicCocycle a k) = SL2NaturalH1.parameterClass k := by
  rw [cubicCocycle, normalizedCocycle_class, map_smul]
  rfl

/-- Normalizing at one actor does not identify distinct cocycle classes. -/
theorem cubicCocycle_injective (a : SL) : Function.Injective (cubicCocycle a) := by
  intro k l h
  apply (SL2NaturalH1.parameterClass_bijective (K := F) (by
    rw [Nat.card_eq_fintype_card, card_field]
    decide)).injective
  simpa only [cubicCocycle_class] using congrArg (classMap naturalCocycleRep) h

/-- Every natural cohomology class has a unique representative in this family. -/
theorem existsUnique_cubicCocycle_class (a : SL) (z : H1 naturalCocycleRep) :
    ∃! k : F, classMap naturalCocycleRep (cubicCocycle a k) = z := by
  have hb := SL2NaturalH1.parameterClass_bijective (K := F) (by
    rw [Nat.card_eq_fintype_card, card_field]
    decide)
  obtain ⟨k, hk⟩ := hb.surjective z
  refine ⟨k, ?_, ?_⟩
  · simpa only [cubicCocycle_class] using hk
  · intro l hl
    apply hb.injective
    simpa only [cubicCocycle_class] using hl.trans hk.symm

end Representation.SL2FourNaturalExtensions
