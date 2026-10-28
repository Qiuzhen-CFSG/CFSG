/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechCrossAction.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Adapted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechCrosses

/-!
The full isometry action on crosses and the standard coordinate cross.
Transport of shell classes defines the action; axis vectors exhaust the standard cross.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem shellClasses_transport (g : LeechIsometryGroup) (r : ℤ) (a : LeechModTwo)
    (ha : a ∈ shellClasses r) : leechModTwoRepresentation g a ∈ shellClasses r := by
  obtain ⟨x,_,hx⟩ := Finset.mem_image.mp ha
  refine Finset.mem_image.mpr ⟨⟨g.val x.val,(g.prop _ _).trans x.prop⟩,Finset.mem_univ _,?_⟩
  exact (leechModTwoRepresentation_reduce g x.val).symm.trans (congrArg (leechModTwoRepresentation g) hx)

def crossAction (g : LeechIsometryGroup) (c : LeechCross) : LeechCross :=
  ⟨leechModTwoRepresentation g c.val,(minimumEightClass_iff _).mpr
    (shellClasses_transport g 8 c.val ((minimumEightClass_iff c.val).mp c.prop))⟩

def crossPermutation (g : LeechIsometryGroup) : Equiv.Perm LeechCross where
  toFun := crossAction g
  invFun := crossAction g⁻¹
  left_inv c := by
    apply Subtype.ext
    change leechModTwoMap g⁻¹ (leechModTwoMap g c.val) = c.val
    rw [← leechModTwoMap_mul,inv_mul_cancel,leechModTwoMap_one]
  right_inv c := by
    apply Subtype.ext
    change leechModTwoMap g (leechModTwoMap g⁻¹ c.val) = c.val
    rw [← leechModTwoMap_mul,mul_inv_cancel,leechModTwoMap_one]

def crossRepresentation : LeechIsometryGroup →* Equiv.Perm LeechCross where
  toFun := crossPermutation
  map_one' := by ext c; exact leechModTwoMap_one c.val
  map_mul' g h := by ext c; exact leechModTwoMap_mul g h c.val

theorem crossVectors_transport (g : LeechIsometryGroup) (c : LeechCross) :
    (crossVectors c).image g.val = crossVectors (crossAction g c) := by
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hr,hn⟩ := (crossVectors_mem c x).mp hx
    apply (crossVectors_mem _ _).mpr
    exact ⟨(leechModTwoRepresentation_reduce g x).symm.trans (congrArg (leechModTwoRepresentation g) hr),
      (g.prop x x).trans hn⟩
  · rw [Finset.card_image_of_injective _ g.val.injective,crossVectors_card,crossVectors_card]

def coordinateEight (a : Omega) : leech := ⟨coordinateVector a 8,coordinate_eight_mem a⟩

theorem coordinateEight_class (a b : Omega) : leechReduction (coordinateEight a) = leechReduction (coordinateEight b) := by
  apply (leechReduction_eq_iff _ _).mpr
  refine ⟨⟨coordinateVector a 4 - coordinateVector b 4,difference_mem a b⟩,?_⟩
  apply Subtype.ext
  ext i
  change coordinateVector a 8 i = coordinateVector b 8 i + 2 * (coordinateVector a 4 i - coordinateVector b 4 i)
  simp only [coordinateVector,Pi.single_apply]
  split_ifs <;> norm_num

def standardCrossAt (a : Omega) : LeechCross :=
  ⟨leechReduction (coordinateEight a),(minimumEightClass_iff _).mpr (by
    refine Finset.mem_image.mpr ⟨⟨coordinateEight a,?_⟩,Finset.mem_univ _,rfl⟩
    change integerDot (coordinateVector a 8) (coordinateVector a 8) = _
    rw [integerDot_coordinateVector]
    simp [coordinateVector])⟩

def standardCross : LeechCross := standardCrossAt ((0,0),0)

theorem standardCross_independent (a b : Omega) : standardCrossAt a = standardCrossAt b :=
  Subtype.ext (coordinateEight_class a b)

def crossIntegerVectors (c : LeechCross) : Finset IntegerCoordinates := (crossVectors c).image Subtype.val

theorem crossIntegerVectors_card (c : LeechCross) : (crossIntegerVectors c).card = 48 := by
  rw [crossIntegerVectors,Finset.card_image_of_injective _ Subtype.val_injective,crossVectors_card]

theorem standardCross_vectors : crossIntegerVectors standardCross = axisEightVectors := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
    let y : leech := ⟨eightAxisVector p,eightAxisVector_mem p⟩
    refine Finset.mem_image.mpr ⟨y,(crossVectors_mem _ _).mpr ⟨?_,eightAxisVector_norm p⟩,rfl⟩
    by_cases hp : p.2 = 0
    · have hy : y = coordinateEight p.1 := by apply Subtype.ext; simp [y,eightAxisVector,hp,coordinateEight]
      rw [hy]
      exact coordinateEight_class p.1 ((0,0),0)
    · have hy : y = -(coordinateEight p.1) := by
        apply Subtype.ext
        simp [y,eightAxisVector,hp,coordinateEight,coordinateVector,Pi.single_neg]
      rw [hy,leechReduction_neg]
      exact coordinateEight_class p.1 ((0,0),0)
  · rw [crossIntegerVectors_card,axisEightVectors_card]

end Atlas.Lattices
