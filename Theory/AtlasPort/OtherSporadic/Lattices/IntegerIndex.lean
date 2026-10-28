/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IntegerIndex.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Proof syntax and simplifier arguments are adjusted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechRank

/-!
Indices of coordinate scaling and even-coordinate-sum lattices.
Surjective residue maps identify the relevant finite quotients and their orders.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators

def coordinateMod (n : ℕ) : IntegerCoordinates →+ (Omega → ZMod n) where
  toFun x := fun i => (x i : ZMod n)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

theorem coordinateMod_surjective (n : ℕ) [NeZero n] : Function.Surjective (coordinateMod n) := by
  intro x
  exact ⟨fun i => (x i).val,by ext i; simp [coordinateMod]⟩

def coordinateScale (n : ℤ) : IntegerCoordinates →+ IntegerCoordinates where
  toFun x := n • x
  map_zero' := by simp
  map_add' x y := smul_add n x y

theorem coordinateScale_injective (n : ℤ) (hn : n ≠ 0) : Function.Injective (coordinateScale n) := by
  intro x y h
  ext i
  have hi := congrFun h i
  change n * x i = n * y i at hi
  exact mul_left_cancel₀ hn hi

theorem coordinateScale_range (n : ℕ) : (coordinateScale n).range = (coordinateMod n).ker := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    ext i
    simp [coordinateScale,coordinateMod]
  · intro hx
    have h (i : Omega) : (n : ℤ) ∣ x i := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp
      exact congrFun hx i
    choose y hy using h
    exact ⟨y,by ext i; exact (hy i).symm⟩

theorem coordinateScale_index (n : ℕ) [NeZero n] : (coordinateScale n).range.index = n^24 := by
  rw [coordinateScale_range,AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.mpr (coordinateMod_surjective n)]
  simp [Omega,HexIndex]

def sumParity : IntegerCoordinates →+ Bit where
  toFun x := ((∑ i, x i : ℤ) : Bit)
  map_zero' := by simp
  map_add' x y := by simp [Finset.sum_add_distrib]

theorem evenCoordinateSum_eq_ker : evenCoordinateSum = sumParity.ker := by
  ext x
  change (∑ i, x i) % 2 = 0 ↔ ((∑ i, x i : ℤ) : Bit) = 0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact ⟨Int.dvd_of_emod_eq_zero,Int.emod_eq_zero_of_dvd⟩

theorem sumParity_surjective : Function.Surjective sumParity := by
  intro b
  refine ⟨coordinateVector ((0,0),0) b.val,?_⟩
  change ((∑ i, coordinateVector ((0,0),0) b.val i : ℤ) : Bit) = b
  have hs : (∑ i, coordinateVector ((0,0),0) b.val i : ℤ) = b.val := by
    simp [coordinateVector]
  rw [hs]
  simp

theorem evenCoordinateSum_index : evenCoordinateSum.index = 2 := by
  rw [evenCoordinateSum_eq_ker,AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.mpr sumParity_surjective]
  simp

def fourEvenLattice : AddSubgroup IntegerCoordinates := evenCoordinateSum.map (coordinateScale 4)

theorem fourEvenLattice_index : fourEvenLattice.index = 2^49 := by
  rw [fourEvenLattice,AddSubgroup.index_map_of_injective _ (coordinateScale_injective 4 (by norm_num)),
    evenCoordinateSum_index,show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl,coordinateScale_index]
  norm_num

theorem fourEvenLattice_le_even : fourEvenLattice ≤ evenGolayLattice := by
  rintro x ⟨z,hz,rfl⟩
  apply (evenGolayLattice_gluing _).mpr
  refine ⟨0,⟨z,hz⟩,?_⟩
  intro i
  simp [coordinateScale,golayIntegerLift]

end Atlas.Lattices
