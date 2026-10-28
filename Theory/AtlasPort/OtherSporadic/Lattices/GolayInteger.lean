/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/GolayInteger.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Adapted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.GolayDistribution

/-!
Integer lifts of binary Golay words and the even Golay lattice.
Reduction modulo two and the doubly-even code property control coordinate sums.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators

abbrev IntegerCoordinates := Omega → ℤ
abbrev RationalCoordinates := Omega → ℚ

def integerReduction : IntegerCoordinates →+ BinaryWord where
  toFun x := fun i => (x i : Bit)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

def coordinateSum : IntegerCoordinates →+ ℤ where
  toFun x := ∑ i, x i
  map_zero' := by simp
  map_add' x y := Finset.sum_add_distrib

def evenHalfLattice : AddSubgroup IntegerCoordinates where
  carrier := {y | integerReduction y ∈ golay ∧ (∑ i, y i) % 4 = 0}
  zero_mem' := ⟨by rw [map_zero]; exact golay.zero_mem, by simp⟩
  add_mem' := by
    rintro x y ⟨hx,hxs⟩ ⟨hy,hys⟩
    refine ⟨?_,?_⟩
    · rw [map_add]; exact golay.add_mem hx hy
    · change (∑ i, (x i + y i)) % 4 = 0
      rw [Finset.sum_add_distrib, Int.add_emod, hxs, hys]
      rfl
  neg_mem' := by
    rintro x ⟨hx,hxs⟩
    refine ⟨?_,?_⟩
    · rw [map_neg]; exact golay.neg_mem hx
    · change (∑ i, -x i) % 4 = 0
      rw [Finset.sum_neg_distrib]
      omega

def doubleCoordinates : IntegerCoordinates →+ IntegerCoordinates where
  toFun x := 2 • x
  map_zero' := by simp
  map_add' x y := smul_add 2 x y

def evenGolayLattice : AddSubgroup IntegerCoordinates :=
  evenHalfLattice.map doubleCoordinates

theorem mem_evenGolayLattice (x : IntegerCoordinates) :
    x ∈ evenGolayLattice ↔ ∃ y : IntegerCoordinates,
      integerReduction y ∈ golay ∧ (∑ i, y i) % 4 = 0 ∧ (∀ i, x i = 2 * y i) := by
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨y,hy.1,hy.2,fun i => by simp [doubleCoordinates, nsmul_eq_mul]⟩
  · rintro ⟨y,hc,hs,he⟩
    refine ⟨y,⟨hc,hs⟩,?_⟩
    ext i
    simp [doubleCoordinates, nsmul_eq_mul, he i]

def golayIntegerLift (c : BinaryWord) : IntegerCoordinates := fun i => if c i = 0 then 0 else 1

theorem integerReduction_lift (c : BinaryWord) : integerReduction (golayIntegerLift c) = c := by
  ext i
  rcases bit_cases (c i) with h | h <;> simp [integerReduction,golayIntegerLift,h]

theorem sum_golayIntegerLift (c : BinaryWord) :
    (∑ i, golayIntegerLift c i) = (hammingNorm c : ℤ) := by
  rw [hammingNorm_eq_sum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [golayIntegerLift]

theorem lift_mem_evenHalfLattice (c : BinaryWord) (hc : c ∈ golay) :
    golayIntegerLift c ∈ evenHalfLattice := by
  refine ⟨by simpa [integerReduction_lift] using hc,?_⟩
  rw [sum_golayIntegerLift]
  obtain ⟨k,hk⟩ := golay_doublyEven c hc
  rw [hk]
  simp

end Atlas.Lattices
