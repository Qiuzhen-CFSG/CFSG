/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechGluing.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Proof syntax and simplifier arguments are adjusted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.GolayGluing

/-!
The integral Leech lattice obtained by adjoining an odd glue vector.
The two cosets form a lattice, and glue differences prove independence of the marked coordinate.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators

def oddGlue (a : Omega) : IntegerCoordinates := fun i => 1 - if i = a then 4 else 0

theorem oddGlue_sum (a : Omega) : (∑ i, oddGlue a i) = 20 := by
  simp [oddGlue, Finset.sum_sub_distrib, Omega, HexIndex]

theorem oddGlue_reduction (a : Omega) : integerReduction (oddGlue a) = allOnes := by
  ext i
  change ((oddGlue a i : ℤ) : ZMod 2) = 1
  by_cases h : i = a <;> simp only [oddGlue,h,ite_true,ite_false] <;> decide

theorem oddGlue_mem_half (a : Omega) : oddGlue a ∈ evenHalfLattice := by
  refine ⟨?_,?_⟩
  · rw [oddGlue_reduction]
    exact C0_le_golay allOnes_mem_C0
  · rw [oddGlue_sum]; rfl

theorem twice_oddGlue_mem_even (a : Omega) : oddGlue a + oddGlue a ∈ evenGolayLattice := by
  apply (mem_evenGolayLattice _).mpr
  exact ⟨oddGlue a,(oddGlue_mem_half a).1,(oddGlue_mem_half a).2,fun i => by simp; ring⟩

def leechAt (a : Omega) : AddSubgroup IntegerCoordinates where
  carrier := {x | x ∈ evenGolayLattice ∨ x - oddGlue a ∈ evenGolayLattice}
  zero_mem' := Or.inl evenGolayLattice.zero_mem
  add_mem' := by
    intro x y hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Or.inl (evenGolayLattice.add_mem hx hy)
    · exact Or.inr (by convert evenGolayLattice.add_mem hx hy using 1; abel)
    · exact Or.inr (by convert evenGolayLattice.add_mem hx hy using 1; abel)
    · exact Or.inl (by
        convert evenGolayLattice.add_mem (evenGolayLattice.add_mem hx hy)
          (twice_oddGlue_mem_even a) using 1; abel)
  neg_mem' := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl (evenGolayLattice.neg_mem hx)
    · exact Or.inr (by
        convert evenGolayLattice.sub_mem (evenGolayLattice.neg_mem hx)
          (twice_oddGlue_mem_even a) using 1; abel)

theorem mem_leechAt (a : Omega) (x : IntegerCoordinates) :
    x ∈ leechAt a ↔ x ∈ evenGolayLattice ∨ x - oddGlue a ∈ evenGolayLattice := Iff.rfl

theorem oddGlue_mem (a : Omega) : oddGlue a ∈ leechAt a :=
  Or.inr (by simp only [sub_self]; exact evenGolayLattice.zero_mem)

theorem even_mem_coordinate_even (x : IntegerCoordinates) (hx : x ∈ evenGolayLattice)
    (i : Omega) : x i % 2 = 0 := by
  obtain ⟨y,_,_,he⟩ := (mem_evenGolayLattice x).mp hx
  rw [he i]
  omega

theorem gluing_disjoint (a : Omega) (x : IntegerCoordinates) (hx : x ∈ evenGolayLattice) :
    x - oddGlue a ∉ evenGolayLattice := by
  intro h
  have h1 := even_mem_coordinate_even x hx a
  have h2 := even_mem_coordinate_even _ h a
  simp only [Pi.sub_apply,oddGlue,ite_true] at h2
  omega

theorem oddGlue_difference (a b : Omega) : oddGlue a - oddGlue b ∈ evenGolayLattice := by
  apply (mem_evenGolayLattice _).mpr
  let y : IntegerCoordinates := fun i => (if i = b then 2 else 0) - (if i = a then 2 else 0)
  refine ⟨y,?_,?_,?_⟩
  · have hy : integerReduction y = 0 := by
      ext i
      by_cases ha : i = a <;> by_cases hb : i = b <;> simp [integerReduction,y,ha,hb]
    rw [hy]; exact golay.zero_mem
  · simp [y,Finset.sum_sub_distrib]
  · intro i
    simp only [Pi.sub_apply,oddGlue,y]
    split_ifs <;> ring

theorem leechAt_independent (a b : Omega) : leechAt a = leechAt b := by
  apply le_antisymm
  · intro x hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (by
        convert evenGolayLattice.add_mem hx (oddGlue_difference a b) using 1; abel)
  · intro x hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (by
        convert evenGolayLattice.add_mem hx (oddGlue_difference b a) using 1; abel)

def leech : Submodule ℤ IntegerCoordinates :=
  (leechAt ((0,0),0)).toIntSubmodule

end Atlas.Lattices
