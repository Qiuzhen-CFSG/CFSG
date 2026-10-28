/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechCongruences.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Adapted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechGluing

/-!
Coordinate congruences characterizing the integral Leech lattice.
The even and odd glue cosets give the two parity cases of the characterization.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators

def halfResidue (x : IntegerCoordinates) (m : ℤ) : BinaryWord :=
  integerReduction (fun i => (x i - m) / 2)

def LeechCongruences (x : IntegerCoordinates) : Prop :=
  ∃ m : ℤ, (m = 0 ∨ m = 1) ∧ (∀ i, x i % 2 = m) ∧
    halfResidue x m ∈ golay ∧ (∑ i, x i) % 8 = 4 * m

theorem even_congruences (x : IntegerCoordinates) :
    x ∈ evenGolayLattice ↔ (∀ i, x i % 2 = 0) ∧
      halfResidue x 0 ∈ golay ∧ (∑ i, x i) % 8 = 0 := by
  constructor
  · intro hx
    obtain ⟨y,hc,hs,he⟩ := (mem_evenGolayLattice x).mp hx
    refine ⟨even_mem_coordinate_even x hx,?_,?_⟩
    · have hr : halfResidue x 0 = integerReduction y := by
        ext i
        simp [halfResidue,integerReduction,he i]
      rw [hr]; exact hc
    · have hsum : (∑ i, x i) = 2 * ∑ i, y i := by
        simp_rw [he]; rw [Finset.mul_sum]
      rw [hsum]; omega
  · rintro ⟨hp,hc,hs⟩
    apply (mem_evenGolayLattice x).mpr
    let y : IntegerCoordinates := fun i => x i / 2
    have he (i : Omega) : x i = 2 * y i := by
      have h := hp i
      dsimp [y]; omega
    refine ⟨y,by simpa [halfResidue,y] using hc,?_,he⟩
    have hsum : (∑ i, x i) = 2 * ∑ i, y i := by
      simp_rw [he]; rw [Finset.mul_sum]
    rw [hsum] at hs
    omega

theorem odd_congruences (a : Omega) (x : IntegerCoordinates) :
    x - oddGlue a ∈ evenGolayLattice ↔ (∀ i, x i % 2 = 1) ∧
      halfResidue x 1 ∈ golay ∧ (∑ i, x i) % 8 = 4 := by
  have hp (i : Omega) : oddGlue a i % 2 = 1 := by
    by_cases h : i = a <;> norm_num [oddGlue,h]
  have hs : (∑ i, (x - oddGlue a) i) = (∑ i, x i) - 20 := by
    simp only [Pi.sub_apply,Finset.sum_sub_distrib,oddGlue_sum]
  have hr : halfResidue (x - oddGlue a) 0 = halfResidue x 1 := by
    ext i
    change (((x i - oddGlue a i - 0) / 2 : ℤ) : Bit) = (((x i - 1) / 2 : ℤ) : Bit)
    by_cases h : i = a
    · subst i
      simp only [oddGlue,ite_true]
      have he : (x a - (1 - 4) - 0) / 2 = (x a - 1) / 2 + 2 := by omega
      rw [he]; simp
    · simp [oddGlue,h]
  rw [even_congruences,hr,hs]
  constructor
  · rintro ⟨he,hc,hxs⟩
    refine ⟨fun i => ?_,hc,by omega⟩
    have h := he i
    have hu := hp i
    change (x i - oddGlue a i) % 2 = 0 at h
    omega
  · rintro ⟨he,hc,hxs⟩
    refine ⟨fun i => ?_,hc,by omega⟩
    have h := he i
    have hu := hp i
    change (x i - oddGlue a i) % 2 = 0
    omega

theorem leechAt_iff_congruences (a : Omega) (x : IntegerCoordinates) :
    x ∈ leechAt a ↔ LeechCongruences x := by
  rw [mem_leechAt,even_congruences,odd_congruences]
  constructor
  · rintro (h | h)
    · exact ⟨0,Or.inl rfl,h.1,h.2.1,by simpa using h.2.2⟩
    · exact ⟨1,Or.inr rfl,h.1,h.2.1,by simpa using h.2.2⟩
  · rintro ⟨m,(rfl | rfl),hp,hc,hs⟩
    · exact Or.inl ⟨hp,hc,by simpa using hs⟩
    · exact Or.inr ⟨hp,hc,by simpa using hs⟩

theorem mem_leech (x : IntegerCoordinates) : x ∈ leech ↔ LeechCongruences x :=
  leechAt_iff_congruences ((0,0),0) x

end Atlas.Lattices
