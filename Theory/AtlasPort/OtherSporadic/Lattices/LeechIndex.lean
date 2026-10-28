/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechIndex.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Proof syntax and simplifier arguments are adjusted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.IntegerIndex

/-!
The index of the integral Leech lattice in the integer coordinate module.
The even and odd residue maps identify the gluing quotients and multiply their indices.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators

def evenResidue : evenGolayLattice →+ golay where
  toFun x := ⟨halfResidue x.val 0,((even_congruences x.val).mp x.prop).2.1⟩
  map_zero' := by apply Subtype.ext; ext i; simp [halfResidue,integerReduction]
  map_add' x y := by
    apply Subtype.ext
    ext i
    have hx := even_mem_coordinate_even x.val x.prop i
    have hy := even_mem_coordinate_even y.val y.prop i
    change (((x.val i + y.val i - 0) / 2 : ℤ) : Bit) =
      (((x.val i - 0) / 2 : ℤ) : Bit) + (((y.val i - 0) / 2 : ℤ) : Bit)
    have h : (x.val i + y.val i - 0) / 2 = (x.val i - 0) / 2 + (y.val i - 0) / 2 := by omega
    rw [h,Int.cast_add]

theorem evenResidue_surjective : Function.Surjective evenResidue := by
  intro c
  have he : (2 : ℤ) • golayIntegerLift c.val ∈ evenGolayLattice :=
    ⟨golayIntegerLift c.val,lift_mem_evenHalfLattice c.val c.prop,rfl⟩
  refine ⟨⟨_,he⟩,?_⟩
  apply Subtype.ext
  ext i
  have h := congrFun (integerReduction_lift c.val) i
  simpa [evenResidue,halfResidue,integerReduction] using h

theorem evenResidue_kernel : evenResidue.ker = fourEvenLattice.addSubgroupOf evenGolayLattice := by
  ext x
  constructor
  · intro hx
    have hr : halfResidue x.val 0 = 0 := congrArg Subtype.val hx
    obtain ⟨c,z,he⟩ := (evenGolayLattice_gluing x.val).mp x.prop
    have hc : halfResidue x.val 0 = c.val := by
      ext i
      have h := congrFun (integerReduction_lift c.val) i
      change (((x.val i - 0) / 2 : ℤ) : Bit) = c.val i
      rw [he i]
      have hdiv : (2 * golayIntegerLift c.val i + 4 * z.val i - 0) / 2 =
          golayIntegerLift c.val i + 2 * z.val i := by omega
      rw [hdiv]
      simpa [integerReduction] using h
    have hc0 : c.val = 0 := hc.symm.trans hr
    refine ⟨z.val,z.prop,?_⟩
    ext i
    change 4 * z.val i = x.val i
    rw [he i,hc0]
    simp [golayIntegerLift]
  · rintro ⟨z,hz,hx⟩
    apply Subtype.ext
    ext i
    have hxi := congrFun hx i
    change 4 * z i = x.val i at hxi
    change (((x.val i - 0) / 2 : ℤ) : Bit) = 0
    rw [← hxi]
    have hdiv : (4 * z i - 0) / 2 = 2 * z i := by omega
    rw [hdiv]
    simp

theorem even_gluing_index : fourEvenLattice.relIndex evenGolayLattice = 2^12 := by
  rw [AddSubgroup.relIndex,← evenResidue_kernel,AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.mpr evenResidue_surjective]
  have h : Nat.card golay = 2^12 := by
    rw [golay_card]
    norm_num
  simpa using h

theorem evenGolayLattice_index : evenGolayLattice.index = 2^37 := by
  have h := AddSubgroup.relIndex_mul_index fourEvenLattice_le_even
  rw [even_gluing_index,fourEvenLattice_index] at h
  norm_num at h ⊢
  omega

def leechParity : leech →+ Bit where
  toFun x := (x.val ((0,0),0) : Bit)
  map_zero' := by simp
  map_add' x y := by simp

theorem leechParity_surjective : Function.Surjective leechParity := by
  intro b
  rcases bit_cases b with h | h
  · subst b; exact ⟨0,by simp⟩
  · subst b
    refine ⟨⟨oddGlue ((0,0),0),oddGlue_mem _⟩,?_⟩
    change ((-3 : ℤ) : Bit) = 1
    decide

theorem leechParity_kernel : leechParity.ker = evenGolayLattice.addSubgroupOf leech.toAddSubgroup := by
  ext x
  constructor
  · intro hx
    have hp : x.val ((0,0),0) % 2 = 0 :=
      Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hx)
    have h := x.prop
    change x.val ∈ leechAt ((0,0),0) at h
    rcases h with h | h
    · exact h
    · have hi := ((odd_congruences ((0,0),0) x.val).mp h).1 ((0,0),0)
      omega
  · intro hx
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr
    exact Int.dvd_of_emod_eq_zero (even_mem_coordinate_even x.val hx ((0,0),0))

theorem odd_gluing_index : evenGolayLattice.relIndex leech.toAddSubgroup = 2 := by
  rw [AddSubgroup.relIndex,← leechParity_kernel,AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.mpr leechParity_surjective]
  simp

theorem leech_index : leech.toAddSubgroup.index = 2^36 := by
  have he : evenGolayLattice ≤ leech.toAddSubgroup := fun _ hx => Or.inl hx
  have h := AddSubgroup.relIndex_mul_index he
  rw [odd_gluing_index,evenGolayLattice_index] at h
  norm_num at h ⊢
  omega

end Atlas.Lattices
