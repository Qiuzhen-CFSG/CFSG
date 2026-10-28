/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/EisensteinPhaseBound.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.EisensteinOrthogonality
public import Mathlib.Data.Finset.Max

/-!
# Eisenstein Phase Bound

An injective family of nonzero vectors that are pairwise orthogonal or differ by a cubic phase has at most 36 members. A maximal orthogonal family has size at most 12, and its phase triples cover the family.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/EisensteinPhaseBound.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for the source coordinate computations.
-/

@[expose] public section

namespace Atlas.Lattices
open Atlas.Algebra
open scoped BigOperators

/-- Hermitian symmetry for the marked scalar form. -/
theorem eisensteinHermitian_star_symm (x y : EisensteinRationalCoordinates) :
    star (eisensteinHermitian x y) = eisensteinHermitian y x := by
  unfold eisensteinHermitian
  simp only [star_smul, star_sum, star_mul, star_star, star_trivial]

theorem eisensteinHermitian_zero_symm
    {x y : EisensteinRationalCoordinates} (h : eisensteinHermitian x y = 0) :
    eisensteinHermitian y x = 0 := by
  rw [← eisensteinHermitian_star_symm, h, star_zero]

/-- A finite injective family of nonzero vectors, any two of which are
orthogonal or differ by one of the three scalar phases, has at most 36 members.
A maximal orthogonal subfamily has at most 12 members and its phase triples
cover the original family; closure under phases is not assumed. -/
theorem eisenstein_phase_or_orthogonal_card_le
    {ι : Type*} [Fintype ι] (v : ι → EisensteinRationalCoordinates)
    (hinj : Function.Injective v) (hne : ∀ i, v i ≠ 0)
    (hclass : ∀ i j, v i = v j ∨ v i = eisensteinRotation (v j) ∨
      v i = eisensteinRotation (eisensteinRotation (v j)) ∨
      eisensteinHermitian (v i) (v j) = 0) : Fintype.card ι ≤ 36 := by
  classical
  let P (S : Finset ι) := ∀ i ∈ S, ∀ j ∈ S, i ≠ j → eisensteinHermitian (v i) (v j) = 0
  let ss : Finset (Finset ι) := Finset.univ.filter P
  have hss : ss.Nonempty := ⟨∅, by simp [ss, P]⟩
  obtain ⟨S, hSmem, hmax⟩ := Finset.exists_max_image ss Finset.card hss
  have hS : P S := (Finset.mem_filter.mp hSmem).2
  have hScard : S.card ≤ 12 := by
    have h := eisenstein_orthogonal_card_le_twelve (fun j : S => v j.val)
      (fun j => hne j.val) (fun i j hij =>
        hS i.val i.property j.val j.property (fun he => hij (Subtype.ext he)))
    simpa only [Fintype.card_coe] using h
  have hcover : ∀ i, ∃ j ∈ S, v i = v j ∨ v i = eisensteinRotation (v j) ∨
      v i = eisensteinRotation (eisensteinRotation (v j)) := by
    intro i
    by_contra! hc
    have hi : i ∉ S := by
      intro hi
      exact (hc i hi).1 rfl
    have ho : ∀ j ∈ S, eisensteinHermitian (v i) (v j) = 0 := by
      intro j hj
      rcases hclass i j with h | h | h | h
      · exact ((hc j hj).1 h).elim
      · exact ((hc j hj).2.1 h).elim
      · exact ((hc j hj).2.2 h).elim
      · exact h
    have hins : P (insert i S) := by
      intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with rfl | haS
      · rcases Finset.mem_insert.mp hb with rfl | hbS
        · exact (hab rfl).elim
        · exact ho b hbS
      · rcases Finset.mem_insert.mp hb with rfl | hbS
        · exact eisensteinHermitian_zero_symm (ho a haS)
        · exact hS a haS b hbS hab
    have hle := hmax (insert i S) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hins⟩)
    rw [Finset.card_insert_of_notMem hi] at hle
    omega
  let F : S × Fin 3 → EisensteinRationalCoordinates := fun p =>
    if p.2 = 0 then v p.1.val else if p.2 = 1 then eisensteinRotation (v p.1.val)
    else eisensteinRotation (eisensteinRotation (v p.1.val))
  have hsubset : Finset.univ.image v ⊆ Finset.univ.image F := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨j, hj, he | he | he⟩ := hcover i
    · exact Finset.mem_image.mpr ⟨(⟨j, hj⟩, 0), Finset.mem_univ _, by simpa [F] using he.symm⟩
    · exact Finset.mem_image.mpr ⟨(⟨j, hj⟩, 1), Finset.mem_univ _, by simpa [F] using he.symm⟩
    · exact Finset.mem_image.mpr ⟨(⟨j, hj⟩, 2), Finset.mem_univ _, by simpa [F] using he.symm⟩
  have hc := (Finset.card_le_card hsubset).trans (Finset.card_image_le (f := F))
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Finset.card_univ] at hc
  simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin] at hc
  omega

end Atlas.Lattices
