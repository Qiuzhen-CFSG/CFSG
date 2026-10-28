module
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.Representative.Basic
public import Theory.Mathieu.M23.QuasithinGeometry.Design

/-!
# The Fano plane determined by an M23 involution

The t-invariant heptads meeting the fixed heptad in three points induce seven
lines. Finite incidence certificates identify those lines explicitly. Since
centralizing permutations preserve both t-invariance and the fixed heptad,
the centralizer acts on this concrete Fano plane.

This supplies the fixed-point geometry for the involution centralizer in
Aschbacher--Smith, *The Classification of Quasithin Groups*, Lemma 5.2.21,
printed p.657 (PDF p.674). All incidence checks use the existing W23 blocks.
-/

namespace Sporadic.Mathieu.M23Geometry
open scoped Pointwise
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

@[expose] public def involutionLines : Finset (Finset (Fin 23)) :=
  {{1,2,5}, {1,3,4}, {1,11,17}, {2,3,17}, {2,4,11}, {3,5,11}, {4,5,17}}

private theorem invariant_block_inter (i : Fin 253)
    (hi : involutionPerm • m23BlockAt i = m23BlockAt i)
    (hcard : (m23BlockAt i ∩ involutionHeptad).card = 3) :
    m23BlockAt i ∩ involutionHeptad ∈ involutionLines := by
  have h : ∀ i : Fin 253,
      involutionPerm • m23BlockAt i = m23BlockAt i →
      (m23BlockAt i ∩ involutionHeptad).card = 3 →
      m23BlockAt i ∩ involutionHeptad ∈ involutionLines := by
    decide +kernel
  exact h i hi hcard

private theorem block_mem (i : Fin 253) : m23BlockAt i ∈ m23Blocks :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

public theorem mem_involutionLines_iff (L : Finset (Fin 23)) :
    L ∈ involutionLines ↔ ∃ B ∈ m23Blocks,
      involutionPerm • B = B ∧ (B ∩ involutionHeptad).card = 3 ∧
      B ∩ involutionHeptad = L := by
  constructor
  · intro hL
    simp only [involutionLines, Finset.mem_insert, Finset.mem_singleton] at hL
    rcases hL with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨m23BlockAt 9, block_mem 9, by decide +kernel, by decide +kernel, by decide +kernel⟩
    · exact ⟨m23BlockAt 21, block_mem 21, by decide +kernel, by decide +kernel, by decide +kernel⟩
    · exact ⟨m23BlockAt 58, block_mem 58, by decide +kernel, by decide +kernel, by decide +kernel⟩
    · exact ⟨m23BlockAt 85, block_mem 85, by decide +kernel, by decide +kernel, by decide +kernel⟩
    · exact ⟨m23BlockAt 97, block_mem 97, by decide +kernel, by decide +kernel, by decide +kernel⟩
    · exact ⟨m23BlockAt 145, block_mem 145, by decide +kernel, by decide +kernel, by decide +kernel⟩
    · exact ⟨m23BlockAt 173, block_mem 173, by decide +kernel, by decide +kernel, by decide +kernel⟩
  · rintro ⟨B, hB, hi, hc, rfl⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hB
    exact invariant_block_inter i hi hc

public theorem centralizer_preserves_involutionLines (g : M23)
    (hg : g ∈ Subgroup.centralizer ({involutionRepresentative} : Set M23)) :
    g • involutionLines = involutionLines := by
  have hc := congrArg M23.subtype (Subgroup.mem_centralizer_singleton_iff.mp hg)
  simp only [map_mul, Subgroup.subtype_apply, involutionRepresentative_coe] at hc
  have hF : (g : Equiv.Perm (Fin 23)) • involutionHeptad = involutionHeptad :=
    centralizer_preserves_involutionHeptad g hg
  apply Finset.eq_of_subset_of_card_le
  · intro L hL
    obtain ⟨K, hK, rfl⟩ := Finset.mem_smul_finset.mp hL
    obtain ⟨B, hB, ht, hcard, rfl⟩ := (mem_involutionLines_iff K).mp hK
    apply (mem_involutionLines_iff _).mpr
    refine ⟨g • B, smul_heptad g hB, ?_, ?_, ?_⟩
    · change involutionPerm • ((g : Equiv.Perm (Fin 23)) • B) =
        (g : Equiv.Perm (Fin 23)) • B
      rw [← mul_smul, ← hc, mul_smul, ht]
    · have he : ((g : Equiv.Perm (Fin 23)) • B) ∩ involutionHeptad =
          (g : Equiv.Perm (Fin 23)) • (B ∩ involutionHeptad) := by
        rw [Finset.smul_finset_inter, hF]
      change (((g : Equiv.Perm (Fin 23)) • B) ∩ involutionHeptad).card = 3
      rw [he, Finset.card_smul_finset, hcard]
    · change ((g : Equiv.Perm (Fin 23)) • B) ∩ involutionHeptad =
        (g : Equiv.Perm (Fin 23)) • (B ∩ involutionHeptad)
      rw [Finset.smul_finset_inter, hF]
  · simp

end Sporadic.Mathieu.M23Geometry
