module

public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.Basic
public import Mathlib.Algebra.Group.Subgroup.Order

/-!
# Maximality of the two-four-point-block stabilizer

An element outside the partition stabilizer, or its inverse, splits an internal
pair. Conjugating its transposition gives a cross-block transposition. Internal
permutations then recover the middle adjacent transposition, so any larger
subgroup is S₈. Maximality lifts through the second projection of C₂ × S₈.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, the two maximal proper 2-locals used in the proof of
Lemma 2.5.26, printed p.569.
-/

public section

namespace Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
open Subgroup Equiv

private theorem internal_swap (a b : Fin 8) (h : a.val / 4 = b.val / 4) :
    swap a b ∈ fourStabilizer := by
  have ht : ∀ a b : Fin 8, a.val / 4 = b.val / 4 → swap a b ∈ fourStabilizer := by
    decide
  exact ht a b h

private def crossMover (a b : Fin 8) : S8 :=
  if a.val / 4 = 0 then swap a 3 * swap b 4 else swap b 3 * swap a 4

private theorem crossMover_spec (a b : Fin 8) (h : a.val / 4 ≠ b.val / 4) :
    crossMover a b ∈ fourStabilizer ∧
    crossMover a b * swap a b * (crossMover a b)⁻¹ = swap 3 4 := by
  have ht : ∀ a b : Fin 8, a.val / 4 ≠ b.val / 4 →
      crossMover a b ∈ fourStabilizer ∧
      crossMover a b * swap a b * (crossMover a b)⁻¹ = swap 3 4 := by
    decide
  exact ht a b h

private theorem top_of_cross_swap (K : Subgroup S8) (hK : fourStabilizer ≤ K)
    {a b : Fin 8} (hab : a.val / 4 ≠ b.val / 4) (hs : swap a b ∈ K) : K = ⊤ := by
  obtain ⟨hm, he⟩ := crossMover_spec a b hab
  have hm' := hK hm
  have hmid : swap (3 : Fin 8) 4 ∈ K := he ▸ K.mul_mem (K.mul_mem hm' hs) (K.inv_mem hm')
  have hgen := Subgroup.closure_eq_top_of_mclosure_eq_top
    (Equiv.Perm.mclosure_swap_castSucc_succ 7)
  rw [eq_top_iff, ← hgen, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact hK (by decide)
  · exact hK (by decide)
  · exact hK (by decide)
  · exact hmid
  · exact hK (by decide)
  · exact hK (by decide)
  · exact hK (by decide)

private theorem top_of_not_mem (K : Subgroup S8) (hK : fourStabilizer ≤ K)
    {g : S8} (hg : g ∈ K) (hout : g ∉ fourStabilizer) : K = ⊤ := by
  have hconj (q : S8) (hq : q ∈ K) (a b : Fin 8)
      (hab : a.val / 4 = b.val / 4) (him : (q a).val / 4 ≠ (q b).val / 4) : K = ⊤ := by
    apply top_of_cross_swap K hK him
    have hs := hK (internal_swap a b hab)
    have he : q * swap a b * q⁻¹ = swap (q a) (q b) := by
      rw [Equiv.mul_swap_eq_swap_mul, mul_inv_cancel_right]
    exact he ▸ K.mul_mem (K.mul_mem hq hs) (K.inv_mem hq)
  simp only [mem_fourStabilizer, not_forall] at hout
  obtain ⟨a, b, hab⟩ := hout
  by_cases h : a.val / 4 = b.val / 4
  · exact hconj g hg a b h (fun he => hab (iff_of_true he h))
  · have he : (g a).val / 4 = (g b).val / 4 := by
      by_contra he
      exact hab (iff_of_false he h)
    exact hconj g⁻¹ (K.inv_mem hg) (g a) (g b) he (by simpa using h)

/-- The stabilizer of the unordered partition `{0123,4567}` is maximal in S₈. -/
theorem fourStabilizer_isCoatom : IsCoatom fourStabilizer := by
  refine ⟨?_, ?_⟩
  · intro he
    apply fourOvergroup_ne_top
    simp [fourOvergroup, he]
  · intro K hK
    obtain ⟨g, hg, hout⟩ := SetLike.exists_of_lt hK
    exact top_of_not_mem K hK.le hg hout

/-- The full inverse image of the block stabilizer is maximal in C₂ × S₈. -/
theorem fourOvergroup_isCoatom : IsCoatom fourOvergroup := by
  have he : fourOvergroup = fourStabilizer.comap (MonoidHom.snd C2 S8) := by
    ext g
    simp
  rw [he]
  exact Subgroup.isCoatom_comap_of_surjective (fun g => ⟨(1, g), rfl⟩)
    fourStabilizer_isCoatom

end Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
