module
public import Theory.Representation.BinaryPermutation.SevenTriangle.Marking

/-!
# Generation from a seven-letter triangle plane

A binary plane whose nonzero vectors all have weight two consists of the
three edges of a triangle. The stabilizer of any one edge moves a second
edge through all remaining letters. These edges span the even-weight core.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
14.7.37(3), printed pp.1059–1060.
-/

public noncomputable section
namespace BinaryPermutation.SevenTriangle
open SevenParabolic
private theorem pair_permute (g : Equiv.Perm (Fin 7)) (i j : Fin 7) :
    action g (pair i j) = pair (g i) (g j) := by
  apply Subtype.ext
  funext a
  simp only [action,coreRepresentation_apply,representation_apply,pair,Pi.add_apply,Pi.single_apply]
  simp only [g.symm_apply_eq]

private theorem pair_star_sum (i : Fin 7) (v : Space) :
    ∑ j : Fin 7, v.val j • pair i j = v := by
  apply Subtype.ext
  change (∑ j : Fin 7, v.val j • (Pi.single i 1 + Pi.single j 1)) = v.val
  have hv : ∑ j : Fin 7, v.val j = 0 := (mem_core (Fin 7) v.val).mp v.property
  simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hv, zero_smul, zero_add]
  convert Finset.univ_sum_single v.val using 1
  apply Finset.sum_congr rfl
  intro j _
  ext a
  simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> simp

/-- The stabilizer of a nonzero vector in a pair plane generates the whole seven-letter core from that plane. -/
theorem point_stabilizer_generates
    (B S : Submodule (ZMod 2) Space) (hd : Module.finrank (ZMod 2) B = 2)
    (hw : ∀ v ∈ B, v ≠ 0 → weight v = 2)
    (u : Space) (hu : u ∈ B) (hu0 : u ≠ 0) (hBS : B ≤ S)
    (hs : ∀ g : Equiv.Perm (Fin 7), action g u = u →
      ∀ v ∈ S, action g v ∈ S) : S = ⊤ := by
  obtain ⟨i,j,k,hij,hik,hjk,rfl,hB⟩ := Marking.plane_basis_through B hd hw u hu hu0
  have hp : pair i j ∈ S := hBS hu
  have hq : pair i k ∈ S := hBS (hB ▸ Submodule.subset_span (by simp))
  have hall (l : Fin 7) : pair i l ∈ S := by
    by_cases hli : l = i
    · subst l
      have hz : pair i i = 0 := by apply Subtype.ext; exact ZModModule.add_self _
      rw [hz]; exact S.zero_mem
    by_cases hlj : l = j
    · subst l; exact hp
    let g := Equiv.swap k l
    have hgi : g i = i := Equiv.swap_apply_of_ne_of_ne hik (Ne.symm hli)
    have hgj : g j = j := Equiv.swap_apply_of_ne_of_ne hjk (Ne.symm hlj)
    have hfix : action g (pair i j) = pair i j := by rw [pair_permute,hgi,hgj]
    have hh := hs g hfix _ hq
    simpa only [pair_permute,hgi,g,Equiv.swap_apply_left] using hh
  apply top_unique
  intro v _
  rw [←pair_star_sum i v]
  exact S.sum_mem (fun j _ => S.smul_mem (v.val j) (hall j))
end BinaryPermutation.SevenTriangle

