module
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Mathlib.GroupTheory.Index

/-!
# Conjugate spans with an index-two stabilizer

If an index-two subgroup of T normalizes U, the T-conjugate span of U
is U joined with its conjugate by any element of the other coset.
The same coset calculation says that the square of every element of T
normalizes U. These are the literal subgroup identities used in D.3.6.

Source: Aschbacher–Smith, D.3.6, printed p.196.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] (U T N : Subgroup G)

theorem componentOrbit_eq_sup_of_index_two
    (hi : N.relIndex T = 2) (hN : T ⊓ N ≤ normalizer (U : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ N) :
    componentOrbit U T = U ⊔ U.map (MulAut.conj t).toMonoidHom := by
  apply le_antisymm
  · apply iSup_le
    intro s
    by_cases hs : (s : G) ∈ N
    · have he : U.map (MulAut.conj (s : G)).toMonoidHom = U :=
        mem_normalizer_iff_map_conj_eq.mp (hN ⟨s.property,hs⟩)
      rw [he]
      exact le_sup_left
    · have hts : t⁻¹ * s ∈ N := by
        have hmem := (mul_mem_iff_of_index_two hi
          (a := (⟨t,ht⟩ : T)⁻¹) (b := s)).mpr
          (iff_of_false (by simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_inv,
            Subgroup.inv_mem_iff] using htn) hs)
        exact hmem
      have he : U.map (MulAut.conj (s : G)).toMonoidHom =
          U.map (MulAut.conj t).toMonoidHom := by
        calc
          _ = (U.map (MulAut.conj (t⁻¹ * s)).toMonoidHom).map
              (MulAut.conj t).toMonoidHom := by
            rw [map_map]
            congr 1
            ext x
            simp [MulAut.conj_apply, mul_assoc]
          _ = _ := congrArg (map (MulAut.conj t).toMonoidHom)
            (mem_normalizer_iff_map_conj_eq.mp
              (hN ⟨T.mul_mem (T.inv_mem ht) s.property,hts⟩))
      rw [he]
      exact le_sup_right
  · exact sup_le (le_componentOrbit U T)
      (le_iSup (fun s : T => U.map (MulAut.conj (s : G)).toMonoidHom) ⟨t,ht⟩)

theorem conjugate_twice_eq_of_index_two
    (hi : N.relIndex T = 2) (hN : T ⊓ N ≤ normalizer (U : Set G))
    {t : G} (ht : t ∈ T) :
    (U.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = U := by
  have ht2 : t * t ∈ N := mul_self_mem_of_index_two hi (⟨t,ht⟩ : T)
  calc
    _ = U.map (MulAut.conj (t*t)).toMonoidHom := by
      rw [map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    _ = U := mem_normalizer_iff_map_conj_eq.mp (hN ⟨T.mul_mem ht ht,ht2⟩)

end Theory.GroupTheory
