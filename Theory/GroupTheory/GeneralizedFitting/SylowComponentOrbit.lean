module
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Mathlib.GroupTheory.Sylow

/-!
# Normality of a Sylow orbit of length at most two

If a subgroup is normal or has normalizer of index two, its Sylow-two
conjugate closure is normal. In the index-two case the Sylow group contains
an element in the nontrivial coset, so its orbit already includes every
ambient conjugate. This is the orbit step in Aschbacher–Smith 1.3.4, p.510.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem componentOrbit_normal_of_normal_or_index_two (B : Subgroup G) (S : Sylow 2 G)
    (hB : B.Normal ∨ (normalizer (B : Set G)).index = 2) :
    (componentOrbit B (S : Subgroup G)).Normal := by
  rcases hB with hn | hi
  · let := hn
    have he : componentOrbit B (S : Subgroup G) = B := by
      apply le_antisymm _ (le_componentOrbit B _)
      apply iSup_conjugates_le_of_le_normalizer B _ B le_rfl
      rw [normalizer_eq_top]
      exact le_top
    rw [he]
    exact hn
  · have hs : ¬ (S : Subgroup G) ≤ normalizer (B : Set G) := by
      intro hs
      have hd := index_dvd_of_le hs
      rw [hi] at hd
      exact S.not_dvd_index hd
    obtain ⟨s, hs, hsn⟩ := Set.not_subset.mp hs
    have hconj (g : G) : B.map (MulAut.conj g).toMonoidHom ≤
        componentOrbit B (S : Subgroup G) := by
      by_cases hg : g ∈ normalizer (B : Set G)
      · exact (show B.map (MulAut.conj g).toMonoidHom = B from
          mem_normalizer_iff_map_conj_eq.mp hg).le.trans (le_componentOrbit B _)
      have hsg : s⁻¹ * g ∈ normalizer (B : Set G) :=
        (mul_mem_iff_of_index_two hi).mpr (iff_of_false (by simpa using hsn) hg)
      have he : B.map (MulAut.conj g).toMonoidHom = B.map (MulAut.conj s).toMonoidHom := by
        calc
          _ = (B.map (MulAut.conj (s⁻¹ * g)).toMonoidHom).map
              (MulAut.conj s).toMonoidHom := by
            rw [map_map]
            congr 1
            ext x
            simp [MulAut.conj_apply, mul_assoc]
          _ = _ := congrArg (map (MulAut.conj s).toMonoidHom)
            (show B.map (MulAut.conj (s⁻¹ * g)).toMonoidHom = B from
              mem_normalizer_iff_map_conj_eq.mp hsg)
      rw [he]
      exact le_iSup (fun a : (S : Subgroup G) => B.map (MulAut.conj (a : G)).toMonoidHom) ⟨s, hs⟩
    have he : componentOrbit B (S : Subgroup G) = componentOrbit B ⊤ := by
      apply le_antisymm
      · apply iSup_le
        intro s
        exact le_iSup (fun a : (⊤ : Subgroup G) => B.map (MulAut.conj (a : G)).toMonoidHom)
          ⟨s, mem_top _⟩
      · exact iSup_le fun g => hconj g
    rw [he, ← normalizer_eq_top_iff]
    apply top_unique
    simpa only [sup_top_eq] using
      (normal_subgroupOf_iff_le_normalizer (componentOrbit_le_sup B ⊤)).mp
        (componentOrbit_normal_subgroupOf_sup B ⊤)

end Theory.GroupTheory
