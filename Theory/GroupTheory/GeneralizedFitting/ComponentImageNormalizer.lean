module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Reflecting a surviving component's normalizer

Distinct components cannot have the same nontrivial homomorphic image.
Consequently an element normalizing a component's surviving image already
normalizes the original component. This is the lifting step in GLS2,
Theorem 26.24, Step 1.
-/

public section
open Subgroup
namespace Theory.GroupTheory
lemma IsComponent.mem_normalizer_of_mem_normalizer_map
    {G H : Type*} [Group G] [Group H] {L : Subgroup G}
    (hL : IsComponent G L) (f : G →* H) (hne : L.map f ≠ ⊥)
    {a : G} (ha : f a ∈ normalizer (L.map f : Set H)) :
    a ∈ normalizer (L : Set G) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply (hL.eq_of_map_eq (hL.map_conj a) f ?_ hne).symm
  have hm : (L.map (MulAut.conj a).toMonoidHom).map f =
      (L.map f).map (MulAut.conj (f a)).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply]
  rw [hm]
  exact (mem_normalizer_iff_map_conj_eq.mp ha).symm
end Theory.GroupTheory

