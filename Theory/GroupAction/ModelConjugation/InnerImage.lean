module

public import Theory.GroupAction.ModelConjugation
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Transport and inverse images of inner actors

A group equivalence carries a subgroup's inner image and its stabilizing
actors to the corresponding images in the new model. For an ambient
conjugation action on a normalized subgroup K, the inverse image of the
inner actors from U is the embedded U joined with C_T(K). This follows
from the map/comap identity and the actual conjugation kernel; the action
need not be faithful and K need not be normal in the ambient group.

These identities support the model calculations in Aschbacher–Smith,
proof of 13.8.20, printed p.954.
-/

public section
open Subgroup
namespace Theory.GroupAction.ModelConjugation
variable {D K : Type*} [Group D] [Group K]

/-- Transport carries the full inner image of a subgroup to the inner image of its image. -/
theorem inner_image_congr (e : D ≃* K) (U : Subgroup D) :
    (U.map MulAut.conj).map (MulAut.congr e).toMonoidHom =
      (U.map e.toMonoidHom).map MulAut.conj := by
  rw [map_map, map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  exact MulAut.congr_conj e x

/-- A subgroup stabilized by an automorphism remains stabilized after transport. -/
theorem stable_map_congr (e : D ≃* K) (U : Subgroup D) (a : MulAut D)
    (ha : U.map a.toMonoidHom = U) :
    (U.map e.toMonoidHom).map (MulAut.congr e a).toMonoidHom = U.map e.toMonoidHom := by
  have hm : (MulAut.congr e a).toMonoidHom.comp e.toMonoidHom =
      e.toMonoidHom.comp a.toMonoidHom := by
    ext x
    simp [MulAut.congr]
  rw [map_map, hm, ← map_map, ha]

/-- An embedded subgroup contained in the actors has its inner image in the action range. -/
theorem inner_le_action_range {G D : Type*} [Group G] [Group D]
    (T K : Subgroup G) (hTK : T ≤ normalizer (K : Set G)) (e : K ≃* D)
    (U : Subgroup D) (hUT : U.map (K.subtype.comp e.symm.toMonoidHom) ≤ T) :
    U.map MulAut.conj ≤ (action T K hTK e).range := by
  rw [← inner_image T K hTK e U hUT]
  rintro a ⟨t, _, rfl⟩
  exact ⟨t, rfl⟩

/-- Lifting an inner image retains the entire ambient action kernel. -/
theorem action_mem_inner_iff {G D : Type*} [Group G] [Group D]
    (T K : Subgroup G) (hTK : T ≤ normalizer (K : Set G)) (e : K ≃* D)
    (U : Subgroup D) (hUT : U.map (K.subtype.comp e.symm.toMonoidHom) ≤ T) (t : T) :
    action T K hTK e t ∈ U.map MulAut.conj ↔
      (t : G) ∈ U.map (K.subtype.comp e.symm.toMonoidHom) ⊔
        (T ⊓ centralizer (K : Set G)) := by
  rw [← inner_image T K hTK e U hUT]
  change t ∈ (((U.map (K.subtype.comp e.symm.toMonoidHom)).subgroupOf T).map
    (action T K hTK e)).comap (action T K hTK e) ↔ _
  rw [comap_map_eq]
  have hm : ((U.map (K.subtype.comp e.symm.toMonoidHom)).subgroupOf T ⊔
      (action T K hTK e).ker).map T.subtype =
      U.map (K.subtype.comp e.symm.toMonoidHom) ⊔ (T ⊓ centralizer (K : Set G)) := by
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hUT, action_ker_map]
  rw [← hm]
  exact (mem_map_iff_mem T.subtype_injective).symm

end Theory.GroupAction.ModelConjugation
