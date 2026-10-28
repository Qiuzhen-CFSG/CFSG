module
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Normalizers of embedded characteristic subgroups

An injective homomorphism transports a characteristic subgroup to a
characteristic subgroup of its actual image. Thus every ambient normalizer
of the image normalizes the embedded characteristic subgroup.

This supplies the literal Sylow-image transport in the MS93 (5.1) Niles
application, without assuming that the ambient group itself is finite.
-/

@[expose] public section
open Subgroup
namespace Subgroup
variable {P G : Type*} [Group P] [Group G]
theorem normalizer_le_normalizer_characteristic_map
    (C : Subgroup P) (F : Subgroup C) [F.Characteristic]
    (i : P →* G) (hi : Function.Injective i) :
    normalizer (C.map i : Set G) ≤ normalizer ((F.map C.subtype).map i : Set G) := by
  let e := C.equivMapOfInjective i hi
  let K := F.map e.toMonoidHom
  have hK : K.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro a x hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨(MulAut.congr e.symm a) y,
      characteristic_iff_le_comap.mp inferInstance (MulAut.congr e.symm a) hy, ?_⟩
    exact e.apply_symm_apply (a (e y))
  have he : (F.map C.subtype).map i = K.map (C.map i).subtype := by
    rw [map_map, map_map]
    rfl
  rw [he]
  exact normalizer_le_normalizer_characteristic_image (C.map i) K
end Subgroup

