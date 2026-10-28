module

public import Theory.GroupTheory.CharacteristicNormalizerClosure

/-!
# Restricting characteristic-normalizer generation to a subgroup

A faithful embedding carries each characteristic subgroup to a characteristic
subgroup of the image and carries its normalizer into the corresponding
normalizer. Taking joins gives the same containment for C(G,R). Consequently
ambient control of C(G,R) restricts to C(H,R) whenever R ≤ H.

The transport argument also appears in the Section 15.4 local-setup development;
this independent extension makes it available without importing that later
source argument. Source: Aschbacher–Smith, combined manuscript (1 March 2004),
C.1.3 and the restriction used in 15.3.11(10), pp.122 and 1124.
-/

public section
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

private theorem characteristic_map_equivalence (e : G ≃* H)
    (C : Subgroup G) [C.Characteristic] : (C.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨(MulAut.congr e.symm a) y,
    characteristic_iff_le_comap.mp inferInstance (MulAut.congr e.symm a) hy, ?_⟩
  exact e.apply_symm_apply (a (e y))

/-- Faithful maps preserve containment in the characteristic-normalizer join. -/
theorem map_characteristicNormalizerClosure_le (f : G →* H)
    (hf : Function.Injective f) (R : Subgroup G) :
    R.characteristicNormalizerClosure.map f ≤ (R.map f).characteristicNormalizerClosure := by
  rw [characteristicNormalizerClosure, Subgroup.map_iSup]
  apply iSup_le
  intro C
  rw [Subgroup.map_iSup]
  apply iSup_le
  intro hC
  rw [Subgroup.map_iSup]
  apply iSup_le
  intro hCne
  let := hC
  let e := equivMapOfInjective R f hf
  let D := C.map e.toMonoidHom
  let : D.Characteristic := characteristic_map_equivalence e C
  have hDne : D ≠ ⊥ := fun h => hCne ((C.map_eq_bot_iff_of_injective e.injective).mp h)
  have he : (C.map R.subtype).map f = D.map (R.map f).subtype := by
    rw [map_map, map_map]
    rfl
  exact ((C.map R.subtype).le_normalizer_map f).trans
    (he ▸ normalizer_le_characteristicNormalizerClosure (R.map f) D hDne)

/-- Control of C(G,R) restricts to C(H,R), with characteristicness inside R. -/
theorem characteristicNormalizerClosure_subgroupOf_le {R H M : Subgroup G}
    (hRH : R ≤ H) (hc : R.characteristicNormalizerClosure ≤ M) :
    (R.subgroupOf H).characteristicNormalizerClosure ≤ M.subgroupOf H := by
  apply (map_le_iff_le_comap).mp
  have h := map_characteristicNormalizerClosure_le H.subtype H.subtype_injective (R.subgroupOf H)
  rw [map_subgroupOf_eq_of_le hRH] at h
  exact h.trans hc

end Subgroup
end
