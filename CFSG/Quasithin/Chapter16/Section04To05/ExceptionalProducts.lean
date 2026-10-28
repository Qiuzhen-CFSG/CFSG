module

public import CFSG.Quasithin.Chapter16.Section04To05.Terminal
public import Theory.GroupTheory.CharacteristicCentralizerSylow
public import Theory.AtlasPort.LinearGroups.G2.ShortRootProducts.CoreReduction

/-!
# Exceptional conjugate-product interfaces for the final contradiction

The intrinsic residual and both choices of W are defined in
`Theory.GroupTheory.CentralizerResidualProducts`. Here intrinsic Sylow
centrality is identified with centrality inside the ambient subgroup L,
and characteristicity supplies the normalizer containment needed by
`Intersections.projected_product_eq_one_of_mem`.

For G₂ the explicit octonion calculations construct the product and prove
its long-root class and two-centrality. The remaining structural premise
in `g2_products_of_rootC_core` is the exact identification of the residual's
two-core with the concrete long-root plane. It is kept explicit: this
module does not yet complete the three exceptional cases. The Ree and
genuine graph-field triality cases still require their marked intrinsic
commutator-subgroup and product calculations.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), printed pp.1202–1203, the final three
cases before Theorem 16.5.14. Conjugation here is left conjugation.
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter16.Intersections.ExceptionalProducts

variable {G : Type*} [Group G]

theorem isTwoCentralIn_iff (L : Subgroup G) (v : L) :
    IsTwoCentralIn L (v : G) ↔ IsSylowCentralInvolution v := by
  constructor
  · rintro ⟨ho, S, ⟨T, hT⟩, hv, hc⟩
    refine ⟨?_, T, ?_, ?_⟩
    · simpa only [orderOf_submonoid] using ho
    · rw [← hT] at hv
      obtain ⟨w, hw, he⟩ := hv
      have h : w = v := Subtype.ext he
      exact h ▸ hw
    · intro x hx
      apply mem_centralizer_singleton_iff.mpr
      apply Subtype.ext
      exact mem_centralizer_singleton_iff.mp (hc (hT ▸ mem_map_of_mem L.subtype hx))
  · rintro ⟨ho, T, hv, hc⟩
    refine ⟨?_, (T : Subgroup L).map L.subtype, ⟨T, rfl⟩,
      mem_map_of_mem L.subtype hv, ?_⟩
    · simpa only [orderOf_submonoid] using ho
    · rintro _ ⟨w, hw, rfl⟩
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp (hc hw)))

theorem normalizer_core (L : Subgroup G) (v : L) :
    normalizer ((centralizerTwoResidual v).map L.subtype : Set G) ≤
      normalizer ((centralizerResidualCore v).map L.subtype : Set G) :=
  normalizer_le_normalizer_characteristic_map L.subtype L.subtype_injective
    (centralizerTwoResidual v) (pCore 2 (centralizerTwoResidual v))

theorem normalizer_commutator (L : Subgroup G) (v : L) :
    normalizer ((centralizerTwoResidual v).map L.subtype : Set G) ≤
      normalizer ((centralizerResidualCommutator v).map L.subtype : Set G) :=
  normalizer_le_normalizer_characteristic_map L.subtype L.subtype_injective
    (centralizerTwoResidual v) (centerCoreCommutator (centralizerTwoResidual v))

theorem g2_products_of_rootC_core
    {F L : Type*} [Field F] [CharP F 2] [Finite F] [Group L]
    (hcore : ∀ a : F, a ≠ 0 →
      centralizerResidualCore (Atlas.G2.rootC a) = Atlas.G2.longRootLocal)
    (e : L ≃* Atlas.G2.Model F) {v : L}
    (hv : Atlas.G2.ShortRootProducts.IsShortRootElement (e v)) :
    (∀ w ∈ centralizerResidualCore v, w ≠ 1 →
      Atlas.G2.ShortRootProducts.IsLongRootElement (e w) ∧ IsSylowCentralInvolution w) ∧
    ∃ l : L, v * MulAut.conj l v ≠ 1 ∧ v * MulAut.conj l v ∈ centralizerResidualCore v := by
  let : Finite L := Finite.of_injective e e.injective
  obtain ⟨hW, l, hne, hl⟩ := Atlas.G2.ShortRootProducts.core_products_of_rootC_core hcore hv
  constructor
  · intro w hw hwne
    have hmem : e w ∈ centralizerResidualCore (e v) := by
      rw [← map_centralizerResidualCore e v]
      exact mem_map_of_mem e.toMonoidHom hw
    have hneq : e w ≠ 1 := by
      intro h
      exact hwne (e.injective (h.trans e.map_one.symm))
    obtain ⟨hr, hc⟩ := hW _ hmem hneq
    refine ⟨hr, ?_⟩
    simpa only [e.symm_apply_apply] using hc.map e.symm
  · have he : e (v * MulAut.conj (e.symm l) v) = e v * MulAut.conj l (e v) := by
      simp [MulAut.conj_apply]
    refine ⟨e.symm l, ?_, ?_⟩
    · intro h
      apply hne
      rw [← he, h, map_one]
    · have hmem : e (v * MulAut.conj (e.symm l) v) ∈
          (centralizerResidualCore v).map e.toMonoidHom := by
        rw [map_centralizerResidualCore, he]
        exact hl
      obtain ⟨w, hw, heq⟩ := hmem
      exact e.injective heq ▸ hw

end CFSG.Quasithin.Chapter16.Intersections.ExceptionalProducts
