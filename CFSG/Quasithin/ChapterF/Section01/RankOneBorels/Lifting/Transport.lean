module

public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.QuotientGeometry

/-!
# Transport of the rank-one normalizer conclusions

Source: Aschbacher–Smith, printed pp.259–260, F.1.2–F.1.3(1).
These conditional lemmas transport the intrinsic conclusions along actual
multiplicative equivalences and embed them into the ambient group. In particular,
the normalizer inside L maps to L ∩ N_G(S ∩ L), and the intrinsic two-core
commutes with this embedding. No normality in the ambient group is asserted.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.Source
variable {G H : Type*} [Group G] [Group H]

/-- An injective homomorphism transports the embedded intrinsic two-core. -/
theorem twoCore_map_injective (A : Subgroup G) (f : G →* H)
    (hf : Function.Injective f) : twoCore (A.map f) = (twoCore A).map f := by
  let e := A.equivMapOfInjective f hf
  unfold twoCore
  rw [← pCore_map_iso 2 e, Subgroup.map_map, Subgroup.map_map]
  rfl

/-- Transport every rank-one normalizer conclusion to the actual image Sylow. -/
theorem rankOneSylowFacts_map [Finite G] (T : Sylow 2 G) (e : G ≃* H)
    (h : RankOneSylowFacts T) :
    RankOneSylowFacts (T.mapSurjective (f := e.toMonoidHom) e.surjective) := by
  have hn := Subgroup.map_equiv_normalizer_eq (T : Subgroup G) e
  change (Subgroup.normalizer (T : Set G)).map e.toMonoidHom =
    Subgroup.normalizer ((T.mapSurjective (f := e.toMonoidHom) e.surjective) : Set H) at hn
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hn]
    apply lt_top_iff_ne_top.mpr
    intro he
    apply h.proper.ne
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [he, Subgroup.map_top_of_surjective _ e.surjective]
  · intro M hTM hM
    rw [← hn, ← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective M]
    apply Subgroup.map_mono
    apply h.unique_maximal _ (Subgroup.map_le_iff_le_comap.mp hTM)
    apply lt_top_iff_ne_top.mpr
    intro he
    apply hM.ne
    rw [← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective M, he,
      Subgroup.map_top_of_surjective _ e.surjective]
  · rw [← hn, twoCore_map_injective _ _ e.injective, h.twoCore_eq]
    rfl
  · rw [← hn]
    let := h.solvable
    exact Group.isSolvable_of_surjective
      (MonoidHom.subgroupMap_surjective e.toMonoidHom _)
  · obtain ⟨D, hDN, hc, ha, hd, hs⟩ := h.abelian_odd_complement
    let := ha
    refine ⟨D.map e.toMonoidHom, ?_, ?_, inferInstance, ?_, ?_⟩
    · rw [← hn]; exact Subgroup.map_mono hDN
    · rwa [← Nat.card_congr (D.equivMapOfInjective e.toMonoidHom e.injective).toEquiv]
    · exact Subgroup.disjoint_map e.injective hd
    · exact (Subgroup.map_sup _ _ _).symm.trans ((congrArg (Subgroup.map e.toMonoidHom) hs).trans hn)

/-- Pull the normalizer conclusions back from an isomorphic finite model. -/
theorem rankOneSylowFacts_of_equiv [Finite G] (T : Sylow 2 G) (e : G ≃* H)
    (h : RankOneSylowFacts (T.mapSurjective (f := e.toMonoidHom) e.surjective)) : RankOneSylowFacts T := by
  let : Finite H := Finite.of_surjective e e.surjective
  have hh := rankOneSylowFacts_map _ e.symm h
  have he : (T.mapSurjective (f := e.toMonoidHom) e.surjective).mapSurjective
      (f := e.symm.toMonoidHom) e.symm.surjective = T := by
    apply Sylow.ext
    change ((T : Subgroup G).map e.toMonoidHom).map e.symm.toMonoidHom = _
    rw [Subgroup.map_map]
    simp
  exact he ▸ hh

/-- Embed the intrinsic conclusions into G using the specified local Sylow. -/
theorem rankOneBorelFacts_of_sylow (L S : Subgroup G) (T : Sylow 2 L)
    (hT : (T : Subgroup L).map L.subtype = S ⊓ L) (h : RankOneSylowFacts T) :
    RankOneBorelFacts L S := by
  have hn : (Subgroup.normalizer (T : Set L)).map L.subtype = borel L S := by
    have hc : (S ⊓ L).subgroupOf L = (T : Subgroup L) := by
      rw [← hT]; exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
    change (Subgroup.normalizer ((T : Subgroup L) : Set L)).map L.subtype = _
    rw [← hc, ← Subgroup.subgroupOf_normalizer_eq inf_le_right,
      Subgroup.subgroupOf, Subgroup.map_comap_eq, Subgroup.range_subtype]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hn]
    refine lt_of_le_of_ne (Subgroup.map_subtype_le _) ?_
    intro he
    apply h.proper.ne
    apply Subgroup.map_injective L.subtype_injective
    simpa only [← MonoidHom.range_eq_map, Subgroup.range_subtype] using he
  · intro M hSM hML
    rw [← hn, ← Subgroup.map_subgroupOf_eq_of_le hML.le]
    apply Subgroup.map_mono
    apply h.unique_maximal
    · apply (Subgroup.map_le_map_iff_of_injective L.subtype_injective).mp
      rwa [hT, Subgroup.map_subgroupOf_eq_of_le hML.le]
    · apply lt_top_iff_ne_top.mpr
      intro he
      apply hML.ne
      rw [← Subgroup.map_subgroupOf_eq_of_le hML.le, he]
      exact (MonoidHom.range_eq_map L.subtype).symm.trans L.range_subtype
  · rw [← hn, twoCore_map_injective _ _ L.subtype_injective, h.twoCore_eq, hT]
  · rw [← hn]
    let := h.solvable
    exact Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective _ _)
  · obtain ⟨D, hDN, hc, ha, hd, hs⟩ := h.abelian_odd_complement
    let := ha
    refine ⟨D.map L.subtype, ?_, ?_, inferInstance, ?_, ?_⟩
    · rw [← hn]; exact Subgroup.map_mono hDN
    · rwa [← Nat.card_congr (D.equivMapOfInjective L.subtype L.subtype_injective).toEquiv]
    · rw [← hT]; exact Subgroup.disjoint_map L.subtype_injective hd
    · rw [← hT, ← Subgroup.map_sup, hs, hn]
end CFSG.Quasithin.ChapterF.Source
