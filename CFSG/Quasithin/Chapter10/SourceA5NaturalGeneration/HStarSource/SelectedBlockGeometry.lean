module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SecondBlock.BothBlockGeometry
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport
/-!
# The same selected block after Hall conjugation

The paired H-star source places a cubic in the prescribed Hall subgroup by
conjugation in the original Sylow. Transport its containing natural block by
that very conjugation. The full core, trivial center and common Baumann Sylow
are preserved. Its generation with the original Sylow proves that this block
still escapes the original maximal local subgroup.

Source: Aschbacher--Smith 10.2.3(4), printed pp.746--747.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC ChapterB
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L H : Subgroup G}

/-- Keep the actual selected component while moving its cubic into the Hall. -/
theorem source_selected_block_ambient_conjugate
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (K : Subgroup H) (hgen : K ⊔ (T.subtype hH.1.1.2 : Subgroup H)=⊤)
    (geom : SourceBothBlockGeometry T L H hH.1.1.2 K)
    (s : H) (hs : s ∈ (T.subtype hH.1.1.2 : Subgroup H)) :
    let K' := (K.map H.subtype).map (MulAut.conj (s:G)).toMonoidHom
    IsL2EvenBlock K' 2 ∧ pCore 2 K'=blockU K' ∧ center K'=⊥ ∧
      Chapter1.IsSylowIn 2 (baumann (T : Subgroup G) ⊓ K') K' ∧
      baumann (T : Subgroup G) ≤ normalizer (K' : Set G) ∧
      ¬ K' ≤ D.maximalLocal := by
  let S := T.subtype hH.1.1.2
  let f := MulAut.conj (s:G)
  let K₀ := K.map H.subtype
  let K' := K₀.map f.toMonoidHom
  let a : K ≃* K' := (K.equivMapOfInjective H.subtype H.subtype_injective).trans
    (f.subgroupMap K₀)
  have hb : (baumann (S : Subgroup H)).map H.subtype = baumann (T : Subgroup G) := by
    have hh := baumann_map_injective H.subtype H.subtype_injective (S : Subgroup H)
    change (baumann (S : Subgroup H)).map H.subtype = baumann ((S : Subgroup H).map H.subtype) at hh
    rw [show (S : Subgroup H).map H.subtype=(T : Subgroup G) from
      map_subgroupOf_eq_of_le hH.1.1.2] at hh
    exact hh
  have hbf : (baumann (T : Subgroup G)).map f.toMonoidHom = baumann (T : Subgroup G) :=
    mem_normalizer_iff_map_conj_eq.mp
      (normalizer_le_normalizer_baumann _ ((T : Subgroup G).le_normalizer hs))
  have hc : pCore 2 K'=blockU K' := by
    rw [←pCore_map_iso 2 a,geom.selected_core,blockU,map_commutator,pCore_map_iso,
      map_top_of_surjective _ a.surjective,blockU]
  have hz : center K'=⊥ := by
    apply bot_unique
    intro k hk
    have hh := (centerCongr a.symm ⟨k,hk⟩).property
    change a.symm k ∈ center K at hh
    rw [geom.selected_center,mem_bot] at hh
    exact mem_bot.mpr (a.symm.injective (hh.trans a.symm.map_one.symm))
  have hSylow := Chapter1.Section02.IndexTwo.isSylowIn_map
    (Chapter1.Section02.IndexTwo.isSylowIn_map geom.selected_sylow H.subtype) f.toMonoidHom
  rw [map_inf _ _ _ H.subtype_injective,hb,map_inf _ _ _ f.injective,hbf] at hSylow
  have hN : baumann (T : Subgroup G) ≤ normalizer (K₀ : Set G) := by
    rw [←hb]
    exact (map_mono geom.baumann_normalizes_selected).trans (K.le_normalizer_map H.subtype)
  have hN' : baumann (T : Subgroup G) ≤ normalizer (K' : Set G) := by
    have hh := map_mono (f:=f.toMonoidHom) hN
    rwa [hbf,map_equiv_normalizer_eq] at hh
  have hout : ¬ K₀ ≤ D.maximalLocal := by
    intro hK
    apply hH.1.2
    have hh := congrArg (map H.subtype) hgen
    rw [Subgroup.map_sup,show (T.subtype hH.1.1.2 : Subgroup H).map H.subtype=
      (T : Subgroup G) from map_subgroupOf_eq_of_le hH.1.1.2,
      ←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh.symm.le.trans (sup_le hK (le_normalizer_componentOrbit L T))
  have hRf : (localOrbit T L).map f.toMonoidHom=localOrbit T L :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_componentOrbit L T hs)
  have hMf : D.maximalLocal.map f.toMonoidHom=D.maximalLocal := by
    change (normalizer (localOrbit T L : Set G)).map f.toMonoidHom = _
    rw [map_equiv_normalizer_eq,hRf]
  refine ⟨geom.selected_natural.of_mulEquiv a,hc,hz,hSylow,hN',?_⟩
  intro hK'
  apply hout
  exact (map_le_map_iff_of_injective f.injective).mp (hK'.trans_eq hMf.symm)
end CFSG.Quasithin.Chapter10
