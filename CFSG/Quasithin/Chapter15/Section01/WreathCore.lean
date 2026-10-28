module
public import CFSG.Quasithin.ChapterE.Section02.Structure.WreathCore
public import CFSG.Quasithin.Chapter15.Section01.MinimalParabolicSource
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# The original wreath intersection core normalizes its component

Original 15.1.9 identifies H ∩ M with the unique maximal subgroup above the
intrinsic Sylow of H. The actual symmetric-five wreath quotient therefore
puts O₂(H ∩ M) in the normalizer of every C-component of H. Its normal
Sylow containment gives O₂(H ∩ M) ≤ T ∩ N(K₁). The residual/Sylow
supplement identifies the literal subgroup XT in 15.2.4 with H ∩ M.

This supplies O₂(XT) ≤ S, where S = T ∩ N(K₁), for the original
Aschbacher--Smith 15.2.4 configuration, printed p.1106.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original intersection core normalizes each actual C-component. -/
theorem source_HStar_symmetricFive_wreath_intersection_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M H K1 : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))))
    (hK : K1 ∈ Chapter1.cComponentsIn H) :
    (H ⊓ M).pCoreIn 2 ≤ (T : Subgroup G) ⊓ normalizer (K1 : Set G) := by
  obtain ⟨e⟩ := he
  obtain ⟨_,hP,hmax,_,_⟩ := source_centralizing_minimalParabolic hG T hM hJ H hH
  have hTM : (T : Subgroup G) ≤ H ⊓ M := le_inf hH.1.1.2 hM.1.2
  refine le_inf ?_ ?_
  · have hh := pCoreIn_le_sylow (H ⊓ M) (T.subtype hTM)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM] using hh
  · have hmaxeq := ChapterB.minimalParabolicMax_unique (T.subtype hH.1.1.2) hP hmax
      (show ((T.subtype hH.1.1.2 : Sylow 2 H) : Subgroup H) ≤ (H ⊓ M).subgroupOf H from
        fun x hx => ⟨x.property,hM.1.2 hx⟩)
    have hn := ChapterE.Structure.minimalParabolicMax_core_normalizes_of_symmetricFive_wreath
      (T.subtype hH.1.1.2) hP e hK.2
    rw [← hmaxeq] at hn
    have hm := map_mono (f := H.subtype) hn
    rw [map_pCoreIn_of_injective 2 _ H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le (show H ⊓ M ≤ H from inf_le_left)] at hm
    exact hm.trans (by
      have hh := (K1.subgroupOf H).le_normalizer_map H.subtype
      rwa [map_subgroupOf_eq_of_le hK.1] at hh)

/-- The literal residual/Sylow join in 15.2.4 has its core inside S. -/
theorem source_HStar_symmetricFive_wreath_residual_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M H K1 : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))))
    (hK : K1 ∈ Chapter1.cComponentsIn H) :
    (((pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype) ⊔
      (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) ⊓ normalizer (K1 : Set G) := by
  have hTM : (T : Subgroup G) ≤ H ⊓ M := le_inf hH.1.1.2 hM.1.2
  have hs := congrArg (Subgroup.map (H ⊓ M).subtype)
    (pResidual_sup_sylow_eq_top (T.subtype hTM))
  rw [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM,
    ← MonoidHom.range_eq_map,range_subtype] at hs
  rw [hs]
  exact source_HStar_symmetricFive_wreath_intersection_core hG T hM hJ hH he hK
end CFSG.Quasithin.Chapter15.Section01
