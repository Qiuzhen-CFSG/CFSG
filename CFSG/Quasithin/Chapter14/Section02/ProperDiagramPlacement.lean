module
public import Theory.GroupTheory.CComponent.ImageInOvergroup
public import CFSG.Quasithin.Chapter14.Section02.ComponentPlacement
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramCharacteristic

/-!
# The quotient comparison needed for diagram-component placement

Original 1.2.4 already supplies the unique normal C-component of Mc
containing the selected normal component K of H. The remaining embedding
screen need only show equality of their literal images in Mc/O₂(Mc).
Since O₂(Mc) lies in the original Sylow T and hence in H, equal images
put the containing component inside H, where comparable C-components
coincide. The diagram consumer below keeps this source embedding screen
explicit; it does not claim to prove it from a moved-subgroup hypothesis.

Source: Aschbacher--Smith 14.2.9 and 1.2.8(3)--(4), printed pp.983,506--507.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

theorem source_outside_component_eq_of_twoCore_images
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K : Subgroup H) (hK : K.IsCComponent)
    (D : Subgroup G) (hD : D ∈ Chapter1.cComponentsIn Mc)
    (hKD : K.map H.subtype ≤ D)
    (himage : ((K.map H.subtype).subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc)) =
      (D.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) : K.map H.subtype = D := by
  have hHMc : H ≤ Mc :=
    ((source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2).trans
      (InitialSource.centralizer_le_partner T hu)
  have hTMc : (T : Subgroup G) ≤ Mc := hH.1.1.2.trans hHMc
  have hQH : Mc.pCoreIn 2 ≤ H := by
    have hh := pCoreIn_le_sylow Mc (T.subtype hTMc)
    change Mc.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf Mc).map Mc.subtype at hh
    rw [map_subgroupOf_eq_of_le hTMc] at hh
    exact hh.trans hH.1.1.2
  have hKa : ((K.map H.subtype).subgroupOf H).IsCComponent := by
    simpa only [subgroupOf, comap_map_eq_self_of_injective H.subtype_injective] using hK
  exact cComponent_eq_of_equal_images_of_kernel_le Mc H (K.map H.subtype) D
    (QuotientGroup.mk' (pCore 2 Mc)) hHMc (map_subtype_le K) hD.1 hKD hKa hD.2
    (by simpa only [QuotientGroup.ker_mk', pCoreIn] using hQH) himage

theorem source_diagram_component_placement_of_twoCore_images
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (_hn : 1 < generationParameter H)
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (_hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (_hgen : K ⊔ (T.subtype hH.1.1.2 : Subgroup H) = ⊤) {f : ℕ} (_hf : 1 < f)
    (_hm : DiagramModel ((H ⊓ M).subgroupOf H) K (T.subtype hH.1.1.2 : Subgroup H) f)
    (himage : ∀ D : Subgroup G, D ∈ Chapter1.cComponentsIn Mc →
      K.map H.subtype ≤ D → (D.subgroupOf Mc).Normal →
      ((K.map H.subtype).subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc)) =
        (D.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) :
    K.map H.subtype ∈ Chapter1.cComponentsIn Mc ∧
      ((K.map H.subtype).subgroupOf Mc).Normal := by
  obtain ⟨D,hD,hKD,_,_,_,_,hnD⟩ :=
    source_outside_component_placement hG T hempty hM hu hmany hcard e H hH K hK
  have hHN : H ≤ normalizer (K.map H.subtype : Set G) := by
    have hh := K.le_normalizer_map H.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hnormal : (D.subgroupOf Mc).Normal := hnD (hH.1.1.2.trans hHN)
  have he := source_outside_component_eq_of_twoCore_images hG T hempty hM hu hmany
    hcard e H hH K hK D hD hKD (himage D hD hKD hnormal)
  exact he.symm ▸ ⟨hD,hnormal⟩
end CFSG.Quasithin.Chapter14.Section02
