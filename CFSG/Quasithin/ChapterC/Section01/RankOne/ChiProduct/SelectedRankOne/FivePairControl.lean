module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.BlockSelection
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.ExternalPair
public import Theory.GroupTheory.PGroup.CharacteristicPairReduction
/-!
# Characteristic-normalizer control of the original first pair member

C₁(T) is the center restriction of the pair chosen on Baum(T). Transport
the pair to the intrinsic Baumann subgroup of T and apply C.1.19. This
retains both nontriviality and characteristicity of the restricted subgroup,
so its actual ambient normalizer lies in C(G,T).

Source: Aschbacher–Smith C.1.19–20 and C.1.26, pp.126–127,132.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB GlaubermanNiles FiveBlockSource
variable {G : Type*} [Group G] [Finite G]

/-- The original C₁(T), with the center restriction retained, has its
normalizer in the actual characteristic-normalizer control subgroup. -/
theorem firstAmbient_normalizer_le_control (T : Subgroup G) (hp : IsPGroup 2 T)
    (D : CharacteristicPair (baumann T)) :
    normalizer (firstAmbient T D : Set G) ≤ T.characteristicNormalizerClosure := by
  let B := (baumann T).subgroupOf T
  have hB : B = baumann (⊤ : Subgroup T) := by
    apply map_injective T.subtype_injective
    rw [map_subgroupOf_eq_of_le (show baumann T ≤ T from inf_le_left)]
    symm
    change ((⊤ : Subgroup T) ⊓ centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (⊤ : Subgroup T)) : Set T)).map T.subtype = _
    rw [baumann_map_injective T.subtype T.subtype_injective,
      ←MonoidHom.range_eq_map,range_subtype]
    rfl
  let : B.Characteristic := hB ▸ baumann_characteristic
  let a : baumann T ≃* B := (subgroupOfEquivOfLe (show baumann T ≤ T from inf_le_left)).symm
  let E := transportPair D a
  let : E.first.Characteristic := E.first_characteristic
  have hc := centerRestriction_spec hp B E.first E.first_ne_bot E.first_le_omegaCenter
  let : (centerRestriction B E.first).Characteristic := hc.1
  have hm : (centerRestriction B E.first).map T.subtype = firstAmbient T D := by
    change (center T ⊓ E.first.map B.subtype).map T.subtype = _
    rw [Subgroup.map_inf _ _ _ T.subtype_injective,map_map]
    change (center T).map T.subtype ⊓ (D.first.map a.toMonoidHom).map _ = _
    rw [map_map]
    rfl
  rw [←hm]
  exact normalizer_le_characteristicNormalizerClosure T _ hc.2.1
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
