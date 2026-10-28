module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.Setup
public import Stellmacher.BaumannMap
public import Stellmacher.BaumannNormalizer
/-!
# The canonical central and normal cases of C.1.23

If the original omega-center orbit centralizes L, the prescribed C₁(T)
is central in H=LR. If the original Baumann subgroup is normalized by H,
its prescribed characteristic subgroup C₂(T) is normal in H. This includes
the literal Baumann-of-the-core alternative of B.2.10. All source subgroup
maps remain in the common ambient group; T need not lie in H.
Source: Aschbacher–Smith C.1.23(1), printed pp.129–130.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
variable {A : Type*} [Group A]

theorem first_central_of_moved_eq_bot (T H L R : Subgroup A)
    (D : GlaubermanNiles.CharacteristicPair (ChapterB.baumann T))
    (hBR : ChapterB.baumann T ≤ R) (hRT : R ≤ T) (hRH : R ≤ H) (hLH : L ≤ H)
    (hprod : ∀ g ∈ H, ∃ l ∈ L, ∃ r ∈ R, l*r=g)
    (hzero : ⁅normalClosure ((omegaOneCenterAmbient T).subgroupOf H : Set H),L.subgroupOf H⁆ = ⊥) :
    firstAmbient T D ≤ (center H).map H.subtype := by
  intro x hx
  have hxZ := firstAmbient_le_omegaCenter T D hx
  have hxH : x ∈ H := hRH (hBR (omegaCenter_le_baumann T hxZ))
  refine ⟨⟨x,hxH⟩,mem_center_iff.mpr ?_,rfl⟩
  intro g
  obtain ⟨l,hl,r,hr,he⟩ := hprod g g.property
  have hxl : l*x=x*l := by
    have hc := commutator_eq_bot_iff_le_centralizer.mp hzero
    exact congrArg H.subtype ((hc (le_normalClosure (show (⟨x,hxH⟩ : H) ∈
      (omegaOneCenterAmbient T).subgroupOf H from hxZ))) ⟨l,hLH hl⟩ hl)
  have hxr : r*x=x*r := ((mem_omegaOneCenterAmbient_iff _ _).mp hxZ).2.2 r (hRT hr)
  apply Subtype.ext
  change (g:A)*x=x*g
  rw [←he,mul_assoc,hxr,←mul_assoc,hxl,mul_assoc]

theorem second_normal_of_baumann_normal (T H R : Subgroup A)
    (D : GlaubermanNiles.CharacteristicPair (ChapterB.baumann T))
    (hBR : ChapterB.baumann T ≤ R) (hRH : R ≤ H)
    (hn : H ≤ normalizer (ChapterB.baumann T : Set A)) :
    ((secondAmbient T D).subgroupOf H).Normal := by
  let : D.second.Characteristic := D.second_characteristic
  apply (normal_subgroupOf_iff_le_normalizer
    ((map_subtype_le D.second).trans (hBR.trans hRH))).mpr
  exact hn.trans (normalizer_le_normalizer_characteristic_image _ D.second)

theorem second_normal_of_core_baumann (T H R : Subgroup A)
    (D : GlaubermanNiles.CharacteristicPair (ChapterB.baumann T))
    (hBR : ChapterB.baumann T ≤ R) (hRH : R ≤ H)
    (he : ChapterB.baumann T = (ChapterB.baumann (pCore 2 H)).map H.subtype) :
    ((secondAmbient T D).subgroupOf H).Normal := by
  apply second_normal_of_baumann_normal T H R D hBR hRH
  rw [he]
  change H ≤ normalizer (((pCore 2 H) ⊓ centralizer
    (omegaOneCenterAmbient (elementaryAbelianMaxJ (pCore 2 H)) : Set H)).map H.subtype : Set A)
  rw [baumann_map_injective H.subtype H.subtype_injective]
  exact (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))).trans
    (normalizer_le_normalizer_baumann _)
end CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
