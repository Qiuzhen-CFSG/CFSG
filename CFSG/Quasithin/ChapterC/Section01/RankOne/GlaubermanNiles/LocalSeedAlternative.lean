module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.ShortSeedPropagation
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.Source

/-!
# The original local seed and the characteristic-or-block alternative

Apply the now-proved uniform C.1.18 pair to the actual inclusion S ≤ H.
A normal image in H remains normal in the ambient group when H together
with N_G(S) generates it, because each chosen subgroup is characteristic
in S. In the block branch, the literal image of O²(H) is the short seed;
the preceding source propagation theorem constructs the ambient block.

Source: Aschbacher–Smith C.1.21(3), printed pp.128–129. The selected local
class and generation are the source geometric inputs, constructed for the
A₆ application in the accompanying SymmetricSix source family.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.GlaubermanArgument
open GlaubermanNiles
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem normal_characteristic_image_of_local
    (S H : Subgroup G) (hSH : S ≤ H) (D : Subgroup S) [D.Characteristic]
    (hn : (D.map (inclusion hSH)).Normal)
    (hgen : H ⊔ normalizer (S : Set G) = ⊤) : (D.map S.subtype).Normal := by
  let := hn
  have hH : H ≤ normalizer (D.map S.subtype : Set G) := by
    apply le_normalizer_iff.mpr
    intro h hh x hx
    obtain ⟨d,hd,rfl⟩ := hx
    have hd' : (inclusion hSH) d ∈ D.map (inclusion hSH) := mem_map_of_mem _ hd
    have hc := hn.conj_mem _ hd' (⟨h,hh⟩ : H)
    obtain ⟨z,hz,he⟩ := hc
    exact ⟨z,hz,congrArg Subtype.val he⟩
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [←hgen]
  exact sup_le hH (normalizer_le_normalizer_characteristic_image S D)

theorem local_seed_alternative
    (S H L : Subgroup G) (hSH : S ≤ H)
    (hlocal : InLocalClass (inclusion hSH))
    (D : CharacteristicPair S) (hD : D.Universal.{u,u})
    (hgen : H ⊔ normalizer (S : Set G) = ⊤)
    (hYL : (pResidual 2 H).map H.subtype ≤ L)
    (hL : L.IsSubnormal) (hpL : IsPPerfect 2 L)
    (hfL : generalizedFitting L = pCore 2 L) [IsQuasisimple (L ⧸ pCore 2 L)]
    (hQY : pCore 2 G ≤ normalizer ((pResidual 2 H).map H.subtype : Set G))
    (hne : ¬ (((pResidual 2 H).map H.subtype).subgroupOf L).map
      (QuotientGroup.mk' (pCore 2 L)) ≤ center (L ⧸ pCore 2 L)) :
    (∃ C : Subgroup S, C.Characteristic ∧ C ≠ ⊥ ∧ (C.map S.subtype).Normal) ∨ IsBlock L := by
  rcases hD H (inclusion hSH) hlocal with hc | hn | hb
  · left
    let := D.first_characteristic
    exact ⟨D.first,inferInstance,D.first_ne_bot,normal_characteristic_image_of_local S H hSH _
      ((hlocal.first_normal_iff_central D.first D.first_le_omegaCenter).mpr hc) hgen⟩
  · left
    let := D.second_characteristic
    exact ⟨D.second,inferInstance,D.second_ne_bot,
      normal_characteristic_image_of_local S H hSH _ hn hgen⟩
  · right
    have hY : IsShort ((pResidual 2 H).map H.subtype) :=
      hb.1.short.of_mulEquiv ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective)
    exact isBlock_of_short_seed _ L hYL hY hL hpL hfL hQY hne

theorem exists_normal_characteristic_or_block_of_local_seed
    (S H L : Subgroup G) [Nontrivial S] (hpS : IsPGroup 2 S) (hS : IsBaumannFixed S)
    (hSH : S ≤ H) (hlocal : InLocalClass (inclusion hSH))
    (hgen : H ⊔ normalizer (S : Set G) = ⊤)
    (hYL : (pResidual 2 H).map H.subtype ≤ L)
    (hL : L.IsSubnormal) (hpL : IsPPerfect 2 L)
    (hfL : generalizedFitting L = pCore 2 L) [IsQuasisimple (L ⧸ pCore 2 L)]
    (hQY : pCore 2 G ≤ normalizer ((pResidual 2 H).map H.subtype : Set G))
    (hne : ¬ (((pResidual 2 H).map H.subtype).subgroupOf L).map
      (QuotientGroup.mk' (pCore 2 L)) ≤ center (L ⧸ pCore 2 L)) :
    (∃ C : Subgroup S, C.Characteristic ∧ C ≠ ⊥ ∧ (C.map S.subtype).Normal) ∨ IsBlock L := by
  obtain ⟨D,hD⟩ := exists_universal_characteristicPair.{u,u} hpS hS
  exact local_seed_alternative S H L hSH hlocal D hD hgen hYL hL hpL hfL hQY hne
end CFSG.Quasithin.ChapterC.RankOne.GlaubermanArgument
