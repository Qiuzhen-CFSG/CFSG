module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.OrdinaryGeometry.Pair.Cubic.Images
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.OrdinaryGeometry.Pair.Cubic.Model

/-!
# Simultaneous recognition of the original seven-letter cubic images

The image contains A₇ and is therefore A₇ or S₇. Its common Sylow is
conjugated to the corresponding checked model. The fixed-Sylow calculation
recognizes both subgroup images, and the composite conjugator transports
them simultaneously. Neither a faithful ambient action nor a partition
marking is assumed. This discharges the cubic-pair input of Pair.Source.

Source: Aschbacher--Smith, original14.6.10(5), printed p.1029.
-/

public section
open Subgroup

namespace CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry.Pair
open Cubic
universe u
-- After the fixed-Sylow calculation is built, only literal image transports occur here.
theorem cubicPairRecognition : CubicPairRecognition.{u} := by
  intro K _ _ A B h f hf
  obtain ⟨full,hfull⟩ := ambient_cases f.range hf
  let E : f.range ≃* ambient full := MulEquiv.subgroupCongr hfull
  let q : K →* ambient full := E.toMonoidHom.comp f.rangeRestrict
  have hq : Function.Surjective q := E.surjective.comp f.rangeRestrict_surjective
  have hqf (x : K) : (q x : Perm7) = f x := rfl
  have hn : ¬ Group.IsSolvable (ambient full) := by
    intro hs
    let := hs
    exact nonsolvable_range f hf
      (Group.isSolvable_of_isSolvable_injective (f := E.toMonoidHom) E.injective)
  obtain ⟨S,hSA,hSB,hiA,hiB,hAB⟩ := ChapterF.pair_image_cubic_data h q hq hn
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (ambient full) S (sylow full)
  let c : ambient full →* Perm7 := (ambient full).subtype.comp (MulAut.conj g).toMonoidHom
  let A' := (A.map q).map c
  let B' := (B.map q).map c
  have hc : Function.Injective c := Subtype.val_injective.comp (MulAut.conj g).injective
  have hcr : c.range = ambient full := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr (MulAut.conj g).surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  have hS : (S : Subgroup (ambient full)).map c = sylowGroup full := by
    have hh : (S : Subgroup (ambient full)).map (MulAut.conj g).toMonoidHom =
        (sylow full : Subgroup (ambient full)) := congrArg Sylow.toSubgroup hg
    rw [show c = (ambient full).subtype.comp (MulAut.conj g).toMonoidHom from rfl,
      ←map_map,hh,sylow_map]
  have hcard (D : Subgroup (ambient full))
      (hSD : (S : Subgroup (ambient full)) ≤ D) (hi : (S : Subgroup (ambient full)).relIndex D = 3) :
      Nat.card (D.map c) = 3 * (if full then 16 else 8) := by
    have hh := ((S : Subgroup (ambient full)).subgroupOf D).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hSD).toEquiv] at hh
    change Nat.card S * (S : Subgroup (ambient full)).relIndex D = Nat.card D at hh
    have hs : Nat.card S = if full then 16 else 8 := by
      rw [←card_map_of_injective hc (K := (S : Subgroup (ambient full))),hS,sylowGroup_card]
    rw [card_map_of_injective hc,←hh,hi,hs,Nat.mul_comm]
  have hgen : alternatingGroup (Fin 7) ≤ A' ⊔ B' := by
    change alternatingGroup (Fin 7) ≤ (A.map q).map c ⊔ (B.map q).map c
    rw [←Subgroup.map_sup,hAB,←MonoidHom.range_eq_map,hcr]
    exact hfull ▸ hf
  have hpair := fixed_pair full A' B'
    ((map_le_range _ _).trans hcr.le) ((map_le_range _ _).trans hcr.le)
    (hS ▸ map_mono hSA) (hS ▸ map_mono hSB)
    (hcard _ hSA hiA) (hcard _ hSB hiB) hgen
  -- Compose the Sylow conjugator and the common partition relabelling.
  let f' : K →* Perm7 := (MulAut.conj (relabelling * g.val)).toMonoidHom.comp f
  have hf' : f' = (MulAut.conj relabelling).toMonoidHom.comp (c.comp q) := by
    apply MonoidHom.ext
    intro x
    change (relabelling*g.val)*f x*(relabelling*g.val)⁻¹ =
      relabelling*(g.val*(q x).val*g.val⁻¹)*relabelling⁻¹
    rw [hqf]
    group
  have hr : f'.range = ambient full := by
    rw [hf',MonoidHom.range_comp,MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr hq,←MonoidHom.range_eq_map,hcr,map_ambient]
  refine ⟨relabelling*g.val,?_⟩
  change (A.map f' = f'.range ⊓ _ ∧ B.map f' = f'.range ⊓ _) ∨
    (A.map f' = f'.range ⊓ _ ∧ B.map f' = f'.range ⊓ _)
  rw [hr]
  simpa only [hf',←map_map] using hpair
end CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry.Pair
