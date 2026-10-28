module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.OriginalRestriction
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.MSPairs

/-!
# The original C.2.7 input supplies (MS3)

Transport each actual characteristic subgroup of `R` through the canonical
identification with `R ≤ KR`.  If it were normal in `KR`, its normalizer
would be the whole group, contradicting the original characteristic-normalizer
control in the proper intersection with `M`.  This discharges (MS3) in the
C.2.7 to C.1.32/34 reduction.  The parabolic (MS2) and quotient (MS1) fields
remain separate source obligations.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H K R M : Subgroup G}

theorem source_ms_characteristic (h : Input κ H R M K) : MSNoCharacteristicNormal K R := by
  intro C hC hn
  let _ := hC
  let J := K ⊔ R
  let R₀ := R.subgroupOf J
  let M₀ := (M ⊓ J).subgroupOf J
  let e : R ≃* R₀ := (subgroupOfEquivOfLe (show R ≤ J from le_sup_right)).symm
  let D := C.map e.toMonoidHom
  have hDC : D.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro a x hx
    obtain ⟨y,hy,rfl⟩ := hx
    refine ⟨(MulAut.congr e.symm a) y,
      characteristic_iff_le_comap.mp hC (MulAut.congr e.symm a) hy,?_⟩
    exact e.apply_symm_apply (a (e y))
  let _ := hDC
  have hDJ : D.map R₀.subtype = (C.map R.subtype).subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [map_subgroupOf_eq_of_le ((map_subtype_le C).trans (show R ≤ J from le_sup_right)),
      map_map,map_map]
    rfl
  have hproper : M₀ < ⊤ := lt_top_iff_ne_top.mpr (by
    intro ht
    exact h.outside (fun k hk => ((subgroupOf_eq_top.mp ht) (mem_sup_left hk)).1))
  by_contra hc
  have hd : D ≠ ⊥ := fun hd => hc ((C.map_eq_bot_iff_of_injective e.injective).mp hd)
  exact not_normal_of_characteristicNormalizerClosure_le R₀ M₀ hproper
    (source_join_input h).setup.characteristic_control D hd (hDJ.symm ▸ hn)

end CFSG.Quasithin.ChapterC.C27Source
