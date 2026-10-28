module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.Marking
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed
/-!
# Transporting the preselected characteristic pair

A group isomorphism transports both original characteristic subgroups,
the omega-center containment, and the universal local-class property.
This changes only the literal subgroup carrier when the external Baumann
group is realized inside an overgroup; no new pair is selected.
Source: the common Baumann base in C.1.21–23, printed pp.127–130.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
open GlaubermanNiles
universe u v w
variable {B : Type u} {C : Type v} [Group B] [Group C]
private theorem characteristic_map_equiv (a : B ≃* C) (D : Subgroup B)
    [D.Characteristic] : (D.map a.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  rintro f x ⟨y,hy,rfl⟩
  refine ⟨(MulAut.congr a.symm f) y,
    characteristic_iff_le_comap.mp inferInstance (MulAut.congr a.symm f) hy,?_⟩
  exact a.apply_symm_apply _

/-- Transport one already chosen pair, retaining its original two subgroups. -/
@[expose] def transportPair (D : CharacteristicPair B) (a : B ≃* C) : CharacteristicPair C where
  first := D.first.map a.toMonoidHom
  second := D.second.map a.toMonoidHom
  first_characteristic := by
    let := D.first_characteristic
    exact characteristic_map_equiv a D.first
  second_characteristic := by
    let := D.second_characteristic
    exact characteristic_map_equiv a D.second
  first_ne_bot := fun h => D.first_ne_bot ((D.first.map_eq_bot_iff_of_injective a.injective).mp h)
  second_ne_bot := fun h => D.second_ne_bot ((D.second.map_eq_bot_iff_of_injective a.injective).mp h)
  first_le_omegaCenter := (map_mono D.first_le_omegaCenter).trans_eq (omegaCenter_map_equiv a)

/-- The same universal property survives a literal source-group marking. -/
theorem transportPair_universal (D : CharacteristicPair B) (hD : D.Universal.{u,w})
    (a : B ≃* C) : (transportPair D a).Universal.{v,w} := by
  intro H _ _ e he
  have ha := hD H (e.comp a.toMonoidHom) (he.precomp_equiv a)
  simpa only [Alternatives,transportPair,map_map] using ha
end CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
