module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.Marking

/-!
# Transport of the same universal characteristic pair

A group isomorphism carries both characteristic subgroups and the first
member's omega-center containment. Precomposing each marked local embedding
with this isomorphism preserves its local-class membership, so the universal
property transports for this same pair. No new pair is chosen.

This is the exact change of ambient subgroup used when a full Sylow subgroup
is viewed inside a selected minimal parabolic in C.1.28 and 14.1.11.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
universe u v w
variable {B : Type u} [Group B] {C : Type v} [Group C]

private theorem characteristic_map_equiv (e : B ≃* C) (A : Subgroup B)
    (ha : A.Characteristic) : (A.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_map_eq.mpr
  intro f
  have h := congrArg (Subgroup.map e.toMonoidHom)
    (characteristic_iff_map_eq.mp ha (e.trans (f.trans e.symm)))
  rw [Subgroup.map_map] at h ⊢
  convert h using 1
  congr 1
  ext x
  simp

/-- The transported pair consists of the images of the two original members. -/
@[expose] def CharacteristicPair.map (D : CharacteristicPair B) (e : B ≃* C) :
    CharacteristicPair C where
  first := D.first.map e.toMonoidHom
  second := D.second.map e.toMonoidHom
  first_characteristic := by exact characteristic_map_equiv e D.first D.first_characteristic
  second_characteristic := by exact characteristic_map_equiv e D.second D.second_characteristic
  first_ne_bot := fun he => D.first_ne_bot ((map_eq_bot_iff_of_injective _ e.injective).mp he)
  second_ne_bot := fun he => D.second_ne_bot ((map_eq_bot_iff_of_injective _ e.injective).mp he)
  first_le_omegaCenter := (map_mono D.first_le_omegaCenter).trans_eq (omegaCenter_map_equiv e)

/-- The universal marked theorem follows the same two subgroup images. -/
theorem CharacteristicPair.Universal.map {D : CharacteristicPair B}
    (hD : D.Universal.{u,w}) (e : B ≃* C) : (D.map e).Universal.{v,w} := by
  intro H _ _ f hf
  have h := hD H (f.comp e.toMonoidHom) (hf.precomp_equiv e)
  simpa only [CharacteristicPair.map,Alternatives,Subgroup.map_map] using h

end CFSG.Quasithin.ChapterC.GlaubermanNiles
