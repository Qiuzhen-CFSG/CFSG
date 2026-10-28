module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.Source
public import Stellmacher.BaumannMap
public import Stellmacher.OmegaOneCenterMap
/-!
# The uniform pair on the actual ambient Baumann subgroup

Baumann heredity shows that the intrinsic Baumann operator fixes Baum(T).
The central involutions of a nontrivial two-group prove nontriviality.
The complete C.1.18 source therefore chooses one pair before all finite
marked targets. This supplies the literal base used by C.1.26 and C.1.28.

Source: Aschbacher–Smith B.2.3(4), C.1.18, printed pp.75,126.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB GlaubermanNiles
universe u v
variable {G : Type u} [Group G] [Finite G]

theorem baumann_fixed (T : Subgroup G) : IsBaumannFixed (baumann T) := by
  let B := baumann T
  apply map_injective B.subtype_injective
  change (baumann (⊤ : Subgroup B)).map B.subtype = (⊤ : Subgroup B).map B.subtype
  unfold baumann thompsonAlpha
  rw [baumann_map_injective B.subtype B.subtype_injective]
  have hm : (⊤ : Subgroup B).map B.subtype = B := by
    rw [←MonoidHom.range_eq_map,range_subtype]
  rw [hm]
  exact baumann_eq_of_intermediate T B le_rfl inf_le_left

theorem baumann_nontrivial (T : Subgroup G) (hp : IsPGroup 2 T) (hne : T ≠ ⊥) :
    Nontrivial (baumann T) := by
  let : Nontrivial T := (nontrivial_iff_ne_bot T).mpr hne
  have hZ : omegaOneCenterAmbient T ≠ ⊥ := by
    intro hz
    exact omega_center_ne_bot hp ((((omega₁ (center T) (p := 2)).map (center T).subtype).map_eq_bot_iff_of_injective T.subtype_injective).mp hz)
  apply (nontrivial_iff_ne_bot _).mpr
  intro hb
  apply hZ
  apply le_bot_iff.mp
  rw [←hb]
  intro z hz
  obtain ⟨hzT,_,hzc⟩ := (mem_omegaOneCenterAmbient_iff T z).mp hz
  refine ⟨hzT,?_⟩
  intro e he
  have heJ := ((mem_omegaOneCenterAmbient_iff (elementaryAbelianMaxJ T) e).mp he).1
  have hJT : elementaryAbelianMaxJ T ≤ T := sSup_le fun _ hA => hA.1
  exact hzc e (hJT heJ)

/-- One pair on the actual ambient Baumann subgroup works in every finite target. -/
theorem exists_baumann_universal_pair (T : Subgroup G)
    (hp : IsPGroup 2 T) (hne : T ≠ ⊥) :
    ∃ P : CharacteristicPair (baumann T), P.Universal.{u,v} := by
  let : Nontrivial (baumann T) := baumann_nontrivial T hp hne
  exact exists_universal_characteristicPair (hp.to_le inf_le_left) (baumann_fixed T)
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
