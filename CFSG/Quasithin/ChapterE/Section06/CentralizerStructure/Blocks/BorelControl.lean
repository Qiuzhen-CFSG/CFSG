module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.SylowAction
public import Theory.GroupTheory.CharacteristicNormalizerClosure
public import Theory.GroupTheory.PGroup.CharacteristicPairReduction
public import Theory.GroupTheory.PGroup.OmegaCenterIn

/-!
# Central-Sylow control of a block's Sylow normalizer

Every ambient central involution acts on a block through an element of the
block's Sylow omega-center. Thus a block Sylow normalizer which fixes that
omega-center centralizes the original ambient omega-center. The latter is
nontrivial and characteristic in the ambient Sylow subgroup, so its normalizer
belongs to the original characteristic-normalizer closure.

Source: Aschbacher–Smith C.1.29, printed p.134, and the block action in
E.6.7, printed p.246. The original ambient group and Sylow are retained.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06
variable {G : Type*} [Group G] [Finite G]

theorem block_sylow_normalizer_le_characteristic_control
    (hf : generalizedFitting G = pCore 2 G) (S : Sylow 2 G)
    (hS : (S : Subgroup G) ≠ ⊥) (L : Subgroup G) (hL : ChapterC.IsBlock L)
    (P : Sylow 2 L) (hP : (P : Subgroup L).map L.subtype = L ⊓ S)
    (hc : normalizer (P : Set L) ≤
      centralizer (Stellmacher.omegaOneCenterAmbient (P : Subgroup L) : Set L)) :
    (normalizer (P : Set L)).map L.subtype ≤
      (S : Subgroup G).characteristicNormalizerClosure := by
  let V := Stellmacher.omegaOneCenterAmbient (S : Subgroup G)
  let : IsElementaryAbelian 2 V := Stellmacher.omegaOneCenterAmbient_elementaryAbelian _
  have hV : V ≤ (S : Subgroup G) ⊓ centralizer (S : Set G) := by
    intro v hv
    have hh := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hv
    exact ⟨hh.1, hh.2.2⟩
  have hact := (central_elementary_sylow_block_action hf S L hL V hV).2
  have hxC : (normalizer (P : Set L)).map L.subtype ≤ centralizer (V : Set G) := by
    rintro x ⟨l, hl, rfl⟩ v hv
    obtain ⟨z,hz,he⟩ := hact v hv
    rw [←hP, Stellmacher.omegaOneCenterAmbient_map_injective L.subtype L.subtype_injective] at hz
    obtain ⟨z,hz,rfl⟩ := hz
    have hzcomm : (z : G) * (l : G) = (l : G) * (z : G) :=
      congrArg Subtype.val (hc hl z hz)
    have hh := he l l.property
    change (z : G) * (l : G) * (z : G)⁻¹ = v * (l : G) * v⁻¹ at hh
    rw [hzcomm, mul_inv_cancel_right] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm)
  let D : Subgroup (S : Subgroup G) :=
    (omega₁ (center (S : Subgroup G)) (p := 2)).map (center (S : Subgroup G)).subtype
  let : (omega₁ (center (S : Subgroup G)) (p := 2)).Characteristic := omega₁_characteristic _
  let : D.Characteristic := inferInstance
  let : Nontrivial (S : Subgroup G) := (Subgroup.nontrivial_iff_ne_bot _).mpr hS
  have hD : D ≠ ⊥ := omega_center_ne_bot S.isPGroup'
  exact hxC.trans ((centralizer_le_normalizer (V : Set G)).trans
    (normalizer_le_characteristicNormalizerClosure (S : Subgroup G) D hD))

end CFSG.Quasithin.ChapterE.Section06
