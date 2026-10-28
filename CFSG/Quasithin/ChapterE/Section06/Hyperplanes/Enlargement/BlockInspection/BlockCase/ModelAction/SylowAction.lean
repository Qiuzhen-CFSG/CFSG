module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase.Contracts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase.ModelAction.CharacteristicTwo
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.Setup
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.SylowAction
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# The common-Sylow action of V on an actual block overgroup

Restrict the Sylow subgroup Q from the obstruction centralizer to a
characteristic-two intermediate group and then to the actual subnormal
block X. The intrinsic block-action theorem gives conjugating elements in
Ω₁(Z(X ∩ Q)); the subtype equivalences below preserve both this membership
and the literal conjugation equality in the original ambient group.

The final theorem uses CharacteristicTwo to construct the intermediate
join ⟨X,Q⟩. Thus the common-Sylow action needs no identification of X with
an E.6.7 factor, and no assertion that Q normalizes X.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.7,
printed p.246, as applied in E.6.23, printed p.254 (PDF pp.257 and 265).
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase
variable {G : Type*} [Group G] [Finite G]
variable {𝒦 : GroupClass} {T : Sylow 2 G} {M V A X J : Subgroup G}

/-- Restrict the common Sylow and transport the intrinsic inner-action
witnesses across the two subgroup inclusions, preserving literal conjugation. -/
theorem block_action_of_characteristicTwo_intermediate
    (h : HypothesisE61 𝒦 T M V) (hA : A ∈ obstructionFamily M V)
    (hX : CentralizerBlock A X)
    (hQJ : sylowCentralizer (T : Subgroup G) V ≤ J)
    (hXJ : X ≤ J) (hJA : J ≤ centralizer (A : Set G))
    (hJ : HasCharacteristicTwo J) :
    ∃ S : Sylow 2 X,
      (S : Subgroup X).map X.subtype = X ⊓ sylowCentralizer (T : Subgroup G) V ∧
      ∀ v ∈ V, ∃ z : X, z ∈ Stellmacher.omegaOneCenterAmbient (S : Subgroup X) ∧
        ∀ x : X, (z : G) * (x : G) * (z : G)⁻¹ = v * (x : G) * v⁻¹ := by
  let _ := h.elementary
  let Q := sylowCentralizer (T : Subgroup G) V
  obtain ⟨P, hP⟩ := h.sylow_obstructionIntermediate hA hQJ hJA
  have hp (x : J) : x ∈ (P : Subgroup J) ↔ (x : G) ∈ Q := by
    change x ∈ (P : Subgroup J) ↔ (x : G) ∈ sylowCentralizer (T : Subgroup G) V
    rw [← hP]
    exact (mem_map_iff_mem J.subtype_injective).symm
  have hshort : ChapterC.IsShort X := hX.2.short.of_mulEquiv (subgroupOfEquivOfLe hX.1)
  have hblock : ChapterC.IsBlock (X.subgroupOf J) :=
    ⟨inferInstance, hshort.of_mulEquiv (subgroupOfEquivOfLe hXJ).symm,
      hX.2.subnormal.comap (inclusion hJA)⟩
  have hVQ : V ≤ Q := by
    intro v hv
    refine ⟨h.le_sylow hv, mem_centralizer_iff.mpr ?_⟩
    intro w hw
    exact congrArg (fun y : V => (y : G)) (mul_comm (⟨w, hw⟩ : V) ⟨v, hv⟩)
  have hVJ : V ≤ J := hVQ.trans hQJ
  let _ : IsElementaryAbelian 2 (V.subgroupOf J) := IsElementaryAbelian.subgroupOf hVJ
  have hVP : V.subgroupOf J ≤ (P : Subgroup J) ⊓ centralizer (P : Set J) := by
    intro v hv
    refine ⟨(hp v).mpr (hVQ hv), ?_⟩
    apply mem_centralizer_iff.mpr
    intro p hpP
    apply Subtype.ext
    exact (mem_centralizer_iff.mp ((hp p).mp hpP).2 v hv).symm
  obtain ⟨R, hR⟩ := P.exists_subgroupOf_eq_of_subnormal (X.subgroupOf J) hblock.subnormal
  let e := subgroupOfEquivOfLe hXJ
  let S : Sylow 2 X := R.mapSurjective (f := e.toMonoidHom) e.surjective
  have hs (x : X) : x ∈ (S : Subgroup X) ↔ (x : G) ∈ Q := by
    change x ∈ (R : Subgroup (X.subgroupOf J)).map e.toMonoidHom ↔ _
    rw [hR]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hp y).mp hy
    · intro hx
      exact ⟨e.symm x, (hp _).mpr hx, e.apply_symm_apply x⟩
  refine ⟨S, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, (hs y).mp hy⟩
    · rintro ⟨hx, hq⟩
      exact ⟨⟨x, hx⟩, (hs _).mpr hq, rfl⟩
  · intro v hv
    obtain ⟨z, hz, he⟩ := (central_elementary_sylow_block_action
      (generalizedFitting_eq_pCore_of_selfCentralizing 2 hJ) P (X.subgroupOf J) hblock
      (V.subgroupOf J) hVP).2 ⟨v, hVJ hv⟩ hv
    obtain ⟨hzXP, hz2, hzcomm⟩ := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz
    let zX : X := ⟨z, hzXP.1⟩
    refine ⟨zX, (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr ⟨?_, ?_, ?_⟩, ?_⟩
    · exact (hs zX).mpr ((hp z).mp hzXP.2)
    · exact Subtype.ext (congrArg (fun y : J => (y : G)) hz2)
    · intro y hy
      exact Subtype.ext (congrArg (fun y : J => (y : G))
        (hzcomm ⟨y, hXJ y.property⟩ ⟨y.property, (hp _).mpr ((hs y).mp hy)⟩))
    · intro x
      exact congrArg Subtype.val (he ⟨x, hXJ x.property⟩ x.property)

/-- Every actual block has the required common-Sylow inner action after E.6.21.
Characteristic two of its join with Q is established, not assumed. -/
theorem block_common_sylow_action
    (h : HypothesisE61 𝒦 T M V) (h21 : OddCoreFree V)
    (hA : A ∈ obstructionFamily M V) (hX : CentralizerBlock A X) :
    ∃ S : Sylow 2 X,
      (S : Subgroup X).map X.subtype = X ⊓ sylowCentralizer (T : Subgroup G) V ∧
      ∀ v ∈ V, ∃ z : X, z ∈ Stellmacher.omegaOneCenterAmbient (S : Subgroup X) ∧
        ∀ x : X, (z : G) * (x : G) * (z : G)⁻¹ = v * (x : G) * v⁻¹ := by
  have hQA : sylowCentralizer (T : Subgroup G) V ≤ centralizer (A : Set G) :=
    inf_le_right.trans (centralizer_le hA.1)
  exact block_action_of_characteristicTwo_intermediate h hA hX
    (J := X ⊔ sylowCentralizer (T : Subgroup G) V) le_sup_right le_sup_left
    (sup_le hX.1 hQA) (block_join_characteristicTwo h h21 hA hX)


end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase
