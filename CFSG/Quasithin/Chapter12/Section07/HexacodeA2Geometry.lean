module

public import CFSG.Quasithin.ChapterE.Section03.OddCore
public import Theory.Representation.HexacodeAction.SmallFixedSpace

/-!
# The actual A2 actors on the hexacode

An A2 actor centralizes the normal cubic scalar by E.3.40, so it lies in
the even cover. Its elementary rank is exactly two. The defining fixed-space
condition makes its fixed space the four-space of any of its involutions.
It is therefore a best offender. The intrinsic hexacode uniqueness theorem
then identifies any two A2 actors lying in the same two-group.

Source: Aschbacher–Smith, 12.7.3 and 12.7.11, using E.3.40 and K.1.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Atlas.Codes
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open ChapterE Hexacode

private theorem a2_le_even {A : Subgroup HexAutomorphisms}
    (hA : A ∈ fixedSpaceFamily action 2) : A ≤ hexSign.ker := by
  let Z := zpowers hexZ
  have hZ : Z.Normal := by
    change (zpowers hexZ).Normal
    rw [← hexCoordinate_kernel]
    infer_instance
  let := hZ
  have hc := centralizes_odd_of_mem_fixedSpaceFamily action action_injective hA Z
    (by change Odd (Nat.card (zpowers hexZ)); rw [Nat.card_zpowers, hexZ_order]; decide)
    (by rw [Z.normalizer_eq_top]; exact le_top)
  intro g hg
  change hexSign g = 1
  rcases Int.units_eq_one_or (hexSign g) with he | ho
  · exact he
  · have hh := hex_conjugation_odd g ho
    have hz : hexZ * g = g * hexZ := hc hg hexZ (mem_zpowers hexZ)
    rw [← hz, mul_inv_cancel_right] at hh
    have hp : hexZ ^ 2 = 1 := by rw [pow_two]; exact (congrArg (fun z => z * hexZ) hh).trans (inv_mul_cancel hexZ)
    have hd := orderOf_dvd_of_pow_eq_one hp
    rw [hexZ_order] at hd
    norm_num at hd

/-- Every A2 actor is the genuine even rank-two best offender, fixing
 exactly four binary dimensions of the literal hexacode. -/
theorem hexacode_a2_bestOffender (A : Subgroup HexAutomorphisms)
    (hA : A ∈ fixedSpaceFamily action 2) :
    A ≤ hexSign.ker ∧ rank A = 2 ∧
      Module.finrank (ZMod 2) (fixedSpace action A) = 4 ∧ IsBestOffender action A := by
  let := hA.2.1.2
  have hAe := a2_le_even hA
  let B := A.subgroupOf hexSign.ker
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hAe
  have hBcard : Nat.card B = Nat.card A := Nat.card_congr (subgroupOfEquivOfLe hAe).toEquiv
  have hrank : rank A = 2 := by
    have hlo := parameter_le_rank_of_mem_fixedSpaceFamily action action_injective hA
    have hhi := ThompsonOffenders.elementary_card_le_four B inferInstance
    rw [hBcard] at hhi
    have hh := Nat.log_mono_right (b := 2) hhi
    change rank A ≤ 2 at hh
    omega
  have hcard : Nat.card A = 4 := by
    rw [hA.2.1.card_eq_two_pow_rank, hrank]
    rfl
  obtain ⟨x, hx, hxne⟩ := A.bot_or_exists_ne_one.resolve_left hA.2.1.1
  have hx2 : x ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian x hx
  have hxo : orderOf x = 2 := orderOf_eq_prime hx2 hxne
  have hzx : zpowers x ≤ A := zpowers_le.mpr hx
  have hi : (zpowers x).relIndex A = 2 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup HexAutomorphisms) (zpowers x) A bot_le hzx
    rw [relIndex_bot_left, relIndex_bot_left, Nat.card_zpowers, hxo, hcard] at hh
    omega
  have hfixed := hA.2.2 (zpowers x) hzx (by rw [hi]; decide)
  let xe : HexEvenAutomorphisms := ⟨x, hAe hx⟩
  have hxe2 : xe ^ 2 = 1 := Subtype.ext hx2
  have hxene : xe ≠ 1 := fun he => hxne (congrArg Subtype.val he)
  have hsame : fixedSpace evenAction (zpowers xe) = fixedSpace action (zpowers x) := by
    change fixedSpace (action.comp hexSign.ker.subtype) _ = _
    rw [fixedSpace_comp_map, MonoidHom.map_zpowers]
    rfl
  have hdim : Module.finrank (ZMod 2) (fixedSpace action A) = 4 := by
    rw [hfixed, ← hsame]
    exact ProjectiveLineNormalizer.involution_fixedSpace_finrank xe hxe2 hxene
  have hBmap : B.map hexSign.ker.subtype = A := map_subgroupOf_eq_of_le hAe
  have hBfixed : fixedSpace evenAction B = fixedSpace action A := by
    change fixedSpace (action.comp hexSign.ker.subtype) B = _
    rw [fixedSpace_comp_map, hBmap]
  have hBrank : rank B = 2 := by unfold rank; rw [hBcard]; exact hrank
  have hBne : B ≠ ⊥ := by intro he; rw [he, card_bot, hcard] at hBcard; omega
  have hbest : IsBestOffender evenAction B := by
    apply (isBestOffender_iff_of_not_strong evenAction ThompsonOffenders.no_strong B).mpr
    refine ⟨⟨hBne, inferInstance⟩, ?_⟩
    have hh := fixedCodim_add_finrank evenAction B
    rw [hBfixed, hdim, hexacode_finrank] at hh
    rw [hBrank]
    omega
  refine ⟨hAe, hrank, hdim, ?_⟩
  have hh := hbest.map_subtype action
  rwa [hBmap] at hh

/-- The A2 actor is unique inside any actual two-subgroup of the full code group. -/
theorem hexacode_a2_unique_in_pgroup
    (P : Subgroup HexAutomorphisms) (hP : IsPGroup 2 P)
    {A B : Subgroup HexAutomorphisms} (hAP : A ≤ P) (hBP : B ≤ P)
    (hA : A ∈ fixedSpaceFamily action 2) (hB : B ∈ fixedSpaceFamily action 2) : A = B :=
  ThompsonOffenders.bestOffender_unique_in_pgroup P hP hAP hBP
    (hexacode_a2_bestOffender A hA).2.2.2 (hexacode_a2_bestOffender B hB).2.2.2

/-- Conversely, the actual four-element best offender belongs to the A2 family. -/
theorem hexacode_bestOffender_mem_a2 (A : Subgroup HexAutomorphisms)
    (hA : IsBestOffender action A) : A ∈ fixedSpaceFamily action 2 := by
  let := hA.1.2
  have hAe := ThompsonOffenders.bestOffender_le_even A hA
  have hcard := ThompsonOffenders.full_bestOffender_card A hA
  have hdim := ThompsonOffenders.full_bestOffender_fixedSpace_finrank A hA
  refine ⟨by decide, hA.1, ?_⟩
  intro B hBA hidx
  have hBne : B ≠ ⊥ := by
    intro hb
    rw [hb, relIndex_bot_left, hcard] at hidx
    norm_num at hidx
  obtain ⟨x, hx, hxne⟩ := B.bot_or_exists_ne_one.resolve_left hBne
  let xe : HexEvenAutomorphisms := ⟨x, hAe (hBA hx)⟩
  have hx2 : xe ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian x (hBA hx))
  have hxene : xe ≠ 1 := fun hh => hxne (congrArg Subtype.val hh)
  have hsame : fixedSpace evenAction (zpowers xe) = fixedSpace action (zpowers x) := by
    change fixedSpace (action.comp hexSign.ker.subtype) _ = _
    rw [fixedSpace_comp_map, MonoidHom.map_zpowers]
    rfl
  have hAB : fixedSpace action A ≤ fixedSpace action B := ChapterE.fixedSpace_antitone action hBA
  have hBX : fixedSpace action B ≤ fixedSpace action (zpowers x) :=
    ChapterE.fixedSpace_antitone action (zpowers_le.mpr hx)
  apply Submodule.eq_of_le_of_finrank_eq hAB
  have hh := Submodule.finrank_mono hBX
  rw [← hsame, ProjectiveLineNormalizer.involution_fixedSpace_finrank xe hx2 hxene] at hh
  have hlo := Submodule.finrank_mono hAB
  rw [hdim] at hlo ⊢
  omega

end CFSG.Quasithin.Chapter12.Section07
