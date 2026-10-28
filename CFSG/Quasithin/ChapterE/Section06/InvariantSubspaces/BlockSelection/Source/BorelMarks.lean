module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Source.SylowAction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.BorelTransport
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.BorelMarks.Five

/-!
# C.1.29 Borel marks on the original E.6.7 factors

Apply the characteristic-normalizer control theorem inside the original
intermediate subgroup H. Transport the resulting full preimage along the
canonical equivalence from the relative block to its ambient carrier.
The marked subgroup becomes exactly M.subgroupOf L.

Source: Aschbacher–Smith C.1.29 and E.6.7, printed pp.134 and 246.
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The double relative intersection transports to the original relative intersection. -/
theorem map_relative_intersection {M H L : Subgroup G} (hLH : L ≤ H) :
    ((M.subgroupOf H).subgroupOf (L.subgroupOf H)).map
      (subgroupOfEquivOfLe hLH).toMonoidHom = M.subgroupOf L := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨⟨x, hLH x.property⟩, x.property⟩, hx, rfl⟩

/-- The literal intermediate Sylow and its characteristic-normalizer control. -/
theorem source_control_sylow {𝒦 : GroupClass} {T : Sylow 2 G} {M V W H : Subgroup G}
    (h : HypothesisE61 𝒦 T M V) (hW : W ∈ obstructionFamily M V)
    (hQH : sylowCentralizer (T : Subgroup G) V ≤ H)
    (hHC : H ≤ centralizer (W : Set G)) :
    ∃ S : Sylow 2 H, (S : Subgroup H) = (sylowCentralizer (T : Subgroup G) V).subgroupOf H ∧
      (S : Subgroup H).characteristicNormalizerClosure ≤ M.subgroupOf H := by
  obtain ⟨S, hS⟩ := h.sylow_obstructionIntermediate hW hQH hHC
  have he : (S : Subgroup H) = (sylowCentralizer (T : Subgroup G) V).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hS, map_subgroupOf_eq_of_le hQH]
  refine ⟨S, he, ?_⟩
  rw [he]
  exact h.characteristic_normalizers_intermediate hQH

/-- Both selected alternating Borel marks follow from the original source hypotheses. -/
theorem source_alternating_borel {𝒦 : GroupClass} {T : Sylow 2 G}
    {M V W H L : Subgroup G} {n : ℕ}
    (h : HypothesisE61 𝒦 T M V) (hW : W ∈ obstructionFamily M V)
    (hQH : sylowCentralizer (T : Subgroup G) V ≤ H)
    (hHC : H ≤ centralizer (W : Set G)) (hc : HasCharacteristicTwo H)
    (hLH : L ≤ H) (hL : ChapterC.IsBlock (L.subgroupOf H))
    (hout : ¬ L ≤ M) (hType : ChapterC.IsAlternatingBlock L n)
    (hn : n = 3 ∨ n = 5) : AlternatingBlockBorel L (M.subgroupOf L) n := by
  obtain ⟨S, _, hcontrol⟩ := source_control_sylow h hW hQH hHC
  let e := subgroupOfEquivOfLe hLH
  have ht := ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv e.symm hType
  have hout' : ¬ L.subgroupOf H ≤ M.subgroupOf H := by
    intro hh
    apply hout
    intro l hl
    exact hh (show (⟨l, hLH hl⟩ : H) ∈ L.subgroupOf H from hl)
  have hb : AlternatingBlockBorel (L.subgroupOf H)
      ((M.subgroupOf H).subgroupOf (L.subgroupOf H)) n := by
    rcases hn with rfl | rfl
    · exact alternating_three_block_borel_of_control S _ _ hcontrol hL hout' ht
    · exact alternating_five_block_borel_of_control
        (generalizedFitting_eq_pCore_of_selfCentralizing 2 hc) S _ _ hcontrol hL hout' ht
  have hh := hb.of_mulEquiv e
  rw [map_relative_intersection hLH] at hh
  exact hh

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
