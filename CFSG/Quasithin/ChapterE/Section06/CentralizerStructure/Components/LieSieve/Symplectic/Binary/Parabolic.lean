module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic.Binary.Escape

/-!
# The binary parabolic action as an actual matrix-model subgroup

Package the source action in the literal derived matrix carrier. Its image
has order two, is induced by full Sp₄(2) conjugation, and fixes the transported
maximal parabolic pointwise. The parabolic retains a genuine Sylow subgroup.
These are the inputs to the remaining intrinsic root-identification step.

Source: Aschbacher–Smith, E.6.8(2b), printed pp.247–248.
-/

public section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic
open RemainingSieve.AlternatingActions
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G}

omit [Finite G] in
private theorem action_range (hn : V ≤ normalizer (L : Set G)) :
    (inducedAutomizer L V).map (Automizer L).subtype = (actionHom hn).range := by
  ext a
  constructor
  · rintro ⟨b, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨⟨v, hv⟩, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨L.normalizerMonoidHom.rangeRestrict ⟨v, hn v.property⟩,
      ⟨⟨v, hn v.property⟩, v.property, rfl⟩, rfl⟩

/-- The precise intrinsic inputs for identifying the root action, retaining
the actual induced subgroup and the full-group conjugation on the derived carrier. -/
theorem binary_parabolic_image_data (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : SymplecticDerivedModel L 1) (hp : MaximalParabolic L (L ⊓ M)) :
    ∃ e : L ≃* commutator (Sp (ZMod 2)),
      let J := ((inducedAutomizer L V).map (Automizer L).subtype).map
        (MulAut.congr e).toMonoidHom
      Nat.card J = 2 ∧ J ≤ (MulAut.conjNormal (H := commutator (Sp (ZMod 2)))).range ∧
      ∃ P : Subgroup (commutator (Sp (ZMod 2))), IsCoatom P ∧
        (∃ S : Sylow 2 (commutator (Sp (ZMod 2))), (S : Subgroup _) ≤ P) ∧
        ∀ a ∈ J, ∀ x ∈ P, a x = x := by
  let _ := h.elementary
  have hn := component_normalized_by_V h hU hL
  have hd := binary_parabolic_actionCorank_one h earlier hU hL hm hp
  obtain ⟨e, he⟩ := component_binary_action h hU hL hm
  have hcard : Nat.card (actionHom hn).range = 2 := by
    rw [← index_ker, actionHom_ker hn]
    change (V ⊓ centralizer (L : Set G)).relIndex V = 2
    rw [relIndex_eq_two_pow_quotient_finrank, ← subgroupCorank_eq_quotient_finrank]
    change 2 ^ actionCorank V L = 2
    rw [hd]
    rfl
  refine ⟨e, ?_, he, ((L ⊓ M).subgroupOf L).map e.toMonoidHom,
    (e.mapSubgroup.isCoatom_iff _).mpr hp.2.1, ?_, ?_⟩
  · rw [card_map_of_injective (MulAut.congr e).injective, action_range hn, hcard]
  · obtain ⟨S, hS⟩ := hp.2.2
    exact ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective,
      map_mono ((S : Subgroup L).le_normalizer.trans hS)⟩
  · rintro a ⟨b, ⟨c, ⟨v, hv, rfl⟩, rfl⟩, rfl⟩ x ⟨y, hy, rfl⟩
    change e (L.normalizerMonoidHom v (e.symm (e y))) = e y
    rw [e.symm_apply_apply]
    apply congrArg e
    apply Subtype.ext
    change (v : G) * (y : G) * (v : G)⁻¹ = y
    have hyC : (y : G) ∈ L ⊓ centralizer (V : Set G) :=
      binary_intersection_eq_centralizer h hU hL hm ▸ hy
    rw [mem_centralizer_iff.mp hyC.2 (v : G) hv, mul_inv_cancel_right]

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic
