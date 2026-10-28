module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic.Binary.Intersection
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.AlternatingActions.Transport
public import Theory.SpecificGroups.SymplecticFour.Binary.ComponentActionGeometry.FixedGeneration

/-!
# The escaping hyperplane in the binary Borel case

An action of corank two has faithful image of order four. Its nonidentity
actors' fixed groups generate A₆, hence the actual component. Pulling back
the corresponding lines in the action image gives hyperplanes of V
containing U. At least one has centralizer escaping M. The corank bound
forces strict containment of U, and corank one forces strict containment
in V. This supplies every clause of the binary Borel alternative.

Source: Aschbacher–Smith, E.6.8(2a), printed pp.247–248.
-/

public section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour.Binary.ComponentActionGeometry
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic
open RemainingSieve.AlternatingActions
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G}

/-- The escaping subgroup has the two strict inclusions asserted by the source. -/
theorem binary_corank_two_escape (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : SymplecticDerivedModel L 1) (hd : actionCorank V L = 2) :
    ∃ A : Subgroup G, U < A ∧ A < V ∧ subgroupCorank V A = 1 ∧
      ¬ L ⊓ centralizer (A : Set G) ≤ M := by
  classical
  let _ := h.elementary
  have hn := component_normalized_by_V h hU hL
  let _ := range_elementary hn
  obtain ⟨e⟩ := alternating_six_of_model_one hm
  obtain ⟨S, hS⟩ := exists_sylow_fixed_by_range h hU hL hn
  have hc := card_range_eq_four_of_actionCorank_two hn hd
  let J := (actionHom hn).range
  have hgen : (⊤ : Subgroup L) ≤ ⨆ (a : J) (_ : a ≠ 1),
      fixedSubgroup (a : MulAut L) := by
    let H : Subgroup L := ⨆ (a : J) (_ : a ≠ 1), fixedSubgroup (a : MulAut L)
    have he : H = ⊤ := by
      apply fixed_generation e S J (IsElementaryAbelian.isPGroup 2 (actionHom hn).range) hS hc H
      intro a ha hne
      have hne' : (⟨a, ha⟩ : J) ≠ 1 := fun he => hne (congrArg Subtype.val he)
      exact le_iSup_of_le (⟨a, ha⟩ : J) (le_iSup_of_le hne' (fun x hx => hx))
    exact he.ge
  have hg := hyperplane_generation_of_fixedSubgroup_generation hn hU.1 hL.1 hc hgen
  have hesc : ∃ A : Subgroup G, U ≤ A ∧ A ≤ V ∧ subgroupCorank V A = 1 ∧
      ¬ L ⊓ centralizer (A : Set G) ≤ M := by
    by_contra! hall
    apply component_not_le h earlier hU hL
    apply hg.trans
    exact iSup_le fun A => iSup_le fun hUA => iSup_le fun hAV =>
      iSup_le fun hcod => hall A hUA hAV hcod
  obtain ⟨A, hUA, hAV, hcod, hAM⟩ := hesc
  have hbound := fixedSpace_corank_le hU.1 hL.1
  change actionCorank V L ≤ subgroupCorank V U at hbound
  rw [hd] at hbound
  refine ⟨A, lt_of_le_of_ne hUA ?_, lt_of_le_of_ne hAV ?_, hcod, hAM⟩
  · intro he
    rw [he, hcod] at hbound
    omega
  · intro he
    rw [he, subgroupCorank, relIndex_self] at hcod
    norm_num at hcod

/-- Every clause of E.6.8(2a) at n = 1, conditional only on the actual
intersection being a Borel. -/
theorem binary_borel_alternative (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : SymplecticDerivedModel L 1) (hb : BorelPreimage L (L ⊓ M)) :
    SymplecticAlternative M V U L 1 := by
  refine ⟨hm, fixedSpace_corank_le hU.1 hL.1, by omega, Or.inl ⟨hb, ?_⟩⟩
  rcases component_binary_actionCorank_cases h earlier hU hL hm with hd | hd
  · exact Or.inr ⟨alternating_six_of_model_one hm, hd⟩
  · exact Or.inl ⟨by simpa using hd, binary_corank_two_escape h earlier hU hL hm hd⟩


/-- A maximal-parabolic intersection forces action corank one. The remaining
matrix-root identification is separate from this numerical assertion. -/
theorem binary_parabolic_actionCorank_one (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : SymplecticDerivedModel L 1) (hp : MaximalParabolic L (L ⊓ M)) :
    actionCorank V L = 1 := by
  let _ := h.elementary
  rcases component_binary_actionCorank_cases h earlier hU hL hm with hd | hd
  · exact hd
  · have hn := component_normalized_by_V h hU hL
    let _ := range_elementary hn
    obtain ⟨e⟩ := alternating_six_of_model_one hm
    obtain ⟨S, hS⟩ := exists_sylow_fixed_by_range h hU hL hn
    have hc := card_range_eq_four_of_actionCorank_two hn hd
    have hnot := coatom_not_fixed_of_card_four e S (actionHom hn).range
      (IsElementaryAbelian.isPGroup 2 (actionHom hn).range) hS hc
      ((L ⊓ M).subgroupOf L) hp.2.1
    apply False.elim
    apply hnot
    rintro a ⟨v, rfl⟩ x hx
    have hxC : (x : G) ∈ L ⊓ centralizer (V : Set G) :=
      binary_intersection_eq_centralizer h hU hL hm ▸ hx
    apply Subtype.ext
    change (v : G) * (x : G) * (v : G)⁻¹ = x
    rw [mem_centralizer_iff.mp hxC.2 (v : G) v.property, mul_inv_cancel_right]

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic
