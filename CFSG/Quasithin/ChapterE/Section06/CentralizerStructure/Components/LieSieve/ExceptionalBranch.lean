module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.ExceptionalBranch.LocalSubgroups
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.ExceptionalBranch.BorelAction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.ExceptionalBranch.SylowKernel

/-!
# The exceptional PSL₂(4) branch of E.6.8

The intersection L ∩ M is either the actual Sylow four-group L ∩ C_T(V),
or its full Borel normalizer. In the latter case the intrinsic Borel action
gives every field of `BorelAlternative` at n = 2, including the actual cubic
automizer, direct decomposition, and displacement dimension.

In the Sylow case the complete, universally quantified E.6.7 input gives
action corank one through the constructed Borel block. The fixed-space
inequality then gives global rank one, and the actual PSL₂(5) comparison
supplies the Fermat-prime model on L itself. `adequate_borel_or_odd` assembles
these alternatives with only `EarlierLocalFacts` and `E67Input` explicit.
It omits the unresolved assertion U = C_V(L) in the odd case, as required
by the adequate route; it does not assert the full `OddAlternative` or
assume maximality of U. The complete output records remain unchanged.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.ExceptionalBranch

variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G}

/-- The full Borel alternative for the exceptional component, including all
action and decomposition fields, from the actual intersection normalizer. -/
theorem borelAlternative_of_intersection_normalizer
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : ClassicalGroup.IsPSL L 2 4) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype =
      L ⊓ sylowCentralizer (T : Subgroup G) V)
    (hB : (L ⊓ M).subgroupOf L = normalizer (S : Set L)) :
    BorelAlternative M V U L 2 := by
  let _ := h.elementary
  have hN := component_normalized_by_V h hU hL
  have hfix : ∀ v ∈ V, ∀ x : S,
      v * ((x : L) : G) * v⁻¹ = ((x : L) : G) := by
    intro v hv x
    have hx : ((x : L) : G) ∈ L ⊓ sylowCentralizer (T : Subgroup G) V :=
      hS ▸ mem_map_of_mem L.subtype x.property
    rw [mem_centralizer_iff.mp hx.2.2 v hv]
    simp
  have hBmap := congrArg (Subgroup.map L.subtype) hB
  rw [map_subgroupOf_eq_of_le inf_le_left] at hBmap
  have hne : ¬ V ≤ centralizer (L : Set G) := by
    intro hc
    exact component_not_le h earlier hU hL
      ((le_centralizer_iff.mpr hc).trans h.centralizer_le)
  obtain ⟨_, hd, hdim, hw, ha⟩ := BorelAction.intrinsic_borel_action hm hN S hfix
    hBmap (component_intersection_normalizes h hU hL.1) hne
  refine ⟨.linear_two (by decide) hm,
    borelPreimage_of_intersection_normalizer hm S hB, ha, hdim.symm, ?_,
    fun _ => hd, fun _ => hw⟩
  calc
    2 = actionCorank V L := hdim.symm
    _ ≤ subgroupCorank V U := fixedSpace_corank_le hU.1 hL.1

open InvariantSubspaces.BlockSelection

/-- The adequate exceptional branch of E.6.8: either every original Borel
field holds, or the actual component has an odd prime model and both ranks
are one. The universal E.6.7 input is explicit; no Borel-placement or
kernel-equality premise is imposed. In the odd case the model is PSL₂(5). -/
theorem adequate_borel_or_odd
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (input : E67Input T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : ClassicalGroup.IsPSL L 2 4) :
    (∃ n, BorelAlternative M V U L n) ∨
      ((∃ p : ℕ, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL L 2 p) ∧
        actionCorank V L = 1 ∧ globalR V = 1) := by
  obtain ⟨S, hS⟩ := component_sylow_intersection h hU hL
  rcases intersection_cases h earlier hU hL hm S hS with hs | hb
  · have hLM := congrArg (Subgroup.map L.subtype) hs
    rw [map_subgroupOf_eq_of_le inf_le_left, hS] at hLM
    have hd := SylowKernel.actionCorank_one h earlier input hU hL hm hLM
    refine Or.inr ⟨odd_model_of_four hm, hd, le_antisymm ?_ (one_le_globalR V)⟩
    have hbound : globalR V ≤ (actionCorank V L : ℕ∞) :=
      fixedSpace_globalR_le h (component_not_le h earlier hU hL)
    simpa only [hd, Nat.cast_one] using hbound
  · exact Or.inl ⟨2, borelAlternative_of_intersection_normalizer h earlier hU hL hm S hS hb⟩

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.ExceptionalBranch
