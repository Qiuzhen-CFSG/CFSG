module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableNormalization
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableFifteenSource.Core

/-!
# The original quintic module and its full fixed-subgroup normalizer

All three actual partner-module sizes put the full original module in the
partner two-core. Full normalization and source ordering then identify the
entire normalizer of the original Thompson fixed subgroup with that partner.
These conclusions retain the original decomposition and Thompson marking.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- Every original quintic partner-size branch contains the full module in its two-core. -/
theorem PreparedChosenModule.decomposable_five_le_partner_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      V ≤ Mc.pCoreIn 2 := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive
  rcases h.decomposable_five_partner_card_cases
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive with
    hcU | hcU | hUE
  · exact h.decomposable_five_partner_two_core
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  · exact h.decomposable_five_partner_four_le_partner_core
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  · exact (h.decomposable_five_full_partner_module_le_core
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hUE).2

/-- The actual partner is the complete normalizer of the original fixed subgroup. -/
theorem PreparedChosenModule.decomposable_five_fixed_normalizer_eq_partner
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      normalizer (thompsonFixed T V : Set G) = Mc := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive
  let E := thompsonFixed T V
  obtain ⟨hupper,hinter,_⟩ := h.decomposable_five_partner_control
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  have hseed := h.decomposable_five_normalization
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  have hMcC : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMcC.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  refine le_antisymm hupper ?_
  intro m hm
  obtain ⟨a,ha,b,hb,rfl⟩ := source_ordering_of_centralizing_orderingMaximal
    hG T hempty hM hJ Mc ⟨hMcC.1,hTMc⟩ m hm
  exact (normalizer (E : Set G)).mul_mem (hinter ⟨ha.2,ha.1⟩)
    (hseed ((centralizer_le (le_conjugateSpanBy (centralInvolutions T) Mc)) hb.2))

end CFSG.Quasithin.Chapter15.Section01
