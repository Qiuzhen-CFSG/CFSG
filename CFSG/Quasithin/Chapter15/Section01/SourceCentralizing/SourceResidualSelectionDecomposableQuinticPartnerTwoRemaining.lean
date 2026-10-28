module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerFourNormalization
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSelectionGenerationEight

/-!
# The precise remaining original quintic normalization branch

The original partner-module cardinal alternatives, the whole-section
order-four exclusion and the seed-centralizer core theorem leave only
the original order-two partner with V outside its two-core. The equality
Uc=E directly gives original normalization. This records the actual
remaining source without replacing the original pair or denominator.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- Only the literal order-two partner outside its core can remain after
all currently established original quintic normalization cases. -/
theorem PreparedChosenModule.decomposable_five_normalization_or_partner_two_outside_core
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
      centralizer (centralInvolutions T : Set G) ≤
          normalizer (thompsonFixed T V : Set G) ∨
        (Nat.card (localModule T Mc) = 2 ∧ ¬V ≤ Mc.pCoreIn 2) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive
  by_cases hVQ : V ≤ Mc.pCoreIn 2
  · exact Or.inl (h.thompsonFixed_residual_normalized_of_le_partner_core
      hG T hempty hM hJ hu hVQ).2
  rcases h.decomposable_five_partner_card_cases
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive with
    hcU | hcU | hUE
  · exact Or.inr ⟨hcU,hVQ⟩
  · exact Or.inl (h.decomposable_five_partner_four_normalization
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).2
  · left
    have hMc : Mc ∈ maximalTwoLocalOvergroups
        (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
    have hn := le_normalizer_conjugateSpanBy (centralInvolutions T) Mc
    change Mc ≤ normalizer (localModule T Mc : Set G) at hn
    rw [hUE] at hn
    exact hMc.2.trans hn

end CFSG.Quasithin.Chapter15.Section01
