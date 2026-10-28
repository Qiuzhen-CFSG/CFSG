module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoCore
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoCoreNormalization

/-!
# Original quintic normalization for the order-two partner module

The three-step original kernel argument puts the full paired-support module
in the actual partner two-core and closes both equal-cost branches.
The original seed-centralizer core theorem then gives both residual
centralization and normalization of its Thompson fixed subgroup. No marked
component generation or global residual hypothesis is supplied.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- Literal original quintic sources with partner module of order two satisfy
both the residual-centralization and normalization conclusions. -/
theorem PreparedChosenModule.decomposable_five_partner_two_normalization
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
      Nat.card (localModule T Mc) = 2 →
      (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
        (centralizer (centralInvolutions T : Set G)).subtype ≤
          centralizer (thompsonFixed T V : Set G) ∧
        centralizer (centralInvolutions T : Set G) ≤
          normalizer (thompsonFixed T V : Set G) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  exact h.thompsonFixed_residual_normalized_of_le_partner_core
    hG T hempty hM hJ hu
    (h.decomposable_five_partner_two_core
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU)

end CFSG.Quasithin.Chapter15.Section01
