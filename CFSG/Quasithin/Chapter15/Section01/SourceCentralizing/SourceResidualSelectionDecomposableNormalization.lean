module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoCore
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoRemaining
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableThreeExclusion
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonFixed.Normalization

/-!
# Original decomposable normalization and all four 15.1.14 clauses

The original partner-size alternatives leave only the order-two noncore
quintic case, now excluded by the literal three-step kernel chain. The
prime-three source is already impossible. Constructing the Thompson pair
from the unchanged decomposable data therefore supplies global normalization,
residual centralization, and all three normalizer inclusions of 15.1.14.
No source normalization premise, model replacement, or quotient lift is added.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- All partner-size branches normalize the unchanged quintic Thompson fixed subgroup. -/
theorem PreparedChosenModule.decomposable_five_normalization
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
        normalizer (thompsonFixed T V : Set G) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive
  rcases h.decomposable_five_normalization_or_partner_two_outside_core
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive with hn | ⟨hcU,hnot⟩
  · exact hn
  · exact (hnot (h.decomposable_five_partner_two_core
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU)).elim

/-- The full original decomposable source supplies normalization with its own Thompson pair. -/
theorem PreparedChosenModule.decomposable_full_centralizer_normalizes_thompsonFixed
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 →
      centralizer (centralInvolutions T : Set G) ≤
        normalizer (thompsonFixed T V : Set G) := by
  let := h.elementary
  intro U c d hd π hp hs hdec hq
  obtain ⟨s⟩ := DecomposableMarker.thompsonPair_of_decomposable
    hG T hempty hM hmany hJ h hfull c d hd π hp hs hdec hq
  rcases s.prime_cases with hthree | hfive
  · exact (h.false_of_decomposable_three_source
      hG T hempty hM hmany hJ hu hne hfull c d hd s π hp hs hdec hq hthree).elim
  · exact h.decomposable_five_normalization
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive

/-- All four original 15.1.14 clauses for the full decomposable row, with no residual premise. -/
theorem PreparedChosenModule.source_lemma_15_1_14_of_decomposable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 →
      (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
          (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G) ∧
      M ⊓ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤
        normalizer (thompsonFixed T V : Set G) ∧
      normalizer (thompsonFixed T V : Set G) ≤ Mc ∧
      normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤ M ⊓ Mc := by
  let := h.elementary
  intro U c d hd π hp hs hdec hq
  have hn := h.decomposable_full_centralizer_normalizes_thompsonFixed
    hG T hempty hM hmany hJ hu hne hfull c d hd π hp hs hdec hq
  exact ⟨h.thompsonFixed_residual_of_normalizes hG T hM hJ hn,
    h.thompsonFixed_normalizers_of_normalizes hG T hM hJ hu hn⟩

end CFSG.Quasithin.Chapter15.Section01
