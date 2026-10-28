module

public import CFSG.Quasithin.Chapter15.SourceAssembly.OriginalPrimeResidualSource
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialMarkedConsumer

/-!
# Theorem E with only quintic normalization remaining

The original full extraspecial action is now excluded without earlier
residual control. Together with the proved quintic residual-order-fifteen
normalization, this leaves only normalization of the literal quintic marked
quotient with residual order five. The later quintic exclusion still ranges
over all original quintic Thompson pairs.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The literal quintic source whose marked quotient residual has order five. -/
abbrev OriginalQuinticPrimeAction (T : Sylow 2 G) (M V : Subgroup G)
    (h : PreparedChosenModule T M V) : Prop :=
  letI := h.elementary
  let ρ := imageRepresentation M V h.normalized
  let f := (actionHom M V h.normalized).rangeRestrict
  cubicRatio ρ = 2 ∧
      ∃ (U : Submodule (ZMod 2) (Additive V)) (c : FactorData ρ (Jhat ρ) U)
        (d : Decomposition c.representation)
        (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
        (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
        d.FittingFull ∧
        (∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
          (c.ambientFactor d (π g i)).actor) ∧
        (∀ g i, (c.ambientFactor d i).space.map (ρ g) =
          (c.ambientFactor d (π g i)).space) ∧
        SourceCases.Decomposable ρ (T : Subgroup G) M f c d π ∧ s.prime = 5 ∧
        let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
        let C := M ⊓ centralizer (Z₁ : Set G)
        letI := caseI_module_centralizer_normal (Z1 := Z₁) h.normalized
        Nat.card (pResidual 2 (C ⧸ (M ⊓ centralizer (V : Set G)).subgroupOf C)) = 5

/-- Original full normalization on the quintic row whose literal marked
quotient residual has order five. -/
abbrev OriginalQuinticPrimeFullNormalizationAt (T : Sylow 2 G) (Mc : Subgroup G) : Prop :=
  ¬ ClassificationModels.IsTheoremEModel G →
    (∀ N : Subgroup G, IsOrderingMaximal T N →
      ¬ Nonempty (NaturalOrthogonalAction N (localModule T N))) →
    ∀ (M : Subgroup G) (_hM : IsOrderingMaximal T M), M ≠ Mc →
      elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G) →
      ∀ hp : PreparedChosenModule T M (localModule T M),
        letI := hp.elementary
        let V := localModule T M
        let D := internalActionImage M V hp.normalized
        let S := ((T : Subgroup G).subgroupOf M).map
          (actionHom M V hp.normalized).rangeRestrict
        4 ∣ Nat.card D →
        ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
          (actionHom M V hp.normalized).rangeRestrict < S →
        OriginalQuinticPrimeAction T M V hp →
        centralizer (centralInvolutions T : Set G) ≤
          normalizer (thompsonFixed T V : Set G)

/-- The actual prior-free extraspecial contradiction supplies that row of
normalization at the same original group, Sylow subgroup and chosen module. -/
theorem original_prime_residual_normalization_of_quintic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hnormalize : OriginalQuinticPrimeFullNormalizationAt T Mc) :
    OriginalPrimeResidualFullNormalizationAt T Mc := by
  intro hnot hn M hM hne hJ h
  let := h.elementary
  dsimp only
  intro hfour hstrict haction
  rcases haction with hextra | hquintic
  · exact (h.false_of_full_extraspecial_without_residual
      hG T hempty hM hmany hJ hu hne rfl hextra).elim
  · exact hnormalize hnot hn M hM hne hJ h hfour hstrict hquintic

/-- Theorem E with extraspecial normalization supplied internally. -/
theorem source_theoremE_of_original_quintic_prime_sources
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hrank : ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      RankTwoResolver T Mc)
    (hnormalize : ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      OriginalQuinticPrimeFullNormalizationAt T Mc)
    (hquintic : ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      OriginalQuinticExclusionAt T Mc)
    (h13 : ∀ d : CharacteristicTwo.LocalData G, d.T = T →
      IsOrderingMaximal d.T d.M →
      maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc} →
      ∀ Yplus : Subgroup G, Hypothesis15310 d.M d.Y d.S d.V₁ Yplus →
      primeRank 3 Yplus = 2 →
      ∀ I ∈ outsideFamily Yplus d.S d.M, generalizedFitting I ≠ pCore 2 I) :
    ClassificationModels.IsTheoremEModel G := by
  exact source_theoremE_of_original_prime_residual_sources hG T hmany hempty hrank
    (fun Mc hu => original_prime_residual_normalization_of_quintic
      hG T hmany hempty hu (hnormalize Mc hu)) hquintic h13

end CFSG.Quasithin.Chapter15
