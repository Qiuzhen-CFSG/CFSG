module

public import CFSG.Quasithin.Chapter15.SourceAssembly.OriginalQuinticExclusionSource
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPrimeResidual

/-!
# Theorem E after normalization of the marked residual of order fifteen

The original quintic source with marked residual of order fifteen has its
seed-centralizer normalization proved. Earlier normalization therefore
remains only on the extraspecial row and the quintic row with literal marked
residual of order five. The original factor data and Thompson pair are kept.
The rank-two resolver, later quintic exclusion and original 15.3.13 remain.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The remaining normalization rows, with the literal marked residual of
the quintic row restricted to prime order. -/
abbrev OriginalPrimeResidualLargeAction (T : Sylow 2 G) (M V : Subgroup G)
    (h : PreparedChosenModule T M V) : Prop :=
  letI := h.elementary
  let ρ := imageRepresentation M V h.normalized
  let f := (actionHom M V h.normalized).rangeRestrict
  let S := ((T : Subgroup G).subgroupOf M).map f
  SourceCases.Extraspecial ρ S ∨
    (cubicRatio ρ = 2 ∧
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
        Nat.card (pResidual 2 (C ⧸ (M ⊓ centralizer (V : Set G)).subgroupOf C)) = 5)

/-- Original full normalization on the extraspecial row and the quintic
row whose original marked quotient has residual order five. -/
abbrev OriginalPrimeResidualFullNormalizationAt (T : Sylow 2 G) (Mc : Subgroup G) : Prop :=
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
        OriginalPrimeResidualLargeAction T M V hp →
        centralizer (centralInvolutions T : Set G) ≤
          normalizer (thompsonFixed T V : Set G)

/-- The proved residual-order-fifteen branch supplies its normalization,
leaving only the literal residual-order-five quintic source. -/
theorem original_remaining_normalization_of_prime_residual
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hnormalize : OriginalPrimeResidualFullNormalizationAt T Mc) :
    OriginalRemainingFullNormalizationAt T Mc := by
  intro hnot hn M hM hne hJ h
  let := h.elementary
  dsimp only
  intro hfour hstrict haction
  rcases haction with hextra | ⟨hq,U,c,d,s,π,hd,hp,hs,hdec,hfive⟩
  · exact hnormalize hnot hn M hM hne hJ h hfour hstrict (Or.inl hextra)
  · rcases h.decomposable_five_normalization_or_prime_residual
        hG T hempty hM hmany hJ hu rfl c d hd s π hp hs hdec hq hfive with hnorm | hprime
    · exact hnorm
    · exact hnormalize hnot hn M hM hne hJ h hfour hstrict
        (Or.inr ⟨hq,U,c,d,s,π,hd,hp,hs,hdec,hfive,hprime⟩)

/-- Theorem E with normalization on residual order fifteen supplied by
the original marked quintic source. -/
theorem source_theoremE_of_original_prime_residual_sources
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hrank : ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      RankTwoResolver T Mc)
    (hnormalize : ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      OriginalPrimeResidualFullNormalizationAt T Mc)
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
  exact source_theoremE_of_original_quintic_source hG T hmany hempty hrank
    (fun Mc hu => original_remaining_normalization_of_prime_residual
      hG T hmany hempty hu (hnormalize Mc hu)) hquintic h13

end CFSG.Quasithin.Chapter15
