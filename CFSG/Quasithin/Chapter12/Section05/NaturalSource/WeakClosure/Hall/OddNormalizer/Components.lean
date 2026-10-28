module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.ComponentPlacement
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.TheoremB.Basic
public import CFSG.Quasithin.ChapterA.Section02.FiniteModelRankExclusions
public import CFSG.Quasithin.ChapterA.Section02.OddBModelTwoRank
public import Theory.SpecificGroups.SymplecticSix.OrderRank
public import Theory.GroupTheory.PerfectCentralCoverOuter
public import Theory.GroupTheory.PrimeRankOrderBound

/-!
# Model exclusions on the original exterior odd-normalizer component

Inner residual action puts an elementary subgroup of order 1024 in the
component's central quotient. The full B-model rank bounds exclude every
odd-characteristic row, both alternating and binary linear rows, and every
sporadic except J₄. The order 2⁹·3⁴·5·7 excludes Sp₆(2) as well.

If the residual action is not inner, its marked PSL₅(2) quotient occurs as
an actual section of Out(K). The proved outer-solvability results exclude
all C-models, all alternating groups, and every odd PSL₂ from this branch.
Thus no universal B-model Schreier input is assumed. The remaining outer
sections and the characteristic-two/J₄ placement cases still need exclusion.
Source: Aschbacher--Smith 4.4.10--12, printed pp.621--623.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04 Chapter12.Section02 ChapterA.Section02 ClassificationModels
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The surviving full-B models after placing the exterior module. -/
def ExteriorPlacedComponentModels (Q : Type*) [Group Q] : Prop :=
  IsBenderModel Q ∨ (∃ f, IsRankTwoModel Q f) ∨ Nonempty (Q ≃* Janko4.Model)

private theorem models_of_rank_ten {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsTheoremBModel Q) (hr : 10 ≤ primeRank 2 Q) :
    ExteriorPlacedComponentModels Q := by
  rcases hQ.remaining_of_twoRank_ge_eight (by omega) with ho | hb | hrank | hs | hj
  · exact (no_theoremB_odd_model_of_twoRank_ge_eight (by omega) ho).elim
  · exact Or.inl hb
  · exact Or.inr (Or.inl hrank)
  · obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := hs
    have hu : primeRank 2 (Theory.SpecificGroups.SymplecticSix.PSp F) ≤ 9 := by
      apply primeRank_le_of_prime_pow_not_dvd
      intro hd
      have hh := hd.trans (card_quotient_dvd_card
        (center (Theory.SpecificGroups.SymplecticSix.Sp F)))
      rw [Theory.SpecificGroups.SymplecticSix.card_sp_of_card_two hc] at hh
      norm_num at hh
    rw [primeRank_equiv 2 e] at hr
    change 10 ≤ primeRank 2 (Theory.SpecificGroups.SymplecticSix.PSp F) at hr
    exact (by omega : False).elim
  · exact Or.inr (Or.inr hj)

private theorem no_outer_section_of_solvable {K : Type*} [Group K]
    [Group.IsSolvable (MulAut.Outer K)] :
    ¬ ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* Representation.SL5TenDimensional.Group,
      Function.Surjective f := by
  rintro ⟨U, f, hf⟩
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) :=
    Atlas.psl_simple_high_rank 5 (by decide)
  let : IsSimpleGroup Representation.SL5TenDimensional.Group :=
    Representation.SL5TenDimensional.projectiveEquiv.isSimpleGroup
  let : Group.IsPerfect Representation.SL5TenDimensional.Group := Atlas.sl_perfect 5 (by decide)
  exact Group.IsPerfect.not_isSolvable Representation.SL5TenDimensional.Group
    (Group.isSolvable_of_surjective hf)

private theorem cover_outer_solvable {K : Type*} [Group K] [IsQuasisimple K]
    [Group.IsSolvable (MulAut.Outer (K ⧸ center K))] :
    Group.IsSolvable (MulAut.Outer K) :=
  Group.isSolvable_of_isSolvable_injective
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))

/-- A genuine remaining source alternative: either the actual component
has a PSL₅(2) outer section outside all proved outer-solvability rows, or
it is normal, contains V and L_A, and has one of the surviving large models. -/
def ExteriorOddNormalizerComponentCase (_s : SylowExteriorMarking D) (A : Subgroup G)
    (K : Subgroup (normalizer (A : Set G))) : Prop :=
  ((∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* Representation.SL5TenDimensional.Group,
      Function.Surjective f) ∧
    ¬ IsTheoremCModel (K ⧸ center K) ∧
    (∀ n : ℕ, ¬ Nonempty ((K ⧸ center K) ≃* alternatingGroup (Fin n))) ∧
    (∀ q : ℕ, Odd q → ¬ ClassicalGroup.IsPSL (K ⧸ center K) 2 q)) ∨
  (K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    centralizer (K : Set (normalizer (A : Set G))) =
      pPrimeCore 2 (normalizer (A : Set G)) ∧
    10 ≤ primeRank 2 (K ⧸ center K) ∧ ExteriorPlacedComponentModels (K ⧸ center K))

/-- All model exclusions are proved from the original marking, on the
literal component selected in N(A); there is no model-exclusion callback. -/
theorem exterior_oddNormalizer_component_cases
    (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (A : Subgroup G) (hAM : A ≤ s.marking.M) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) s.marking.M)
    (hout : ¬ normalizer (A : Set G) ≤ s.marking.M)
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (houtK : ¬ K.map (normalizer (A : Set G)).subtype ≤ s.marking.M)
    (hmodel : IsTheoremBModel (K ⧸ center K)) :
    ExteriorOddNormalizerComponentCase s A K := by
  rcases exterior_oddNormalizer_component_inner_or_outer_section s h A hAM hodd hAV K hK
    with hi | ho
  · obtain ⟨hn, hv, hf, hc, hr⟩ := exterior_oddNormalizer_component_placement
      s h A hAM hodd hAV hu hout K hK houtK hi
    exact Or.inr ⟨hn, hv, hf, hc, hr, models_of_rank_ten hmodel hr⟩
  · let : IsQuasisimple K := hK.2
    let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
    let : Group.IsPerfect (K ⧸ center K) := Group.IsPerfect.ofSurjective
      (f := QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _)
    have hna : ¬ IsMulCommutative (K ⧸ center K) := Group.IsPerfect.not_isMulCommutative _
    have hns : ¬ Group.IsSolvable (MulAut.Outer (K ⧸ center K)) := by
      intro hs
      let := hs
      let := cover_outer_solvable (K := K)
      exact no_outer_section_of_solvable ho
    exact Or.inl ⟨ho,
      fun hc => hns (ChapterA.Section03.SourceComponents.TheoremBOuter.of_theoremC hna hc),
      fun n hn => hns (ChapterA.Section03.SourceComponents.TheoremBOuter.alternating hna hn),
      fun q hq hqK => hns (ChapterA.Section03.SourceComponents.TheoremBOuter.linear_two_odd hna hq hqK)⟩

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
