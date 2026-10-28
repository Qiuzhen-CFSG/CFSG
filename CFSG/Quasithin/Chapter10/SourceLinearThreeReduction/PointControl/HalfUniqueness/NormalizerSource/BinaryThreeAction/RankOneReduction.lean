module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.Linear

/-!
# Rank-one enlargements are the only remaining source normalizer cases

The actual Held, PSL₄(2) and PSL₅(2) quotient calculations all normalize the
original parabolic residual. Failure of normalization therefore constructs
only an even-degree binary PSL₂ or odd-prime PSL₂ component. The literal
enlargement, relative normality, full Sylow intersection, R=T₁∩K and source
two-core bounds remain intact.

Apply this to the two parabolics constructed using the specified exchanger.
Their residuals generate L₀, so either the normalizer is contained in M or
one of these rank-one configurations occurs. The already complete containing
argument then gives the same alternative for the exact half-join L₀N_T(L).
The rank-one alternatives remain to be excluded by this task; none of the
alternatives below asserts that source 10.2.5 or 10.2.6 is complete.

Source: Aschbacher--Smith 10.2.4--6, printed pp.747--749. ModuleChoiceAt is
the only external premise, ultimately discharged by qt-d-10-nona5-point-control.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 BinaryThreeAction.Parabolics
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- An actual strict rank-one enlargement of one original parabolic.
The subgroup R is the literal stabilizer intersection, not a chosen subgroup
in an abstract two-core interval. -/
def RankOneEnlargement (D : FundamentalSetup KnownSimple.IsKnownSimple T L) : Prop :=
  ∃ H I : Subgroup G, Data D H ∧
    (enlargement T L H).pCoreIn 2 ≠ ⊥ ∧
    residual H < enlargedResidual T L H ∧
    I ∈ Chapter1.cComponentsIn (enlargement T L H) ∧
    IsQuasisimple (Chapter1.XiQuotient I) ∧
    enlargedResidual T L H = componentOrbit I (T : Subgroup G) ∧
    ((∃ n : ℕ, 2 ≤ n ∧ Even n ∧
        ClassicalGroup.IsPSL (Chapter1.XiQuotient I) 2 (2 ^ n)) ∨
      (∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (Chapter1.XiQuotient I) 2 p)) ∧
    ((enlargedResidual T L H).subgroupOf (enlargement T L H)).Normal ∧
    normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      normalizer (stabilizerIntersection T L H : Set G) ∧
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ enlargedResidual T L H)
      (enlargedResidual T L H) ∧
    (stabilizerIntersection T L H).relIndex
      ((T : Subgroup G) ⊓ enlargedResidual T L H) ≤ 2 ∧
    (enlargedResidual T L H).pCoreIn 2 ≤ stabilizerIntersection T L H ∧
    (residual H ⊔ ((T : Subgroup G) ⊓ enlargedResidual T L H)).pCoreIn 2 ≤
      stabilizerIntersection T L H

/-- An escaping original residual constructs the full source configuration. -/
theorem rankOneEnlargement_of_not_normalizes
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {H : Subgroup G}
    (h : Data D H) (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hN : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      normalizer (residual H : Set G)) : RankOneEnlargement D := by
  obtain ⟨hlt,I,hI,hq,hK,hm⟩ := h.strict_rank_one_models hn hN
  exact ⟨H,I,h,h.enlargement_two_core_ne_bot hn,hlt,hI,hq,hK,hm,
    h.enlargedResidual_normal,h.normalizer_normalizes_intersection,
    h.enlargedResidual_sylow,h.intersection_relIndex_le_two hn,
    h.enlargedResidual_core_le_intersection,h.parabolic_intersection_core_le⟩

/-- Apply the completed Held and binary-linear calculations to the two actual parabolics
constructed from the original specified exchanger. -/
theorem binary_three_normalizer_or_rankOneEnlargement
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hmodel : Selection.BinaryThreeNatural D) (hzero : sourceMovedFixed D = ⊥)
    (hfull : D.fullModule = D.moduleSubgroup)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤ D.maximalLocal ∨
      RankOneEnlargement D := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  obtain ⟨H₁,H₂,h₁,h₂,_,hgen⟩ := exists_pair D hmodel hzero hfull ht htn hcross
  by_cases hN₁ : normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      normalizer (residual H₁ : Set G)
  · by_cases hN₂ : normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
        normalizer (residual H₂ : Set G)
    · exact Or.inl (normalizer_le_of_normalizes_pair h₁ h₂ hgen hN₁ hN₂)
    · exact Or.inr (rankOneEnlargement_of_not_normalizes h₂ hn hN₂)
  · exact Or.inr (rankOneEnlargement_of_not_normalizes h₁ hn hN₁)

/-- The original literal half-join is unique unless one of its actual
parabolic residuals has a strict rank-one enlargement. -/
theorem halfSylowUnique_or_rankOneEnlargement
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hmodel : Selection.BinaryThreeNatural D) (hzero : sourceMovedFixed D = ⊥)
    (hfull : D.fullModule = D.moduleSubgroup)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    HalfSylowUnique D ∨ RankOneEnlargement D := by
  rcases binary_three_normalizer_or_rankOneEnlargement D hmodel hzero hfull ht htn hcross with hN | hc
  · left
    have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
    intro H hH hhalf
    by_contra hne
    obtain ⟨s,K₁,K₂,C⟩ := exists_containingPair D hN hn hH hne hhalf
    exact containingPairExclusionAt_of_moduleChoice hchoice hmany L D hn hna H s K₁ K₂ C
  · exact Or.inr hc

/-- Globally, the only unresolved normalizer cases are genuine strict
rank-one enlargements. The Held, binary-linear and containing-component
calculations are discharged. -/
theorem stabilizerNormalizerAt_or_rankOneEnlargement
    (hchoice : Selection.ModuleChoiceAt T) :
    StabilizerNormalizerAt T ∨
      ∃ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
        RankOneEnlargement D := by
  classical
  by_cases he : ∃ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
      RankOneEnlargement D
  · exact Or.inr he
  · left
    apply stabilizerNormalizerAt_of_moduleChoice_and_parabolic_normalizers hchoice
    intro L D _ _ _ hn _ _ _ _ H hH
    by_contra hN
    exact he ⟨L,D,rankOneEnlargement_of_not_normalizes hH hn hN⟩

/-- The completed containing-component argument applies to the global
normalizer alternative with precisely the authorized ModuleChoiceAt input. -/
theorem halfSylowUniqueAt_or_rankOneEnlargement
    (hchoice : Selection.ModuleChoiceAt T) :
    HalfSylowUniqueAt T ∨
      ∃ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
        RankOneEnlargement D := by
  rcases stabilizerNormalizerAt_or_rankOneEnlargement hchoice with hN | hc
  · exact Or.inl (halfSylowUniqueAt_of_moduleChoice_and_normalizer hchoice hN)
  · exact Or.inr hc

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
