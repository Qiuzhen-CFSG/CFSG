module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallRadical

/-!
# The remaining collapsed-radical source configuration

The full-intersection small-congruence branch is closed whenever the
original radical survives in K/O₂(K). Therefore every remaining failure
has O₂(X) ≤ O₂(K), as well as all the original full-intersection and
zero-kernel source guards. The literal half-join consumer uses the completed
containing-pair argument and keeps exactly this last local obstruction.

The radical-collapse exclusion and final 10.2.5--6 assembly remain with
qt-d-10-nona5-half-sylow-unique. Only ModuleChoiceAt is external, with its
ultimate discharge retained by qt-d-10-nona5-point-control.
Source: Aschbacher--Smith 10.2.5--6, printed pp.748--749.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding BinaryThreeAction.Parabolics
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The remaining actual enlargement retains the full intersection and the literal radical collapse. -/
def CollapsedSmallOddPrimeEnlargement (D : FundamentalSetup KnownSimple.IsKnownSimple T L) : Prop :=
  ∃ (H P I : Subgroup G) (p : ℕ), Data D H ∧
    SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) (residual H) P
      (enlargement T L H) I ∧
    enlargedResidual T L H = componentOrbit I (T : Subgroup G) ∧
    p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (XiQuotient I) 2 p ∧
    (p % 8 = 3 ∨ p % 8 = 5) ∧
    (enlargement T L H).pCoreIn 2 ≠ ⊥ ∧
    residual H < enlargedResidual T L H ∧
    stabilizerIntersection T L H = (T : Subgroup G) ⊓ enlargedResidual T L H ∧
    (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2

/-- A normalization failure forces the original radical into the enlargement radical. -/
theorem collapsedSmallOddPrimeEnlargement_of_not_normalizes
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {H : Subgroup G}
    (h : Data D H) (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hN : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      normalizer (residual H : Set G)) : CollapsedSmallOddPrimeEnlargement D := by
  obtain ⟨H',P,I,p,h',hs,hK,hp,ho,hm,hmod,hcore,hlt,hR⟩ :=
    fullSmallOddPrimeEnlargement_of_not_normalizes h hn hN
  have hn' : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      normalizer (residual H' : Set G) := by
    intro hn'
    have hEH : enlargement T L H' ≤ normalizer (residual H' : Set G) :=
      sup_le hn' (le_normalizer_embedded_pResidual 2 H')
    have he : enlargedResidual T L H' ≤ residual H' := conjugateSpanBy_le le_rfl hEH
    exact hlt.not_ge he
  refine ⟨H',P,I,p,h',hs,hK,hp,ho,hm,hmod,hcore,hlt,hR,?_⟩
  apply h'.quotient_core_eq_bot_iff.mp
  by_contra hpos
  exact hn' (h'.normalizes_residual_of_odd_small_full_positive hn hs hK hp ho hm hmod hR hpos)

/-- Every original zero-kernel source guard is retained at the last local obstruction. -/
def SourceCollapsedSmallOddPrimeEnlargement
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard ∧
    D.IsMinimalFullModule ∧ D.fullModule = D.moduleSubgroup ∧
    ¬ (T : Subgroup G) ≤ normalizer (L : Set G) ∧
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) ∧
    Selection.BinaryThreeNatural D ∧ sourceMovedFixed D = ⊥ ∧
    ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G) ∧
    CollapsedSmallOddPrimeEnlargement D

/-- Only the original collapsed-radical configuration can obstruct 10.2.5. -/
theorem stabilizerNormalizerAt_or_collapsedSmallOddPrimeEnlargement
    (hchoice : Selection.ModuleChoiceAt T) :
    StabilizerNormalizerAt T ∨
      ∃ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
        SourceCollapsedSmallOddPrimeEnlargement D := by
  classical
  by_cases he : ∃ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
      SourceCollapsedSmallOddPrimeEnlargement D
  · exact Or.inr he
  · left
    apply stabilizerNormalizerAt_of_moduleChoice_and_parabolic_normalizers hchoice
    intro L D hmany hmin hfull hn hna hmodel hzero hJ H hH
    by_contra hN
    exact he ⟨L,D,hmany,hmin,hfull,hn,hna,hmodel,hzero,hJ,
      collapsedSmallOddPrimeEnlargement_of_not_normalizes hH hn hN⟩

/-- The completed containing-pair argument gives the literal half-join application. -/
theorem halfSylowUniqueAt_or_collapsedSmallOddPrimeEnlargement
    (hchoice : Selection.ModuleChoiceAt T) :
    HalfSylowUniqueAt T ∨
      ∃ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
        SourceCollapsedSmallOddPrimeEnlargement D := by
  rcases stabilizerNormalizerAt_or_collapsedSmallOddPrimeEnlargement hchoice with hN | hc
  · exact Or.inl (halfSylowUniqueAt_of_moduleChoice_and_normalizer hchoice hN)
  · exact Or.inr hc

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
