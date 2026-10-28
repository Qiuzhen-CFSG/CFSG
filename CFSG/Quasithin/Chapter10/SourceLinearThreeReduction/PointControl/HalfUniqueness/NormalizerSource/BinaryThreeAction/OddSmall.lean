module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddLarge

/-!
# The sole remaining small-congruence normalizer branch

Even-degree rank-one enlargements and both intersection cases for
p ≡ ±1 mod 8 are closed. Every remaining failure supplies the original
parabolic and swapped components with p ≡ 3 or 5 mod 8, the nontrivial
enlargement core, strict residual inclusion and literal index bound.
The global reductions additionally retain all original source hypotheses,
including the minimal binary-three module and zero kernel.

Both source consumers are connected below. These are reductions, not the
completed normalizer or uniqueness theorem. The remaining small-congruence
calculation stays with qt-d-10-nona5-half-sylow-unique. ModuleChoiceAt is the
only external source input, finally discharged by qt-d-10-nona5-point-control.
Source: Aschbacher--Smith 10.2.5--6, printed pp.748--749.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding BinaryThreeAction.Parabolics
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original small-congruence configuration, with its literal subgroup data. -/
def SmallOddPrimeEnlargement (D : FundamentalSetup KnownSimple.IsKnownSimple T L) : Prop :=
  ∃ (H P I : Subgroup G) (p : ℕ), Data D H ∧
    SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) (residual H) P
      (enlargement T L H) I ∧
    enlargedResidual T L H = componentOrbit I (T : Subgroup G) ∧
    p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (XiQuotient I) 2 p ∧
    (p % 8 = 3 ∨ p % 8 = 5) ∧
    (enlargement T L H).pCoreIn 2 ≠ ⊥ ∧
    residual H < enlargedResidual T L H ∧
    (stabilizerIntersection T L H).relIndex ((T : Subgroup G) ⊓ enlargedResidual T L H) ≤ 2

/-- Every failed normalization now supplies a small-congruence enlargement. -/
theorem smallOddPrimeEnlargement_of_not_normalizes
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {H : Subgroup G}
    (h : Data D H) (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hN : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      normalizer (residual H : Set G)) : SmallOddPrimeEnlargement D := by
  obtain ⟨P,I,hs,hK⟩ := h.exists_swapped_input hn hN
  let hA := fun (Y : Type _) [Group Y] [Finite Y] =>
    ChapterA.Section02.theoremA_knownSimple (G := Y)
  let hC := fun (Y : Type _) [Group Y] [Finite Y] =>
    ChapterA.Section02.theoremC_knownSimple (G := Y)
  obtain ⟨_,_,hm⟩ := SwappedSylow.embedding_of_theoremsAC hA hC hs
  rcases hm with ⟨n,he,_,hm⟩ | ⟨p,hp,ho,hm⟩
  · have hn0 : n ≠ 0 := by
      intro hn0
      obtain ⟨F,_,_,hc,_⟩ := hm
      have hlarge := Finite.one_lt_card (α := F)
      simp only [hn0,pow_zero] at hc
      omega
    have hn2 : 2 ≤ n := by obtain ⟨k,hk⟩ := he; omega
    exact (hN (h.normalizes_residual_of_even_swapped hs hK hn2 hm)).elim
  · have hmod : (p % 8 = 3 ∨ p % 8 = 5) ∨ (p % 8 = 1 ∨ p % 8 = 7) := by
      obtain ⟨k,hk⟩ := ho
      omega
    have hremain : p % 8 = 3 ∨ p % 8 = 5 := by
      rcases hmod with hh | hh
      · exact hh
      · exact (hN (h.normalizes_residual_of_odd_large hn hs hK hp ho hm hh)).elim
    exact ⟨H,P,I,p,h,hs,hK,hp,ho,hm,hremain,h.enlargement_two_core_ne_bot hn,
      h.residual_lt_enlargedResidual hN,h.intersection_relIndex_le_two hn⟩

/-- The remaining model alternative with every original source guard retained. -/
def SourceSmallOddPrimeEnlargement (D : FundamentalSetup KnownSimple.IsKnownSimple T L) : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard ∧
    D.IsMinimalFullModule ∧ D.fullModule = D.moduleSubgroup ∧
    ¬ (T : Subgroup G) ≤ normalizer (L : Set G) ∧
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) ∧
    Selection.BinaryThreeNatural D ∧ sourceMovedFixed D = ⊥ ∧
    ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G) ∧
    SmallOddPrimeEnlargement D

/-- Only the original small-congruence source configuration can obstruct the normalizer. -/
theorem stabilizerNormalizerAt_or_smallOddPrimeEnlargement
    (hchoice : Selection.ModuleChoiceAt T) :
    StabilizerNormalizerAt T ∨
      ∃ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
        SourceSmallOddPrimeEnlargement D := by
  classical
  by_cases he : ∃ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
      SourceSmallOddPrimeEnlargement D
  · exact Or.inr he
  · left
    apply stabilizerNormalizerAt_of_moduleChoice_and_parabolic_normalizers hchoice
    intro L D hmany hmin hfull hn hna hmodel hzero hJ H hH
    by_contra hN
    exact he ⟨L,D,hmany,hmin,hfull,hn,hna,hmodel,hzero,hJ,
      smallOddPrimeEnlargement_of_not_normalizes hH hn hN⟩

/-- The completed containing-pair proof gives the same reduction for literal half-join uniqueness. -/
theorem halfSylowUniqueAt_or_smallOddPrimeEnlargement
    (hchoice : Selection.ModuleChoiceAt T) :
    HalfSylowUniqueAt T ∨
      ∃ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
        SourceSmallOddPrimeEnlargement D := by
  rcases stabilizerNormalizerAt_or_smallOddPrimeEnlargement hchoice with hN | hc
  · exact Or.inl (halfSylowUniqueAt_of_moduleChoice_and_normalizer hchoice hN)
  · exact Or.inr hc

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
