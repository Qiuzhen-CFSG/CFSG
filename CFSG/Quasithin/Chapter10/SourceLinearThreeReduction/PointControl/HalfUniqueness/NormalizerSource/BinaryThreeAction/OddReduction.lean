module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.Even

/-!
# The remaining odd-prime enlargement, with the source mod-eight split

The even-degree binary PSL₂ calculation now closes that entire normalizer
branch. A failure of normalization therefore constructs the original
swapped Sylow input with an odd-prime PSL₂ factor. The literal R=T₁∩K,
nontrivial enlargement two-core and quotient Sylow index remain available.
The congruence alternatives are retained separately, as required by the
source's distinct radical and two-S₄ arguments.

The final applications connect this strictly smaller obstruction to the
original StabilizerNormalizerAt and literal half-join uniqueness contracts.
These alternatives do not assert the finished source theorem. The odd-prime
normalizer proof and its final discharge stay with this same task; only
ModuleChoiceAt is external, ultimately discharged by the point-control owner.
Source: Aschbacher--Smith 10.2.5--6, printed pp.748--749.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding BinaryThreeAction.Parabolics
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The actual remaining source configuration, including both mod-eight rows. -/
def OddPrimeEnlargement (D : FundamentalSetup KnownSimple.IsKnownSimple T L) : Prop :=
  ∃ (H P I : Subgroup G) (p : ℕ), Data D H ∧
    SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) (residual H) P
      (enlargement T L H) I ∧
    enlargedResidual T L H = componentOrbit I (T : Subgroup G) ∧
    p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (XiQuotient I) 2 p ∧
    ((p % 8 = 3 ∨ p % 8 = 5) ∨ (p % 8 = 1 ∨ p % 8 = 7)) ∧
    (enlargement T L H).pCoreIn 2 ≠ ⊥ ∧
    residual H < enlargedResidual T L H ∧
    (stabilizerIntersection T L H).relIndex ((T : Subgroup G) ⊓ enlargedResidual T L H) ≤ 2

/-- Every escaping original residual now gives an actual odd-prime factor. -/
theorem oddPrimeEnlargement_of_not_normalizes
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {H : Subgroup G}
    (h : Data D H) (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hN : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      normalizer (residual H : Set G)) : OddPrimeEnlargement D := by
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
    exact ⟨H,P,I,p,h,hs,hK,hp,ho,hm,hmod,h.enlargement_two_core_ne_bot hn,
      h.residual_lt_enlargedResidual hN,h.intersection_relIndex_le_two hn⟩

/-- Apply the even-rank-one proof to the two actual source parabolics. -/
theorem binary_three_normalizer_or_oddPrimeEnlargement
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hmodel : Selection.BinaryThreeNatural D) (hzero : sourceMovedFixed D = ⊥)
    (hfull : D.fullModule = D.moduleSubgroup)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤ D.maximalLocal ∨
      OddPrimeEnlargement D := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  obtain ⟨H₁,H₂,h₁,h₂,_,hgen⟩ := exists_pair D hmodel hzero hfull ht htn hcross
  by_cases hN₁ : normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      normalizer (residual H₁ : Set G)
  · by_cases hN₂ : normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
        normalizer (residual H₂ : Set G)
    · exact Or.inl (normalizer_le_of_normalizes_pair h₁ h₂ hgen hN₁ hN₂)
    · exact Or.inr (oddPrimeEnlargement_of_not_normalizes h₂ hn hN₂)
  · exact Or.inr (oddPrimeEnlargement_of_not_normalizes h₁ hn hN₁)

/-- Only the original odd-prime configurations can still obstruct 10.2.5. -/
theorem stabilizerNormalizerAt_or_oddPrimeEnlargement
    (hchoice : Selection.ModuleChoiceAt T) :
    StabilizerNormalizerAt T ∨
      ∃ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
        OddPrimeEnlargement D := by
  classical
  by_cases he : ∃ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
      OddPrimeEnlargement D
  · exact Or.inr he
  · left
    apply stabilizerNormalizerAt_of_moduleChoice_and_parabolic_normalizers hchoice
    intro L D _ _ _ hn _ _ _ _ H hH
    by_contra hN
    exact he ⟨L,D,oddPrimeEnlargement_of_not_normalizes hH hn hN⟩

/-- The completed containing-pair argument gives the same reduction for
uniqueness of the literal half-join L₀N_T(L). -/
theorem halfSylowUniqueAt_or_oddPrimeEnlargement
    (hchoice : Selection.ModuleChoiceAt T) :
    HalfSylowUniqueAt T ∨
      ∃ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
        OddPrimeEnlargement D := by
  rcases stabilizerNormalizerAt_or_oddPrimeEnlargement hchoice with hN | hc
  · exact Or.inl (halfSylowUniqueAt_of_moduleChoice_and_normalizer hchoice hN)
  · exact Or.inr hc

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
