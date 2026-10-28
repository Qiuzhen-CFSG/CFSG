module

public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.RankTwoExclusion

/-!
# The remaining literal Mathieu Hall obstruction

Apply the rank-two exclusion to the component selected from the original
nonfaithful Hall subgroup. Retain residual uniqueness in the J₄ branch;
the other branch remains the actual maximal pushing-up configuration.
This completes the rank-two elimination in the literal Hall consumer, not
the still-needed pushing-up uniqueness or J₄/M₂₄ ambient contradiction.
Source: Aschbacher--Smith 4.4.12--14, printed pp.621--625.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

set_option maxHeartbeats 400000 in
/-- Literal Hall consumer: the rank-two local exclusions reduce every
nonfaithful original Hall subgroup to the actual pushing-up configuration
or the full J₄-cover configuration with residual uniqueness retained.
Neither remaining branch is assumed impossible, and no residual-uniqueness
or model-exclusion callback is used. -/
theorem sourceOrbit_mathieu_hall_janko_obstruction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < ChapterE.generationParameter H)
    (B : Subgroup H) (hBN : B ≤ (normalizer (L : Set G)).subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes
      (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H)))
    (hker : B.map H.subtype ⊓ sectionCentralizer L ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ H ∧ A ≤ sectionCentralizer L ∧
      A ≤ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      (PushingUpCase L V A ∨
        (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
          MathieuJankoComponentCase L V A (D.orbitComponent ⧸ center D.orbitComponent))) := by
  obtain ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout⟩ :=
    @sourceOrbit_nonfaithful_hall_escaping_actor G instG finG T L V D
      h hmany hV hnon H hH hlarge B hBN hHall hker
  let : Fact p.Prime := ⟨hp⟩
  let := he
  have hodd : Odd (Nat.card A) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [hn]
    exact ho.pow
  have hc := (le_sectionCentralizer_iff A L).mp hAC
  refine ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout,?_⟩
  by_cases hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))
  · have hcomp := D.sourceOrbit_mathieu_normal_component_of_unique h.toHypothesis1221 hV hm
      A hne (le_inf hc.1 hAV) hodd hu hout
    have hrows := D.sourceOrbit_mathieu_component_rows h.toHypothesis1221 hV hm
      A hc.1 hc.2 hodd hAV hcomp
    exact .inr ⟨hu,@sourceOrbit_mathieu_janko_component G instG finG T L V D
      h.toHypothesis1221 hm A hc.1 hc.2 hodd hAV hrows⟩
  · have hM := h.toHypothesis1221.sylow_normalized_maximal_unique D.sylow_normalizes_component
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    have hjoin : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
      ⟨hM.1,sup_le L.le_normalizer D.sylow_normalizes_component,hM.2⟩
    exact .inl (pushingUp_case_of_not_unique h.toHypothesis1221 D hjoin
      A hc.1 hc.2 hodd hAV hu)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
