module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.Constrained

/-!
# Only full J₄ components remain in Mathieu Hall faithfulness

The constrained C.2.7 branch is impossible on the actual normal Mathieu
residual. Failure of residual uniqueness therefore supplies an ordinary
normal component with central quotient J₄. The literal Hall obstruction
has only this ambient pushing-up case or the original odd-normalizer J₄
case. All residual maps, component placements and ambient witnesses are
retained; neither of the distinct J₄ centralizer arguments is assumed.

Source: Aschbacher--Smith, 4.2.13, pp.611--612, and 4.4.3,4.4.14,
pp.623--625.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape

/-- The full original pushing-up configuration with its ordinary J₄ component. -/
@[expose] def MathieuPushingUpJankoCase {G : Type*} [Group G] [Finite G]
    (L V A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G, Witness L V A J H W ∧
    ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (normalizer (L : Set G)).subgroupOf H ∧
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
      ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
      F.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K ∧
      Nonempty ((K ⧸ center K) ≃* Janko4.Model)

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Exclude the constrained branch on the unchanged residual witnesses. -/
theorem sourceOrbit_mathieu_pushingUp_janko_of_component
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    {A : Subgroup G} (hc : MathieuPushingUpComponentCase L V A) :
    MathieuPushingUpJankoCase L V A := by
  obtain ⟨J,H,W,hw,hf,K,hK,hq,hout,hn,hcases⟩ := hc
  rcases hcases with ⟨ho,hn,hF,hW,he⟩ | ⟨hcon,hinput,hmodel⟩
  · exact ⟨J,H,W,hw,hf,K,ho,hn,hout,hF,hW,he⟩
  · exact (D.sourceOrbit_mathieu_no_constrained_pushingUp h hm hw K hK hq hout hcon).elim

/-- Failure of uniqueness now forces the ordinary J₄ ambient case alone. -/
theorem sourceOrbit_mathieu_pushingUp_janko
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (ho : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    MathieuPushingUpJankoCase L V A :=
  D.sourceOrbit_mathieu_pushingUp_janko_of_component h.toHypothesis1221 hm
    (D.sourceOrbit_mathieu_pushingUp_component h hmany hV hnon hm A hAN hcomm ho hAV hnot)

set_option maxHeartbeats 400000 in
/-- A nonfaithful literal Hall actor produces one of the two original J₄
configurations. No constrained component, uniqueness premise, or local model
placement callback remains in this reduction. -/
theorem sourceOrbit_mathieu_hall_two_janko_configurations
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
      (MathieuPushingUpJankoCase L V A ∨
        (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
          MathieuJankoComponentCase L V A (D.orbitComponent ⧸ center D.orbitComponent))) := by
  have hobs :=
    @sourceOrbit_mathieu_hall_pushingUp_obstruction G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  obtain ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout,hcase⟩ := hobs
  refine ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout,?_⟩
  exact hcase.imp (D.sourceOrbit_mathieu_pushingUp_janko_of_component h.toHypothesis1221 hm) id

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
