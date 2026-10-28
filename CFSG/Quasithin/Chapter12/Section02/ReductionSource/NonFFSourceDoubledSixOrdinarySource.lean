module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSixConstrainedExcluded
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSixC28Source

/-!
# The original A₆ Hall reduction after the constrained exclusion

The reciprocal witness now has an ordinary component containing the actual
intersection residual and the entire original doubled orbit. The original
Hall actor therefore retains two ordinary alternatives: the outside component
in its normalizer, or this ordinary reciprocal component. Neither ordinary
alternative is asserted impossible here.
Source: Aschbacher--Smith C.3.2--4, C.4.8 and 7.3.4, pp.149--154,699,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter4 Chapter4.Section04
open Chapter4.Section02.RankOneReciprocalEscape
open ChapterE ChapterE.Section06.FixedPointBounds
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original A₆ reciprocal branch has an ordinary component containing
the whole source orbit and its original intersection residual. -/
theorem sourceOrbit_six_reciprocal_ordinary_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6)))
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    ∃ J H U : Subgroup G, Witness L V A J H U ∧
      D.sourceOrbit ≤ J.pCoreIn 2 ∧
      J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L ∧
      let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
        (H ⊓ normalizer (L : Set G)) F (J.pCoreIn 2) D.sourceOrbit ∧
      ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
        ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
        F.subgroupOf H ≤ K ∧ D.sourceOrbit.subgroupOf H ≤ K := by
  obtain ⟨J,H,U,hw,hWJ,hJC,hc,hescape⟩ :=
    D.sourceOrbit_six_reciprocal_hypothesisC28 h hd hmodel A hAC ho hnot
  have he : ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H :=
    fun hh => hescape (hh.trans (subgroupOf_mono H inf_le_right))
  obtain ⟨K,hK,hq,hout,_,hcases⟩ := hc.ordinary_or_constrained_escape he
  rcases hcases with hordinary | hfK
  · have hFK := hc.ordinary_component_contains_original K hordinary
    have hn := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp
      hw.2.2.2.2.2.2.2.2.1
    have hWF := hc.module_le
    rw [hc.normalized_span_eq hn] at hWF
    exact ⟨J,H,U,hw,hWJ,hJC,hc,K,hordinary,hc.ordinary_component_normal K hordinary,
      hout,hFK,(subgroupOf_mono H hWF).trans hFK⟩
  · exact (D.sourceOrbit_six_witness_not_constrained
      h hd hmodel hw hWJ hJC K hK hq hout hfK).elim

/-- At the actual original Hall actor, both surviving alternatives are
ordinary; no uniqueness or radical-containment premise is added. -/
theorem sourceOrbit_six_hall_ordinary_alternatives
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6))) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      1 < generationParameter H ∧
      ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
        IsElementaryAbelian p A ∧ A ≤ H ∧ A ≤ sectionCentralizer L ∧
        A ≤ centralizer (D.sourceOrbit : Set G) ∧
        (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
        ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
    ((UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
      ∃ K : Subgroup (normalizer (A : Set G)),
        IsComponent (normalizer (A : Set G)) K ∧
        ⁅K,D.sourceOrbit.subgroupOf (normalizer (A : Set G))⁆ = K ∧
        ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
        pCore 2 K = ⊥ ∧ IsQuasithin K ∧ KnownSimple.IsKnownSimple (K ⧸ center K) ∧
        (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
          normalizer (K : Set (normalizer (A : Set G))) ∧
        D.sourceOrbit.subgroupOf (normalizer (A : Set G)) ≤
          normalizer (K : Set (normalizer (A : Set G)))) ∨
     (¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
      ∃ J P U : Subgroup G, Witness L V A J P U ∧
        D.sourceOrbit ≤ J.pCoreIn 2 ∧
        J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L ∧
        let F := (solvableResidual (L ⊓ P : Subgroup G)).map (L ⊓ P).subtype
        ChapterC.HypothesisC28 KnownSimple.IsKnownSimple P
          (P ⊓ normalizer (L : Set G)) F (J.pCoreIn 2) D.sourceOrbit ∧
        ∃ K : Subgroup P, IsComponent P K ∧ K.Normal ∧
          ¬ K ≤ (P ⊓ normalizer (L : Set G)).subgroupOf P ∧
          F.subgroupOf P ≤ K ∧ D.sourceOrbit.subgroupOf P ≤ K)) := by
  obtain ⟨H,hH,hgen,p,A,hp,ho,hne,he,hAH,hAL,hAC,hAT,hout,hcases⟩ :=
    D.sourceOrbit_six_hall_c28_or_component h hd hmany hnon hmodel
  refine ⟨H,hH,hgen,p,A,hp,ho,hne,he,hAH,hAL,hAC,hAT,hout,?_⟩
  rcases hcases with hc | ⟨hnot,_⟩
  · exact Or.inl hc
  · let : Fact p.Prime := ⟨hp⟩
    let := he
    have hodd : Odd (Nat.card A) := by
      obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
      rw [hn]
      exact ho.pow
    exact Or.inr ⟨hnot,D.sourceOrbit_six_reciprocal_ordinary_component
      h hd hmodel A hAC hodd hnot⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
