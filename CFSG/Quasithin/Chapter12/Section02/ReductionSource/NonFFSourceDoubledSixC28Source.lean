module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSixC28
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSymplecticHallReduction

/-!
# Whole-orbit C.2.8 at the original A₆ Hall actor

The original multiple-overgroup and non-FF hypotheses supply the same Hall
actor as the earlier reduction. Its reciprocal branch now retains C.2.8 on
the whole eight-dimensional orbit, including the actual radical's inclusion
in the section centralizer. The ordinary outside-component alternative and
all actual residual normalization and fixed-subgroup data are preserved.

This is source production, not an exclusion of either remaining branch.
Source: Aschbacher--Smith 4.4.6--14 and 7.3.4, printed pp.620--625,699;
C.2.8, p.147, refs/quasithin.pdf.
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

/-- The original A₆ Hall actor supplies either its moved outside component or
a literal full-orbit C.2.8 witness with reciprocal escape. -/
theorem sourceOrbit_six_hall_c28_or_component
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
        ChapterC.HypothesisC28 KnownSimple.IsKnownSimple P
          (P ⊓ normalizer (L : Set G))
          ((solvableResidual (L ⊓ P : Subgroup G)).map (L ⊓ P).subtype)
          (J.pCoreIn 2) D.sourceOrbit ∧
        ¬ (generalizedFitting (P ⧸ pCore 2 P)).comap
          (QuotientGroup.mk' (pCore 2 P)) ≤ (normalizer (L : Set G)).subgroupOf P ∧
        let F := (solvableResidual (L ⊓ P : Subgroup G)).map (L ⊓ P).subtype
        (P ⊓ normalizer (L : Set G)) ≤ normalizer (F : Set G) ∧
          D.sourceOrbit ≤ F.pCoreIn 2 ∧ D.sourceOrbit = ⁅D.sourceOrbit,F⁆ ∧
          D.sourceOrbit ⊓ centralizer (F : Set G) = ⊥)) := by
  obtain ⟨H,hH,hgen,p,A,hp,ho,hne,he,hAH,hAL,hAC,hAT,hout,hcases⟩ :=
    D.sourceOrbit_six_hall_reciprocal_or_component h hd hmany hnon hmodel
  refine ⟨H,hH,hgen,p,A,hp,ho,hne,he,hAH,hAL,hAC,hAT,hout,?_⟩
  rcases hcases with hc | ⟨hnot,_⟩
  · exact Or.inl hc
  · let : Fact p.Prime := ⟨hp⟩
    let := he
    have hodd : Odd (Nat.card A) := by
      obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
      rw [hn]
      exact ho.pow
    obtain ⟨J,P,U,hw,hWJ,hJC,hc,hescape⟩ :=
      D.sourceOrbit_six_reciprocal_hypothesisC28 h hd hmodel A hAC hodd hnot
    have hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) :=
      le_inf (hAC.trans (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd).centralizer_le) hAC
    obtain ⟨hn,_,hWF,hcomm,hfix⟩ :=
      D.sourceOrbit_whole_pushingUp_residual_data h hmany hnon hA hodd hw
    exact Or.inr ⟨hnot,J,P,U,hw,hWJ,hJC,hc,hescape,hn,hWF,hcomm,hfix⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
