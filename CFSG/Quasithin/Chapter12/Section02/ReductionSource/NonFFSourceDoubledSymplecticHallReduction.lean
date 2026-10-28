module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSymplecticPushingUp
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSymplecticSixCartan
-- Internal continuation of this owner, reusing the whole-orbit component selection.
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSymplecticOddAction

/-!
# Original Hall actors after the paired symplectic reciprocal argument

For the nonbinary row, the completed residual-uniqueness theorem removes
pushing up from the original Hall-kernel alternative. Every escaping odd
normalizer therefore supplies a component fully moved by the original
whole orbit. Its ambient embedding, two-core, known-simple central quotient,
and residual normalization are retained.

For A₆ the same Hall actor has either that component configuration or the
full reciprocal C.2.8 witness. The latter now includes the actual escape of
F*(P/O₂(P)), the whole orbit in both two-cores, commutator generation and
trivial fixed subgroup. The seed and whole orbit remain distinct.

The outside-component exclusion in both rows and the A₆ pushing-up
exclusion remain necessary for 4.4.14 and the upper weak-closure bounds;
this module does not assert either row's final numerical contradiction.
Source: Aschbacher--Smith 4.4.6--14 and 7.3.4, printed pp.620--625,699,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterE ChapterE.Section06.FixedPointBounds
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Every escaping nonbinary odd normalizer has an outside component fully
moved by the original orbit; the residual-uniqueness premise is discharged. -/
theorem sourceOrbit_symplectic_oddNormalizer_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (Representation.restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2))))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAC : A ≤ centralizer (D.sourceOrbit : Set G)) (ho : Odd (Nat.card A))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    ∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧
      ⁅K,D.sourceOrbit.subgroupOf (normalizer (A : Set G))⁆ = K ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧ IsQuasithin K ∧ KnownSimple.IsKnownSimple (K ⧸ center K) ∧
      (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))) ∧
      D.sourceOrbit.subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))) := by
  have hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) :=
    le_inf (hAC.trans (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd).centralizer_le) hAC
  apply D.sourceOrbit_whole_oddNormalizer_component_of_large h hd _ A hne hAC ho
    (D.sourceOrbit_symplectic_residual_uniqueness h hd hmany hnon F hn hmodel A hA ho) hout
  apply D.sourceOrbit_card_gt_eight_of_rank
  rw [D.sourceOrbit_symplectic_dimension h hd F hmodel]
  omega

/-- The original Hall kernel in the nonbinary row now necessarily yields an
outside component. The pushing-up branch has been excluded, not assumed away. -/
theorem sourceOrbit_symplectic_hall_escaping_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (Representation.restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2)))) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      F.degree < generationParameter H ∧
      ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
        IsElementaryAbelian p A ∧ A ≤ H ∧ A ≤ sectionCentralizer L ∧
        A ≤ centralizer (D.sourceOrbit : Set G) ∧
        (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
        ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
        UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
      ∃ K : Subgroup (normalizer (A : Set G)),
        IsComponent (normalizer (A : Set G)) K ∧
        ⁅K,D.sourceOrbit.subgroupOf (normalizer (A : Set G))⁆ = K ∧
        ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
        pCore 2 K = ⊥ ∧ IsQuasithin K ∧ KnownSimple.IsKnownSimple (K ⧸ center K) ∧
        (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
          normalizer (K : Set (normalizer (A : Set G))) ∧
        D.sourceOrbit.subgroupOf (normalizer (A : Set G)) ≤
          normalizer (K : Set (normalizer (A : Set G))) := by
  have hx := (D.sourceOrbit_symplectic_cartan_or_odd_escape h hd hmany hnon F hn hmodel).resolve_left
    (not_lt_of_ge (D.sourceOrbit_symplectic_quotientAction_nPrime_le h F hn hmodel))
  obtain ⟨H,hH,hgen,p,A,hp,ho,hne,he,hAH,hAL,hAC,hAT,hout⟩ := hx
  let : Fact p.Prime := ⟨hp⟩
  let := he
  have hodd : Odd (Nat.card A) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [hn]
    exact ho.pow
  have hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) :=
    le_inf (hAC.trans (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd).centralizer_le) hAC
  exact ⟨H,hH,hgen,p,A,hp,ho,hne,he,hAH,hAL,hAC,hAT,hout,
    D.sourceOrbit_symplectic_residual_uniqueness h hd hmany hnon F hn hmodel A hA hodd,
    D.sourceOrbit_symplectic_oddNormalizer_component h hd hmany hnon F hn hmodel A hne hAC hodd hout⟩

/-- In the A₆ row the same Hall actor has either a moved outside component,
or a full reciprocal witness with actual Fitting escape and whole-orbit
residual data. Neither remaining branch is asserted impossible here. -/
theorem sourceOrbit_six_hall_reciprocal_or_component
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
      ∃ J P W : Subgroup G, Witness L V A J P W ∧
        ¬ (generalizedFitting (P ⧸ pCore 2 P)).comap
          (QuotientGroup.mk' (pCore 2 P)) ≤ (normalizer (L : Set G)).subgroupOf P ∧
        let R := (solvableResidual (L ⊓ P : Subgroup G)).map (L ⊓ P).subtype
        (P ⊓ normalizer (L : Set G)) ≤ normalizer (R : Set G) ∧
          D.sourceOrbit ≤ J.pCoreIn 2 ∧ D.sourceOrbit ≤ R.pCoreIn 2 ∧
          D.sourceOrbit = ⁅D.sourceOrbit,R⁆ ∧
          D.sourceOrbit ⊓ centralizer (R : Set G) = ⊥)) := by
  have hx := (D.sourceOrbit_six_cartan_or_odd_escape h hd hmany hnon hmodel).resolve_left
    (not_lt_of_ge (D.sourceOrbit_six_quotientAction_nPrime_le_one h hd hmodel))
  obtain ⟨H,hH,hgen,p,A,hp,ho,hne,he,hAH,hAL,hAC,hAT,hout⟩ := hx
  let : Fact p.Prime := ⟨hp⟩
  let := he
  have hodd : Odd (Nat.card A) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [hn]
    exact ho.pow
  have hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) :=
    le_inf (hAC.trans (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd).centralizer_le) hAC
  refine ⟨H,hH,hgen,p,A,hp,ho,hne,he,hAH,hAL,hAC,hAT,hout,?_⟩
  by_cases hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))
  · refine Or.inl ⟨hu,?_⟩
    apply D.sourceOrbit_whole_oddNormalizer_component_of_large h hd _ A hne hAC hodd hu hout
    apply D.sourceOrbit_card_gt_eight_of_rank
    rw [D.sourceOrbit_six_dimension h hd hmodel]
    decide
  · obtain ⟨J,P,W,hw,he⟩ := D.sourceOrbit_six_reciprocal_escape h hmodel A hA hodd hu
    exact Or.inr ⟨hu,J,P,W,hw,he,
      D.sourceOrbit_whole_pushingUp_residual_data h hmany hnon hA hodd hw⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
