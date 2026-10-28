module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.SporadicSylow
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Normal.PointMaximal

/-!
# The three remaining nonsingular component models

The checked normal-Sylow exclusions remove Held and Rudvalis from the
ordinary-component obstruction. The remaining central quotients are
L5(2) and M24 in degree four, or J4 in either degree. Their original relative
normality, containing residual and moving-space rank are retained.

The last theorem feeds this sharper alternative into the actual
nonsingular-centralizer, global r-bound and degree-five weak-closure
consumer. The two normal-residual branches are already discharged.
Excluding the remaining three models and the nonnormal-parabolic branch
remains with qt-d-double-natural-centralizers. The independent pure-fusion
family remains with qt-d-double-natural-pure-fusion, and
qt-d-1222-double-natural retains final source assembly. This conditional
consumer is not an unconditional proof of12.1.1.
Source: Aschbacher--Smith 12.1.1--3, printed pp.788--789.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The Held and Rudvalis exclusions leave only three actual component quotients. -/
theorem doubleNatural_adapted_component_three_models
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        (n = 4 ∧ (ClassicalGroup.IsPSL (K ⧸ center K) 5 2 ∨
          Nonempty ((K ⧸ center K) ≃* Sporadic.Mathieu.M24))) ∨
        Nonempty ((K ⧸ center K) ≃* Janko4.Model) := by
  let := D.doubledOrbit_elementary h
  intro S w hw K hK
  rcases D.doubleNatural_adapted_component_finite_models h B S w hw K hK with
    ⟨hn,hl | hm | hh | hr⟩ | hj
  · exact .inl ⟨hn,.inl hl⟩
  · exact .inl ⟨hn,.inr hm⟩
  · subst n
    exact (D.doubleNatural_four_adapted_component_not_held h B S w hw K hK hh).elim
  · subst n
    exact (D.doubleNatural_four_adapted_component_not_rudvalis h B S w hw K hK hr).elim
  · exact .inr hj

/-- The characteristic-two obstruction keeps its relatively normal containing component
and original moving-space rank, now with only L5(2), M24 and J4 quotients. -/
theorem doubleNatural_adapted_characteristic_or_three_models
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) ∨
      ∃ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) ∧
        (K.subgroupOf (B.pointCentralizer w)).Normal ∧ B.pointResidual w ≤ K ∧
        2*(n-1) ≤ primeRank 2 (K ⧸ center K) ∧
        ((n = 4 ∧ (ClassicalGroup.IsPSL (K ⧸ center K) 5 2 ∨
          Nonempty ((K ⧸ center K) ≃* Sporadic.Mathieu.M24))) ∨
        Nonempty ((K ⧸ center K) ≃* Janko4.Model)) := by
  let := D.doubledOrbit_elementary h
  intro S w hw
  rcases D.doubleNatural_adapted_characteristic_or_normal_component h B S w hw with
    hc | ⟨K,hK,hn,hRK,_⟩
  · exact .inl hc
  · exact .inr ⟨K,hK,hn,hRK,
      D.doubleNatural_adapted_component_centralQuotient_rank h B S w hw K hK,
      D.doubleNatural_adapted_component_three_models h B S w hw K hK⟩

/-- The actual nonsingular-centralizer and degree-five weak-closure consumer.
Only the three remaining component quotients and nonnormal parabolic branch
remain explicit; the normal-residual branch is already discharged. -/
theorem doubleNatural_nonsingular_controls_of_three_models_parabolic_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    (∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        (K.subgroupOf (B.pointCentralizer w)).Normal → B.pointResidual w ≤ K →
        2*(n-1) ≤ primeRank 2 (K ⧸ center K) →
        ((n = 4 ∧ (ClassicalGroup.IsPSL (K ⧸ center K) 5 2 ∨
          Nonempty ((K ⧸ center K) ≃* Sporadic.Mathieu.M24))) ∨
        Nonempty ((K ⧸ center K) ≃* Janko4.Model)) → False) →
    (∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
      ¬ ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
      ¬ B.pointCentralizer w ≤ normalizer (L : Set G) →
      B.pointResidual w ≤ centralizer (B.fixedLine : Set G)) →
    B.NonsingularCentralizers ∧
      (n : ℕ∞) ≤ ChapterE.globalR (componentOrbit V (T : Subgroup G)) ∧
      (n = 5 → 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) := by
  let := D.doubledOrbit_elementary h
  intro hmodels hparabolic
  apply D.doubleNatural_nonsingular_controls_of_characteristic_parabolic_of_many h hmany B _ hparabolic
  intro S w hw
  rcases D.doubleNatural_adapted_characteristic_or_three_models h B S w hw with
    hc | ⟨K,hK,hn,hRK,hr,hm⟩
  · exact hc
  · exact (hmodels S w hw K hK hn hRK hr hm).elim

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
