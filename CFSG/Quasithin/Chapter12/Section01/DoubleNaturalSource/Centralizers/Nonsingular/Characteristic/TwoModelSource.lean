module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.MathieuComponent
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Parabolic.Source

/-!
# The two remaining nonsingular component models

The literal Mathieu exclusion leaves L5(2) in degree four and J4 in either
degree. Both the component alternative and its actual centralizer/closure
application retain the original relative normality, containing residual,
rank bound, C.2.7 input and fixed-space obligation. This is checked progress,
not an unconditional proof of12.1.1 or degree-five weak closure.

The remaining component, parabolic and closure arguments stay with
qt-d-double-natural-centralizers. Pure fusion remains with
qt-d-double-natural-pure-fusion, and qt-d-1222-double-natural retains final
source assembly and all independent earlier-source obligations.
Source: Aschbacher--Smith12.1.1--3, printed pp.788--789.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter1
open RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Only the actual L5(2) and J4 central quotients remain. -/
theorem doubleNatural_adapted_component_two_models
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        (n = 4 ∧ ClassicalGroup.IsPSL (K ⧸ center K) 5 2) ∨
        Nonempty ((K ⧸ center K) ≃* Janko4.Model) := by
  let := D.doubledOrbit_elementary h
  intro S w hw K hK
  rcases D.doubleNatural_adapted_component_three_models h B S w hw K hK with
    ⟨hn,hl | hm⟩ | hj
  · exact .inl ⟨hn,hl⟩
  · subst n
    exact (D.doubleNatural_four_adapted_component_not_mathieu h B S w hw K hK hm).elim
  · exact .inr hj

/-- The characteristic-two obstruction keeps its original relatively normal component. -/
theorem doubleNatural_adapted_characteristic_or_two_models
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) ∨
      ∃ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) ∧
        (K.subgroupOf (B.pointCentralizer w)).Normal ∧ B.pointResidual w ≤ K ∧
        2*(n-1) ≤ primeRank 2 (K ⧸ center K) ∧
        ((n = 4 ∧ ClassicalGroup.IsPSL (K ⧸ center K) 5 2) ∨
          Nonempty ((K ⧸ center K) ≃* Janko4.Model)) := by
  let := D.doubledOrbit_elementary h
  intro S w hw
  rcases D.doubleNatural_adapted_characteristic_or_three_models h B S w hw with
    hc | ⟨K,hK,hn,hRK,hr,_⟩
  · exact .inl hc
  · exact .inr ⟨K,hK,hn,hRK,hr,
      D.doubleNatural_adapted_component_two_models h B S w hw K hK⟩

/-- The nonsingular and degree-five closure consumer with M24 discharged and
all remaining component and C.2.7 fixed-space premises retained. -/
theorem doubleNatural_nonsingular_controls_of_two_models_C27_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    (∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        (K.subgroupOf (B.pointCentralizer w)).Normal → B.pointResidual w ≤ K →
        2*(n-1) ≤ primeRank 2 (K ⧸ center K) →
        ((n = 4 ∧ ClassicalGroup.IsPSL (K ⧸ center K) 5 2) ∨
          Nonempty ((K ⧸ center K) ≃* Janko4.Model)) → False) →
    (∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
      ¬ ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
      ¬ B.pointCentralizer w ≤ normalizer (L : Set G) →
      let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
      ∀ K : Subgroup G, (K.subgroupOf (B.pointCentralizer w)).Normal →
        B.pointResidual w < K →
        Input KnownSimple.IsKnownSimple (B.pointCentralizer w) Q (B.localPointCentralizer w) K →
        KernelConclusion K Q → OffenderConclusion K Q →
        ((starImage K Q (B.pointResidual w)).subgroupOf
          (starM K Q (B.localPointCentralizer w))).Normal →
        Nonempty (((starImage K Q (B.pointResidual w)) ⧸
          pCore 2 (starImage K Q (B.pointResidual w))) ≃*
          Matrix.ProjectiveSpecialLinearGroup (Fin (n-1)) (ZMod 2)) →
        B.pointResidual w ≤ centralizer ((starV K Q).map (K ⊔ Q).subtype ⊓
          centralizer (B.pointSylow w : Set G) : Set G)) →
    B.NonsingularCentralizers ∧
      (n : ℕ∞) ≤ ChapterE.globalR (componentOrbit V (T : Subgroup G)) ∧
      (n = 5 → 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) := by
  let := D.doubledOrbit_elementary h
  intro hmodels hparabolic
  apply D.doubleNatural_nonsingular_controls_of_three_models_C27_of_many h hmany B _ hparabolic
  intro S w hw K hK hn hRK hr _
  exact hmodels S w hw K hK hn hRK hr
    (D.doubleNatural_adapted_component_two_models h B S w hw K hK)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
