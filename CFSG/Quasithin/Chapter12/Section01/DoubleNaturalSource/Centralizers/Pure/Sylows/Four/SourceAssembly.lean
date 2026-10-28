module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.SourceCriticalFour
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.SourceDistanceFourExclusion
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Assembly

/-!
# Original degree-four marked point Sylows

The contrary original marked-point Sylow source constructs a nonabelian
binary MS setup at distance four. The same original point residual has
opposing natural and dual sections, so that distance is impossible. This
proves the marked ambient Sylow and the exact marked omega consequence
without a universal MS classification premise.

The order, fusion and two-core consumers retain their separate nonsingular
centralizer, degree-five weak-closure and characteristic-two hypotheses.
Source: Aschbacher--Smith 12.1.4--6, printed pp.790--792.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual marked pure point has its original point Sylow as an ambient
Sylow of its centralizer. -/
theorem doubleNatural_four_marked_pure_sylow_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w, (S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      Chapter1.IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix
  by_contra hf
  obtain ⟨hms, e, t, hc, hb⟩ :=
    D.doubleNatural_four_pure_critical_four_source_of_many h hmany B S w hw hp hfix hf
  exact S.pure_binary_setup_distance_ne_four
    (D.doubledOrbit_normalizer_eq h B.orbit_eq) w hw hp hms e t hc hb

/-- The precise original marked omega consequence has no additional MS
classification or recognition premise. -/
theorem doubleNatural_four_markedOmegaFixed_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, S.MarkedOmegaFixed D.sylow_normalizes_component := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf
  exact (hf (D.doubleNatural_four_marked_pure_sylow_of_many h hmany B S w hw hp hfix)).elim

/-- The marked natural-summand normalizer is an ambient point Sylow in
degree four under the original source hypotheses. -/
theorem doubleNatural_four_markedAmbientSylow_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, S.MarkedAmbientSylow D.sylow_normalizes_component := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix
  rw [← S.marked_centralizer_eq D.sylow_normalizes_component w hw hp hfix]
  exact D.doubleNatural_four_marked_pure_sylow_of_many h hmany B S w hw hp hfix

/-- The original degree-four orders, point Sylows and pure fusion, retaining
only the separate nonsingular-centralizer input. -/
theorem doubleNatural_four_pure_orders_sylows_fusion_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ _S : B.SourceModel, B.NonsingularCentralizers →
      B.CentralizerOrders ∧ B.PurePointSylows ∧ B.PureFusion := by
  let := D.doubledOrbit_elementary h
  intro S hns
  exact D.doubleNatural_pure_orders_sylows_fusion_of_marked_of_many h hmany B S hns
    (D.doubleNatural_four_markedAmbientSylow_of_many h hmany B S)

/-- Both source degrees have marked ambient Sylows; only the original
degree-five weak-closure input remains. -/
theorem doubleNatural_markedAmbientSylow_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n)
    (hW : n = 5 → 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, S.MarkedAmbientSylow D.sylow_normalizes_component := by
  let := D.doubledOrbit_elementary h
  intro S
  rcases B.degree with rfl | rfl
  · exact D.doubleNatural_four_markedAmbientSylow_of_many h hmany B S
  · intro w hw hp hfix
    exact (D.doubleNatural_five_marked_pure_sylow_of_many h hmany B (hW rfl) S w hw hp hfix).2

/-- Source orders and fusion in both degrees without a marked omega callback. -/
theorem doubleNatural_pure_orders_sylows_fusion_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n)
    (hW : n = 5 → 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) :
    letI := D.doubledOrbit_elementary h
    ∀ _S : B.SourceModel, B.NonsingularCentralizers →
      B.CentralizerOrders ∧ B.PurePointSylows ∧ B.PureFusion := by
  let := D.doubledOrbit_elementary h
  intro S hns
  exact D.doubleNatural_pure_orders_sylows_fusion_of_marked_of_many h hmany B S hns
    (D.doubleNatural_markedAmbientSylow_of_many h hmany B hW S)

/-- The original core and abelian-closure consumer with the degree-four MS
duty discharged and its separate characteristic-two input preserved. -/
theorem doubleNatural_pure_conclusions_of_characteristicTwo_of_original_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n)
    (hW : n = 5 → 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) :
    letI := D.doubledOrbit_elementary h
    ∀ _S : B.SourceModel, B.NonsingularCentralizers →
      (∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
        (B.coordinates w).toAdd.2 = 0 →
        generalizedFitting (centralizer ({(w : G)} : Set G)) =
          pCore 2 (centralizer ({(w : G)} : Set G))) →
      B.PureFusion ∧ B.PureCentralizerClosureAbelian ∧ B.PureIntersectionCentralizes := by
  let := D.doubledOrbit_elementary h
  intro S hns hc
  obtain ⟨ho, hs, _⟩ := D.doubleNatural_pure_orders_sylows_fusion_of_many h hmany B hW S hns
  exact D.doubleNatural_pure_conclusions_of_characteristicTwo_of_many h hmany B S ho hs hns hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
