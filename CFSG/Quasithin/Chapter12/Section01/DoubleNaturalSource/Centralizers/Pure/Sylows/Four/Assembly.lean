module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Swapped.DiagonalExclusion
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Core.Assembly

/-!
# Ambient Sylows, centralizer orders and fusion after the swapped exclusion

The dimension-four ambient Sylow now follows from the exact fixed-subgroup
MS consequence. The permitted earlier weak closure supplies dimension five.
The existing transports then give the three centralizer orders and pure
fusion in both degrees, with the original points and dual summands retained.

The final theorem feeds the actual two-core and abelian-closure argument.
Its remaining characteristic-two premise is the source component exclusion
in 12.1.6, still owned by `qt-d-double-natural-pure-fusion`. The definition
`MarkedOmegaFixed` states exactly the MS consequence retained by
`qt-rank-two-ms93` and final `qt-d-double-natural-centralizers`. Neither
remaining premise is asserted proved by this module.
Source: Aschbacher--Smith 12.1.4--6, printed pp.790--792.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  {B : DoubledBranch T L V n}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]

/-- The exact source-specific MS consequence needed in the contrary marked
ambient-Sylow branch. Its construction remains with the original MS producer. -/
@[expose] def MarkedOmegaFixed (S : B.SourceModel)
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G)) : Prop :=
  ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
    ∀ hp : (B.coordinates w).toAdd.2 = 0,
    (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
      S.setup.naturalFixed (S.setup.naturalSylowNormalizer
        ((T.subtype hTM).mapSurjective B.actionProjection_surjective)) →
    ¬ Chapter1.IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      omegaCenterIn (B.pointSylow w) ⊓ centralizer (L : Set G) ≠ ⊥

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Source 12.1.4 with its original fixed-subgroup MS consequence explicit. -/
theorem doubleNatural_four_markedAmbientSylow_of_many_of_omega_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, S.MarkedOmegaFixed D.sylow_normalizes_component →
      S.MarkedAmbientSylow D.sylow_normalizes_component := by
  let := D.doubledOrbit_elementary h
  intro S hfixed w hw hp hfix
  rw [← S.marked_centralizer_eq D.sylow_normalizes_component w hw hp hfix]
  exact D.doubleNatural_four_marked_pure_sylow_of_many_of_omega_fixed
    h hmany B S w hw hp hfix (hfixed w hw hp hfix)

/-- The marked ambient Sylow, all three centralizer orders and pure fusion
in dimension four, conditional only on the original earlier MS consequence. -/
theorem doubleNatural_four_pure_orders_sylows_fusion_of_many_of_omega_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, B.NonsingularCentralizers →
      S.MarkedOmegaFixed D.sylow_normalizes_component →
      B.CentralizerOrders ∧ B.PurePointSylows ∧ B.PureFusion := by
  let := D.doubledOrbit_elementary h
  intro S hns hfixed
  exact D.doubleNatural_pure_orders_sylows_fusion_of_marked_of_many h hmany B S hns
    (D.doubleNatural_four_markedAmbientSylow_of_many_of_omega_fixed h hmany B S hfixed)

/-- The marked ambient Sylow for both source degrees, using earlier weak
closure only in dimension five and the precise MS consequence only in four. -/
theorem doubleNatural_markedAmbientSylow_of_many_of_omega_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n)
    (hW : n = 5 → 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, (n = 4 → S.MarkedOmegaFixed D.sylow_normalizes_component) →
      S.MarkedAmbientSylow D.sylow_normalizes_component := by
  let := D.doubledOrbit_elementary h
  intro S hfixed
  rcases B.degree with rfl | rfl
  · exact D.doubleNatural_four_markedAmbientSylow_of_many_of_omega_fixed h hmany B S (hfixed rfl)
  · intro w hw hp hfix
    exact (D.doubleNatural_five_marked_pure_sylow_of_many h hmany B (hW rfl) S w hw hp hfix).2

/-- Both source degrees now have ambient point Sylows, the three distinct
centralizer orders and pure fusion, with only the genuine earlier inputs. -/
theorem doubleNatural_pure_orders_sylows_fusion_of_many_of_omega_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n)
    (hW : n = 5 → 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, B.NonsingularCentralizers →
      (n = 4 → S.MarkedOmegaFixed D.sylow_normalizes_component) →
      B.CentralizerOrders ∧ B.PurePointSylows ∧ B.PureFusion := by
  let := D.doubledOrbit_elementary h
  intro S hns hfixed
  exact D.doubleNatural_pure_orders_sylows_fusion_of_marked_of_many h hmany B S hns
    (D.doubleNatural_markedAmbientSylow_of_many_of_omega_fixed h hmany B hW S hfixed)

/-- The completed Sylow and order argument feeds the original two-core and
abelian-closure consumer. Component exclusion for 12.1.6 remains explicit. -/
theorem doubleNatural_pure_conclusions_of_characteristicTwo_of_many_of_omega_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n)
    (hW : n = 5 → 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, B.NonsingularCentralizers →
      (n = 4 → S.MarkedOmegaFixed D.sylow_normalizes_component) →
      (∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
        (B.coordinates w).toAdd.2 = 0 →
        generalizedFitting (centralizer ({(w : G)} : Set G)) =
          pCore 2 (centralizer ({(w : G)} : Set G))) →
      B.PureFusion ∧ B.PureCentralizerClosureAbelian ∧ B.PureIntersectionCentralizes := by
  let := D.doubledOrbit_elementary h
  intro S hns hfixed hc
  obtain ⟨ho,hs,_⟩ := D.doubleNatural_pure_orders_sylows_fusion_of_many_of_omega_fixed
    h hmany B hW S hns hfixed
  exact D.doubleNatural_pure_conclusions_of_characteristicTwo_of_many h hmany B S ho hs hns hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
