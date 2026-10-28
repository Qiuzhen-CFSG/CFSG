module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.Basic
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.OrbitPersistence.CoveredCore
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.OrbitPersistence.ModelContracts
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.OrbitPersistence.CoveredPersistence
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.OrbitPersistence.FamilySieve
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.OrbitPersistence.SimpleFusion

/-!
# Orbit and persistence in the nonnormal component geometry

Starting from the nonnormal centralizer component, A.1.34(2) constructs its
two-element orbit and gives the Sylow normalizer index two. The intersection
of A.3.8(3), (E2), and 16.1.2(1) supplies the actual model alternatives,
retaining the inherited Fermat/Mersenne restrictions and the covered Sz(8)
case. Every additional model comparison and involution-fusion fact is proved.

In the rank-one cases, conjugation in the swapped factor reduces persistence
to small-index transfer. In the covered case, an involution in the embedded
two-core supplies the seed component for balance. Component normalization
excludes swapping, and the genuine model endpoints exclude proper enlargement.
Both Suzuki endpoints of 16.1.7(3), including (d), are retained in that argument.

The assembly below proves 16.2.5–16.2.6 and supplies the involution needed by
the conditional 16.2.7, with only the explicitly named earlier source inputs.
Their discharge remains with the §16.1–16.2 owner: A.1.34(2), A.3.8(3),
16.1.2(1), I.3.1–I.3.2 balance, the model projection of 16.1.7(3), and
small-centralizer-index transfer (16.1.8). No orbit, model alternative,
fusion, or persistence conclusion is assumed.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, pp.1174–1175.
-/

public section

namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry
open Subgroup Theory.GroupTheory FamilySieve ComponentTransfer CoveredPersistence
universe v
variable {G : Type v} [Group G] [Finite G] {K : GroupClass.{v}}
  {T : Sylow 2 G} {z : G} {L : Subgroup G} {u : G}

namespace CounterexampleSetup

/-- Lemma 16.2.6(1) from the earlier source inputs. The list intersection,
rank-one involution fusion, and all covered-branch comparisons are discharged. -/
theorem componentPersistence (c : CounterexampleSetup K T z L)
    (o : TwoComponentOrbit T z L u)
    (a134 : ComponentPairExhaustion K G)
    (a38 : SourceA38Three K) (s1612 : Source1612One K G)
    (transfer : SmallCentralizerIndexTransfer G)
    (balance : OrdinaryBalanceInput K G) (models : ProperModelInput K G) :
    ComponentPersistence z L u := by
  cases c.refinedAlternative a38 s1612 with
  | rank_one model =>
    exact c.componentPersistence_of_involution_fusion o transfer model.involutions_isConj
  | covered_suzuki_eight hne iso =>
    exact c.coveredSuzuki_persistence a134 o transfer balance models hne iso

/-- Construct all the witnesses and conclusions of 16.2.5–16.2.6 from the
counterexample setup and earlier source statements. The refined alternative
retains the inherited prime restrictions. The final involution lies in the
actual swapped component and can be used directly in the proof of 16.2.7. -/
theorem exists_orbit_persistence (c : CounterexampleSetup K T z L)
    (a134 : ComponentPairExhaustion K G)
    (a38 : SourceA38Three K) (s1612 : Source1612One K G)
    (transfer : SmallCentralizerIndexTransfer G)
    (balance : OrdinaryBalanceInput K G) (models : ProperModelInput K G) :
    ∃ u : G, TwoComponentOrbit T z L u ∧
      (normalizer (L : Set G)).relIndex (T : Subgroup G) = 2 ∧
      RefinedComponentAlternative L ∧ ComponentAlternative L ∧
      ComponentPersistence z L u ∧
      (pCore 2 L ≠ ⊥ →
        Nonempty ((L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1) →
        ∀ s ∈ (pCore 2 L).map L.subtype, orderOf s = 2 → IsCentralizerComponent s L) ∧
      ∃ t : G, t ∈ conjugate L u ∧ orderOf t = 2 := by
  obtain ⟨u, o, hindex, hinvolution⟩ := c.exists_orbit_with_involution a134
  have alternative := c.refinedAlternative a38 s1612
  refine ⟨u, o, hindex, alternative, alternative.to_componentAlternative,
    c.componentPersistence o a134 a38 s1612 transfer balance models, ?_, hinvolution⟩
  intro _ iso s hs hs2
  exact c.coveredSuzuki_core_persistence o transfer iso hs hs2

end CounterexampleSetup
end CFSG.Quasithin.Chapter16.CounterexampleGeometry
