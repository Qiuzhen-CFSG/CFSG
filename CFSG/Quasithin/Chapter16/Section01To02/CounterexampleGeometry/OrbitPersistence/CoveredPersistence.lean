module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.OrbitPersistence.CoveredCore
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.OrbitPersistence.CoveredPersistence.Comparisons
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.OrbitPersistence.CoveredPersistence.FieldClassical
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.OrbitPersistence.CoveredPersistence.FieldExceptional
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.OrbitPersistence.CoveredPersistence.Unitary

/-!
# The covered Suzuki branch of component persistence

Choose an involution s in the embedded nontrivial two-core of L. The proved
covered-core result puts L among the components of C_G(s). For an involution
t in ⟨z⟩Lᵘ, apply component enlargement to s,t. The seed normalizes every
component of C_G(t), so s cannot swap two components. The proper single
component branches are excluded by their actual model endpoints.

This is the assembly step of Aschbacher–Smith 16.2.6(1), printed p.1174.
The balance, model projection of 16.1.7(3), pair exhaustion and small-index
transfer are permitted earlier source inputs. The final theorem discharges
every additional model comparison: cubic elements in the actual derived
subgroups exclude all five field families, and the checked order formula
excludes the unitary endpoint. Both Suzuki endpoints, (d) and (i), are
excluded by simplicity and the nontrivial two-core.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry
open ComponentTransfer CoveredPersistence
universe v
variable {G : Type v} [Group G] [Finite G]
variable {T : Sylow 2 G} {z : G} {L : Subgroup G} {u : G} {K : GroupClass.{v}}

namespace CounterexampleSetup
variable (c : CounterexampleSetup K T z L)
include c

/-- A member of L cannot swap two components of the new centralizer. -/
theorem not_swappedComponents_of_seed_mem
    (a134 : ComponentPairExhaustion K G) (o : TwoComponentOrbit T z L u)
    {s t : G} (hs : s ∈ L)
    (ht : t ∈ involutionContainer z L u) (ht2 : orderOf t = 2)
    (J : Subgroup G) : ¬ SwappedComponents (involutionCentralizer t) s L J := by
  rintro ⟨A, hA, hne, _, _⟩
  have hn := c.seed_normalizes_centralizer_components a134 o ht ht2 hA hs
  exact hne (show A.conjBy s = A from mem_normalizer_iff_map_conj_eq.mp hn).symm

/-- Covered persistence conditional on divisibility by three of the five
field-derived endpoints. All other model comparisons are discharged. -/
theorem coveredSuzuki_persistence_of_field_comparison
    (a134 : ComponentPairExhaustion K G) (o : TwoComponentOrbit T z L u)
    (transfer : SmallCentralizerIndexTransfer G)
    (balance : OrdinaryBalanceInput K G) (models : ProperModelInput K G)
    (fieldThree : ∀ X, FieldDerivedThreeInput X)
    (hne : pCore 2 L ≠ ⊥)
    (iso : Nonempty ((L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)) :
    ComponentPersistence z L u := by
  obtain ⟨s, hs, hs2⟩ := exists_embedded_core_involution hne
  have hsL : s ∈ L := by
    obtain ⟨s, _, rfl⟩ := hs
    exact s.property
  have hcomp := c.coveredSuzuki_core_persistence o transfer iso hs hs2
  intro t ht ht2
  have hst : Setup s t L := by
    refine ⟨hs2, ht2, hcomp, ?_⟩
    apply mem_centralizer_iff.mpr
    intro x hx
    exact mem_centralizer_iff.mp (o.container_le_centralizer c.localSetup ht) x
      ((sup_le (zpowers_le.mpr hsL) le_rfl) hx)
  rcases enlargement_structure_of_balance hst
      (ordinaryBalanceAt_of_hypothesis c.global balance hst) with
    ⟨_, hdone⟩ | hswap | ⟨hJ, hcomm, hrel, hproper⟩
  · exact hdone
  · exact (c.not_swappedComponents_of_seed_mem a134 o hsL ht ht2 _ hswap).elim
  · exact (not_properModels_of_comparisons fieldThree unitaryThree hne iso
      (models c.global s t L _ hst hJ hcomm hrel hproper)).elim

/-- The covered branch of 16.2.6(1), with every intrinsic model comparison
discharged. The remaining inputs are the permitted earlier balance, model
alternatives, component-pair exhaustion and small-index transfer statements. -/
theorem coveredSuzuki_persistence
    (a134 : ComponentPairExhaustion K G) (o : TwoComponentOrbit T z L u)
    (transfer : SmallCentralizerIndexTransfer G)
    (balance : OrdinaryBalanceInput K G) (models : ProperModelInput K G)
    (hne : pCore 2 L ≠ ⊥)
    (iso : Nonempty ((L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)) :
    ComponentPersistence z L u := by
  apply c.coveredSuzuki_persistence_of_field_comparison a134 o transfer balance models
    ?_ hne iso
  intro X
  cases X with
  | linearTwo => exact fieldDerivedThree_linearTwo
  | linearThree => exact fieldDerivedThree_linearThree
  | symplecticFour => exact fieldDerivedThree_symplecticFour
  | g2 => exact FieldDerivedThreeInput.g2
  | triality => exact FieldDerivedThreeInput.triality

end CounterexampleSetup
end CFSG.Quasithin.Chapter16.CounterexampleGeometry
end
