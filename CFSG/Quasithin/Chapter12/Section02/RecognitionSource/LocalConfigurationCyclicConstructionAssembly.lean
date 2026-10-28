module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicConstructionOrbit
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicAssembly

/-!
# Assembly of the invariant odd-subgroup construction

The proved orbit calculation fills the elementary, core, normality,
generation, intersection and commutator clauses of the original invariant
odd-analysis record. The initial pair and the invariant-Sylow selection
remain explicit producers. The latter must establish its Frattini and
residual claims on the literal subgroups; it may reselect P, U and g.

The final application supplies oddStep to the existing cyclic assembly,
leaving the independent prime-order exclusion and block recognition with
their owners. No existence assertion is made without the two producers.
Source: Aschbacher--Smith, 12.2.21--24, printed pp.802--804.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
variable {G : Type*} [Group G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d p : ℕ} {g v : G}

/-- The elementary H-orbit completes the invariant choice to the original
record, with W still distinct from the pair core U. -/
theorem CyclicInvariantSelection.invariantOddLocalAnalysis
    (S : CyclicInvariantSelection T L V d p H P U g v)
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V) :
    InvariantOddLocalAnalysis T L V d p H P U
      (componentOrbit (H.pCoreIn 2 ⊓ V) H) g v := by
  let B := S.toCyclicConstructionSeed
  exact {
    hstar := S.hstar
    prime := S.prime
    odd_prime := S.odd_prime
    pgroup := S.pgroup
    alternatives := S.alternatives
    escapes := S.escapes
    overgroup := S.overgroup
    elementary := B.orbit_elementary D hTV hTI
    in_core := CyclicConstructionSeed.orbit_in_core H V
    normalizes := le_normalizer_componentOrbit _ _
    generated := B.orbit_eq D A hTV
    residual := S.residual
    moved := B.orbit_moved D A hTV
    intersection := B.orbit_intersection D A
    transvections := B.orbit_transvections D A hTV
    action_kernel := S.action_kernel
    hyperplane := S.hyperplane
    frattini_normalizes := S.frattini_normalizes
    frattini_intersection := S.frattini_intersection
    generator_mem := S.generator_mem
    generator_order := S.generator_order
    inverter_mem := S.inverter_mem
    inverter_outside := S.inverter_outside
    inverts_generator := S.inverts_generator
    inverter_normalizes := S.inverter_normalizes
    inverts_frattini_quotient := S.inverts_frattini_quotient
    pair_core := S.pair_core
    pair_generated := S.pair_generated
    pair_disjoint := S.pair_disjoint
    core_generated := S.core_generated
    pair_fixed := S.pair_fixed }

/-- The two independent producers may run with the initial pair as an
explicit input to the selection proof. Their premises are discharged here. -/
theorem invariantOddLocalAnalysis_of_construction_steps
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V)
    (seedStep : ∃ p H P U g, CyclicConstructionSeed T L V d p H P U g)
    (selectionStep : ∀ p H P U g, CyclicConstructionSeed T L V d p H P U g →
      ∃ P' U' g' v, CyclicInvariantSelection T L V d p H P' U' g' v) :
    ∃ p H P U W g v, InvariantOddLocalAnalysis T L V d p H P U W g v := by
  obtain ⟨p, H, P, U, g, S⟩ := seedStep
  obtain ⟨P', U', g', v, R⟩ := selectionStep p H P U g S
  exact ⟨p, H, P', U', componentOrbit (H.pCoreIn 2 ⊓ V) H, g', v,
    R.invariantOddLocalAnalysis D A hTV hTI⟩

/-- The actual oddStep application in the published cyclic/block assembly.
The seed, invariant selection, noncyclic exclusion and block recognition
are explicit source obligations, not inferred from their output records. -/
theorem cyclicLocalAnalysis_of_construction_steps [Finite G]
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V)
    (seedStep : ∃ p H P U g, CyclicConstructionSeed T L V d p H P U g)
    (selectionStep : ∀ p H P U g, CyclicConstructionSeed T L V d p H P U g →
      ∃ P' U' g' v, CyclicInvariantSelection T L V d p H P' U' g' v)
    (primeStep : ∀ p H P U W g v,
      InvariantOddLocalAnalysis T L V d p H P U W g v → Nat.card P = p)
    (blockStep : ∀ p H P U W g v,
      InvariantOddLocalAnalysis T L V d p H P U W g v → Nat.card P = p →
      ⁅(T : Subgroup G) ⊓ centralizer (V : Set G), U⁆ ≤ U ⊓ V →
      ChapterC.IsLinearTwoBlock L d) :
    ∃ H P U, CyclicLocalAnalysis T L V d H P U :=
  cyclicLocalAnalysis_of_invariant_odd_steps hTV
    (invariantOddLocalAnalysis_of_construction_steps D A hTV hTI seedStep selectionStep)
    primeStep blockStep

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
