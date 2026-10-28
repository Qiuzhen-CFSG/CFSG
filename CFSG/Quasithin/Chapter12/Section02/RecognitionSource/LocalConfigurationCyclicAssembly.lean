module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicPair
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationAssembly

/-!
# Assembly of the cyclic branch from its three source obligations

The odd-subgroup construction and noncyclic exclusion supply the prime-order
pair. Its proved core-displacement bound feeds the linear-block producer.
The resulting cyclic analysis is used in the original local configuration
assembly, on the unchanged T, L and V. These three producers remain explicit
and must be discharged before claiming 12.2.21--24.
Source: Aschbacher--Smith, 12.2.21--26, printed pp.802--806.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {d : ℕ}

/-- Assembly on the original chosen module. The three remaining producers
construct 12.2.21--22, prove 12.2.23, and turn the core displacement into
12.2.24. Each producer may use the original ambient hypotheses through its
closure. This theorem does not assert any of those three source results. -/
theorem cyclicLocalAnalysis_of_invariant_odd_steps
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (oddStep : ∃ p H P U W g v,
      InvariantOddLocalAnalysis T L V d p H P U W g v)
    (primeStep : ∀ p H P U W g v,
      InvariantOddLocalAnalysis T L V d p H P U W g v → Nat.card P = p)
    (blockStep : ∀ p H P U W g v,
      InvariantOddLocalAnalysis T L V d p H P U W g v → Nat.card P = p →
      ⁅(T : Subgroup G) ⊓ centralizer (V : Set G), U⁆ ≤ U ⊓ V →
      ChapterC.IsLinearTwoBlock L d) :
    ∃ H P U, CyclicLocalAnalysis T L V d H P U := by
  obtain ⟨p, H, P, U, W, g, v, S⟩ := oddStep
  have hc := primeStep p H P U W g v S
  exact ⟨H, P, U, S.cyclic_of_prime_order hc hTV
    (blockStep p H P U W g v S hc (S.core_displacement_of_prime_order hc hTV))⟩

/-- The actual `cyclicStep` application in the parent local configuration
assembly. Construction, noncyclic exclusion and block recognition remain
explicit; final discharge stays with the cyclic-branch owner. -/
theorem localConfiguration_of_invariant_odd_steps
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (naturalStep : NoEscape L V → IsTISubgroup V →
      ∃ d, NaturalLocalAnalysis T L V d)
    (oddStep : ∀ d, NaturalLocalAnalysis T L V d → NoEscape L V → IsTISubgroup V →
      ∃ p H P U W g v, InvariantOddLocalAnalysis T L V d p H P U W g v)
    (primeStep : ∀ d p H P U W g v, NaturalLocalAnalysis T L V d →
      InvariantOddLocalAnalysis T L V d p H P U W g v →
      NoEscape L V → IsTISubgroup V → Nat.card P = p)
    (blockStep : ∀ d p H P U W g v, NaturalLocalAnalysis T L V d →
      InvariantOddLocalAnalysis T L V d p H P U W g v → Nat.card P = p →
      ⁅(T : Subgroup G) ⊓ centralizer (V : Set G), U⁆ ≤ U ⊓ V →
      NoEscape L V → IsTISubgroup V → ChapterC.IsLinearTwoBlock L d)
    (rigidityStep : ∀ d H P U, NaturalLocalAnalysis T L V d →
      CyclicLocalAnalysis T L V d H P U → NoEscape L V → IsTISubgroup V →
      (d = 3 ∨ d = 4) ∧ normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧
        ParabolicSplitting T L V U)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V) :
    ∃ d, SplitLinearConfiguration L V d := by
  have hTV := ((structural G T L h).2.2 V D).1
  apply localConfiguration_of_source_steps D naturalStep _ rigidityStep hnone hTI
  intro d A hn ht
  exact cyclicLocalAnalysis_of_invariant_odd_steps hTV (oddStep d A hn ht)
    (fun p H P U W g v S => primeStep d p H P U W g v A S hn ht)
    (fun p H P U W g v S hc hd => blockStep d p H P U W g v A S hc hd hn ht)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

