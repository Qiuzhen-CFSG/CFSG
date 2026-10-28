module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalAlternating
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalOvergroupAction

/-!
# The actual A₇ image in the contrary order-four branch

The earlier Chapter 12 normalizer calculations supply both premises for the
original overgroup action. Orbit--stabilizer and the binary four-space
comparison identify its faithful image with A₇. The epimorphism below retains
the original ambient subgroup and its actual centralizer kernel.

Source: Aschbacher--Smith, 6.2.11, printed p.686. Constructing the S₅ preimage
with generation parameter two and excluding order four remain required.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ} {z : G}

/-- The source overgroup has an actual A₇ quotient on the original closure. -/
theorem source_local_four_intersection_alternating
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hcard : Nat.card (commutatorLayer T L ⊓ (centralizer ({z} : Set G)).pCoreIn 2 : Subgroup G) = 4) :
    ∃ q : LocalQuotientAction.fourOvergroup (T : Subgroup G) L z →* alternatingGroup (Fin 7),
      Function.Surjective q ∧ q.ker =
        (centralizer (sourceClosure (T : Subgroup G) L (wholeReduced T L) z : Set G)).subgroupOf
          (LocalQuotientAction.fourOvergroup (T : Subgroup G) L z) := by
  obtain ⟨hp, hNL⟩ := source_local_layer_normalizers D h h611 hnatural
  exact LocalQuotientAction.four_overgroup_alternating_quotient h611 hnatural hz ho hT hp hNL hcard

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
