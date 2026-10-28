module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicConstructionSeed
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicConstructionResidual
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicConstructionAssembly
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicExclusionAssembly
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicBlock

/-!
# Cyclic-source assembly after constructing the literal seed

The seed is constructed from the permitted natural action on the original
chosen module. Its canonical orbit gives the exact residual independently
of the invariant Sylow choice. This supplies the seed producer in 12.2.22;
the proved fixed-layer exclusion and linear-block recognition are also
applied on the same original groups.

Three local arguments remain with qt-d-12213-cyclic-block: invariant Sylow
selection, the numerical extraspecial reduction, and the terminal binary
three contradiction. The theorem below retains these as explicit inputs
and does not assert completion of 12.2.21–24.
Source: Aschbacher–Smith, printed pp.802–804.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {d : ℕ}

/-- The original source hypotheses supply the constructed seed and its exact
residual. Structural1222 is used only for the actual T-normalization of V. -/
theorem exists_cyclicConstructionSeed_of_original
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (hTI : IsTISubgroup V) :
    ∃ p H P U g, CyclicConstructionSeed T L V d p H P U g ∧
      (pResidual 2 H).map H.subtype = P ⊔ componentOrbit (H.pCoreIn 2 ⊓ V) H := by
  have hTV := ((structural G T L h).2.2 V D).1
  obtain ⟨p, H, P, U, g, S⟩ := exists_cyclicConstructionSeed D A hTV hTI
  exact ⟨p, H, P, U, g, S, S.residual D A hTV⟩

/-- The actual selection consumer, with the seed existence premise discharged. -/
theorem invariantOddLocalAnalysis_of_selection
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V)
    (selectionStep : ∀ p H P U g, CyclicConstructionSeed T L V d p H P U g →
      ∃ P' U' g' v, CyclicInvariantSelection T L V d p H P' U' g' v) :
    ∃ p H P U W g v, InvariantOddLocalAnalysis T L V d p H P U W g v :=
  invariantOddLocalAnalysis_of_construction_steps D A hT hTI
    (exists_cyclicConstructionSeed D A hT hTI) selectionStep

/-- Discharge the seed, fixed-layer and block premises in the cyclicStep
consumer. All remaining local source obligations are explicit. -/
theorem cyclicLocalAnalysis_of_selection_and_extraspecial_steps
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (selectionStep : ∀ p H P U g, CyclicConstructionSeed T L V d p H P U g →
      ∃ P' U' g' v, CyclicInvariantSelection T L V d p H P' U' g' v)
    (numerical : ∀ p H P U W g v,
      InvariantOddLocalAnalysis T L V d p H P U W g v →
      IsExtraspecial p P → Nat.card P = p ^ 3 → Monoid.exponent P = p →
      W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥ →
      p = 3 ∧ d = 3 ∧ Nat.card W = 64)
    (terminal : ∀ p H P U W g v,
      InvariantOddLocalAnalysis T L V d p H P U W g v →
      IsExtraspecial p P → Nat.card P = p ^ 3 → Monoid.exponent P = p →
      W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥ →
      p = 3 → d = 3 → Nat.card W = 64 → False) :
    ∃ H P U, CyclicLocalAnalysis T L V d H P U := by
  have hTV := ((structural G T L h).2.2 V D).1
  apply cyclicLocalAnalysis_of_invariant_odd_and_prime_steps h D structural A
    (invariantOddLocalAnalysis_of_selection D A hTV hTI selectionStep)
  intro p H P U W g v S
  exact prime_order_of_extraspecial_steps D A S hnone
    (numerical p H P U W g v S) (terminal p H P U W g v S)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
