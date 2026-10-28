module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometrySplitting
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryNatural

/-!
# The two-copy decomposition on the Chapter 12 layer

Binary displacement and a trace-one scalar identify the original layer with
two copies of the involutory field fixed space. Both coordinates intertwine
the literal N_L(U)-action. This is the direct-sum calculation used in
Aschbacher–Smith 6.1.14(5), printed p.671.
-/

public section
open Subgroup
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G]
  {T : Sylow 2 G} {L U : Subgroup G} {n : ℕ}

/-- The two-copy equivalence retains the original ambient conjugation action. -/
theorem source_field_fixedSpace_double_equiv
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hfield : IsInvolutoryFieldFixedSpace L (normalizer (L : Set G))
      (commutatorLayer T L) U n) (hUne : U ≠ ⊥) :
    ∃ d : commutatorLayer T L ≃* (U × U),
      ∀ (l : (L ⊓ normalizer (U : Set G) : Subgroup G)) (b b' : commutatorLayer T L),
        (b' : G) = (l : G) * (b : G) * (l : G)⁻¹ →
        ((d b').1 : G) = (l : G) * ((d b).1 : G) * (l : G)⁻¹ ∧
        ((d b').2 : G) = (l : G) * ((d b).2 : G) * (l : G)⁻¹ :=
  field_fixedSpace_double_equiv hnatural hfield hUne

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
