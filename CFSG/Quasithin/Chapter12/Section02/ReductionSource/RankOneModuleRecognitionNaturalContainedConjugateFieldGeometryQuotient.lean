module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryQuotient
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryNatural

/-!
# The fixed-space quotient of the original Chapter 12 layer

On B=[R₂(LT),L], displacement identifies the literal quotient B/U with U
and intertwines ambient conjugation by N_L(U). Both this normalizer and
its embedded O² residual therefore have the same half-degree natural
module on the quotient as on U. This is the opening calculation of
Aschbacher–Smith 6.1.14, printed p.671.
-/

public section
open Subgroup
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L U : Subgroup G} {n : ℕ}

/-- The actual normalizer action on B/U, using the original layer's
specified elementary abelian instance. -/
theorem source_field_fixedSpace_quotient
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hfield : IsInvolutoryFieldFixedSpace L (normalizer (L : Set G))
      (commutatorLayer T L) U n)
    (hUne : U ≠ ⊥) (hn : 2 < n) :
    let := h611.layer_elementary
    ∃ (m : ℕ) (eQ : (commutatorLayer T L ⧸ U.subgroupOf (commutatorLayer T L)) ≃* U),
      n = 2 * m ∧
      Chapter6.Source.IsNaturalModule (L ⊓ normalizer (U : Set G)) U m ∧
      Chapter6.Source.IsNaturalModule (fieldLocalResidual L U) U m ∧
      ∀ (l : (L ⊓ normalizer (U : Set G) : Subgroup G))
        (b b' : commutatorLayer T L),
        (b' : G) = (l : G) * (b : G) * (l : G)⁻¹ →
        (eQ (QuotientGroup.mk' (U.subgroupOf (commutatorLayer T L)) b') : G) =
          (l : G) * (eQ (QuotientGroup.mk' (U.subgroupOf (commutatorLayer T L)) b) : G) *
            (l : G)⁻¹ := by
  let := h611.layer_elementary
  exact field_fixedSpace_quotient hnatural hfield hUne hn

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
