module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Statement

/-!
# The common remaining module-extraction contract in B.5.8 and B.5.11

After classifying a smaller nontrivial actor of three-rank at most one, the
source needs a submodule supplementing its fixed space and satisfying one of
B.5.6(3a–c). The natural and doubled cases use the actual moved space; the
exceptional case retains the full four-dimensional quotient extension.

This is an output specification for the independent module-extraction proof.
`RankOneModuleExtraction` is not a permitted earlier-source parameter or an
established theorem. The final induction owner must prove or instantiate it
before using the B.5.8 reduction which consumes it. Its classification premise
must come from the actual strictly smaller-order recursive call.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, pp.106 and 109.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceInduction
universe u v

/-- The full single-factor output, with its original fixed quotient and action. -/
structure FactorModuleConclusion {D : Type u} [Group D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) where
  space : Subrepresentation ρ
  supplement : space.toSubmodule ⊔ ρ.invariants = ⊤
  actionCase : SourceFactorCase ρ ⊤ space

/-- The shared remaining implication from the classified rank-one action.
It is an intermediate task target, not an earlier theorem assumed by the
adequate classification. -/
def RankOneModuleExtraction (K : GroupClass.{u}) : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] [Nontrivial D]
    (V : Type v) [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V),
    FFHypothesis K ρ → primeRank 3 D ≤ 1 → AdequateAlternative ρ →
      Nonempty (FactorModuleConclusion ρ)

end CFSG.Quasithin.ChapterB.SourceInduction
