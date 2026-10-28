module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryNatural
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedConjugateFieldAction

/-!
# The field-fixed module on the original Chapter 12 layer

Apply fixed-field descent to B=[R₂(LT),L], retaining the literal fixed
subgroup U and normalizer residual O²(N_L(U)). Both the normalizer and its
residual act on U through their actual two-core quotients as natural SL₂
modules of degree n/2. This supplies the first local-module calculation
required for 6.1.14, with no Sylow arrangement or local-component premise.

The contained-branch owner still has to construct the normalizer geometry
and the natural action on a conjugate of Z_S before applying the terminal
field-escape argument. Source: Aschbacher--Smith, 6.1.14, printed p.671.
-/

public section
open Subgroup
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L U : Subgroup G} {n : ℕ}

/-- The original field-fixed subgroup is natural for its actual normalizer
and for the embedded O² residual, with the same half-degree. -/
theorem source_field_fixedSpace_natural
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hfield : IsInvolutoryFieldFixedSpace L (normalizer (L : Set G))
      (commutatorLayer T L) U n)
    (hUne : U ≠ ⊥) (hn : 2 < n) :
    ∃ m : ℕ, n = 2 * m ∧
      Chapter6.Source.IsNaturalModule (L ⊓ normalizer (U : Set G)) U m ∧
      Chapter6.Source.IsNaturalModule (fieldLocalResidual L U) U m :=
  field_fixedSpace_natural hn hnatural hfield hUne

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
