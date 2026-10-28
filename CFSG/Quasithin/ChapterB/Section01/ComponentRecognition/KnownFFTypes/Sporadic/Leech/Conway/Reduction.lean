module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Defs
public import Theory.Representation.BinaryOffender.NormalizerOffenderDimension

/-!
# Independent inputs to the Conway FF exclusions

The full normalizer degree estimate separates the uniform group geometry from
the small-module calculations. Six-conjugate generation and automorphism
two-rank at most eleven would bound an FF degree by 66. For each surviving
module, it suffices to examine elementary subgroups A with `dim V ≤ 6 * rank A`.
The offender-specific bound proves that all other elementary subgroups are
irrelevant. Both model inputs below are explicit, unproved obligations.

The source target is Aschbacher–Smith B.1.13, printed pp.73–74 / PDF pp.84–85,
which cites Guralnick–Malle, *Classification of 2F-modules, II*, Table 2,
DOI 10.1515/9783110198126.117. The numbers here specify a proposed sufficient
cutoff, not a claim about the contents of that table. The input proofs must
cover all quasisimple central covers, identify the literal catalogue carrier,
and treat the actual full linear normalizer, including its small-module cases.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.Conway
open Subgroup Theory.GroupTheory Representation.BinaryOffender
universe u v

/-- The uniform model estimates needed by the degree reduction. Simplicity
and perfectness of the carrier may be inherited from the actual central quotient.
Neither estimate is supplied merely by defining this predicate. -/
def NormalizerEstimates (name : KnownSimple.SporadicName) : Prop :=
  ∀ {L : Type u} {W : Type v} [Group L] [Finite L] [IsQuasisimple L]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) L W),
    Function.Injective σ → σ.IsIrreducible →
    Nonempty (L ⧸ center L ≃* name.Carrier) →
    NormalizerConjugateGenerationBound σ 6 ∧
      primeRank 2 (MulAut name.Carrier) ≤ 11

/-- The residual small-module calculation is an inequality for actual elementary
subgroups of the full normalizer. It has no offender premise. The degree and
rank cutoffs are discharged by the uniform estimates in final assembly. -/
def SmallModuleEstimate (name : KnownSimple.SporadicName) : Prop :=
  ∀ {L : Type u} {W : Type v} [Group L] [Finite L] [IsQuasisimple L]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) L W),
    Function.Injective σ → σ.IsIrreducible →
    Nonempty (L ⧸ center L ≃* name.Carrier) →
    Module.finrank (ZMod 2) W ≤ 66 →
    ∀ A : Subgroup (linearNormalizer σ), IsElementaryTwo A →
      Module.finrank (ZMod 2) W ≤ 6 * rank A →
      rank A < fixedCodim (normalizerRepresentation σ) A

/-- The precise source application of the offender-specific degree bound.
The global estimates and small-module calculations remain independent premises. -/
theorem exclusion_of_estimates (name : KnownSimple.SporadicName)
    (hglobal : NormalizerEstimates.{u,v} name)
    (hsmall : SmallModuleEstimate.{u,v} name) : FaithfulExclusion.{u,v} name := by
  intro L W _ _ _ _ _ _ σ hf hi he hff
  obtain ⟨hgen, hr⟩ := hglobal σ hf hi he
  have hd : Module.finrank (ZMod 2) W ≤ 66 := by
    exact finrank_le_of_ff_normalizer_central_quotient σ hf hi he.some hgen hr hff
  obtain ⟨A, hA⟩ := hff
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  have hArank := finrank_le_mul_rank_of_normalizer_offender σ hf hi hgen hA
  exact (Nat.not_lt_of_ge hA.2) (hsmall σ hf hi he hd A hA.1 hArank)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.Conway
