module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.ModelExclusion.Sporadic.MathieuTwentyTwo

/-!
# The original sporadic marked-component exclusion

The elementary sixteen and the marked centralizer order exclude every allowed
sporadic carrier except M₂₂. Quasithinness and the trivial two-core of the
literal deleted-point quotient give the M₂₂ marked centralizer order at most
768, contradicting the subgroup of order 1152 in the supplied local extension.
The quotient embedding retains the central-cover kernel, subnormal component
image and original conjugation action throughout.

The source theorem discharges the complete sporadic exclusion contract under
the original factor hypotheses, including terminal solvability. Its actual
marked-model consumer keeps the independent local-extension and even-model
inputs explicit; their discharge remains with the final assembly owner.
Source: Aschbacher--Smith, 14.3.20, final paragraph on printed p.998,
and the sporadic alternatives in 1.1.5(3)(f), printed p.502.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}

/-- Quasithinness excludes all allowed sporadic components with the supplied
literal quotient-centralizer structure. -/
theorem sporadicExclusionSource_of_quasithin (hG : IsQuasithin G)
    (F : InvariantFlag T V 2) (L : Subgroup G) : SporadicExclusionSource F L :=
  sporadicExclusionSource_of_mathieuTwentyTwo F L
    (mathieuTwentyTwoExclusionSource_of_quasithin hG F L)

open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)

include hG hempty hM hu hmany hcard e hnot hne hgP hgH hs

/-- The full sporadic source obligation under exactly the original factor
hypotheses, with no additional model exclusion premise. -/
theorem sporadicExclusionSource_of_source_inputs :
    SporadicExclusionSource F (sourceResidual M Mc) :=
  sporadicExclusionSource_of_mathieuTwentyTwo F (sourceResidual M Mc)
    (source_mathieuTwentyTwoExclusion hG T hempty hM hu hmany hcard e hnot F hne
      g hgP hgH hs)

/-- Apply the completed sporadic exclusion to the literal marked-model
consumer. The independent local-extension and even-model inputs remain. -/
theorem modelExclusionSource_of_source_inputs_and_local_even
    (hlocal : QuotientCentralizerSource F (sourceResidual M Mc))
    (heven : EvenExclusionSource F (sourceResidual M Mc)) :
    ModelExclusionSource F (sourceResidual M Mc) :=
  modelExclusionSource_of_local_inputs F (sourceResidual M Mc) hlocal heven
    (sporadicExclusionSource_of_source_inputs
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
