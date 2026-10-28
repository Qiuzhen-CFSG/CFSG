module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48ConstrainedExcluded

/-!
# The original binary-three doubled orbit is FF

The actual multiple-overgroup non-FF source constructs a reciprocal witness
and a constrained component after the ordinary exclusions. The original
constrained module calculation excludes that component. Thus the unchanged
full source-orbit normalizer representation is FF in the binary-three branch.
The other doubled/natural branches and normalization remain separate duties.
Source: Aschbacher--Smith C.4.8, 12.1.11 and 12.2.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original binary-three source branch is FF without any local
classification, parabolic, module, or residual-placement callback. -/
theorem sourceOrbit_binary_natural_three_ff
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F) :
    IsFFModule D.sourceOrbitNormalizerRepresentation := by
  by_contra hnon
  obtain ⟨A,J,H,U,hw,hWJ,hJC,K,hK,hq,hout,hfK,_,_,_⟩ :=
    D.sourceOrbit_binary_reciprocal_constrained_linear_models h hd hmany hnon F hF hmodel
  exact D.sourceOrbit_binary_witness_no_constrained_component
    h hd F hF hmodel hw hWJ hJC K hK hq hout hfK

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
