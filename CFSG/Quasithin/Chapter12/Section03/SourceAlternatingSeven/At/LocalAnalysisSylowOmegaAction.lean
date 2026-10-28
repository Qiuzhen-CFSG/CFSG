module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowOmegaAction
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisSylowOmegaSpan

/-!
# LocalAnalysisSylowOmegaAction at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisSylowOmegaAction`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

public section

open Subgroup

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}

variable {E : S.NaturalCoordinates}

namespace SylowNormalizer.Points

variable (P : Points E)

theorem normalizer_le_of_source_inputs_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (M : P.Models) (R : P.AmbientResiduals) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  by_contra hescape
  obtain ⟨g, hg, he⟩ := P.transport_of_omegaSpan_at structural M R hescape
  exact no_transport M R S.chosen.sylow_normalizes_component hg he

theorem controlsFusion_of_source_inputs_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (M : P.Models) (R : P.AmbientResiduals)
    (x y : G) (hx : x ∈ V) (hy : y ∈ V) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hxy : ∃ g : G, g * x * g⁻¹ = y) : ∃ l ∈ L, l * x * l⁻¹ = y :=
  E.controlsFusion_at structural (P.normalizer_le_of_source_inputs_at structural M R)
    x y hx hy hx1 hy1 hxy

end SylowNormalizer.Points

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

