module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowNormalizer
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisSylowModelsCore
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisSylowResidualsSource

/-!
# LocalAnalysisSylowNormalizer at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisSylowNormalizer`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}

namespace Setup.NaturalCoordinates

variable (E : S.NaturalCoordinates)

include E

theorem sylow_normalizer_le_component_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  by_contra hescape
  obtain ⟨P⟩ := SylowNormalizer.points_nonempty_at E structural
  obtain ⟨M⟩ := P.models_of_contrary_normalizer_at structural hescape
  exact hescape (P.normalizer_le_of_models_at structural M)

theorem controlsFusion_of_source_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (x y : G) (hx : x ∈ V) (hy : y ∈ V) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hxy : ∃ g : G, g * x * g⁻¹ = y) : ∃ l ∈ L, l * x * l⁻¹ = y :=
  E.controlsFusion_at structural (E.sylow_normalizer_le_component_at structural)
    x y hx hy hx1 hy1 hxy

end Setup.NaturalCoordinates

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

