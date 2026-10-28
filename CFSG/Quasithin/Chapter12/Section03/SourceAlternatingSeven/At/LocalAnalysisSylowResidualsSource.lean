module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowResidualsSource
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisSylowOmegaAction
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisSylowResidualsComponentsSourceModels
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisSylowResidualsQuotients

/-!
# LocalAnalysisSylowResidualsSource at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisSylowResidualsSource`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}

variable {E : S.NaturalCoordinates}

namespace SylowNormalizer.Points

variable (P : Points E)

theorem ambientResiduals_of_source_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (M : P.Models)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    P.AmbientResiduals := by
  obtain ⟨⟨eL⟩, ⟨e6⟩⟩ := P.twoCore_quotients_of_contrary_normalizer_at structural M hescape
  exact P.ambientResiduals_of_coset_components_at structural eL e6
    (P.cosetComponents_of_source_at structural M e6)

theorem six_residual_of_source_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (M : P.Models)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    {c : G} (hc : c ∈ P.fixed) :
    pointThreeResidual (c * (P.six : G)) = P.sixGroup :=
  (P.ambientResiduals_of_source_at structural M hescape).six_residual c hc

theorem fixed_residual_of_source_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (M : P.Models)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    {c : G} (hc : c ∈ P.fixed) (hne : c ≠ 1) : pointThreeResidual c = L :=
  (P.ambientResiduals_of_source_at structural M hescape).fixed_residual c hc hne

theorem no_transport_of_source_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (M : P.Models)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    {g : G} (hg : g ∈ normalizer (T : Set G)) :
    g * (P.two : G) * g⁻¹ ≠ P.six :=
  SylowNormalizer.no_transport M (P.ambientResiduals_of_source_at structural M hescape)
    S.chosen.sylow_normalizes_component hg

theorem normalizer_le_of_models_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (M : P.Models) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  by_contra hescape
  exact hescape (P.normalizer_le_of_source_inputs_at structural M
    (P.ambientResiduals_of_source_at structural M hescape))

theorem controlsFusion_of_models_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (M : P.Models)
    (x y : G) (hx : x ∈ V) (hy : y ∈ V) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hxy : ∃ g : G, g * x * g⁻¹ = y) : ∃ l ∈ L, l * x * l⁻¹ = y :=
  E.controlsFusion_at structural (P.normalizer_le_of_models_at structural M)
    x y hx hy hx1 hy1 hxy

end SylowNormalizer.Points

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

