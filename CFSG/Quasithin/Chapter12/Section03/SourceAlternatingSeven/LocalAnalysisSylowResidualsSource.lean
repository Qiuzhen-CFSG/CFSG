module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowResidualsQuotients
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowResidualsComponentsSourceModels
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowOmegaAction

/-!
# The ambient residual identities in the A₇ Sylow-normalizer argument

In the contrary-normalizer branch, the source block construction supplies
the actual A₇ and A₆ quotients by O₂. The C.2.3/C.2.7 argument makes the
six-point residual a normal C-component in every fixed-coset centralizer;
uniqueness does the same for L at each nonidentity fixed point. A.3.18
therefore gives both ambient prime-to-three residual identities, with
their original subgroup embeddings and the essential nonidentity condition.

The resulting constructor discharges all quotient and coset-component
premises. Its applications supply `no_transport` and the omega-action proof,
then the original ambient-fusion consumer. Only structural 12.2.2 and the
local `Models` remain explicit; their final discharge belongs to
`qt-d-1235-a7-sylow-normalizer` and its local-model producer.

Source: Aschbacher--Smith, 3.3.22 (*) and (**), printed pp.597--598,
using 3.3.6--8, C.2.3/C.2.7 and A.3.18. The fusion consumer is 12.3.5,
printed p.809.
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

/-- Construct both literal ambient residual identities from the original
source setup and local models, discharging the two independent source inputs. -/
theorem ambientResiduals_of_source
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (M : P.Models)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    P.AmbientResiduals := by
  obtain ⟨⟨eL⟩, ⟨e6⟩⟩ := P.twoCore_quotients_of_contrary_normalizer structural M hescape
  exact P.ambientResiduals_of_coset_components structural eL e6
    (P.cosetComponents_of_source structural M e6)

/-- Source 3.3.22 (*), for every element of the actual fixed coset. -/
theorem six_residual_of_source
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (M : P.Models)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    {c : G} (hc : c ∈ P.fixed) :
    pointThreeResidual (c * (P.six : G)) = P.sixGroup :=
  (P.ambientResiduals_of_source structural M hescape).six_residual c hc

/-- Source 3.3.22 (**), retaining the essential nonidentity restriction. -/
theorem fixed_residual_of_source
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (M : P.Models)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    {c : G} (hc : c ∈ P.fixed) (hne : c ≠ 1) : pointThreeResidual c = L :=
  (P.ambientResiduals_of_source structural M hescape).fixed_residual c hc hne

/-- The constructed residuals feed the original marked transport obstruction. -/
theorem no_transport_of_source
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (M : P.Models)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    {g : G} (hg : g ∈ normalizer (T : Set G)) :
    g * (P.two : G) * g⁻¹ ≠ P.six :=
  SylowNormalizer.no_transport M (P.ambientResiduals_of_source structural M hescape)
    S.chosen.sylow_normalizes_component hg

/-- Discharge the ambient-residual input of the actual omega-action proof.
The local models remain with the Sylow-normalizer assembly owner. -/
theorem normalizer_le_of_models
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (M : P.Models) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  by_contra hescape
  exact hescape (P.normalizer_le_of_source_inputs structural M
    (P.ambientResiduals_of_source structural M hescape))

/-- The literal 12.3.5 fusion consumer, with the ambient residuals constructed. -/
theorem controlsFusion_of_models
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (M : P.Models)
    (x y : G) (hx : x ∈ V) (hy : y ∈ V) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hxy : ∃ g : G, g * x * g⁻¹ = y) : ∃ l ∈ L, l * x * l⁻¹ = y :=
  E.controlsFusion structural (P.normalizer_le_of_models structural M)
    x y hx hy hx1 hy1 hxy

end SylowNormalizer.Points
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
