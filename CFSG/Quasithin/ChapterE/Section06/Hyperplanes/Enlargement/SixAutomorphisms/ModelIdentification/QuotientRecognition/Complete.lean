module
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.OddBender
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Source
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.Sporadic.Source
/-!
# Complete source quotient recognition in E.6.23

The full Theorem C catalogue is inspected on the original central quotient,
with its actual order-eight action and fixed A₆ component. Odd and Bender
models are excluded by their intrinsic fixed-component calculations. The
rank-two family includes the genuine Sp₄(4) source field exception. The HS
sporadic row retains the original common Sylow and its central cover.
Every model calculation is proved; the endpoint has no exclusion callback.

Source: Aschbacher–Smith Theorem C, printed p.33, and E.6.23, p.254.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification
open QuotientScreen
variable {G : Type*} [Group G] [Finite G]
theorem quotientRecognition (T : Sylow 2 G) (M V : Subgroup G)
    [IsElementaryAbelian 2 V] : QuotientRecognition T M V :=
  quotientRecognition_of_model_exclusions oddFixedComponentExclusion
    benderFixedComponentExclusion (RankTwo.rankTwoExclusion_source T M V)
    (sporadicExclusion T M V)
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification
