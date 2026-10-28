module
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.Sporadic
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.Sporadic.ProvedCentralizers
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.Sporadic.Mathieu
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.Sporadic.Rudvalis
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.Sporadic.HigmanSims
/-!
# The complete sporadic quotient exclusion in E.6.23

Every entry of the original catalogue is screened by its proved involution
calculation. The genuine HS fixed-six case uses the full original source
geometry and the actual quotient action. Simplicity and perfectness in model
rows are inherited from the original quasisimple component.

Source: Aschbacher–Smith Theorem C, p.33, and E.6.23, p.254.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen
open ClassificationModels
variable {G : Type*} [Group G] [Finite G]
theorem sporadicExclusion (T : Sylow 2 G) (M V : Subgroup G)
    [IsElementaryAbelian 2 V] : SporadicExclusion T M V := by
  apply sporadicExclusion_of_remaining
  · intro name h11 h23 h3 hhs hs hp
    cases name with
    | m11 => exact (h11 rfl).elim
    | m12 => exact Sporadic.m12
    | m22 => exact Sporadic.m22
    | m23 => exact (h23 rfl).elim
    | m24 => exact Sporadic.m24
    | j2 => exact Sporadic.janko_two
    | j3 => exact (h3 rfl).elim
    | j4 => exact @Sporadic.janko_four hs hp
    | hs => exact (hhs rfl).elim
    | he => exact Sporadic.held
    | ru => exact @Sporadic.rudvalis hs hp
  · exact Sporadic.higman_sims_source T M V
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen
