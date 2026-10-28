module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowResidualsQuotients
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisSylowReduction
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisSylowResiduals
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisSylowResidualsQuotientsSource

/-!
# LocalAnalysisSylowResidualsQuotients at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisSylowResidualsQuotients`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

public noncomputable section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}

variable {E : S.NaturalCoordinates}

namespace SylowNormalizer.Points

variable (P : Points E)

theorem ambientResiduals_of_seven_quotient_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (M : P.Models)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7))
    (C : P.CosetComponents) : P.AmbientResiduals := by
  obtain ⟨e6⟩ := P.six_twoCore_quotient_of_seven M eL
  exact P.ambientResiduals_of_coset_components_at structural eL e6 C

theorem no_transport_of_seven_quotient_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (M : P.Models)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7))
    (C : P.CosetComponents) {g : G} (hg : g ∈ normalizer (T : Set G)) :
    g * (P.two : G) * g⁻¹ ≠ P.six :=
  SylowNormalizer.no_transport M (P.ambientResiduals_of_seven_quotient_at structural M eL C)
    S.chosen.sylow_normalizes_component hg

theorem twoCore_quotients_of_contrary_normalizer_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (M : P.Models)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 7)) ∧
      Nonempty ((P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨eL⟩ := E.seven_twoCore_quotient_at structural hescape
  exact ⟨⟨eL⟩, P.six_twoCore_quotient_of_seven M eL⟩

theorem ambientResiduals_of_contrary_normalizer_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (M : P.Models)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (C : P.CosetComponents) : P.AmbientResiduals := by
  obtain ⟨⟨eL⟩, ⟨e6⟩⟩ := P.twoCore_quotients_of_contrary_normalizer_at structural M hescape
  exact P.ambientResiduals_of_coset_components_at structural eL e6 C

theorem no_transport_of_contrary_normalizer_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (M : P.Models)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (C : P.CosetComponents) {g : G} (hg : g ∈ normalizer (T : Set G)) :
    g * (P.two : G) * g⁻¹ ≠ P.six :=
  SylowNormalizer.no_transport M
    (P.ambientResiduals_of_contrary_normalizer_at structural M hescape C)
    S.chosen.sylow_normalizes_component hg

end SylowNormalizer.Points

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

