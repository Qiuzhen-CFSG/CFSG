module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowModelsRecognition
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisSylowReduction
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisSylowResidualsQuotientsSource

/-!
# LocalAnalysisSylowModelsRecognition at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisSylowModelsRecognition`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

public noncomputable section

open Subgroup

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}

private lemma center_eq_bot_of_alternating_equiv_at {A : Type*} [Group A]
    {n : ℕ} (hn : 4 ≤ n) (e : A ≃* alternatingGroup (Fin n)) : center A = ⊥ := by
  apply bot_unique
  intro x hx
  have he : e x ∈ center (alternatingGroup (Fin n)) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨a,rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hx a)
  rw [alternatingGroup.center_eq_bot (by simpa using hn),mem_bot] at he
  exact e.map_eq_one_iff.mp he

namespace Setup.NaturalCoordinates

variable (E : S.NaturalCoordinates)

end Setup.NaturalCoordinates

namespace SylowNormalizer.Points

variable {E : S.NaturalCoordinates} (P : Points E)

lemma point_quotients_of_contrary_normalizer_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    Nonempty ((P.five ⧸ pCore 2 P.five) ≃* alternatingGroup (Fin 5)) ∧
      Nonempty (CentralQuotient P.sixGroup ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨eL⟩ := E.seven_twoCore_quotient_at structural hescape
  exact ⟨⟨P.fiveCoreEquiv⟩, ⟨P.sixCentralEquivOfSeven eL⟩⟩

end SylowNormalizer.Points

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

