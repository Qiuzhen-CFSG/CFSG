module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.SourceRankOne
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.MarkedLocal

/-!
# Ree rank-one collection on original and geometric markings

The conditional finite Suzuki equations reduce local words on the same
marked quotient. The supplied original-to-standard amalgam isomorphism
then lifts those words uniquely to the selected original endpoint. This
uses `MarkedLocal.endpointMap`, so it applies equally to the generated
source quotient and the universal/geometric quotient, without a map
between the two ambient completions.

This leaf proves the local descent application only. It does not assert
the full Ree marked comparison or a Chapter12 classification alternative.
Source: DGS, Groups and Graphs, Theorem D, p.224; GLS3 §2.4; Aschbacher–Smith
F.1.1, pp.259–260.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open ReeF4.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReePresentation
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (split : SplitData Q.tits) (i : Fin 2) (n : Q.tits.N)
  {m : ℕ} (d : SourceRankOne.SuzukiData Q split i n m)

/-- Pull the exact generated local subgroup back through its original endpoint marking. -/
def localSubgroup : Subgroup (parabolic L S i) :=
  (SourceRankOne.generated Q split i n).comap (MarkedLocal.endpointMap Q e i)

include d in
/-- Every local source word has one original endpoint lift under the given
marking, even when the numerator of Q is the universal completion. -/
theorem existsUnique_original_lift (g : X ⧸ Q.D)
    (hg : g ∈ SourceRankOne.generated Q split i n) :
    ∃! a : parabolic L S i, MarkedLocal.endpointMap Q e i a = g := by
  let y : Q.tits.standardParabolic {Q.simple i} :=
    ⟨g, SourceRankOne.generated_le_endpoint Q split i n d hg⟩
  refine ⟨(MarkedLocal.endpoint Q e i).symm y, ?_, ?_⟩
  · exact congrArg Subtype.val ((MarkedLocal.endpoint Q e i).apply_symm_apply y)
  · intro a ha
    apply (MarkedLocal.endpoint Q e i).injective
    rw [MulEquiv.apply_symm_apply]
    exact Subtype.ext ha

/-- The original local word has precisely the finite source coordinates,
through its literal endpoint map. No model equivalence is assumed. -/
theorem original_coordinateForm (a : localSubgroup Q e split i n) :
    (∃ u : ReeF4.CoefficientField m × ReeF4.CoefficientField m, ∃ t : TorusParameter m,
      MarkedLocal.endpointMap Q e i a = (d.chart u : X ⧸ Q.D) * d.h t) ∨
    ∃ u : ReeF4.CoefficientField m × ReeF4.CoefficientField m, ∃ t : TorusParameter m,
      ∃ v : ReeF4.CoefficientField m × ReeF4.CoefficientField m,
        MarkedLocal.endpointMap Q e i a =
          (d.chart u : X ⧸ Q.D) * d.h t * n * (d.chart v : X ⧸ Q.D) :=
  SourceRankOne.coordinateForm Q split i n d _ a.property

/-- Both original endpoint conventions retain the existing whole-Borel square. -/
theorem local_borel_formula (h : HypothesisF11 L S) (b : commonBorel L S)
    (hb : MarkedLocal.borelMap Q e h b ∈ SourceRankOne.generated Q split i n) :
    ∃ a : localSubgroup Q e split i n,
      (a.val : G) = b ∧ MarkedLocal.endpointMap Q e i a = MarkedLocal.borelMap Q e h b := by
  refine ⟨⟨⟨b, commonBorel_le_parabolic i b.property⟩, ?_⟩, rfl, ?_⟩
  · change MarkedLocal.endpointMap Q e i _ ∈ SourceRankOne.generated Q split i n
    rwa [MarkedLocal.endpoint_borel Q e h i b]
  · exact MarkedLocal.endpoint_borel Q e h i b

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReePresentation
