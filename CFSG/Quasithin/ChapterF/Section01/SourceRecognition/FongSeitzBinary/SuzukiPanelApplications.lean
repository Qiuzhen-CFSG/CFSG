module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SuzukiPanelCompletion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# Original Suzuki panel coordinates for the Chapter 12 pair

The proper-K/full KnownSimple preparation supplies F.1.1 on the actual
pair ![L,R] and its original Sylow. The given Suzuki quotient of R now
constructs the isomorphism of the entire original faithful endpoint
quotient, sends the entire Borel to the standard root normalizer, and
constructs the two-parameter root chart with its multiplication and
literal endpoint-image equation. Parameter zero is included and neither
original endpoint is assumed perfect.

This supplies the Suzuki full-panel marking and root chart required by
the Ree (6H)/Section 10 consumers. The same independently marked split
quotient remains an earlier source input. Selection of the Ree branch,
the common field, its mixed relations and the exhaustive seven-row
comparison remain with their existing source and assembly owners.

Source: Aschbacher--Smith 12.2.2 and F.1.1--3; DGS (1985), Theorem D,
p.224; Fong--Seitz I (3B), (6H), pp.13,51 and II §10, pp.221--230.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The actual Chapter 12 preparation supplies the full original Suzuki panel
marking and its two-parameter root chart, also for the solvable binary factor. -/
theorem rankOne_global_suzuki_panel_coordinates
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    {m : ℕ} (μ : (R ⧸ pCore 2 R) ≃* SuzukiMatrixGroup m)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    ∃ (τ : (parabolic ![L,R] (Global.sourceS L H) 1 ⧸
          ReeSource.originalPanelKernel (L := ![L,R]) (S := Global.sourceS L H) 1) ≃*
        SuzukiMatrixGroup m)
      (u : BinaryGaloisField (2*m+1) → BinaryGaloisField (2*m+1) →
        parabolic ![L,R] (Global.sourceS L H) 1),
      (ReeSource.originalFaithfulBorel (L := ![L,R]) (S := Global.sourceS L H) 1).map
        τ.toMonoidHom = normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)) ∧
      (∀ a b c f, u a b * u c f = u (a+c) (b+f+a*suzukiTits m c)) ∧
      (∀ a b, τ (QuotientGroup.mk'
        (ReeSource.originalPanelKernel (L := ![L,R]) (S := Global.sourceS L H) 1) (u a b)) =
          (matrixRootPoint m a b : SuzukiMatrixGroup m)) ∧
      Set.range (fun p : BinaryGaloisField (2*m+1) × BinaryGaloisField (2*m+1) =>
        MarkedLocal.endpointMap Q e 1 (u p.1 p.2)) =
          (simpleRoot Q split 1 : Set (X ⧸ Q.D)) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact SuzukiPanel.original_coordinates Q e hf split 1 μ

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
