module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeFactorPanels
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# Full linear panels and Ree input for the Chapter 12 pair

The proper-K/full KnownSimple preparation supplies F.1.1 for the actual
pair ![L,R]. Each original linear factor quotient now constructs its full
faithful endpoint marking and injective additive root chart, with the
whole Borel, model projection and original endpoint image retained.
The endpoint index is arbitrary, so a binary second factor is included.

When the original factors are linear and Suzuki in the octagonal branch,
the same preparation supplies the complete panel inputs of ReeSixHData.
Both full markings and their Borel equations are constructed. Its literal
mixed subgroup equations, the odd degree and the octagonal Weyl order
remain explicit source inputs; this does not assert the final Ree
comparison or exhaustive seven-row recognition.

Source: Aschbacher--Smith 12.2.2 and F.1.1--3; DGS (1985), Theorem D,
p.224; Fong--Seitz I (3B), (5C), (6H), pp.13,25--26,51 and II §10.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The proper-K/full KnownSimple Chapter 12 preparation gives the full
original linear endpoint and its additive root coordinates, on either side. -/
theorem rankOne_global_linear_panel_coordinates
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (i : Fin 2) {F : Type*} [Field F] [Finite F] [CharP F 2]
    (μ : ((![L,R] i) ⧸ pCore 2 (![L,R] i)) ≃* PSL(2,F))
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    ∃ (τ : (parabolic ![L,R] (Global.sourceS L H) i ⧸
          ReeSource.originalPanelKernel (L := ![L,R]) (S := Global.sourceS L H) i) ≃*
        PSL(2,F))
      (Tf : Sylow 2 PSL(2,F))
      (u : Multiplicative F →* parabolic ![L,R] (Global.sourceS L H) i),
      (ReeSource.originalFaithfulBorel (L := ![L,R]) (S := Global.sourceS L H) i).map
        τ.toMonoidHom = normalizer (Tf : Set PSL(2,F)) ∧
      Function.Injective u ∧
      (∀ a, τ (QuotientGroup.mk'
        (ReeSource.originalPanelKernel (L := ![L,R]) (S := Global.sourceS L H) i) (u a)) =
          (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive Tf a : PSL(2,F))) ∧
      ((MarkedLocal.endpointMap Q e i).comp u).range = simpleRoot Q split i := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact LinearPanel.original_coordinates Q e hf split i μ

/-- Both actual factor markings supply the Section 10 panel input for the
Chapter 12 pair. The source subgroup equations and octagonal branch are retained. -/
theorem rankOne_global_ree_input_of_factor_markings
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    {a m : ℕ} (ha : Odd a)
    (μ₀ : (L ⧸ pCore 2 L) ≃* PSL2BinaryMatrixGroup a)
    (μ₁ : (R ⧸ pCore 2 R) ≃* SuzukiMatrixGroup m)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : rotationOrder Q = 8)
    (relations : SixHRelations Q split) : Nonempty (ReeSixHData Q split a m) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact ReeFactorPanels.section10_input Q e hf split hm a ha m μ₀ μ₁ relations

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
