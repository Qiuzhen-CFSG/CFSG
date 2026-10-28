module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearPanelCompletion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SuzukiPanelCompletion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.Construction

/-!
# Section 10 panel inputs from the actual original factor quotients

The original PSL₂ and Suzuki factor quotient markings now construct the
entire faithful endpoint markings, their whole-Borel equations and their
original quotient squares. Apply the existing original-carrier (6H)
constructor to those markings and the actual root reflections. Its common
field, Cartan order and separation conclusions therefore hold at this
original-factor boundary, including n = 1 and Suzuki parameter zero.

The octagonal Weyl order, odd linear degree and the literal SixHRelations
remain source hypotheses. In particular no mixed equation is inferred from
the local models. The Section 10 and final assembly owners must still
construct those equations and the subsequent global presentation. The
Chapter 12 consumer is LinearPanelApplications.

Source: Fong--Seitz I (6H), p.51; II §10, pp.221--230;
DGS, Groups and Graphs (1985), Theorem D, p.224.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeFactorPanels
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 8) (n : ℕ) (hn : Odd n) (m : ℕ)
  (μ₀ : ((L 0) ⧸ pCore 2 (L 0)) ≃* PSL2BinaryMatrixGroup n)
  (μ₁ : ((L 1) ⧸ pCore 2 (L 1)) ≃* SuzukiMatrixGroup m)

include e h hm hn μ₀ μ₁ in
/-- The original factor markings, together with the actual subgroup equations,
construct the precise Section 10 input. Both full endpoint markings and
whole-Borel equations are discharged, including the smallest Ree parameter. -/
theorem section10_input (relations : SixHRelations Q split) :
    Nonempty (ReeSixHData Q split n m) := by
  obtain ⟨_,T,τ₀,_,hB₀,_,_,_⟩ := LinearPanel.original_panel Q e h split 0 μ₀
  obtain ⟨_,_,τ₁,_,hB₁,_,_,_⟩ := SuzukiPanel.original_panel Q e h split 1 μ₁
  exact ⟨ReeSection10.ofOriginalSixH Q split e h n hn m τ₀ T hB₀ τ₁ hB₁
    (UnitarySource.actorReflection Q split) relations hm⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeFactorPanels
