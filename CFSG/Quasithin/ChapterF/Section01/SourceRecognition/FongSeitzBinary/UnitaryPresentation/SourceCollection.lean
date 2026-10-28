module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FourPositive
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.FivePositive
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.NormalGeneration

/-!
# Field-parametrized positive collection on the same original source quotient

The exact U₄ or U₅ positive equations imply collection in the literal quotient
by Q.D. When the source-coordinate producer proves that these root images
generate its U, this collects every element of the original S image under Q.q.
The two Hermitian parameter groups in U₅ are retained at every field order.

This discharges the positive-word collection step only. Field reconstruction,
the exact source equations and their generation premise are still inputs from
the split-quotient source owner. Torus, Weyl, full Bruhat presentation and both
endpoint comparisons are separate unfinished parts of this presentation family.

Source: DGS, Groups and Graphs, Theorem D, printed p.224; Steinberg,
Lectures on Chevalley Groups, Theorem 33 and Lemmas 63–64, pp.181–187.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryPresentation
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {E : Type*} [Field E] [CharP E 2]

omit [CharP E 2] in
/-- Conditional U₄ collection on Q.q(S), keeping the actual fixed field. -/
theorem four_originalS_collected (h : HypothesisF11 L S) (Q : SourceQuotient L S)
    (split : SplitData Q.tits) (σ : E ≃+* E) (hσ : Function.Involutive σ)
    (r : PositiveMaps ((generated L S) ⧸ Q.D)
      (Multiplicative E) (Multiplicative (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FixedField E σ))
      (Multiplicative E) (Multiplicative (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FixedField E σ)))
    (heq : FourPositive.Relations E σ hσ r) (hgen : split.U ≤ r.generated)
    (x : (generated L S) ⧸ Q.D) (hx : x∈(S.subgroupOf (generated L S)).map Q.q) :
    ∃ a d c b, x=r.word a d c b := by
  rw [quotient_sourceS_image_eq_unipotent h Q split] at hx
  exact PositiveMaps.exists_word (FourPositive.Relations.collects E σ hσ heq) (hgen hx)

/-- Conditional U₅ collection on the same Q.q(S), using both full Hermitian groups. -/
theorem five_originalS_collected (h : HypothesisF11 L S) (Q : SourceQuotient L S)
    (split : SplitData Q.tits) (J : HermitianForm 5 E)
    (r : PositiveMaps ((generated L S) ⧸ Q.D) (Multiplicative E) (FivePositive.Parameter J)
      (Multiplicative E) (FivePositive.Parameter J))
    (heq : FivePositive.Relations J r) (hgen : split.U ≤ r.generated)
    (x : (generated L S) ⧸ Q.D) (hx : x∈(S.subgroupOf (generated L S)).map Q.q) :
    ∃ a d c b, x=r.word a d c b := by
  rw [quotient_sourceS_image_eq_unipotent h Q split] at hx
  exact PositiveMaps.exists_word (FivePositive.Relations.collects J heq) (hgen hx)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryPresentation
