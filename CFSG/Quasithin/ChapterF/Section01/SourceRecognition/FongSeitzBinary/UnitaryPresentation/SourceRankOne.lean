module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.RankOneCollection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryPresentation.SourceCollection

/-!
# Both rank-one collection steps on the original marked quotient

Exact root equations and source root generation give the two-cell alternatives
for the image of the original S under the same quotient map Q.q. The Cartan
range remains in the actual B intersect N, and the complete Borel occurs in
both alternatives. This proves the local collection step, not presentation
faithfulness, generation of SU₅, or a marked source-model equivalence.

Source: DGS, Groups and Graphs, Theorem D, p.224; Steinberg, Lectures on
Chevalley Groups, Lemma 24 and Theorem 33.
-/
public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryPresentation
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {E : Type*} [Field E] [CharP E 2]
variable {H : Type*} [Group H]

private theorem originalS_reflected
    {RA RD RC RB : Type*} [Group RA] [Group RD] [Group RC] [Group RB]
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (r : PositiveMaps ((generated L S) ⧸ Q.D) RA RD RC RB)
    (hcol : r.Collects) (hgen : r.generated=split.U)
    (cartan : H →* ((generated L S) ⧸ Q.D))
    (hc : cartan.range≤Q.tits.B ⊓ Q.tits.N)
    (s t : (generated L S) ⧸ Q.D) (he : ReflectionLaws r cartan s t)
    (x : (generated L S) ⧸ Q.D) (hx : x∈(S.subgroupOf (generated L S)).map Q.q) :
    (s*x*s∈Q.tits.B ∨ ∃ l∈Q.tits.B, ∃ v∈Q.tits.B, s*x*s=l*s*v) ∧
    (t*x*t∈Q.tits.B ∨ ∃ l∈Q.tits.B, ∃ v∈Q.tits.B, t*x*t=l*t*v) := by
  rw [quotient_sourceS_image_eq_unipotent h Q split,←hgen] at hx
  obtain ⟨a,d,c,b,rfl⟩ := PositiveMaps.exists_word hcol hx
  have hr : r.generated≤Q.tits.B := hgen.le.trans split.U_le
  exact ⟨he.s_word Q.tits.B hr (hc.trans inf_le_left) a d c b,
    he.t_word Q.tits.B hr (hc.trans inf_le_left) a d c b⟩

omit [CharP E 2] in
/-- Both reflected positive words for U₄, on the literal original quotient. -/
theorem four_originalS_rankOne (h : HypothesisF11 L S) (Q : SourceQuotient L S)
    (split : SplitData Q.tits) (σ : E ≃+* E) (hσ : Function.Involutive σ)
    (r : PositiveMaps ((generated L S) ⧸ Q.D)
      (Multiplicative E) (Multiplicative (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FixedField E σ))
      (Multiplicative E) (Multiplicative (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FixedField E σ)))
    (heq : FourPositive.Relations E σ hσ r) (hgen : r.generated=split.U)
    (cartan : H →* ((generated L S) ⧸ Q.D)) (hc : cartan.range≤Q.tits.B ⊓ Q.tits.N)
    (s t : (generated L S) ⧸ Q.D) (he : ReflectionLaws r cartan s t)
    (x : (generated L S) ⧸ Q.D) (hx : x∈(S.subgroupOf (generated L S)).map Q.q) :
    (s*x*s∈Q.tits.B ∨ ∃ l∈Q.tits.B, ∃ v∈Q.tits.B, s*x*s=l*s*v) ∧
    (t*x*t∈Q.tits.B ∨ ∃ l∈Q.tits.B, ∃ v∈Q.tits.B, t*x*t=l*t*v) :=
  originalS_reflected h Q split r (FourPositive.Relations.collects E σ hσ heq)
    hgen cartan hc s t he x hx

/-- Both reflected positive words for general U₅, retaining full Hermitian roots. -/
theorem five_originalS_rankOne (h : HypothesisF11 L S) (Q : SourceQuotient L S)
    (split : SplitData Q.tits) (J : HermitianForm 5 E)
    (r : PositiveMaps ((generated L S) ⧸ Q.D) (Multiplicative E) (FivePositive.Parameter J)
      (Multiplicative E) (FivePositive.Parameter J))
    (heq : FivePositive.Relations J r) (hgen : r.generated=split.U)
    (cartan : H →* ((generated L S) ⧸ Q.D)) (hc : cartan.range≤Q.tits.B ⊓ Q.tits.N)
    (s t : (generated L S) ⧸ Q.D) (he : ReflectionLaws r cartan s t)
    (x : (generated L S) ⧸ Q.D) (hx : x∈(S.subgroupOf (generated L S)).map Q.q) :
    (s*x*s∈Q.tits.B ∨ ∃ l∈Q.tits.B, ∃ v∈Q.tits.B, s*x*s=l*s*v) ∧
    (t*x*t∈Q.tits.B ∨ ∃ l∈Q.tits.B, ∃ v∈Q.tits.B, t*x*t=l*t*v) :=
  originalS_reflected h Q split r (FivePositive.Relations.collects J heq)
    hgen cartan hc s t he x hx

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryPresentation
