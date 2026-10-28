module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.BorelCells
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryPresentation.SourceRankOne

/-!
# Root-and-Cartan two-cell collection on the original quotient

Both reflection calculations apply to an original S image followed by any
full torus parameter. Every factor remains in the actual source Borel.
This does not assume or assert that the Cartan map is onto B intersect N;
that equality belongs to the later presentation and marked comparison.
Source: DGS, Theorem D, p.224; Steinberg, Lectures on Chevalley Groups,
Lemmas 21–24 and Theorem 33.
-/
public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryPresentation
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {E : Type*} [Field E] [CharP E 2]
variable {H : Type*} [Group H]

/-- The generic source application, before either field-parametrized specialization. -/
theorem originalS_torus_rankOne
    {RA RD RC RB : Type*} [Group RA] [Group RD] [Group RC] [Group RB]
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (r : PositiveMaps ((generated L S) ⧸ Q.D) RA RD RC RB)
    (hcol : r.Collects) (hgen : r.generated=split.U)
    (cartan : H →* ((generated L S) ⧸ Q.D))
    (hc : cartan.range≤Q.tits.B ⊓ Q.tits.N) (ht : r.TorusLaws cartan)
    (s t : (generated L S) ⧸ Q.D) (he : ReflectionLaws r cartan s t)
    (hsh : ∀ k, ∃ l, s*cartan k*s=cartan l)
    (hth : ∀ k, ∃ l, t*cartan k*t=cartan l)
    (x : (generated L S) ⧸ Q.D) (hx : x∈(S.subgroupOf (generated L S)).map Q.q) (k : H) :
    (s*(x*cartan k)*s∈Q.tits.B ∨
      ∃ l∈Q.tits.B, ∃ v∈Q.tits.B, s*(x*cartan k)*s=l*s*v) ∧
    (t*(x*cartan k)*t∈Q.tits.B ∨
      ∃ l∈Q.tits.B, ∃ v∈Q.tits.B, t*(x*cartan k)*t=l*t*v) := by
  rw [quotient_sourceS_image_eq_unipotent h Q split,←hgen] at hx
  have hB : r.borel cartan≤Q.tits.B := sup_le (hgen.le.trans split.U_le) (hc.trans inf_le_left)
  have hxB : x*cartan k∈r.borel cartan :=
    (r.borel cartan).mul_mem ((le_sup_left : r.generated≤r.borel cartan) hx)
      ((le_sup_right : cartan.range≤r.borel cartan) ⟨k,rfl⟩)
  constructor
  · rcases he.s_borel hcol ht hsh hxB with hm|⟨l,hl,v,hv,heq⟩
    · exact Or.inl (hB hm)
    · exact Or.inr ⟨l,hB hl,v,hB hv,heq⟩
  · rcases he.t_borel hcol ht hth hxB with hm|⟨l,hl,v,hv,heq⟩
    · exact Or.inl (hB hm)
    · exact Or.inr ⟨l,hB hl,v,hB hv,heq⟩

omit [CharP E 2] in
/-- U₄ specialization retains the actual fixed-field root parameters. -/
theorem four_originalS_torus_rankOne (h : HypothesisF11 L S) (Q : SourceQuotient L S)
    (split : SplitData Q.tits) (σ : E ≃+* E) (hσ : Function.Involutive σ)
    (r : PositiveMaps ((generated L S) ⧸ Q.D)
      (Multiplicative E) (Multiplicative (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FixedField E σ))
      (Multiplicative E) (Multiplicative (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.FixedField E σ)))
    (heq : FourPositive.Relations E σ hσ r) (hgen : r.generated=split.U)
    (cartan : H →* ((generated L S) ⧸ Q.D)) (hc : cartan.range≤Q.tits.B ⊓ Q.tits.N)
    (ht : r.TorusLaws cartan)
    (s t : (generated L S) ⧸ Q.D) (he : ReflectionLaws r cartan s t)
    (hsh : ∀ k, ∃ l, s*cartan k*s=cartan l)
    (hth : ∀ k, ∃ l, t*cartan k*t=cartan l)
    (x : (generated L S) ⧸ Q.D) (hx : x∈(S.subgroupOf (generated L S)).map Q.q) (k : H) :
    (s*(x*cartan k)*s∈Q.tits.B ∨
      ∃ l∈Q.tits.B, ∃ v∈Q.tits.B, s*(x*cartan k)*s=l*s*v) ∧
    (t*(x*cartan k)*t∈Q.tits.B ∨
      ∃ l∈Q.tits.B, ∃ v∈Q.tits.B, t*(x*cartan k)*t=l*t*v) :=
  originalS_torus_rankOne h Q split r (FourPositive.Relations.collects E σ hσ heq)
    hgen cartan hc ht s t he hsh hth x hx k

/-- General U₅ specialization retains both entire Hermitian parameter groups. -/
theorem five_originalS_torus_rankOne (h : HypothesisF11 L S) (Q : SourceQuotient L S)
    (split : SplitData Q.tits) (J : HermitianForm 5 E)
    (r : PositiveMaps ((generated L S) ⧸ Q.D) (Multiplicative E) (FivePositive.Parameter J)
      (Multiplicative E) (FivePositive.Parameter J))
    (heq : FivePositive.Relations J r) (hgen : r.generated=split.U)
    (cartan : H →* ((generated L S) ⧸ Q.D)) (hc : cartan.range≤Q.tits.B ⊓ Q.tits.N)
    (ht : r.TorusLaws cartan)
    (s t : (generated L S) ⧸ Q.D) (he : ReflectionLaws r cartan s t)
    (hsh : ∀ k, ∃ l, s*cartan k*s=cartan l)
    (hth : ∀ k, ∃ l, t*cartan k*t=cartan l)
    (x : (generated L S) ⧸ Q.D) (hx : x∈(S.subgroupOf (generated L S)).map Q.q) (k : H) :
    (s*(x*cartan k)*s∈Q.tits.B ∨
      ∃ l∈Q.tits.B, ∃ v∈Q.tits.B, s*(x*cartan k)*s=l*s*v) ∧
    (t*(x*cartan k)*t∈Q.tits.B ∨
      ∃ l∈Q.tits.B, ∃ v∈Q.tits.B, t*(x*cartan k)*t=l*t*v) :=
  originalS_torus_rankOne h Q split r (FivePositive.Relations.collects J heq)
    hgen cartan hc ht s t he hsh hth x hx k

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryPresentation
