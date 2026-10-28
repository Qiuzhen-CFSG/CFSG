module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.EightCells
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryPresentation.SourceBorelCells

/-!
# Eight-cell collection on the original quotient

The unitary equations and generation give eight cells on the original
finite quotient, with both outer factors collected in the actual source
Borel. The source owner still supplies the equations and generation. No
Cartan surjectivity, source recognition, or endpoint comparison is asserted.
Source: DGS, Theorem D, printed p.224; Steinberg, Lectures on Chevalley
Groups, Lemma 25 and Theorem 4(a).
-/
public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryPresentation
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {RA RD RC RB H : Type*} [Group RA] [Group RD] [Group RC] [Group RB] [Group H]

/-- The original finite quotient has eight cells for its supplied unitary
coordinates, before faithfulness or marked recognition is asserted. -/
theorem original_quotient_eight_cells
    (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (r : PositiveMaps ((generated L S) ⧸ Q.D) RA RD RC RB)
    (hcol : r.Collects) (hroot : r.generated≤split.U)
    (cartan : H →* ((generated L S) ⧸ Q.D))
    (hc : cartan.range≤Q.tits.B ⊓ Q.tits.N) (ht : r.TorusLaws cartan)
    (s t : (generated L S) ⧸ Q.D) (he : ReflectionLaws r cartan s t)
    (hsh : ∀ k, ∃ l, s*cartan k*s=cartan l)
    (hth : ∀ k, ∃ l, t*cartan k*t=cartan l) (hst : (s*t)^4=1)
    (hgen : ReflectionLaws.fullGenerated r cartan s t=⊤)
    (x : (generated L S) ⧸ Q.D) :
    ∃ w : WeylWord, ∃ a d c b k a' d' c' b' k',
      x=(r.word a d c b*cartan k)*w.eval s t*(r.word a' d' c' b'*cartan k') ∧
      r.word a d c b*cartan k∈Q.tits.B ∧ r.word a' d' c' b'*cartan k'∈Q.tits.B := by
  have hx : x∈ReflectionLaws.fullGenerated r cartan s t := hgen ▸ mem_top x
  obtain ⟨w,l,hl,v,hv,heq⟩ := he.exists_cell hcol ht hsh hth hst hx
  have hB : r.borel cartan≤Q.tits.B := sup_le (hroot.trans split.U_le) (hc.trans inf_le_left)
  obtain ⟨a,d,c,b,k,hl'⟩ := ht.exists_word hcol hl
  obtain ⟨a',d',c',b',k',hv'⟩ := ht.exists_word hcol hv
  exact ⟨w,a,d,c,b,k,a',d',c',b',k',by simpa only [←hl',←hv'] using heq,
    hl' ▸ hB hl,hv' ▸ hB hv⟩
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryPresentation
