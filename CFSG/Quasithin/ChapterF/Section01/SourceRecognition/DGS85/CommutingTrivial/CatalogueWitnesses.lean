module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.MixedSourceRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ReciprocalDihedralExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.NaturalResidualDihedralExclusion

/-!
# Chapter 9 model witnesses from the full source catalogue

In the small-neighbor branch, the two mixed index comparisons recognize
both linear quotients directly from the full catalogue. In the escape branch,
the actual dihedral residual square bound first excludes the beta dihedral
row. The existing reciprocal recognition then produces the natural beta
section, which excludes the alpha dihedral row by the original core obstruction.
Conjugacy supplies the terminal marking in both branches.

Thus the three concrete binary-model witnesses used by the later Chapter 9
argument are consequences of its original catalogue and geometry. The earlier
Chapter 8 exchange statement remains explicit here and is discharged at the
final source consumer. Source: DGS, Groups and Graphs (1985), 9.2--9.4, pp.142--143.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- All three concrete witnesses are obtained from the retained source catalogue;
no dihedral row is dropped and no natural-section premise is assumed. -/
theorem reduced_critical_binary_models_of_source (h : HypothesisF11 L S₀)
    (models : ∀ v : Vertex (Reduction.reducedFamily L S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (htriv : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓ Q (Reduction.reducedFamily L S₀) a',
      V (Reduction.reducedFamily L S₀) a' 1⁆ = ⊥)
    (h8 : ∀ z : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj z a' →
      IsCriticalPair (Reduction.reducedFamily L S₀) z beta →
      ⁅Z (Reduction.reducedFamily L S₀) z, Z (Reduction.reducedFamily L S₀) beta⁆ = ⊥ →
      ⁅V (Reduction.reducedFamily L S₀) a' 1 ⊓ Q (Reduction.reducedFamily L S₀) beta,
        V (Reduction.reducedFamily L S₀) beta 1⁆ ≠ ⊥ →
      ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
        b (Reduction.reducedFamily L S₀) = 3 ∧
          Nonempty ((graphLocalGroup (Reduction.reducedFamily L S₀) z ⧸
            pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) z)) ≃* SL(2,F))) :
    let Γ := Reduction.reducedFamily L S₀
    Nonempty (BinaryRankOneModel (graphLocalGroup Γ a ⧸ pCore 2 (graphLocalGroup Γ a)) ×
      BinaryRankOneModel (graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)) ×
      BinaryRankOneModel (graphLocalGroup Γ a' ⧸ pCore 2 (graphLocalGroup Γ a'))) := by
  let Γ := Reduction.reducedFamily L S₀
  let hob := Reduction.reduced_graph_core_obstruction h
  by_cases hs : V Γ a' 1 ≤ Q Γ beta
  · obtain ⟨_,F,instF,finF,charF,K,instK,finK,charK,n,m,hn,hF,hm,hK,⟨eα⟩,⟨eβ⟩⟩ :=
      reduced_small_neighbor_source_linear_markings h hc hab hd hb hcomm htriv hs hob
        (models a) (models a')
    let := instF
    let := finF
    let := charF
    let := instK
    let := finK
    let := charK
    obtain ⟨g,e₀,f,hg,he₀,hf,_⟩ := reduced_critical_parameter_transport h hc hab hd hb hcomm
    exact ⟨.sl2 F n hn hF eα, .sl2 K m hm hK eβ, .sl2 K m hm hK (f.trans eβ)⟩
  · have hnd : ¬ Nonempty ((graphLocalGroup Γ beta ⧸
        pCore 2 (graphLocalGroup Γ beta)) ≃* DihedralGroup 5) := by
      rintro ⟨ed⟩
      exact reduced_large_neighbor_not_dihedral h hc hab hd hb hcomm htriv hs ed
    obtain ⟨Mβ⟩ := (models beta).binaryModel_of_not_dihedral hnd
    obtain ⟨F,instF,finF,charF,n,hn,hF,eβ,e',_,_,_,_,_,hres,_⟩ :=
      reduced_large_neighbor_recognized_sections h hc hab hd hb hcomm htriv hs h8 hob Mβ
    let := instF
    let := finF
    let := charF
    have hna : ¬ Nonempty ((graphLocalGroup Γ a ⧸
        pCore 2 (graphLocalGroup Γ a)) ≃* DihedralGroup 5) := by
      rintro ⟨ed⟩
      exact reduced_natural_residual_not_dihedral h hc hab hd hb hcomm
        (models a) hn hF eβ hres ed
    obtain ⟨Mα⟩ := (models a).binaryModel_of_not_dihedral hna
    exact ⟨Mα, Mβ, .sl2 F n hn hF e'⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
