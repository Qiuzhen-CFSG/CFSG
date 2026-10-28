module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.PathBorel

/-!
# The path actor in the critical-distance-three configuration

Source 8.1 chooses the predecessor of alpha-prime, containing V_beta.
At critical distance three this predecessor is adjacent to beta as well.
The original 6.5 obstruction makes its core escape Q_beta, and the path
image theorem then gives the full beta Borel unless the predecessor local
quotient is D₁₀. All subgroups and quotient maps remain the literal ones
of the reduced F1.11 graph.

Source: DGS, *Groups and Graphs* (1985), 8.1 and the natural alternative
in 8.5, printed pp.132--133 and 139.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The actual critical-distance-three path has the beta Borel image, with
only the explicit D₁₀ middle alternative retained. The predecessor core
containment is carried alongside the image for its residual-section use. -/
theorem reduced_critical_path_borel_or_dihedral
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓
          Q (Reduction.reducedFamily J S₀) v : Subgroup (Reduction.G₀ J S₀)) :
          Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily J S₀))
    (hb : b (Reduction.reducedFamily J S₀) = 3)
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,
      Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e : (graphLocalGroup (Reduction.reducedFamily J S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) beta)) ≃* SL(2,k)) :
    let F := Reduction.reducedFamily J S₀
    let L := graphLocalGroup F beta
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
    ∃ mid : Vertex F, (graph F).Adj beta mid ∧ (graph F).Adj a' mid ∧
      V F beta 1 ≤ Q F mid ∧ ¬ Q F mid ≤ Q F a' ∧
      (Nonempty ((graphLocalGroup F mid ⧸ pCore 2 (graphLocalGroup F mid)) ≃*
        DihedralGroup 5) ∨
      ∃ T : Sylow 2 SL(2,k), ((Q F mid).subgroupOf L).map q = T ∧
        ((stabilizer F mid ⊓ stabilizer F a').subgroupOf L).map q =
          normalizer (T : Set SL(2,k)) ∧
        ∀ l : L, q l ∈ normalizer (T : Set SL(2,k)) ↔
          (l : Reduction.G₀ J S₀) • mid = mid) := by
  let F := Reduction.reducedFamily J S₀
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedEarlierLocalTheorems h hob
  have hb1 : 1 < b F := by change 1 < b (Reduction.reducedFamily J S₀); omega
  obtain ⟨_,_,_,_,mid,ham,hdm,hVm,hescape⟩ :=
    source_critical_geometry ht d hc hab hd hb1 hcomm
  change (graph F).dist beta mid + 1 = (graph F).dist beta a' at hdm
  have hdist : (graph F).dist beta a' = 2 := by
    change (graph (Reduction.reducedFamily J S₀)).dist beta a' = 2
    omega
  have hbm : (graph F).Adj beta mid := SimpleGraph.dist_eq_one_iff_adj.mp (by
    omega)
  have hne : beta ≠ a' := by
    intro he
    simp only [he,SimpleGraph.dist_self] at hdist
    omega
  refine ⟨mid,hbm,ham,hVm,hescape,?_⟩
  by_cases hi : Nonempty ((graphLocalGroup F mid ⧸ pCore 2 (graphLocalGroup F mid)) ≃*
      DihedralGroup 5)
  · exact Or.inl hi
  · exact Or.inr (reduced_linear_path_borel_image_of_not_dihedral h hob models
      hbm ham hne hi e)
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
