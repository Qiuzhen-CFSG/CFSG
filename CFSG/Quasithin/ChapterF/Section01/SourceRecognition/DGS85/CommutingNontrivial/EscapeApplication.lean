module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ReciprocalEscape
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ChapterEightRows
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ReorientedConfiguration

/-!
# DGS 8.2 and the original reciprocal critical configuration

The full ending catalogue discharges the only numerical input to reciprocal
escape. Applying escape to the literal reduced F1.11 graph selects a reverse
critical pair with commuting centers. Its vertices, cores and spans belong
to the same reduced completion, and no starting or ending model is excluded.
This supplies the reciprocal configuration used after 8.2; it does not assert
the distance-three, equal-field or natural-module conclusions of 8.4–8.7.

Source: DGS, Groups and Graphs (1985), 8.2–8.3, printed pp.134–137;
the critical-pair selection is the same graph argument used in 9.2, p.142.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- Full DGS 8.2 on the actual reduced graph, preserving all earlier-source
premises and allowing either orientation of the critical pair. -/
theorem reduced_reciprocal_escape
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,
      Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓
      Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
    : ¬ V (Reduction.reducedFamily J S₀) a' 1 ≤
      Q (Reduction.reducedFamily J S₀) beta := by
  let : ∀ i, Finite (Reduction.reducedFamily J S₀ i) :=
    finite_endpoints (Reduction.reduced_triple h)
  let : Finite (graphLocalGroup (Reduction.reducedFamily J S₀) a') :=
    Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  exact source_reciprocal_escape_of_factor_bound (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reducedEarlierLocalTheorems h hob)
    hc hab hd hb hcomm models hne
    (reduced_ending_catalogue_bound h hob hc hab hd hb hcomm
      (MulEquiv.refl _) (models a'))

/-- Escape supplies an actual reverse critical pair, with the literal
commuting centers and unchanged opposite spans. This is the reciprocal
configuration required for the subsequent Chapter 8 comparisons. -/
theorem reduced_reciprocal_critical_configuration
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,
      Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓
      Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
    : let F := Reduction.reducedFamily J S₀
      ¬ V F a' 1 ≤ Q F beta ∧
      ∃ z : Vertex F, (graph F).Adj z a' ∧ IsCriticalPair F z beta ∧
        (graph F).dist a' beta + 1 = b F ∧
        ⁅Z F z, Z F beta⁆ = ⊥ ∧ ¬ Z F z ≤ Q F beta := by
  have he := reduced_reciprocal_escape h hob models hc hab hd hb hcomm hne
  obtain ⟨z,hz,hcz,hzQ⟩ := CommutingTrivial.reduced_reverse_criticalPair h
    (Reduction.reduced_kernel_sylow h) hd he
  refine ⟨he,z,hz.symm,hcz,?_,?_,hzQ⟩
  · rwa [SimpleGraph.dist_comm]
  · exact CommutingTrivial.reverse_critical_centers_commute (Reduction.reduced_triple h) hcz
      (Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm).2.2.1

/-- The Suzuki estimate is applied alongside full reciprocal escape to
prepare the two literal directions of the Chapter 8 index comparison.
This uses `ChapterEightRows` as an estimate, with its original model premise;
it asserts no additional classification or Chapter 8.3 conclusion. -/
theorem reduced_suzuki_comparison_configuration
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,
      Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓
      Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
    (m : ℕ) :
    let F := Reduction.reducedFamily J S₀
    ¬ V F a' 1 ≤ Q F beta ∧
    ∃ w : (graph F).neighborSet a',
      ⁅V F beta 1 ⊓ Q F a', Z F w.val⁆ ≠ ⊥ ∧
      (∀ _e : (graphLocalGroup F w.val ⧸ pCore 2 (graphLocalGroup F w.val)) ≃*
        SuzukiMatrixGroup m,
        (Q F w.val).relIndex (V F beta 1 ⊓ Q F a') ^ 2 ≤
          (centralizer ((V F beta 1 ⊓ Q F a' : Subgroup (Reduction.G₀ J S₀)) :
            Set (Reduction.G₀ J S₀))).relIndex (Z F w.val)) ∧
      ∃ z : Vertex F, (graph F).Adj z a' ∧ IsCriticalPair F z beta ∧
        (graph F).dist a' beta + 1 = b F ∧
        ⁅Z F z, Z F beta⁆ = ⊥ ∧ ¬ Z F z ≤ Q F beta := by
  obtain ⟨he,hreverse⟩ := reduced_reciprocal_critical_configuration
    h hob models hc hab hd hb hcomm hne
  obtain ⟨w,hm,hbound⟩ := reduced_chapterEight_suzuki_row h hob hc hab hd hb hcomm hne m
  exact ⟨he,w,hm,hbound,hreverse⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
