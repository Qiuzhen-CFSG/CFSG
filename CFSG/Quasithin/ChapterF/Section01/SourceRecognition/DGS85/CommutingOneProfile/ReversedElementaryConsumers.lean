module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReversedElementarySource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryMarkedConsumers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.FieldDegreeConsumers

/-!
# Original-pair recognition when the linear factor is at beta

The original left PSL2 marking makes its actual Borel two-core quotient
elementary. Reorienting the critical pair therefore feeds the completed
nonbinary elementary construction, without a supplied branch selection,
local catalogue or Chapter 14 premise. Reverse the marked maps back before
Chapter 15 restores both original endpoints and the full original Borel.

The Chapter 12 consumer uses full KnownSimple and its same selected perfect
right factor. The unitary and binary source branches remain separate.
Source: DGS, Groups and Graphs (1985), (11.7), pp.174--175,
Theorem D and (15.2), pp.224,226--228; Aschbacher--Smith F.1.12 and 12.2.2.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- A distance-one critical pair can be moved to the actual base edge;
its direction is retained in the two alternatives. -/
theorem original_critical_base_edge_or_reverse (h : HypothesisF11 L S)
    (hb : b (Reduction.reducedFamily L S) = 1) :
    IsCriticalPair (Reduction.reducedFamily L S)
        (base (Reduction.reducedFamily L S) false) (base (Reduction.reducedFamily L S) true) ∨
      IsCriticalPair (Reduction.reducedFamily L S)
        (base (Reduction.reducedFamily L S) true) (base (Reduction.reducedFamily L S) false) := by
  let F := Reduction.reducedFamily L S
  let _ : ∀ i, Finite (F i) := finite_endpoints (Reduction.reduced_triple h)
  obtain ⟨a,c,hc⟩ := source_exists_criticalPair (Reduction.reduced_triple h)
  have hadj := SimpleGraph.dist_eq_one_iff_adj.mp (hc.1.trans hb)
  obtain ⟨g,hga,hgc⟩ := incident_common_translate F hadj.2
  have hc' := CommutingNontrivial.criticalPair_translate F hc g⁻¹
  rw [←hga,←hgc,inv_smul_smul,inv_smul_smul] at hc'
  have hne := hadj.1
  cases ha : a.type <;> cases hc : c.type
  · exact (hne (ha.trans hc.symm)).elim
  · exact .inl (by simpa only [ha,hc] using hc')
  · exact .inr (by simpa only [ha,hc] using hc')
  · exact (hne (ha.trans hc.symm)).elim

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85 ChapterF.Source.DGS85.CommutingOneProfile
open ChapterF.Source.DGS85.OriginalExtension ChapterF.Source.SuzukiContainment
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory RankTwoAmalgam
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}

/-- With the original left linear factor at beta, the source constructs
and restores the reversed marked U4 comparison. The elementary quotient,
both catalogues, reflections, exchange and root signs are all discharged. -/
theorem comparison_of_commuting_one_reversed_linear_source
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (sourceS L H))
      (base (Reduction.reducedFamily ![L,R] (sourceS L H)) true)
      (base (Reduction.reducedFamily ![L,R] (sourceS L H)) false))
    (hb : b (Reduction.reducedFamily ![L,R] (sourceS L H)) = 1)
    (hcomm : ⁅Z (Reduction.reducedFamily ![L,R] (sourceS L H))
        (base (Reduction.reducedFamily ![L,R] (sourceS L H)) false),
      Z (Reduction.reducedFamily ![L,R] (sourceS L H))
        (base (Reduction.reducedFamily ![L,R] (sourceS L H)) true)⁆ = ⊥) :
    ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) := by
  obtain ⟨m,hm,⟨f⟩⟩ := ReversedElementary.reversed_linear_reduced_comparison
    L R (sourceS L H) (d.hypothesisF11 h hTH) hc hb hcomm h.exponent h.linear
  exact d.concreteComparison_of_reduced_alternatives h hTH hp (.unitaryFour m hm true ⟨f⟩)

/-- At original field degree two or three, the alpha orientation is
impossible and the reversed linear construction completes this source
branch. The caller supplies no directed critical pair. -/
theorem comparison_of_commuting_one_small_degree_source
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R) (hsmall : n < 4)
    (hb : b (Reduction.reducedFamily ![L,R] (sourceS L H)) = 1)
    (hcomm : ⁅Z (Reduction.reducedFamily ![L,R] (sourceS L H))
        (base (Reduction.reducedFamily ![L,R] (sourceS L H)) false),
      Z (Reduction.reducedFamily ![L,R] (sourceS L H))
        (base (Reduction.reducedFamily ![L,R] (sourceS L H)) true)⁆ = ⊥) :
    ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) := by
  rcases original_critical_base_edge_or_reverse (d.hypothesisF11 h hTH) hb with hc | hc
  · obtain ⟨m,hm,he⟩ := d.commuting_one_field_degree h hTH hp hc hb hcomm
    omega
  · exact d.comparison_of_commuting_one_reversed_linear_source h hTH hp hc hb hcomm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85 ChapterF.Source.DGS85.CommutingOneProfile
open ChapterF.Source.DGS85.OriginalExtension ChapterF.Source.SuzukiContainment
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory RankTwoAmalgam
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  {A B R : Subgroup G} (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
  (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (Global.sourceS L H))
    (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) true)
    (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) false))
  (hb : b (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) = 1)
  (hcomm : ⁅Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H))
      (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) false),
    Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H))
      (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) true)⁆ = ⊥)

include D h hmany hn hpsl hH d hp hc hb hcomm in
/-- The full KnownSimple chosen-module consumer in the reverse critical
orientation, on the same original pair and full Borel. -/
theorem rankOne_comparison_of_commuting_one_reversed_linear_source :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) :=
  d.comparison_of_commuting_one_reversed_linear_source
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp
    hc hb hcomm

include D h hmany hn hpsl hH d hp hb hcomm in
/-- Both critical orientations of the commuting distance-one branch are
resolved at small original left field degree, with full KnownSimple. -/
theorem rankOne_comparison_of_commuting_one_small_degree_source (hsmall : n < 4) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) :=
  d.comparison_of_commuting_one_small_degree_source
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp hsmall hb hcomm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
