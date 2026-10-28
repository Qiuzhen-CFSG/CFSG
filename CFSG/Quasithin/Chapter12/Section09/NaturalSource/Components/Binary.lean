module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.Overgroups
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryNestedQuotients

/-!
# The binary point-model branch of the plane-component argument

A proper plane component inside the PSL₅(2) point model must have
PSL₄(2) or PSL₅(2) two-core quotient. Both are excluded by the literal
S₃ action on the original plane. Hence L₂ itself is the normal component
of its plane normalizer in this branch. Every remaining failure has an
actual M₂₄ or J₄ point quotient; the sporadic comparisons, other component
indices and abelianity remain with the natural-source assembly owner.

Source: Aschbacher--Smith, 12.9.3, printed pp.858--859.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- A proper plane overcomponent cannot be contained in a point component
with the binary five-space quotient. -/
theorem five_plane_not_binary_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) (J D : Subgroup G)
    (hJ : J ∈ Chapter1.cComponentsIn F.H)
    (hJm : ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 5 2)
    (hD : D ∈ Chapter1.cComponentsIn (F.Gi 2))
    (hDn : (D.subgroupOf (F.Gi 2)).Normal)
    (hLD : F.Li L 2 < D) (hDJ : D ≤ J) : False := by
  have hl := (Li_mem_local h earlier F 2 (Or.inl ⟨rfl,by decide,by decide⟩)).1
  have hd : D ∈ ChapterA.Section03.localCComponents T :=
    hD.2.subgroupOf_of_le le_sup_left (sup_le hD.1 (F.invariant 2))
  have hj : J ∈ ChapterA.Section03.localCComponents T :=
    hJ.2.subgroupOf_of_le le_sup_left (sup_le hJ.1 (F.invariant 1))
  have hm : ClassicalGroup.IsPSL (F.Li L 2 ⧸ pCore 2 (F.Li L 2)) 3 2 :=
    Li_core_model h F 2 (Or.inl ⟨rfl,by decide,by decide⟩)
  rcases ChapterA.Section03.SourceEmbeddings.BinaryNested.strict_three_in_five_models T hl hd hj hLD hDJ hm hJm with hm | hm
  · exact plane_component_not_linear h F D hD hDn (Or.inl rfl) hm
  · exact plane_component_not_linear h F D hD hDn (Or.inr rfl) hm

/-- The actual plane residual is a relatively normal C-component when the
containing point component has the PSL₅(2) quotient. -/
theorem five_plane_component_of_binary_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) (J : Subgroup G)
    (hJ : J ∈ Chapter1.cComponentsIn F.H) (hLJ : F.Li L 1 ≤ J)
    (hJn : (J.subgroupOf F.H).Normal)
    (hJm : ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 5 2) :
    ((F.Li L 2).subgroupOf (F.Gi 2)).IsCComponent ∧
      ((F.Li L 2).subgroupOf (F.Gi 2)).Normal := by
  obtain ⟨D,hd,_⟩ := exists_unique_normal_local_component h earlier F 2
    (Or.inl ⟨rfl,by decide,by decide⟩)
  have he : D = F.Li L 2 := by
    by_contra hne
    exact five_plane_not_binary_point h earlier F J D hJ hJm hd.1 hd.2.2
      (lt_of_le_of_ne hd.2.1 (Ne.symm hne))
      (five_plane_component_lt_point h earlier F D hd.1 hd.2.1 J hJ.1 hLJ hJn).le
  exact he ▸ ⟨hd.1.2,hd.2.2⟩

/-- This branch supplies the original component record, retaining the
chosen point component J. Only the dimension-three component assertion
remains explicit for qt-d-1291-natural-source. -/
theorem five_componentGeometry_of_binary_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) (J : Subgroup G)
    (hJ : J ∈ Chapter1.cComponentsIn F.H) (hLJ : F.Li L 1 ≤ J)
    (hJn : (J.subgroupOf F.H).Normal)
    (hJm : ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 5 2)
    (hthree : ((F.Li L 3).subgroupOf (F.Gi 3)).IsCComponent ∧
      ((F.Li L 3).subgroupOf (F.Gi 3)).Normal) :
    ∃ C : ComponentGeometry F L, C.K1 = J := by
  refine ⟨⟨J,hJ.1,hLJ,hJ.2,hJn,Or.inr (Or.inl (Or.inl hJm)),?_⟩,rfl⟩
  intro i hi
  rcases (show i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl
  · exact five_plane_component_of_binary_point h earlier F J hJ hLJ hJn hJm
  · exact hthree
  · exact five_hyperplane_component h earlier F

/-- Every remaining plane failure has a genuine sporadic point quotient.
The original strict nested components, their relative normality, and the
literal join quotient are retained for the two remaining model comparisons. -/
theorem exists_five_sporadic_plane_components
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5)
    (hfail : ¬ (((F.Li L 2).subgroupOf (F.Gi 2)).IsCComponent ∧
      ((F.Li L 2).subgroupOf (F.Gi 2)).Normal)) :
    ∃ J D : Subgroup G,
      J ∈ Chapter1.cComponentsIn F.H ∧ F.Li L 1 < J ∧
      (J.subgroupOf F.H).Normal ∧
      (Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.Mathieu.M24) ∨
        Nonempty ((J ⧸ pCore 2 J) ≃* Janko4.Model)) ∧
      D ∈ Chapter1.cComponentsIn (F.Gi 2) ∧ F.Li L 2 < D ∧
      (D.subgroupOf (F.Gi 2)).Normal ∧ D < J ∧
      (Nonempty (((J ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (J ⊔ (T : Subgroup G) : Subgroup G)) ≃* Sporadic.Mathieu.M24) ∨
      Nonempty (((J ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (J ⊔ (T : Subgroup G) : Subgroup G)) ≃* Janko4.Model)) := by
  obtain ⟨J,D,hJ,hLJ,hJn,hm,hD,hLD,hDn,hDJ,_⟩ :=
    exists_five_strict_plane_components h earlier F hfail
  have hspor : Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.Mathieu.M24) ∨
      Nonempty ((J ⧸ pCore 2 J) ≃* Janko4.Model) := by
    rcases hm with hb | hs
    · exact (five_plane_not_binary_point h earlier F J D hJ hb hD hDn hLD hDJ.le).elim
    · exact hs
  obtain ⟨e⟩ := (five_point_join_quotient_model h earlier F J hJ.1 hLJ.le hJn hm).1
  refine ⟨J,D,hJ,hLJ,hJn,hspor,hD,hLD,hDn,hDJ,?_⟩
  rcases hspor with ha | ha
  · obtain ⟨a⟩ := ha
    exact Or.inl ⟨e.trans a⟩
  · obtain ⟨a⟩ := ha
    exact Or.inr ⟨e.trans a⟩

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
