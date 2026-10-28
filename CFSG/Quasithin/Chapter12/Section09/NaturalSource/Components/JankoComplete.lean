module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.JankoMathieu
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoExclusion

/-!
# The complete degree-five plane assertion of source 12.9.3

The original strict J₄ plane pair passes through the literal quotient
JT/O₂(JT), retaining both local components, their intrinsic quotients,
the full Sylow actor and strict inclusion. The nontrivial plane core,
quasisimplicity, and exclusions of PSL₄(2) and M₂₄ are already consequences
of the source hypotheses. The native J₄ comparison now contradicts these
data, with no placement or classification callback.

Together with the checked normal-point, binary and Mathieu branches,
this proves that the original solvable residual L₂ is a C-component
normal in N_G(V₂). The actual ComponentGeometry application now needs
only the dimension-three component assertion in degree five. That case,
the degree-four cases, nonnormal abelianity and original local-control
premises remain with qt-d-1291-natural-source. NaturalBranchInput is not
yet asserted.

Source: Aschbacher--Smith 12.9.3, printed pp.858--859 of refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Subgroup Theory.GroupTheory
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- The complete J4 comparison excludes every original strict plane enlargement. -/
theorem five_plane_not_janko_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) (J D : Subgroup G)
    (hJ : J ∈ Chapter1.cComponentsIn F.H) (hLJ : F.Li L 1 ≤ J)
    (hJn : (J.subgroupOf F.H).Normal)
    (hJm : Nonempty ((J ⧸ pCore 2 J) ≃* Janko4.Model))
    (hD : D ∈ Chapter1.cComponentsIn (F.Gi 2))
    (hDn : (D.subgroupOf (F.Gi 2)).Normal)
    (hLD : F.Li L 2 < D) (hDJ : D < J) : False := by
  let X := J ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 X)
  let B := (D.subgroupOf X).map q
  let A := ((F.Li L 2).subgroupOf X).map q
  let S := (T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)).mapSurjective
    (QuotientGroup.mk'_surjective (pCore 2 X))
  have hDX : D ≤ X := hDJ.le.trans le_sup_left
  have hm : LargePointModel (J ⧸ pCore 2 J) := Or.inr (Or.inr hJm)
  have hmodels := five_quotient_local_models h earlier F J D hJ hLJ hm hD hDJ.le
  have hn : (S : Subgroup (X ⧸ pCore 2 X)) ≤ normalizer (B : Set _) := by
    have hTD : (T : Subgroup G) ≤ normalizer (D : Set G) :=
      (F.invariant 2).trans ((normal_subgroupOf_iff_le_normalizer hD.1).mp hDn)
    have hnX : (T : Subgroup G).subgroupOf X ≤ normalizer (D.subgroupOf X : Set X) := by
      rw [←subgroupOf_normalizer_eq hDX]
      exact comap_mono hTD
    exact (map_mono (f := q) hnX).trans ((D.subgroupOf X).le_normalizer_map q)
  have hk : IsPGroup 2 (q.subgroupMap (D.subgroupOf X)).ker := by
    rw [ker_subgroupMap]
    have hq : IsPGroup 2 q.ker := by
      rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
    exact hq.comap_subtype
  let d := subgroupOfEquivOfLe hDX
  let a := (QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).symm.trans
    ((q.subgroupMap (D.subgroupOf X)).pCoreQuotientEquiv
      (q.subgroupMap_surjective _) hk)
  have hquasi : IsQuasisimple (B ⧸ pCore 2 B) :=
    (five_sporadic_plane_component_quasisimple h F J D (Or.inr hJm) hD hLD.le hDJ.le).of_mulEquiv a
  have hXH : X ≤ F.H := sup_le hJ.1 (F.invariant 1)
  have hsqX : IsSQTK KnownSimple.IsKnownSimple X :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hXH)).mp
      ((h.source.simpleQTKE.twoLocal_sqtk (Gi_twoLocal h F 1 (by decide))).subgroup
        (X.subgroupOf F.H))
  have hsqQ := ChapterE.Structure.sqtk_two_quotient hsqX (pCore 2 X) pCore_isPGroup
  have hlt : A < B :=
    (five_quotient_overgroup_chain h earlier F J D hJ hLJ hJn hD hDn hLD hDJ).2.2.2.1
  have hna : (S : Subgroup (X ⧸ pCore 2 X)) ≤ normalizer (A : Set _) := by
    have hAX : F.Li L 2 ≤ X := hLD.le.trans hDX
    have hnX : (T : Subgroup G).subgroupOf X ≤ normalizer ((F.Li L 2).subgroupOf X : Set X) := by
      rw [←subgroupOf_normalizer_eq hAX]
      exact comap_mono (sylow_normalizes_Li h earlier F 2)
    exact (map_mono (f := q) hnX).trans (((F.Li L 2).subgroupOf X).le_normalizer_map q)
  obtain ⟨e⟩ := (five_point_join_quotient_model h earlier F J hJ.1 hLJ hJn hm).1
  exact ChapterA.Section03.SourceEmbeddings.JankoMathieu.not_strict_three_pair
    (e.trans hJm.some) hsqQ S hmodels.2.1 hmodels.2.2.1 hlt hna hn hmodels.2.2.2.2.1
    hquasi (five_janko_plane_image_core_ne_bot h earlier F J D hJ hLJ hJn hJm hD hDn hLD hDJ)
    (fun hb => plane_component_not_linear h F D hD hDn (Or.inl rfl) (hb.of_mulEquiv a))
    (fun hb => plane_component_not_mathieu h F D hD hDn ⟨a.trans hb.some⟩)

/-- The original plane-component assertion is proved for the J4 point row,
with normality in the literal plane normalizer. -/
theorem five_plane_component_of_janko_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) (J : Subgroup G)
    (hJ : J ∈ Chapter1.cComponentsIn F.H) (hLJ : F.Li L 1 ≤ J)
    (hJn : (J.subgroupOf F.H).Normal)
    (hJm : Nonempty ((J ⧸ pCore 2 J) ≃* Janko4.Model)) :
    ((F.Li L 2).subgroupOf (F.Gi 2)).IsCComponent ∧
      ((F.Li L 2).subgroupOf (F.Gi 2)).Normal := by
  obtain ⟨D,hd,_⟩ := exists_unique_normal_local_component h earlier F 2
    (Or.inl ⟨rfl,by decide,by decide⟩)
  have he : D = F.Li L 2 := by
    by_contra hne
    exact five_plane_not_janko_point h earlier F J D hJ hLJ hJn hJm hd.1 hd.2.2
      (lt_of_le_of_ne hd.2.1 (Ne.symm hne))
      (five_plane_component_lt_point h earlier F D hd.1 hd.2.1 J hJ.1 hLJ hJn)
  exact he ▸ ⟨hd.1.2,hd.2.2⟩

/-- The complete degree-five plane assertion of source 12.9.3. All point
models are discharged, with the original solvable residual and normalizer. -/
theorem five_plane_component
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) :
    ((F.Li L 2).subgroupOf (F.Gi 2)).IsCComponent ∧
      ((F.Li L 2).subgroupOf (F.Gi 2)).Normal := by
  by_contra hfail
  obtain ⟨J,D,hJ,hLJ,hJn,hm,hD,hLD,hDn,hDJ,_⟩ :=
    exists_five_janko_plane_components h earlier F hfail
  exact five_plane_not_janko_point h earlier F J D hJ hLJ.le hJn hm hD hDn hLD hDJ

/-- The actual degree-five ComponentGeometry consumer now requires only
the dimension-three component assertion, retained by this source owner. -/
theorem five_componentGeometry_of_three_component
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5)
    (hthree : ((F.Li L 3).subgroupOf (F.Gi 3)).IsCComponent ∧
      ((F.Li L 3).subgroupOf (F.Gi 3)).Normal) : Nonempty (ComponentGeometry F L) := by
  apply five_componentGeometry_of_middle_components h earlier F
  intro i hi
  rcases hi with rfl | rfl
  · exact five_plane_component h earlier F
  · exact hthree

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
