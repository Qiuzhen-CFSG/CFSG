module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.Sporadic
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.MathieuRank

/-!
# The complete Mathieu plane-component comparison

In every strict degree-five plane enlargement with M₂₄ point quotient,
the actual plane image in JT/O₂(JT) is quasisimple, has trivial two-core,
and admits the faithful action of the original quotient Sylow. The
original PSL₃(2) section supplies a factor seven. SQTK descends from the
original point normalizer through its subgroup and two-core quotient.
The complete rank-and-order comparison therefore makes the plane image
the whole quotient, contradicting the proved strict overgroup chain.

This proves the original plane-component assertion in the M₂₄ point row
and reduces every remaining plane failure to J₄. The J₄ comparison, the
other component indices, nonnormal abelianity and the original local-control
premises remain with qt-d-1291-natural-source; this is not ComponentInput.

Source: Aschbacher--Smith 12.9.3, printed pp.858--859 of refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Subgroup Theory.GroupTheory
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- All surviving original Mathieu plane invariants force its image to
be the whole literal JT/O₂(JT) quotient. -/
theorem five_mathieu_plane_image_eq_top
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) (J D : Subgroup G)
    (hJ : J ∈ Chapter1.cComponentsIn F.H) (hLJ : F.Li L 1 ≤ J)
    (hJn : (J.subgroupOf F.H).Normal)
    (hJm : Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.Mathieu.M24))
    (hD : D ∈ Chapter1.cComponentsIn (F.Gi 2))
    (hDn : (D.subgroupOf (F.Gi 2)).Normal)
    (hLD : F.Li L 2 < D) (hDJ : D < J) :
    let X := J ⊔ (T : Subgroup G)
    let B := (D.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
    B = ⊤ := by
  let X := J ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 X)
  let B := (D.subgroupOf X).map q
  let A := ((F.Li L 2).subgroupOf X).map q
  let S := (T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)).mapSurjective
    (QuotientGroup.mk'_surjective (pCore 2 X))
  change B = ⊤
  have hDX : D ≤ X := hDJ.le.trans le_sup_left
  have hm : LargePointModel (J ⧸ pCore 2 J) := Or.inr (Or.inl hJm)
  obtain ⟨hquasi,hfaith⟩ :=
    five_mathieu_plane_image_quasisimple_faithful h earlier F J D hJ hLJ hJn hJm hD hDn hLD hDJ
  let : IsQuasisimple B := hquasi
  have hn : (S : Subgroup (X ⧸ pCore 2 X)) ≤ normalizer (B : Set _) := by
    have hTD : (T : Subgroup G) ≤ normalizer (D : Set G) :=
      (F.invariant 2).trans ((normal_subgroupOf_iff_le_normalizer hD.1).mp hDn)
    have hnX : (T : Subgroup G).subgroupOf X ≤ normalizer (D.subgroupOf X : Set X) := by
      rw [←subgroupOf_normalizer_eq hDX]
      exact comap_mono hTD
    exact (map_mono (f := q) hnX).trans ((D.subgroupOf X).le_normalizer_map q)
  obtain ⟨e⟩ := (five_point_join_quotient_model h earlier F J hJ.1 hLJ hJn hm).1
  let a := e.trans hJm.some
  have h7 : 7 ∣ Nat.card B := by
    have hmodel : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 3 2 :=
      (five_quotient_local_models h earlier F J D hJ hLJ hm hD hDJ.le).2.2.2.2.1
    obtain ⟨k,_,_,hk,⟨f⟩⟩ := hmodel
    have hc : Nat.card (A ⧸ pCore 2 A) = 168 := by
      rw [Nat.card_congr f.toEquiv,Matrix.PSL3.LinearThree.card_projective,hk]
      norm_num
    have hAB : A ≤ B := map_mono (comap_mono hLD.le)
    have hh := (card_quotient_dvd_card (pCore 2 A)).trans (card_dvd_of_le hAB)
    rw [hc] at hh
    exact (by decide : 7 ∣ 168).trans hh
  have hcore : pCore 2 B = ⊥ :=
    five_mathieu_plane_image_core_eq_bot h earlier F J D hJ hLJ hJn hJm hD hDn hLD hDJ
  have hXH : X ≤ F.H := sup_le hJ.1 (F.invariant 1)
  have hsqX : IsSQTK KnownSimple.IsKnownSimple X :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hXH)).mp
      ((h.source.simpleQTKE.twoLocal_sqtk (Gi_twoLocal h F 1 (by decide))).subgroup
        (X.subgroupOf F.H))
  have hsqQ := ChapterE.Structure.sqtk_two_quotient hsqX (pCore 2 X) pCore_isPGroup
  exact ChapterA.Section03.SourceEmbeddings.MathieuRank.eq_top_of_quasisimple_faithful_sylow
    a S B (hsqQ.subgroup B) hcore h7 hn hfaith



/-- The M₂₄ point row admits no strict plane enlargement. The image is
forced to be the whole quotient, contradicting the saved strict chain
through the original quotient map. -/
theorem five_plane_not_mathieu_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) (J D : Subgroup G)
    (hJ : J ∈ Chapter1.cComponentsIn F.H) (hLJ : F.Li L 1 ≤ J)
    (hJn : (J.subgroupOf F.H).Normal)
    (hJm : Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.Mathieu.M24))
    (hD : D ∈ Chapter1.cComponentsIn (F.Gi 2))
    (hDn : (D.subgroupOf (F.Gi 2)).Normal)
    (hLD : F.Li L 2 < D) (hDJ : D < J) : False := by
  have he := five_mathieu_plane_image_eq_top h earlier F J D hJ hLJ hJn hJm hD hDn hLD hDJ
  have hc := (five_quotient_overgroup_chain h earlier F J D hJ hLJ hJn hD hDn hLD hDJ).2.1
  have hh := map_mono (f := QuotientGroup.mk' (pCore 2 (J ⊔ (T : Subgroup G) : Subgroup G)))
    (comap_mono (f := (J ⊔ (T : Subgroup G) : Subgroup G).subtype)
      (show D ≤ D ⊔ (T : Subgroup G) from le_sup_left))
  change (D.subgroupOf (J ⊔ (T : Subgroup G))).map
    (QuotientGroup.mk' (pCore 2 (J ⊔ (T : Subgroup G) : Subgroup G))) ≤ _ at hh
  rw [he] at hh
  exact (not_le_of_gt hc) hh

/-- The original degree-five plane assertion is proved in the M₂₄ point
case, retaining the original flag and its relative normality. -/
theorem five_plane_component_of_mathieu_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) (J : Subgroup G)
    (hJ : J ∈ Chapter1.cComponentsIn F.H) (hLJ : F.Li L 1 ≤ J)
    (hJn : (J.subgroupOf F.H).Normal)
    (hJm : Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.Mathieu.M24)) :
    ((F.Li L 2).subgroupOf (F.Gi 2)).IsCComponent ∧
      ((F.Li L 2).subgroupOf (F.Gi 2)).Normal := by
  obtain ⟨D,hd,_⟩ := exists_unique_normal_local_component h earlier F 2
    (Or.inl ⟨rfl,by decide,by decide⟩)
  have he : D = F.Li L 2 := by
    by_contra hne
    exact five_plane_not_mathieu_point h earlier F J D hJ hLJ hJn hJm hd.1 hd.2.2
      (lt_of_le_of_ne hd.2.1 (Ne.symm hne))
      (five_plane_component_lt_point h earlier F D hd.1 hd.2.1 J hJ.1 hLJ hJn)
  exact he ▸ ⟨hd.1.2,hd.2.2⟩

/-- Every remaining plane failure has J₄ point quotient. The complete
Mathieu branch has been removed using the original literal quotients. -/
theorem exists_five_janko_plane_components
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5)
    (hfail : ¬ (((F.Li L 2).subgroupOf (F.Gi 2)).IsCComponent ∧
      ((F.Li L 2).subgroupOf (F.Gi 2)).Normal)) :
    ∃ J D : Subgroup G,
      J ∈ Chapter1.cComponentsIn F.H ∧ F.Li L 1 < J ∧
      (J.subgroupOf F.H).Normal ∧
      Nonempty ((J ⧸ pCore 2 J) ≃* Janko4.Model) ∧
      D ∈ Chapter1.cComponentsIn (F.Gi 2) ∧ F.Li L 2 < D ∧
      (D.subgroupOf (F.Gi 2)).Normal ∧ D < J ∧
      IsQuasisimple (D ⧸ pCore 2 D) := by
  obtain ⟨J,D,hJ,hLJ,hJn,hm,hD,hLD,hDn,hDJ,_⟩ :=
    exists_five_sporadic_plane_components h earlier F hfail
  have hj : Nonempty ((J ⧸ pCore 2 J) ≃* Janko4.Model) := by
    rcases hm with hm | hm
    · exact (five_plane_not_mathieu_point h earlier F J D hJ hLJ.le hJn hm hD hDn hLD hDJ).elim
    · exact hm
  exact ⟨J,D,hJ,hLJ,hJn,hj,hD,hLD,hDn,hDJ,
    five_sporadic_plane_component_quasisimple h F J D (Or.inr hj) hD hLD.le hDJ.le⟩

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
