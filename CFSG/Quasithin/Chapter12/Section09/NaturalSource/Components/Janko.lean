module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.MathieuComplete
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoRank
public import CFSG.Quasithin.MainConverse.SporadicLocal.J4.SylowCenterEven

/-!
# The trivial-core J₄ plane branch of source 12.9.3

Suppose the original strict plane image in JT/O₂(JT) had trivial two-core.
Its already proved quasisimple core quotient would make the image itself
quasisimple. Even characteristic of the actual J₄ carrier makes the full
quotient Sylow action faithful. The source PSL₃(2) section supplies seven,
and SQTK descends through the literal subgroup and quotient maps.
The complete rank-and-order comparison then makes the image the whole
quotient, contradicting the original strict Sylow-overgroup chain.

Thus every remaining source plane failure has J₄ point quotient and a
plane image with nontrivial two-core. Its characteristic-core normalizer
is a genuine two-local containing both that image and the original full
quotient Sylow. The remaining marked nontrivial-core comparison, all other
component and abelianity cases, and local-control premises stay with
qt-d-1291-natural-source; this module does not assert ComponentInput.

Source: Aschbacher--Smith 12.9.3, printed pp.858--859 of refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Subgroup Theory.GroupTheory
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Every remaining J₄ plane enlargement has nontrivial intrinsic two-core
in its literal image in JT/O₂(JT). -/
theorem five_janko_plane_image_core_ne_bot
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) (J D : Subgroup G)
    (hJ : J ∈ Chapter1.cComponentsIn F.H) (hLJ : F.Li L 1 ≤ J)
    (hJn : (J.subgroupOf F.H).Normal)
    (hJm : Nonempty ((J ⧸ pCore 2 J) ≃* Janko4.Model))
    (hD : D ∈ Chapter1.cComponentsIn (F.Gi 2))
    (hDn : (D.subgroupOf (F.Gi 2)).Normal)
    (hLD : F.Li L 2 < D) (hDJ : D < J) :
    pCore 2 ((D.subgroupOf (J ⊔ (T : Subgroup G))).map
      (QuotientGroup.mk' (pCore 2 (J ⊔ (T : Subgroup G) : Subgroup G)))) ≠ ⊥ := by
  let X := J ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 X)
  let B := (D.subgroupOf X).map q
  let A := ((F.Li L 2).subgroupOf X).map q
  let S := (T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)).mapSurjective
    (QuotientGroup.mk'_surjective (pCore 2 X))
  change pCore 2 B ≠ ⊥
  intro hcore
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
    (((q.subgroupMap (D.subgroupOf X)).pCoreQuotientEquiv
      (q.subgroupMap_surjective _) hk).trans
      ((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot))
  let hquasi : IsQuasisimple B :=
    (five_sporadic_plane_component_quasisimple h F J D (Or.inr hJm) hD hLD.le hDJ.le).of_mulEquiv a
  obtain ⟨e⟩ := (five_point_join_quotient_model h earlier F J hJ.1 hLJ hJn hm).1
  let eJ := e.trans hJm.some
  have hfaith := ChapterA.Section03.SourceEmbeddings.sylow_centralizer_eq_bot_of_evenCharacteristic
    S (MainConverse.SporadicLocal.J4SylowCenterEven.evenCharacteristic_of_equiv eJ S)
    hmodels.2.2.1 hn
  have h7 : 7 ∣ Nat.card B := by
    obtain ⟨k,_,_,hk,⟨f⟩⟩ := hmodels.2.2.2.2.1
    have hc : Nat.card (A ⧸ pCore 2 A) = 168 := by
      rw [Nat.card_congr f.toEquiv,Matrix.PSL3.LinearThree.card_projective,hk]
      norm_num
    have hAB : A ≤ B := map_mono (comap_mono hLD.le)
    have hh := (card_quotient_dvd_card (pCore 2 A)).trans (card_dvd_of_le hAB)
    rw [hc] at hh
    exact (by decide : 7 ∣ 168).trans hh
  have hXH : X ≤ F.H := sup_le hJ.1 (F.invariant 1)
  have hsqX : IsSQTK KnownSimple.IsKnownSimple X :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hXH)).mp
      ((h.source.simpleQTKE.twoLocal_sqtk (Gi_twoLocal h F 1 (by decide))).subgroup
        (X.subgroupOf F.H))
  have hsqQ := ChapterE.Structure.sqtk_two_quotient hsqX (pCore 2 X) pCore_isPGroup
  have he := ChapterA.Section03.SourceEmbeddings.JankoRank.eq_top_of_quasisimple_faithful_sylow
    eJ S B (hsqQ.subgroup B) hcore h7 hn hfaith
  have hc := (five_quotient_overgroup_chain h earlier F J D hJ hLJ hJn hD hDn hLD hDJ).2.1
  have hh := map_mono (f := q)
    (comap_mono (f := X.subtype)
      (show D ≤ D ⊔ (T : Subgroup G) from le_sup_left))
  change B ≤ _ at hh
  rw [he] at hh
  exact (not_le_of_gt hc) hh

/-- The characteristic core supplies a genuine two-local containing the
original plane image and the full quotient Sylow. No placement callback is used. -/
theorem five_janko_plane_image_twoLocal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) (J D : Subgroup G)
    (hJ : J ∈ Chapter1.cComponentsIn F.H) (hLJ : F.Li L 1 ≤ J)
    (hJn : (J.subgroupOf F.H).Normal)
    (hJm : Nonempty ((J ⧸ pCore 2 J) ≃* Janko4.Model))
    (hD : D ∈ Chapter1.cComponentsIn (F.Gi 2))
    (hDn : (D.subgroupOf (F.Gi 2)).Normal)
    (hLD : F.Li L 2 < D) (hDJ : D < J) :
    let X := J ⊔ (T : Subgroup G)
    let q := QuotientGroup.mk' (pCore 2 X)
    let B := (D.subgroupOf X).map q
    let S := (T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)).mapSurjective
      (QuotientGroup.mk'_surjective (pCore 2 X))
    ∃ N : Subgroup (X ⧸ pCore 2 X), IsTwoLocal N ∧ B ≤ N ∧ (S : Subgroup _) ≤ N := by
  let X := J ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 X)
  let B := (D.subgroupOf X).map q
  let S := (T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)).mapSurjective
    (QuotientGroup.mk'_surjective (pCore 2 X))
  let U := (pCore 2 B).map B.subtype
  have hU : U ≠ ⊥ := fun he =>
    five_janko_plane_image_core_ne_bot h earlier F J D hJ hLJ hJn hJm hD hDn hLD hDJ
      ((map_eq_bot_iff_of_injective _ B.subtype_injective).mp he)
  have hn : (S : Subgroup (X ⧸ pCore 2 X)) ≤ normalizer (B : Set _) := by
    have hDX : D ≤ X := hDJ.le.trans le_sup_left
    have hTD : (T : Subgroup G) ≤ normalizer (D : Set G) :=
      (F.invariant 2).trans ((normal_subgroupOf_iff_le_normalizer hD.1).mp hDn)
    have hnX : (T : Subgroup G).subgroupOf X ≤ normalizer (D.subgroupOf X : Set X) := by
      rw [←subgroupOf_normalizer_eq hDX]
      exact comap_mono hTD
    exact (map_mono (f := q) hnX).trans ((D.subgroupOf X).le_normalizer_map q)
  have hnU := normalizer_le_normalizer_characteristic_image B (pCore 2 B)
  exact ⟨normalizer (U : Set _), ⟨U,hU,pCore_isPGroup.map B.subtype,rfl⟩,
    B.le_normalizer.trans hnU, hn.trans hnU⟩

/-- Every remaining degree-five plane failure supplies a nontrivial-core
J₄ plane image. This applies the full catalogue calculation to the actual
source flag, preserving both containing components and their relative normality. -/
theorem exists_five_janko_plane_components_core_ne_bot
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
      IsQuasisimple (D ⧸ pCore 2 D) ∧
      pCore 2 ((D.subgroupOf (J ⊔ (T : Subgroup G))).map
        (QuotientGroup.mk' (pCore 2 (J ⊔ (T : Subgroup G) : Subgroup G)))) ≠ ⊥ := by
  obtain ⟨J,D,hJ,hLJ,hJn,hm,hD,hLD,hDn,hDJ,hq⟩ :=
    exists_five_janko_plane_components h earlier F hfail
  exact ⟨J,D,hJ,hLJ,hJn,hm,hD,hLD,hDn,hDJ,hq,
    five_janko_plane_image_core_ne_bot h earlier F J D hJ hLJ.le hJn hm hD hDn hLD hDJ⟩

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
