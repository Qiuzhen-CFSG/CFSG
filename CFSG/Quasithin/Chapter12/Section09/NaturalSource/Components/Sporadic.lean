module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.Mathieu
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SporadicNestedQuotients
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.EvenCharacteristic
public import CFSG.Quasithin.MainConverse.MathieuLocal.M24Even
public import CFSG.Quasithin.MainConverse.Transport
public import Theory.SpecificGroups.Janko4.Model.Cardinality

/-!
# Ordinary plane sections in the remaining sporadic point cases

The original PSL₃(2) plane section forces a factor seven in D/O₂(D).
The literal inclusion D≤J makes its order divide |J/O₂(J)|. Thus the
proved A.3.6 order obstruction excludes every nonquasisimple plane
quotient in the M₂₄ and J₄ point cases. Combined with the existing normal
and binary branches, every source degree-five plane component now has
quasisimple two-core quotient.

In the M₂₄ case the previously proved trivial two-core of the plane image
in JT/O₂(JT) makes that image itself quasisimple. The native M₂₄ even-
characteristic theorem then makes its original quotient-Sylow action
faithful. Relative normality and all original quotient maps are retained.
The proper quasisimple overgroup comparisons and the other source stages
remain with qt-d-1291-natural-source; this is not ComponentInput.

Source: Aschbacher--Smith 12.9.3, printed pp.858--859 of refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Subgroup Theory.GroupTheory
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem quotient_card_dvd {X : Type*} [Group X] [Finite X]
    (A : Subgroup X) : Nat.card (A ⧸ pCore 2 A) ∣ Nat.card (X ⧸ pCore 2 X) := by
  let q := QuotientGroup.mk' (pCore 2 X)
  have hk : IsPGroup 2 (q.subgroupMap A).ker := by
    rw [ker_subgroupMap]
    have hq : IsPGroup 2 q.ker := by
      rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
    exact hq.comap_subtype
  let e := (q.subgroupMap A).pCoreQuotientEquiv (q.subgroupMap_surjective A) hk
  rw [Nat.card_congr e.toEquiv]
  exact (card_quotient_dvd_card _).trans (A.map q).card_subgroup_dvd_card

private theorem quotient_card_dvd_of_le {A B : Subgroup G} (hAB : A ≤ B) :
    Nat.card (A ⧸ pCore 2 A) ∣ Nat.card (B ⧸ pCore 2 B) := by
  let e := subgroupOfEquivOfLe hAB
  have hd := quotient_card_dvd (A.subgroupOf B)
  rwa [Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv] at hd

/-- In either remaining sporadic point model, the original plane component
has quasisimple two-core quotient. This rules out both nonquasisimple A.3.6
alternatives while preserving D, J and their literal quotients. -/
theorem five_sporadic_plane_component_quasisimple
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (F : InvariantFlag T V 5) (J D : Subgroup G)
    (hJm : Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.Mathieu.M24) ∨
      Nonempty ((J ⧸ pCore 2 J) ≃* Janko4.Model))
    (hD : D ∈ Chapter1.cComponentsIn (F.Gi 2))
    (hLD : F.Li L 2 ≤ D) (hDJ : D ≤ J) :
    IsQuasisimple (D ⧸ pCore 2 D) := by
  have h7L : 7 ∣ Nat.card (F.Li L 2 ⧸ pCore 2 (F.Li L 2)) := by
    let := h.chosen.elementary
    obtain ⟨d,hd,_,⟨e⟩⟩ := Li_core_linear F h.naturalMarking 2
      (Or.inl ⟨rfl,by decide,by decide⟩)
    have he : d = 3 := by norm_num at hd; exact hd
    subst d
    rw [Nat.card_congr (e.trans (BinaryLinear.OuterCyclic.slEquivLinear 3).symm).toEquiv,
      Matrix.PSL3Two.card_SL]
    decide
  have h7D := h7L.trans (quotient_card_dvd_of_le hLD)
  have hd : Nat.card (D ⧸ pCore 2 D) ∣ 244823040 ∨
      Nat.card (D ⧸ pCore 2 D) ∣ 86775571046077562880 := by
    have hd := quotient_card_dvd_of_le hDJ
    rcases hJm with hm | hm
    · rw [Nat.card_congr hm.some.toEquiv,Sporadic.Mathieu.m24_order] at hd
      exact Or.inl hd
    · rw [Nat.card_congr hm.some.toEquiv,Janko4.Cardinality.model_card] at hd
      exact Or.inr hd
  let e := subgroupOfEquivOfLe hD.1
  let a := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  have hcard := Nat.card_congr a.toEquiv
  exact (ChapterA.Section03.SourceEmbeddings.SporadicNested.twoCore_quotient_quasisimple_of_sporadic_order
    (h.source.simpleQTKE.twoLocal_sqtk (Gi_twoLocal h F 2 (by decide))) hD.2
    (hcard.symm ▸ h7D) (hcard.symm ▸ hd)).of_mulEquiv a

/-- Every degree-five plane component has quasisimple two-core quotient:
the unchanged and binary cases are already controlled, and the two actual
sporadic orders exclude the exceptional nonquasisimple alternatives. -/
theorem five_plane_component_quasisimple
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) (D : Subgroup G)
    (hD : D ∈ Chapter1.cComponentsIn (F.Gi 2))
    (hLD : F.Li L 2 ≤ D) (hDn : (D.subgroupOf (F.Gi 2)).Normal) :
    IsQuasisimple (D ⧸ pCore 2 D) := by
  by_cases he : D = F.Li L 2
  · let := h.chosen.elementary
    exact he ▸ Li_core_quasisimple F h.naturalMarking 2
      (Or.inl ⟨rfl,by decide,by decide⟩)
  have hlt : F.Li L 2 < D := lt_of_le_of_ne hLD (Ne.symm he)
  obtain ⟨J,hJ,hLJ,hJn,hm⟩ := exists_five_point_component h earlier F
  have hDJ := five_plane_component_lt_point h earlier F D hD hLD J hJ.1 hLJ hJn
  rcases hm with hsame | hm | hm
  · have hplane := five_plane_component_of_point_normal h earlier F (hsame ▸ hJn)
    have heq := exists_unique_normal_local_component h earlier F 2
      (Or.inl ⟨rfl,by decide,by decide⟩)
    have hh : D = F.Li L 2 := heq.unique ⟨hD,hLD,hDn⟩
      ⟨⟨(F.Li_le L 2).trans inf_le_right,hplane.1⟩,le_rfl,hplane.2⟩
    exact (he hh).elim
  · exact (five_plane_not_binary_point h earlier F J D hJ hm hD hDn hlt hDJ.le).elim
  · exact five_sporadic_plane_component_quasisimple h F J D hm hD hLD hDJ.le

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components

namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Subgroup Theory.GroupTheory
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- In the surviving M₂₄ case the literal plane image is an ordinary
quasisimple group, and the original quotient Sylow acts faithfully on it. -/
theorem five_mathieu_plane_image_quasisimple_faithful
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
    let q := QuotientGroup.mk' (pCore 2 X)
    let B := (D.subgroupOf X).map q
    let S := (T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)).mapSurjective
      (QuotientGroup.mk'_surjective (pCore 2 X))
    IsQuasisimple B ∧ (S : Subgroup (X ⧸ pCore 2 X)) ⊓
      centralizer (B : Set (X ⧸ pCore 2 X)) = ⊥ := by
  let X := J ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 X)
  let B := (D.subgroupOf X).map q
  let S := (T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)).mapSurjective
    (QuotientGroup.mk'_surjective (pCore 2 X))
  change IsQuasisimple B ∧ (S : Subgroup (X ⧸ pCore 2 X)) ⊓ centralizer (B : Set _) = ⊥
  have hDX : D ≤ X := hDJ.le.trans le_sup_left
  have hm : LargePointModel (J ⧸ pCore 2 J) := Or.inr (Or.inl hJm)
  have hl := (five_quotient_local_models h earlier F J D hJ hLJ hm hD hDJ.le).2.2.1
  have hn : (S : Subgroup (X ⧸ pCore 2 X)) ≤ normalizer (B : Set _) := by
    have hTD : (T : Subgroup G) ≤ normalizer (D : Set G) :=
      (F.invariant 2).trans ((normal_subgroupOf_iff_le_normalizer hD.1).mp hDn)
    have hnX : (T : Subgroup G).subgroupOf X ≤ normalizer (D.subgroupOf X : Set X) := by
      rw [←subgroupOf_normalizer_eq hDX]
      exact comap_mono hTD
    exact (map_mono (f := q) hnX).trans ((D.subgroupOf X).le_normalizer_map q)
  have hcore : pCore 2 B = ⊥ :=
    five_mathieu_plane_image_core_eq_bot h earlier F J D hJ hLJ hJn hJm hD hDn hLD hDJ
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
    (five_sporadic_plane_component_quasisimple h F J D (Or.inl hJm) hD hLD.le hDJ.le).of_mulEquiv a
  obtain ⟨e⟩ := (five_point_join_quotient_model h earlier F J hJ.1 hLJ hJn hm).1
  have hE := MainConverse.evenCharacteristic_of_model_equiv (e.trans hJm.some)
    MainConverse.m24_evenCharacteristic
  exact ⟨hquasi,ChapterA.Section03.SourceEmbeddings.sylow_centralizer_eq_bot_of_evenCharacteristic
    S (hE S) hl hn⟩

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
