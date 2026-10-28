module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.Binary
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.MathieuNestedQuotients
public import Theory.GroupTheory.PCoreImageRestriction
public import Theory.GroupTheory.PCoreInRestriction

/-!
# The nontrivial-core Mathieu plane comparison

In a strict plane enlargement L₂ < D < J with point quotient M₂₄,
pass through the original map JT → JT/O₂(JT). The saved quotient
construction preserves strictness, the full Sylow action and the original
PSL₃(2) quotient. If the image of D has nontrivial two-core, the native
Mathieu calculation forces its core quotient to be PSL₄(2). The original
plane action excludes that model.

Thus the plane image has trivial two-core, and the literal core-preimage
identity gives O₂(D) = D ∩ O₂(JT) in G. The final source application retains
the actual nested pair and reduces every remaining plane failure to this
Mathieu case or the J₄ point row. Excluding the trivial-core Mathieu case,
the J₄ comparison and the other component/abelianity branches still belongs
to qt-d-1291-natural-source; no complete ComponentInput is asserted here.

Source: Aschbacher--Smith, 12.9.3, printed pp.858--859 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Every strict plane enlargement in the M₂₄ point case has trivial
two-core in the literal JT/O₂(JT) quotient. -/
theorem five_mathieu_plane_image_core_eq_bot
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) (J D : Subgroup G)
    (hJ : J ∈ Chapter1.cComponentsIn F.H) (hLJ : F.Li L 1 ≤ J)
    (hJn : (J.subgroupOf F.H).Normal)
    (hJm : Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.Mathieu.M24))
    (hD : D ∈ Chapter1.cComponentsIn (F.Gi 2))
    (hDn : (D.subgroupOf (F.Gi 2)).Normal)
    (hLD : F.Li L 2 < D) (hDJ : D < J) :
    pCore 2 ((D.subgroupOf (J ⊔ (T : Subgroup G))).map
      (QuotientGroup.mk' (pCore 2 (J ⊔ (T : Subgroup G) : Subgroup G)))) = ⊥ := by
  let X := J ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 X)
  let image := fun A : Subgroup G => (A.subgroupOf X).map q
  let S := (T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)).mapSurjective
    (QuotientGroup.mk'_surjective (pCore 2 X))
  change pCore 2 (image D) = ⊥
  have hDX : D ≤ X := hDJ.le.trans le_sup_left
  have hm : LargePointModel (J ⧸ pCore 2 J) := Or.inr (Or.inl hJm)
  obtain ⟨hl1,hl2,hd,hm1,hm2,hm1T,hjm⟩ :=
    five_quotient_local_models h earlier F J D hJ hLJ hm hD hDJ.le
  have hchain := five_quotient_overgroup_chain h earlier F J D hJ hLJ hJn hD hDn hLD hDJ
  have hn : (S : Subgroup (X ⧸ pCore 2 X)) ≤ normalizer (image D : Set (X ⧸ pCore 2 X)) := by
    have hTD : (T : Subgroup G) ≤ normalizer (D : Set G) :=
      (F.invariant 2).trans ((normal_subgroupOf_iff_le_normalizer hD.1).mp hDn)
    have hnX : (T : Subgroup G).subgroupOf X ≤ normalizer (D.subgroupOf X : Set X) := by
      rw [←subgroupOf_normalizer_eq hDX]
      exact comap_mono hTD
    exact (map_mono (f := q) hnX).trans ((D.subgroupOf X).le_normalizer_map q)
  obtain ⟨e⟩ := (five_point_join_quotient_model h earlier F J hJ.1 hLJ hJn hm).1
  by_contra hc
  have hdmodel := ChapterA.Section03.SourceEmbeddings.MathieuNested.strict_three_models_of_core_ne_bot
    (e.trans hJm.some) S hl2 hd hchain.2.2.2.1 hn hc hm2
  have hk : IsPGroup 2 (q.subgroupMap (D.subgroupOf X)).ker := by
    rw [ker_subgroupMap]
    have hq : IsPGroup 2 q.ker := by
      rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
    exact hq.comap_subtype
  let d := subgroupOfEquivOfLe hDX
  let a := (QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).symm.trans
    ((q.subgroupMap (D.subgroupOf X)).pCoreQuotientEquiv
      (q.subgroupMap_surjective _) hk)
  exact plane_component_not_linear h F D hD hDn (Or.inl rfl) (hdmodel.of_mulEquiv a)

/-- The remaining M₂₄ plane obstruction has no new intrinsic two-core:
O₂(D) is exactly D∩O₂(JT), with both subgroups embedded in the original G. -/
theorem five_mathieu_plane_core_eq_intersection
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) (J D : Subgroup G)
    (hJ : J ∈ Chapter1.cComponentsIn F.H) (hLJ : F.Li L 1 ≤ J)
    (hJn : (J.subgroupOf F.H).Normal)
    (hJm : Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.Mathieu.M24))
    (hD : D ∈ Chapter1.cComponentsIn (F.Gi 2))
    (hDn : (D.subgroupOf (F.Gi 2)).Normal)
    (hLD : F.Li L 2 < D) (hDJ : D < J) :
    D.pCoreIn 2 = D ⊓ (J ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2 := by
  let X := J ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 X)
  have hDX : D ≤ X := hDJ.le.trans le_sup_left
  have hcore := five_mathieu_plane_image_core_eq_bot h earlier F J D hJ hLJ hJn hJm hD hDn hLD hDJ
  have hbot : ((D.subgroupOf X).map q).pCoreIn 2 = ⊥ := by
    rw [pCoreIn,hcore,Subgroup.map_bot]
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have he := inf_comap_pCoreIn_eq_of_ker_isPGroup 2 q (D.subgroupOf X) hk
  rw [hbot] at he
  change D.subgroupOf X ⊓ q.ker = (D.subgroupOf X).pCoreIn 2 at he
  rw [QuotientGroup.ker_mk',pCoreIn_subgroupOf 2 D X hDX] at he
  apply le_antisymm
  · intro x hx
    have hxX : x ∈ X := hDX ((D.pCoreIn_le 2) hx)
    have hm : (⟨x,hxX⟩ : X) ∈ D.subgroupOf X ⊓ pCore 2 X := he.symm ▸ hx
    exact ⟨hm.1,mem_map_of_mem X.subtype hm.2⟩
  · rintro x ⟨hxD,y,hy,rfl⟩
    change y ∈ (D.pCoreIn 2).subgroupOf X
    rw [←he]
    exact ⟨hxD,hy⟩

/-- Apply the native M₂₄ comparison to every remaining degree-five plane
failure. The original nested pair is retained. Its point quotient is J₄,
or it is M₂₄ and the literal plane image has trivial two-core. -/
theorem exists_five_plane_components_mathieu_core_or_janko
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5)
    (hfail : ¬ (((F.Li L 2).subgroupOf (F.Gi 2)).IsCComponent ∧
      ((F.Li L 2).subgroupOf (F.Gi 2)).Normal)) :
    ∃ J D : Subgroup G,
      J ∈ Chapter1.cComponentsIn F.H ∧ F.Li L 1 < J ∧
      (J.subgroupOf F.H).Normal ∧
      D ∈ Chapter1.cComponentsIn (F.Gi 2) ∧ F.Li L 2 < D ∧
      (D.subgroupOf (F.Gi 2)).Normal ∧ D < J ∧
      (Nonempty ((J ⧸ pCore 2 J) ≃* Janko4.Model) ∨
        Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.Mathieu.M24) ∧
        pCore 2 ((D.subgroupOf (J ⊔ (T : Subgroup G))).map
          (QuotientGroup.mk' (pCore 2 (J ⊔ (T : Subgroup G) : Subgroup G)))) = ⊥ ∧
        D.pCoreIn 2 = D ⊓ (J ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2) := by
  obtain ⟨J,D,hJ,hLJ,hJn,hm,hD,hLD,hDn,hDJ,_⟩ :=
    exists_five_sporadic_plane_components h earlier F hfail
  refine ⟨J,D,hJ,hLJ,hJn,hD,hLD,hDn,hDJ,?_⟩
  rcases hm with hm | hm
  · exact Or.inr ⟨hm,
      five_mathieu_plane_image_core_eq_bot h earlier F J D hJ hLJ.le hJn hm hD hDn hLD hDJ,
      five_mathieu_plane_core_eq_intersection h earlier F J D hJ hLJ.le hJn hm hD hDn hLD hDJ⟩
  · exact Or.inl hm

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
