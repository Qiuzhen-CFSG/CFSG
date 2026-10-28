module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.PointAction
public import Theory.GroupTheory.PResidual.NormalizedComparison

/-!
# The literal Sylow-overgroup obstruction in the degree-five plane case

A failure of the source plane-component assertion yields L₂ < D < J. Recovery
of the original two-residuals gives L₂T < DT < JT and DT ≠ L₁T. Quotienting
by O₂(JT) preserves these comparisons, local-component membership, the
PSL₃(2) and PSL₄(2) quotients, and the failure of D to normalize L₂.

The final theorem constructs all these data from the original natural-module
hypotheses, including the exclusions of the three possible terminal plane
models. The remaining finite-model Sylow-overgroup comparison and the full
source assembly belong to qt-d-1291-natural-source.

Source: Aschbacher--Smith, 12.9.3, printed pp.858--859 of refs/quasithin.pdf.
-/

public noncomputable section
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G}

private theorem component_twoPerfect {D H : Subgroup G}
    (hD : D ∈ Chapter1.cComponentsIn H) : IsPPerfect 2 D := by
  let := hD.2.perfect
  let e := subgroupOfEquivOfLe hD.1
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  intro R hn hp
  let := hn
  by_contra hne
  let : Nontrivial (D ⧸ R) := QuotientGroup.nontrivial_iff.mpr hne
  exact Group.IsPerfect.not_isNilpotent _ hp.isNilpotent

/-- A proper plane overcomponent cannot normalize the original nonsolvable residual L₂. -/
theorem five_plane_residual_not_normalized_by_component
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5)
    (D : Subgroup G) (hD : D ∈ Chapter1.cComponentsIn (F.Gi 2))
    (hLD : F.Li L 2 < D) : ¬ D ≤ normalizer (F.Li L 2 : Set G) := by
  intro hn
  let B := (F.Li L 2).subgroupOf D
  let : B.Normal := (normal_subgroupOf_iff_le_normalizer hLD.le).mpr hn
  have htop : (⊤ : Subgroup D).IsCComponent := by
    let e := subgroupOfEquivOfLe hD.1
    have hc : (⊤ : Subgroup (D.subgroupOf (F.Gi 2))).IsCComponent := by
      simpa only [subgroupOf_self] using hD.2.subgroupOf le_rfl
    simpa only [map_top_of_surjective e.toMonoidHom e.surjective] using hc.map_equiv e
  have hB : ¬ Group.IsSolvable B := by
    intro hs
    let := hs
    let e := subgroupOfEquivOfLe hLD.le
    let : Group.IsSolvable (F.Li L 2) := Group.isSolvable_of_surjective
      (f := e.toMonoidHom) e.surjective
    have hl := (Li_mem_local h earlier F 2 (Or.inl ⟨rfl,by decide,by decide⟩)).1
    let eL := subgroupOfEquivOfLe (show F.Li L 2 ≤ F.Li L 2 ⊔ (T : Subgroup G) from le_sup_left)
    exact hl.not_isSolvable (Group.isSolvable_of_isSolvable_injective
      (f := eL.toMonoidHom) eL.injective)
  have ht := htop.le_normal_of_nonsolvable_subgroup hB le_top le_rfl
  exact hLD.not_ge (subgroupOf_eq_top.mp (top_unique ht))

/-- The literal strict Sylow-overgroup chain used in 12.9.3, including separation from L₁T. -/
theorem five_strict_sylow_overgroups
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5)
    (J D : Subgroup G)
    (hJ : J ∈ Chapter1.cComponentsIn F.H)
    (hJn : (J.subgroupOf F.H).Normal)
    (hD : D ∈ Chapter1.cComponentsIn (F.Gi 2))
    (hDn : (D.subgroupOf (F.Gi 2)).Normal)
    (hLD : F.Li L 2 < D) (hDJ : D < J) :
    F.Li L 2 ⊔ (T : Subgroup G) < D ⊔ (T : Subgroup G) ∧
      D ⊔ (T : Subgroup G) < J ⊔ (T : Subgroup G) ∧
      D ⊔ (T : Subgroup G) ≠ F.Li L 1 ⊔ (T : Subgroup G) := by
  have hTJ := (F.invariant 1).trans ((normal_subgroupOf_iff_le_normalizer hJ.1).mp hJn)
  have hTD := (F.invariant 2).trans ((normal_subgroupOf_iff_le_normalizer hD.1).mp hDn)
  have hpD := component_twoPerfect hD
  have hpJ := component_twoPerfect hJ
  refine ⟨(sup_lt_sup_iff_of_twoPerfect _ _ _ (Li_twoPerfect F 2) hpD T.isPGroup'
      (sylow_normalizes_Li h earlier F 2) hTD).mpr hLD,
    (sup_lt_sup_iff_of_twoPerfect _ _ _ hpD hpJ T.isPGroup' hTD hTJ).mpr hDJ, ?_⟩
  intro he
  have he' : D = F.Li L 1 := le_antisymm
    ((sup_le_sup_iff_of_twoPerfect _ _ _ hpD (Li_twoPerfect F 1) T.isPGroup' hTD
      (sylow_normalizes_Li h earlier F 1)).mp he.le)
    ((sup_le_sup_iff_of_twoPerfect _ _ _ (Li_twoPerfect F 1) hpD T.isPGroup'
      (sylow_normalizes_Li h earlier F 1) hTD).mp he.ge)
  exact point_residual_not_le_plane_normalizer h F (he' ▸ hD.1)


/-- In the exact source quotient, strictness and the failure of normalization
survive the ambient two-core. All maps retain the original Sylow subgroup. -/
theorem five_quotient_overgroup_chain
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5)
    (J D : Subgroup G)
    (hJ : J ∈ Chapter1.cComponentsIn F.H)
    (hLJ : F.Li L 1 ≤ J) (hJn : (J.subgroupOf F.H).Normal)
    (hD : D ∈ Chapter1.cComponentsIn (F.Gi 2))
    (hDn : (D.subgroupOf (F.Gi 2)).Normal)
    (hLD : F.Li L 2 < D) (hDJ : D < J) :
    let X := J ⊔ (T : Subgroup G)
    let q := QuotientGroup.mk' (pCore 2 X)
    let image := fun A : Subgroup G => (A.subgroupOf X).map q
    image (F.Li L 2 ⊔ (T : Subgroup G)) < image (D ⊔ (T : Subgroup G)) ∧
      image (D ⊔ (T : Subgroup G)) < ⊤ ∧
      image (D ⊔ (T : Subgroup G)) ≠ image (F.Li L 1 ⊔ (T : Subgroup G)) ∧
      image (F.Li L 2) < image D ∧
      ¬ image D ≤ normalizer (image (F.Li L 2) : Set (X ⧸ pCore 2 X)) := by
  let X := J ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 X)
  let image := fun A : Subgroup G => (A.subgroupOf X).map q
  change image (F.Li L 2 ⊔ (T : Subgroup G)) < image (D ⊔ (T : Subgroup G)) ∧
    image (D ⊔ (T : Subgroup G)) < ⊤ ∧
    image (D ⊔ (T : Subgroup G)) ≠ image (F.Li L 1 ⊔ (T : Subgroup G)) ∧
    image (F.Li L 2) < image D ∧
    ¬ image D ≤ normalizer (image (F.Li L 2) : Set (X ⧸ pCore 2 X))
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  have hDX : D ≤ X := hDJ.le.trans le_sup_left
  have hB2X : F.Li L 2 ≤ X := hLD.le.trans hDX
  have hB1X : F.Li L 1 ≤ X := hLJ.trans le_sup_left
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hkT : q.ker ≤ (T : Subgroup G).subgroupOf X := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal (T.subtype hTX)
  have compare (A B : Subgroup G) (hAX : A ≤ X) (hBX : B ≤ X)
      (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B) :
      image A ≤ image B ↔ A ≤ B := by
    constructor
    · intro hab
      have hc := comap_mono (f := q) hab
      dsimp only [image] at hc
      rw [comap_map_eq_self (H := A.subgroupOf X) (hkT.trans (comap_mono hTA)),
        comap_map_eq_self (H := B.subgroupOf X) (hkT.trans (comap_mono hTB))] at hc
      have hm := map_mono (f := X.subtype) hc
      rwa [map_subgroupOf_eq_of_le hAX,map_subgroupOf_eq_of_le hBX] at hm
    · exact fun hab => map_mono (comap_mono hab)
  have compareLt (A B : Subgroup G) (hAX : A ≤ X) (hBX : B ≤ X)
      (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B) :
      image A < image B ↔ A < B := by
    simp only [lt_iff_le_not_ge,compare A B hAX hBX hTA hTB,
      compare B A hBX hAX hTB hTA]
  have hDTX : D ⊔ (T : Subgroup G) ≤ X := sup_le hDX hTX
  have hB2TX : F.Li L 2 ⊔ (T : Subgroup G) ≤ X := sup_le hB2X hTX
  have hB1TX : F.Li L 1 ⊔ (T : Subgroup G) ≤ X := sup_le hB1X hTX
  obtain ⟨hsmall,hlarge,hne⟩ := five_strict_sylow_overgroups h earlier F J D hJ hJn hD hDn hLD hDJ
  have htop : image X = ⊤ := by
    dsimp only [image]
    rw [subgroupOf_self,map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  refine ⟨(compareLt _ _ hB2TX hDTX le_sup_right le_sup_right).mpr hsmall,
    htop ▸ (compareLt _ _ hDTX le_rfl le_sup_right hTX).mpr hlarge, ?_, ?_, ?_⟩
  · intro he
    exact hne (le_antisymm
      ((compare _ _ hDTX hB1TX le_sup_right le_sup_right).mp he.le)
      ((compare _ _ hB1TX hDTX le_sup_right le_sup_right).mp he.ge))
  · have hpB : IsPPerfect 2 ((F.Li L 2).subgroupOf X) :=
      (Li_twoPerfect F 2).of_surjective (subgroupOfEquivOfLe hB2X).symm.toMonoidHom
        (subgroupOfEquivOfLe hB2X).symm.surjective
    have hpD : IsPPerfect 2 (D.subgroupOf X) :=
      (component_twoPerfect hD).of_surjective (subgroupOfEquivOfLe hDX).symm.toMonoidHom
        (subgroupOfEquivOfLe hDX).symm.surjective
    have hnB : q.ker ≤ normalizer ((F.Li L 2).subgroupOf X : Set X) := by
      rw [← subgroupOf_normalizer_eq hB2X]
      exact hkT.trans (comap_mono (sylow_normalizes_Li h earlier F 2))
    have hnD : q.ker ≤ normalizer (D.subgroupOf X : Set X) := by
      rw [← subgroupOf_normalizer_eq hDX]
      exact hkT.trans (comap_mono ((F.invariant 2).trans
        ((normal_subgroupOf_iff_le_normalizer hD.1).mp hDn)))
    apply (map_lt_map_iff_of_pPerfect q _ _ hpB hpD hk hnB hnD).mpr
    apply (map_lt_map_iff_of_injective X.subtype_injective).mp
    rwa [map_subgroupOf_eq_of_le hB2X,map_subgroupOf_eq_of_le hDX]
  · intro hn
    have hpB : IsPPerfect 2 ((F.Li L 2).subgroupOf X) :=
      (Li_twoPerfect F 2).of_surjective (subgroupOfEquivOfLe hB2X).symm.toMonoidHom
        (subgroupOfEquivOfLe hB2X).symm.surjective
    have hnB : q.ker ≤ normalizer ((F.Li L 2).subgroupOf X : Set X) := by
      rw [← subgroupOf_normalizer_eq hB2X]
      exact hkT.trans (comap_mono (sylow_normalizes_Li h earlier F 2))
    have hn' := (map_le_normalizer_map_iff_of_pPerfect q _ _ hpB hk hnB).mp hn
    rw [← subgroupOf_normalizer_eq hB2X] at hn'
    apply five_plane_residual_not_normalized_by_component h earlier F D hD hLD
    intro d hd
    exact hn' (show (⟨d,hDX hd⟩ : X) ∈ D.subgroupOf X from hd)


/-- The intrinsic two-core quotient of a subgroup is preserved by the
literal quotient of a containing group by its two-core. -/
private noncomputable def imageCoreEquiv (X A : Subgroup G) (hAX : A ≤ X) :
    (A ⧸ pCore 2 A) ≃*
      (((A.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))) ⧸
        pCore 2 ((A.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X)))) := by
  let q := QuotientGroup.mk' (pCore 2 X)
  let e := subgroupOfEquivOfLe hAX
  have hk : IsPGroup 2 (q.subgroupMap (A.subgroupOf X)).ker := by
    rw [ker_subgroupMap]
    have hq : IsPGroup 2 q.ker := by
      rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
    exact hq.comap_subtype
  exact (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm.trans
    ((q.subgroupMap (A.subgroupOf X)).pCoreQuotientEquiv
      (q.subgroupMap_surjective _) hk)

/-- The model and local-component data in the source quotient are derived
from the actual original subgroups, with its full Sylow and no new marking. -/
theorem five_quotient_local_models
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5)
    (J D : Subgroup G)
    (hJ : J ∈ Chapter1.cComponentsIn F.H)
    (hLJ : F.Li L 1 ≤ J) (hJmodel : LargePointModel (J ⧸ pCore 2 J))
    (hD : D ∈ Chapter1.cComponentsIn (F.Gi 2))
    (hDJ : D ≤ J) :
    let X := J ⊔ (T : Subgroup G)
    let q := QuotientGroup.mk' (pCore 2 X)
    let image := fun A : Subgroup G => (A.subgroupOf X).map q
    let S := (T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)).mapSurjective
      (QuotientGroup.mk'_surjective (pCore 2 X))
    image (F.Li L 1) ∈ ChapterA.Section03.localCComponents (S : Subgroup (X ⧸ pCore 2 X)) ∧
      image (F.Li L 2) ∈ ChapterA.Section03.localCComponents (S : Subgroup (X ⧸ pCore 2 X)) ∧
      image D ∈ ChapterA.Section03.localCComponents (S : Subgroup (X ⧸ pCore 2 X)) ∧
      ClassicalGroup.IsPSL (image (F.Li L 1) ⧸ pCore 2 (image (F.Li L 1))) 4 2 ∧
      ClassicalGroup.IsPSL (image (F.Li L 2) ⧸ pCore 2 (image (F.Li L 2))) 3 2 ∧
      ClassicalGroup.IsPSL (image (F.Li L 1 ⊔ (T : Subgroup G)) ⧸
        pCore 2 (image (F.Li L 1 ⊔ (T : Subgroup G)))) 4 2 ∧
      LargePointModel (image J) := by
  let X := J ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 X)
  let image := fun A : Subgroup G => (A.subgroupOf X).map q
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  have hJX : J ≤ X := le_sup_left
  have hB1X : F.Li L 1 ≤ X := hLJ.trans hJX
  have hB2X : F.Li L 2 ≤ X := (five_plane_residual_le_point h F).trans hB1X
  let S := (T.subtype hTX).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 X))
  change image (F.Li L 1) ∈ ChapterA.Section03.localCComponents (S : Subgroup (X ⧸ pCore 2 X)) ∧
    image (F.Li L 2) ∈ ChapterA.Section03.localCComponents (S : Subgroup (X ⧸ pCore 2 X)) ∧
    image D ∈ ChapterA.Section03.localCComponents (S : Subgroup (X ⧸ pCore 2 X)) ∧
    ClassicalGroup.IsPSL (image (F.Li L 1) ⧸ pCore 2 (image (F.Li L 1))) 4 2 ∧
    ClassicalGroup.IsPSL (image (F.Li L 2) ⧸ pCore 2 (image (F.Li L 2))) 3 2 ∧
    ClassicalGroup.IsPSL (image (F.Li L 1 ⊔ (T : Subgroup G)) ⧸
      pCore 2 (image (F.Li L 1 ⊔ (T : Subgroup G)))) 4 2 ∧
    LargePointModel (image J)
  let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']; infer_instance
  have localImage (A : Subgroup G) (hA : A ∈ ChapterA.Section03.localCComponents (T : Subgroup G))
      (hAX : A ≤ X) : image A ∈ ChapterA.Section03.localCComponents (S : Subgroup (X ⧸ pCore 2 X)) := by
    have hl : A.subgroupOf X ∈ ChapterA.Section03.localCComponents ((T : Subgroup G).subgroupOf X) :=
      ChapterA.Section03.SourceEmbeddings.local_restrict (S := (T : Subgroup G)) hA hAX
    change (A.subgroupOf X).map q ∈ ChapterA.Section03.localCComponents
      (((T : Subgroup G).subgroupOf X).map q)
    exact Chapter1.Section02.localCComponents_map_of_solvable_ker
      (B := A.subgroupOf X) (S := (T : Subgroup G).subgroupOf X) hl q
  have hDlocal : D ∈ ChapterA.Section03.localCComponents T :=
    hD.2.subgroupOf_of_le le_sup_left (sup_le hD.1 (F.invariant 2))
  refine ⟨localImage _ (Li_mem_local h earlier F 1 (Or.inl ⟨rfl,by decide,by decide⟩)).1 hB1X,
    localImage _ (Li_mem_local h earlier F 2 (Or.inl ⟨rfl,by decide,by decide⟩)).1 hB2X,
    localImage D hDlocal (hDJ.trans hJX), ?_, ?_, ?_, ?_⟩
  · have hm : ClassicalGroup.IsPSL (F.Li L 1 ⧸ pCore 2 (F.Li L 1)) 4 2 :=
      Li_core_model h F 1 (Or.inl ⟨rfl,by decide,by decide⟩)
    exact hm.of_mulEquiv (imageCoreEquiv X _ hB1X).symm
  · have hm : ClassicalGroup.IsPSL (F.Li L 2 ⧸ pCore 2 (F.Li L 2)) 3 2 :=
      Li_core_model h F 2 (Or.inl ⟨rfl,by decide,by decide⟩)
    exact hm.of_mulEquiv (imageCoreEquiv X _ hB2X).symm
  · exact (five_point_residual_join_model h earlier F).of_mulEquiv
      (imageCoreEquiv X _ (sup_le hB1X hTX)).symm
  · have hJc : (J.subgroupOf X).IsCComponent :=
      hJ.2.subgroupOf_of_le hJX (sup_le hJ.1 (F.invariant 1))
    let e := subgroupOfEquivOfLe hJX
    let eQ := (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm.trans
      (cComponentTwoCoreQuotientEquiv hJc)
    rcases hJmodel with hm | hm | hm
    · exact Or.inl (hm.of_mulEquiv eQ.symm)
    · obtain ⟨eM⟩ := hm
      exact Or.inr (Or.inl ⟨eQ.symm.trans eM⟩)
    · obtain ⟨eM⟩ := hm
      exact Or.inr (Or.inr ⟨eQ.symm.trans eM⟩)


/-- The source point component is normal in its own Sylow overgroup, and
its image and the original Sylow image generate the whole core quotient. -/
theorem five_quotient_point_component
    (F : InvariantFlag T V 5) (J : Subgroup G)
    (hJ : J ∈ Chapter1.cComponentsIn F.H) (hJn : (J.subgroupOf F.H).Normal) :
    let X := J ⊔ (T : Subgroup G)
    let q := QuotientGroup.mk' (pCore 2 X)
    let image := fun A : Subgroup G => (A.subgroupOf X).map q
    (image J).IsCComponent ∧ (image J).Normal ∧
      image J ⊔ image (T : Subgroup G) = ⊤ := by
  let X := J ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 X)
  have hJX : J ≤ X := le_sup_left
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  have hXH : X ≤ F.H := sup_le hJ.1 (F.invariant 1)
  have hcomp : (J.subgroupOf X).IsCComponent := hJ.2.subgroupOf_of_le hJX hXH
  let : (J.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hJX).mpr
    (hXH.trans ((normal_subgroupOf_iff_le_normalizer hJ.1).mp hJn))
  let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
  refine ⟨hcomp.map_quotient _,
    (inferInstance : (J.subgroupOf X).Normal).map q (QuotientGroup.mk'_surjective _), ?_⟩
  change (J.subgroupOf X).map q ⊔ ((T : Subgroup G).subgroupOf X).map q = ⊤
  rw [← Subgroup.map_sup, ← subgroupOf_sup hJX hTX, subgroupOf_self,
    map_top_of_surjective q (QuotientGroup.mk'_surjective _)]

/-- Every failure of the source plane assertion constructs the original
strict pair together with its full quotient configuration. This is the
consumer of the residual and quotient comparisons, ready for the three
finite-model Sylow-overgroup calculations on printed pp.858--859. -/
theorem exists_five_plane_quotient_obstruction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5)
    (hfail : ¬ (((F.Li L 2).subgroupOf (F.Gi 2)).IsCComponent ∧
      ((F.Li L 2).subgroupOf (F.Gi 2)).Normal)) :
    ∃ J D : Subgroup G,
      J ∈ Chapter1.cComponentsIn F.H ∧ F.Li L 1 < J ∧
      (J.subgroupOf F.H).Normal ∧ LargePointModel (J ⧸ pCore 2 J) ∧
      D ∈ Chapter1.cComponentsIn (F.Gi 2) ∧ F.Li L 2 < D ∧
      (D.subgroupOf (F.Gi 2)).Normal ∧ D < J ∧
      let X := J ⊔ (T : Subgroup G)
      let q := QuotientGroup.mk' (pCore 2 X)
      let image := fun A : Subgroup G => (A.subgroupOf X).map q
      let S := (T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)).mapSurjective
        (QuotientGroup.mk'_surjective (pCore 2 X))
      LargePointModel (X ⧸ pCore 2 X) ∧ image J = ⊤ ∧
      (image J).IsCComponent ∧ (image J).Normal ∧
      image J ⊔ (S : Subgroup (X ⧸ pCore 2 X)) = ⊤ ∧
      LargePointModel (image J) ∧
      image (F.Li L 1) ∈ ChapterA.Section03.localCComponents (S : Subgroup (X ⧸ pCore 2 X)) ∧
      image (F.Li L 2) ∈ ChapterA.Section03.localCComponents (S : Subgroup (X ⧸ pCore 2 X)) ∧
      image D ∈ ChapterA.Section03.localCComponents (S : Subgroup (X ⧸ pCore 2 X)) ∧
      ClassicalGroup.IsPSL (image (F.Li L 1) ⧸ pCore 2 (image (F.Li L 1))) 4 2 ∧
      ClassicalGroup.IsPSL (image (F.Li L 2) ⧸ pCore 2 (image (F.Li L 2))) 3 2 ∧
      ClassicalGroup.IsPSL (image (F.Li L 1 ⊔ (T : Subgroup G)) ⧸
        pCore 2 (image (F.Li L 1 ⊔ (T : Subgroup G)))) 4 2 ∧
      image (F.Li L 2 ⊔ (T : Subgroup G)) < image (D ⊔ (T : Subgroup G)) ∧
      image (D ⊔ (T : Subgroup G)) < ⊤ ∧
      image (D ⊔ (T : Subgroup G)) ≠ image (F.Li L 1 ⊔ (T : Subgroup G)) ∧
      image (F.Li L 2) < image D ∧
      ¬ image D ≤ normalizer (image (F.Li L 2) : Set (X ⧸ pCore 2 X)) ∧
      ¬ ClassicalGroup.IsPSL (image D ⧸ pCore 2 (image D)) 4 2 ∧
      ¬ ClassicalGroup.IsPSL (image D ⧸ pCore 2 (image D)) 5 2 ∧
      ¬ Nonempty ((image D ⧸ pCore 2 (image D)) ≃* Sporadic.Mathieu.M24) := by
  obtain ⟨J,D,hJ,hLJ,hJn,hJm,hD,hLD,hDn,hDJ,_,hfour,hfive,hmathieu⟩ :=
    exists_five_strict_plane_components h earlier F hfail
  have hchain := five_quotient_overgroup_chain h earlier F J D hJ hLJ.le hJn hD hDn hLD hDJ
  obtain ⟨hl1,hl2,hd,hm1,hm2,hm1T,hjm⟩ :=
    five_quotient_local_models h earlier F J D hJ hLJ.le hJm hD hDJ.le
  obtain ⟨hc,hn,hgen⟩ := five_quotient_point_component F J hJ hJn
  have hXm := (five_point_join_quotient_model h earlier F J hJ.1 hLJ.le hJn hJm).2
  have hJtop := five_point_image_eq_top h earlier F J hJ.1 hLJ.le hJn hJm
  refine ⟨J,D,hJ,hLJ,hJn,hJm,hD,hLD,hDn,hDJ,hXm,hJtop,hc,hn,hgen,hjm,
    hl1,hl2,hd,hm1,hm2,hm1T,hchain.1,hchain.2.1,hchain.2.2.1,hchain.2.2.2.1,
    hchain.2.2.2.2,?_,?_,?_⟩
  · intro hm
    exact hfour (hm.of_mulEquiv (imageCoreEquiv (J ⊔ (T : Subgroup G)) D
      (hDJ.le.trans le_sup_left)))
  · intro hm
    exact hfive (hm.of_mulEquiv (imageCoreEquiv (J ⊔ (T : Subgroup G)) D
      (hDJ.le.trans le_sup_left)))
  · rintro ⟨e⟩
    exact hmathieu ⟨(imageCoreEquiv (J ⊔ (T : Subgroup G)) D
      (hDJ.le.trans le_sup_left)).trans e⟩

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
