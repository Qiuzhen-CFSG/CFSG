module
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.TwoCoreParabolics
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeLinearSelection
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.StarCoordinates
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSymplecticGeometry
public import CFSG.Quasithin.ChapterF.Section01.CoreQuotient

/-!
# Complete higher-field linear right factors for the prime Cartan argument

The canonical factor is the solvable residual of the marked parabolic
preimage inside the original component. The overlap two-core preserves
that parabolic when the marked exponent is not two, and therefore preserves
its whole perfect residual, without removing the cubic covering center.

The two-point diagram action bounds each Sylow-normalizer index by two.
The unique Sylow subgroup of the model Borel identifies the literal local
Borel with the original overlap; restriction of the original odd Hall
subgroup then gives its exact Borel product. These calculations supply
all RightData clauses and both genuine core alternatives for the prime pair.
The source dispatcher leaves only the linear field-four row for selection.

Field-four covering geometry, zero-core model exclusions, the outstanding
field comparisons and universal changed-Sylow normalization remain with
qt-d-1222-rankone-cartan-local-to-global. No equality of the original and
residual field degrees is imposed. Source: Aschbacher–Smith E.2.2,
5.1.10–11 and 5.2.1–2, printed pp.215–216,634–635,646–649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open Matrix.PSL3.LinearThree
open Matrix.PSL3.LinearThree.OuterExtensions
variable {X : Type*} [Group X] [Finite X]
variable {Y : Type*} [Group Y]
variable {F : Type} [Field F] [Finite F] [CharP F 2]

/-- The marked full parabolic preimage inside the original component. -/
@[expose] def linearSourceParabolic (M C : Subgroup X)
    (e : sourceImage M C ≃* PSL(3,F)) (i : Bool) : Subgroup X :=
  ((CoveredLocals.parabolic F i).comap (linearComponentProjection M C e)).map C.subtype

omit [Finite X] [CharP F 2] in
/-- The parabolic preimage retains its intersection with the actual component. -/
theorem linearSourceParabolic.eq_preimage {M C : Subgroup X}
    (e : sourceImage M C ≃* PSL(3,F)) (i : Bool) :
    linearSourceParabolic M C e i = C ⊓
      (((CoveredLocals.parabolic F i).map
        ((sourceImage M C).subtype.comp e.symm.toMonoidHom)).comap
          (QuotientGroup.mk' (sourceKernel M))) := by
  let q := QuotientGroup.mk' (sourceKernel M)
  let j := (sourceImage M C).subtype.comp e.symm.toMonoidHom
  let r := linearComponentProjection M C e
  have heq (x : C) : j (r x) = q x.val := by
    change (e.symm (e ((q.subgroupMap C) x))).val = _
    exact congrArg Subtype.val (e.symm_apply_apply ((QuotientGroup.mk' (sourceKernel M)).subgroupMap C x))
  have hj : Function.Injective j := (sourceImage M C).subtype_injective.comp e.symm.injective
  ext x
  constructor
  · rintro ⟨c,hc,rfl⟩
    exact ⟨c.property,r c,hc,heq c⟩
  · rintro ⟨hx,y,hy,he⟩
    refine ⟨⟨x,hx⟩,?_,rfl⟩
    change r ⟨x,hx⟩ ∈ CoveredLocals.parabolic F i
    have hh : r ⟨x,hx⟩ = y := hj ((heq ⟨x,hx⟩).trans he.symm)
    rwa [hh]

omit [CharP F 2] in
/-- The canonical factor is the perfect residual of that same parabolic. -/
theorem linearSourceFactor.eq_parabolic_residual {M C : Subgroup X}
    (e : sourceImage M C ≃* PSL(3,F)) (i : Bool) :
    linearSourceFactor M C e i =
      (solvableResidual (linearSourceParabolic M C e i)).map
        (linearSourceParabolic M C e i).subtype := by
  let P := (CoveredLocals.parabolic F i).comap (linearComponentProjection M C e)
  have hh := congrArg (map (P.map C.subtype).subtype)
    (map_solvableResidual_eq (C.subtype.subgroupMap P) (C.subtype.subgroupMap_surjective P))
  change ((solvableResidual P).map P.subtype).map C.subtype =
    (solvableResidual (P.map C.subtype)).map (P.map C.subtype).subtype
  rw [←hh,map_map,map_map]
  rfl

omit [CharP F 2] in
/-- Parabolic preservation in the source quotient lifts to the whole factor. -/
theorem linearSourceFactor.normalizes_of_parabolic {M C : Subgroup X} [C.Normal]
    (e : sourceImage M C ≃* PSL(3,F)) (i : Bool) {g : X}
    (hg : QuotientGroup.mk' (sourceKernel M) g ∈ normalizer
      ((CoveredLocals.parabolic F i).map
        ((sourceImage M C).subtype.comp e.symm.toMonoidHom) : Set _)) :
    g ∈ normalizer (linearSourceFactor M C e i : Set X) := by
  rw [linearSourceFactor.eq_parabolic_residual]
  apply normalizer_le_normalizer_characteristic_image
    (linearSourceParabolic M C e i) (solvableResidual (linearSourceParabolic M C e i))
  rw [linearSourceParabolic.eq_preimage]
  apply inf_normalizer_le_normalizer_inf
  exact ⟨normalizer_eq_top (H := C) ▸ mem_top g,
    le_normalizer_comap (QuotientGroup.mk' (sourceKernel M)) hg⟩

omit [CharP F 2] in
/-- The factor maps onto the literal projective local under the original marking. -/
theorem linearSourceFactor.map_quotient (hF : 4 ≤ Nat.card F)
    (M C : Subgroup X) (e : sourceImage M C ≃* PSL(3,F)) (i : Bool) :
    (linearSourceFactor M C e i).map (QuotientGroup.mk' (sourceKernel M)) =
      (CoveredLocals.localProjective F i).map
        ((sourceImage M C).subtype.comp e.symm.toMonoidHom) := by
  let q := QuotientGroup.mk' (sourceKernel M)
  let j := (sourceImage M C).subtype.comp e.symm.toMonoidHom
  let r := linearComponentProjection M C e
  have hr : Function.Surjective r := e.surjective.comp (q.subgroupMap_surjective C)
  calc
    _ = ((CoveredLocals.factor r i).map r).map j := by
      change ((CoveredLocals.factor r i).map C.subtype).map q = _
      rw [Subgroup.map_map (CoveredLocals.factor r i) q C.subtype,
        Subgroup.map_map (CoveredLocals.factor r i) j r]
      apply congrArg (fun z : C →* X ⧸ sourceKernel M => (CoveredLocals.factor r i).map z)
      ext x
      exact (congrArg Subtype.val (e.symm_apply_apply
        ((QuotientGroup.mk' (sourceKernel M)).subgroupMap C x))).symm
    _ = _ := by rw [CoveredLocals.factor_image hF r hr]

/-- Outside field four, the overlap two-core normalizes the whole selected factor. -/
theorem linearSourceFactor.twoCore_normalizes {M C : Subgroup X} [C.Normal]
    {f : ℕ} (hf : 1 < f) (hf2 : f ≠ 2) (hF : Nat.card F = 2 ^ f)
    (e : sourceImage M C ≃* PSL(3,F))
    (he : (componentOverlap M C).map e.toMonoidHom = borel F) (i : Bool) :
    M.pCoreIn 2 ≤ normalizer (linearSourceFactor M C e i : Set X) := by
  let q := QuotientGroup.mk' (sourceKernel M)
  let N := sourceImage M C
  let : N.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let j := N.subtype.comp e.symm.toMonoidHom
  have hM : (M.map q).comap j = borel F := by
    rw [source_overlap_coordinate] at he
    exact (comap_equiv_eq_map_symm e.symm _).trans he
  have hn := twoCore_normalizes_parabolic hF hf hf2 N (M.map q) e.symm hM i
  have hmap : (M.pCoreIn 2).map q ≤ (M.map q).pCoreIn 2 := by
    have hh : (pCore 2 M).map (q.subgroupMap M) ≤ pCore 2 (M.map q) :=
      le_sSup ⟨Normal.map inferInstance _ (q.subgroupMap_surjective M),pCore_isPGroup.map _⟩
    have hh' := map_mono (f := (M.map q).subtype) hh
    have heq : (M.map q).subtype.comp (q.subgroupMap M) = q.comp M.subtype := by
      ext x
      rfl
    simpa only [pCoreIn,map_map,heq] using hh'
  intro g hg
  exact linearSourceFactor.normalizes_of_parabolic e i (hn (hmap (mem_map_of_mem q hg)))

omit [CharP F 2] in
/-- The two diagram nodes bound the relative normalizer index, including field four. -/
theorem linearSourceFactor.normalizer_index_le_two {M C U : Subgroup X} [C.Normal]
    {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f) (hUM : U ≤ M)
    (e : sourceImage M C ≃* PSL(3,F))
    (he : (componentOverlap M C).map e.toMonoidHom = borel F) (i : Bool) :
    (U ⊓ normalizer (linearSourceFactor M C e i : Set X)).relIndex U ≤ 2 := by
  let q := QuotientGroup.mk' (sourceKernel M)
  let N := sourceImage M C
  let : N.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let j := N.subtype.comp e.symm.toMonoidHom
  have hM : (M.map q).comap j = borel F := by
    rw [source_overlap_coordinate] at he
    exact (comap_equiv_eq_map_symm e.symm _).trans he
  let a := (markedAction N e.symm).comp (q.comp U.subtype)
  let r := (diagramAction F (by omega : 0 < f) hF).comp a
  have hkn : r.ker ≤ (normalizer (linearSourceFactor M C e i : Set X)).subgroupOf U := by
    intro u hu
    have hk : diagramAction F (by omega : 0 < f) hF (a u) = 1 := hu
    have hb := markedAction_preserves_borel N (M.map q) e.symm hM (mem_map_of_mem q (hUM u.property))
    have hU := Matrix.PSL3.CartanActions.FullTorusFixer.map_unipotent_of_map_borel hF (a u) hb
    have hp := Matrix.PSL3Even.MinimalParabolicWitness.map_parabolic_of_preserves_unipotent
      F (by omega : 0 < f) hF (a u) hU i
    rw [hk] at hp
    apply linearSourceFactor.normalizes_of_parabolic e i
    apply mem_normalizer_iff_map_conj_eq.mpr
    calc
      _ = ((CoveredLocals.parabolic F i).map (a u).toMonoidHom).map j := by
        rw [map_map,map_map]
        congr 1
        ext x
        exact (markedAction_apply N e.symm (q u.val) x).symm
      _ = _ := by change ((Matrix.PSL3.RootPlaneGeometry.parabolic F i).map (a u).toMonoidHom).map j = _; rw [hp]; rfl
  rw [inf_relIndex_left]
  have hd := index_dvd_of_le hkn
  have hri : r.ker.index ≤ 2 := by
    rw [index_ker]
    apply le_trans (card_le_card_group r.range)
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero r.ker.index_ne_zero_of_finite) hd).trans hri
omit [CharP F 2] in
private theorem model_sylow_in_borel {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 1 ≤ f)
    {A : Subgroup (PSL(3,F))} (hUA : unipotent F ≤ A) (P : Sylow 2 A)
    (hP : (P : Subgroup A).map A.subtype ≤ borel F) :
    (P : Subgroup A).map A.subtype = unipotent F := by
  have hle : (P : Subgroup A).map A.subtype ≤ unipotent F := by
    have hh := (unipotentSylow F (by omega) hF).is_maximal'
      ((P.isPGroup'.map A.subtype).to_sup_of_normal_right'
        (unipotentSylow F (by omega) hF).isPGroup' (hP.trans (borel_le_normalizer_unipotent F))) le_sup_right
    exact le_sup_left.trans hh.le
  have he := P.3 ((unipotentSylow F (by omega) hF).isPGroup'.comap_of_injective A.subtype A.subtype_injective)
    (map_le_iff_le_comap.mp hle)
  rw [←he]
  exact map_subgroupOf_eq_of_le hUA

omit [CharP F 2] in
private theorem mapped_sylow_eq_unipotent {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 1 ≤ f)
    (q : X →* Y) (j : PSL(3,F) →* Y) (hj : Function.Injective j)
    {M R : Subgroup X} {A : Subgroup (PSL(3,F))}
    (hM : (M.map q).comap j = borel F)
    (hR : R.map q = A.map j) (hUA : unipotent F ≤ A)
    (P : Sylow 2 R) (hP : (P : Subgroup R).map R.subtype ≤ M) :
    ((P : Subgroup R).map R.subtype).map q = (unipotent F).map j := by
  let e := (MulEquiv.subgroupCongr hR).trans (A.equivMapOfInjective j hj).symm
  let a := e.toMonoidHom.comp (q.subgroupMap R)
  have ha : Function.Surjective a := e.surjective.comp (q.subgroupMap_surjective R)
  let Q := P.mapSurjective ha
  have hmap : ((Q : Subgroup A).map A.subtype).map j =
      ((P : Subgroup R).map R.subtype).map q := by
    change (((P : Subgroup R).map a).map A.subtype).map j = _
    simp only [map_map]
    congr 1
    ext x
    change j (e (q.subgroupMap R x)).val = q x.val
    exact congrArg Subtype.val ((A.equivMapOfInjective j hj).apply_symm_apply
      ((MulEquiv.subgroupCongr hR) (q.subgroupMap R x)))
  have hb : (Q : Subgroup A).map A.subtype ≤ borel F := by
    rw [←hM]
    apply map_le_iff_le_comap.mp
    rw [hmap]
    exact map_mono hP
  rw [←hmap,model_sylow_in_borel hF hf hUA Q hb]


omit [CharP F 2] in
/-- The literal rank-one Borel is the original maximal-subgroup intersection. -/
theorem linearSourceFactor.borel_eq_overlap {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (T : Sylow 2 X) {M C : Subgroup X} (hTM : (T : Subgroup X) ≤ M)
    (e : sourceImage M C ≃* PSL(3,F))
    (he : (componentOverlap M C).map e.toMonoidHom = borel F)
    (i : Bool)
    (hnot : ¬ linearSourceFactor M C e i ≤ M)
    (hquot : ChapterF.Source.IsRankOneModel
      (linearSourceFactor M C e i ⧸ pCore 2 (linearSourceFactor M C e i)))
    (P : Sylow 2 (linearSourceFactor M C e i))
    (hP : (P : Subgroup _).map (linearSourceFactor M C e i).subtype =
      (T : Subgroup X) ⊓ linearSourceFactor M C e i) :
    ChapterF.Source.borel (linearSourceFactor M C e i) (T : Subgroup X) =
      M ⊓ linearSourceFactor M C e i := by
  let R := linearSourceFactor M C e i
  let q := QuotientGroup.mk' (sourceKernel M)
  let j := (sourceImage M C).subtype.comp e.symm.toMonoidHom
  have hj : Function.Injective j := (sourceImage M C).subtype_injective.comp e.symm.injective
  have hM : (M.map q).comap j = borel F := by
    rw [source_overlap_coordinate] at he
    exact (comap_equiv_eq_map_symm e.symm _).trans he
  have hUA : unipotent F ≤ CoveredLocals.localProjective F i := by
    cases i
    · exact unipotent_le_lineLocal F
    · exact unipotent_le_pointLocal F
  have hmP : ((T : Subgroup X) ⊓ R).map q = (unipotent F).map j := by
    rw [←hP]
    exact mapped_sylow_eq_unipotent hF hf.le q j hj hM (linearSourceFactor.map_quotient (by
        have hh := Nat.pow_le_pow_right (by decide : 0 < 2) hf
        omega) M C e i) hUA P
      (hP ▸ inf_le_left.trans hTM)
  have hbM : ChapterF.Source.borel R (T : Subgroup X) ≤ M := by
    intro x hx
    obtain ⟨y,hy,hxy⟩ := (linearSourceFactor.map_quotient (by
        have hh := Nat.pow_le_pow_right (by decide : 0 < 2) hf
        omega) M C e i).le (mem_map_of_mem q hx.1)
    have hn : q x ∈ normalizer ((unipotent F).map j : Set _) := by
      rw [←hmP]
      exact le_normalizer_map q (mem_map_of_mem q hx.2)
    have hny : y ∈ normalizer (unipotent F : Set (PSL(3,F))) := by
      rw [←hxy] at hn
      change y ∈ (normalizer ((unipotent F).map j : Set _)).comap j at hn
      rwa [comap_normalizer_eq_of_le_range (map_le_range _ _),
        comap_map_eq_self_of_injective hj] at hn
    have hym : j y ∈ M.map q := by
      change y ∈ (M.map q).comap j
      rw [hM,←normalizer_unipotent F (by omega) hF]
      exact hny
    rw [hxy] at hym
    have hpre : (M.map q).comap q = M := comap_map_eq_self (by
      rw [QuotientGroup.ker_mk'];exact M.normalCore_le)
    rw [←hpre]
    exact hym
  have hfacts := ChapterF.Source.rankOneBorelFacts_of_sylow R (T : Subgroup X) P hP
    (ChapterF.Source.rankOneSylowFacts_of_rankOneQuotient hquot P)
  apply le_antisymm (le_inf hbM inf_le_left)
  apply hfacts.unique_maximal
  · exact inf_le_inf hTM le_rfl
  · apply lt_of_le_of_ne inf_le_right
    intro hh
    exact hnot (hh.ge.trans inf_le_left)



/-- The marked linear factors supply every right-side local clause once the
overlap two-core preserves them. The source constructions below discharge this
precise preservation premise, including through the field-four scalar cover. -/
theorem linear_source_rightData_of_factor_normalizes
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L H A B : Subgroup G} {f : ℕ}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H)) (hf : 1 < f)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f)
    (e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* PSL(3,F))
    (he : (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
      e.toMonoidHom = borel F)
    (hmove : MovesDiagram ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) e
      (pointParabolic F) (lineParabolic F))
    (hSn0 : ∀ i, (((normalizer (L : Set G)).subgroupOf H).pCoreIn 2) ≤
      normalizer (linearSourceFactor ((normalizer (L : Set G)).subgroupOf H) C e i : Set H)) :
    ∃ R : Bool → Subgroup G, ∀ i, RightData T L H B (R i) ∧
      ClassicalGroup.IsPSL (R i ⧸ pCore 2 (R i)) 2 (2 ^ f) := by
  let S := T.subtype hH.1.1.2
  let M := (normalizer (L : Set G)).subgroupOf H
  have hr := linear_source_original_factors_marked
    hTL hH hpar c hC hqs hc hf hF e he hmove
  let R0 := linearSourceFactor M C e
  let R := fun i => (R0 i).map H.subtype
  have hST : (S : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le hH.1.1.2
  have hSK := diagram_sourceS_intersection_residual hTL hH hpar hC hc hf
    (Or.inl ⟨F,inferInstance,inferInstance,inferInstance,by omega,hF,e,he,hmove⟩)
  let : C.Normal := DiagramHall.single_component_normal S hC hc
  refine ⟨R,?_⟩
  intro i
  obtain ⟨hRK,hout,hgen,hquot,hcomp,hBn,P,hP⟩ := hr i
  have hRH : R i ≤ H := map_subtype_le _
  have hSm : (M.pCoreIn 2).map H.subtype = Global.sourceS L H := by
    rw [map_pCoreIn_of_injective 2 M H.subtype H.subtype_injective,subgroupOf_map_subtype]
    rfl
  have hSn : Global.sourceS L H ≤ normalizer (R i : Set G) := by
    rw [←hSm]
    exact (map_mono (hSn0 i)).trans
      (le_normalizer_map H.subtype)
  have hSR : Global.sourceS L H ⊓ R i = (T : Subgroup G) ⊓ R i := by
    calc
      _ = (Global.sourceS L H ⊓ residual H) ⊓ R i := by rw [inf_assoc,inf_eq_right.mpr hRK]
      _ = _ := by rw [hSK,inf_assoc,inf_eq_right.mpr hRK]
  let er := (R0 i).equivMapOfInjective H.subtype H.subtype_injective
  let P0 := P.mapSurjective (f := er.symm.toMonoidHom) er.symm.surjective
  have hP0 : (P0 : Subgroup (R0 i)).map (R0 i).subtype = (S : Subgroup H) ⊓ R0 i := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_inf _ _ _ H.subtype_injective,hST]
    calc
      _ = (P : Subgroup (R i)).map (R i).subtype := by
        change (((P : Subgroup (R i)).map er.symm.toMonoidHom).map (R0 i).subtype).map H.subtype = _
        simp only [map_map]
        congr 1
        ext x
        exact congrArg Subtype.val (er.apply_symm_apply x)
      _ = _ := hP.trans hSR
  let eqr := QuotientGroup.congr _ _ er (pCore_map_iso 2 er)
  have hnot0 : ¬ R0 i ≤ M := by
    intro hh
    exact hout (map_le_iff_le_comap.mpr hh)
  have hq0 : ChapterF.Source.IsRankOneModel (R0 i ⧸ pCore 2 (R0 i)) :=
    .linear f (by omega) (hquot.of_mulEquiv eqr)
  have hb0 := linearSourceFactor.borel_eq_overlap hf hF S (comap_mono hTL) e he i hnot0 hq0 P0 hP0
  have hb : ChapterF.Source.borel (R i) (Global.sourceS L H) =
      normalizer (L : Set G) ⊓ R i := by
    have hh := congrArg (map H.subtype) hb0
    change (ChapterF.Source.borel (R0 i) (S : Subgroup H)).map H.subtype =
      (M ⊓ R0 i).map H.subtype at hh
    rw [ChapterF.Source.borel_map_of_ker_le H.subtype (R0 i) S ⟨P0,hP0⟩
      (by rw [H.ker_subtype];exact bot_le),hST,
      Subgroup.map_inf _ _ _ H.subtype_injective,subgroupOf_map_subtype] at hh
    rw [inf_assoc,inf_eq_right.mpr hRH] at hh
    change R i ⊓ normalizer ((Global.sourceS L H ⊓ R i : Subgroup G) : Set G) = _
    rw [hSR]
    exact hh
  have hNC : (normalizer (R i : Set G)).comap H.subtype = normalizer (R0 i : Set H) := by
    rw [comap_normalizer_eq_of_le_range (by rw [range_subtype];exact hRH),
      comap_map_eq_self_of_injective H.subtype_injective]
  have hind : (normalizingSylow T (R i)).relIndex (T : Subgroup G) ≤ 2 := by
    change ((T : Subgroup G) ⊓ normalizer (R i : Set G)).relIndex (T : Subgroup G) ≤ 2
    rw [inf_relIndex_left,←hST,←relIndex_comap,hNC,←inf_relIndex_left]
    exact linearSourceFactor.normalizer_index_le_two hf hF (comap_mono hTL) e he i
  refine ⟨⟨hRK,hout,hgen,?_,hcomp,hind,hSK,hSn,hBn,⟨P,hP⟩,
    .linear f (by omega) hquot,?_⟩,hquot⟩
  · intro hs
    let := hs
    exact hcomp.not_isSolvable
      (Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe (show R i ≤ R i ⊔ normalizingSylow T (R i) from le_sup_left)).toMonoidHom)
        (subgroupOfEquivOfLe le_sup_left).injective)
  · let U := normalizer (L : Set G) ⊓ R i
    have hU : U ≤ Global.intersection L H := le_inf inf_le_left (inf_le_right.trans hRH)
    have hBU : B ≤ normalizer (U : Set G) :=
      (le_inf ((c.right_le.trans inf_le_left).trans (normalizer (L : Set G)).le_normalizer)
        hBn).trans inf_normalizer_le_normalizer_inf
    have hh := OddHall.hall_restrict_of_normalizes c.right_hall c.right_le hU hBU
    obtain ⟨Q,hQ⟩ := P.exists_map_subtype_eq_of_le (show U ≤ R i from inf_le_right)
      (hP.trans hSR ▸ le_inf (inf_le_left.trans hTL) inf_le_right)
    have heq := congrArg (map U.subtype) (OddHall.sylow_complement_of_hall Q hh).sup_eq_top
    have hi : B ⊓ U = B ⊓ R i := by
      dsimp [U]
      rw [←inf_assoc,inf_eq_left.mpr (c.right_le.trans inf_le_left)]
    rw [Subgroup.map_sup,hQ,hP,subgroupOf_map_subtype,hi,
      ←MonoidHom.range_eq_map,range_subtype] at heq
    rw [hb]
    exact heq.symm

/-- The higher-field linear diagram row supplies every right-side local clause. -/
theorem linear_source_rightData
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L H A B : Subgroup G} {f : ℕ}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H)) (hf : 1 < f) (hf2 : f ≠ 2)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f)
    (e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* PSL(3,F))
    (he : (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
      e.toMonoidHom = borel F)
    (hmove : MovesDiagram ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) e
      (pointParabolic F) (lineParabolic F)) :
    ∃ R : Bool → Subgroup G, ∀ i, RightData T L H B (R i) ∧
      ClassicalGroup.IsPSL (R i ⧸ pCore 2 (R i)) 2 (2 ^ f) := by
  let : C.Normal := DiagramHall.single_component_normal (T.subtype hH.1.1.2) hC hc
  exact linear_source_rightData_of_factor_normalizes hTL hH hpar c hC hqs hc hf hF e he hmove
    (fun i => linearSourceFactor.twoCore_normalizes hf hf2 hF e he i)

/-- Outside field four, both linear factors give the genuine F.1.1 pair in the zero-core
branch and the actual moving-factor normalizer in the other branch. -/
theorem linear_source_prime_pair
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p f : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H)) (hf : 1 < f) (hf2 : f ≠ 2)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f)
    (e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* PSL(3,F))
    (he : (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
      e.toMonoidHom = borel F)
    (hmove : MovesDiagram ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) e
      (pointParabolic F) (lineParabolic F)) :
    ∃ R : Bool → Subgroup G, ∀ i,
      ClassicalGroup.IsPSL (R i ⧸ pCore 2 (R i)) 2 (2 ^ f) ∧
      LocalData T L H B D (R i) ∧
      (((generated L H D (R i)).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R i] (Global.sourceS L H)) ∨
       ((generated L H D (R i)).pCoreIn 2 ≠ ⊥ ∧ ¬ D ≤ normalizer (R i : Set G) ∧
        (normalizingSylow T (R i)).relIndex (T : Subgroup G) = 2)) := by
  obtain ⟨R,hr⟩ := linear_source_rightData h.sylow_normalizes hH hpar c hC hqs hc hf hf2 hF e he hmove
  refine ⟨R,?_⟩
  intro i
  let d := (hr i).1.localData h hH c hd
  refine ⟨(hr i).2,d,?_⟩
  by_cases hz : (generated L H D (R i)).pCoreIn 2 = ⊥
  · exact Or.inl ⟨hz,d.hypothesisF11 h hH c hd hz⟩
  · exact Or.inr ⟨hz,d.prime_actor_not_normalizes_right h hH c hd hz,
      d.normalizingSylow_index hH.1.1.2 c hd hz⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open Matrix.PSL3.LinearThree
variable {G : Type*} [Group G] [Finite G]

/-- The remaining field-four linear source row, with the actual component,
scalar-cover alternative, projective marking, Borel and diagram action. -/
@[expose] def RightLinearFourDiagramSource (T : Sylow 2 G) (L H : Subgroup G) : Prop :=
  ∃ C : Subgroup H, C.IsCComponent ∧ IsQuasisimple (C ⧸ pCore 2 C) ∧
    C ⊔ (T : Subgroup G).subgroupOf H = ⊤ ∧
    SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) ∧
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 4 ∧
      ∃ e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* PSL(3,F),
        (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
          e.toMonoidHom = borel F ∧
        MovesDiagram ((normalizer (L : Set G)).subgroupOf H) C
          ((T : Subgroup G).subgroupOf H) e (pointParabolic F) (lineParabolic F)
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- All source rows construct the literal prime pair except for the linear
field-four row. Its special-linear cover is retained for the remaining argument. -/
theorem source_prime_pair_or_four_linear_diagram
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hd : CartanPrimeActor A H p D) :
    (∃ R : Subgroup G, LocalData T L H B D R) ∨ Global.RightLinearFourDiagramSource T L H := by
  rcases source_prime_pair_or_linear_diagram h hH hpar c hd with hr | hs
  · exact Or.inl hr
  obtain ⟨C,f,hC,hqs,hgen,hf,hc,F,_,_,_,_,hF,e,he,hmove⟩ := hs
  by_cases hf2 : f = 2
  · subst f
    exact Or.inr ⟨C,hC,hqs,hgen,hc,F,inferInstance,inferInstance,inferInstance,
      by simpa using hF,e,he,hmove⟩
  · obtain ⟨R,hr⟩ := linear_source_rightData h.sylow_normalizes hH hpar c hC hqs hc hf hf2 hF e he hmove
    exact Or.inl ⟨R true,(hr true).1.localData h hH c hd⟩
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
