module
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.CoveredLocals
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeDiagramSource
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeConstruction
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalRightGeometry

/-!
# The two linear diagram factors over the original source marking

Take the solvable residuals of the point and line parabolic preimages in
C. The literal component projection factors through C/O₂(C). The scalar
covering theorem identifies both residual quotients with PSL₂ over the
same field, without deleting the possible cubic center of C/O₂(C).
Perfectness and the quotient models prove their relative component property.

The marked Borel normalizes both factors and neither lies in it. On the
original H-star subgroup, this gives generation with T, normalization by
the actual odd Hall subgroup B, and full Sylow intersections. The proved
source equality S ∩ K = T ∩ K transfers those intersections to S.
The separate normalization of the whole factors by S, the remaining
RightData clauses and all outstanding normalization cases remain with
qt-d-1222-rankone-cartan-local-to-global.

Source: Aschbacher–Smith E.2.2,I.1.3,5.1.10–11,5.2.1–2,
printed pp.215–216,407,634–635,646–649 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open Matrix.PSL3.LinearThree
variable {X : Type*} [Group X] [Finite X]
variable {F : Type} [Field F] [Finite F] [CharP F 2]

/-- The prescribed source projection on the original component. -/
@[expose] def linearComponentProjection (M C : Subgroup X)
    (e : sourceImage M C ≃* PSL(3,F)) : C →* PSL(3,F) :=
  e.toMonoidHom.comp ((QuotientGroup.mk' (sourceKernel M)).subgroupMap C)

/-- The two canonical perfect parabolic lifts inside the original component. -/
@[expose] def linearSourceFactor (M C : Subgroup X)
    (e : sourceImage M C ≃* PSL(3,F)) (i : Bool) : Subgroup X :=
  (CoveredLocals.factor (linearComponentProjection M C e) i).map C.subtype

omit [Finite X] [Finite F] [CharP F 2] in
private theorem linear_projection_surjective {M C : Subgroup X}
    (e : sourceImage M C ≃* PSL(3,F)) :
    Function.Surjective (linearComponentProjection M C e) :=
  e.surjective.comp ((QuotientGroup.mk' (sourceKernel M)).subgroupMap_surjective C)

omit [Finite X] [Finite F] [CharP F 2] in
private theorem linear_projection_borel {M C : Subgroup X}
    (e : sourceImage M C ≃* PSL(3,F))
    (he : (componentOverlap M C).map e.toMonoidHom = borel F) :
    (borel F).comap (linearComponentProjection M C e) = M.subgroupOf C := by
  ext x
  let z : sourceImage M C := ⟨QuotientGroup.mk' (sourceKernel M) x.val,x.val,x.property,rfl⟩
  change e z ∈ borel F ↔ _
  rw [←he,mem_map_equiv,e.symm_apply_apply]
  change QuotientGroup.mk' (sourceKernel M) x.val ∈ sourceImage M (M ⊓ C) ↔ x.val ∈ M
  constructor
  · rintro ⟨m,hm,hmx⟩
    have hd := QuotientGroup.eq_iff_div_mem.mp hmx
    have hdM := M.normalCore_le hd
    have hh := M.mul_mem (M.inv_mem hdM) hm.1
    simpa only [div_eq_mul_inv,mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel,mul_one] using hh
  · intro hx
    exact ⟨x.val,⟨hx,x.property⟩,rfl⟩

private theorem perfect_twoPerfect (R : Type*) [Group R] [Finite R] [Group.IsPerfect R] :
    IsPPerfect 2 R := by
  intro J hJ hp
  let := hJ
  apply top_unique
  intro x _
  apply (QuotientGroup.eq_one_iff x).mp
  by_contra hh
  let : Nontrivial (R ⧸ J) := ⟨⟨QuotientGroup.mk x,1,hh⟩⟩
  exact Group.IsPerfect.not_isNilpotent (R ⧸ J) hp.isNilpotent

omit [Finite F] in
private theorem perfect_rankOne_component
    (R : Subgroup X) [Group.IsPerfect R] {J : Subgroup X}
    (hRJ : R ≤ J) (hJN : J ≤ normalizer (R : Set X)) (hF : 4 ≤ Nat.card F)
    (e : (R ⧸ pCore 2 R) ≃* PSL(2,F)) :
    (R.subgroupOf J).IsCComponent := by
  let a := e.trans (Theory.PSL2.sl2QuotientEquiv F).symm
  let : Group.IsPerfect SL(2,F) := Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective
  let : IsQuasisimple SL(2,F) := ⟨Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF⟩
  let : IsQuasisimple (R ⧸ pCore 2 R) := IsQuasisimple.of_mulEquiv a.symm
  let j := subgroupOfEquivOfLe hRJ
  let eqj := QuotientGroup.congr _ _ j (pCore_map_iso 2 j)
  let : IsQuasisimple ((R.subgroupOf J) ⧸
      pCore 2 (R.subgroupOf J)) := IsQuasisimple.of_mulEquiv eqj.symm
  have hn : (R.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer hJN
  exact isCComponent_of_isPPerfect_of_quasisimple_core_quotient hn.isSubnormal
    ((perfect_twoPerfect R).of_surjective j.symm.toMonoidHom j.symm.surjective)

/-- The source center is retained while both literal factors acquire their
rank-one quotient, perfectness, and relative component property. -/
theorem linear_source_factor_spec {M C : Subgroup X} {f : ℕ}
    (hC : C.IsCComponent) (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hO : pCore 2 X ≤ sourceKernel M) (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (e : sourceImage M C ≃* PSL(3,F))
    (he : (componentOverlap M C).map e.toMonoidHom = borel F) (i : Bool) :
    let R := linearSourceFactor M C e i
    R ≤ C ∧ ¬ R ≤ M ∧ Group.IsPerfect R ∧
      Nonempty ((R ⧸ pCore 2 R) ≃* PSL(2,F)) ∧
      (R.subgroupOf (normalizer (R : Set X))).IsCComponent ∧
      M ⊓ C ≤ normalizer (R : Set X) := by
  let r := linearComponentProjection M C e
  let R0 := CoveredLocals.factor r i
  let R := linearSourceFactor M C e i
  have hr : Function.Surjective r := linear_projection_surjective e
  have hlarge : 4 ≤ Nat.card F := by
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ f by omega)
    omega
  have hk : pCore 2 C ≤ r.ker := by
    intro x hx
    apply e.map_eq_one_iff.mpr
    apply Subtype.ext
    apply (QuotientGroup.eq_one_iff x.val).mpr
    apply hO
    exact pCoreIn_le_of_subnormal 2 hC.subnormal (mem_map_of_mem C.subtype hx)
  let r0 := QuotientGroup.lift (pCore 2 C) r hk
  have hr0 : Function.Surjective r0 := by
    intro y
    obtain ⟨x,hx⟩ := hr y
    exact ⟨QuotientGroup.mk' (pCore 2 C) x,hx⟩
  let := hqs
  let eq0 : (R0 ⧸ pCore 2 R0) ≃* PSL(2,F) := CoveredLocals.twoCoreFactorEquiv hlarge r0 hr0 i
  let er := R0.equivMapOfInjective C.subtype C.subtype_injective
  let eqr := QuotientGroup.congr _ _ er (pCore_map_iso 2 er)
  let eqR := eqr.symm.trans eq0
  let P := (CoveredLocals.parabolic F i).comap r
  let : Group.IsPerfect R0 := Group.IsPerfect.map P.subtype
  let : Group.IsPerfect R := Group.IsPerfect.map C.subtype
  have hB := linear_projection_borel e he
  have hn0 := CoveredLocals.borel_normalizes_factor r i
  rw [hB] at hn0
  have hn : M ⊓ C ≤ normalizer (R : Set X) := by
    have hh := (map_mono (f := C.subtype) hn0).trans (le_normalizer_map C.subtype)
    rwa [subgroupOf_map_subtype] at hh
  refine ⟨map_subtype_le _,?_,inferInstance,
    ⟨eqR⟩,perfect_rankOne_component R R.le_normalizer le_rfl hlarge eqR,hn⟩
  intro hRM
  exact CoveredLocals.factor_not_le_borel hlarge r hr i ((map_le_iff_le_comap.mp hRM).trans hB.ge)

private theorem sylow_in_normalized_subfactor
    {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) {K R : Subgroup G} (hRK : R ≤ K)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hTR : (T : Subgroup G) ⊓ K ≤ normalizer (R : Set G)) :
    ∃ P : Sylow 2 R, (P : Subgroup R).map R.subtype = (T : Subgroup G) ⊓ R := by
  obtain ⟨S,hS⟩ := NormalSylowQuotientAction.intersection_sylow T K hTK
  have hn : (S : Subgroup K) ≤ normalizer (R.subgroupOf K : Set K) := by
    rw [hS]
    apply le_trans _ (le_normalizer_comap K.subtype)
    intro x hx
    exact hTR ⟨hx,x.property⟩
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow S (R.subgroupOf K) hn
  let e := subgroupOfEquivOfLe hRK
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change ((P : Subgroup (R.subgroupOf K)).map e.toMonoidHom).map R.subtype = _
  rw [hP,hS]
  ext x
  constructor
  · rintro ⟨r,⟨y,hy,rfl⟩,rfl⟩
    exact ⟨hy,y.property⟩
  · rintro ⟨ht,hr⟩
    exact ⟨⟨x,hr⟩,⟨⟨⟨x,hRK hr⟩,hr⟩,ht,rfl⟩,rfl⟩

/-- Both original linear diagram factors are constructed in the literal
residual, with the original Hall action and full Sylow intersections.
No scalar-cover identification or equality of field degrees is assumed. -/
theorem linear_source_original_factors_marked
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
    (hF : Nat.card F = 2 ^ f)
    (e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* PSL(3,F))
    (he : (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
      e.toMonoidHom = borel F)
    (hmove : MovesDiagram ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) e (pointParabolic F) (lineParabolic F)) :
    let R := fun i => (linearSourceFactor
      ((normalizer (L : Set G)).subgroupOf H) C e i).map H.subtype
    ∀ i,
      R i ≤ residual H ∧ ¬ R i ≤ normalizer (L : Set G) ∧
      R i ⊔ (T : Subgroup G) = H ∧
      ClassicalGroup.IsPSL (R i ⧸ pCore 2 (R i)) 2 (2 ^ f) ∧
      ((R i).subgroupOf (R i ⊔ normalizingSylow T (R i))).IsCComponent ∧
      B ≤ normalizer (R i : Set G) ∧
      ∃ P : Sylow 2 (R i), (P : Subgroup (R i)).map (R i).subtype =
        Global.sourceS L H ⊓ R i := by
  let S := T.subtype hH.1.1.2
  let M := (normalizer (L : Set G)).subgroupOf H
  let R0 := linearSourceFactor M C e
  let R (i : Bool) := (R0 i).map H.subtype
  have hO : pCore 2 H ≤ sourceKernel M := normal_le_normalCore.mpr
    ((pCore_isPGroup.le_sylow_of_normal S).trans (comap_mono hTL))
  have hCK : C = pResidual 2 H := (DiagramHall.single_component_eq_twoResidual S hC hc).symm
  have hSK := diagram_sourceS_intersection_residual hTL hH hpar hC hc hf
    (Or.inl ⟨F,inferInstance,inferInstance,inferInstance,by omega,hF,e,he,hmove⟩)
  have hlarge : 4 ≤ Nat.card F := by
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ f by omega)
    omega
  dsimp only
  intro i
  obtain ⟨hRC,hout,hperfect,⟨eq0⟩,_,hn0⟩ :=
    linear_source_factor_spec hC hqs hO hf hF e he i
  let := hperfect
  let : Group.IsPerfect (R i) := Group.IsPerfect.map H.subtype
  have hRK : R i ≤ residual H := map_mono (hRC.trans_eq hCK)
  have hRH : R i ≤ H := map_subtype_le _
  have hnot : ¬ R i ≤ normalizer (L : Set G) :=
    fun hh => hout (map_le_iff_le_comap.mp hh)
  let er := (R0 i).equivMapOfInjective H.subtype H.subtype_injective
  let eqr := QuotientGroup.congr _ _ er (pCore_map_iso 2 er)
  let eqR := eqr.symm.trans eq0
  have hn : normalizer (L : Set G) ⊓ residual H ≤ normalizer (R i : Set G) := by
    have hh := (map_mono (f := H.subtype) hn0).trans (le_normalizer_map H.subtype)
    have heC : C.map H.subtype = residual H := congrArg (map H.subtype) hCK
    rw [Subgroup.map_inf _ _ _ H.subtype_injective,heC,subgroupOf_map_subtype] at hh
    exact le_trans (by
      intro x hx
      exact ⟨⟨hx.1,(map_subtype_le (pResidual 2 H)) hx.2⟩,hx.2⟩) hh
  have hjc := perfect_rankOne_component (R i)
    (show R i ≤ R i ⊔ normalizingSylow T (R i) from le_sup_left)
    (sup_le (R i).le_normalizer inf_le_right) hlarge eqR
  have hBn : B ≤ normalizer (R i : Set G) :=
    (le_inf (c.right_le.trans inf_le_left) (Global.right_cartan_le_residual c)).trans hn
  obtain ⟨P,hP⟩ := sylow_in_normalized_subfactor T hRK
    (hH.1.1.2.trans (le_normalizer_residual H)) ((inf_le_inf_right _ hTL).trans hn)
  have hSR : Global.sourceS L H ⊓ R i = (T : Subgroup G) ⊓ R i := by
    calc
      _ = (Global.sourceS L H ⊓ residual H) ⊓ R i := by rw [inf_assoc,inf_eq_right.mpr hRK]
      _ = _ := by rw [hSK,inf_assoc,inf_eq_right.mpr hRK]
  refine ⟨hRK,hnot,?_,⟨F,inferInstance,inferInstance,hF,⟨eqR⟩⟩,hjc,hBn,P,hP.trans hSR.symm⟩
  apply le_antisymm (sup_le hRH hH.1.1.2)
  by_contra hh
  have hlt : R i ⊔ (T : Subgroup G) < H :=
    lt_of_le_of_ne (sup_le hRH hH.1.1.2) (fun he => hh he.ge)
  exact hnot (le_sup_left.trans (Chapter3.HStar.proper_overgroup_le T hH le_sup_right hlt))

/-- The canonical marked factors also supply the original existential interface. -/
theorem linear_source_original_factors
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
    (hF : Nat.card F = 2 ^ f)
    (e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* PSL(3,F))
    (he : (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
      e.toMonoidHom = borel F)
    (hmove : MovesDiagram ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) e (pointParabolic F) (lineParabolic F)) :
    ∃ R : Bool → Subgroup G, ∀ i,
      R i ≤ residual H ∧ ¬ R i ≤ normalizer (L : Set G) ∧
      R i ⊔ (T : Subgroup G) = H ∧
      ClassicalGroup.IsPSL (R i ⧸ pCore 2 (R i)) 2 (2 ^ f) ∧
      ((R i).subgroupOf (R i ⊔ normalizingSylow T (R i))).IsCComponent ∧
      B ≤ normalizer (R i : Set G) ∧
      ∃ P : Sylow 2 (R i), (P : Subgroup (R i)).map (R i).subtype =
        Global.sourceS L H ⊓ R i := by
  refine ⟨fun i => (linearSourceFactor ((normalizer (L : Set G)).subgroupOf H) C e i).map H.subtype,?_⟩
  exact linear_source_original_factors_marked hTL hH hpar c hC hqs hc hf hF e he hmove

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
