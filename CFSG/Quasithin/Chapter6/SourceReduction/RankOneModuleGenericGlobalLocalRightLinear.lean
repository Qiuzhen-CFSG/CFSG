module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeLinearSelection
public import Theory.GroupTheory.SubgroupCoverTransport
public import Theory.GroupTheory.SylowPairSolvableGeneration
public import Theory.GroupTheory.SolvableResidual.PrimeTo

/-!
# Cartan action and exact Borels of the selected linear factors

The two maximal parabolic preimages over the marked Borel are intrinsic:
subgroup correspondence and the concrete PSL₃ Borel-overgroup theorem
identify every maximal overgroup with one of them. An odd group preserving
the original component overlap fixes both parabolics and their solvable
residuals. Applying this to the original left Cartan proves its action on
the canonical linear factors, including through a nontrivial scalar cover.

The actual Sylow of each factor maps onto the standard model unipotent
subgroup. Its normalizer therefore lies in the marked Borel. Normality of
S = O₂(N_G(L) ∩ H) proves the reverse inclusion. Restricting the original
odd Hall subgroup gives the full product with B ∩ R. The Chapter 12
extension applies this to local preparation with the independent original
uniqueness implication and source 5.2.1's whole-factor S-action explicit.
Neither that S-action nor completion recognition is asserted here.

The existing linear selection supplies the intrinsic rank-one quotients.
This extension retains its canonical factors so that Cartan action, Sylow
intersection and Borel equality refer to the same literal subgroup.
Source: Aschbacher--Smith 5.1.10--11, 5.2.1 and 5.2.4, printed
pp.634--635,646,649--650 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3 Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {X : Type*} [Group X] [Finite X]
variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] in
private theorem linear_parabolic_coatom (i : Bool) :
    IsCoatom (CoveredLocals.parabolic F i) := by
  have hp : IsCoatom ((CoveredLocals.parabolic F i).comap (projection F)) := by
    cases i
    · rw [show CoveredLocals.parabolic F false = lineParabolic F from rfl,
        lineParabolic_comap]
      exact lineParabolicSL_isCoatom F
    · rw [show CoveredLocals.parabolic F true = pointParabolic F from rfl,
        pointParabolic_comap]
      exact pointParabolicSL_isCoatom F
  have hh := isCoatom_map_of_surjective_of_ker_le (projection F)
    (projection_surjective F) _ ((CoveredLocals.parabolic F i).ker_le_comap _) hp
  rwa [map_comap_eq_self_of_surjective (projection_surjective F)] at hh

omit [Finite X] [CharP F 2] in
private theorem linear_coatom_pair (r : X →* PSL(3,F)) (hr : Function.Surjective r)
    (J : Subgroup X) (hb : (borel F).comap r ≤ J) (hc : IsCoatom J) :
    J = (pointParabolic F).comap r ∨ J = (lineParabolic F).comap r := by
  have hk := ((borel F).ker_le_comap r).trans hb
  have hm := isCoatom_map_of_surjective_of_ker_le r hr J hk hc
  have hb' : borel F ≤ J.map r := by
    have hh := map_mono (f := r) hb
    rwa [map_comap_eq_self_of_surjective hr] at hh
  have hh := ParabolicResiduals.coatom_over_borel F (J.map r) hb' hm
  rcases hh with hh | hh
  · exact Or.inl ((comap_map_eq_self hk).symm.trans (congrArg (comap r) hh))
  · exact Or.inr ((comap_map_eq_self hk).symm.trans (congrArg (comap r) hh))

omit [CharP F 2] in
private theorem odd_preserves_linear_factors {D : Type*} [Group D] [Finite D]
    (r : X →* PSL(3,F)) (hr : Function.Surjective r)
    (a : D →* MulAut X) (ho : Odd (Nat.card D))
    (ha : ∀ d, ((borel F).comap r).map (a d).toMonoidHom = (borel F).comap r)
    (i : Bool) (d : D) :
    (CoveredLocals.factor r i).map (a d).toMonoidHom = CoveredLocals.factor r i := by
  have hp (j : Bool) : IsCoatom ((CoveredLocals.parabolic F j).comap r) :=
    isCoatom_comap_of_surjective hr (linear_parabolic_coatom j)
  have hb (j : Bool) : (borel F).comap r ≤ (CoveredLocals.parabolic F j).comap r := by
    apply comap_mono
    cases j
    · exact map_mono (f := projection F) inf_le_right
    · exact map_mono (f := projection F) inf_le_left
  have hi : ∀ d : D, ∀ Y : Subgroup X,
      Y = (pointParabolic F).comap r ∨ Y = (lineParabolic F).comap r →
      Y.map (a d).toMonoidHom = (pointParabolic F).comap r ∨
      Y.map (a d).toMonoidHom = (lineParabolic F).comap r := by
    intro d Y hY
    have hc : IsCoatom Y := hY.elim (fun he => he ▸ hp true) (fun he => he ▸ hp false)
    have hBY : (borel F).comap r ≤ Y :=
      hY.elim (fun he => he ▸ hb true) (fun he => he ▸ hb false)
    exact linear_coatom_pair r hr _ ((ha d) ▸ map_mono hBY)
      (((a d).mapSubgroup.isCoatom_iff Y).mpr hc)
  have he := odd_preserves_pair a ho
    (show (CoveredLocals.parabolic F i).comap r = (pointParabolic F).comap r ∨
      (CoveredLocals.parabolic F i).comap r = (lineParabolic F).comap r by
      cases i
      · exact Or.inr rfl
      · exact Or.inl rfl) hi d
  change ((solvableResidual _).map _).map _ = _
  rw [map_embedded_solvableResidual_of_hom,he]

omit [Finite X] [Finite F] [CharP F 2] in
private theorem linear_borel_preimage {M C : Subgroup X}
    (e : sourceImage M C ≃* PSL(3,F))
    (he : (componentOverlap M C).map e.toMonoidHom = borel F) :
    (borel F).comap (Prime.linearComponentProjection M C e) = M.subgroupOf C := by
  ext x
  let z : sourceImage M C := ⟨QuotientGroup.mk' (sourceKernel M) x.val,x.val,x.property,rfl⟩
  change e z ∈ borel F ↔ _
  rw [←he,mem_map_equiv,e.symm_apply_apply]
  change QuotientGroup.mk' (sourceKernel M) x.val ∈ sourceImage M (M ⊓ C) ↔ x.val ∈ M
  constructor
  · rintro ⟨m,hm,hmx⟩
    have hdM := M.normalCore_le (QuotientGroup.eq_iff_div_mem.mp hmx)
    have hh := M.mul_mem (M.inv_mem hdM) hm.1
    simpa only [div_eq_mul_inv,mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel,mul_one] using hh
  · intro hx
    exact ⟨x.val,⟨hx,x.property⟩,rfl⟩

variable {G : Type*} [Group G] [Finite G]

omit [CharP F 2] in
/-- The left odd Cartan fixes each literal linear parabolic residual. -/
theorem linear_source_cartan_normalizes
    {T : Sylow 2 G} {L H A B : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H) (c : CartanPair T L H A B)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    {C : Subgroup H} (hC : C.IsCComponent)
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    (e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* PSL(3,F))
    (he : (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
      e.toMonoidHom = borel F) (i : Bool) :
    A ≤ normalizer (((Prime.linearSourceFactor
      ((normalizer (L : Set G)).subgroupOf H) C e i).map H.subtype) : Set G) := by
  let M := (normalizer (L : Set G)).subgroupOf H
  let K := C.map H.subtype
  let j : C →* G := H.subtype.comp C.subtype
  let k : C ≃* K := C.equivMapOfInjective H.subtype H.subtype_injective
  have hCK : K = residual H := congrArg (map H.subtype)
    (DiagramHall.single_component_eq_twoResidual (T.subtype hTH) hC hc).symm
  have hAK : A ≤ normalizer (K : Set G) := hCK ▸ c.left_le.trans hN
  let a : A →* MulAut C := (MulAut.congr k.symm).toMonoidHom.comp
    (K.normalizerMonoidHom.comp (inclusion hAK))
  have act (d : A) : j.comp (a d).toMonoidHom = (MulAut.conj (d : G)).toMonoidHom.comp j := by
    ext x
    change j (k.symm (K.normalizerMonoidHom ⟨d,hAK d.property⟩ (k x))) = _
    have hjk (y : K) : j (k.symm y) = (y : G) :=
      congrArg Subtype.val (k.apply_symm_apply y)
    rw [hjk]
    exact normalizerMonoidHom_apply_apply_coe K ⟨d,hAK d.property⟩ (k x)
  let r := Prime.linearComponentProjection M C e
  have hr : Function.Surjective r :=
    e.surjective.comp ((QuotientGroup.mk' (sourceKernel M)).subgroupMap_surjective C)
  have hj : Function.Injective j := H.subtype_injective.comp C.subtype_injective
  have him : ((borel F).comap r).map j = normalizer (L : Set G) ⊓ K := by
    rw [linear_borel_preimage e he]
    change (M.subgroupOf C).map (H.subtype.comp C.subtype) = _
    rw [←map_map,subgroupOf_map_subtype,Subgroup.map_inf _ _ _ H.subtype_injective,
      subgroupOf_map_subtype]
    exact inf_assoc _ _ _ |>.trans (congrArg (fun Q : Subgroup G => normalizer (L : Set G) ⊓ Q)
      (inf_eq_right.mpr (map_subtype_le C)))
  have hAM : A ≤ normalizer (normalizer (L : Set G) : Set G) :=
    ((c.left_le.trans inf_le_left).trans L.le_normalizer).trans
      (normalizer (L : Set G)).le_normalizer
  have hAI := (le_inf hAM hAK).trans inf_normalizer_le_normalizer_inf
  have ha (d : A) : ((borel F).comap r).map (a d).toMonoidHom = (borel F).comap r := by
    apply map_injective hj
    rw [map_map,act,←map_map,him]
    exact mem_normalizer_iff_map_conj_eq.mp (hAI d.property)
  have ho : Odd (Nat.card A) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
    exact OddHall.odd_hall_odd c.left_hall
  intro d hd
  have hh := congrArg (map j) (odd_preserves_linear_factors r hr a ho ha i ⟨d,hd⟩)
  rw [map_map,act,←map_map] at hh
  apply mem_normalizer_iff_map_conj_eq.mpr
  change ((Prime.linearSourceFactor M C e i).map H.subtype).map
    (MulAut.conj d).toMonoidHom = (Prime.linearSourceFactor M C e i).map H.subtype
  simpa only [Prime.linearSourceFactor,map_map,j,r,M,MonoidHom.comp_assoc] using hh

omit [CharP F 2] in
private theorem linear_factor_sylow_normalizer_le
    (r : X →* PSL(3,F)) (hr : Function.Surjective r)
    {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2 ^ f) (hlarge : 4 ≤ Nat.card F)
    (j : X →* G) (hj : Function.Injective j) (M : Subgroup G)
    (hmark : (borel F).comap r = M.comap j) (i : Bool)
    (P : Sylow 2 ((CoveredLocals.factor r i).map j))
    (hP : (P : Subgroup _).map ((CoveredLocals.factor r i).map j).subtype ≤ M) :
    (normalizer (P : Set _)).map ((CoveredLocals.factor r i).map j).subtype ≤ M := by
  let R0 := CoveredLocals.factor r i
  let R := R0.map j
  let D := CoveredLocals.localProjective F i
  let e : R0 ≃* R := R0.equivMapOfInjective j hj
  let v : R0 →* D := (MulEquiv.subgroupCongr (CoveredLocals.factor_image hlarge r hr i)).toMonoidHom.comp
    (r.subgroupMap R0)
  have hv : Function.Surjective v :=
    (MulEquiv.subgroupCongr (CoveredLocals.factor_image hlarge r hr i)).surjective.comp
      (r.subgroupMap_surjective R0)
  let q : R →* D := v.comp e.symm.toMonoidHom
  have hq : Function.Surjective q := hv.comp e.symm.surjective
  have hUD : unipotent F ≤ D := by
    cases i
    · exact unipotent_le_lineLocal F
    · exact unipotent_le_pointLocal F
  let U := (unipotentSylow F hf hF).subtype hUD
  have hUN : normalizer (U : Set D) = (borel F).subgroupOf D := by
    change normalizer ((unipotent F).subgroupOf D : Set D) = _
    rw [←subgroupOf_normalizer_eq hUD,normalizer_unipotent F hf hF]
  have hm (x : R) : q x ∈ (borel F).subgroupOf D ↔ (x : G) ∈ M := by
    change r (e.symm x).val ∈ borel F ↔ _
    change (e.symm x).val ∈ (borel F).comap r ↔ _
    rw [hmark]
    change j (e.symm x).val ∈ M ↔ _
    have hx : j (e.symm x).val = (x : G) := congrArg Subtype.val (e.apply_symm_apply x)
    rw [hx]
  let Q := P.mapSurjective hq
  have hQN : (Q : Subgroup D) ≤ normalizer (U : Set D) := by
    rw [hUN]
    rintro _ ⟨x,hx,rfl⟩
    exact (hm x).mpr (hP (mem_map_of_mem R.subtype hx))
  have hQU : (Q : Subgroup D) ≤ U := by
    have hh := Q.isPGroup'.inf_normalizer_sylow U
    rw [inf_eq_left.mpr hQN] at hh
    exact hh.le.trans inf_le_right
  have hQUeq : Q = U := Sylow.ext (Q.is_maximal' U.isPGroup' hQU).symm
  rintro _ ⟨x,hx,rfl⟩
  apply (hm x).mp
  rw [←hUN,←hQUeq]
  exact (le_normalizer_map q) (mem_map_of_mem q hx)

omit [CharP F 2] in
/-- The linear factor's Borel is exactly its overlap with N_G(L). The
Sylow is the original S-intersection, not a subsequently conjugated choice. -/
theorem linear_source_factor_borel
    {L H : Subgroup G} {C : Subgroup H} {f : ℕ}
    (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* PSL(3,F))
    (he : (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
      e.toMonoidHom = borel F) (i : Bool)
    (hP : ∃ P : Sylow 2 ((Prime.linearSourceFactor
        ((normalizer (L : Set G)).subgroupOf H) C e i).map H.subtype),
      (P : Subgroup _).map ((Prime.linearSourceFactor
        ((normalizer (L : Set G)).subgroupOf H) C e i).map H.subtype).subtype =
      sourceS L H ⊓ (Prime.linearSourceFactor
        ((normalizer (L : Set G)).subgroupOf H) C e i).map H.subtype) :
    ChapterF.Source.borel ((Prime.linearSourceFactor
      ((normalizer (L : Set G)).subgroupOf H) C e i).map H.subtype) (sourceS L H) =
      normalizer (L : Set G) ⊓ (Prime.linearSourceFactor
        ((normalizer (L : Set G)).subgroupOf H) C e i).map H.subtype := by
  let M := (normalizer (L : Set G)).subgroupOf H
  let R := (Prime.linearSourceFactor M C e i).map H.subtype
  let j : C →* G := H.subtype.comp C.subtype
  let r := Prime.linearComponentProjection M C e
  have hR : R = (CoveredLocals.factor r i).map j := by
    exact map_map _ _ _
  have hr : Function.Surjective r :=
    e.surjective.comp ((QuotientGroup.mk' (sourceKernel M)).subgroupMap_surjective C)
  have hj : Function.Injective j := H.subtype_injective.comp C.subtype_injective
  have hmark : (borel F).comap r = (normalizer (L : Set G)).comap j :=
    linear_borel_preimage e he
  have hlarge : 4 ≤ Nat.card F := by
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ f by omega)
    omega
  obtain ⟨P,hP⟩ := hP
  have hpeq : (P : Subgroup R) = (sourceS L H ⊓ R).subgroupOf R := by
    apply map_injective R.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le inf_le_right]
  have hb : (normalizer (P : Set R)).map R.subtype = ChapterF.Source.borel R (sourceS L H) := by
    change (normalizer ((P : Subgroup R) : Set R)).map R.subtype = _
    rw [hpeq,←subgroupOf_normalizer_eq inf_le_right,subgroupOf_map_subtype,inf_comm]
    rfl
  have hPN : (P : Subgroup R).map R.subtype ≤ normalizer (L : Set G) := by
    rw [hP]
    exact inf_le_left.trans ((pCoreIn_le 2 (intersection L H)).trans inf_le_left)
  have hBN : ChapterF.Source.borel R (sourceS L H) ≤ normalizer (L : Set G) := by
    rw [←hb]
    have hh := linear_factor_sylow_normalizer_le r hr (by omega : 0 < f) hF hlarge
      j hj (normalizer (L : Set G)) hmark i
    rw [←hR] at hh
    exact hh P hPN
  apply le_antisymm (le_inf hBN inf_le_left)
  apply le_inf inf_le_right
  apply le_trans _ inf_normalizer_le_normalizer_inf
  exact le_inf ((le_inf inf_le_left (inf_le_right.trans (map_subtype_le _))).trans
    (intersection_normalizes_sourceS L H)) (inf_le_right.trans R.le_normalizer)

private theorem sylow_in_normalized_subfactor
    (T : Sylow 2 G) {K R : Subgroup G} (hRK : R ≤ K)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hTR : (T : Subgroup G) ⊓ K ≤ normalizer (R : Set G)) :
    ∃ P : Sylow 2 R, (P : Subgroup R).map R.subtype = (T : Subgroup G) ⊓ R := by
  obtain ⟨S,hS⟩ := exists_sylow_component hTK
  let I := R ⊔ ((T : Subgroup G) ⊓ K)
  obtain ⟨P,hP⟩ := S.exists_map_subtype_eq_of_le
    (show I ≤ K from sup_le hRK inf_le_right) (hS ▸ le_sup_right)
  obtain ⟨Q,hQ⟩ := P.exists_map_subtype_eq_inf_of_normalizes
    (show R ≤ I from le_sup_left) (sup_le R.le_normalizer hTR)
  exact ⟨Q,by rw [hQ,hP,hS,inf_assoc,inf_eq_right.mpr hRK]⟩

/-- Both canonical linear factors have the exact Cartan and Borel geometry.
Only the separate source S-action is absent from the RightFactor contract. -/
theorem linear_source_factor_geometry
    {T : Sylow 2 G} {L H A B : Subgroup G} {f : ℕ}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H)) (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* PSL(3,F))
    (he : (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
      e.toMonoidHom = borel F)
    (hmove : MovesDiagram ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) e (pointParabolic F) (lineParabolic F)) (i : Bool) :
    let R := (Prime.linearSourceFactor ((normalizer (L : Set G)).subgroupOf H) C e i).map H.subtype
    R ≤ residual H ∧ ¬ R ≤ normalizer (L : Set G) ∧ R ⊔ (T : Subgroup G) = H ∧
      ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ f) ∧
      (∃ P : Sylow 2 R, (P : Subgroup R).map R.subtype = sourceS L H ⊓ R) ∧
      A ≤ normalizer (R : Set G) ∧ B ≤ normalizer (R : Set G) ∧
      ChapterF.Source.borel R (sourceS L H) = normalizer (L : Set G) ⊓ R ∧
      ChapterF.Source.borel R (sourceS L H) = (sourceS L H ⊓ R) ⊔ (B ⊓ R) := by
  let M := (normalizer (L : Set G)).subgroupOf H
  let R0 := Prime.linearSourceFactor M C e i
  let R := R0.map H.subtype
  have hO : pCore 2 H ≤ sourceKernel M := normal_le_normalCore.mpr
    ((pCore_isPGroup.le_sylow_of_normal (T.subtype hH.1.1.2)).trans (comap_mono hTL))
  have hCK : C = pResidual 2 H := (DiagramHall.single_component_eq_twoResidual
    (T.subtype hH.1.1.2) hC hc).symm
  obtain ⟨hRC,hout,_,⟨eq0⟩,_,hn0⟩ := Prime.linear_source_factor_spec hC hqs hO hf hF e he i
  have hRK : R ≤ residual H := map_mono (hRC.trans_eq hCK)
  have hRH : R ≤ H := map_subtype_le _
  have hnot : ¬ R ≤ normalizer (L : Set G) := fun hh => hout (map_le_iff_le_comap.mp hh)
  let er := R0.equivMapOfInjective H.subtype H.subtype_injective
  let eqr := QuotientGroup.congr _ _ er (pCore_map_iso 2 er)
  have hmodel : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ f) :=
    ⟨F,inferInstance,inferInstance,hF,⟨eqr.symm.trans eq0⟩⟩
  have hn : normalizer (L : Set G) ⊓ residual H ≤ normalizer (R : Set G) := by
    have hh := (map_mono (f := H.subtype) hn0).trans (le_normalizer_map H.subtype)
    have heC : C.map H.subtype = residual H := congrArg (map H.subtype) hCK
    rw [Subgroup.map_inf _ _ _ H.subtype_injective,heC,subgroupOf_map_subtype] at hh
    exact le_trans (by
      intro x hx
      exact ⟨⟨hx.1,(map_subtype_le (pResidual 2 H)) hx.2⟩,hx.2⟩) hh
  have hBn : B ≤ normalizer (R : Set G) :=
    (le_inf (c.right_le.trans inf_le_left) (right_cartan_le_residual c)).trans hn
  obtain ⟨P,hP⟩ := sylow_in_normalized_subfactor T hRK
    (hH.1.1.2.trans (le_normalizer_residual H)) ((inf_le_inf_right _ hTL).trans hn)
  have hSK := Prime.diagram_sourceS_intersection_residual hTL hH hpar hC hc hf
    (Or.inl ⟨F,inferInstance,inferInstance,inferInstance,by omega,hF,e,he,hmove⟩)
  have hSR : sourceS L H ⊓ R = (T : Subgroup G) ⊓ R := by
    calc
      _ = (sourceS L H ⊓ residual H) ⊓ R := by rw [inf_assoc,inf_eq_right.mpr hRK]
      _ = _ := by rw [hSK,inf_assoc,inf_eq_right.mpr hRK]
  have hPS : (P : Subgroup R).map R.subtype = sourceS L H ⊓ R := hP.trans hSR.symm
  have hb := linear_source_factor_borel hf hF e he i ⟨P,hPS⟩
  refine ⟨hRK,hnot,?_,hmodel,⟨P,hPS⟩,
    linear_source_cartan_normalizes hH.1.1.2 c hN hC hc e he i,hBn,hb,?_⟩
  · apply le_antisymm (sup_le hRH hH.1.1.2)
    by_contra hh
    have hlt : R ⊔ (T : Subgroup G) < H :=
      lt_of_le_of_ne (sup_le hRH hH.1.1.2) (fun he => hh he.ge)
    exact hnot (le_sup_left.trans (Chapter3.HStar.proper_overgroup_le T hH le_sup_right hlt))
  · let U := normalizer (L : Set G) ⊓ R
    have hU : U ≤ intersection L H := le_inf inf_le_left (inf_le_right.trans hRH)
    have hBU : B ≤ normalizer (U : Set G) :=
      (le_inf ((c.right_le.trans inf_le_left).trans (normalizer (L : Set G)).le_normalizer)
        hBn).trans inf_normalizer_le_normalizer_inf
    have hh := OddHall.hall_restrict_of_normalizes c.right_hall c.right_le hU hBU
    obtain ⟨Q,hQ⟩ := P.exists_map_subtype_eq_of_le (show U ≤ R from inf_le_right)
      (hP ▸ le_inf (inf_le_left.trans hTL) inf_le_right)
    have heq := congrArg (map U.subtype) (OddHall.sylow_complement_of_hall Q hh).sup_eq_top
    have hi : B ⊓ U = B ⊓ R := by
      dsimp [U]
      rw [←inf_assoc,inf_eq_left.mpr (c.right_le.trans inf_le_left)]
    rw [Subgroup.map_sup,hQ,hPS,subgroupOf_map_subtype,hi,
      ←MonoidHom.range_eq_map,range_subtype] at heq
    exact hb.trans heq.symm

/-- Source 5.2.1's whole-factor S-action completes the marked linear right
factor; all Cartan and exact-overlap clauses are proved above. -/
theorem linear_source_rightFactor_of_sourceS
    {T : Sylow 2 G} {L H A B : Subgroup G} {f : ℕ}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H)) (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* PSL(3,F))
    (he : (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
      e.toMonoidHom = borel F)
    (hmove : MovesDiagram ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) e (pointParabolic F) (lineParabolic F)) (i : Bool)
    (hS : sourceS L H ≤ normalizer (((Prime.linearSourceFactor
      ((normalizer (L : Set G)).subgroupOf H) C e i).map H.subtype) : Set G)) :
    RightFactor T L H A B ((Prime.linearSourceFactor
      ((normalizer (L : Set G)).subgroupOf H) C e i).map H.subtype) := by
  obtain ⟨hRK,hout,_,hmodel,hSyl,hA,_,_,hb⟩ :=
    linear_source_factor_geometry hTL hH hpar c hN hC hqs hc hf hF e he hmove i
  exact ⟨hRK,hout,hSyl,.linear f (by omega) hmodel,hS,hA,hb⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

