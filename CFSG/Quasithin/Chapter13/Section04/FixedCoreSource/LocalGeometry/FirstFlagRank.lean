module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.CoveredPlacement
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.AugmentationCoveredComparison

/-!
# The original first action core in both augmentation rows

The action of M₁=N_LT(V₁) on the original five-dimensional module has the
same kernel as its six-letter permutation action. Transporting the two-core
of its actual image therefore puts R₁ inside the correct point radical,
without removing the central three in the covered row. The Sylow kernel
identity gives C_R₁(V)=O₂(LT). The absence of strong offenders on the
augmentation point radical then proves m₂(R₁)=m₂(O₂(LT)) and V≤J(R₁).

FirstFlagSmallImages applies this literal kernel to the source Baumann
alternative. R₁ is never identified with O₂(L₁T) in the covered row.
The earlier structural input remains explicit, as required by the existing
firstFlagCore definition; no universal record is constructed from At data.
Source: Aschbacher--Smith Notation 13.2.1 and 13.2.2(6), p.877,
using B.2.4(3) and B.3.4, pp.75--76,84--85.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Solvable Nonsolvable
open ChapterB.BaumannArgument
open Section08.TransvectionRecognition.Component.ModelExtension
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem actionCore_image_le
    {P A B : Type*} [Group P] [Group A] [Group B]
    (f : P →* A) (g : P →* B) (h : f.ker = g.ker)
    {x : P} (hx : f.rangeRestrict x ∈ pCore 2 f.range) :
    g x ∈ g.range.pCoreIn 2 := by
  let e : f.range ≃* g.range := (QuotientGroup.quotientKerEquivRange f).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq h).trans
      (QuotientGroup.quotientKerEquivRange g))
  have hfx : (QuotientGroup.quotientKerEquivRange f).symm (f.rangeRestrict x) =
      QuotientGroup.mk x := by
    apply (QuotientGroup.quotientKerEquivRange f).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  have he : e (f.rangeRestrict x) = g.rangeRestrict x := by
    change QuotientGroup.quotientKerEquivRange g
      (QuotientGroup.quotientMulEquivOfEq h
        ((QuotientGroup.quotientKerEquivRange f).symm (f.rangeRestrict x))) = _
    rw [hfx,QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  have hh : g.rangeRestrict x ∈ pCore 2 g.range := by
    rw [←pCore_map_iso 2 e,←he]
    exact mem_map_of_mem e.toMonoidHom hx
  exact mem_map_of_mem g.range.subtype hh

/-- The literal source action core maps into the point radical in both
covering rows. Its central-three kernel is retained throughout. -/
theorem firstFlagCore_permutation_marking
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    let X := L ⊔ (T : Subgroup G)
    ∃ q : X →* Equiv.Perm (Fin 6),
      (∀ (x : X) (v : V),
        (m.coordinate (V.normalizerMonoidHom
          ⟨x.val,(sup_le D.normalizes ((structural G T L h).2.2 V D).1) x.property⟩ v)).toAdd =
          BinaryPermutation.coreRepresentation (Fin 6) (q x) (m.coordinate v).toAdd) ∧
      (L.subgroupOf X).map q = alternatingGroup (Fin 6) ∧
      ((firstFlagCore h structural D m).subgroupOf X).map q ≤
        (BinaryPermutation.SixCorePoint.stabilizer (m.coordinate z).toAdd ⊓ q.range).pCoreIn 2 := by
  let X := L ⊔ (T : Subgroup G)
  have hn := normalizer_component_le_module h structural D m
  obtain ⟨qN,hqN,hqNL,hker⟩ := exists_core_normalizer_permutation D m hn
  have hXN : X ≤ normalizer (L : Set G) := sup_le L.le_normalizer D.sylow_normalizes_component
  let q := qN.comp (inclusion hXN)
  have hq (x : X) (v : V) :
      (m.coordinate (V.normalizerMonoidHom
        ⟨x.val,(sup_le D.normalizes ((structural G T L h).2.2 V D).1) x.property⟩ v)).toAdd =
        BinaryPermutation.coreRepresentation (Fin 6) (q x) (m.coordinate v).toAdd :=
    hqN (inclusion hXN x) v
  have hqL (l : L) : q (inclusion (show L ≤ X from le_sup_left) l) =
      (m.quotient (QuotientGroup.mk' (centralCore L) l)).val := hqNL l
  have him : (L.subgroupOf X).map q = alternatingGroup (Fin 6) := by
    apply le_antisymm
    · rintro a ⟨x,hx,rfl⟩
      have hh := hqL ⟨x.val,hx⟩
      change q x = _ at hh
      rw [hh]
      exact (m.quotient (QuotientGroup.mk' (centralCore L) ⟨x.val,hx⟩)).property
    · intro a ha
      obtain ⟨w,hw⟩ := m.quotient.surjective ⟨a,ha⟩
      obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (centralCore L) w
      exact ⟨inclusion le_sup_left l,l.property,(hqL l).trans (congrArg Subtype.val hw)⟩
  refine ⟨q,hq,him,?_⟩
  let P := firstFlagNormalizer T L V
  have hPX : P ≤ X := inf_le_left
  let f := firstFlagAction h structural D m
  let g := q.comp (inclusion hPX)
  have hfg : f.ker = g.ker := by
    ext p
    change f p = 1 ↔ g p = 1
    constructor
    · intro hp
      apply BinaryPermutation.SixCoreNormalizer.action_injective
      apply LinearMap.ext
      intro w
      obtain ⟨v,rfl⟩ := m.coordinate.surjective (Multiplicative.ofAdd w)
      have he := hq (inclusion hPX p) v
      change (m.coordinate (f p v)).toAdd =
        BinaryPermutation.coreRepresentation (Fin 6) (g p) (m.coordinate v).toAdd at he
      rw [hp] at he
      change (m.coordinate v).toAdd =
        BinaryPermutation.coreRepresentation (Fin 6) (g p) (m.coordinate v).toAdd at he
      change BinaryPermutation.coreRepresentation (Fin 6) (g p) (m.coordinate v).toAdd =
        (m.coordinate v).toAdd
      exact he.symm
    · intro hp
      apply MulEquiv.ext
      intro v
      apply m.coordinate.injective
      apply Multiplicative.toAdd.injective
      have he := hq (inclusion hPX p) v
      change _ = BinaryPermutation.coreRepresentation (Fin 6) (g p) _ at he
      rw [hp,map_one,Module.End.one_apply] at he
      exact he
  have hPr : g.range =
      BinaryPermutation.SixCorePoint.stabilizer (m.coordinate z).toAdd ⊓ q.range := by
    have hP := first_flag_normalizer_eq_centralizer h structural D m z hz hzL
    change P = X ⊓ centralizer ({z.val} : Set G) at hP
    let U := V.subgroupOf X
    have hVX : V ≤ X := D.le_sylow.trans le_sup_right
    let : U.Normal := normal_subgroupOf_of_le_normalizer
      (sup_le D.normalizes ((structural G T L h).2.2 V D).1)
    let eu : U ≃* V := subgroupOfEquivOfLe hVX
    let e := eu.trans m.coordinate
    let zi := eu.symm z
    have he (x : X) (v : U) : (e (MulAut.conjNormal x v)).toAdd =
        BinaryPermutation.coreRepresentation (Fin 6) (q x) (e v).toAdd := hq x (eu v)
    have hg : g.range = (centralizer ({zi.val} : Set X)).map q := by
      apply le_antisymm
      · rintro a ⟨p,rfl⟩
        refine ⟨inclusion hPX p,?_,rfl⟩
        apply mem_centralizer_singleton_iff.mpr
        exact Subtype.ext (mem_centralizer_singleton_iff.mp ((hP.le p.property).2))
      · rintro a ⟨x,hx,rfl⟩
        have hxp : x.val ∈ P := hP.symm ▸ ⟨x.property,
          mem_centralizer_singleton_iff.mpr
            (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx))⟩
        exact ⟨⟨x.val,hxp⟩,rfl⟩
    rw [hg,ChapterB.Offenders.SixCorePoint.point_image U q e he zi]
    rfl
  rintro a ⟨x,hx,rfl⟩
  obtain ⟨t,ht,htx⟩ := hx
  have hxv : t.val = x.val := htx
  let p : P := ⟨t.val,sylow_le_firstFlagNormalizer t.property⟩
  have hh : g p ∈ g.range.pCoreIn 2 := actionCore_image_le f g hfg ht
  have hqeq : g p = q x := congrArg q (Subtype.ext hxv)
  rw [hqeq,hPr] at hh
  exact hh

/-- O₂(LT) is contained in the original R₁, whose module centralizer is
exactly O₂(LT), even when L/O₂(L) is covered. -/
theorem firstFlagCore_kernel
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ firstFlagCore h structural D m ∧
      firstFlagCore h structural D m ⊓ centralizer (V : Set G) =
        (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hc := RecognitionSource.chosen_sylow_centralizer_eq_core h D structural
  have hQR : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ firstFlagCore h structural D m := by
    intro x hx
    have hxT := (hc.symm ▸ hx).1
    refine ⟨⟨x,hxT⟩,?_,rfl⟩
    have hf : firstFlagAction h structural D m ⟨x,sylow_le_firstFlagNormalizer hxT⟩ = 1 := by
      apply MulEquiv.ext
      intro v
      apply Subtype.ext
      change x * v.val * x⁻¹ = v.val
      have hxc : x ∈ centralizer (V : Set G) := (hc.symm ▸ hx).2
      rw [←hxc v.val v.property,mul_inv_cancel_right]
    change (firstFlagAction h structural D m).rangeRestrict
      ⟨x,sylow_le_firstFlagNormalizer hxT⟩ ∈ pCore 2 _
    have he : (firstFlagAction h structural D m).rangeRestrict
        ⟨x,sylow_le_firstFlagNormalizer hxT⟩ = 1 := Subtype.ext hf
    rw [he]
    exact one_mem _
  refine ⟨hQR,le_antisymm ?_ ?_⟩
  · exact (inf_le_inf_right _ (map_subtype_le _)).trans hc.le
  · exact le_inf hQR D.core_centralizes


private def coreCoordinates {H : Type*} [Group H] (U : Subgroup H)
    [IsElementaryAbelian 2 U]
    (e : U ≃* Multiplicative (BinaryPermutation.core (Fin 6))) :
    Additive U ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 6) := by
  let a : Additive U ≃+ BinaryPermutation.core (Fin 6) := {
    toFun := fun v => (e v.toMul).toAdd
    invFun := fun w => Additive.ofMul (e.symm (Multiplicative.ofAdd w))
    left_inv := fun v => e.symm_apply_apply v
    right_inv := fun w => e.apply_symm_apply (Multiplicative.ofAdd w)
    map_add' := fun v w => e.map_mul v.toMul w.toMul }
  exact { a with map_smul' := ZMod.map_smul a }

private theorem noStrong_of_point_image
    {H : Type*} [Group H] [Finite H]
    (U R : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (q : H →* Equiv.Perm (Fin 6))
    (e : U ≃* Multiplicative (BinaryPermutation.core (Fin 6)))
    (he : ∀ g v, (e (MulAut.conjNormal g v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 6) (q g) (e v).toAdd)
    (hY : alternatingGroup (Fin 6) ≤ q.range)
    (z : U)
    (hz : ¬ ∀ a : alternatingGroup (Fin 6),
      BinaryPermutation.alternatingCoreRepresentation (Fin 6) a (e z).toAdd = (e z).toAdd)
    (hR : R.map q ≤
      (BinaryPermutation.SixCorePoint.stabilizer (e z).toAdd ⊓ q.range).pCoreIn 2) :
    NoStrongOffenders U R := by
  let rho := BinaryPermutation.coreRepresentation (Fin 6)
  have hker := ChapterB.Offenders.SixCorePoint.kernel_centralizer U q e he
  let q0 := q.rangeRestrict
  have hq0 := q.rangeRestrict_surjective
  have hk0 : q0.ker = centralizer (U : Set H) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  let r := Representation.NormalElementaryQuotient.representation U q0 hq0 hk0
  have heq (a : q.range) (v : Additive U) :
      coreCoordinates U e (r a v) = rho a.val (coreCoordinates U e v) := by
    obtain ⟨a,rfl⟩ := hq0 a
    have h := Representation.NormalElementaryQuotient.representation_apply U q0 hq0 hk0 a v
    have hh : (r (q0 a) v).toMul = MulAut.conjNormal a v.toMul := Subtype.ext h
    change (e _).toAdd = rho (q a) (e v.toMul).toAdd
    rw [hh]
    exact he a v.toMul
  have hcod (A : Subgroup H) : fixedCodim U A =
      Representation.BinaryOffender.fixedCodim rho (A.map q) := by
    rw [fixedCodim_eq_centralizer_quotient U q0 hq0 hk0]
    have hh := Representation.BinaryOffender.fixedCodim_map_equivariant r rho q.range.subtype
      (coreCoordinates U e) heq (A.map q0)
    rw [map_map] at hh
    exact hh
  intro A hA heA hne
  let k := QuotientGroup.lift (centralizer (U : Set H)) q hker.symm.le
  have hmap : (A.map (actionMap U)).map k = A.map q := by
    rw [map_map]
    rfl
  have hAq : IsElementaryAbelian 2 (A.map q) := hmap ▸ heA.map k
  have hneq : A.map q ≠ ⊥ := by
    intro hh
    apply hne
    apply (map_eq_bot_iff A).mpr
    rw [actionMap_ker,←hker]
    exact (map_eq_bot_iff A).mp hh
  have hc : Nat.card (A.map (actionMap U)) = Nat.card (A.map q) := by
    rw [←relIndex_ker,←relIndex_ker,actionMap_ker,hker]
  rw [hc,hcod]
  apply Nat.le_of_not_gt
  intro hlt
  apply ChapterB.Offenders.SixCorePoint.model_no_strong q.range hY (e z).toAdd hz
    ((map_mono hA).trans hR)
  exact ⟨⟨hneq,hAq⟩,hlt⟩

/-- Source 13.2.2(6) on the original action core, including the triple-cover
row: its two-rank equals that of O₂(LT), and V lies in J(R₁). -/
theorem firstFlagCore_rank_and_module
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) :
    ChapterB.twoRank (firstFlagCore h structural D m) =
        ChapterB.twoRank ((L ⊔ (T : Subgroup G)).pCoreIn 2) ∧
      V ≤ elementaryAbelianMaxJ (firstFlagCore h structural D m) := by
  let X := L ⊔ (T : Subgroup G)
  let R := firstFlagCore h structural D m
  let U := V.subgroupOf X
  let Ri := R.subgroupOf X
  have hVX : V ≤ X := D.le_sylow.trans le_sup_right
  have hRT : R ≤ T := map_subtype_le _
  have hRX : R ≤ X := hRT.trans le_sup_right
  let : U.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le D.normalizes ((structural G T L h).2.2 V D).1)
  let := D.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hVX
  let eu : U ≃* V := subgroupOfEquivOfLe hVX
  let e := eu.trans m.coordinate
  let zi := eu.symm z
  obtain ⟨q,hq,him,hR⟩ := firstFlagCore_permutation_marking h structural D m z hz hzL
  have he (x : X) (v : U) : (e (MulAut.conjNormal x v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 6) (q x) (e v).toAdd := hq x (eu v)
  have hY : alternatingGroup (Fin 6) ≤ q.range := him ▸ map_le_range q (L.subgroupOf X)
  have hz' : ¬ ∀ a : alternatingGroup (Fin 6),
      BinaryPermutation.alternatingCoreRepresentation (Fin 6) a (e zi).toAdd = (e zi).toAdd := by
    intro ha
    apply hzL
    apply (m.mem_fixed_iff z).mpr
    apply (BinaryPermutation.core_fixed_iff_constant (by simp) _).mp
    change ∀ a : alternatingGroup (Fin 6),
      BinaryPermutation.coreRepresentation (Fin 6) a.val (e zi).toAdd = (e zi).toAdd at ha
    simpa only [e,zi,MulEquiv.trans_apply,eu.apply_symm_apply] using ha
  have hno := noStrong_of_point_image U Ri q e he hY zi hz' hR
  obtain ⟨hQR,hRC⟩ := firstFlagCore_kernel h structural D m
  have hVR : U ≤ Ri := comap_mono (D.le_core.trans hQR)
  have hcore : Ri ⊓ centralizer (U : Set X) = pCore 2 X := by
    apply map_injective X.subtype_injective
    rw [←map_inf_centralizer_of_injective X.subtype X.subtype_injective,
      map_subgroupOf_eq_of_le hRX,map_subgroupOf_eq_of_le hVX]
    exact hRC
  have hh := centralizer_rank_and_alpha U Ri hVR hno
  rw [hcore] at hh
  have hmodule : U ≤ elementaryAbelianMaxJ Ri := by
    have hUJ : U ≤ elementaryAbelianMaxJ (pCore 2 X) := by
      intro v hv
      exact ((mem_omegaOneCenterAmbient_iff _ _).mp (hh.2.2.1 hv)).1
    exact hUJ.trans (sSup_le fun A hA => le_sSup (hh.2.1 hA))
  have hRm : Ri.map X.subtype = R := map_subgroupOf_eq_of_le hRX
  constructor
  · have hr := ChapterB.twoRank_map_injective X.subtype X.subtype_injective Ri
    have hq := ChapterB.twoRank_map_injective X.subtype X.subtype_injective (pCore 2 X)
    rw [hRm] at hr
    exact hr.trans (hh.1.symm.trans hq.symm)
  · have hm := map_mono (f := X.subtype) hmodule
    rw [map_subgroupOf_eq_of_le hVX,←elementaryAbelianMaxJ_map_injective X.subtype
      X.subtype_injective,hRm] at hm
    exact hm


end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
