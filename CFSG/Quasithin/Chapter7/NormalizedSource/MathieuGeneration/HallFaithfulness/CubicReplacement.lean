module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.CubicFixedSeed
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.GroupTheory.SolvableResidual.TwoSupplement

/-!
# The concrete subgroup for the exceptional cubic replacement

For a cubic in the actual J4 model, take the preimage of the triple cover
inside the first involution centralizer and transport it by cubic fusion.
Its solvable residual is the entire involution-centralizer residual, and
the cubic lies in the kernel of its quotient onto M22.

Lift this construction through the original component's simple-section
projection. Taking the solvable residual of the preimage preserves the
original perfect seed and the exact native residual image. The odd actor
acts trivially on the lifted subgroup modulo its two-core: its action on
the M22 quotient is trivial, and the solvable kernel maps into the center
of the quasisimple two-core quotient. Every ambient element whose induced
J4 automorphism fixes the selected native involution normalizes the lifted
replacement; this follows from characteristic residuality in the preimage.

The literal Hall application retains the original covering components,
involution centralizer, seed inclusion and quotient action. It constructs
the subgroup needed for the exceptional cubic branch on printed p.623.
Compatibility with the original T still has to be proved to obtain the
source's T-normalized I_Z; this module does not assert that compatibility.
The M12/M22 pushing-up branches and the final Mathieu seed generation
comparison also remain obligations of SourceMathieuHallFaithfulAt.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 4.4.3,
printed p.623, and its application in 4.4.14, printed pp.624--625. The
native J4 and Mathieu certificates retain their imported attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Sporadic.Mathieu Janko4.InvolutionCentralizers
open First.QuotientExtension
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem scalar_replacement
    (x : First.centralizer) (hx : orderOf x = 3)
    (hs : First.centralizerExtension.rightHom x = scalarElement)
    (hJ : IsSQTK KnownSimple.IsKnownSimple Janko4.Model) :
    ∃ I : Subgroup Janko4.Model,
      (solvableResidual (centralizer ({(x : Janko4.Model)} : Set Janko4.Model))).map
        (centralizer ({(x : Janko4.Model)} : Set Janko4.Model)).subtype ≤ I ∧
      ∃ hxI : (x : Janko4.Model) ∈ I,
        ∃ f : I →* M22, Function.Surjective f ∧ Group.IsSolvable f.ker ∧
          f ⟨x,hxI⟩ = 1 ∧
          I ≤ centralizer ({Janko4.a} : Set Janko4.Model) ∧
          centralizer ({Janko4.a} : Set Janko4.Model) ≤ normalizer (I : Set Janko4.Model) ∧
          (solvableResidual I).map I.subtype =
            (solvableResidual First.centralizer).map First.centralizer.subtype := by
  let I := H.map First.centralizer.subtype
  let e : H ≃* I := H.equivMapOfInjective First.centralizer.subtype
    First.centralizer.subtype_injective
  let q := M22TripleCover.centralQuotientEquiv.toMonoidHom.comp
    (QuotientGroup.mk' (center M22TripleCover))
  let f := (q.comp coverProjection).comp e.symm.toMonoidHom
  have hf : Function.Surjective f :=
    (M22TripleCover.centralQuotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _)).comp
      (coverProjection_surjective.comp e.symm.surjective)
  have hxH : x ∈ H := by
    change First.centralizerExtension.rightHom x ∈ coverSubgroup
    rw [hs,←coverInclusion_range]
    exact ⟨M22TripleCover.scalar,rfl⟩
  have hxI : (x : Janko4.Model) ∈ I := mem_map_of_mem _ hxH
  have he : e.symm ⟨x,hxI⟩ = ⟨x,hxH⟩ := by
    apply e.injective
    exact e.apply_symm_apply _
  have hsc : coverProjection ⟨x,hxH⟩ = M22TripleCover.scalar := by
    apply inclusion_injective
    exact (coverProjection_inclusion _).trans hs
  have hk : Group.IsSolvable coverProjection.ker := by
    rw [coverProjection_ker]
    let : Group.IsNilpotent (Q.subgroupOf H) :=
      (pCore_isPGroup.comap_subtype (p := 2) (G := First.centralizer)).isNilpotent
    infer_instance
  let := hk
  let : Group.IsSolvable (q.comp coverProjection).ker := by
    rw [←MonoidHom.comap_ker]
    have hq : q.ker = center M22TripleCover := by
      rw [MonoidHom.ker_comp_of_injective _ _ M22TripleCover.centralQuotientEquiv.injective,
        QuotientGroup.ker_mk']
    rw [hq]
    exact isSolvable_comap_of_solvable_ker coverProjection _
  let : Group.IsSolvable e.symm.toMonoidHom.ker := by
    rw [e.symm.toMonoidHom.ker_eq_bot_iff.mpr e.symm.injective]
    infer_instance
  have hker : Group.IsSolvable f.ker := by
    rw [show f.ker = (q.comp coverProjection).ker.comap e.symm.toMonoidHom from rfl]
    exact isSolvable_comap_of_solvable_ker e.symm.toMonoidHom _
  refine ⟨I,?_,hxI,f,hf,hker,?_,map_subtype_le _,?_,?_⟩
  · rw [native_cubic_full_residual x hx hs (hJ.subgroup _)]
    rintro _ ⟨d,⟨w,hw,rfl⟩,rfl⟩
    apply mem_map_of_mem First.centralizer.subtype
    have hm := map_solvableResidual_le (centralizer ({x} : Set First.centralizer)).subtype
      (mem_map_of_mem _ hw)
    have hle : solvableResidual First.centralizer ≤ H := by
      let : Group.IsSolvable (First.centralizer ⧸ H) :=
        Group.isSolvable_of_isSolvable_injective
          (f := centralizerQuotientEquivC2.toMonoidHom) centralizerQuotientEquivC2.injective
      exact solvableResidual_le_of_solvable_quotient H
    exact hle hm
  · change q (coverProjection (e.symm ⟨x,hxI⟩)) = 1
    rw [he,hsc]
    change M22TripleCover.centralQuotientEquiv
      (QuotientGroup.mk' (center M22TripleCover) M22TripleCover.scalar) = 1
    exact (congrArg M22TripleCover.centralQuotientEquiv
      ((QuotientGroup.eq_one_iff _).mpr M22TripleCover.scalar_mem_center)).trans (map_one _)
  · simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      H.le_normalizer_map First.centralizer.subtype
  · let : Group.IsSolvable (First.centralizer ⧸ H) :=
      Group.isSolvable_of_isSolvable_injective
        (f := centralizerQuotientEquivC2.toMonoidHom) centralizerQuotientEquivC2.injective
    rw [←map_solvableResidual_eq e.toMonoidHom e.surjective,map_map]
    have hh := congrArg (map First.centralizer.subtype)
      (map_solvableResidual_eq_of_solvable_quotient H)
    rw [map_map] at hh
    exact hh

/-- The native triple-cover preimage contains the full cubic residual.
Its own residual is the full residual at the selected involution. -/
theorem cubic_replacement_model
    (hJ : IsSQTK KnownSimple.IsKnownSimple Janko4.Model)
    (y : Janko4.Model) (hy : orderOf y = 3) :
    ∃ (t : Janko4.Model) (I : Subgroup Janko4.Model), orderOf t = 2 ∧
      I ≤ centralizer ({t} : Set Janko4.Model) ∧
      centralizer ({t} : Set Janko4.Model) ≤ normalizer (I : Set Janko4.Model) ∧
      (solvableResidual (centralizer ({y} : Set Janko4.Model))).map
        (centralizer ({y} : Set Janko4.Model)).subtype ≤ I ∧
      ∃ f : I →* M22, Function.Surjective f ∧ Group.IsSolvable f.ker ∧
        zpowers y ≤ f.ker.map I.subtype ∧
        (solvableResidual I).map I.subtype =
          (solvableResidual (centralizer ({t} : Set Janko4.Model))).map
            (centralizer ({t} : Set Janko4.Model)).subtype := by
  obtain ⟨x,hx,hs⟩ := First.CubicResidual.exists_scalar_lift
  obtain ⟨J,hRJ,hxJ,g,hg,hgk,hgx,hJC,hCJ,hJres⟩ := scalar_replacement x hx hs hJ
  obtain ⟨c,hc⟩ := Janko4.LocalStructure.cubic_cyclic_fusion
    (MonoidHom.id Janko4.Model) Function.surjective_id (by simp) y
    (x : Janko4.Model) hy ((orderOf_coe x).trans hx)
  let a := MulAut.conj c
  let I := J.map a.symm.toMonoidHom
  let e : J ≃* I := a.symm.subgroupMap J
  let f := g.comp e.symm.toMonoidHom
  let t := a.symm Janko4.a
  have hC : (centralizer ({t} : Set Janko4.Model)).map a.toMonoidHom =
      centralizer ({Janko4.a} : Set Janko4.Model) := by
    rw [map_centralizer_equiv,Set.image_singleton,a.apply_symm_apply]
  have hCy : (centralizer ({y} : Set Janko4.Model)).map a.toMonoidHom =
      centralizer ({(x : Janko4.Model)} : Set Janko4.Model) := by
    rw [←centralizer_closure,←zpowers_eq_closure,map_centralizer_equiv]
    change centralizer ((zpowers y).map a.toMonoidHom : Set Janko4.Model) = _
    rw [hc,zpowers_eq_closure,centralizer_closure]
  let er := (a.subgroupMap (centralizer ({y} : Set Janko4.Model))).trans
    (MulEquiv.subgroupCongr hCy)
  have hR : ((solvableResidual (centralizer ({y} : Set Janko4.Model))).map
      (centralizer ({y} : Set Janko4.Model)).subtype).map a.toMonoidHom =
      (solvableResidual (centralizer ({(x : Janko4.Model)} : Set Janko4.Model))).map
        (centralizer ({(x : Janko4.Model)} : Set Janko4.Model)).subtype := by
    rw [←map_solvableResidual_eq er.toMonoidHom er.surjective,map_map,map_map]
    rfl
  refine ⟨t,I,(a.symm.orderOf_eq _).trans Janko4.orderOf_a,?_,?_,?_,f,
    hg.comp e.symm.surjective,?_,?_,?_⟩
  · rintro _ ⟨j,hj,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    exact (map_mul a.symm _ _).symm.trans
      ((congrArg a.symm (mem_centralizer_singleton_iff.mp (hJC hj))).trans
        (map_mul a.symm _ _))
  · intro z hz
    have hz' := hCJ (hC ▸ mem_map_of_mem a.toMonoidHom hz)
    have hh := J.le_normalizer_map a.symm.toMonoidHom
      (mem_map_of_mem a.symm.toMonoidHom hz')
    change a.symm (a z) ∈ normalizer (I : Set Janko4.Model) at hh
    rwa [a.symm_apply_apply] at hh
  · intro z hz
    have hh := hRJ (hR ▸ mem_map_of_mem a.toMonoidHom hz)
    exact ⟨a z,hh,a.symm_apply_apply z⟩
  · let := hgk
    let : Group.IsSolvable e.symm.toMonoidHom.ker := by
      rw [e.symm.toMonoidHom.ker_eq_bot_iff.mpr e.symm.injective]
      infer_instance
    exact isSolvable_comap_of_solvable_ker e.symm.toMonoidHom g.ker
  · intro z hz
    have haz : a z ∈ zpowers (x : Janko4.Model) := hc ▸ mem_map_of_mem a.toMonoidHom hz
    have hxk : (x : Janko4.Model) ∈ g.ker.map J.subtype := ⟨⟨x,hxJ⟩,hgx,rfl⟩
    obtain ⟨w,hw,hew⟩ := (zpowers_le.mpr hxk) haz
    refine ⟨e w,?_,?_⟩
    · change g (e.symm (e w)) = 1
      rwa [e.symm_apply_apply]
    · change a.symm (w : Janko4.Model) = z
      exact (congrArg a.symm hew).trans (a.symm_apply_apply z)
  · have hCt : (centralizer ({Janko4.a} : Set Janko4.Model)).map a.symm.toMonoidHom =
        centralizer ({t} : Set Janko4.Model) := by
      rw [map_centralizer_equiv,Set.image_singleton]
    let ec := (a.symm.subgroupMap (centralizer ({Janko4.a} : Set Janko4.Model))).trans
      (MulEquiv.subgroupCongr hCt)
    rw [←map_solvableResidual_eq e.toMonoidHom e.surjective,
      ←map_solvableResidual_eq ec.toMonoidHom ec.surjective,map_map,map_map]
    have hh := congrArg (map a.symm.toMonoidHom) hJres
    rw [map_map,map_map] at hh
    exact hh

open Chapter4 Chapter4.Section04.OddLocalMathieu

private theorem trivial_simpleAction_of_solvable_kernel
    {C Y : Type*} [Group C] [Group Y] [Finite C]
    (R : Subgroup C) [R.Normal] [IsQuasisimple (R ⧸ pCore 2 R)]
    (f : R →* Y) [Group.IsSolvable f.ker]
    (a : C) (ha : ∀ x : R, f (MulAut.conjNormal a x) = f x) :
    simpleAction R a = 1 := by
  let q := QuotientGroup.mk' (pCore 2 R)
  have hk : f.ker ≤ solvableRadical R := le_solvableRadical _ inferInstance inferInstance
  have hz : (solvableRadical R).map q ≤ center (R ⧸ pCore 2 R) :=
    (map_solvableRadical_le_of_surjective q (QuotientGroup.mk'_surjective _)).trans
      IsQuasisimple.solvableRadical_le_center
  ext u
  obtain ⟨v,rfl⟩ := projection_surjective R u
  rw [simpleAction_projection,MulAut.one_apply]
  apply QuotientGroup.eq.mpr
  change (q (MulAut.conjNormal a v))⁻¹ * q v ∈ center (R ⧸ pCore 2 R)
  rw [←map_inv,←map_mul]
  apply hz
  apply mem_map_of_mem q
  apply hk
  change f ((MulAut.conjNormal a v)⁻¹ * v) = 1
  rw [map_mul,map_inv,ha,inv_mul_cancel]

private theorem replacement_lift
    {C S : Type*} [Group C] [Finite C] [Group S] [Finite S]
    (hC : IsSQTK KnownSimple.IsKnownSimple C)
    (Q A : Subgroup C) [Q.Normal]
    (q : C →* S) (hq : Function.Surjective (q.comp Q.subtype))
    (hk : Group.IsSolvable (q.comp Q.subtype).ker)
    (I : Subgroup S) (f : I →* M22) (hf : Function.Surjective f)
    (hfk : Group.IsSolvable f.ker)
    (P : Subgroup Q) [Group.IsPerfect P]
    (hP : P.map (q.comp Q.subtype) ≤ I)
    (hA : A.map q ≤ f.ker.map I.subtype) :
    ∃ R : Subgroup C, P.map Q.subtype ≤ R ∧ R ≤ Q ∧
      A ≤ sectionCentralizer R ∧ Group.IsPerfect R ∧
      IsQuasisimple (R ⧸ pCore 2 R) ∧
      Nonempty ((R ⧸ solvableRadical R) ≃* M22) ∧
      (normalizer (I : Set S)).comap q ≤ normalizer (R : Set C) ∧
      R.map q = (solvableResidual I).map I.subtype := by
  let E := I.comap q
  let H := Q.subgroupOf E
  let r := (solvableResidual H).map H.subtype
  let qE := q.subgroupComap I
  let fE := f.comp qE
  let fH := fE.comp H.subtype
  let fR := fE.comp r.subtype
  have hAE : A ≤ E := by
    intro a ha
    exact (map_subtype_le f.ker) (hA (mem_map_of_mem q ha))
  have hqH : Function.Surjective (qE.comp H.subtype) := by
    intro y
    obtain ⟨x,hx⟩ := hq y
    refine ⟨⟨⟨x,?_⟩,x.property⟩,Subtype.ext hx⟩
    change q (x : C) ∈ I
    exact hx.symm ▸ y.property
  have hfH : Function.Surjective fH := hf.comp hqH
  have hkH : Group.IsSolvable (qE.comp H.subtype).ker := by
    let := hk
    let j : (qE.comp H.subtype).ker →* (q.comp Q.subtype).ker := {
      toFun x := ⟨⟨x.val.val.val,x.val.property⟩,congrArg I.subtype x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    exact Group.isSolvable_of_isSolvable_injective (f := j) (by
      intro x y he
      exact Subtype.ext (Subtype.ext (Subtype.ext
        (congrArg (fun z : (q.comp Q.subtype).ker => ((z : Q) : C)) he))))
  have hfHk : Group.IsSolvable fH.ker := by
    let := hkH
    let := hfk
    exact isSolvable_comap_of_solvable_ker (qE.comp H.subtype) f.ker
  let := hfHk
  let : IsSimpleGroup M22 := m22_isSimpleGroup
  let : Group.IsPerfect M22 := Group.IsPerfect.ofSurjective
    (f := M22TripleCover.centralQuotientEquiv.toMonoidHom.comp
      (QuotientGroup.mk' (center M22TripleCover)))
    (M22TripleCover.centralQuotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _))
  have hM : (solvableResidual M22).IsCComponent := by
    rw [solvableResidual_eq_top]
    let : IsSimpleGroup (⊤ : Subgroup M22) :=
      (topEquiv : (⊤ : Subgroup M22) ≃* M22).isSimpleGroup
    exact isCComponent_of_isSimpleGroup_of_isPerfect
      (inferInstance : (⊤ : Subgroup M22).Normal).isSubnormal
  have hr : r.IsCComponent :=
    (residual_isCComponent_of_surjective fH hfH hM).map_subtype
      (inferInstance : H.Normal).isSubnormal
  let : Group.IsPerfect r := hr.perfect
  have hfR : Function.Surjective fR := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp,range_subtype]
    change ((solvableResidual H).map H.subtype).map fE = ⊤
    rw [map_map,map_solvableResidual_eq fH hfH,solvableResidual_eq_top]
  have hfRk : Group.IsSolvable fR.ker := by
    have hle : r ≤ H := map_subtype_le _
    let j : fR.ker →* fH.ker := {
      toFun x := ⟨⟨x.val.val,hle x.val.property⟩,x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    exact Group.isSolvable_of_isSolvable_injective (f := j) (by
      intro x y he
      exact Subtype.ext (Subtype.ext
        (congrArg (fun z : fH.ker => ((z : H) : E)) he)))
  let := hfRk
  have htop : (⊤ : Subgroup r).IsCComponent := by
    simpa only [subgroupOf_self] using hr.subgroupOf le_rfl
  have hkr := kernel_eq_solvableRadical_of_top_isCComponent htop fR hfR
  let er : (r ⧸ solvableRadical r) ≃* M22 :=
    (QuotientGroup.quotientMulEquivOfEq hkr.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective fR hfR)
  let : IsQuasisimple (r ⧸ pCore 2 r) :=
    ChapterA.Section03.cComponent_twoCore_quasisimple_of_three_rank (hC.subgroup E) hr
      (mathieu_radical_three_rank er)
  let : r.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    simpa only [normalizer_eq_top] using
      normalizer_le_normalizer_characteristic_image H (solvableResidual H)
  have hc : ⁅A.subgroupOf E,r⁆ ≤ r.pCoreIn 2 := by
    apply commutator_le_of_trivial_simpleAction
    intro a
    apply trivial_simpleAction_of_solvable_kernel r fR a
    intro x
    have ha : fE (a : E) = 1 := by
      obtain ⟨y,hy,he⟩ := hA (mem_map_of_mem q a.property)
      have he' : qE (a : E) = y := Subtype.ext he.symm
      change f (qE (a : E)) = 1
      rwa [he']
    change fE (↑(MulAut.conjNormal (a : E) x)) = fE (x : E)
    rw [MulAut.conjNormal_apply,map_mul,map_mul,map_inv,ha]
    simp
  let R := r.map E.subtype
  let e : r ≃* R := r.equivMapOfInjective E.subtype E.subtype_injective
  have hRQ : R ≤ Q := by
    rintro _ ⟨x,hx,rfl⟩
    have hxH : x ∈ H := map_subtype_le (solvableResidual H) hx
    exact hxH
  refine ⟨R,?_,hRQ,?_,?_,?_,?_,?_,?_⟩
  · have hPQ : P.map Q.subtype ≤ E := by
      rintro _ ⟨x,hx,rfl⟩
      exact hP (mem_map_of_mem _ hx)
    let P' := (P.map Q.subtype).subgroupOf E
    let : Group.IsPerfect (P.map Q.subtype) := Group.IsPerfect.map _
    let : Group.IsPerfect P' := Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe hPQ).symm.toMonoidHom)
      (subgroupOfEquivOfLe hPQ).symm.surjective
    have hPH : P' ≤ H := by
      rintro x ⟨p,hp,he⟩
      change (x : C) ∈ Q
      exact (show E.subtype x ∈ Q from he ▸ p.property)
    have hh := map_mono (f := E.subtype) (le_map_solvableResidual_of_isPerfect P' H hPH)
    rwa [map_subgroupOf_eq_of_le hPQ] at hh
  · apply (le_sectionCentralizer_iff _ _).mpr
    have hn : E ≤ normalizer (R : Set C) := by
      simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
        r.le_normalizer_map E.subtype
    refine ⟨hAE.trans hn,?_⟩
    have hh := map_mono (f := E.subtype) hc
    rwa [map_commutator,map_subgroupOf_eq_of_le hAE,
      ←AmalgamLocalCores.pCoreIn_map_of_injective 2 E.subtype E.subtype_injective] at hh
  · exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  · exact IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  · exact ⟨(QuotientGroup.congr _ _ e.symm (map_solvableRadical_equiv e.symm)).trans er⟩
  · let d : H →* C := E.subtype.comp H.subtype
    have hd : Function.Injective d := E.subtype_injective.comp H.subtype_injective
    let ed : H ≃* d.range := MonoidHom.ofInjective hd
    have hD : d.range = Q ⊓ E := by
      rw [MonoidHom.range_comp,range_subtype,subgroupOf_map_subtype]
    have hR : R = (solvableResidual d.range).map d.range.subtype := by
      rw [←map_solvableResidual_eq ed.toMonoidHom ed.surjective,map_map]
      change ((solvableResidual H).map H.subtype).map E.subtype =
        (solvableResidual H).map (E.subtype.comp H.subtype)
      rw [map_map]
    rw [hR]
    apply le_trans _ (normalizer_le_normalizer_characteristic_image
      d.range (solvableResidual d.range))
    rw [hD]
    exact (le_inf le_normalizer_of_normal (I.le_normalizer_comap q)).trans
      inf_normalizer_le_normalizer_inf
  · have hh := congrArg (map I.subtype)
      (map_solvableResidual_eq (qE.comp H.subtype) hqH)
    rw [map_map] at hh
    change (((solvableResidual H).map H.subtype).map E.subtype).map q = _
    rw [map_map,map_map]
    exact hh

/-- Lift the concrete native replacement through the original component
projection, retaining the whole seed, the exact quotient image and the action
of the selected involution's stabilizer on the lifted replacement. -/
theorem cubic_replacement_component
    {C : Type*} [Group C] [Finite C]
    (hC : IsSQTK KnownSimple.IsKnownSimple C)
    (Q A : Subgroup C) [Q.Normal] [IsQuasisimple (Q ⧸ pCore 2 Q)]
    (e : SimpleSection Q ≃* Janko4.Model)
    {P : Type*} [Group P] [Group.IsPerfect P] (j : P →* Q)
    (x : A)
    (hU : let f := (projection Q).comp j
      let b := (simpleAction Q).comp A.subtype
      f.range = (solvableResidual (b x).fixedSubgroup).map (b x).fixedSubgroup.subtype)
    (y : center ((projection Q).comp j).range) (hy : orderOf y = 3)
    (he : MulAut.conj ((y : ((projection Q).comp j).range) : SimpleSection Q) =
      (simpleAction Q) (x : C))
    (hb : ((simpleAction Q).comp A.subtype).range =
      (zpowers ((y : ((projection Q).comp j).range) : SimpleSection Q)).map
        MulAut.conj) :
    ∃ R : Subgroup C, j.range.map Q.subtype ≤ R ∧ R ≤ Q ∧
      A ≤ sectionCentralizer R ∧ Group.IsPerfect R ∧
      IsQuasisimple (R ⧸ pCore 2 R) ∧
      Nonempty ((R ⧸ solvableRadical R) ≃* M22) ∧
      ∃ t : Janko4.Model, orderOf t = 2 ∧
        (∀ c : C, MulAut.congr e (simpleAction Q c) t = t →
          c ∈ normalizer (R : Set C)) ∧
        (R.subgroupOf Q).map (e.toMonoidHom.comp (projection Q)) =
          (solvableResidual (centralizer ({t} : Set Janko4.Model))).map
            (centralizer ({t} : Set Janko4.Model)).subtype := by
  let c : Janko4.Model ≃* MulAut Janko4.Model := MulEquiv.ofBijective MulAut.conj
    ⟨MulAut.conj_injective_of_center_eq_bot Janko4.model_center_eq_bot,
      Janko4.AdequateLocal.conj_surjective⟩
  let q : C →* Janko4.Model := c.symm.toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp (simpleAction Q))
  have hqQ : q.comp Q.subtype = e.toMonoidHom.comp (projection Q) := by
    ext u
    apply c.injective
    change c (c.symm (MulAut.congr e (simpleAction Q (u : C)))) = _
    rw [c.apply_symm_apply]
    change MulAut.congr e (simpleAction Q (u : C)) = MulAut.conj (e (projection Q u))
    rw [←MulAut.congr_conj]
    congr 1
    ext v
    obtain ⟨w,rfl⟩ := projection_surjective Q v
    rw [simpleAction_projection]
    change projection Q (u * w * u⁻¹) =
      projection Q u * projection Q w * (projection Q u)⁻¹
    simp only [map_mul,map_inv]
  have hq : Function.Surjective (q.comp Q.subtype) := by
    rw [hqQ]
    exact e.surjective.comp (projection_surjective Q)
  have hk : Group.IsSolvable (q.comp Q.subtype).ker := by
    rw [hqQ,MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact projection_kernel_solvable Q
  let v : SimpleSection Q := y.val.val
  have hv : orderOf (e v) = 3 := by
    rw [e.orderOf_eq]
    exact (orderOf_coe y.val).trans ((orderOf_coe y).trans hy)
  have hS := simpleSection_sqtk (hC.subgroup Q)
  have hJ : IsSQTK KnownSimple.IsKnownSimple Janko4.Model := by
    refine ⟨?_,?_⟩
    · intro p hp ho
      rw [←primeRank_equiv p e]
      exact hS.stronglyQuasithin p hp ho
    · intro Y _ hY W g hg
      let := hY
      let W' := W.comap e.toMonoidHom
      let r := g.comp (e.toMonoidHom.subgroupComap W)
      have hr : Function.Surjective r := hg.comp
        (e.toMonoidHom.subgroupComap_surjective_of_surjective W e.surjective)
      let a := QuotientGroup.quotientKerEquivOfSurjective r hr
      let : IsSimpleGroup (W' ⧸ r.ker) := a.isSimpleGroup
      exact (hS.isKGroup (W' ⧸ r.ker) inferInstance W' (QuotientGroup.mk' r.ker)
        (QuotientGroup.mk'_surjective _)).of_mulEquiv a.symm
  obtain ⟨t,I,ht,hIC,hCI,hRI,g,hg,hgk,hvg,hIres⟩ := cubic_replacement_model hJ (e v) hv
  let : Group.IsPerfect j.range := Group.IsPerfect.range j
  have hP : j.range.map (q.comp Q.subtype) ≤ I := by
    have hCmap : (centralizer ({v} : Set (SimpleSection Q))).map e.toMonoidHom =
        centralizer ({e v} : Set Janko4.Model) := by
      rw [map_centralizer_equiv,Set.image_singleton]
    let ec := (e.subgroupMap (centralizer ({v} : Set (SimpleSection Q)))).trans
      (MulEquiv.subgroupCongr hCmap)
    have hRmap : ((solvableResidual (centralizer ({v} : Set (SimpleSection Q)))).map
        (centralizer ({v} : Set (SimpleSection Q))).subtype).map e.toMonoidHom =
        (solvableResidual (centralizer ({e v} : Set Janko4.Model))).map
          (centralizer ({e v} : Set Janko4.Model)).subtype := by
      rw [←map_solvableResidual_eq ec.toMonoidHom ec.surjective,map_map,map_map]
      rfl
    have hU' : ((projection Q).comp j).range =
        (solvableResidual (centralizer ({v} : Set (SimpleSection Q)))).map
          (centralizer ({v} : Set (SimpleSection Q))).subtype := by
      change _ = (solvableResidual (simpleAction Q (x : C)).fixedSubgroup).map
        (simpleAction Q (x : C)).fixedSubgroup.subtype at hU
      rw [←he,MulAut.fixedSubgroup_conj] at hU
      exact hU
    rw [hqQ,←map_map,MonoidHom.map_range,hU',hRmap]
    exact hRI
  have hA : A.map q ≤ g.ker.map I.subtype := by
    rintro _ ⟨a,ha,rfl⟩
    have hab : simpleAction Q a ∈ ((simpleAction Q).comp A.subtype).range := ⟨⟨a,ha⟩,rfl⟩
    rw [hb] at hab
    obtain ⟨w,hw,hew⟩ := hab
    have hqa : q a = e w := by
      apply c.injective
      change c (c.symm (MulAut.congr e (simpleAction Q a))) = MulAut.conj (e w)
      rw [c.apply_symm_apply,←hew,MulAut.congr_conj]
    rw [hqa]
    apply hvg
    have hh := mem_map_of_mem e.toMonoidHom hw
    rwa [MonoidHom.map_zpowers] at hh
  obtain ⟨R,hPR,hRQ,hAR,hperf,hqs,heR,hRn,hRm⟩ :=
    replacement_lift hC Q A q hq hk I g hg hgk j.range hP hA
  refine ⟨R,hPR,hRQ,hAR,hperf,hqs,heR,t,ht,?_,?_⟩
  · intro u hu
    apply hRn
    apply hCI
    have hc : MulAut.conj (q u) = MulAut.congr e (simpleAction Q u) :=
      c.apply_symm_apply _
    have ht' : q u * t * (q u)⁻¹ = t := by
      change MulAut.conj (q u) t = t
      rwa [hc]
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp ht')
  · rw [←hqQ,←map_map,map_subgroupOf_eq_of_le hRQ,hRm,hIres]

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Sporadic.Mathieu
/-- The exceptional cubic data with a concrete replacement above the original
seed. The original T-normalization remains to be established. -/
@[expose] def MathieuJankoCubicReplacementCase {G : Type*} [Group G]
    (T L V A : Subgroup G) : Prop :=
  ∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
    V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    ∃ a : JankoNormalizerAction K,
      a.ResidualSeedFamily ∧
      ∃ z : K, ((z : normalizer (A : Set G)) : G) ∈ V ∧ orderOf z = 2 ∧
        T ≤ centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ∧
        ∃ P : Subgroup (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ⊓
            centralizer (A : Set G) : Subgroup G),
          P.IsCComponent ∧ P.Normal ∧ Nonempty ((P ⧸ solvableRadical P) ≃* M22) ∧
          P.map (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ⊓
            centralizer (A : Set G)).subtype =
              ((solvableResidual (centralizer ({z} : Set K))).map
                (centralizer ({z} : Set K)).subtype).map
                  ((normalizer (A : Set G)).subtype.comp K.subtype) ∧
          ∃ Q : Subgroup (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G)),
            Q.IsCComponent ∧ ∃ hPQ : P.map (inclusion inf_le_left) ≤ Q,
              ∃ hn : Q.Normal, letI := hn
              IsQuasisimple (Q ⧸ pCore 2 Q) ∧
              Nonempty (OddLocalMathieu.SimpleSection Q ≃* Janko4.Model) ∧
              ∃ hAz : A ≤ centralizer ({((z : normalizer (A : Set G)) : G)} : Set G),
                ∃ x : A, orderOf (OddLocalMathieu.simpleAction Q ⟨x,hAz x.property⟩) = 3 ∧
                  Nat.card ((OddLocalMathieu.simpleAction Q).comp (inclusion hAz)).range = 3 ∧
                  (let f := (OddLocalMathieu.projection Q).comp
                      (OddLocalMathieu.seedInclusion inf_le_left hPQ)
                   let b := (OddLocalMathieu.simpleAction Q).comp (inclusion hAz)
                   f.range = (solvableResidual (b x).fixedSubgroup).map
                     (b x).fixedSubgroup.subtype ∧
                   ∃ y : center f.range, orderOf y = 3 ∧
                     MulAut.conj ((y : f.range) : OddLocalMathieu.SimpleSection Q) = b x ∧
                     b.range = (zpowers ((y : f.range) : OddLocalMathieu.SimpleSection Q)).map
                       MulAut.conj) ∧
                  ∃ I : Subgroup G,
                    P.map (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ⊓
                      centralizer (A : Set G)).subtype ≤ I ∧
                    I ≤ Q.map (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G)).subtype ∧
                    A ≤ sectionCentralizer I ∧ Group.IsPerfect I ∧
                    IsQuasisimple (I ⧸ pCore 2 I) ∧
                    Nonempty ((I ⧸ solvableRadical I) ≃* M22) ∧
                    ∃ R : Subgroup (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G)),
                      I = R.map (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G)).subtype ∧
                      R ≤ Q ∧ ∃ (e : OddLocalMathieu.SimpleSection Q ≃* Janko4.Model)
                        (t : Janko4.Model), orderOf t = 2 ∧
                        (∀ c : centralizer ({((z : normalizer (A : Set G)) : G)} : Set G),
                          MulAut.congr e (OddLocalMathieu.simpleAction Q c) t = t →
                            (c : G) ∈ normalizer (I : Set G)) ∧
                        (R.subgroupOf Q).map (e.toMonoidHom.comp (OddLocalMathieu.projection Q)) =
                          (solvableResidual (centralizer ({t} : Set Janko4.Model))).map
                            (centralizer ({t} : Set Janko4.Model)).subtype

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 OddLocalMathieu
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V A : Subgroup G}

/-- Construct the exceptional replacement inside the original involution
centralizer, with trivial odd-actor action modulo its two-core. -/
theorem mathieu_janko_cubic_replacement
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : MathieuJankoCubicCentralSeedCase (T : Subgroup G) L V A) :
    MathieuJankoCubicReplacementCase (T : Subgroup G) L V A := by
  obtain ⟨K,hK,hn,hout,hV,hF,a,hseed,z,hzV,hz,hTz,
    P,hP,hPn,eP,hPm,Q,hQ,hPQ,hnQ,hqs,hmodel,hAz,x,hx,hcard,hdata⟩ := hc
  let := hnQ
  let := hqs
  let C := centralizer ({((z : normalizer (A : Set G)) : G)} : Set G)
  let E := C ⊓ centralizer (A : Set G)
  have hzG : orderOf (((z : normalizer (A : Set G)) : G)) = 2 := by
    rw [orderOf_coe,orderOf_coe]
    exact hz
  have hz1 : ((z : normalizer (A : Set G)) : G) ≠ 1 := by
    intro he
    rw [he,orderOf_one] at hzG
    omega
  have hC : IsSQTK KnownSimple.IsKnownSimple C := by
    apply h.simpleQTKE.twoLocal_sqtk
    refine ⟨zpowers (((z : normalizer (A : Set G)) : G)),
      fun hb => hz1 (mem_bot.mp (hb ▸ mem_zpowers _)),?_,
      (normalizer_zpowers_eq_centralizer_of_order_two _ hzG).symm⟩
    exact IsPGroup.of_card (show Nat.card (zpowers (((z : normalizer (A : Set G)) : G))) = 2^1 by
      rw [Nat.card_zpowers,hzG]; rfl)
  let := hP.perfect
  let j := seedInclusion inf_le_left hPQ
  let A' := A.subgroupOf C
  let x' : A' := ⟨⟨x,hAz x.property⟩,x.property⟩
  have hb : ((simpleAction Q).comp A'.subtype).range =
      ((simpleAction Q).comp (inclusion hAz)).range := by
    ext u
    constructor
    · rintro ⟨b,rfl⟩
      exact ⟨⟨b,b.property⟩,rfl⟩
    · rintro ⟨b,rfl⟩
      exact ⟨⟨⟨b,hAz b.property⟩,b.property⟩,rfl⟩
  obtain ⟨hU,y,hy,he,hb'⟩ := hdata
  obtain ⟨R,hPR,hRQ,hAR,hperf,hqR,eR,t,ht,hnorm,himage⟩ := cubic_replacement_component hC Q A'
    hmodel.some j x' hU y hy he (hb.trans hb')
  let I := R.map C.subtype
  let ei : R ≃* I := R.equivMapOfInjective C.subtype C.subtype_injective
  let := hperf
  let := hqR
  refine ⟨K,hK,hn,hout,hV,hF,a,hseed,z,hzV,hz,hTz,
    P,hP,hPn,eP,hPm,Q,hQ,hPQ,hnQ,hqs,hmodel,hAz,x,hx,hcard,
    ⟨hU,y,hy,he,hb'⟩,I,?_,map_mono hRQ,?_,?_,?_,?_,R,rfl,hRQ,hmodel.some,t,ht,?_,himage⟩
  · have hh := map_mono (f := C.subtype) hPR
    have heq : Q.subtype.comp j = (inclusion (show E ≤ C from inf_le_left)).comp P.subtype := rfl
    rw [MonoidHom.map_range,heq,MonoidHom.range_comp,range_subtype,map_map,
      subtype_comp_inclusion] at hh
    exact hh
  · obtain ⟨hn,hcomm⟩ := (le_sectionCentralizer_iff _ _).mp hAR
    apply (le_sectionCentralizer_iff _ _).mpr
    constructor
    · have hh := (map_mono (f := C.subtype) hn).trans (R.le_normalizer_map C.subtype)
      rwa [map_subgroupOf_eq_of_le hAz] at hh
    · have hh := map_mono (f := C.subtype) hcomm
      rwa [map_commutator,map_subgroupOf_eq_of_le hAz,
        ←AmalgamLocalCores.pCoreIn_map_of_injective 2 C.subtype C.subtype_injective] at hh
  · exact Group.IsPerfect.ofSurjective (f := ei.toMonoidHom) ei.surjective
  · exact IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ ei (pCore_map_iso 2 ei))
  · exact ⟨(QuotientGroup.congr _ _ ei.symm (map_solvableRadical_equiv ei.symm)).trans eR.some⟩
  · intro c hc
    exact R.le_normalizer_map C.subtype (mem_map_of_mem C.subtype (hnorm c hc))

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal Hall obstruction supplies a concrete exceptional replacement
above the original seed, with its full native residual image and trivial
action modulo its two-core. Original T-normalization is still required. -/
theorem sourceOrbit_mathieu_hall_cubic_replacement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < ChapterE.generationParameter H)
    (B : Subgroup H) (hBN : B ≤ (normalizer (L : Set G)).subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes
      (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H)))
    (hker : B.map H.subtype ⊓ sectionCentralizer L ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ H ∧ A ≤ sectionCentralizer L ∧
      A ≤ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ normalizer (L : Set G)) ∧
      (∀ Q : Subgroup G, (T : Subgroup G) ≤ normalizer (Q : Set G) →
        A ≤ sectionCentralizer Q → Q ≤ normalizer (L : Set G)) ∧
      (((Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M12) ∨
          Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M22)) ∧
          MathieuPushingUpFactoredCase T L V A ∧ MathieuPushingUpFactorGap T L V A) ∨
        (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
          MathieuJankoSeedResidualCase (T : Subgroup G) L V A
            (D.orbitComponent ⧸ center D.orbitComponent) ∧
          (MathieuJankoComparedResidualCase (T : Subgroup G) L V A ∨
            (p = 3 ∧ MathieuJankoCubicReplacementCase (T : Subgroup G) L V A)))) := by
  have hsource :=
    @sourceOrbit_mathieu_hall_cubic_central_seed G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  refine hsource.imp fun p hpA => hpA.imp fun A hA => ?_
  revert hA
  iterate 11 apply And.imp_right
  apply Or.imp id
  intro hc
  exact ⟨hc.1,hc.2.1,hc.2.2.imp id (fun ht =>
    ⟨ht.1,mathieu_janko_cubic_replacement h.toHypothesis1221 ht.2⟩)⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
