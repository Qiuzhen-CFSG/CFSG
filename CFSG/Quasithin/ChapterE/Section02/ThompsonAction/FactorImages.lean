module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.SolvableBaumann
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.QuasisimpleWhole
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.QuasisimpleFiveWhole
/-!
# Original Thompson and Baumann images in the single-factor branches

The solvable singleton is the full SL₂(2) image. The genuine quasisimple
whole-module coordinates give the natural semilinear image calculation.
The symmetric-five whole quotient gives the same transposition four-group
for both original subgroups. Equality is transported through the unchanged
centralizer kernel; no image equality is an input.

Source: Aschbacher–Smith E.2.3(2),(3), printed pp.216–217.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
theorem solvable_single_images_of_factors
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G)) (hcore : pCore 2 H = ⊥)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (d : ChapterB.ThreeConjugates.SolvableFFStructure
      (NormalElementaryQuotient.representation U q hq hker)) (hc : d.count = 1) :
    (elementaryAbelianMaxJ (T : Subgroup G)).map q = (T : Subgroup G).map q ∧
      (ChapterB.baumann (T : Subgroup G)).map q = (T : Subgroup G).map q := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let D := d.toSolvableFFFactors
  have hfaith := NormalElementaryQuotient.representation_injective U q hq hker
  have hne : q.ker ≠ ⊤ := by
    intro he
    exact hJ (hker ▸ (he ▸ (le_top : elementaryAbelianMaxJ (T : Subgroup G) ≤ ⊤)))
  have hp := (ChapterB.minimalParabolic_reduced_image T hP q hq hcore hne).2
  have hff : IsFFModule α := (isFFModule_iff_quadraticRatio_le_one α).mpr d.ratio_one.le
  have hr := (ChapterB.offender_generation (T.mapSurjective hq) hp α hff hcore).1
  let j := D.singleAmbientHom hc
  have hji := D.singleAmbientHom_injective hfaith hcore hr hc
  have hjs := D.singleAmbientHom_surjective hc
  let q' := j.comp q
  have hq' : Function.Surjective q' := hjs.comp hq
  have hk' : q'.ker = centralizer (U : Set G) := by
    rw [← hker]
    ext g
    change j (q g) = 1 ↔ q g = 1
    exact (map_eq_one_iff j hji)
  let α' := NormalElementaryQuotient.representation U q' hq' hk'
  have heq (a : H) (v : Additive U) : α' (j a) v = α a v := by
    obtain ⟨g,rfl⟩ := hq a
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (NormalElementaryQuotient.representation_apply U q' hq' hk' g v).trans
      (NormalElementaryQuotient.representation_apply U q hq hker g v).symm

  have hf := D.singleQuotientMap_surjective hfaith hr hc
  have he : ∀ a v, D.singleQuotientMap hfaith hr hc (α' a v) =
      SL2NaturalOffenders.NoStrong.natural a (D.singleQuotientMap hfaith hr hc v) := by
    intro a v
    obtain ⟨a,rfl⟩ := hjs a
    rw [heq,D.singleQuotientMap_equivariant]
    exact (D.singleAmbientHom_action hc a _).symm
  obtain ⟨hj,hb⟩ := ChapterB.RankOneBaumann.thompson_baumann_images_of_natural_quotient
    T U q' hq' hk' (hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)) hJ
    (D.singleQuotientMap hfaith hr hc) hf he
  constructor
  · apply Subgroup.map_injective hji
    simpa only [Subgroup.map_map] using hj
  · apply Subgroup.map_injective hji
    simpa only [Subgroup.map_map] using hb
end CFSG.Quasithin.ChapterE.ThompsonAction
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
attribute [local instance] RankOneBaumann.semilinear_moved_elementary
theorem quasisimple_linear_source_images
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (hqs : IsQuasisimple (generalizedFitting
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (s : MovedSection ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype)
      (generalizedFitting (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (F : BinaryField)
    (hnatural : IsLinearNatural (s.action.comp (generalizedFitting
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))).subtype) F 2) :
    let Y := offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)
    (elementaryAbelianMaxJ (T : Subgroup G)).map q = (T : Subgroup G).map q ⊓ Y ∧
      (baumann (T : Subgroup G)).map q = (T : Subgroup G).map q ⊓ Y := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  let A := generalizedFitting Y
  let := offenderSubgroup_normal α
  let := hqs
  let : IsSimpleGroup (A ⧸ center A) := hqs.simple
  let : Nontrivial A := Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (center A))
  obtain ⟨e⟩ := hnatural
  have hF := perfect_linear_two_field_large F e.groupEquiv
  have hcore : pCore 2 H = ⊥ := by
    let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
    rw [← pCore_map_iso 2 e,hU.quotient_pCore_eq_bot,Subgroup.map_bot]
  have hn : q.ker ≠ ⊤ := by
    intro he
    exact hJ (hker ▸ (he ▸ (le_top : elementaryAbelianMaxJ (T:Subgroup G) ≤ ⊤)))
  have hp := (minimalParabolic_reduced_image T hP q hq hcore hn).2
  have hff : IsFFModule α := by
    obtain hf | ⟨_,hff,_,_,_⟩ := lemma_B_2_7 U q hq hker T
    · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top T).trans hf.1)).elim
    · exact hff
  have hL := (source_quasisimple_fitting_eq_residual (T.mapSurjective hq) hp Y
    (offender_generation (T.mapSurjective hq) hp α hff hcore).2 hqs).1
  have hX : A.map Y.subtype = (pResidual 2 G).map q := by
    rw [map_pResidual_of_surjective 2 q hq]
    exact hL


  let σ := α.comp Y.subtype
  obtain ⟨_,hAtop,_,⟨eV⟩⟩ := quasisimple_linear_whole_source T hP U hU hJ q hq hker hqs s F ⟨e⟩
  let L := A.map Y.subtype
  let : L.Normal := by change (A.map Y.subtype).Normal; infer_instance
  have hLY : L = Y := by
    change A.map Y.subtype = Y
    rw [show A=⊤ from hAtop,←MonoidHom.range_eq_map,range_subtype]
  have hself : centralizer (L : Set H) ≤ L := by
    change centralizer (A.map Y.subtype : Set H) ≤ A.map Y.subtype
    rw [hL]
    exact centralizer_pResidual_le_of_pCore_eq_bot hcore
  let f := eV.linearEquiv.toLinearMap.comp (fixedSpace σ A).mkQ
  have hf : Function.Surjective f := eV.linearEquiv.surjective.comp (fixedSpace σ A).mkQ_surjective
  have hkf : f.ker = fixedSpace α L := by
    ext v
    change eV.linearEquiv ((fixedSpace σ A).mkQ v)=0 ↔ _
    rw [←eV.linearEquiv.map_zero,eV.linearEquiv.injective.eq_iff,
      Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
    rw [fixedSpace_comp_map]
  let eg := (A.equivMapOfInjective Y.subtype Y.subtype_injective).symm.trans eV.groupEquiv
  let τ := (SL2NaturalOffenders.NoStrong.natural (F:=F.Carrier)).comp eg.toMonoidHom
  have hτ : Function.Injective τ := by
    intro a b hab
    apply eg.injective
    apply Subtype.ext
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    exact LinearMap.congr_fun hab v
  have hef (g : L) v : f (α (g:H) v)=τ g (f v) := by
    let a := (A.equivMapOfInjective Y.subtype Y.subtype_injective).symm g
    have ha : ((a:Y):H) = (g:H) := congrArg Subtype.val
      ((A.equivMapOfInjective Y.subtype Y.subtype_injective).apply_symm_apply g)
    have hh := eV.intertwines a ((fixedSpace σ A).mkQ v)
    change f (α ((a:Y):H) v)=_ at hh
    rw [ha] at hh
    exact hh
  obtain ⟨ρ,hρ,heρ,hnat⟩ := exists_faithful_action_of_normal_layer_quotient α L hself τ hτ f hf hkf hef
  have himages := RankOneBaumann.thompson_baumann_images_of_semilinear_quotient T U q hq hker
    (hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)) hJ L eg ρ hρ
    (fun g v => hnat g v) hF f hf heρ
  simpa only [hLY] using himages
theorem quasisimple_five_source_images
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (hqs : IsQuasisimple (generalizedFitting
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (s : MovedSection ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype)
      (generalizedFitting (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (e : MarkedActionEquiv s.action (offenderSubgroup s.action)
      (generalizedFitting (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)))
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5))) :
    (elementaryAbelianMaxJ (T : Subgroup G)).map q = (baumann (T : Subgroup G)).map q := by
  obtain ⟨p,hp,hk,f,hf,he,hfk⟩ := quasisimple_five_whole_quotient T hP U hU hJ q hq hker hqs s e
  have him := (ChapterC.SymmetricFive.source_natural_quotient_conclusions T hP U hU
    p hp hk f hf he hJ hfk).1
  apply Subgroup.comap_injective hq
  have hh := congrArg (comap p) him
  simpa only [comap_map_eq,hk,hker] using hh
end CFSG.Quasithin.ChapterE.ThompsonAction
