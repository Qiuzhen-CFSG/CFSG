module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.CubicActorComparison
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.CubicFusion

/-!
# The full fixed seed in the exceptional cubic Mathieu comparison

The native simultaneous-centralizer calculation identifies the entire cubic
centralizer residual in J4. Cubic fusion transports that identity to every
order-three element, including membership of the cubic itself in the
residual. A perfect subgroup with the same M22 radical quotient must equal
this quasisimple residual: its image covers the central quotient, and
perfectness removes the remaining central supplement.

Apply this to the original seed image under the literal projection
(Q/O2(Q))/Z(Q/O2(Q)). Its full fixed residual is the seed image itself, and
the entire order-three actor image is conjugation by a central cubic of
that same seed. The application retains the full original components,
involution-centralizer residual, inclusions and quotient action.

This supplies the fixed-seed identification in the exceptional branch of
4.4.3. Construction of its T-normalized replacement subgroup I_Z, the
M12/M22 pushing-up exclusions, and identification of the original L_A with
the generating Mathieu seed remain necessary for SourceMathieuHallFaithfulAt.
In particular, no assertion that the whole seed center has order three is
made here.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 4.4.3,
printed p.623, and its application in 4.4.14, printed pp.624--625. The native
J4 fusion and centralizer certificates retain their imported attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4.Section04.OddLocalMathieu Sporadic.Mathieu
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private def centerQuotientCongr {P Q : Type*} [Group P] [Group Q]
    (e : P ≃* Q) : (P ⧸ center P) ≃* (Q ⧸ center Q) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨z,hz,rfl⟩
      exact (centerCongr e ⟨z,hz⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)

private theorem perfect_subgroup_eq_top_of_radical_quotient
    {R : Type*} [Group R] [Finite R] [Group.IsPerfect R]
    (U : Subgroup R) [Group.IsPerfect U]
    (e : (U ⧸ solvableRadical U) ≃* (R ⧸ center R)) : U = ⊤ := by
  let q := QuotientGroup.mk' (center R)
  let f := q.comp U.subtype
  have hk : f.ker ≤ center U := by
    intro x hx
    have hxz : (x : R) ∈ center R := (QuotientGroup.eq_one_iff _).mp hx
    exact mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp hxz y))
  let : Group.IsSolvable f.ker := Group.isSolvable_of_comm (fun x y =>
    Subtype.ext (mem_center_iff.mp (hk x.property) y).symm)
  let : Group.IsSolvable f.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    infer_instance
  let er := (solvableRadicalQuotientEquiv f.rangeRestrict f.rangeRestrict_surjective).symm.trans e
  have hcard : Nat.card (R ⧸ center R) ≤ Nat.card f.range := by
    rw [←Nat.card_congr er.toEquiv]
    exact Nat.card_le_card_of_surjective (QuotientGroup.mk' (solvableRadical f.range))
      (QuotientGroup.mk'_surjective _)
  have hr : f.range = ⊤ := eq_top_of_card_eq f.range (le_antisymm
    (Nat.card_le_card_of_injective f.range.subtype f.range.subtype_injective) hcard)
  have hmap : (⊤ : Subgroup R).map q ≤ U.map q := by
    have he : U.map q = f.range := by rw [MonoidHom.range_comp,range_subtype]
    rw [he,hr]
    exact le_top
  have := perfect_le_of_map_le_of_central_kernel q (by rw [QuotientGroup.ker_mk'])
    (⊤ : Subgroup R) U hmap
  exact top_unique this

/-- The full cubic centralizer residual at every cubic, including the cubic itself. -/
theorem janko_cubic_residual_at
    (hJ : IsSQTK KnownSimple.IsKnownSimple Janko4.Model)
    (y : Janko4.Model) (hy : orderOf y = 3) :
    IsQuasisimple (solvableResidual (centralizer ({y} : Set Janko4.Model))) ∧
      Nonempty ((solvableResidual (centralizer ({y} : Set Janko4.Model)) ⧸
        center (solvableResidual (centralizer ({y} : Set Janko4.Model)))) ≃* M22) ∧
      (⟨y,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({y} : Set Janko4.Model)) ∈
        solvableResidual (centralizer ({y} : Set Janko4.Model)) := by
  obtain ⟨x,hx,hqx,hmem,hres,hqs,he⟩ := cubic_full_residual_of_cover
    (MonoidHom.id Janko4.Model) Function.surjective_id (by simp) (by simp) hJ
  have hx' : orderOf (x : Janko4.Model) = 3 := hqx
  obtain ⟨g,hg⟩ := Janko4.LocalStructure.cubic_cyclic_fusion
    (MonoidHom.id Janko4.Model) Function.surjective_id (by simp) (x : Janko4.Model) y hx' hy
  let a := MulAut.conj g
  let C := centralizer ({(x : Janko4.Model)} : Set Janko4.Model)
  let E := centralizer ({y} : Set Janko4.Model)
  have hc : C.map a.toMonoidHom = E := by
    dsimp only [C,E]
    rw [←centralizer_closure,←zpowers_eq_closure,map_centralizer_equiv]
    change centralizer ((zpowers (x : Janko4.Model)).map a.toMonoidHom : Set Janko4.Model) = _
    rw [hg,zpowers_eq_closure,centralizer_closure]
  let c : C ≃* E := (a.subgroupMap C).trans (MulEquiv.subgroupCongr hc)
  let r := c.solvableResidualEquiv
  let := hqs
  refine ⟨IsQuasisimple.of_mulEquiv r,⟨(centerQuotientCongr r.symm).trans he.some⟩,?_⟩
  have hxm : (x : Janko4.Model) ∈ (solvableResidual C).map C.subtype := by
    rw [hres]
    exact mem_map_of_mem C.subtype
      (mem_map_of_mem ((Janko4.InvolutionCentralizers.First.centralizer.comap
        (MonoidHom.id Janko4.Model)).subtype.elementCentralizerMap x) hmem)
  have hmap : ((solvableResidual C).map C.subtype).map a.toMonoidHom =
      (solvableResidual E).map E.subtype := by
    rw [←map_solvableResidual_eq c.toMonoidHom c.surjective,map_map,map_map]
    rfl
  have hle := map_mono (f := a.toMonoidHom) (zpowers_le.mpr hxm)
  rw [hg,hmap] at hle
  obtain ⟨t,ht,hty⟩ := hle (mem_zpowers y)
  have het : t = (⟨y,mem_centralizer_singleton_iff.mpr rfl⟩ : E) := Subtype.ext hty
  exact het ▸ ht

/-- The original perfect Mathieu image is the entire cubic residual. -/
theorem janko_cubic_fixed_seed_eq_residual
    (hJ : IsSQTK KnownSimple.IsKnownSimple Janko4.Model)
    (y : Janko4.Model) (hy : orderOf y = 3)
    (U : Subgroup Janko4.Model) [Group.IsPerfect U]
    (eU : (U ⧸ solvableRadical U) ≃* M22)
    (hU : U ≤ centralizer ({y} : Set Janko4.Model)) :
    U = (solvableResidual (centralizer ({y} : Set Janko4.Model))).map
      (centralizer ({y} : Set Janko4.Model)).subtype ∧ y ∈ U := by
  let C := centralizer ({y} : Set Janko4.Model)
  let R := solvableResidual C
  have h := janko_cubic_residual_at hJ y hy
  let := h.1
  let UC := U.subgroupOf C
  let eUC : UC ≃* U := subgroupOfEquivOfLe hU
  let : Group.IsPerfect UC := Group.IsPerfect.ofSurjective (f := eUC.symm.toMonoidHom) eUC.symm.surjective
  have hUR : UC ≤ R := le_solvableResidual_of_isPerfect UC
  let UR := UC.subgroupOf R
  let eUR : UR ≃* U := (subgroupOfEquivOfLe hUR).trans eUC
  let : Group.IsPerfect UR := Group.IsPerfect.ofSurjective (f := eUR.symm.toMonoidHom) eUR.symm.surjective
  have he : UR = ⊤ := perfect_subgroup_eq_top_of_radical_quotient UR
    (((QuotientGroup.congr _ _ eUR (map_solvableRadical_equiv eUR)).trans eU).trans h.2.1.some.symm)
  have hUC : UC = R := by
    have hh := congrArg (map R.subtype) he
    rw [map_subgroupOf_eq_of_le hUR,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hUeq : U = R.map C.subtype := by
    have hh := congrArg (map C.subtype) hUC
    rwa [map_subgroupOf_eq_of_le hU] at hh
  exact ⟨hUeq,hUeq.symm ▸ mem_map_of_mem C.subtype h.2.2⟩

/-- The actual simple section inherits SQTK from its original C-component. -/
theorem simpleSection_sqtk {Q : Type*} [Group Q] [Finite Q]
    [IsQuasisimple (Q ⧸ pCore 2 Q)]
    (hQ : IsSQTK KnownSimple.IsKnownSimple Q) :
    IsSQTK KnownSimple.IsKnownSimple (SimpleSection Q) := by
  let E := Q ⧸ pCore 2 Q
  let S := SimpleSection Q
  let : IsSimpleGroup S := IsQuasisimple.simple
  let : Group.IsPerfect S := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center E)) (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple S := IsQuasisimple.of_surjective
    (QuotientGroup.mk' (center E)) (QuotientGroup.mk'_surjective _)
  have hsemi : ChapterA.Section02.IsSemisimple S := by
    apply top_unique
    apply le_sSup
    exact ⟨(inferInstance : (⊤ : Subgroup S).Normal).isSubnormal,
      IsQuasisimple.of_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup S) ≃* S).symm⟩
  have hsec := ChapterA.Section02.IsSectionOf.of_surjective (projection Q) (projection_surjective Q)
  exact ⟨ChapterA.Section02.theoremA_knownSimple.stronglyQuasithin_section
    hQ.stronglyQuasithin hQ.isKGroup hsec hsemi,
    (hQ.isKGroup.quotient (pCore 2 Q)).quotient (center E)⟩

/-- A cubic fixing the actual perfect Mathieu image is conjugation by
an element of its center, and that image is the entire fixed residual. -/
theorem cubic_fixed_seed_central_inner
    {S : Type*} [Group S] [Finite S]
    (hS : IsSQTK KnownSimple.IsKnownSimple S) (e : S ≃* Janko4.Model)
    (U : Subgroup S) [Group.IsPerfect U]
    (eU : (U ⧸ solvableRadical U) ≃* M22)
    (a : MulAut S) (ha : orderOf a = 3) (hfix : U ≤ a.fixedSubgroup) :
    U = (solvableResidual a.fixedSubgroup).map a.fixedSubgroup.subtype ∧
      ∃ y : center U, orderOf y = 3 ∧ MulAut.conj ((y : U) : S) = a := by
  obtain ⟨t,ht⟩ := Janko4.AdequateLocal.conj_surjective (MulAut.congr e a)
  obtain ⟨y,hy⟩ := (MulAut.congr_inner_iff e a).mp ⟨t,ht.symm⟩
  have hye : MulAut.conj (e y) = MulAut.congr e a := by
    rw [hy,MulAut.congr_conj]
  have hyo : orderOf y = 3 := by
    have hh := orderOf_injective MulAut.conj
      (MulAut.conj_injective_of_center_eq_bot Janko4.model_center_eq_bot) (e y)
    rw [hye,(MulAut.congr e).orderOf_eq,e.orderOf_eq] at hh
    exact hh.symm.trans ha
  let C := centralizer ({y} : Set S)
  let E := centralizer ({e y} : Set Janko4.Model)
  let UM := U.map e.toMonoidHom
  let eu : U ≃* UM := U.equivMapOfInjective e.toMonoidHom e.injective
  let : Group.IsPerfect UM := Group.IsPerfect.ofSurjective (f := eu.toMonoidHom) eu.surjective
  have hUM : UM ≤ E := by
    rintro _ ⟨u,hu,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change e u * e y = e y * e u
    have hh := hfix hu
    rw [hy,MulAut.fixedSubgroup_conj] at hh
    simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp hh)
  have hmodel : IsSQTK KnownSimple.IsKnownSimple Janko4.Model := by
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
  obtain ⟨heq,hym⟩ := janko_cubic_fixed_seed_eq_residual hmodel
    (e y) (by rw [e.orderOf_eq]; exact hyo) UM
    ((QuotientGroup.congr _ _ eu.symm (map_solvableRadical_equiv eu.symm)).trans eU) hUM
  have hc : C.map e.toMonoidHom = E := by
    dsimp only [C,E]
    rw [←centralizer_closure,←zpowers_eq_closure,map_centralizer_equiv]
    change centralizer ((zpowers y).map e.toMonoidHom : Set Janko4.Model) = _
    rw [MonoidHom.map_zpowers,zpowers_eq_closure,centralizer_closure]
    rfl
  let ec : C ≃* E := (e.subgroupMap C).trans (MulEquiv.subgroupCongr hc)
  have hR : ((solvableResidual C).map C.subtype).map e.toMonoidHom =
      (solvableResidual E).map E.subtype := by
    rw [←map_solvableResidual_eq ec.toMonoidHom ec.surjective,map_map,map_map]
    rfl
  have hUeq : U = (solvableResidual C).map C.subtype := by
    apply map_injective (f := e.toMonoidHom) e.injective
    exact heq.trans hR.symm
  have hyU : y ∈ U := by
    obtain ⟨u,hu,huye⟩ := hym
    exact e.injective huye ▸ hu
  have hyZ : (⟨y,hyU⟩ : U) ∈ center U := by
    apply mem_center_iff.mpr
    intro u
    apply Subtype.ext
    have hu := hfix u.property
    rw [hy,MulAut.fixedSubgroup_conj] at hu
    exact mem_centralizer_singleton_iff.mp hu
  refine ⟨?_,⟨⟨y,hyU⟩,hyZ⟩,?_,hy.symm⟩
  · rw [hy,MulAut.fixedSubgroup_conj]
    exact hUeq
  · rw [←orderOf_coe,←orderOf_coe]
    exact hyo

/-- The entire order-three actor image is realized by the same central
cubic of the original fixed seed. -/
theorem cubic_actor_fixed_seed_central_range
    {A S : Type*} [Group A] [Group S] [Finite S]
    (hS : IsSQTK KnownSimple.IsKnownSimple S) (e : S ≃* Janko4.Model)
    (U : Subgroup S) [Group.IsPerfect U]
    (eU : (U ⧸ solvableRadical U) ≃* M22)
    (b : A →* MulAut S) (x : A) (hx : orderOf (b x) = 3)
    (hcard : Nat.card b.range = 3)
    (hfix : U ≤ (b x).fixedSubgroup) :
    U = (solvableResidual (b x).fixedSubgroup).map (b x).fixedSubgroup.subtype ∧
      ∃ y : center U, orderOf y = 3 ∧ MulAut.conj ((y : U) : S) = b x ∧
        b.range = (zpowers ((y : U) : S)).map MulAut.conj := by
  obtain ⟨hU,y,hy,he⟩ := cubic_fixed_seed_central_inner hS e U eU (b x) hx hfix
  refine ⟨hU,y,hy,he,?_⟩
  rw [MonoidHom.map_zpowers,he]
  symm
  apply eq_of_le_of_card_ge (show zpowers (b x) ≤ b.range from zpowers_le.mpr ⟨x,rfl⟩)
  rw [hcard,Nat.card_zpowers,hx]

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Sporadic.Mathieu
/-- The cubic actor is realized centrally inside the full fixed seed image,
with the original covering component, residual and quotient maps retained. -/
@[expose] def MathieuJankoCubicCentralSeedCase {G : Type*} [Group G]
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
                       MulAut.conj)

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 OddLocalMathieu
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V A : Subgroup G}

/-- Identify the actual fixed seed, and realize the full cubic actor image
by its central cubic, without replacing the ambient covering component. -/
theorem mathieu_janko_cubic_central_seed
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : MathieuJankoCubicSectionCase (T : Subgroup G) L V A) :
    MathieuJankoCubicCentralSeedCase (T : Subgroup G) L V A := by
  obtain ⟨K,hK,hn,hout,hV,hF,a,hseed,z,hzV,hz,hTz,
    P,hP,hPn,⟨eP⟩,hPm,Q,hQ,hPQ,hnQ,hqs,hmodel,hAz,x,hx,hcard⟩ := hc
  let := hnQ
  let := hqs
  let zG : G := ((z : normalizer (A : Set G)) : G)
  let C := centralizer ({zG} : Set G)
  let E := C ⊓ centralizer (A : Set G)
  have hzG : orderOf zG = 2 := by
    rw [orderOf_coe,orderOf_coe]
    exact hz
  have hz1 : zG ≠ 1 := by intro he; rw [he,orderOf_one] at hzG; omega
  have hC : IsSQTK KnownSimple.IsKnownSimple C := by
    apply h.simpleQTKE.twoLocal_sqtk
    refine ⟨zpowers zG,fun hb => hz1 (mem_bot.mp (hb ▸ mem_zpowers _)),?_,
      (normalizer_zpowers_eq_centralizer_of_order_two _ hzG).symm⟩
    exact IsPGroup.of_card (show Nat.card (zpowers zG) = 2^1 by
      rw [Nat.card_zpowers,hzG]; rfl)
  let := hP.perfect
  let : Nontrivial P := (nontrivial_iff_ne_bot _).mpr hP.ne_bot
  let j := seedInclusion inf_le_left hPQ
  let f := (projection Q).comp j
  obtain ⟨hfn,_,⟨e⟩⟩ := seed_image j (seedInclusion_injective inf_le_left hPQ) eP
  let : Group.IsPerfect f.range := Group.IsPerfect.ofSurjective
    (f := f.rangeRestrict) f.rangeRestrict_surjective
  let b := (simpleAction Q).comp (inclusion hAz)
  have hfixed : f.range ≤ (b x).fixedSubgroup := by
    rintro _ ⟨y,rfl⟩
    rw [MulAut.mem_fixedSubgroup]
    change simpleAction Q (⟨x,hAz x.property⟩ : C) (projection Q (j y)) = projection Q (j y)
    rw [simpleAction_projection]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    change (x : G) * ((y : E) : G) * (x : G)⁻¹ = _
    rw [y.val.property.2 (x : G) x.property,mul_inv_cancel_right]
    rfl
  have hs := cubic_actor_fixed_seed_central_range (simpleSection_sqtk (hC.subgroup Q))
    hmodel.some f.range e b x hx hcard hfixed
  exact ⟨K,hK,hn,hout,hV,hF,a,hseed,z,hzV,hz,hTz,
    P,hP,hPn,⟨eP⟩,hPm,Q,hQ,hPQ,hnQ,hqs,hmodel,hAz,x,hx,hcard,hs⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal Hall obstruction now identifies the entire exceptional cubic
fixed residual with the original seed image and realizes the full actor
image by a central cubic in that same seed. -/
theorem sourceOrbit_mathieu_hall_cubic_central_seed
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
            (p = 3 ∧ MathieuJankoCubicCentralSeedCase (T : Subgroup G) L V A)))) := by
  have hsource :=
    @sourceOrbit_mathieu_hall_cubic_section G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  refine hsource.imp fun p hpA => hpA.imp fun A hA => ?_
  revert hA
  iterate 11 apply And.imp_right
  apply Or.imp id
  intro hc
  exact ⟨hc.1,hc.2.1,hc.2.2.imp id (fun ht =>
    ⟨ht.1,mathieu_janko_cubic_central_seed h.toHypothesis1221 ht.2⟩)⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
