module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityActualPair
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityActualPairHeld
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension.SolvableKernel
public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapNormSylow
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.ConjugateSpanSylow
/-!
# The original moved pair in the Held quotient

Retain P=(B∨T)∩K, the original mover, and the full Sylow intersection
with K. The source index-two orbit theorem identifies the T-span with B
joined to its conjugate. Solvable-kernel transport preserves both components
in K/O∞(K). The Held two-local theorem forces the image overgroup's two-core
to be trivial, making the two images actual simple PSL₂(7) factors.
Their join is the original span image, still normalized by the full Sylow.
The Held action-kernel theorem excludes it entirely downstairs.

Source: Aschbacher--Smith, A.3.12(19) and 1.2.8(1), pp.48 and 506.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.Section02.MovedMaximality
variable {G : Type*} [Group G] [Finite G]

private theorem exists_sylow_normalized_restriction (T : Sylow 2 G) (K : Subgroup G)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) :
    ∃ S : Sylow 2 K, (S : Subgroup K) = (T : Subgroup G).subgroupOf K := by
  let H := K ⊔ (T : Subgroup G)
  have hKH : K ≤ H := le_sup_left
  let C := K.subgroupOf H
  let : C.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hTK)
  let U := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  obtain ⟨S,hS⟩ := U.exists_subgroupOf_eq_of_normal C
  let e := subgroupOfEquivOfLe hKH
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (S : Subgroup C).map e.toMonoidHom = _
  rw [hS]
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨⟨x,hKH x.property⟩,x.property⟩,hx,rfl⟩

omit [Finite G] in
private theorem map_conj_subtype (P : Subgroup G) (A : Subgroup P) (t : P) :
    (A.map (MulAut.conj t).toMonoidHom).map P.subtype =
      (A.map P.subtype).map (MulAut.conj (t : G)).toMonoidHom := by
  rw [map_map,map_map]
  rfl

private noncomputable def simple_core_image_equiv
    {X Y Z : Type*} [Group X] [Finite X] [Group Y] [Finite Y] [Group Z]
    (f : X →* Y) (hf : Function.Surjective f) [Group.IsSolvable f.ker] (hcore : pCore 2 Y = ⊥)
    (A : Subgroup X) (hA : A.IsCComponent)
    [IsSimpleGroup (A ⧸ pCore 2 A)] (e : (A ⧸ pCore 2 A) ≃* Z) :
    A.map f ≃* Z := by
  let g := f.subgroupMap A
  let : Group.IsSolvable g.ker := by
    rw [show g = f.subgroupMap A from rfl,ker_subgroupMap]
    exact Group.isSolvable_of_isSolvable_injective
      (f := A.subtype.subgroupComap f.ker)
      (fun a b he => Subtype.ext (Subtype.ext
        (congrArg (fun x : f.ker => (x : X)) he)))
  let := hA.perfect
  have hc : pCore 2 (A.map f) = ⊥ := by
    rw [pCore_subnormal_eq_comap 2
      (cComponent_map_of_solvable_ker hA f hf).subnormal,hcore]
    exact (A.map f).subtype.ker_eq_bot (A.map f).subtype_injective
  exact ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm.trans
    ((PerfectCoreTwoExtension.solvableKernelQuotientEquiv g (f.subgroupMap_surjective A)).symm.trans e)

private theorem image_pair_ne {X Y : Type*} [Group X] [Group Y] [Finite X]
    (f : X →* Y) (hf : Function.Surjective f) [Group.IsSolvable f.ker]
    {A D : Subgroup X} (hA : A.IsCComponent) (hD : D.IsCComponent) (hne : A ≠ D) :
    A.map f ≠ D.map f := by
  intro he
  apply hne
  apply hA.eq_of_map_quotient_eq hD f.ker
  apply map_injective (f := (QuotientGroup.quotientKerEquivOfSurjective f hf).toMonoidHom)
    (QuotientGroup.quotientKerEquivOfSurjective f hf).injective
  have hc : (QuotientGroup.quotientKerEquivOfSurjective f hf).toMonoidHom.comp
      (QuotientGroup.mk' f.ker) = f := by ext x; rfl
  simpa only [map_map,hc] using he

/-- The actual moved PSL₂(7) pair cannot lie in a normalized overcomponent
whose intrinsic radical quotient is Held. -/
theorem actual_pair_not_held_of_seven
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ L G (T : Subgroup G)) (hBK : B ≤ K)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : B < conjugateSpanBy B (T : Subgroup G))
    (hseven : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 7)
    (hheld : Nonempty ((K ⧸ solvableRadical K) ≃* Held.He)) : False := by
  let J := B ⊔ (T : Subgroup G)
  let P := J ⊓ K
  let V := conjugateSpanBy B (T : Subgroup G)
  have hBP : B ≤ P := le_inf le_sup_left hBK
  have hPK : P ≤ K := inf_le_right
  have hTP : (T : Subgroup G) ≤ normalizer (P : Set G) :=
    (le_inf ((show (T : Subgroup G) ≤ J from le_sup_right).trans J.le_normalizer)
      hTK).trans inf_normalizer_le_normalizer_inf
  have hnon : ¬ (T : Subgroup G) ≤ normalizer (B : Set G) :=
    fun hn => hm.not_ge (conjugateSpanBy_le le_rfl hn)
  obtain ⟨t,ht,htB⟩ := Set.not_subset.mp hnon
  let ep := P.normalizerMonoidHom ⟨t,hTP ht⟩
  let A := B.subgroupOf P
  let D := A.map ep.toMonoidHom
  have hA : A.IsCComponent := hB.1.subgroupOf_of_le hBP inf_le_left
  have hD : D.IsCComponent := hA.map_equiv ep
  have hmaps : D.map P.subtype = B.map (MulAut.conj t).toMonoidHom := by
    change (A.map ep.toMonoidHom).map P.subtype = _
    rw [map_map]
    have hc : P.subtype.comp ep.toMonoidHom = (MulAut.conj t).toMonoidHom.comp P.subtype := rfl
    rw [hc,←map_map,map_subgroupOf_eq_of_le hBP]
  have hne : A ≠ D := by
    intro he
    apply htB
    apply mem_normalizer_iff_map_conj_eq.mpr
    change B.map (MulAut.conj t).toMonoidHom = B
    rw [←hmaps,←he,map_subgroupOf_eq_of_le hBP]
  have hindex : (normalizer ((B.subgroupOf J) : Set J)).index = 2 := by
    have hQ := uniqueness_local_quotient_sqtk hG hB.2.2
    rcases proposition_1_2_1_three_index_knownSimple hQ hB.1 with hn | ⟨hi,_⟩
    · exact (hnon (le_sup_right.trans
        ((normal_subgroupOf_iff_le_normalizer (show B ≤ J from le_sup_left)).mp hn))).elim
    · exact hi
  have htm : (B.subgroupOf J).map (MulAut.conj (⟨t,(show (T : Subgroup G) ≤ J from le_sup_right) ht⟩ : J)).toMonoidHom ≠
      B.subgroupOf J := by
    intro he
    apply htB
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hh := congrArg (map J.subtype) he
    change B.map (MulAut.conj t).toMonoidHom = B
    simpa only [map_conj_subtype,map_subgroupOf_eq_of_le
      (show B ≤ J from le_sup_left)] using hh
  have horbit (s : T) : B.map (MulAut.conj (s : G)).toMonoidHom = B ∨
      B.map (MulAut.conj (s : G)).toMonoidHom = B.map (MulAut.conj t).toMonoidHom := by
    have hh := NormPair.conjugate_eq_or_eq_of_normalizer_index_two hindex htm
      (⟨s,(show (T : Subgroup G) ≤ J from le_sup_right) s.property⟩ : J)
    exact hh.imp (fun he => by
      have hh := congrArg (map J.subtype) he
      simpa only [map_conj_subtype,map_subgroupOf_eq_of_le
        (show B ≤ J from le_sup_left)] using hh) (fun he => by
      have hh := congrArg (map J.subtype) he
      simpa only [map_conj_subtype,map_subgroupOf_eq_of_le
        (show B ≤ J from le_sup_left)] using hh)
  have hspan : B ⊔ B.map (MulAut.conj t).toMonoidHom = V := by
    apply le_antisymm
    · refine sup_le (le_conjugateSpanBy B _) ?_
      rw [show V = conjugateSpanBy B (T : Subgroup G) from rfl,conjugateSpanBy_eq_iSup_conj]
      exact le_iSup (fun s : T => B.map (MulAut.conj (s : G)).toMonoidHom) ⟨t,ht⟩
    · rw [show V = conjugateSpanBy B (T : Subgroup G) from rfl,conjugateSpanBy_eq_iSup_conj]
      apply iSup_le
      intro s
      exact (horbit s).elim (fun he => he.le.trans le_sup_left) (fun he => he.le.trans le_sup_right)
  have hVJ : V ≤ J := conjugateSpanBy_le le_sup_left
    ((show (T : Subgroup G) ≤ J from le_sup_right).trans J.le_normalizer)
  have hVK : V ≤ K := conjugateSpanBy_le hBK hTK
  have hVP : V ≤ P := le_inf hVJ hVK
  have hgen : A ⊔ D = V.subgroupOf P := by
    apply map_injective P.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hBP,hmaps,hspan,map_subgroupOf_eq_of_le hVP]
  let q := QuotientGroup.mk' (solvableRadical K)
  let f := q.comp (inclusion hPK)
  let Y := f.range
  let g := f.rangeRestrict
  let : Group.IsSolvable f.ker := by
    rw [show f = q.comp (inclusion hPK) from rfl,←MonoidHom.comap_ker]
    rw [show q = QuotientGroup.mk' (solvableRadical K) from rfl,QuotientGroup.ker_mk']
    exact Group.isSolvable_of_isSolvable_injective
      (f := (inclusion hPK).subgroupComap (solvableRadical K))
      (fun a b he => Subtype.ext (inclusion_injective hPK (congrArg Subtype.val he)))
  let : Group.IsSolvable g.ker := by
    rw [show g.ker = f.ker from f.ker_rangeRestrict]
    infer_instance
  let A' := A.map g
  let D' := D.map g
  have hA' : A'.IsCComponent := cComponent_map_of_solvable_ker hA g f.rangeRestrict_surjective
  have hD' : D'.IsCComponent := cComponent_map_of_solvable_ker hD g f.rangeRestrict_surjective
  have hne' : A' ≠ D' := image_pair_ne g f.rangeRestrict_surjective hA hD hne
  obtain ⟨S,hS⟩ := exists_sylow_normalized_restriction T K hTK
  let SQ := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hSY : (SQ : Subgroup (K ⧸ solvableRadical K)) ≤ Y := by
    rintro _ ⟨s,hs,rfl⟩
    refine ⟨⟨s,?_,s.property⟩,rfl⟩
    have hsT : (s : G) ∈ (T : Subgroup G) := by
      have hh : s ∈ (T : Subgroup G).subgroupOf K := hS ▸ hs
      exact hh
    exact (show (T : Subgroup G) ≤ J from le_sup_right) hsT
  have hcore : pCore 2 Y = ⊥ := by
    by_contra hn
    exact hne' (held_eq_of_le_overgroup_twoCore_ne_bot hheld SQ Y Y hSY le_rfl hn hA' hD')
  let := moved_local_simple_core_quotient hG T hB hm
  obtain ⟨F,_,_,hF,⟨eB⟩⟩ := hseven
  let a : A ≃* B := subgroupOfEquivOfLe hBP
  let da : D ≃* B := (ep.subgroupMap A).symm.trans a
  let aq : (A ⧸ pCore 2 A) ≃* (B ⧸ pCore 2 B) :=
    QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let dq : (D ⧸ pCore 2 D) ≃* (B ⧸ pCore 2 B) :=
    QuotientGroup.congr _ _ da (pCore_map_iso 2 da)
  let : IsSimpleGroup (A ⧸ pCore 2 A) := aq.isSimpleGroup
  let : IsSimpleGroup (D ⧸ pCore 2 D) := dq.isSimpleGroup
  let ae : A' ≃* PSL(2,F) := simple_core_image_equiv g f.rangeRestrict_surjective hcore A hA (aq.trans eB)
  let de : D' ≃* PSL(2,F) := simple_core_image_equiv g f.rangeRestrict_surjective hcore D hD (dq.trans eB)
  let : IsSimpleGroup PSL(2,F) := eB.symm.isSimpleGroup
  let : IsSimpleGroup A' := ae.isSimpleGroup
  let : IsSimpleGroup D' := de.isSimpleGroup
  let := hA'.perfect
  have hc : A' ≤ centralizer (D' : Set Y) := commutator_eq_bot_iff_le_centralizer.mp
    (simple_subnormal_commute_of_ne A' D' hA'.subnormal hD'.subnormal hne')
  have hzA : center A' = ⊥ := by
    apply (inferInstance : (center A').Normal).eq_bot_or_eq_top.resolve_right
    intro ht
    let := hA'.perfect
    exact Group.IsPerfect.not_isMulCommutative A' (center_eq_top_iff.mp ht)
  have hd : Disjoint A' D' := by
    apply disjoint_def.mpr
    intro x hxA hxD
    have hh : (⟨x,hxA⟩ : A') ∈ center A' := mem_center_iff.mpr fun y =>
      Subtype.ext ((hc y.property x hxD).symm)
    exact congrArg Subtype.val (show (⟨x,hxA⟩ : A') = 1 from mem_bot.mp (hzA ▸ hh))
  obtain ⟨pe,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A' D' hd hc
  let W := A' ⊔ D'
  let we : W ≃* (PSL(2,F) × PSL(2,F)) := pe.symm.trans (ae.prodCongr de)
  have hnV : (V.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer
    ((show P ≤ J from inf_le_left).trans
      (sup_le ((le_conjugateSpanBy B (T : Subgroup G)).trans V.le_normalizer)
        (le_normalizer_conjugateSpanBy B (T : Subgroup G))))
  let : W.Normal := by
    change (A.map g ⊔ D.map g).Normal
    rw [←Subgroup.map_sup,hgen]
    exact hnV.map g f.rangeRestrict_surjective
  have hYW : Y ≤ normalizer (W.map Y.subtype : Set (K ⧸ solvableRadical K)) := by
    have hh := W.le_normalizer_map Y.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  obtain ⟨eH⟩ := hheld
  let SH := SQ.mapSurjective (f := eH.toMonoidHom) eH.surjective
  let WH := (W.map Y.subtype).map eH.toMonoidHom
  have hSH : (SH : Subgroup Held.He) ≤ normalizer (WH : Set Held.He) :=
    (map_mono (hSY.trans hYW)).trans ((W.map Y.subtype).le_normalizer_map eH.toMonoidHom)
  let wq : W ≃* W.map Y.subtype := equivMapOfInjective W Y.subtype Y.subtype_injective
  let wh : W.map Y.subtype ≃* WH := eH.subgroupMap (W.map Y.subtype)
  exact held_no_sylow_normalized_seven_square SH WH hSH hF ((wq.trans wh).symm.trans we)

end CFSG.Quasithin.Chapter1.Section02.MovedMaximality
