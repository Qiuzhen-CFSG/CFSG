module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeLargerInvariantModels
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeCommonSylow
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeJankoFourNonA5
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityActualPairGeometry

/-!
# The common overcomponent of an actual moved right component is moved

At the larger changed Sylow, retain the actual H-component R and the
unique common overcomponent I in X = ⟨N_G(T₀), H⟩. If T preserves I,
the two original conjugate components give a full-Sylow invariant square
in I modulo its solvable radical. The source model sieve leaves only J₄,
Held and Rudvalis. The square's order excludes J₄; the literal involution
centralizers exclude the A₅ squares in Held and Rudvalis. The non-A₅
rows were already excluded by source 1.2.8.

Thus T moves I. The existing common-orbit calculation now applies
unconditionally to the actual-component branch, with the same Sylow
intersections and the J₁/odd-prime PSL₂ containing models. The selected
parabolic branch is kept separate throughout. Source: Aschbacher–Smith
1.2.8 and 5.2.2, printed pp.506–507 and 648–649, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open Chapter1.Section02.MovedMaximality
open Theory.SpecificGroups.Alternating
variable {G : Type*} [Group G] [Finite G]
namespace LargerInvariant

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

private theorem actual_pair_five_square
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ Chapter1.L G (T : Subgroup G)) (hBK : B ≤ K)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : B < conjugateSpanBy B (T : Subgroup G))
    (hfour : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4)
    (hmodels : Nonempty ((K ⧸ solvableRadical K) ≃* Held.He) ∨
      Nonempty ((K ⧸ solvableRadical K) ≃* Rudvalis.Model)) :
    ∃ (S : Sylow 2 (K ⧸ solvableRadical K)) (W : Subgroup (K ⧸ solvableRadical K)),
      (S : Subgroup (K ⧸ solvableRadical K)) ≤ normalizer (W : Set _) ∧
      Nonempty (W ≃* FiveSquareAutomorphisms.Pair) := by
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
    have hQ := Chapter1.Section02.uniqueness_local_quotient_sqtk hG hB.2.2
    rcases Chapter1.Section02.proposition_1_2_1_three_index_knownSimple hQ hB.1 with hn | ⟨hi,_⟩
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
    rcases hmodels with hh | hr
    · exact hne' (held_eq_of_le_overgroup_twoCore_ne_bot hh SQ Y Y hSY le_rfl hn hA' hD')
    · exact hne' (rudvalis_eq_of_le_overgroup_twoCore_ne_bot hr SQ Y Y hSY le_rfl hn hA' hD')
  let := moved_local_simple_core_quotient hG T hB hm
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hfour
  let eB := eF.trans (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some
  let a : A ≃* B := subgroupOfEquivOfLe hBP
  let da : D ≃* B := (ep.subgroupMap A).symm.trans a
  let aq : (A ⧸ pCore 2 A) ≃* (B ⧸ pCore 2 B) :=
    QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let dq : (D ⧸ pCore 2 D) ≃* (B ⧸ pCore 2 B) :=
    QuotientGroup.congr _ _ da (pCore_map_iso 2 da)
  let : IsSimpleGroup (A ⧸ pCore 2 A) := aq.isSimpleGroup
  let : IsSimpleGroup (D ⧸ pCore 2 D) := dq.isSimpleGroup
  let ae : A' ≃* alternatingGroup (Fin 5) := simple_core_image_equiv g f.rangeRestrict_surjective hcore A hA (aq.trans eB)
  let de : D' ≃* alternatingGroup (Fin 5) := simple_core_image_equiv g f.rangeRestrict_surjective hcore D hD (dq.trans eB)
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := eB.symm.isSimpleGroup
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
  let we : W ≃* (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) := pe.symm.trans (ae.prodCongr de)
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
  let wq : W ≃* W.map Y.subtype := equivMapOfInjective W Y.subtype Y.subtype_injective
  exact ⟨SQ,W.map Y.subtype,hSY.trans hYW,⟨wq.symm.trans we⟩⟩

private theorem actual_pair_not_held_or_rudvalis
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ Chapter1.L G (T : Subgroup G)) (hBK : B ≤ K)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : B < conjugateSpanBy B (T : Subgroup G))
    (hfour : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4)
    (hmodels : Nonempty ((K ⧸ solvableRadical K) ≃* Held.He) ∨
      Nonempty ((K ⧸ solvableRadical K) ≃* Rudvalis.Model)) : False := by
  obtain ⟨S,W,hn,⟨e⟩⟩ := actual_pair_five_square hG T hB hBK hTK hm hfour hmodels
  rcases hmodels with hh | hr
  · obtain ⟨a⟩ := hh
    exact held_no_square (S.mapSurjective (f := a.toMonoidHom) a.surjective)
      (W.map a.toMonoidHom)
      ((map_mono (f := a.toMonoidHom) hn).trans (W.le_normalizer_map a.toMonoidHom))
      ((a.subgroupMap W).symm.trans e)
  · obtain ⟨a⟩ := hr
    exact rudvalis_no_square (S.mapSurjective (f := a.toMonoidHom) a.surjective)
      (W.map a.toMonoidHom)
      ((map_mono (f := a.toMonoidHom) hn).trans (W.le_normalizer_map a.toMonoidHom))
      ((a.subgroupMap W).symm.trans e)

/-- A moved member of the full-Sylow local family has no containing
local component normalized by that Sylow, including the A₅ exception. -/
theorem normalized_chain_impossible
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ Chapter1.L G (T : Subgroup G)) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hBK : B ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : B < conjugateSpanBy B (T : Subgroup G)) : False := by
  by_cases hfour : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4
  · let C := K.subgroupOf (K ⊔ (T : Subgroup G))
    let Q := C ⧸ solvableRadical C
    obtain ⟨hs,_,hmodel,hu⟩ := moved_normalized_remaining_simple_quotient hG T hB hK hBK hTK hm
    let := hs
    let := hK.1.perfect
    rcases hmodel with (ha | ha) | ⟨p,hp,ho,unitary,ho3⟩ | hr | hb | hspor
    · exact hu (alternating_seven_sylow_overgroup_component_unique ha)
    · exact hu (even_sylow_overgroup_component_unique (Or.inr (Or.inr ha)))
    · exact hu (odd_ternary_sylow_overgroup_component_unique hp ho unitary ho3)
    · exact hu (even_sylow_overgroup_component_unique (Or.inl hr))
    · exact hu (even_sylow_overgroup_component_unique (Or.inr (Or.inl hb)))
    · obtain ⟨name,hn,iso⟩ := sporadic_model_remaining_after_higman_sims hspor hu
      let eK : K ≃* C := (subgroupOfEquivOfLe
        (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left)).symm
      let eQ : (K ⧸ solvableRadical K) ≃* Q :=
        QuotientGroup.congr _ _ eK (map_solvableRadical_equiv eK)
      rcases hn with rfl | rfl | rfl
      · have hd := actual_pair_twoCore_square_dvd hG T hB hBK hTK hm
        obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hfour
        let a := eF.trans (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some
        have hc : Nat.card (B ⧸ pCore 2 B) = 60 := by
          rw [Nat.card_congr a.toEquiv,nat_card_alternatingGroup]
          norm_num [Nat.factorial]
        rw [hc,Nat.card_congr (eQ.trans iso.some).toEquiv] at hd
        change 60^2 ∣ Nat.card Janko4.Model at hd
        rw [Janko4.Cardinality.model_card] at hd
        norm_num at hd
      · exact actual_pair_not_held_or_rudvalis hG T hB hBK hTK hm hfour
          (.inl ⟨eQ.trans iso.some⟩)
      · exact actual_pair_not_held_or_rudvalis hG T hB hBK hTK hm hfour
          (.inr ⟨eQ.trans iso.some⟩)
  · exact actual_pair_normalized_chain_impossible hG T hB hK hBK hTK hm hfour

end LargerInvariant

/-- The common overcomponent of the actual moved H-component cannot be
preserved by the original full Sylow, including the exceptional A₅ row. -/
theorem LocalData.common_component_not_normalized
    {T : Sylow 2 G} {L W H A B D R I : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hC : (R.subgroupOf H).IsCComponent) (hRI : R ≤ I)
    (hIX : I ≤ normalizer (normalizingSylow T R : Set G) ⊔ H)
    (hI : (I.subgroupOf (normalizer (normalizingSylow T R : Set G) ⊔ H)).IsCComponent) :
    ¬ (T : Subgroup G) ≤ normalizer (I : Set G) := by
  intro hn
  have hTX : (T : Subgroup G) ≤ normalizer (normalizingSylow T R : Set G) ⊔ H :=
    (show (T : Subgroup G) ≤ H from hH.1.1.2).trans le_sup_right
  have hlocal : I ∈ Chapter1.L G (T : Subgroup G) :=
    Chapter1.mem_L_of_cComponent (d.common_normal_overgroup h hH c hd hz).1
      ⟨T.subtype hTX,map_subgroupOf_eq_of_le hTX⟩ hIX hI
  apply LargerInvariant.normalized_chain_impossible h.qtke T
    (d.right_mem_original_local_family hH.1.1 hC) hlocal hRI hn
  rw [←d.residual_eq_conjugateSpan]
  exact d.right_lt_residual hH.1.1.2 c hd hz

/-- For an actual H-component at a larger changed Sylow, its common
container is moved and has the J₁ or odd-prime PSL₂ quotient. The two
Sylow intersections with its whole orbit are literally equal. -/
theorem LocalData.largerSylow_actual_component_container
    {T U : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hs : SelectedSourceModels H R) (hC : (R.subgroupOf H).IsCComponent)
    (P : Sylow 2 (extension T L H B D R))
    (hTP : normalizingSylow T R ≤
      (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype)
    (hU : (U : Subgroup G) =
      (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype) :
    let X := normalizer (normalizingSylow T R : Set G) ⊔ H
    ∃ I : Subgroup G, R < I ∧ I ≤ X ∧ (I.subgroupOf X).IsCComponent ∧
      ¬ (T : Subgroup G) ≤ normalizer (I : Set G) ∧
      (T : Subgroup G) ⊓ normalizer (I : Set G) = normalizingSylow T R ∧
      (U : Subgroup G) ⊓ normalizer (I : Set G) = normalizingSylow T R ∧
      (U : Subgroup G) ⊓ conjugateSpanBy I (T : Subgroup G) =
        (T : Subgroup G) ⊓ conjugateSpanBy I (T : Subgroup G) ∧
      (Nonempty ((I ⧸ pCore 2 I) ≃* Janko1.Model) ∨
        ∃ q : ℕ, q.Prime ∧ Odd q ∧ ClassicalGroup.IsPSL (I ⧸ pCore 2 I) 2 q) := by
  obtain ⟨I,hRI,hIX,hI,hTI,hu,_⟩ :=
    d.changedSylow_common_orbit_strict h hH c hd hz P hTP hU
  have hm := d.common_component_not_normalized h hH c hd hz hC hRI.le hIX hI
  obtain ⟨hTN,_,hinter,_,hUN⟩ := d.changedSylow_moved_common_intersections h hH c hd hz
    (hTP.trans_eq hU.symm) hIX hI hTI hm
  have hmodels := (d.moved_common_component_models h hH hgen hthree c hd hz hs
    hRI hIX hI hu hm).2.2.2.2
  exact ⟨I,hRI,hIX,hI,hm,hTN,hUN,hinter,hmodels⟩

/-- Retain the original selected pair and its two remaining alternatives.
In the actual-component larger-Sylow branch, the common container is now
necessarily moved; its J₁/odd-prime PSL₂ model and both Sylow intersections
are consequences, not additional source assumptions. -/
theorem source_prime_pair_larger_moved_container
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    ∃ R : Subgroup G, LocalData T L H B D R ∧ SelectedSourceModels H R ∧
      (((generated L H D R).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)) ∨
       ((generated L H D R).pCoreIn 2 ≠ ⊥ ∧
        ¬ D ≤ normalizer (R : Set G) ∧
        (normalizingSylow T R).relIndex (T : Subgroup G) = 2 ∧
        (ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 → p = 5 ∧ n ≠ 2) ∧
        ∃ P : Sylow 2 (extension T L H B D R),
          let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
          normalizingSylow T R < T₁ ∧
          T₁ ≤ normalizer ((D ⊔ normalizingSylow T R : Subgroup G) : Set G) ∧
          ∃ U : Sylow 2 G, (U : Subgroup G) = T₁ ∧ RemainingLargerSource H R p n ∧
            ((R.subgroupOf H).IsCComponent →
              let X := normalizer (normalizingSylow T R : Set G) ⊔ H
              ∃ I : Subgroup G, R < I ∧ I ≤ X ∧ (I.subgroupOf X).IsCComponent ∧
                ¬ (T : Subgroup G) ≤ normalizer (I : Set G) ∧
                (T : Subgroup G) ⊓ normalizer (I : Set G) = normalizingSylow T R ∧
                (U : Subgroup G) ⊓ normalizer (I : Set G) = normalizingSylow T R ∧
                (U : Subgroup G) ⊓ conjugateSpanBy I (T : Subgroup G) =
                  (T : Subgroup G) ⊓ conjugateSpanBy I (T : Subgroup G) ∧
                (Nonempty ((I ⧸ pCore 2 I) ≃* Janko1.Model) ∨
                  ∃ q : ℕ, q.Prime ∧ Odd q ∧ ClassicalGroup.IsPSL (I ⧸ pCore 2 I) 2 q)))) := by
  obtain ⟨R,d,hs,hcases⟩ := source_prime_pair_zero_or_largerSylow h hH hgen hthree c hd
  refine ⟨R,d,hs,?_⟩
  rcases hcases with hz | ⟨hz,hD,hi,hA5,P,hlt,hDT,U,hU,hr⟩
  · exact .inl hz
  exact .inr ⟨hz,hD,hi,hA5,P,hlt,hDT,U,hU,hr,fun hC =>
    d.largerSylow_actual_component_container h hH hgen hthree c hd hz hs hC P hlt.le hU⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
