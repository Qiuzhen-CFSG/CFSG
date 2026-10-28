module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimplePointLine
public import Theory.SpecificGroups.Rudvalis.ComponentFacts
public import Theory.SpecificGroups.Janko4.PerfectCoverActions

/-!
# Original global fixed space in the quasisimple nonsingular branch

A nonidentity vector in the original C_V(L) acts nontrivially on an
escaping K_v, by normalizer uniqueness. If every automorphism of the
central-quotient model is inner, this gives an actual model involution
centralizing the literal images of L_v and V_v. The original T_v fixes
that involution and normalizes both images, so the same quotient Sylow
meets their simultaneous normalizer and centralizer in index at most two.

In Ru, the A6 quotient of the local image contradicts the three-part of
every involution centralizer. In J4, the Sylow bound selects its first
involution centralizer. The original local commutant rigidity and its
extraspecial core then force the moved image to have order at most two,
contrary to its order at least sixteen. Together with the HS result,
this excludes every quasisimple row when the original C_V(L) is nontrivial.

The preferred-point consumer retains the original Sylow position,
component, point line and compatible covering catalogue. Every remaining
quasisimple row has C_V(L)=1, |V|=64 and original action image of order 32.
HS, Ru and J4 with trivial original fixed space, and the subsequent block,
splitting and general fixed-space arguments remain open; neither 12.6.2
nor 12.6.23 is asserted. Earlier invariance/TI retain producer
qt-d-1222-source and final discharge owner qt-d-12634-source.

Source: Aschbacher--Smith, proof of 12.6.12, printed pp.825--826;
GLS3 Tables 5.3i and 5.3r for the native J4 and Ru centralizers.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- A nonzero original global fixed vector supplies an actual inner model involution,
centralizing both literal local images and compatible with the same Sylow bound. -/
theorem SourceHypothesis.nonsingular_global_fixed_inner_geometry
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (hnot : ¬ Kv (v : G) ≤ M L) (hz : ZV L V ≠ ⊥)
    {F : Type*} [Group F] [Finite F]
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* F)
    (j : F ≃* MulAut F) (hj : ∀ x, j x = MulAut.conj x) :
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center (Kv (v : G))))
    let B := ((Lv L (v : G)).subgroupOf (Kv (v : G))).map f
    let W := ((Vv L V (v : G)).subgroupOf (Kv (v : G))).map f
    ∃ t : F, orderOf t = 2 ∧ B ≤ centralizer ({t} : Set F) ∧
      W ≤ centralizer ({t} : Set F) ∧
      ∃ P : Sylow 2 F,
        (normalizer (B : Set F) ⊓ normalizer (W : Set F) ⊓
          centralizer ({t} : Set F)).relIndex (P : Subgroup F) ≤ 2 := by
  let := hK
  let C := Kv (v : G)
  let A := Gv (v : G)
  let a := j.symm.toMonoidHom.comp (nonsingularModelAction (v : G) e)
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center C))
  have ha (x : C) : a (inclusion (Kv_le_Gv (v : G)) x) = f x := by
    change j.symm (nonsingularModelAction (v : G) e (inclusion (Kv_le_Gv (v : G)) x)) = _
    rw [nonsingularModelAction_on_component,←hj,j.symm_apply_apply]
    rfl
  have has : Function.Surjective a := by
    intro y
    obtain ⟨x,rfl⟩ := e.surjective y
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (center C) x
    exact ⟨inclusion (Kv_le_Gv (v : G)) x,ha x⟩
  have hak : a.ker = (centralizer (C : Set G)).subgroupOf A := by
    rw [MonoidHom.ker_comp_of_injective _ _ j.symm.injective,nonsingularModelAction_ker]
  have hmap (U : Subgroup G) (hUC : U ≤ C) :
      (U.subgroupOf A).map a = (U.subgroupOf C).map f := by
    let k := inclusion (Kv_le_Gv (v : G))
    have hU : (U.subgroupOf C).map k = U.subgroupOf A := by
      apply map_injective A.subtype_injective
      rw [map_map]
      change (U.subgroupOf C).map C.subtype = _
      rw [map_subgroupOf_eq_of_le hUC,map_subgroupOf_eq_of_le (hUC.trans (Kv_le_Gv (v : G)))]
    rw [←hU,map_map]
    congr 1
    exact MonoidHom.ext ha
  let B := ((Lv L (v : G)).subgroupOf C).map f
  let W := ((Vv L V (v : G)).subgroupOf C).map f
  have hBC : Lv L (v : G) ≤ C := Lv_le_Kv_of_A6 L _
    (Classical.choice (D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv))
  have hWC : Vv L V (v : G) ≤ C := (H.nonsingular_component_rank D v hv).1
  obtain ⟨z,hzZ,hzne⟩ := (ZV L V).bot_or_exists_ne_one.resolve_left hz
  let zA : A := ⟨z,V_le_Gv v hzZ.1⟩
  let t := a zA
  have htne : t ≠ 1 := by
    intro ht
    have hc : zA ∈ a.ker := ht
    rw [hak] at hc
    have hh : z ∈ ZV L V ⊓ centralizer (C : Set G) := ⟨hzZ,hc⟩
    rw [H.nonsingular_fixed_component_centralizer D v hTV hnot,mem_bot] at hh
    exact hzne hh
  have ht : orderOf t = 2 := orderOf_eq_prime (p := 2) (by
    change a zA ^ 2 = 1
    rw [←map_pow]
    have hz2 : zA^2=1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian _ hzZ.1)
    rw [hz2,map_one]) htne
  have hBt : B ≤ centralizer ({t} : Set F) := by
    rintro _ ⟨b,hb,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    rw [←ha]
    change a _ * a zA = a zA * a _
    rw [←map_mul,←map_mul]
    exact congrArg a (Subtype.ext (mem_centralizer_iff.mp hzZ.2 (b : G) (Lv_le_L L _ hb)))
  have hWt : W ≤ centralizer ({t} : Set F) := by
    rintro _ ⟨w,hw,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    rw [←ha]
    change a _ * a zA = a zA * a _
    rw [←map_mul,←map_mul]
    exact congrArg a (Subtype.ext (setLike_mul_comm
      (Vv_le_V H.chosen.normalizes _ hw) hzZ.1))
  refine ⟨t,ht,hBt,hWt,?_⟩
  let N := normalizer (B : Set F) ⊓ normalizer (W : Set F) ⊓ centralizer ({t} : Set F)
  obtain ⟨S,hTS,_⟩ := exists_sylow_with_Lv_normalizer T L
    H.chosen.sylow_normalizes_component (v : G)
  have hSi := H.nonsingular_quasisimple_sylow_index_le_two D v hv hK hi S hTS
  have hnB : Tv T (v : G) ≤ normalizer (Lv L (v : G) : Set G) :=
    (inf_le_inf H.chosen.sylow_normalizes_component le_rfl).trans (Mv_le_normalizer_Lv L _)
  have hnW : Tv T (v : G) ≤ normalizer (Vv L V (v : G) : Set G) :=
    normalizes_Vv_of_normalizes _ _ (inf_le_left.trans hTV) hnB
  have hnBA : (Tv T (v : G)).subgroupOf A ≤ normalizer ((Lv L (v : G)).subgroupOf A : Set A) := by
    rw [←subgroupOf_normalizer_eq (Lv_le_Gv L (v : G))]
    exact comap_mono hnB
  have hnWA : (Tv T (v : G)).subgroupOf A ≤ normalizer ((Vv L V (v : G)).subgroupOf A : Set A) := by
    rw [←subgroupOf_normalizer_eq (hWC.trans (Kv_le_Gv (v : G)))]
    exact comap_mono hnW
  have hn : (Tv T (v : G)).subgroupOf A ≤ N.comap a := by
    intro x hx
    refine ⟨⟨?_,?_⟩,?_⟩
    · dsimp only [B]
      rw [←hmap _ hBC]
      exact le_normalizer_map a (mem_map_of_mem a (hnBA hx))
    · dsimp only [W]
      rw [←hmap _ hWC]
      exact le_normalizer_map a (mem_map_of_mem a (hnWA hx))
    · apply mem_centralizer_singleton_iff.mpr
      change a x * a zA = a zA * a x
      rw [←map_mul,←map_mul]
      exact congrArg a (Subtype.ext
        (D.join_centralizes_fixed H.chosen hTV (mem_sup_right hx.1) z hzZ).symm)
  refine ⟨S.mapSurjective has,?_⟩
  change N.relIndex ((S : Subgroup A).map a) ≤ 2
  rw [←relIndex_comap]
  apply (relIndex_le_of_le_left hn index_ne_zero_of_finite).trans
  change ((Tv T (v : G)).comap A.subtype).relIndex (S : Subgroup A) ≤ 2
  rw [relIndex_comap]
  exact hSi

/-- Ru cannot occur with nontrivial original fixed space. -/
theorem SourceHypothesis.nonsingular_ru_fixed_eq_bot
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (hnot : ¬ Kv (v : G) ≤ M L)
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Rudvalis.Model) : ZV L V = ⊥ := by
  by_contra hz
  let := hK
  let : IsSimpleGroup ((Kv (v : G)) ⧸ center (Kv (v : G))) := IsQuasisimple.simple
  let : IsSimpleGroup Rudvalis.Model := e.symm.isSimpleGroup
  let j : Rudvalis.Model ≃* MulAut Rudvalis.Model := MulEquiv.ofBijective MulAut.conj
    ⟨MulAut.conj_injective_of_center_eq_bot Rudvalis.LowCentralizers.model_center_eq_bot,
      Rudvalis.component_conj_surjective⟩
  obtain ⟨t,ht,hBt,_,_⟩ := H.nonsingular_global_fixed_inner_geometry D v hv hK hTV hi hnot hz e j
    (fun _ => rfl)
  have hn := Rudvalis.InvolutionCentralizers.centralizer_not_nine t ht
  apply hn
  apply dvd_trans _ (card_dvd_of_le hBt)
  rw [←map_map,card_map_of_injective e.injective]
  obtain ⟨_,⟨eB⟩,_⟩ := H.nonsingular_centralQuotient_local_marking D v hv
  apply dvd_trans _ (card_quotient_dvd_card (pCore 2 _))
  rw [Nat.card_congr eB.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
  decide

/-- The original global fixed involution excludes the remaining central-line J4 case
when the global fixed space is nontrivial. -/
theorem SourceHypothesis.nonsingular_jankoFour_fixed_eq_bot
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (hnot : ¬ Kv (v : G) ≤ M L)
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Janko4.Model) : ZV L V = ⊥ := by
  by_contra hz
  let C := Kv (v : G)
  let q := QuotientGroup.mk' (center C)
  let f := e.toMonoidHom.comp q
  let B := ((Lv L (v : G)).subgroupOf C).map f
  let W := ((Vv L V (v : G)).subgroupOf C).map f
  let j : Janko4.Model ≃* MulAut Janko4.Model := MulEquiv.ofBijective MulAut.conj
    ⟨MulAut.conj_injective_of_center_eq_bot Janko4.model_center_eq_bot,
      Janko4.AdequateLocal.conj_surjective⟩
  obtain ⟨t,ht,hBt,hWt,P,hP⟩ := H.nonsingular_global_fixed_inner_geometry
    D v hv hK hTV hi hnot hz e j (fun _ => rfl)
  obtain ⟨c⟩ := Janko4.InvolutionCentralizers.centralizer_equiv_first_of_sylow_index_le_two
    t ht P ((relIndex_le_of_le_left inf_le_right index_ne_zero_of_finite).trans hP)
  let K := centralizer ({t} : Set Janko4.Model)
  let d : pCore 2 K ≃* pCore 2 Janko4.InvolutionCentralizers.First.centralizer :=
    (c.subgroupMap (pCore 2 K)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 c))
  have hQ : IsExtraspecial 2 (pCore 2 K) := IsExtraspecial.of_mulEquiv
    d.symm Janko4.InvolutionCentralizers.First.centralizer_twoCore_extraspecial
  obtain ⟨hperfect,_,_,_,hele,hmove,_⟩ := H.nonsingular_centralQuotient_local_marking D v hv
  let A := ((Lv L (v : G)).subgroupOf C).map q
  let U := ((Vv L V (v : G)).subgroupOf C).map q
  let : Group.IsPerfect A := hperfect
  let : Group.IsPerfect B := by
    change Group.IsPerfect (((Lv L (v : G)).subgroupOf C).map (e.toMonoidHom.comp q))
    rw [←map_map]
    exact Group.IsPerfect.map e.toMonoidHom
  have heW : IsElementaryAbelian 2 W := by
    let : IsElementaryAbelian 2 U := hele
    change IsElementaryAbelian 2 (((Vv L V (v : G)).subgroupOf C).map (e.toMonoidHom.comp q))
    rw [←map_map]
    exact IsElementaryAbelian.map e.toMonoidHom
  have hm : ⁅W,B⁆ = W := by
    have hWmap : W = U.map e.toMonoidHom := (map_map _ _ _).symm
    have hBmap : B = A.map e.toMonoidHom := (map_map _ _ _).symm
    rw [hWmap,hBmap,←map_commutator,←hmove]
  have hb := moved_card_le_two_in_extraspecial_overgroup P B W K heW hm hBt hWt hQ
    (Janko4.InvolutionCentralizers.centralizer_characteristic_two t ht)
    (H.nonsingular_central_image_core_rigidity D v hv e) hP
  have hc : 16 ≤ Nat.card W := by
    change 16 ≤ Nat.card (((Vv L V (v : G)).subgroupOf C).map (e.toMonoidHom.comp q))
    rw [←map_map,card_map_of_injective e.injective]
    exact H.nonsingular_centralQuotient_moved_card D v hv
  omega

/-- Every escaping quasisimple residual forces the original global fixed space to vanish. -/
theorem SourceHypothesis.nonsingular_quasisimple_fixed_eq_bot
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (hnot : ¬ Kv (v : G) ≤ M L) : ZV L V = ⊥ := by
  obtain ⟨name,hn,⟨e⟩⟩ := H.nonsingular_quasisimple_models_after_held D v hv hK
  rcases hn with rfl | rfl | rfl
  · exact H.nonsingular_hs_fixed_eq_bot D v hv hK hTV hnot e
  · exact H.nonsingular_ru_fixed_eq_bot D v hv hK hTV hi hnot e
  · exact H.nonsingular_jankoFour_fixed_eq_bot D v hv hK hTV hi hnot e

/-- Every remaining quasisimple row acts on the original order-64 module,
with action image of order 32 and kernel the point line. -/
theorem SourceHypothesis.nonsingular_quasisimple_original_card
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (hnot : ¬ Kv (v : G) ≤ M L) :
    Nat.card V = 64 ∧ ∀ {F : Type*} [Group F],
      ∀ e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* F,
        Nat.card ((V.subgroupOf (Gv (v : G))).map
          (nonsingularModelAction (v : G) e)) = 32 := by
  have hz := H.nonsingular_quasisimple_fixed_eq_bot D v hv hK hTV hi hnot
  have hfix : (fixedSeed L V H.chosen.normalizes).toSubmodule = ⊥ := by
    apply bot_unique
    intro w hw
    have hh := (mem_fixedSeed_iff L V H.chosen.normalizes w).mp hw
    rw [hz,mem_bot] at hh
    exact (show w = 0 from Additive.toMul.injective (Subtype.ext hh))
  let q := (fixedSeed L V H.chosen.normalizes).toSubmodule.mkQ
  have hq : Function.Bijective q :=
    ⟨LinearMap.ker_eq_bot.mp (by rw [Submodule.ker_mkQ,hfix]),Submodule.mkQ_surjective _⟩
  let c := (LinearEquiv.ofBijective q hq).trans D.coordinates
  have hV : Nat.card V = 64 := by
    change Nat.card (Additive V) = 64
    rw [Nat.card_congr c.toEquiv,Module.natCard_eq_pow_finrank (K := ZMod 2),
      BinaryPermutation.finrank_natural_even (Fin 8) (by decide),Nat.card_zmod]
    decide
  refine ⟨hV,?_⟩
  intro F _ e
  have hc := H.nonsingular_original_action_card D v hv hK hTV hnot e
  omega

/-- At the actual preferred escaping point, nontrivial fixed space now excludes
quasisimplicity without any extra model or centralizer premise. -/
theorem SourceHypothesis.exists_preferred_nonsingular_nontrivial_fixed_not_quasisimple
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
      Lv L (w : G) < Kv (w : G) ∧ ¬ Kv (w : G) ≤ M L ∧
      ((Kv (w : G)).subgroupOf (Gv (w : G))).IsCComponent ∧
      IsQuasisimple (Star (Kv (w : G))) ∧ IsSimpleGroup (Star (Kv (w : G))) ∧
      V ⊓ centralizer (Kv (w : G) : Set G) = zpowers (w : G) ∧
      (ZV L V ≠ ⊥ → ¬ IsQuasisimple (Kv (w : G))) ∧
      (IsQuasisimple (Kv (w : G)) → ZV L V = ⊥ ∧
        NonsingularRemainingCoverModels (Kv (w : G)) ∧
        ZV (Lv L (w : G)) (Vv L V (w : G)) = zpowers (w : G) ∧
        (w : G) ∈ Vv L V (w : G) ∧
        Nat.card V = 64 ∧ ∀ {F : Type*} [Group F],
          ∀ e : ((Kv (w : G)) ⧸ center (Kv (w : G))) ≃* F,
            Nat.card ((V.subgroupOf (Gv (w : G))).map
              (nonsingularModelAction (w : G) e)) = 32) := by
  obtain ⟨w,hw,he,hs,hi,hlt,hnot,hc,hq,hsimple,hmodels⟩ :=
    H.exists_preferred_nonsingular_central_fixed_line D hTV hTI v hv he
  refine ⟨w,hw,he,hs,hi,hlt,hnot,hc,hq,hsimple,
    H.nonsingular_original_component_centralizer D w hw hTV hnot,?_,?_⟩
  · exact fun hz hK => hz (H.nonsingular_quasisimple_fixed_eq_bot D w hw hK hTV hi hnot)
  · intro hK
    obtain ⟨hline,hwW⟩ := H.nonsingular_quasisimple_point_line D w hw hK hTV hi hnot
    exact ⟨H.nonsingular_quasisimple_fixed_eq_bot D w hw hK hTV hi hnot,
      (hmodels hK).1,hline,hwW,H.nonsingular_quasisimple_original_card D w hw hK hTV hi hnot⟩

end CFSG.Quasithin.Chapter12.Section06
