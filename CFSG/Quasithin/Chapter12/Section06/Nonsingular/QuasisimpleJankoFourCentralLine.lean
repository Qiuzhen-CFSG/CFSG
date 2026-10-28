module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleJankoFour
public import Theory.GroupAction.ExtraspecialSmallNormalizer

/-!
# The original fixed line is central in the remaining J₄ branch

If the original generator of C_{V_v}(L_v) survives the central projection,
its image lies in the first native J₄ involution centralizer and the image
of V_v still has order 32. The same model Sylow meets the simultaneous
normalizer and that centralizer in index at most two.

Transport the original six-letter commutant rigidity through the literal
central map. Perfectness lifts normalization of L_v; full movement lifts
normalization of V_v. The extraspecial core bound then puts its image in
a group of order two, contradicting 32. Thus the original fixed line is
central in K_v. It is exactly the projection kernel on V_v, whose image
has order sixteen.

The final consumer combines this with the checked HS and Ru results at
the original preferred escaping point. Every remaining quasisimple row
now has a central original fixed line and the same order-sixteen moved
image. The central-line J₄ case, HS/Ru exclusions, block construction,
splitting and fixed-space elimination remain; neither 12.6.2 nor 12.6.23
is asserted. Earlier invariance and TI retain producer qt-d-1222-source
and final discharge owner qt-d-12634-source.

Source: Aschbacher--Smith, paragraph preceding 12.6.6 and proof of 12.6.12,
printed pp.824--826; GLS3 Table 5.3i for the native J₄ centralizer.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The actual six-letter rigidity survives the literal central quotient and model map. -/
theorem SourceHypothesis.nonsingular_central_image_core_rigidity
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    {F : Type*} [Group F] [Finite F]
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* F) :
    let C := Kv (v : G)
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center C))
    let B := ((Lv L (v : G)).subgroupOf C).map f
    let W := ((Vv L V (v : G)).subgroupOf C).map f
    ∀ r ∈ normalizer (B : Set F) ⊓ normalizer (W : Set F),
      (∀ b ∈ B, ⁅r,b⁆ ∈ B.pCoreIn 2) → r ∈ centralizer (W : Set F) := by
  let C := Kv (v : G)
  let A := (Lv L (v : G)).subgroupOf C
  let W := (Vv L V (v : G)).subgroupOf C
  let q := QuotientGroup.mk' (center C)
  let f := e.toMonoidHom.comp q
  obtain ⟨eA⟩ := D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv
  have hLC : Lv L (v : G) ≤ C := Lv_le_Kv_of_A6 L (v : G) eA
  have hWC : Vv L V (v : G) ≤ C := (Vv_le_Lv H.chosen v).trans hLC
  let a : A ≃* Lv L (v : G) := subgroupOfEquivOfLe hLC
  let : Group.IsPerfect (Lv L (v : G)) := Lv_isPerfect_of_A6 L (v : G) eA
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective (f := a.symm.toMonoidHom) a.symm.surjective
  let aQ : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans eA
  have hc : center (A ⧸ pCore 2 A) = ⊥ := by
    apply bot_unique
    intro x hx
    have he : aQ x ∈ center (alternatingGroup (Fin 6)) := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨z,rfl⟩ := aQ.surjective y
      simpa only [map_mul] using congrArg aQ (mem_center_iff.mp hx z)
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at he
    exact mem_bot.mpr (aQ.injective (he.trans aQ.map_one.symm))
  have hkp : IsPGroup 2 (f.subgroupMap A).ker := by
    apply pCore_isPGroup.to_le
    intro x hx
    apply CentralQuotientLocalMarking.subgroupMap_ker_le_pCore 2 A hc
    apply Subtype.ext
    apply e.injective
    exact (congrArg Subtype.val hx).trans e.map_one.symm
  have hk : f.ker ≤ center C := by
    intro x hx
    apply (QuotientGroup.eq_one_iff _).mp
    exact e.injective (hx.trans e.map_one.symm)
  have hm : ⁅W,A⁆ = W := by
    apply map_injective C.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hWC,map_subgroupOf_eq_of_le hLC]
    exact D.local_moved_generated H.chosen v hv
  have hfix : ∀ r ∈ normalizer (Lv L (v : G) : Set G) ⊓
      normalizer (Vv L V (v : G) : Set G),
      (∀ b ∈ Lv L (v : G), ⁅r,b⁆ ∈ (Lv L (v : G)).pCoreIn 2) →
      r ∈ centralizer (Vv L V (v : G) : Set G) := by
    intro r hr hcomm
    exact D.local_moved_centralizer H.chosen H.source.quasisimple v hv
      ⟨(mem_coreQuotientCentralizer_iff _ _).mpr ⟨hr.1,hcomm⟩,hr.2⟩
  exact core_rigidity_central_image f (e.surjective.comp (QuotientGroup.mk'_surjective _))
    hk A W hkp hm (core_rigidity_subgroupOf C _ _ hLC hWC hfix)

/-- The first-centralizer alternative contradicts the original order-32 moved image. -/
theorem SourceHypothesis.nonsingular_jankoFour_fixed_line_central
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Janko4.Model) :
    ∃ z : Kv (v : G), orderOf (z : G) = 2 ∧
      ZV (Lv L (v : G)) (Vv L V (v : G)) = zpowers (z : G) ∧
      z ∈ center (Kv (v : G)) := by
  let C := Kv (v : G)
  let q := QuotientGroup.mk' (center C)
  let f := e.toMonoidHom.comp q
  let B := ((Lv L (v : G)).subgroupOf C).map f
  let W := ((Vv L V (v : G)).subgroupOf C).map f
  obtain ⟨z,hz,hline,hzcase⟩ :=
    H.nonsingular_jankoFour_fixed_line_placement D v hv hK hTV hi e
  refine ⟨z,hz,hline,?_⟩
  rcases hzcase with hzcent | ⟨hft,⟨c⟩,hBC,hWC,hcard,P,hP⟩
  · exact hzcent
  exfalso
  let K := centralizer ({f z} : Set Janko4.Model)
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
  have hb := moved_card_le_two_in_extraspecial_overgroup P B W K heW hm hBC hWC hQ
    (Janko4.InvolutionCentralizers.centralizer_characteristic_two (f z) hft)
    (H.nonsingular_central_image_core_rigidity D v hv e) hP
  change Nat.card W = 32 at hcard
  omega
end CFSG.Quasithin.Chapter12.Section06

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- In the remaining J₄ branch the projection kills exactly the original
local fixed line on V_v, so its literal moved image has order sixteen. -/
theorem SourceHypothesis.nonsingular_jankoFour_moved_image_card
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Janko4.Model) :
    let C := Kv (v : G)
    (ZV (Lv L (v : G)) (Vv L V (v : G))).subgroupOf C ≤ center C ∧
      Nat.card (((Vv L V (v : G)).subgroupOf C).map
        (QuotientGroup.mk' (center C))) = 16 := by
  let C := Kv (v : G)
  let W := Vv L V (v : G)
  let Z := ZV (Lv L (v : G)) W
  obtain ⟨z,_,hline,hzc⟩ := H.nonsingular_jankoFour_fixed_line_central D v hv hK hTV hi e
  have hZC : Z.subgroupOf C ≤ center C := by
    intro x hx
    have hx' : (x : G) ∈ zpowers (z : G) := hline ▸ hx
    obtain ⟨n,hn⟩ := mem_zpowers_iff.mp hx'
    have he : z^n=x := Subtype.ext hn
    rw [←he]
    exact zpow_mem hzc n
  refine ⟨hZC,?_⟩
  have hWC : W ≤ C := (H.nonsingular_component_rank D v hv).1
  have hLC : Lv L (v : G) ≤ C := Lv_le_Kv_of_A6 L _
    (Classical.choice (D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv))
  let f := (QuotientGroup.mk' (center C)).comp (inclusion hWC)
  have hk : f.ker = Z.subgroupOf W := by
    ext w
    change QuotientGroup.mk' (center C) (inclusion hWC w) = 1 ↔ (w : G) ∈ Z
    constructor
    · intro hz
      have hz := (QuotientGroup.eq_one_iff _).mp hz
      refine ⟨w.property,?_⟩
      intro b hb
      exact congrArg Subtype.val (mem_center_iff.mp hz ⟨b,hLC hb⟩)
    · intro hz
      exact (QuotientGroup.eq_one_iff _).mpr (hZC hz)
  have hc := f.ker.card_mul_index
  rw [index_ker,hk,Nat.card_congr (subgroupOfEquivOfLe (show Z ≤ W from inf_le_left)).toEquiv,
    D.nonsingular_moved_fixed_card H.chosen v hv,D.nonsingular_moved_card H.chosen v hv] at hc
  have hr : Nat.card f.range = 16 := by omega
  simpa only [f,MonoidHom.range_comp,inclusion_range] using hr

/-- At the actual preferred escaping point, every surviving quasisimple
model kills the original fixed line; its moved central-quotient image has
order sixteen. The HS/Ru and central-line J₄ exclusions remain required. -/
theorem SourceHypothesis.exists_preferred_nonsingular_central_fixed_line
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
      (IsQuasisimple (Kv (w : G)) →
        NonsingularRemainingCoverModels (Kv (w : G)) ∧
        (ZV (Lv L (w : G)) (Vv L V (w : G))).subgroupOf (Kv (w : G)) ≤
          center (Kv (w : G)) ∧
        Nat.card (((Vv L V (w : G)).subgroupOf (Kv (w : G))).map
          (QuotientGroup.mk' (center (Kv (w : G))))) = 16) := by
  obtain ⟨w,hw,he,hs,hi,hlt,hnot,hc,hq,hsimple,hmodels⟩ :=
    H.exists_preferred_nonsingular_quasisimple_strict_sylow D hTV hTI v hv he
  refine ⟨w,hw,he,hs,hi,hlt,hnot,hc,hq,hsimple,?_⟩
  intro hK
  refine ⟨(hmodels hK).1,?_⟩
  obtain ⟨name,hn,hmodel⟩ := H.nonsingular_quasisimple_models_after_held D w hw hK
  rcases hn with rfl | rfl | rfl
  · exact ⟨(H.nonsingular_hs_fixed_line_eq_center D w hw hK hmodel).le,
      H.nonsingular_hs_moved_image_card D w hw hmodel⟩
  · exact ⟨H.nonsingular_ru_fixed_line_le_center D w hw hmodel,
      H.nonsingular_ru_moved_image_card D w hw hmodel⟩
  · exact H.nonsingular_jankoFour_moved_image_card D w hw hK hTV hi (Classical.choice hmodel)
end CFSG.Quasithin.Chapter12.Section06
