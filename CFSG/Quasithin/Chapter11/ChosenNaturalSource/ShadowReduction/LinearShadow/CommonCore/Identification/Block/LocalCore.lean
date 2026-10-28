module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification.Block.Thompson
public import Theory.SpecificGroups.PSL3.LinearThreeLocalCoordinates
public import Theory.ThreeSubgroups
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import Theory.GroupTheory.CommutatorPreimage.Membership

/-!
# Recovering the original plane-local two-core

The actual inner Sylow normalizer lifts diag(t,t,t⁻²). It preserves P=J(PV)
and centralizes the quotient action of L₂ on V₂. Perfection and the
three-subgroup lemma imply [L₂,d]≤P. Since t⁻²≠1 for a nonidentity t in
the binary field, its action on PV/P puts O₂(L₂) in P. This also applies
when q=4. Conversely the full radical image lifts every element of P into
O₂(L₂), and plane transitivity places the remaining V₂ kernel there.

All conjugations, residuals and quotient maps are those of the original
chosen module and its marked flag.

Source: Aschbacher--Smith, refs/quasithin.pdf, printed p.774,
the final sentence of the third paragraph.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Matrix
open scoped IsMulCommutative commutatorElement MatrixGroups
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
namespace CoreRecovery
open SL3.PlaneAction SL3.RadicalAction Matrix.PSL3.LinearThree
variable {F : Type*} [Field F]

def planeScalar (t : Fˣ) : SL(3,F) :=
  ⟨Matrix.diagonal ![(t : F),(t : F),((t⁻¹ : Fˣ) : F)^2], by
    simp [Matrix.det_diagonal,Fin.prod_univ_three,pow_two,mul_assoc]⟩

theorem planeScalar_inv (t : Fˣ) : (planeScalar t)⁻¹ = planeScalar t⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeScalar,Matrix.diagonal_mul,Matrix.mul_diagonal,pow_two,mul_assoc]

theorem planeScalar_borel [Finite F] (t : Fˣ) : planeScalar t ∈ borelSL F := by
  rw [mem_borelSL_iff]
  simp [planeScalar]

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

theorem aligned_innerSylow :
    ((T : Subgroup G).subgroupOf L).map (alignedQuotient D S a) =
      unipotentSL S.field.Carrier := by
  rw [alignedQuotient,←Subgroup.map_map,←SL3.innerSylow_eq,←SL3.alignment_sylow,
    Subgroup.map_map]
  have he : (MulAut.conj (SL3.alignment D S a)⁻¹).toMonoidHom.comp
      (MulAut.conj (SL3.alignment D S a)).toMonoidHom = MonoidHom.id _ := by
    ext x : 1
    simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,MonoidHom.id_apply]
    group
  rw [he,Subgroup.map_id]

/-- The original inner Sylow normalizer lifts the scalar-plane torus element. -/
theorem exists_planeScalar_lift (t : S.field.Carrierˣ) :
    ∃ d : L, (d : G) ∈ cartanNormalizer T L ∧ alignedQuotient D S a d = planeScalar t := by
  let R := (SL3.coordinates D S a).innerSylow
  have hm : (R : Subgroup L).map (alignedQuotient D S a) = unipotentSL S.field.Carrier := by
    rw [Coordinates.innerSylow_coe]
    exact aligned_innerSylow D S a
  have hn : planeScalar t ∈ (normalizer (R : Set L)).map (alignedQuotient D S a) := by
    rw [R.normalizer_map_surjective _ (alignedQuotient_surjective D S a),hm]
    exact borelSL_le_normalizer_unipotentSL _ (planeScalar_borel t)
  obtain ⟨d,hd,he⟩ := hn
  refine ⟨d,?_,he⟩
  rw [←componentNormalizer_map R (Coordinates.innerSylow_coe _)]
  exact mem_map_of_mem L.subtype hd

private theorem local_normalized_by_cartanNormalizer :
    cartanNormalizer T L ≤ normalizer ((SL3.flag D S a).Li 1 : Set G) := by
  let N := L ⊓ normalizer ((SL3.flag D S a).Vi 1 : Set G)
  have hn : cartanNormalizer T L ≤ N := le_inf inf_le_left
    ((SL3.flag D S a).normalizer_le_flag_normalizer (SL3.flag_inner_unique D S a) 1)
  exact hn.trans (N.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image N (solvableResidual N)))

private theorem planeProjection_entry (l : (SL3.flag D S a).Li 1) (i j : Fin 2) :
    (planeProjection D S a l).val i j =
      (alignedQuotient D S a ⟨l,(localResidual_le _ l.property).1⟩).val
        i.castSucc j.castSucc := by
  change (lineLocalAffineEquiv S.field.Carrier (localProjection D S a 1 l)).right.val i j = _
  rw [lineLocalAffineEquiv_right_val,localProjection_coe]
  fin_cases i <;> fin_cases j <;> rfl

/-- Scalar action on the plane commutes with the original local quotient action. -/
theorem scalar_commutator_le_core (d : L) (hd : (d : G) ∈ cartanNormalizer T L)
    (t : S.field.Carrierˣ) (ht : alignedQuotient D S a d = planeScalar t) :
    ⁅(SL3.flag D S a).Li 1,zpowers (d : G)⁆ ≤ ((SL3.flag D S a).Li 1).pCoreIn 2 := by
  let J := (SL3.flag D S a).Li 1
  let α : MulAut J := J.normalizerMonoidHom ⟨d,local_normalized_by_cartanNormalizer D S a hd⟩
  have hproj (l : J) : planeProjection D S a (α l) = planeProjection D S a l := by
    apply Subtype.ext
    ext i j
    rw [planeProjection_entry,planeProjection_entry]
    have he : (⟨(α l : G),(localResidual_le _ (α l).property).1⟩ : L) =
        d * (⟨l,(localResidual_le _ l.property).1⟩ : L) * d⁻¹ := rfl
    rw [he,map_mul,map_mul,map_inv,ht,planeScalar_inv]
    fin_cases i <;> fin_cases j <;>
      simp [planeScalar,SpecialLinearGroup.coe_mul,Matrix.diagonal_mul,Matrix.mul_diagonal,mul_assoc,mul_comm,mul_left_comm]
  have hgen : ∀ l ∈ J, ⁅(d : G),l⁆ ∈ J.pCoreIn 2 := by
    intro l hl
    have hh : α ⟨l,hl⟩ * (⟨l,hl⟩ : J)⁻¹ ∈ pCore 2 J := by
      rw [←planeProjection_ker]
      change planeProjection D S a (α ⟨l,hl⟩ * (⟨l,hl⟩ : J)⁻¹) = 1
      rw [map_mul,map_inv,hproj,mul_inv_cancel]
    exact mem_map_of_mem J.subtype hh
  let N := normalizer (J.pCoreIn 2 : Set G)
  have hn : (d : G) ∈ N := (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
    (local_normalized_by_cartanNormalizer D S a hd)
  have hm : zpowers (d : G) ≤ commutatorPreimage N J (J.pCoreIn 2) :=
    zpowers_le.mpr ((mem_commutatorPreimage_iff N J (J.pCoreIn 2) le_rfl d).mpr ⟨hn,hgen⟩)
  rw [commutator_comm]
  exact (commutator_mono hm le_rfl).trans (commutator_commutatorPreimage_le N J _ le_rfl)

def displacement (l : L) (v : V) : V :=
  V.normalizerMonoidHom (inclusion D.normalizes l) v * v⁻¹

theorem displacement_coordinates (l : L) (v : V) :
    (vectorEquiv D S a (displacement D l v)).toAdd =
      (alignedQuotient D S a l).val *ᵥ (vectorEquiv D S a v).toAdd -
        (vectorEquiv D S a v).toAdd := by
  rw [displacement,map_mul,map_inv]
  change (vectorEquiv D S a (V.normalizerMonoidHom _ v)).toAdd +
    -(vectorEquiv D S a v).toAdd = _
  rw [←sub_eq_add_neg]
  have he := alignedAction_projection D S a (inclusion le_sup_left l) v
  rw [alignedAction_component] at he
  exact congrArg (fun w => w - (vectorEquiv D S a v).toAdd) he

theorem local_seed_commutator :
    ⁅(SL3.flag D S a).Li 1,V⁆ ≤ (SL3.flag D S a).Vi 1 := by
  apply commutator_le.mpr
  intro l hl v hv
  let l' : (SL3.flag D S a).Li 1 := ⟨l,hl⟩
  let lL : L := ⟨l,(localResidual_le _ hl).1⟩
  have hrow := (mem_lineLocalSL_iff S.field.Carrier _).mp
    (localProjection D S a 1 l').property
  rw [localProjection_coe] at hrow
  change (displacement D lL ⟨v,hv⟩ : G) ∈ (SL3.flag D S a).Vi 1
  apply (vectorEquiv_mem_plane D S a _).mpr
  rw [displacement_coordinates]
  simp [Matrix.mulVec,dotProduct,Fin.sum_univ_three,hrow.1,hrow.2.1,hrow.2.2,lL,l']

/-- The original plane lies in the intrinsic two-core of its local residual. -/
theorem plane_le_local_core (hcore : L.pCoreIn 2 = V) :
    (SL3.flag D S a).Vi 1 ≤ ((SL3.flag D S a).Li 1).pCoreIn 2 := by
  let B := (SL3.flag D S a).Vi 1
  let J := (SL3.flag D S a).Li 1
  let e := planeEquiv D S a
  have hBN : B ≤ normalizer (J : Set G) :=
    (D.centralQuotientPreimage_le _).trans (hcore ▸ core_normalizes_local D S a 1)
  have hBJ : B ≤ J := by
    let v : Additive B := e.symm ![1,0]
    let w : Additive B := e.symm ![0,1]
    have hv : v ≠ 0 := by
      intro hz
      have he := congrArg e hz
      have h0 := congrFun he 0
      simp [v] at h0
    have hw : w ≠ 0 := by
      intro hz
      have he := congrArg e hz
      have h1 := congrFun he 1
      simp [w] at h1
    obtain ⟨l,hl⟩ := plane_nonzero_transitive D S a v w hv hw
    let c : B := w.toMul * v.toMul⁻¹
    have hcJ : (c : G) ∈ J := by
      have hconj := congrArg (fun z : Additive B => (z.toMul : G)) hl
      change (l : G) * (v.toMul : G) * (l : G)⁻¹ = (w.toMul : G) at hconj
      change (w.toMul : G) * (v.toMul : G)⁻¹ ∈ J
      rw [←hconj]
      simpa only [mul_assoc] using J.mul_mem l.property
        ((mem_normalizer_iff.mp (hBN v.toMul.property) _).mp (J.inv_mem l.property))
    have hc0 : Additive.ofMul c ≠ 0 := by
      intro hz
      have he := congrArg e hz
      have h1 := congrFun he 1
      change e (w + -v) 1 = e 0 1 at h1
      simp [w,v] at h1
    intro b hb
    by_cases hb1 : b = 1
    · exact hb1 ▸ J.one_mem
    have hb0 : Additive.ofMul (⟨b,hb⟩ : B) ≠ 0 := by
      intro he
      exact hb1 (congrArg (fun z : Additive B => (z.toMul : G)) he)
    obtain ⟨k,hk⟩ := plane_nonzero_transitive D S a (Additive.ofMul c)
      (Additive.ofMul (⟨b,hb⟩ : B)) hc0 hb0
    have he := congrArg (fun z : Additive B => (z.toMul : G)) hk
    change (k : G) * (c : G) * (k : G)⁻¹ = b at he
    exact he ▸ J.mul_mem (J.mul_mem k.property hcJ) (J.inv_mem k.property)
  let := D.elementary
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le (D.centralQuotientPreimage_le _)
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 B) hBJ
    ((localResidual_le _).trans inf_le_right)

/-- A scalar-plane torus element detects the remaining line quotient in PV. -/
theorem scalar_fixed_pairJoin
    (P : Subgroup G) (hPL : P ≤ L)
    (hPV : P ⊓ V = (SL3.flag D S a).Vi 1)
    (d : L) (hdP : (d : G) ∈ normalizer (P : Set G))
    (t : S.field.Carrierˣ) (ht : alignedQuotient D S a d = planeScalar t)
    (ht2 : (((t⁻¹ : S.field.Carrierˣ) : S.field.Carrier)^2) ≠ 1)
    (r : G) (hr : r ∈ P ⊔ V) (hc : ⁅(d : G),r⁆ ∈ P) : r ∈ P := by
  change r ∈ ((P ⊔ V : Subgroup G) : Set G) at hr
  rw [coe_mul_of_left_le_normalizer_right P V (hPL.trans D.normalizes)] at hr
  obtain ⟨p,hp,v,hv,rfl⟩ := hr
  have hdp : ⁅(d : G),p⁆ ∈ P := by
    exact P.mul_mem ((mem_normalizer_iff.mp hdP p).mp hp) (P.inv_mem hp)
  have hdv : ⁅(d : G),v⁆ ∈ P := by
    have hh := P.mul_mem (P.mul_mem (P.mul_mem (P.inv_mem hp) (P.inv_mem hdp)) hc) hp
    convert hh using 1
    dsimp [commutatorElement]
    group
  have hdisp : (displacement D d ⟨v,hv⟩ : G) ∈ (SL3.flag D S a).Vi 1 :=
    hPV.le ⟨hdv,(displacement D d ⟨v,hv⟩).property⟩
  have hz := (vectorEquiv_mem_plane D S a _).mp hdisp
  rw [displacement_coordinates,ht] at hz
  have hz' : (((t⁻¹ : S.field.Carrierˣ) : S.field.Carrier)^2 - 1) *
      (vectorEquiv D S a ⟨v,hv⟩).toAdd 2 = 0 := by
    simpa [planeScalar,Matrix.mulVec_diagonal,sub_mul] using hz
  have hv2 : (vectorEquiv D S a ⟨v,hv⟩).toAdd 2 = 0 :=
    (mul_eq_zero.mp hz').resolve_left (sub_ne_zero.mpr ht2)
  exact P.mul_mem hp (hPV.symm.le ((vectorEquiv_mem_plane D S a _).mpr hv2)).1

/-- Perfection removes the scalar line quotient from the actual plane-local core. -/
theorem local_core_le_pair
    (P : Subgroup G) (hPL : P ≤ L)
    (hPV : P ⊓ V = (SL3.flag D S a).Vi 1)
    (hR : (SL3.flag D S a).Ri 1 ⊓ L = P ⊔ V)
    (hJ : Stellmacher.elementaryAbelianMaxJ (P ⊔ V) = P) :
    ((SL3.flag D S a).Li 1).pCoreIn 2 ≤ P := by
  let J := (SL3.flag D S a).Li 1
  have : Group.IsPerfect J := localResidual_perfect _
  obtain ⟨hnJ,hnC⟩ := OriginalBlock.pair_normalizers D S a P hR hJ
  have hRP : P ⊔ V ≤ normalizer (P : Set G) := by
    have hn := (P ⊔ V).le_normalizer.trans
      (Stellmacher.normalizer_le_normalizer_elementaryAbelianMaxJ (P ⊔ V))
    rwa [hJ] at hn
  have hRJ : ⁅P ⊔ V,J⁆ ≤ P := by
    apply commutator_sup_le_of_relative_normal (P ⊔ V) P V J P hRP le_sup_left le_sup_right
    · exact le_normalizer_iff_commutator_le_left.mp hnJ
    · rw [commutator_comm]
      exact (local_seed_commutator D S a).trans (hPV.symm.le.trans inf_le_left)
  have hCR : J.pCoreIn 2 ≤ P ⊔ V := by
    rw [←hR]
    exact le_inf (planeCore_le_radical D S a)
      ((J.pCoreIn_le 2).trans ((localResidual_le _).trans inf_le_left))
  have : Nontrivial S.field.Carrierˣ := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [Nat.card_units]
    have := field_card D S
    omega)
  obtain ⟨t,ht⟩ := exists_ne (1 : S.field.Carrierˣ)
  obtain ⟨d,hd,hdt⟩ := exists_planeScalar_lift D S a t
  have ht2 : (((t⁻¹ : S.field.Carrierˣ) : S.field.Carrier)^2) ≠ 1 := by
    intro he
    have he1 : ((t⁻¹ : S.field.Carrierˣ) : S.field.Carrier) = 1 := by
      simpa only [sq_eq_one_iff,CharTwo.neg_eq,or_self] using he
    exact ht (inv_eq_one.mp (Units.ext he1))
  have hnD : zpowers (d : G) ≤ normalizer (P : Set G) := zpowers_le.mpr (hnC hd)
  have hDC := scalar_commutator_le_core D S a d hd t hdt
  have hdouble := (commutator_mono (hDC.trans hCR) le_rfl).trans hRJ
  have hcomm := commutator_commutator_le_of_rotate_of_le_normalizer hnJ hnJ hnD
    hdouble (by
      change ⁅⁅zpowers (d : G),J⁆,J⁆ ≤ P
      rw [commutator_comm (zpowers (d : G)) J]
      exact hdouble)
  rw [J.commutator_eq_self] at hcomm
  intro r hr
  have hc : ⁅(d : G),r⁆ ∈ P := by
    rw [commutator_comm J (zpowers (d : G))] at hcomm
    exact hcomm (commutator_mem_commutator (mem_zpowers _) ((J.pCoreIn_le 2) hr))
  exact scalar_fixed_pairJoin D S a P hPL hPV d (hnC hd) t hdt ht2 r (hCR hr) hc

/-- The full plane-radical image and its original plane kernel recover the core. -/
theorem pair_eq_local_core
    (P : Subgroup G) (hPL : P ≤ L)
    (hcore : L.pCoreIn 2 = V)
    (hPV : P ⊓ V = (SL3.flag D S a).Vi 1)
    (hR : (SL3.flag D S a).Ri 1 ⊓ L = P ⊔ V)
    (hJ : Stellmacher.elementaryAbelianMaxJ (P ⊔ V) = P)
    (him : (P.subgroupOf L).map (alignedQuotient D S a) =
      (lineRadicalSL S.field.Carrier).map (lineLocalSL S.field.Carrier).subtype) :
    P = ((SL3.flag D S a).Li 1).pCoreIn 2 := by
  let J := (SL3.flag D S a).Li 1
  have hCP := local_core_le_pair D S a P hPL hPV hR hJ
  apply le_antisymm ?_ hCP
  intro p hp
  have himp : alignedQuotient D S a ⟨p,hPL hp⟩ ∈
      (lineRadicalSL S.field.Carrier).map (lineLocalSL S.field.Carrier).subtype := by
    rw [←him]
    exact mem_map_of_mem _ hp
  obtain ⟨z,hz,hzp⟩ := himp
  obtain ⟨k,hk⟩ := localProjection_surjective D S a 1 z
  have hkC : k ∈ pCore 2 J := by
    have he := (localProjection D S a 1).comap_pCore_of_ker_isPGroup
      (localProjection_surjective D S a 1) (localProjection_ker_isTwoGroup D S a 1)
    rw [←he]
    change localProjection D S a 1 k ∈ pCore 2 (lineLocalSL S.field.Carrier)
    rw [hk,lineLocalSL_twoCore_eq]
    exact hz
  have hkP : (k : G) ∈ P := hCP (mem_map_of_mem J.subtype hkC)
  let kL : L := ⟨k,(localResidual_le _ k.property).1⟩
  have hq : alignedQuotient D S a kL = alignedQuotient D S a ⟨p,hPL hp⟩ :=
    (localProjection_coe D S a 1 k).symm.trans ((congrArg Subtype.val hk).trans hzp)
  have hv : (k : G)⁻¹ * p ∈ V := by
    apply hcore.le
    change L.subtype (kL⁻¹ * ⟨p,hPL hp⟩) ∈ (pCore 2 L).map L.subtype
    apply mem_map_of_mem L.subtype
    rw [←alignedQuotient_ker]
    change alignedQuotient D S a (kL⁻¹ * ⟨p,hPL hp⟩) = 1
    rw [map_mul,map_inv,hq,inv_mul_cancel]
  have hb : (k : G)⁻¹ * p ∈ (SL3.flag D S a).Vi 1 :=
    hPV.le ⟨P.mul_mem (P.inv_mem hkP) hp,hv⟩
  have hprod := (J.pCoreIn 2).mul_mem (mem_map_of_mem J.subtype hkC)
    (plane_le_local_core D S a hcore hb)
  change (k : G) * ((k : G)⁻¹ * p) ∈ J.pCoreIn 2 at hprod
  simpa only [mul_inv_cancel_left] using hprod

end CoreRecovery

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
