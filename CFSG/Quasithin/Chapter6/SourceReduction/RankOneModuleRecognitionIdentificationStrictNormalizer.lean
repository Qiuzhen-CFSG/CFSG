module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictKernel
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictStabilizer
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# Lifting the strict moved-plane stabilizer to the source normalizer

The moved plane recovers the literal hyperplane U ∩ V as [V,U]⟨z⟩.
An element centralizing the dotted layer has its commutators with V in
K ∩ C_H(U/Z(U)), hence in O₂(H). The earlier action-kernel identity
therefore makes it normalize this hyperplane. The source hyperplane
uniqueness then makes it normalize V.

Thus the inverse image of C_H-dot(V-dot), and also of the setwise
stabilizer of the moved plane, is exactly H ∩ M. Every map in this
argument is the actual quotient or conjugation map.

Source: Aschbacher--Smith, 6.2.16(5), printed p.689. The LocalAnalysis
premise is discharged by qt-d-1222-rankone-recognition-identification.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
  {κ : GroupClass.{u}} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

theorem LocalAnalysis.strict_intersection_eq_commutator_sup_line
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    sourceClosure (T : Subgroup G) L R z ⊓ layer L R =
      ⁅layer L R, sourceClosure (T : Subgroup G) L R z⁆ ⊔ zpowers z := by
  let U := sourceClosure (T : Subgroup G) L R z
  let V := layer L R
  let I := U ⊓ V
  let C := ⁅V, U⁆ ⊔ zpowers z
  have hCI : C ≤ I := sup_le
    (A.layer_closure_commutator.trans (by rw [inf_comm]))
    ((zpowers_le.mpr hz).trans hstrict.le)
  obtain ⟨he, B, _, _, _, _, hmark⟩ :=
    A.strict_symplectic_layer_action h611 hnatural hz horder hstrict
  let := he
  let W := strictLayerImage (T : Subgroup G) L R z
  have hW : W ≠ ⊥ := by
    intro hh
    have hc := A.strict_layer_actor_image_card h611 hnatural hz horder hstrict
    change Nat.card W = 2 at hc
    rw [hh, card_bot] at hc
    omega
  obtain ⟨a, ha, hane⟩ : ∃ a, a ∈ W ∧ a ≠ 1 := by
    by_contra! hh
    apply hW
    exact eq_bot_iff.mpr (fun a ha => mem_bot.mpr (hh a ha))
  have hplane := (hmark a ha hane).2.1
  obtain ⟨v, hv, rfl⟩ := ha
  apply le_antisymm ?_ hCI
  intro x hx
  let q := QuotientGroup.mk' (center U)
  let xU : U := ⟨x, hx.1⟩
  have hxplane : Additive.ofMul (q xU) ∈ strictCentralPlane (T : Subgroup G) L R z :=
    mem_map_of_mem q hx
  rw [← hplane] at hxplane
  obtain ⟨w, hw⟩ := hxplane
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (center U) w.toMul
  have hw' : w = Additive.ofMul (q u) := congrArg Additive.ofMul hu.symm
  rw [hw'] at hw
  change Additive.ofMul (strictQuotientAction (T : Subgroup G) L R z v (q u)) -
    Additive.ofMul (q u) = Additive.ofMul (q xU) at hw
  let c : U := strictClosureAction (T : Subgroup G) L R z v u / u
  have hc : (c : G) = ⁅(v : G), (u : G)⁆ := by
    change (strictClosureAction (T : Subgroup G) L R z v u : G) / (u : G) = _
    rw [strictClosureAction_apply, div_eq_mul_inv, commutatorElement_def]
  have hcV : (c : G) ∈ V :=
    hc ▸ (A.layer_closure_commutator (commutator_mem_commutator hv u.property)).1
  have hq : q c = q xU := by
    rw [show q c = strictQuotientAction (T : Subgroup G) L R z v (q u) / q u by
      rw [strictQuotientAction_mk, ← map_div]]
    exact congrArg Additive.toMul hw
  have hzmem : ((c / xU : U) : G) ∈ zpowers z := by
    rw [← A.strict_layer_center_intersection h611 hnatural hz horder hstrict]
    exact ⟨mem_map_of_mem U.subtype (QuotientGroup.eq_iff_div_mem.mp hq),
      V.div_mem hcV hx.2⟩
  have hcC : (c : G) ∈ C :=
    (show ⁅V, U⁆ ≤ C from le_sup_left) (hc ▸ commutator_mem_commutator hv u.property)
  have hzC : (c : G) / x ∈ C := (show zpowers z ≤ C from le_sup_right) hzmem
  have hlast := C.mul_mem (C.inv_mem hzC) hcC
  simpa only [inv_div, div_mul_cancel] using hlast

theorem LocalAnalysis.strict_intersection_normalizer
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    centralizer ({z} : Set G) ⊓ normalizer
      (sourceClosure (T : Subgroup G) L R z ⊓ layer L R : Set G) =
      centralizer ({z} : Set G) ⊓ M := by
  let U := sourceClosure (T : Subgroup G) L R z
  let V := layer L R
  let I := U ⊓ V
  rw [← A.layer_normalizer]
  apply le_antisymm
  · intro h hh
    refine ⟨hh.1, ?_⟩
    change h ∈ normalizer (V : Set G)
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply A.hyperplane_unique
    have hI : I.map (MulAut.conj h).toMonoidHom = I :=
      mem_normalizer_iff_map_conj_eq.mp hh.2
    have hi : I ≤ V ⊓ V.map (MulAut.conj h).toMonoidHom :=
      le_inf inf_le_right (hI ▸ map_mono (f := (MulAut.conj h).toMonoidHom) inf_le_right)
    have hc := card_le_of_le hi
    rw [(A.strict_intersection_eq_core h611 hnatural hstrict).2] at hc
    exact hc
  · intro h hh
    refine ⟨hh.1, ?_⟩
    change h ∈ normalizer (I : Set G)
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (U ⊓ V).map _ = U ⊓ V
    rw [Subgroup.map_inf _ _ _ (MulAut.conj h).injective,
      mem_normalizer_iff_map_conj_eq.mp (sourceClosure_normalized _ _ _ _ hh.1),
      mem_normalizer_iff_map_conj_eq.mp hh.2]

theorem LocalAnalysis.strict_intersection_normalized_of_core_commutators
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    (h : centralizer ({z} : Set G))
    (hc : ∀ v ∈ layer L R, ⁅(h : G), v⁆ ∈ (centralizer ({z} : Set G)).pCoreIn 2) :
    (h : G) ∈ normalizer (sourceClosure (T : Subgroup G) L R z ⊓ layer L R : Set G) := by
  let H := centralizer ({z} : Set G)
  let U := sourceClosure (T : Subgroup G) L R z
  let V := layer L R
  let I := U ⊓ V
  let φ := (MulAut.conj (h : G)).toMonoidHom
  have hspan : I = ⁅V, U⁆ ⊔ zpowers z :=
    A.strict_intersection_eq_commutator_sup_line h611 hnatural hz horder hstrict
  have hline : zpowers z ≤ I := (zpowers_le.mpr hz).trans hstrict.le
  have hU : U.map φ = U := mem_normalizer_iff_map_conj_eq.mp
    (sourceClosure_normalized _ _ _ _ h.property)
  have hzfix : φ z = z := by
    change (h : G) * z * (h : G)⁻¹ = z
    rw [mem_centralizer_singleton_iff.mp h.property, mul_inv_cancel_right]
  have hzmap : (zpowers z).map φ = zpowers z := by rw [MonoidHom.map_zpowers, hzfix]
  have hm : I.map φ ≤ I := by
    apply (map_mono (f := φ) hspan.le).trans
    rw [Subgroup.map_sup, map_commutator, hU, hzmap]
    apply sup_le ?_ hline
    apply commutator_le.mpr
    rintro _ ⟨v, hv, rfl⟩ u hu
    let k := ⁅(h : G), v⁆
    have hk : k ∈ H.pCoreIn 2 := hc v hv
    have hku := (A.action_kernel k ((H.pCoreIn_le 2) hk)).mpr hk
    have hvu : ⁅v, u⁆ ∈ I := by
      have hh := A.layer_closure_commutator (commutator_mem_commutator hv hu)
      exact ⟨hh.2, hh.1⟩
    have hkc : k * ⁅v, u⁆ * k⁻¹ ∈ I := by
      rw [show k * ⁅v, u⁆ * k⁻¹ = ⁅k, ⁅v, u⁆⁆ * ⁅v, u⁆ by
        rw [commutatorElement_def]; group]
      exact I.mul_mem (hline (hku _ hvu.1)) hvu
    have hvconj : φ v = k * v := conj_eq_commutatorElement_mul
    rw [hvconj, commutatorElement_mul_left_eq_conj_mul]
    exact I.mul_mem hkc (hline (hku u hu))
  change (h : G) ∈ normalizer (I : Set G)
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact eq_of_le_of_card_ge hm (by rw [card_map_of_injective (MulAut.conj (h : G)).injective])

theorem LocalAnalysis.strict_layerImage_centralizer_preimage
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    (centralizer (strictLayerImage (T : Subgroup G) L R z :
      Set (StrictActor (T : Subgroup G) L R z))).comap
        (QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L R z).ker) =
      M.subgroupOf (centralizer ({z} : Set G)) := by
  let H := centralizer ({z} : Set G)
  let K := equalityLayerClosure L R z
  let W := strictLayerImage (T : Subgroup G) L R z
  let q := QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L R z).ker
  ext h
  constructor
  · intro hh
    have hcore : ∀ v ∈ layer L R, ⁅(h : G), v⁆ ∈ H.pCoreIn 2 := by
      intro v hv
      let vH : H := ⟨v, layer_le_involution_centralizer h611 hz hv⟩
      have hvK : vH ∈ K := le_normalClosure hv
      let k : H := ⁅h, vH⁆
      have hkK : k ∈ K := by
        change h * vH * h⁻¹ * vH⁻¹ ∈ K
        exact K.mul_mem ((inferInstance : K.Normal).conj_mem vH hvK h) (K.inv_mem hvK)
      have hcomm : q h * q vH = q vH * q h :=
        (mem_centralizer_iff.mp hh (q vH) (mem_map_of_mem q hv)).symm
      have hkker : k ∈ (strictQuotientAction (T : Subgroup G) L R z).ker := by
        apply (QuotientGroup.eq_one_iff k).mp
        change q ⁅h, vH⁆ = 1
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm
      have hkcore := A.strict_layerClosure_kernel_le_core h611 hnatural hstrict ⟨hkker, hkK⟩
      exact mem_map_of_mem H.subtype hkcore
    have hn := A.strict_intersection_normalized_of_core_commutators h611 hnatural hz horder hstrict h hcore
    have hm : (h : G) ∈ H ⊓ M :=
      A.strict_intersection_normalizer h611 hnatural hstrict ▸ ⟨h.property, hn⟩
    exact hm.2
  · intro hh
    have hn : (h : G) ∈ normalizer (layer L R : Set G) := by
      have hm : (h : G) ∈ H ⊓ M := ⟨h.property, hh⟩
      rw [← A.layer_normalizer] at hm
      exact hm.2
    have hnW : q h ∈ normalizer (W : Set (StrictActor (T : Subgroup G) L R z)) := by
      apply ((layer L R).subgroupOf H).le_normalizer_map q
      apply mem_map_of_mem
      rw [← subgroupOf_normalizer_eq (layer_le_involution_centralizer h611 hz)]
      exact hn
    exact normalizer_le_centralizer_of_card_two W
      (A.strict_layer_actor_image_card h611 hnatural hz horder hstrict) hnW

theorem LocalAnalysis.strict_plane_stabilizer_iff_mem
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    [IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L R z)]
    (h : centralizer ({z} : Set G)) :
    (∀ x, x ∈ strictCentralPlane (T : Subgroup G) L R z ↔
      strictRepresentation (T : Subgroup G) L R z
        (QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L R z).ker h) x ∈
          strictCentralPlane (T : Subgroup G) L R z) ↔ (h : G) ∈ M := by
  let W := strictLayerImage (T : Subgroup G) L R z
  let q := QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L R z).ker
  have hcard : Nat.card W = 2 :=
    A.strict_layer_actor_image_card h611 hnatural hz horder hstrict
  obtain ⟨a, ha1, huniq⟩ := (Nat.card_eq_two_iff' (1 : W)).mp hcard
  have hane : (a : StrictActor (T : Subgroup G) L R z) ≠ 1 :=
    fun hh => ha1 (Subtype.ext hh)
  rw [A.strict_plane_stabilizer_iff_commute h611 hnatural hz horder hstrict a a.property hane]
  have hiff : q h ∈ centralizer (W : Set (StrictActor (T : Subgroup G) L R z)) ↔ (h : G) ∈ M := by
    change h ∈ (centralizer (W : Set (StrictActor (T : Subgroup G) L R z))).comap q ↔ _
    rw [A.strict_layerImage_centralizer_preimage h611 hnatural hz horder hstrict]
    rfl
  rw [← hiff]
  constructor
  · intro hc b hb
    by_cases hb1 : b = 1
    · simp only [hb1, one_mul, mul_one]
    · have he : (⟨b, hb⟩ : W) = a :=
        huniq _ (fun hh => hb1 (congrArg Subtype.val hh))
      have he' : b = (a : StrictActor (T : Subgroup G) L R z) := congrArg Subtype.val he
      rw [he']
      exact hc.eq.symm
  · intro hc
    exact (hc a a.property).symm

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
