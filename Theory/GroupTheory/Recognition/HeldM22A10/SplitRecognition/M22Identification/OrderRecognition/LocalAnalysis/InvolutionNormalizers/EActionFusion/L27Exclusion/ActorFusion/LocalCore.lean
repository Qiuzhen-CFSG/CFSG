module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.Interfaces
public import Theory.GroupTheory.OddCoreKleinFourCentralizers
public import Theory.Quasithin.EvenCharacteristic
public import Theory.GroupTheory.ZStar.CoreFree
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.FusionReduction

/-!
# The odd core and weak closure step in the order-168 branch

Fusion of the marked involution with printed z₃ makes the full centralizers
of the three nonidentity elements of E ∩ C(a) characteristic two. The
Klein-four odd-core theorem therefore gives O₂′(C(a)) = 1. If the local
centralizer C(z₁) ∩ C(a) is Sylow in C(a), and C(z₃) ∩ C(a) lies in
C(z₁), comparison of centralizers rules out fusion of z₁ and z₃ inside
C(a). The five coordinate classes then prove weak closure; core-free
Z-star yields C(a) ≤ C(z₁).

The Sylow and intersection hypotheses of the second theorem are explicit.
The assembly module discharges them using separate normalizer control.
No simplicity of C(a) is asserted or used.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, Lemma 6, printed p.6. Printed z₃ is `z 2`.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
open LocalModelDichotomy

private theorem model_characteristic_two :
    centralizer (pCore 2 TwistedModel : Set TwistedModel) ≤ pCore 2 TwistedModel := by
  let : modelE.Normal := by unfold modelE; infer_instance
  let := modelE_elementary
  have hE : modelE ≤ pCore 2 TwistedModel :=
    le_sSup ⟨inferInstance, IsElementaryAbelian.isPGroup 2 modelE⟩
  exact (centralizer_le hE).trans (by rwa [modelE_centralizer])

universe u
variable {G : Type u} [Group G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

include k in
private theorem marked_characteristic_two :
    centralizer (pCore 2 D.centralizer : Set D.centralizer) ≤ pCore 2 D.centralizer :=
  (Theory.Quasithin.centralizer_pCore_le_iff 2 k).mp model_characteristic_two

include k in
private theorem conjugate_characteristic_two {v : G} (h : IsConj D.z v) :
    centralizer (pCore 2 (centralizer ({v} : Set G)) :
      Set (centralizer ({v} : Set G))) ≤ pCore 2 (centralizer ({v} : Set G)) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  let e := MulAut.conj g
  have hez : e D.z = v := hg
  have he : D.centralizer.map e.toMonoidHom = centralizer ({v} : Set G) := by
    apply le_antisymm
    · have hi := map_centralizer_le_centralizer_image ({D.z} : Set G) e.toMonoidHom
      simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom, hez] using hi
    · intro x hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      apply mem_centralizer_singleton_iff.mpr
      apply e.injective
      simpa only [map_mul, e.apply_symm_apply, hez] using
        mem_centralizer_singleton_iff.mp hx
  let f := (e.subgroupMap D.centralizer).trans (MulEquiv.subgroupCongr he)
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 f).mp
    (marked_characteristic_two D k)

local instance : DecidableEq TwistedModel := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm
local instance : Fintype TwistedModel := Fintype.ofEquiv
  (BinaryFour × SymmetricFour) SemidirectProduct.equivProd.symm

private def actorFour : Subgroup TwistedModel := modelE ⊓ centralizer {a}
local instance : DecidablePred (· ∈ actorFour) := fun x =>
  decidable_of_iff (x.right = 1 ∧ x * a = a * x) (by
    change _ ↔ x.right = 1 ∧ x ∈ centralizer ({a} : Set TwistedModel)
    rw [mem_centralizer_singleton_iff])

private theorem actorFour_elements : ∀ x ∈ actorFour,
    x = 1 ∨ x = z 0 ∨ x = z 2 ∨ x = z 0 * z 2 := by decide +kernel

private theorem actorFour_card : Nat.card actorFour = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem actorFour_elementary : IsElementaryAbelian 2 actorFour := by
  have hs : ∀ x : actorFour, x ^ 2 = 1 := by
    intro x
    apply Subtype.ext
    let := modelE_elementary
    exact elemPow_eq_one_of_isElementaryAbelian x.val x.property.1
  refine
    { is_comm := ?_
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
  exact ⟨fun x y => (Commute.of_orderOf_dvd_two
    (fun x => orderOf_dvd_of_pow_eq_one (hs x)) x y).eq⟩

variable [Finite G]

/-- The odd core of C(a) vanishes as soon as printed z₁ and z₃ are fused. -/
public theorem l27_a_centralizer_oddCore_eq_bot_of_z_three_fusion
    (hz3 : IsConj D.z (into D k (z 2))) :
    pPrimeCore 2 (centralizer ({into D k a} : Set G)) = ⊥ := by
  let V := actorFour.map (into D k)
  let := actorFour_elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
  apply pPrimeCore_centralizer_eq_bot_of_klein_four (into D k a)
    (by rw [orderOf_injective _ (into_injective D k)]; exact actor_orders.1) V
  · rw [← Nat.card_congr (actorFour.equivMapOfInjective _ (into_injective D k)).toEquiv]
    exact actorFour_card
  · rintro v ⟨x, hx, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    simpa only [← map_mul] using congrArg (into D k)
      (mem_centralizer_singleton_iff.mp hx.2)
  · rintro v ⟨x, hx, rfl⟩ hne
    apply conjugate_characteristic_two D k
    rcases actorFour_elements x hx with rfl | rfl | rfl | rfl
    · exact False.elim (hne (map_one _))
    · rw [into_z_zero D k]
    · exact hz3
    · apply hz3.trans
      apply (into D k).map_isConj
      exact isConj_iff.mpr ⟨b⁻¹, by decide +kernel⟩


private def aCentralizerZ : centralizer ({into D k a} : Set G) :=
  ⟨D.z, mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp (k a).property).symm⟩

private def aCentralizerZThree : centralizer ({into D k a} : Set G) :=
  ⟨into D k (z 2), mem_centralizer_singleton_iff.mpr (by
    rw [← map_mul, ← map_mul]
    exact congrArg (into D k) (by decide +kernel : z 2 * a = a * z 2))⟩

private def aCentralizerB : centralizer ({into D k a} : Set G) :=
  ⟨into D k b, mem_centralizer_singleton_iff.mpr (by
    rw [← map_mul, ← map_mul]
    exact congrArg (into D k) (by decide +kernel : b * a = a * b))⟩

private theorem centralizer_card_conj {H : Type*} [Group H] {x y : H}
    (h : IsConj x y) : Nat.card (centralizer ({x} : Set H)) =
      Nat.card (centralizer ({y} : Set H)) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  let e := MulAut.conj g
  have he : e x = y := hg
  apply Nat.card_congr (Equiv.subtypeEquiv e.toEquiv ?_)
  intro t
  change t ∈ centralizer ({x} : Set H) ↔ e t ∈ centralizer ({y} : Set H)
  simp only [mem_centralizer_singleton_iff, ← he, ← map_mul, e.injective.eq_iff]

private theorem z_not_fused_in_a_centralizer
    (hinter : centralizer ({into D k (z 2)} : Set G) ⊓
      centralizer ({into D k a} : Set G) ≤ D.centralizer) :
    ¬ IsConj (aCentralizerZ D k) (aCentralizerZThree D k) := by
  intro hf
  let C := centralizer ({into D k a} : Set G)
  have hle : centralizer ({aCentralizerZThree D k} : Set C) ≤
      centralizer ({aCentralizerZ D k} : Set C) := by
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hinter ⟨
      mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx)), x.property⟩)
  have he := eq_of_le_of_card_ge hle (centralizer_card_conj hf).le
  have hb : aCentralizerB D k ∈ centralizer ({aCentralizerZ D k} : Set C) := by
    apply mem_centralizer_singleton_iff.mpr
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (k b).property)
  rw [← he] at hb
  have hbad : b * z 2 = z 2 * b := by
    apply into_injective D k
    have hbval := congrArg Subtype.val (mem_centralizer_singleton_iff.mp hb)
    change into D k b * into D k (z 2) = into D k (z 2) * into D k b at hbval
    simpa only [map_mul] using hbval
  exact (by decide +kernel : b * z 2 ≠ z 2 * b) hbad

/-- Involutions commuting with a have no printed-z₂ class: their vector part
lies in the four generated by printed z₁ and z₃. -/
public theorem l27_model_a_involution_classes (x : TwistedModel)
    (hx : x ∈ centralizer ({a} : Set TwistedModel)) (h2 : orderOf x = 2) :
    x = z 0 ∨ x = z 2 ∨ x = z 0 * z 2 ∨ IsConj x a ∨ IsConj x d := by
  have hv (i : Fin 4) (h : IsConj x (z i)) :
      x = z 0 ∨ x = z 2 ∨ x = z 0 * z 2 := by
    have hmap := (SemidirectProduct.rightHom : TwistedModel →* SymmetricFour).map_isConj h
    change IsConj x.right (z i).right at hmap
    have hi : (z i).right = 1 := z_mem_modelE i
    rw [hi] at hmap
    have hE : x ∈ modelE := isConj_one_left.mp hmap
    rcases actorFour_elements x ⟨hE, hx⟩ with h | h | h | h
    · simp [h] at h2
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  rcases model_involution_classes x h2 with h | h | h | h | h
  · rcases hv 0 h with h | h | h <;> simp only [h, true_or, or_true]
  · rcases hv 1 h with h | h | h <;> simp only [h, true_or, or_true]
  · rcases hv 2 h with h | h | h <;> simp only [h, true_or, or_true]
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- The local Sylow and intersection conclusions imply C(a) ≤ C(z₁).
The odd-core and weak-closure premises of Z-star are proved internally. -/
public theorem l27_a_centralizer_le_marked_of_local_sylow
    (hz3 : IsConj D.z (into D k (z 2)))
    (hna : ¬ IsConj D.z (into D k a))
    (hnd : ¬ IsConj D.z (into D k d))
    (hSylow : ∃ S : Sylow 2 (centralizer ({into D k a} : Set G)),
      (S : Subgroup (centralizer ({into D k a} : Set G))) =
        D.centralizer.subgroupOf (centralizer ({into D k a} : Set G)))
    (hinter : centralizer ({into D k (z 2)} : Set G) ⊓
      centralizer ({into D k a} : Set G) ≤ D.centralizer) :
    centralizer ({into D k a} : Set G) ≤ D.centralizer := by
  let C := centralizer ({into D k a} : Set G)
  let t := aCentralizerZ D k
  let t3 := aCentralizerZThree D k
  obtain ⟨S, hS⟩ := hSylow
  have ht : orderOf t = 2 := (Subgroup.orderOf_coe t).symm.trans D.z_order
  have htI : BenderSuzuki.PFAppendixIII.IsInvolution t := by
    constructor
    · intro he; simp [he] at ht
    · simpa only [ht] using pow_orderOf_eq_one t
  have htS : t ∈ (S : Subgroup C) := by
    rw [hS]
    exact mem_centralizer_singleton_iff.mpr rfl
  have htcent : ∀ s, s ∈ (S : Subgroup C) → s * t = t * s := by
    intro s hs
    rw [hS] at hs
    exact Subtype.ext (mem_centralizer_singleton_iff.mp hs)
  have htweak : Glauberman.ZStar.IsWeaklyClosedInSylow t (S : Subgroup C) := by
    refine ⟨htS, ?_⟩
    intro g hg
    let w : C := g * t * g⁻¹
    have hwC : (w : G) ∈ D.centralizer := by
      rw [hS] at hg
      exact hg
    let v := k.symm ⟨(w : G), hwC⟩
    have hv : into D k v = (w : G) := congrArg Subtype.val (k.apply_symm_apply _)
    have hvC : v ∈ centralizer ({a} : Set TwistedModel) := by
      apply mem_centralizer_singleton_iff.mpr
      apply into_injective D k
      simpa only [map_mul, hv] using mem_centralizer_singleton_iff.mp w.property
    have htw : IsConj t w := isConj_iff.mpr ⟨g, rfl⟩
    have hv2 : orderOf v = 2 := by
      rw [← orderOf_injective (into D k) (into_injective D k), hv, Subgroup.orderOf_coe]
      change orderOf (MulAut.conj g t) = 2
      rw [MulEquiv.orderOf_eq, ht]
    have hDv : IsConj D.z (into D k v) := by
      rw [hv]
      exact C.subtype.map_isConj htw
    have hno := z_not_fused_in_a_centralizer D k hinter
    rcases l27_model_a_involution_classes v hvC hv2 with he | he | he | he | he
    · apply Subtype.ext
      rw [he, into_z_zero D k] at hv
      exact hv.symm
    · apply False.elim
      apply hno
      apply htw.trans
      have hw : w = t3 := Subtype.ext (by rw [he] at hv; exact hv.symm)
      rw [hw]
    · apply False.elim
      have hw : w = t * t3 := by
        apply Subtype.ext
        rw [he, map_mul, into_z_zero D k] at hv
        exact hv.symm
      have hb : IsConj t3 (t * t3) := by
        apply isConj_iff.mpr
        refine ⟨(aCentralizerB D k)⁻¹, ?_⟩
        apply Subtype.ext
        change (into D k b)⁻¹ * into D k (z 2) * ((into D k b)⁻¹)⁻¹ =
          D.z * into D k (z 2)
        rw [← into_z_zero D k, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
        exact congrArg (into D k) (by decide +kernel)
      exact hno ((hw ▸ htw).trans hb.symm)
    · exact False.elim (hna (hDv.trans ((into D k).map_isConj he)))
    · exact False.elim (hnd (hDv.trans ((into D k).map_isConj he)))
  have hcenter := Glauberman.ZStar.glauberman_zstar_corefree
    (l27_a_centralizer_oddCore_eq_bot_of_z_three_fusion D k hz3) S t htI htS htcent htweak
  intro x hx
  exact mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_center_iff.mp hcenter (⟨x, hx⟩ : C)))

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
