module

public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.ElementaryCore.OrderTwo.Lift
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.NaturalFixed

/-!
# Fusion lifts in the contrary order-two branch

Source: Aschbacher–Smith, proof of Lemma 2.5.24, printed p.568,
combined manuscript of 1 March 2004.

An element e of the original marked four-group whose crossing conjugate
leaves K S_C is fused in K to z = z_K. The source natural-action input
therefore puts the action of eˣ in the natural S₆. Its two possible odd
involution types are treated on the actual six-letter carrier. An even
conjugator sends either type to a marked element centralizing the inner
Sylow subgroup. Lifting this K-conjugation preserves order two. The action
kernel places its result in S, and faithfulness on S ∩ K proves actual
centralization. The resulting element belongs to ⟨S ∩ K, eˣ⟩; its conjugator
need not belong to that extension.

For a fixed marking, natural membership alone does not select the
transposition type. The marked Sylow rotation interchanges the transposition
and triple-transposition representatives. We lift this correction to an
actual element of S and retain the combined H-conjugator back to the same
eˣ. Thus neither a change of four-group nor a change of A₆ coordinates is
silently assumed, and no arbitrary lift of a quotient involution is used.
-/

public section

open Subgroup AlternatingSix.ShadowLocal
namespace CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore.OrderTwo.Fusion
open Equiv.Perm

private theorem even_conjugator (σ τ : Equiv.Perm (Fin 6))
    (hσ : σ ∉ alternatingGroup (Fin 6)) (h : IsConj σ τ) :
    ∃ k : A6, k.val * σ * k.val⁻¹ = τ := by
  obtain ⟨p, hp⟩ := isConj_iff.mp h
  by_cases he : p ∈ alternatingGroup (Fin 6)
  · exact ⟨⟨p, he⟩, hp⟩
  · have hpodd : sign p = -1 := (Int.units_eq_one_or _).resolve_left
      (fun h => he (mem_alternatingGroup.mpr h))
    have hσodd : sign σ = -1 := (Int.units_eq_one_or _).resolve_left
      (fun h => hσ (mem_alternatingGroup.mpr h))
    refine ⟨⟨p * σ, mem_alternatingGroup.mpr ?_⟩, ?_⟩
    · rw [map_mul, hpodd, hσodd]; decide
    · change (p * σ) * σ * (p * σ)⁻¹ = τ
      calc
        _ = p * σ * p⁻¹ := by group
        _ = τ := hp

private theorem conjugate_marked (P : Sylow 2 AutA6) (β : AutA6)
    (ho : orderOf β = 2) (hn : β ∈ natural) (hi : β ∉ AlternatingSix.ShadowLocal.inner) :
    ∃ k : A6,
      MulAut.conj k * β * (MulAut.conj k)⁻¹ =
        (Identification.sylowEquiv P Holomorph.transposition : AutA6) ∨
      MulAut.conj k * β * (MulAut.conj k)⁻¹ =
        (Identification.sylowEquiv P
          (Holomorph.transposition * Holomorph.rotation ^ 4) : AutA6) := by
  obtain ⟨σ, he⟩ := hn
  change permutationAction σ = β at he
  subst β
  have hσo : orderOf σ = 2 :=
    (orderOf_injective permutationAction permutationAction_injective σ).symm.trans ho
  have hσ : σ ∉ alternatingGroup (Fin 6) := by
    intro he
    exact hi ⟨⟨σ, he⟩, (permutationAction_coe ⟨σ, he⟩).symm⟩
  let p := Identification.conjugatingPermutation P
  rcases odd_involution_cycleType σ hσo hσ with hs | ht
  · have hc : IsConj σ (Equiv.swap (p 4) (p 5)) :=
      isConj_of_cycleType_eq ((isSwap_iff_cycleType.mp hs).trans
        (isSwap_iff_cycleType.mp (Identification.conjugatedTransposition_isSwap P)).symm)
    obtain ⟨k, hk⟩ := even_conjugator σ _ hσ hc
    refine ⟨k, Or.inl ?_⟩
    rw [Identification.sylowEquiv_transposition, ← permutationAction_coe,
      ← map_inv, ← map_mul, ← map_mul, hk]
  · let τ := Identification.transpositionPerm * dihedralRotation.val ^ 2
    have hτ : τ.cycleType = {2, 2, 2} := by decide +kernel
    have hc : IsConj σ (p * τ * p⁻¹) :=
      isConj_of_cycleType_eq (ht.trans (by rw [cycleType_conj, hτ]))
    obtain ⟨k, hk⟩ := even_conjugator σ _ hσ hc
    refine ⟨k, Or.inr ?_⟩
    rw [← permutationAction_coe, ← map_inv, ← map_mul, ← map_mul, hk,
      map_mul (Identification.sylowEquiv P), Subgroup.coe_mul,
      Identification.sylowEquiv_transposition, Identification.sylowEquiv_rotation_four]
    rw [← map_mul]
    congr 1
    change p * (Identification.transpositionPerm * dihedralRotation.val ^ 2) * p⁻¹ =
      Equiv.swap (p 4) (p 5) * (p * dihedralRotation.val ^ 2 * p⁻¹)
    rw [Equiv.swap_apply_apply]
    change _ = (p * Identification.transpositionPerm * p⁻¹) * _
    group

private theorem marked_centralizes (P : Sylow 2 AutA6) :
    Identification.sylowEquiv P Holomorph.transposition ∈
      centralizer (sylowInner P : Set P) ∧
    Identification.sylowEquiv P (Holomorph.transposition * Holomorph.rotation ^ 4) ∈
      centralizer (sylowInner P : Set P) := by
  have hb : Identification.sylowEquiv P Holomorph.transposition ∈
      SylowGeometry.transpositionSubgroup P :=
    ⟨_, mem_zpowers _, rfl⟩
  have hz : Identification.sylowEquiv P (Holomorph.rotation ^ 4) ∈ center P := by
    rw [SylowGeometry.center_eq]
    exact mem_zpowers _
  rw [SylowGeometry.centralizer_inner]
  exact ⟨mem_sup_right hb, by rw [map_mul]; exact mul_mem (mem_sup_right hb) (mem_sup_left hz)⟩

-- This conclusion records an inner conjugator; it need not belong to P.
private theorem natural_outer_centralizing_conjugate (P : Sylow 2 AutA6) (β : AutA6)
    (ho : orderOf β = 2) (hn : β ∈ natural) (hi : β ∉ AlternatingSix.ShadowLocal.inner) :
    ∃ (k : A6) (a : P),
      MulAut.conj k * β * (MulAut.conj k)⁻¹ = (a : AutA6) ∧
      a ∈ centralizer (sylowInner P : Set P) ∧
      ∃ r : P, r * a * r⁻¹ = Identification.sylowEquiv P Holomorph.transposition := by
  obtain ⟨k, h | h⟩ := conjugate_marked P β ho hn hi
  · exact ⟨k, _, h, (marked_centralizes P).1, 1, by simp⟩
  · refine ⟨k, _, h, (marked_centralizes P).2,
      Identification.sylowEquiv P Holomorph.rotation, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg (Identification.sylowEquiv P) (by decide +kernel)
end CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore.OrderTwo.Fusion
namespace CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore.OrderTwo.Fusion
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
variable (d : EarlierSetup κ G)

private theorem action_K_image : (d.K.subgroupOf d.H).map d.action =
    AlternatingSix.ShadowLocal.inner := by
  ext a
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨d.modelK ⟨k, hk⟩, (d.action_on_K ⟨k, hk⟩).symm⟩
  · rintro ⟨a, rfl⟩
    refine ⟨⟨d.modelK.symm a, d.k_le_h (d.modelK.symm a).property⟩,
      (d.modelK.symm a).property, ?_⟩
    rw [d.action_on_K, d.modelK.apply_symm_apply]

private theorem action_inner_iff (h : d.H) :
    d.action h ∈ AlternatingSix.ShadowLocal.inner ↔ (h : G) ∈ d.K ⊔ d.SC := by
  have he : (AlternatingSix.ShadowLocal.inner.comap d.action).map d.H.subtype =
      d.K ⊔ d.SC := by
    rw [← action_K_image d, comap_map_eq, Subgroup.map_sup, d.action_kernel,
      map_subgroupOf_eq_of_le d.k_le_h, map_subgroupOf_eq_of_le d.sc_le_h]
  rw [← he]
  constructor
  · intro hh; exact ⟨h, hh, rfl⟩
  · rintro ⟨k, hk, heq⟩
    exact (Subtype.ext heq : k = h) ▸ hk

private theorem mem_s_of_action_mem (h : d.H) (hh : d.action h ∈ d.imageSylow) :
    (h : G) ∈ d.S := by
  change d.action h ∈ (d.imageSylow : Subgroup AutA6) at hh
  rw [d.imageSylow_eq_range] at hh
  obtain ⟨s, hs⟩ := hh
  let sh : d.H := ⟨s, d.s_le_h s.property⟩
  have hc : h * sh⁻¹ ∈ d.action.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    change d.action h * (d.sylowAction s)⁻¹ = 1
    rw [hs, mul_inv_cancel]
  rw [d.action_kernel] at hc
  have hv := d.S.mul_mem (d.sc_le_s hc) s.property
  change ((h : G) * (s : G)⁻¹) * (s : G) ∈ d.S at hv
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hv

private theorem centralizes_of_action (v : d.S) (a : d.imageSylow)
    (ha : d.toImageSylow v = a)
    (hc : a ∈ centralizer (sylowInner d.imageSylow : Set d.imageSylow)) :
    (v : G) ∈ centralizer ((d.S ⊓ d.K : Subgroup G) : Set G) := by
  intro k hk
  have hn : d.S ≤ normalizer (d.S ⊓ d.K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer inf_le_left).mp d.normal_sk
  have hk' : (v : G) * k * (v : G)⁻¹ ∈ d.S ⊓ d.K :=
    (mem_normalizer_iff.mp (hn v.property) k).mp hk
  have him : innerAction d ⟨(v : G) * k * (v : G)⁻¹, hk'⟩ =
      innerAction d ⟨k, hk⟩ := by
    apply Subtype.ext
    change d.toImageSylow (v * ⟨k, hk.1⟩ * v⁻¹) = d.toImageSylow ⟨k, hk.1⟩
    rw [map_mul, map_mul, map_inv, ha]
    have he := hc (innerAction d ⟨k, hk⟩) (innerAction d ⟨k, hk⟩).property
    change d.toImageSylow ⟨k, hk.1⟩ * a = a * d.toImageSylow ⟨k, hk.1⟩ at he
    rw [← he, mul_assoc, mul_inv_cancel, mul_one]
  have he := congrArg Subtype.val (innerAction_injective d him)
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- Fusion of every nonidentity member of the actual inner four-group with z. -/
theorem fourZero_fused_z (hz : d.z = d.zK) (e : G) (he : e ∈ fourZero d)
    (hne : e ≠ 1) : ∃ k : d.K, (k : G)⁻¹ * d.z * k = e := by
  have hek : e ∈ d.K := (fourZero_le d he).2
  have hzk : d.z ∈ d.K := hz ▸ (fourZero_le d (zK_mem_fourZero d)).2
  have he2 : e ^ 2 = 1 := by
    have h := IsKleinFour.mul_self (⟨e, he⟩ : fourZero d)
    simpa only [coe_mul, coe_one, pow_two] using congrArg Subtype.val h
  have heo : orderOf (⟨e, hek⟩ : d.K) = 2 :=
    orderOf_eq_prime (Subtype.ext he2) (fun h => hne (congrArg Subtype.val h))
  have hzo : orderOf (⟨d.z, hzk⟩ : d.K) = 2 :=
    (orderOf_injective d.K.subtype d.K.subtype_injective _).symm.trans d.z_order
  obtain ⟨k, hk⟩ := isConj_iff.mp (involutions_isConj
    (d.modelK ⟨d.z, hzk⟩) (d.modelK ⟨e, hek⟩)
    ((d.modelK.orderOf_eq _).trans hzo) ((d.modelK.orderOf_eq _).trans heo))
  refine ⟨d.modelK.symm k⁻¹, ?_⟩
  have h := congrArg (fun a => (d.modelK.symm a : G)) hk
  simpa only [map_mul, map_inv, MulEquiv.symm_apply_apply, coe_mul, coe_inv,
    inv_inv] using h
end CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore.OrderTwo.Fusion
namespace CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore.OrderTwo
open Fusion
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
variable (d : EarlierSetup κ G)

/-- The fusion witness keeps its original four-group element, an actual
K-conjugator, placement in the indicated extension, and the S-correction
which changes the triple-transposition marking to a transposition. -/
theorem exists_fused_centralizingInvolution
    (hz : d.z = d.zK) (hact : ZConjugateActions d)
    (hout : ¬ rightConjugate d.x (fourZero d) ≤ d.K ⊔ d.SC) :
    ∃ e ∈ fourZero d, e ∉ zpowers d.z ∧
      ∃ (k : d.K) (v : CentralizingInvolution d),
        v.element = (k : G) * (d.x⁻¹ * e * d.x) * (k : G)⁻¹ ∧
        v.element ∈ (d.S ⊓ d.K) ⊔ zpowers (d.x⁻¹ * e * d.x) ∧
        ∃ s : d.S,
          d.toImageSylow (s * ⟨v.element, v.mem_s⟩ * s⁻¹) =
            Identification.sylowEquiv d.imageSylow Holomorph.transposition := by
  classical
  obtain ⟨a, ha, houta⟩ := SetLike.not_le_iff_exists.mp hout
  obtain ⟨e, he, rfl⟩ := ha
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at houta
  let a := d.x⁻¹ * e * d.x
  have haS : a ∈ d.S := d.rightConjugate_le (fourZero_le d |>.trans inf_le_left)
    ⟨e, he, by simp [a]⟩
  have hne : e ≠ 1 := by
    intro h
    apply houta
    simp [h]
  have hzfix : (MulAut.conj d.x⁻¹) d.z = d.z := by
    have hzT : d.z ∈ centerIn (d.T : Subgroup G) := d.center_t ▸ mem_zpowers d.z
    have hc := hzT.2 d.x d.x_mem
    change d.x⁻¹ * d.z * (d.x⁻¹)⁻¹ = d.z
    rw [inv_inv, mul_assoc, ← hc, inv_mul_cancel_left]
  have hez : e ∉ zpowers d.z := by
    intro hez
    have hline : (zpowers d.z).map (MulAut.conj d.x⁻¹).toMonoidHom = zpowers d.z := by
      rw [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, hzfix]
    have ham := mem_map_of_mem (MulAut.conj d.x⁻¹).toMonoidHom hez
    rw [hline] at ham
    apply houta
    apply mem_sup_left
    apply (zpowers_le.mpr (show d.z ∈ d.K from
      hz ▸ (fourZero_le d (zK_mem_fourZero d)).2))
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using ham
  have heo : orderOf e = 2 := by
    apply orderOf_eq_prime _ hne
    simpa only [coe_mul, coe_one, pow_two] using
      congrArg Subtype.val (IsKleinFour.mul_self (⟨e, he⟩ : fourZero d))
  have hao : orderOf a = 2 := by
    simpa only [MulAut.conj_apply, inv_inv] using
      ((MulAut.conj d.x⁻¹).orderOf_eq e).trans heo
  let aH : d.H := ⟨a, d.s_le_h haS⟩
  let β := d.action aH
  have hβi : β ∉ AlternatingSix.ShadowLocal.inner := by
    intro h
    exact houta ((action_inner_iff d aH).mp h)
  have hβo : orderOf β = 2 := by
    apply orderOf_eq_prime
    · have ha2 : aH ^ 2 = 1 := Subtype.ext (hao ▸ pow_orderOf_eq_one a)
      simpa only [map_pow, map_one] using congrArg d.action ha2
    · intro h
      exact hβi (h ▸ one_mem _)
  obtain ⟨q, hq⟩ := fourZero_fused_z d hz e he hne
  have hq' : ((q : G) * d.x)⁻¹ * d.z * ((q : G) * d.x) = a := by
    calc
      _ = d.x⁻¹ * ((q : G)⁻¹ * d.z * q) * d.x := by group
      _ = a := by rw [hq]
  have hβn : β ∈ natural := by
    have h := (hact ((q : G) * d.x) (hq' ▸ haS)).2
    simpa only [hq'] using h
  obtain ⟨k, b, hb, hbc, r, hr⟩ := natural_outer_centralizing_conjugate d.imageSylow β hβo hβn hβi
  let kG : d.K := d.modelK.symm k
  let kH : d.H := ⟨kG, d.k_le_h kG.property⟩
  let wH : d.H := kH * aH * kH⁻¹
  have hwact : d.action wH = (b : AutA6) := by
    change d.action (kH * aH * kH⁻¹) = _
    rw [map_mul, map_mul, map_inv]
    have hkact : d.action kH = MulAut.conj k := by
      rw [d.action_on_K]
      exact congrArg MulAut.conj (d.modelK.apply_symm_apply k)
    rw [hkact]
    exact hb
  have hwS : (wH : G) ∈ d.S := mem_s_of_action_mem d wH (hwact ▸ b.property)
  have hwto : d.toImageSylow ⟨wH, hwS⟩ = b := Subtype.ext hwact
  have hwc : (wH : G) ∈ centralizer ((d.S ⊓ d.K : Subgroup G) : Set G) :=
    centralizes_of_action d ⟨wH, hwS⟩ b hwto hbc
  have hwo : orderOf (wH : G) = 2 :=
    ((MulAut.conj (kG : G)).orderOf_eq a).trans hao
  have hwi : (wH : G) ∉ d.K ⊔ d.SC := by
    intro hw
    have hbinner : (b : AutA6) ∈ AlternatingSix.ShadowLocal.inner :=
      hwact ▸ (action_inner_iff d wH).mpr hw
    have h := (inferInstance : AlternatingSix.ShadowLocal.inner.Normal).conj_mem
      _ hbinner (MulAut.conj k)⁻¹
    rw [← hb] at h
    have heq : (MulAut.conj k)⁻¹ * (MulAut.conj k * β * (MulAut.conj k)⁻¹) *
        ((MulAut.conj k)⁻¹)⁻¹ = β := by group
    exact hβi (heq ▸ h)
  let v : CentralizingInvolution d := ⟨wH, hwS, hwo, hwi, hwc⟩
  have hwext : v.element ∈ (d.S ⊓ d.K) ⊔ zpowers a := by
    have hn : d.H ≤ normalizer (d.K : Set G) :=
      (normal_subgroupOf_iff_le_normalizer d.k_le_h).mp d.normalK
    have hak : a * (kG : G)⁻¹ * a⁻¹ ∈ d.K :=
      (mem_normalizer_iff.mp (hn aH.property) _).mp (d.K.inv_mem kG.property)
    have hwk : (wH : G) * a⁻¹ ∈ d.K := by
      change (kG : G) * a * (kG : G)⁻¹ * a⁻¹ ∈ d.K
      simpa only [mul_assoc] using d.K.mul_mem kG.property hak
    have hws : (wH : G) * a⁻¹ ∈ d.S := d.S.mul_mem hwS (d.S.inv_mem haS)
    have h := ((d.S ⊓ d.K) ⊔ zpowers a).mul_mem
      (mem_sup_left ⟨hws, hwk⟩) (mem_sup_right (mem_zpowers a))
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
  obtain ⟨s, hs⟩ := toImageSylow_surjective d r
  refine ⟨e, he, hez, kG, v, rfl, hwext, s, ?_⟩
  change d.toImageSylow (s * ⟨wH, hwS⟩ * s⁻¹) = _
  rw [map_mul, map_mul, map_inv, hs, hwto, hr]

private theorem marked_transposition_not_inner (P : Sylow 2 AutA6) :
    (Identification.sylowEquiv P Holomorph.transposition : AutA6) ∉
      AlternatingSix.ShadowLocal.inner := by
  intro h
  have hp : Identification.sylowEquiv P Holomorph.transposition ∈ sylowInner P := h
  rw [← Identification.sylowEquiv_innerD, mem_map_equiv,
    MulEquiv.symm_apply_apply, Holomorph.mem_innerD] at hp
  have hn : ¬ ∃ b, Holomorph.innerEmbedding b = Holomorph.transposition := by decide +kernel
  exact hn hp

/-- After the explicit S-correction the actual involution induces the marked
transposition. Its conjugacy provenance still starts in the original fourZero,
although the combined conjugator is in H and need not be in S. -/
theorem exists_fused_transposition_centralizingInvolution
    (hz : d.z = d.zK) (hact : ZConjugateActions d)
    (hout : ¬ rightConjugate d.x (fourZero d) ≤ d.K ⊔ d.SC) :
    ∃ e ∈ fourZero d, e ∉ zpowers d.z ∧
      ∃ (g : d.H) (v : CentralizingInvolution d),
        v.element = (g : G) * (d.x⁻¹ * e * d.x) * (g : G)⁻¹ ∧
        d.toImageSylow ⟨v.element, v.mem_s⟩ =
          Identification.sylowEquiv d.imageSylow Holomorph.transposition := by
  obtain ⟨e, he, hez, k, v, hv, _, s, hs⟩ :=
    exists_fused_centralizingInvolution d hz hact hout
  let w : d.S := s * ⟨v.element, v.mem_s⟩ * s⁻¹
  have hwo : orderOf (w : G) = 2 :=
    ((MulAut.conj (s : G)).orderOf_eq v.element).trans v.order_two
  have hwc : (w : G) ∈ centralizer ((d.S ⊓ d.K : Subgroup G) : Set G) :=
    centralizes_of_action d w _ hs (Fusion.marked_centralizes d.imageSylow).1
  have hwi : (w : G) ∉ d.K ⊔ d.SC := by
    intro hw
    have h := (action_inner_iff d ⟨w, d.s_le_h w.property⟩).mpr hw
    have ha := congrArg (fun b : d.imageSylow => (b : AutA6)) hs
    change d.action ⟨w, d.s_le_h w.property⟩ = _ at ha
    rw [ha] at h
    exact marked_transposition_not_inner d.imageSylow h
  let wv : CentralizingInvolution d := ⟨w, w.property, hwo, hwi, hwc⟩
  let g : d.H := ⟨(s : G) * k, d.H.mul_mem (d.s_le_h s.property) (d.k_le_h k.property)⟩
  refine ⟨e, he, hez, g, wv, ?_, hs⟩
  change (s : G) * v.element * (s : G)⁻¹ =
    ((s : G) * k) * (d.x⁻¹ * e * d.x) * ((s : G) * k)⁻¹
  rw [hv]
  group

/-- The contrary order-two branch has an actual centralizing involution. -/
theorem centralizingInvolution_of_not_contained
    (_hEA : IsElementaryAbelian 2 d.SC) (_hcard : Nat.card d.SC = 2)
    (hz : d.z = d.zK) (hact : ZConjugateActions d)
    (hout : ¬ rightConjugate d.x (fourZero d) ≤ d.K ⊔ d.SC) :
    Nonempty (CentralizingInvolution d) := by
  obtain ⟨e, he, hez, g, v, hv, hs⟩ :=
    exists_fused_transposition_centralizingInvolution d hz hact hout
  exact ⟨v⟩
end CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore.OrderTwo
