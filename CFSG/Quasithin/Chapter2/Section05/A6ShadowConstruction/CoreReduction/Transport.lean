module

public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction.CoreReduction.Model

/-!
# Transport to the actual A₆ automorphism image

Source: Aschbacher–Smith, printed pp.569–570. The action on `S` has kernel
`S_C`, and its inner part is exactly the faithful image of `S_K`. Relative
normality and the disjointness of the two core factors are preserved in this
transport. These facts make the later quotient calculation applicable.
-/

namespace CFSG.Quasithin.Chapter2.A6ShadowConstruction.CoreReduction

open Subgroup

variable {G : Type*} [Group G] (d : Setup G)

public theorem s_le_h : d.S ≤ d.H := by rw [d.generated]; exact le_sup_right
public theorem k_le_h : d.K ≤ d.H := by rw [d.generated]; exact le_sup_left

/-- Restriction of the supplied compatible action to `S`. -/
@[expose] public def action : d.S →* AutA6 := d.action.comp (inclusion (s_le_h d))

/-- The faithful action of the inner Sylow factor. -/
@[expose] public def skAction : d.sk →* AutA6 :=
  (action d).comp (inclusion (show d.sk ≤ d.S from inf_le_left))

public theorem action_kernel : (action d).ker = d.core.subgroupOf d.S := by
  ext s
  change d.action ⟨s, s_le_h d s.property⟩ = 1 ↔ (s : G) ∈ d.core
  rw [← MonoidHom.mem_ker, d.action_kernel]
  rfl

public theorem conjugate_s : conjugate d.x d.S = d.S :=
  mem_normalizer_iff_map_conj_eq.mp ((normalizer (d.S : Set G)).inv_mem d.x_normalizes)

public theorem conjugate_le {L : Subgroup G} (hL : L ≤ d.S) :
    conjugate d.x L ≤ d.S := (conjugate_s d) ▸ map_mono hL

public theorem conjugate_normal {L : Subgroup G} (hL : L ≤ d.S)
    (hn : (L.subgroupOf d.S).Normal) :
    ((conjugate d.x L).subgroupOf d.S).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer (conjugate_le d hL)).mpr
  have hSN := (normal_subgroupOf_iff_le_normalizer hL).mp hn
  calc
    d.S = conjugate d.x d.S := (conjugate_s d).symm
    _ ≤ (normalizer (L : Set G)).map (MulAut.conj d.x⁻¹).toMonoidHom := map_mono hSN
    _ ≤ normalizer (conjugate d.x L : Set G) := le_normalizer_map _

/-- The conjugate core meets the kernel trivially, inside `S`. -/
public theorem conjugate_disjoint_kernel {L : Subgroup G} (hL : L ≤ d.core) :
    Disjoint ((conjugate d.x L).subgroupOf d.S) (action d).ker := by
  rw [action_kernel]
  apply disjoint_def.mpr
  intro s hsL hsC
  exact Subtype.ext (disjoint_def.mp d.core_disjoint hsC (map_mono hL hsL))

public theorem zK_mem_conjugate_core : d.zK ∈ conjugate d.x d.core :=
  ⟨d.t, d.t_mem, by simpa using d.t_conjugate⟩

public theorem disjoint_core_sk : Disjoint d.core d.sk := by
  apply disjoint_def.mpr
  intro g hgC hgD
  have hz : g ∈ (center d.sk).map d.sk.subtype := by
    refine ⟨⟨g, hgD⟩, mem_center_iff.mpr ?_, rfl⟩
    intro k
    exact Subtype.ext (hgC.2 k k.property.2)
  change g ∈ (center (d.S ⊓ d.K : Subgroup G)).map (d.S ⊓ d.K).subtype at hz
  rw [d.center_sk] at hz
  exact disjoint_def.mp d.core_disjoint hgC
    ((zpowers_le.mpr (zK_mem_conjugate_core d)) hz)

public theorem skAction_injective : Function.Injective (skAction d) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro k hk
  have hker : (⟨k, k.property.1⟩ : d.S) ∈ (action d).ker := hk
  rw [action_kernel] at hker
  exact Subtype.ext (disjoint_def.mp (disjoint_core_sk d) hker k.property)

private theorem action_on_K (k : d.K) :
    d.action ⟨k, k_le_h d k.property⟩ = MulAut.conj (d.modelK k) := by
  ext a : 1
  obtain ⟨b, rfl⟩ := d.modelK.surjective a
  apply d.modelK.symm.injective
  apply Subtype.ext
  rw [d.action_compatible]
  simp [MulAut.conj_apply]

variable [Finite G]

/-- The image Sylow subgroup under the actual surjective action. -/
@[expose] public def imageSylow : Sylow 2 AutA6 :=
  d.sylow.mapSurjective d.action_surjective

public theorem imageSylow_eq_range : (imageSylow d : Subgroup AutA6) = (action d).range := by
  have hSyl : (d.sylow : Subgroup d.H) = d.S.subgroupOf d.H := by
    rw [← d.sylow_eq, subgroupOf, comap_map_eq_self_of_injective d.H.subtype_injective]
  change (d.sylow : Subgroup d.H).map d.action = _
  rw [hSyl]
  ext a
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h, hh⟩, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨⟨s, s_le_h d s.property⟩, s.property, rfl⟩

/-- An inner image has an `S_K` lift because the action kernel lies in `S`. -/
public theorem skAction_range : (skAction d).range = innerSylow (imageSylow d) := by
  ext a
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨?_, d.modelK ⟨k, k.property.2⟩, ?_⟩
    · rw [imageSylow_eq_range]
      exact ⟨⟨k, k.property.1⟩, rfl⟩
    · exact (action_on_K d ⟨k, k.property.2⟩).symm
  · rintro ⟨haP, k, hk⟩
    rw [imageSylow_eq_range] at haP
    obtain ⟨s, hs⟩ := haP
    let kG : d.K := d.modelK.symm k
    let kH : d.H := ⟨kG, k_le_h d kG.property⟩
    let sH : d.H := ⟨s, s_le_h d s.property⟩
    have hkact : d.action kH = a := by
      rw [action_on_K]
      simpa only [kG, d.modelK.apply_symm_apply] using hk
    have hc : sH * kH⁻¹ ∈ d.action.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hkact]
      change action d s * a⁻¹ = 1
      rw [hs, mul_inv_cancel]
    rw [d.action_kernel] at hc
    have hkS : (kG : G) ∈ d.S := by
      have h := d.S.mul_mem (d.S.inv_mem hc.1) s.property
      change (((s : G) * (kG : G)⁻¹)⁻¹ * (s : G)) ∈ d.S at h
      simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] using h
    exact ⟨⟨kG, hkS, kG.property⟩, hkact⟩

/-- The literal inner image is isomorphic to `S_K`, with its specified action. -/
@[expose] public noncomputable def skEquiv : d.sk ≃* innerSylow (imageSylow d) :=
  (MonoidHom.ofInjective (skAction_injective d)).trans
    (MulEquiv.subgroupCongr (skAction_range d))

@[simp] public theorem skEquiv_apply (k : d.sk) :
    (skEquiv d k : AutA6) = skAction d k := rfl

/-- Noncentrality is transported using the actual center of `S_K`. -/
public theorem skAction_noncentral {e : G} (he : e ∈ d.sk)
    (hne : e ∉ zpowers d.zK) :
    skAction d ⟨e, he⟩ ∉
      (center (innerSylow (imageSylow d))).map (innerSylow (imageSylow d)).subtype := by
  rintro ⟨a, ha, hval⟩
  change (a : AutA6) = skAction d ⟨e, he⟩ at hval
  have heZ : (⟨e, he⟩ : d.sk) ∈ center d.sk := by
    apply mem_center_iff.mpr
    intro k
    apply skAction_injective d
    have hc := congrArg Subtype.val (mem_center_iff.mp ha (skEquiv d k))
    simpa only [map_mul, skEquiv_apply, coe_mul, hval] using hc
  apply hne
  rw [← d.center_sk]
  exact ⟨⟨e, he⟩, heZ, rfl⟩

/-- Each involution of the rank-one core is its distinguished involution. -/
public theorem core_involution {c : G} (hc : c ∈ d.core) (hc2 : c ^ 2 = 1) :
    c = 1 ∨ c = d.t := by
  by_cases hc1 : c = 1
  · exact Or.inl hc1
  right
  have hcO : orderOf (⟨c, hc⟩ : d.core) = 2 :=
    orderOf_eq_prime (Subtype.ext hc2) (fun h => hc1 (congrArg Subtype.val h))
  have htO : orderOf (⟨d.t, d.t_mem⟩ : d.core) = 2 :=
    orderOf_eq_prime (Subtype.ext d.t_square) (fun h => d.t_ne_one (congrArg Subtype.val h))
  suffices (⟨c, hc⟩ : d.core) = ⟨d.t, d.t_mem⟩ from congrArg Subtype.val this
  rcases d.alternatives with hf | hf | hf
  · obtain ⟨f⟩ := hf
    let : IsCyclic d.core := isCyclic_of_injective f.toMonoidHom f.injective
    exact IsCyclic.eq_of_orderOf_eq_two hcO htO
  · obtain ⟨f⟩ := hf
    let : IsCyclic d.core := isCyclic_of_injective f.toMonoidHom f.injective
    exact IsCyclic.eq_of_orderOf_eq_two hcO htO
  · obtain ⟨f⟩ := hf
    apply f.injective
    exact QuaternionGroup.eq_of_orderOf_eq_two _ _
      ((f.orderOf_eq _).trans hcO) ((f.orderOf_eq _).trans htO)

omit [Finite G] in
public theorem zK_mem_sk : d.zK ∈ d.sk := by
  have h : d.zK ∈ (center d.sk).map d.sk.subtype := by
    change d.zK ∈ (center (d.S ⊓ d.K : Subgroup G)).map (d.S ⊓ d.K).subtype
    rw [d.center_sk]
    exact mem_zpowers _
  obtain ⟨k, _, hk⟩ := h
  exact hk ▸ k.property

omit [Finite G] in
public theorem t_mem_conjugate_sk : d.t ∈ conjugate d.x d.sk :=
  ⟨d.zK, zK_mem_sk d, by simpa using d.zK_conjugate⟩

omit [Finite G] in
public theorem conjugate_mem {L : Subgroup G} {e : G} (he : e ∈ L) :
    d.x⁻¹ * e * d.x ∈ conjugate d.x L := ⟨e, he, by simp⟩

/-- The conjugate of a noncentral involution of `S_K` has non-inner image.
Being outside `S_K` alone would not suffice: the proof uses the kernel's
unique involution and the disjointness of `S_K` and `S_Kˣ`. -/
public theorem conjugate_involution_noninner {e : G} (he : e ∈ d.sk)
    (he2 : e ^ 2 = 1) (hne : e ∉ zpowers d.zK) :
    action d ⟨d.x⁻¹ * e * d.x,
      conjugate_le d (L := d.sk) inf_le_left (conjugate_mem d he)⟩ ∉ innerSylow (imageSylow d) := by
  let a : d.S := ⟨d.x⁻¹ * e * d.x,
    conjugate_le d (L := d.sk) inf_le_left (conjugate_mem d he)⟩
  have haX : (a : G) ∈ conjugate d.x d.sk := conjugate_mem d he
  have ha2 : a ^ 2 = 1 := by
    apply Subtype.ext
    change (d.x⁻¹ * e * d.x) ^ 2 = 1
    simpa only [map_pow, map_one, MulAut.conj_apply, inv_inv] using
      congrArg (MulAut.conj d.x⁻¹) he2
  intro haD
  rw [← skAction_range] at haD
  obtain ⟨k, hk⟩ := haD
  have hk2 : k ^ 2 = 1 := by
    apply skAction_injective d
    rw [map_pow, map_one, hk]
    exact (map_pow (action d) a 2).symm.trans (by rw [ha2, map_one])
  let kS : d.S := ⟨k, k.property.1⟩
  have hc : (a * kS⁻¹ : d.S) ∈ (action d).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    change action d a * (skAction d k)⁻¹ = 1
    rw [hk, mul_inv_cancel]
  rw [action_kernel] at hc
  have hk2G : (k : G) ^ 2 = 1 := congrArg Subtype.val hk2
  have ha2G : (a : G) ^ 2 = 1 := congrArg Subtype.val ha2
  have hcomm : Commute (a : G) (k : G) :=
    d.sk_centralizes_conjugate k.property a haX
  have hc2 : ((a : G) * (k : G)⁻¹) ^ 2 = 1 := by
    rw [hcomm.inv_right.mul_pow, ha2G, inv_pow, hk2G, inv_one, mul_one]
  have hc' : (a : G) * (k : G)⁻¹ ∈ d.core := hc
  have hcases := core_involution d hc' hc2
  have hcX : (a : G) * (k : G)⁻¹ ∈ conjugate d.x d.sk := by
    rcases hcases with h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact t_mem_conjugate_sk d
  have hkX : (k : G) ∈ conjugate d.x d.sk := by
    have hh := (conjugate d.x d.sk).mul_mem
      ((conjugate d.x d.sk).inv_mem hcX) haX
    simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] using hh
  have hk1 : (k : G) = 1 := disjoint_def.mp d.disjoint_sk_conjugate k.property hkX
  have ha : (a : G) = 1 ∨ (a : G) = d.t := by
    simpa only [hk1, inv_one, mul_one] using hcases
  rcases ha with ha | ha
  · have he1 : e = 1 := by
      have hh := congrArg (fun g : G => d.x * g * d.x⁻¹) ha
      simpa [a, mul_assoc] using hh
    exact hne (he1 ▸ one_mem _)
  · have hez : e = d.zK := by
      have hsame : d.x⁻¹ * e * d.x = d.x⁻¹ * d.zK * d.x := ha.trans d.zK_conjugate.symm
      exact mul_left_cancel (mul_right_cancel hsame)
    exact hne (hez ▸ mem_zpowers _)

end CFSG.Quasithin.Chapter2.A6ShadowConstruction.CoreReduction
