module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.Simplicity.Centralizers.Local
/-!
# The normal odd layer in GLS Lemma 4.10

Suppose `G = N⟨z⟩`, with `N` normal and `z` an involution, and let
`L` be a normal subgroup of `H` containing `z`. If the intrinsic intersection
of `L` with `N` has odd order, then `z` is central modulo `O₂′(H)` and
`L ≤ O₂′(H)⟨z⟩`.

The intersection `K = L ⊓ (N ∩ H)` is normal in `H`. An explicit equivalence
transfers the given odd order to `K`, so `K ≤ O₂′(H)`. The ambient supplement
implies `L = K⟨z⟩`. Thus every element of `L` maps to either one or the image
of `z` in the quotient. Normality of `L` forces conjugation to fix that image.
All intersections and normality statements remain relative to `H` and `L`.

This is the odd-layer calculation used in clauses (a) and (b), rather than
an assertion of the complete source lemma. The assumption `z ∉ N` is retained
in the source-facing interface; the calculation also works without it.

Source: GLS, Volume 4, Chapter 2, Lemma 4.10,
`refs/KGroup/GLS4/Chapter2.tex`, lines 692–704.
-/

namespace BenderSuzuki.ZD.Centralizers
open PFAppendixIII
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem layer_cover (H N : Subgroup G) [N.Normal]
    {z : G} (hzH : z ∈ H) (hgen : N ⊔ Subgroup.zpowers z = ⊤)
    (L : Subgroup H) (hzL : (⟨z, hzH⟩ : H) ∈ L) :
    L = (L ⊓ N.comap H.subtype) ⊔ Subgroup.zpowers (⟨z, hzH⟩ : H) := by
  apply le_antisymm
  · intro x hx
    have hxG : (x : G) ∈ N ⊔ Subgroup.zpowers z := by rw [hgen]; trivial
    obtain ⟨n, hn, a, ha, hna⟩ := Subgroup.mem_sup_of_normal_left.mp hxG
    have ha' : a ∈ (Subgroup.zpowers (⟨z, hzH⟩ : H)).map H.subtype := by
      simpa only [MonoidHom.map_zpowers, Subgroup.coe_subtype] using ha
    obtain ⟨b, hb, hba⟩ := ha'
    have hbL : b ∈ L := (Subgroup.zpowers_le.mpr hzL) hb
    have hxbN : x * b⁻¹ ∈ N.comap H.subtype := by
      change (x : G) * (b : G)⁻¹ ∈ N
      change (b : G) = a at hba
      rw [hba, ← hna, mul_inv_cancel_right]
      exact hn
    have hxb : x * b⁻¹ ∈ L ⊓ N.comap H.subtype :=
      ⟨L.mul_mem hx (L.inv_mem hbL), hxbN⟩
    simpa only [inv_mul_cancel_right] using
      ((L ⊓ N.comap H.subtype) ⊔ Subgroup.zpowers (⟨z, hzH⟩ : H)).mul_mem
        (Subgroup.mem_sup_left hxb) (Subgroup.mem_sup_right hb)
  · exact sup_le inf_le_left (Subgroup.zpowers_le.mpr hzL)

/-- A normal local layer with odd intersection has central involution image in
`H / O₂′(H)` and is covered by the odd core and the distinguished involution. -/
public theorem normal_odd_layer_central_and_cover
    (H N : Subgroup G) [N.Normal] {z : G} (hz : IsInvolution z)
    (hzH : z ∈ H) (_hzN : z ∉ N) (hgen : N ⊔ Subgroup.zpowers z = ⊤)
    (L : Subgroup H) [L.Normal] (hzL : (⟨z, hzH⟩ : H) ∈ L)
    (hodd : Odd (Nat.card ((N.comap H.subtype).comap L.subtype))) :
    QuotientGroup.mk' (pPrimeCore 2 H) (⟨z, hzH⟩ : H) ∈
        Subgroup.center (H ⧸ pPrimeCore 2 H) ∧
      L ≤ pPrimeCore 2 H ⊔ Subgroup.zpowers (⟨z, hzH⟩ : H) := by
  let zH : H := ⟨z, hzH⟩
  let K : Subgroup H := L ⊓ N.comap H.subtype
  let e : ((N.comap H.subtype).comap L.subtype) ≃ K :=
    { toFun := fun x => ⟨x.val.val, x.val.property, x.property⟩
      invFun := fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hKodd : Odd (Nat.card K) := (Nat.card_congr e) ▸ hodd
  have hKcore : K ≤ pPrimeCore 2 H :=
    le_sSup ⟨inferInstance, Nat.coprime_two_left.mpr hKodd⟩
  have hcover : L = K ⊔ Subgroup.zpowers zH := layer_cover H N hzH hgen L hzL
  have hle : L ≤ pPrimeCore 2 H ⊔ Subgroup.zpowers zH := by
    rw [hcover]
    exact sup_le_sup_right hKcore _
  refine ⟨?_, hle⟩
  let q := QuotientGroup.mk' (pPrimeCore 2 H)
  have hcases (x : H) (hx : x ∈ L) : q x = 1 ∨ q x = q zH := by
    rw [hcover] at hx
    obtain ⟨k, hk, a, ha, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
    have hkq : q k = 1 := (QuotientGroup.eq_one_iff k).mpr (hKcore hk)
    have hzord : orderOf zH = 2 := by
      rw [← Subgroup.orderOf_coe zH]
      exact orderOf_eq_prime_iff.mpr ⟨hz.sq_eq_one, hz.ne_one⟩
    classical
    rw [mem_zpowers_iff_mem_range_orderOf, hzord] at ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    have hi' : i < 2 := Finset.mem_range.mp hi
    interval_cases i <;> simp [map_mul, hkq]
  apply Subgroup.mem_center_iff.mpr
  intro y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 H) y
  have hc := hcases (g * zH * g⁻¹)
    ((inferInstance : L.Normal).conj_mem zH hzL g)
  simp only [map_mul, map_inv] at hc
  rcases hc with h1 | hzq
  · have hz1 : q zH = 1 := by
      have := congrArg (fun t => (q g)⁻¹ * t * q g) h1
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, mul_one,
        inv_mul_cancel] using this
    change q g * q zH = q zH * q g
    simp only [hz1, mul_one, one_mul]
  · exact mul_inv_eq_iff_eq_mul.mp hzq
end BenderSuzuki.ZD.Centralizers
