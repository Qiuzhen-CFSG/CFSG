module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.Simplicity.Centralizers.Local
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Theory.GroupTheory.ZStar.LocalReduction

/-!
# Sylow isolation for GLS Lemma 4.10(c)

Suppose an involution z lies outside a normal subgroup N and G = N⟨z⟩.
Let H contain z and an ambient Sylow two-subgroup, and let L be generated
inside H by a conjugacy-invariant set of involutions containing z.
If the intrinsic intersection L ∩ N has odd order, then H contains an
ambient Sylow two-subgroup T in which z is central and weakly closed.

Choose a Sylow subgroup of H containing z. Its image is Sylow in G because
H has odd index. An element in T ∩ L ∩ N has both two-power and odd order,
so is trivial. The quotient G/N has order two; hence any two nonidentity
elements of T ∩ L have the same quotient image and are equal. Every
ambient conjugate of z lying in T belongs to L by conjugacy invariance.
This proves weak closure, which also gives centrality by conjugation in T.
In particular, neither source Lemma 4.6 nor the Z-star theorem is assumed.

Source: GLS, Volume 4, Chapter 2, Lemma 4.10(c),
`refs/KGroup/GLS4/Chapter2.tex`, lines 704–708.
-/

namespace BenderSuzuki.ZD.Centralizers
open PFAppendixIII Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

private theorem sylow_in_overgroup (H : Subgroup G)
    (hSyl : ∃ U : Sylow 2 G, (U : Subgroup G) ≤ H)
    {z : G} (hz : IsInvolution z) (hzH : z ∈ H) :
    ∃ T : Sylow 2 G, (T : Subgroup G) ≤ H ∧ z ∈ T := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, hUH⟩ := hSyl
  obtain ⟨Q, hQ⟩ := (isPGroup_zpowers_of_involution (IsInvolution.subtype hz hzH)).exists_le_sylow
  have hindex : ¬ 2 ∣ ((Q : Subgroup H).map H.subtype).index := by
    rw [Subgroup.index_map_subtype]
    exact Nat.prime_two.not_dvd_mul Q.not_dvd_index
      (fun hd => U.not_dvd_index (hd.trans (Subgroup.index_dvd_of_le hUH)))
  refine ⟨(Q.isPGroup'.map H.subtype).toSylow hindex, Subgroup.map_subtype_le _, ?_⟩
  exact Subgroup.mem_map_of_mem H.subtype (hQ (Subgroup.mem_zpowers (⟨z, hzH⟩ : H)))

omit [Finite G] in
private theorem odd_intersection_eq_one
    (H N : Subgroup G) (L : Subgroup H) (T : Sylow 2 G)
    (hodd : Odd (Nat.card ((N.comap H.subtype).comap L.subtype)))
    (x : H) (hxL : x ∈ L) (hxT : (x : G) ∈ T) (hxN : (x : G) ∈ N) : x = 1 := by
  let K := (N.comap H.subtype).comap L.subtype
  let xK : K := ⟨⟨x, hxL⟩, hxN⟩
  have hd : orderOf (x : G) ∣ Nat.card K := by
    have hd := orderOf_dvd_natCard xK
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe] at hd
    exact hd
  have hc : (orderOf (x : G)).Coprime (Nat.card K) := by
    simpa only [Subgroup.orderOf_mk] using
      T.isPGroup'.orderOf_coprime hodd.coprime_two_left (⟨x, hxT⟩ : T)
  apply Subtype.ext
  exact orderOf_eq_one_iff.mp (hc.eq_one_of_dvd hd)

/-- The Sylow isolation configuration from an odd local intersection.
All intersections with N are formed intrinsically inside the local closure. -/
public theorem exists_weaklyClosed_sylow_of_odd_local_intersection
    {Z : Set G} (hInv : ∀ g x : G, x ∈ Z → MulAut.conj g x ∈ Z)
    (hI : ∀ x ∈ Z, IsInvolution x)
    (N : Subgroup G) [N.Normal] {z : G} (hz : z ∈ Z) (hzN : z ∉ N)
    (hgen : N ⊔ Subgroup.zpowers z = ⊤)
    (H : Subgroup G) (hzH : z ∈ H)
    (hSyl : ∃ U : Sylow 2 G, (U : Subgroup G) ≤ H)
    (hodd : Odd (Nat.card ((N.comap H.subtype).comap
      (Subgroup.closure (H.subtype ⁻¹' Z)).subtype))) :
    ∃ T : Sylow 2 G, (T : Subgroup G) ≤ H ∧ z ∈ T ∧
      (∀ t : T, Commute z (t : G)) ∧
      Glauberman.ZStar.IsWeaklyClosedInSylow z (T : Subgroup G) := by
  obtain ⟨T, hTH, hzT⟩ := sylow_in_overgroup H hSyl (hI z hz) hzH
  let L := Subgroup.closure (H.subtype ⁻¹' Z)
  let zH : H := ⟨z, hzH⟩
  have hzL : zH ∈ L := Subgroup.subset_closure hz
  have hnorm : z ∈ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    trivial
  have hcard : Nat.card G = 2 * Nat.card N := by
    simpa only [hgen, Subgroup.card_top] using
      Subgroup.card_sup_zpowers_of_normalizing_involution N z (hI z hz).sq_eq_one hzN hnorm
  have hquot : Nat.card (G ⧸ N) = 2 := by
    have heq := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have hpos : 0 < Nat.card N := Nat.card_pos
    nlinarith
  let q := QuotientGroup.mk' N
  have hqz : q z ≠ 1 := fun he => hzN ((QuotientGroup.eq_one_iff z).mp he)
  obtain ⟨a, _, ha⟩ := (Nat.card_eq_two_iff' (1 : G ⧸ N)).mp hquot
  have hweak : Glauberman.ZStar.IsWeaklyClosedInSylow z (T : Subgroup G) := by
    refine ⟨hzT, ?_⟩
    intro g hgT
    let x : H := ⟨g * z * g⁻¹, hTH hgT⟩
    have hxZ : (x : G) ∈ Z := hInv g z hz
    have hxL : x ∈ L := Subgroup.subset_closure hxZ
    have hxN : (x : G) ∉ N := by
      intro hn
      have he := odd_intersection_eq_one H N L T hodd x hxL hgT hn
      exact (hI x hxZ).ne_one (congrArg H.subtype he)
    have hqx : q (x : G) ≠ 1 := fun he => hxN ((QuotientGroup.eq_one_iff (x : G)).mp he)
    have hqeq : q (x : G) = q z := (ha _ hqx).trans (ha _ hqz).symm
    have hxzN : ((x / zH : H) : G) ∈ N := QuotientGroup.eq_iff_div_mem.mp hqeq
    have he : x / zH = 1 := odd_intersection_eq_one H N L T hodd (x / zH)
      (L.div_mem hxL hzL) (T.div_mem hgT hzT) hxzN
    exact congrArg H.subtype (div_eq_one.mp he)
  refine ⟨T, hTH, hzT, ?_, hweak⟩
  intro t
  have he := hweak.2 (t : G) (T.mul_mem (T.mul_mem t.property hzT) (T.inv_mem t.property))
  exact (mul_inv_eq_iff_eq_mul.mp he).symm
end BenderSuzuki.ZD.Centralizers
