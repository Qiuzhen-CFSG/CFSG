module

public import Theory.GroupTheory.InvolutionTransfer
public import Theory.ElementaryAbelian.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Transfer from an elementary-sixteen extension

Suppose the elementary subgroups inside an index-two Sylow section have
order at most eight, while all outside involutions lie in one elementary
sixteen A. Every conjugate of A inside the Sylow subgroup is A. If N(A)
normalizes the inside subgroup L and the centralizers in T of A minus L
are contained in A, Sylow conjugacy shows that those elements have
elementary Sylow centralizers even in the ambient group.

Consequently they cannot fuse with an involution of L that centralizes an
element of order four. Thompson's involution transfer gives the contradiction
when the ambient group has no normal subgroup of index two.

Source: a sufficient local route for the E₁₆ exclusion in Aschbacher–Smith,
Lemma 14.4.5, combined 1 March 2004 manuscript, printed p.1008. The local
involution and order-four hypotheses remain explicit model obligations.
No global nonfusion or fusion-invariant character is assumed.
-/

open Subgroup
open scoped IsMulCommutative

namespace Subgroup

/-- The outside involutions and an inside rank bound force weak closure of
the elementary sixteen subgroup. -/
public theorem elementary_sixteen_weakly_closed_of_outside_involutions
    {G : Type*} [Group G] [Finite G]
    (T L A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 16)
    (hbound : ∀ E : Subgroup G, E ≤ T → E ≤ L → IsElementaryAbelian 2 E →
      Nat.card E ≤ 8)
    (hout : ∀ x ∈ T, x ∉ L → x ^ 2 = 1 → x ∈ A)
    (g : G) (hg : A.map (MulAut.conj g).toMonoidHom ≤ T) :
    A.map (MulAut.conj g).toMonoidHom = A := by
  let E := A.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  have hE : Nat.card E = 16 :=
    (card_map_of_injective (MulAut.conj g).injective).trans hA
  have hn : ¬ E ≤ L := by
    intro h
    have hb := hbound E hg h inferInstance
    omega
  obtain ⟨b, hb, hbL⟩ := SetLike.not_le_iff_exists.mp hn
  have hp (x : G) (hx : x ∈ E) : x ^ 2 = 1 := by
    exact congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 E) (⟨x, hx⟩ : E))
  have hbA := hout b (hg hb) hbL (hp b hb)
  apply eq_of_le_of_card_ge ?_ (by rw [hE, hA])
  intro x hx
  by_cases hxL : x ∈ L
  · have hbxL : b * x ∉ L := by
      intro h
      exact hbL (by simpa only [mul_inv_cancel_right] using L.mul_mem h (L.inv_mem hxL))
    have hbx := hout (b*x) (hg (E.mul_mem hb hx)) hbxL (hp _ (E.mul_mem hb hx))
    simpa only [inv_mul_cancel_left] using A.mul_mem (A.inv_mem hbA) hbx
  · exact hout x (hg hx) hxL (hp x hx)

/-- Weak closure and elementary Sylow centralizers outside L exclude every
commuting element of order four, even in the ambient group. -/
public theorem no_commuting_order_four_of_weakly_closed_elementary
    {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (L A : Subgroup G) [IsElementaryAbelian 2 A]
    (hweak : ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
      A.map (MulAut.conj g).toMonoidHom = A)
    (hnorm : normalizer (A : Set G) ≤ normalizer (L : Set G))
    (hsmall : ∀ x ∈ A, x ∉ L →
      (T : Subgroup G) ⊓ centralizer ({x} : Set G) ≤ A)
    (a : G) (ha : a ∈ A) (haL : a ∉ L) :
    ∀ r : G, Commute a r → orderOf r ≠ 4 := by
  let C := centralizer ({a} : Set G)
  have hAC : A ≤ C := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (A.le_centralizer ha x hx)
  obtain ⟨P, hAP⟩ := ((IsElementaryAbelian.isPGroup 2 A).comap_subtype (K := C)).exists_le_sylow
  obtain ⟨S, hPS⟩ := (P.isPGroup'.map C.subtype).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S T
  have hPT : ((P : Subgroup C).map C.subtype).map (MulAut.conj g).toMonoidHom ≤
      (T : Subgroup G) := by
    rw [← hg]
    exact map_mono hPS
  have hAPT : A.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) := by
    apply le_trans (map_mono ?_) hPT
    intro x hx
    exact mem_map_of_mem C.subtype (hAP (show (⟨x, hAC hx⟩ : C) ∈ A.subgroupOf C from hx))
  have hAg := hweak g hAPT
  have hgL := hnorm (mem_normalizer_iff_map_conj_eq.mpr hAg)
  have hga : MulAut.conj g a ∈ A := hAg ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom ha
  have hgaL : MulAut.conj g a ∉ L := by
    intro h
    exact haL ((mem_normalizer_iff.mp hgL a).mpr h)
  have hPpow (x : P) : x ^ 2 = 1 := by
    have hxT : MulAut.conj g ((x : C) : G) ∈ (T : Subgroup G) :=
      hPT (mem_map_of_mem (MulAut.conj g).toMonoidHom (mem_map_of_mem C.subtype x.property))
    have hxC : MulAut.conj g ((x : C) : G) ∈
        centralizer ({MulAut.conj g a} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      simpa only [map_mul] using
        congrArg (MulAut.conj g) (mem_centralizer_singleton_iff.mp (x : C).property)
    have hxA := hsmall _ hga hgaL ⟨hxT, hxC⟩
    have hx2 : (MulAut.conj g ((x : C) : G)) ^ 2 = 1 :=
      congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A) (⟨_, hxA⟩ : A))
    apply Subtype.ext
    apply Subtype.ext
    apply (MulAut.conj g).injective
    change MulAut.conj g (((x : C) : G) ^ 2) = MulAut.conj g 1
    simpa only [map_pow, map_one] using hx2
  intro r hr hr4
  let rC : C := ⟨r, mem_centralizer_singleton_iff.mpr hr.symm.eq⟩
  have hrC : orderOf rC = 4 := by rw [← Subgroup.orderOf_coe]; exact hr4
  have hp : IsPGroup 2 (zpowers rC) := IsPGroup.of_card (n := 2)
    (by rw [Nat.card_zpowers, hrC]; decide)
  obtain ⟨R, hR⟩ := hp.exists_le_sylow
  let rR : R := ⟨rC, hR (mem_zpowers rC)⟩
  have hr2 : rR ^ 2 = 1 := (R.equiv P).injective (by
    simpa only [map_pow, map_one] using hPpow ((R.equiv P) rR))
  have hdiv : orderOf rC ∣ 2 := orderOf_dvd_of_pow_eq_one
    (congrArg (fun x : R => (x : C)) hr2)
  rw [hrC] at hdiv
  norm_num at hdiv

/-- Transfer eliminates an elementary-sixteen extension once its local
involution centralizers and the inside order-four witnesses are established.
No nonfusion or character-invariance conclusion is assumed. -/
public theorem elementary_sixteen_extension_transfer
    {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (L A : Subgroup G) [IsElementaryAbelian 2 A]
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (hAT : A ≤ (T : Subgroup G)) (hA : Nat.card A = 16)
    (hindex : (L.subgroupOf (T : Subgroup G)).index = 2)
    (hbound : ∀ E : Subgroup G, E ≤ (T : Subgroup G) → E ≤ L →
      IsElementaryAbelian 2 E → Nat.card E ≤ 8)
    (hout : ∀ x ∈ (T : Subgroup G), x ∉ L → x ^ 2 = 1 → x ∈ A)
    (hnorm : normalizer (A : Set G) ≤ normalizer (L : Set G))
    (hsmall : ∀ x ∈ A, x ∉ L →
      (T : Subgroup G) ⊓ centralizer ({x} : Set G) ≤ A)
    (hfour : ∀ y ∈ L, orderOf y = 2 → ∃ r : G, Commute y r ∧ orderOf r = 4) :
    False := by
  have hn : ¬ A ≤ L := by
    intro h
    have hb := hbound A hAT h inferInstance
    omega
  obtain ⟨a, ha, haL⟩ := SetLike.not_le_iff_exists.mp hn
  have ha1 : a ≠ 1 := by intro he; exact haL (he ▸ L.one_mem)
  have ha2 : a ^ 2 = 1 := congrArg Subtype.val
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) (⟨a, ha⟩ : A))
  have hao : orderOf a = 2 := orderOf_eq_prime_iff.mpr ⟨ha2, ha1⟩
  have hweak := elementary_sixteen_weakly_closed_of_outside_involutions
    (T : Subgroup G) L A hA hbound hout
  have hnon := no_commuting_order_four_of_weakly_closed_elementary T L A
    hweak hnorm hsmall a ha haL
  obtain ⟨b, hab, hb⟩ := T.exists_isConj_mem_of_index_two hno
    (L.subgroupOf (T : Subgroup G)) hindex ⟨a, hAT ha⟩
    (by rw [← Subgroup.orderOf_coe]; exact hao)
  obtain ⟨g, hg⟩ := isConj_iff.mp hab
  have hbo : orderOf (b : G) = 2 := by
    rw [← hg]
    exact (MulAut.conj g).orderOf_eq a |>.trans hao
  obtain ⟨r, hr, hr4⟩ := hfour b hb hbo
  have hgr : Commute a (MulAut.conj g⁻¹ r) := by
    have hc := hr.map (MulAut.conj g⁻¹).toMonoidHom
    have hbga : MulAut.conj g⁻¹ (b : G) = a := by
      rw [← hg]
      simp [mul_assoc]
    change Commute (MulAut.conj g⁻¹ (b : G)) (MulAut.conj g⁻¹ r) at hc
    rwa [hbga] at hc
  exact hnon _ hgr ((MulAut.conj g⁻¹).orderOf_eq r |>.trans hr4)

end Subgroup
