module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic

/-!
# Sylow subgroups and a single involution class

In a finite group with one nonempty conjugacy class of involutions, each
involution centralizer has odd index. A Sylow two-subgroup has a nontrivial
center and hence a central involution; conjugacy carries this Sylow subgroup
into any specified involution centralizer. Index divisibility gives oddness.

An explicit centralizer model can therefore transport its Sylow subgroups to
any ambient Sylow subgroup. This avoids ambient matrix-group order formulas
in applications to SL₃ and SU₃.

Source: the Sylow reduction for Aschbacher–Smith, *The Classification of
Quasithin Groups*, A.3.21(a)–(b), printed p. 55.
-/

namespace Sylow
/-- A Sylow two-subgroup of a finite group of even order centralizes an involution. -/
public theorem exists_central_involution {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (hG : 2 ∣ Nat.card G) :
    ∃ z : G, orderOf z = 2 ∧ (T : Subgroup G) ≤ Subgroup.centralizer {z} := by
  let : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot _).mpr (T.ne_bot_of_dvd_card hG)
  let := T.isPGroup'.center_nontrivial
  have hZ : IsPGroup 2 (Subgroup.center T) := T.isPGroup'.to_subgroup _
  obtain ⟨n, hn, hc⟩ := hZ.nontrivial_iff_card.mp inferInstance
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center T) 2
    (hc ▸ dvd_pow_self 2 (by omega : n ≠ 0))
  refine ⟨z.val.val, ?_, ?_⟩
  · simpa only [Subgroup.orderOf_coe] using hz
  · intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_center_iff.mp z.property (⟨x, hx⟩ : T)))
end Sylow

namespace Subgroup
/-- A single nonempty involution class forces every involution centralizer to have odd index. -/
public theorem odd_index_centralizer_of_one_involution_class {G : Type*} [Group G] [Finite G]
    (z : G) (hz : orderOf z = 2)
    (hconj : ∀ w : G, orderOf w = 2 → IsConj w z) :
    Odd (centralizer ({z} : Set G)).index := by
  let T : Sylow 2 G := Classical.choice inferInstance
  obtain ⟨w, hw, hT⟩ := T.exists_central_involution (hz ▸ _root_.orderOf_dvd_natCard z)
  obtain ⟨g, hg⟩ := isConj_iff.mp (hconj w hw)
  let e := MulAut.conj g
  have hmap : (T : Subgroup G).map e.toMonoidHom ≤ centralizer {z} := by
    apply le_trans (map_mono hT)
    have h := map_centralizer_le_centralizer_image ({w} : Set G) e.toMonoidHom
    simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom, show e w = z from hg] using h
  apply Nat.not_even_iff_odd.mp
  intro he
  apply T.not_dvd_index
  have hd := (even_iff_two_dvd.mp he).trans (index_dvd_of_le hmap)
  rwa [index_map_of_bijective e.bijective] at hd

/-- A Sylow subgroup of an explicit model of an odd-index subgroup is isomorphic to every ambient Sylow two-subgroup. -/
public theorem sylow_equiv_of_odd_index {G K : Type*} [Group G] [Finite G] [Group K] [Finite K]
    (H : Subgroup G) (hH : Odd H.index) (e : H ≃* K)
    (T : Sylow 2 G) (P : Sylow 2 K) : Nonempty (T ≃* P) := by
  let Q := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let R : Subgroup G := (Q : Subgroup H).map H.subtype
  have hR : IsPGroup 2 R := Q.isPGroup'.map H.subtype
  have hi : ¬ 2 ∣ R.index := by
    rw [show R.index = (Q : Subgroup H).index * H.index from index_map_subtype _]
    exact Nat.prime_two.not_dvd_mul Q.not_dvd_index hH.not_two_dvd_nat
  let S : Sylow 2 G := hR.toSylow hi
  let eQ : Q ≃* R := (Q : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective
  let eP : P ≃* Q := (P : Subgroup K).equivMapOfInjective e.symm.toMonoidHom e.symm.injective
  exact ⟨(T.equiv S).trans (eQ.symm.trans eP.symm)⟩
end Subgroup
