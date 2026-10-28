module

public import Theory.GroupTheory.SylowNormalCenterIntersection
public import Theory.GroupTheory.PGroup.NormalizedSylowConjugation
public import Theory.ElementaryAbelian.Basic

/-!
# Positioning an elementary actor by its inner involution

Suppose a normal subgroup has a single class of involutions. An elementary
actor whose intersection with that subgroup has order two can be conjugated
into any fixed Sylow two-subgroup so that its inner involution is central in
the Sylow. First choose an involution in the normal subgroup's intersection
with the Sylow center. Conjugate the original involution to it, then position
the whole actor using Sylow conjugacy inside its centralizer.

This retains a conjugate of the whole actor, rather than taking a subgroup
of it. The application is the order-four outer-family case of
Aschbacher--Smith, E.1.14(7), printed p.214.
-/

public section
open Subgroup
open scoped IsMulCommutative

/-- Position the entire actor with its inner involution central in the specified
Sylow. No assertion about an arbitrary centralizer intersection being Sylow
is used: the final conjugation takes place in a centralizer containing T. -/
theorem Subgroup.exists_conjugate_actor_with_sylow_central_involution {G : Type*} [Group G] [Finite G]
    (L : Subgroup G) [L.Normal] (T : Sylow 2 G)
    (hconj : ∀ x y : L, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hinter : Nat.card (A ⊓ L : Subgroup G) = 2) :
    ∃ (g z : G), orderOf z = 2 ∧ z ∈ L ∧
      z ∈ A.map (MulAut.conj g).toMonoidHom ∧
      A.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
      (T : Subgroup G) ≤ centralizer ({z} : Set G) := by
  have hd : 2 ∣ Nat.card L := hinter ▸ card_dvd_of_le (show A ⊓ L ≤ L from inf_le_right)
  obtain ⟨x, hx, hx1, hxL⟩ := T.exists_ne_one_mem_center_of_normal L hd
  let n := orderOf x / 2
  have hxn : orderOf (x ^ n) = 2 :=
    orderOf_pow_orderOf_div (orderOf_pos x).ne' (T.isPGroup'.dvd_orderOf hx1)
  let z : G := (x ^ n : T)
  have hz : orderOf z = 2 := by simpa only [z, orderOf_coe] using hxn
  have hzL : z ∈ L := L.pow_mem hxL n
  have hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G) := by
    intro t ht
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mem_center_iff.mp ((center T).pow_mem hx n) ⟨t, ht⟩)
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := (A ⊓ L : Subgroup G)) 2
    (by rw [hinter])
  let uL : L := ⟨u, u.property.2⟩
  have huL : orderOf uL = 2 := by simpa only [uL, orderOf_mk, orderOf_coe] using hu
  have hzLorder : orderOf (⟨z, hzL⟩ : L) = 2 := by simpa only [orderOf_mk] using hz
  obtain ⟨g, hg⟩ := isConj_iff.mp (hconj uL ⟨z, hzL⟩ huL hzLorder)
  let f := MulAut.conj (g : G)
  let B := A.map f.toMonoidHom
  have hfu : f (u : G) = z := congrArg Subtype.val hg
  have hzB : z ∈ B := hfu ▸ mem_map_of_mem f.toMonoidHom u.property.1
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map f.toMonoidHom
  have hBC : B ≤ centralizer ({z} : Set G) := by
    intro b hb
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm (⟨b, hb⟩ : B) ⟨z, hzB⟩))
  obtain ⟨c, hc, hcT⟩ := IsPGroup.exists_conj_le_sylow_of_normalized T
    (centralizer ({z} : Set G)) B (hTz.trans le_normalizer)
    (IsElementaryAbelian.isPGroup 2 B) hBC
  have hcz : MulAut.conj c z = z := by
    change c * z * c⁻¹ = z
    rw [mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right]
  have heq : B.map (MulAut.conj c).toMonoidHom =
      A.map (MulAut.conj (c * (g : G))).toMonoidHom := by
    rw [map_map]
    congr 1
    ext y
    simp [f, MulAut.conj_apply, mul_assoc]
  refine ⟨c * (g : G), z, hz, hzL, ?_, heq ▸ hcT, hTz⟩
  rw [← heq, ← hcz]
  exact mem_map_of_mem (MulAut.conj c).toMonoidHom hzB
