module

public import Theory.GroupTheory.CharacteristicAbelianIndexTwoNorm
public import Theory.ElementaryAbelian.Basic

/-!
# A surjective norm forces a characteristic elementary eight

Let an abelian subgroup of order sixteen have index two, and suppose its
square-one elements form the ambient center of order four. If the norm of
the outside coset maps onto the center, its kernel is precisely that center.
Surjectivity gives an outside involution. Every other outside involution is
a central multiple of it. Thus all square-one elements form a characteristic
elementary subgroup containing the center properly, of order at least eight.

This proves the large-norm exclusion in the order-thirty-two extension
argument of Janko–Thompson, Math. Z. 113 (1970), results 1.3–1.4, p.386.
-/

namespace Subgroup

/-- A surjective outside norm makes the full set of involutions into a
characteristic elementary subgroup of order at least eight. -/
public theorem exists_characteristic_elementary_of_surjective_abelian_norm
    {G : Type*} [Group G] [Finite G]
    (A : Subgroup G) [A.Normal] [IsMulCommutative A]
    (hi : A.index = 2) (hA : Nat.card A = 16) (hZ : Nat.card (center G) = 4)
    (hbinary : ∀ x : G, x ∈ center G ↔ x ∈ A ∧ x ^ 2 = 1)
    (t : G) (ht : t ∉ A) (hrange : (abelianConjNorm A t).range = center G) :
    ∃ K : Subgroup G, K.Characteristic ∧ IsElementaryAbelian 2 K ∧ 8 ≤ Nat.card K := by
  let n := abelianConjNorm A t
  have hZA : center G ≤ A := fun x hx => ((hbinary x).mp hx).1
  have hZker : (center G).subgroupOf A ≤ n.ker := by
    intro a ha
    change (a : G) * (t * a * t⁻¹) = 1
    have hcomm : Commute t (a : G) := mem_center_iff.mp ha t
    rw [hcomm.mul_inv_cancel, ← pow_two]
    exact ((hbinary a).mp ha).2
  have hkerCard : Nat.card n.ker = 4 := by
    have hh := n.ker.card_mul_index
    rw [index_ker, hrange, hZ, hA] at hh
    omega
  have hker : (center G).subgroupOf A = n.ker := by
    apply eq_of_le_of_card_ge hZker
    rw [hkerCard, Nat.card_congr (subgroupOfEquivOfLe hZA).toEquiv, hZ]
  have htZ : t ^ 2 ∈ center G := sq_mem_center_of_not_mem_abelian_index_two A hi t ht
  have htrange : (t ^ 2)⁻¹ ∈ n.range := by
    rw [hrange]
    exact (center G).inv_mem htZ
  obtain ⟨a, ha⟩ := htrange
  let s : G := a * t
  have hs : s ^ 2 = 1 := by
    rw [show s = (a : G) * t from rfl, mul_sq_eq_abelianConjNorm_mul_sq, ha,
      inv_mul_cancel]
  have hsA : s ∉ A := by
    intro h
    have hh := A.mul_mem (A.inv_mem a.property) h
    apply ht
    simpa only [s, inv_mul_cancel_left] using hh
  have hdecomp (x : G) (hx : x ^ 2 = 1) :
      x ∈ center G ∨ x * s⁻¹ ∈ center G := by
    by_cases hxA : x ∈ A
    · exact Or.inl ((hbinary x).mpr ⟨hxA, hx⟩)
    · right
      have hb : x * s⁻¹ ∈ A := (A.mul_mem_iff_of_index_two hi).mpr (by
        simp only [A.inv_mem_iff, hxA, hsA])
      let b : A := ⟨x * s⁻¹, hb⟩
      have hbn : n b = 1 := by
        have hmul := mul_sq_eq_abelianConjNorm_mul_sq A s b
        have heq : abelianConjNorm A s b = n b := by
          simp only [abelianConjNorm_apply, n]
          rw [conj_eq_of_not_mem_abelian_index_two A hi t s ht hsA _ b.property]
        rw [heq, hs, mul_one] at hmul
        have hbs : (b : G) * s = x := by dsimp [b]; group
        rw [hbs, hx] at hmul
        exact hmul.symm
      have hk : b ∈ n.ker := hbn
      rwa [← hker] at hk
  have hcomm (x y : G) (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) : Commute x y := by
    rcases hdecomp x hx with hxc | hxc
    · exact (mem_center_iff.mp hxc y).symm
    rcases hdecomp y hy with hyc | hyc
    · exact mem_center_iff.mp hyc x
    have hsy : Commute s y := by
      have hh := (show Commute s (y * s⁻¹) from mem_center_iff.mp hyc s).mul_right
        (Commute.refl s)
      simpa only [inv_mul_cancel_right] using hh
    have hh := (show Commute (x * s⁻¹) y from (mem_center_iff.mp hxc y).symm).mul_left hsy
    simpa only [inv_mul_cancel_right] using hh
  let K : Subgroup G := {
    carrier := {x | x ^ 2 = 1}
    one_mem' := one_pow 2
    mul_mem' := by
      intro x y hx hy
      change (x * y) ^ 2 = 1
      rw [(hcomm x y hx hy).mul_pow, hx, hy, one_mul]
    inv_mem' := by
      intro x hx
      change x⁻¹ ^ 2 = 1
      rw [inv_pow, hx, inv_one] }
  have hKchar : K.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro f x hx
    change (f x) ^ 2 = 1
    rw [← map_pow, show x ^ 2 = 1 from hx, map_one]
  let : IsMulCommutative K := ⟨⟨fun x y => Subtype.ext (hcomm x y x.property y.property)⟩⟩
  let : IsElementaryAbelian 2 K :=
    ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => Subtype.ext x.property)⟩
  refine ⟨K, hKchar, inferInstance, ?_⟩
  have hZK : center G ≤ K := fun x hx => ((hbinary x).mp hx).2
  have hdiv : 4 ∣ Nat.card K := hZ ▸ card_dvd_of_le hZK
  have hgt : 4 < Nat.card K := by
    by_contra hn
    have heq : center G = K := eq_of_le_of_card_ge hZK (by omega)
    have hsZ : s ∈ center G := heq ▸ hs
    exact hsA (hZA hsZ)
  obtain ⟨k, hk⟩ := hdiv
  omega

end Subgroup
