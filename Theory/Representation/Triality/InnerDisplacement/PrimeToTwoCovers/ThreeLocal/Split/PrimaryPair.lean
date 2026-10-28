module

public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Split.Normalizer
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Primary generators diagonalized for a triality reflection

Let U and V be Sylow threes of the extension-field and fixed-field units.
Their product maps onto the chosen primary subgroup of the actual split torus,
by uniqueness of a Sylow subgroup in an abelian group. Choose generators u, v.
The actual norm sends U into V, where squaring is bijective; choose z with
z² = Norm(u). The torus elements (1, v) and (u, z) generate that product.
The central Weyl reflection inverts the first and fixes the second.

Taking m = 3|V| gives positive power exponents m−1 and 1. Since m is odd,
gcd(m, m−2) = 1, as required by the alternating-pairing detector. This treats
arbitrarily large three-parts and keeps the two cyclic factors distinct.

Source: the coroot and torus conventions of GLS3 §§2.3–2.4 and the
nondefining-characteristic calculation underlying Theorem 6.1.4, Tables 6.1.2–3.
-/

@[expose] public section
noncomputable section

namespace Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Split
open Standard Standard.Parabolics Standard.ConcreteBruhat
open Standard.ConcreteBruhat.TorusCoordinates
open PerfectCentralCovering.OddSylow Subgroup

private theorem skew_pair_generates {X Y G : Type*} [Group X] [Group Y] [Group G]
    (f : X × Y →* G) (u : X) (v z : Y)
    (hu : ∀ x, x ∈ zpowers u) (hv : ∀ y, y ∈ zpowers v) :
    closure ({f (1, v), f (u, z)} : Set G) = f.range := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro g (rfl | rfl) <;> exact ⟨_, rfl⟩
  · rintro g ⟨⟨x, y⟩, rfl⟩
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp (hu x)
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (hv ((z ^ i)⁻¹ * y))
    have he : (x, y) = (u, z) ^ i * (1, v) ^ j := by
      ext <;> simp [← hi, hj]
    rw [he, map_mul, map_zpow, map_zpow]
    exact mul_mem (zpow_mem (subset_closure (by simp)) i)
      (zpow_mem (subset_closure (by simp)) j)

private def productSylow {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (U : Sylow 3 X) (V : Sylow 3 Y) : Sylow 3 (X × Y) := by
  have hprod : IsPGroup 3 (U × V) := by
    obtain ⟨a, ha⟩ := U.isPGroup'.exists_card_eq
    obtain ⟨b, hb⟩ := V.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (n := a + b) (by rw [Nat.card_prod, ha, hb, pow_add])
  exact (hprod.of_equiv (Subgroup.prodEquiv (U : Subgroup X) (V : Subgroup Y)).symm).toSylow
    (by
      rw [Subgroup.index_prod]
      exact fun h => (Nat.prime_three.dvd_mul.mp h).elim U.not_dvd_index V.not_dvd_index)

/-- A pair of actual primary torus generators, diagonalized for the central
reflection. No upper bound on either three-primary cyclic factor is imposed. -/
theorem nonempty_primary_pair (n : ℕ) (hn : 0 < n) :
    Nonempty (TorusPair (primaryImage n hn)) := by
  let P := binaryParameters n hn
  have hp : P.prime = 2 := rfl
  let U : Sylow 3 (ExtensionField P)ˣ := Classical.choice inferInstance
  let V : Sylow 3 (fixedField P)ˣ := Classical.choice inferInstance
  let f : U × V →* BinaryCarrier n hn :=
    (torus P).subtype.comp ((torusMulEquiv P hp).toMonoidHom.comp
      ((U : Subgroup (ExtensionField P)ˣ).subtype.prodMap
        (V : Subgroup (fixedField P)ˣ).subtype))
  have hrange : f.range = primaryImage n hn := by
    let : IsMulCommutative (torus P) := by
      apply IsMulCommutative.of_comm
      intro a b
      apply (torusMulEquiv P hp).symm.injective
      simp only [map_mul, mul_comm]
    let : Unique (Sylow 3 (torus P)) := Sylow.unique_of_normal (primary n hn) inferInstance
    have hsy : (productSylow U V).mapSurjective (f := (torusMulEquiv P hp).toMonoidHom) (torusMulEquiv P hp).surjective =
        primary n hn := Subsingleton.elim _ _
    have hs := congrArg (fun Q : Sylow 3 (torus P) => (Q : Subgroup (torus P))) hsy
    change ((U : Subgroup (ExtensionField P)ˣ).prod (V : Subgroup (fixedField P)ˣ)).map
      (torusMulEquiv P hp).toMonoidHom = (primary n hn : Subgroup (torus P)) at hs
    change MonoidHom.range ((torus P).subtype.comp _) = _
    rw [MonoidHom.range_comp, MonoidHom.range_comp]
    rw [MonoidHom.range_prodMap]
    simp only [Subgroup.range_subtype]
    rw [hs]
    rfl
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := U)
  obtain ⟨v, hv⟩ := IsCyclic.exists_generator (α := V)
  have hnorm : normUnit P u.val ∈ V := by
    exact ((U.isPGroup'.map (normUnitHom P)).le_sylow_of_normal V)
      (mem_map.mpr ⟨u.val, u.property, rfl⟩)
  obtain ⟨k, hk⟩ := V.isPGroup'.exists_card_eq
  have hc : (Nat.card V).Coprime 2 := by rw [hk]; exact (by decide : Nat.Coprime 3 2).pow_left k
  obtain ⟨z, hz⟩ := hc.pow_left_bijective.surjective (⟨normUnit P u.val, hnorm⟩ : V)
  let m := 3 * Nat.card V
  have hm : 2 ≤ m := by have := Nat.card_pos (α := V); dsimp [m]; omega
  have hmc : m.Coprime 2 := (by decide : Nat.Coprime 3 2).mul_left hc
  have hvpow : v ^ m = 1 := by
    calc
      v ^ m = (v ^ Nat.card V) ^ 3 := pow_mul' v 3 (Nat.card V)
      _ = 1 := by rw [pow_card_eq_one', one_pow]
  have hleftPow : (f (1, v)) ^ m = 1 := by
    rw [← map_pow]
    simp only [Prod.pow_mk, one_pow, hvpow]
    exact f.map_one
  refine ⟨{
    left := f (1, v)
    right := f (u, z)
    actor := simpleRepresentative P hp .central
    generates := (skew_pair_generates f u v z hu hv).trans hrange
    commute := (Commute.all (1, v) (u, z)).map f
    exponent := m
    leftPower := m - 1
    rightPower := 1
    positive := by simp; omega
    coprime := by simpa only [mul_one, Nat.sub_sub] using (Nat.coprime_self_sub_right hm).mpr hmc
    pow_eq_one := hleftPow
    conjugate_left := ?_
    conjugate_right := ?_ }⟩
  · change simpleRepresentative P hp .central * torusElement P hp 1 v.val *
      (simpleRepresentative P hp .central)⁻¹ = (torusElement P hp 1 v.val) ^ (m - 1)
    rw [central_torusElement_conjugation P hp]
    have hn1 : normUnit P 1 = 1 := (normUnitHom P).map_one
    rw [hn1, one_mul]
    have hinv : torusElement P hp 1 v.val⁻¹ = (torusElement P hp 1 v.val)⁻¹ := by
      simpa only [torusElement, Prod.inv_mk, inv_one, Subgroup.coe_inv] using
        congrArg Subtype.val (map_inv (torusMulEquiv P hp) (1, v.val))
    rw [hinv, pow_sub _ (by omega : 1 ≤ m), pow_one]
    have ht : (torusElement P hp 1 v.val) ^ m = 1 := hleftPow
    rw [ht, one_mul]
  · change simpleRepresentative P hp .central * torusElement P hp u.val z.val *
      (simpleRepresentative P hp .central)⁻¹ = (torusElement P hp u.val z.val) ^ 1
    rw [central_torusElement_conjugation P hp, pow_one]
    have he : z.val ^ 2 = normUnit P u.val := congrArg Subtype.val hz
    rw [← he, pow_two, mul_inv_cancel_right]

end Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Split
