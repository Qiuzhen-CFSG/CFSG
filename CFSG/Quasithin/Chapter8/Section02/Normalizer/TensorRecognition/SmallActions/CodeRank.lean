module

public import Theory.PGroupCore
public import Theory.Representation.HexacodeAction.ThreeRank
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# The elementary three-subgroup in the cubic code branch

The concrete nonsplit triple cover of A₆ contains the elementary plane
spanned by its central scalar and the hexacode lift `evenX`. Its product
with the rotations of D₆ is elementary of order 27. Given the actual
product identification modulo O₂(Y), a Sylow subgroup of the inverse image
lifts this cube isomorphically across the two-group kernel.

This supplies the rank obstruction in the opening of Proposition 8.2.8(6),
Aschbacher–Smith, printed p.719 (PDF p.736). The hexacode model and its
explicit elements come from the attributed ATLAS imports; no split
replacement for the triple cover is used.
-/

public section

open Subgroup Atlas.Codes Representation.Hexacode
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition.SmallActions

/-- A concrete elementary plane in the nonsplit triple-A₆ model. -/
theorem hexacode_elementary_plane : ∃ E : Subgroup HexEvenAutomorphisms,
    IsElementaryAbelian 3 E ∧ Nat.card E = 9 := by
  let E := zpowers hexEvenZ
  let : IsElementaryAbelian 3 E :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (hexEvenZ_order ▸ pow_orderOf_eq_one hexEvenZ)
  have hE : E ≤ center HexEvenAutomorphisms := by
    rw [← even_kernel_eq_center, hexEvenCoordinate_kernel]
  have hnot : evenX ∉ E := fun h => evenX_not_mem_center (hE h)
  obtain ⟨hp, hc⟩ := IsElementaryAbelian.fixed_join_card E evenX evenX_order
    (E.disjoint_zpowers_of_prime_order_not_mem evenX evenX_order hnot)
    (by
      intro z hz
      exact mem_centralizer_singleton_iff.mpr
        (mem_center_iff.mp (hE hz) evenX).symm)
    (show Nat.card E = 3 ^ 1 by rw [Nat.card_zpowers, hexEvenZ_order, pow_one])
  exact ⟨E ⊔ zpowers evenX, hp, hc⟩

/-- The cubic product action contains an elementary subgroup of order 27. -/
theorem hexacode_dihedral_elementary_cube : ∃ E : Subgroup (HexEvenAutomorphisms × DihedralGroup 3),
    IsElementaryAbelian 3 E ∧ Nat.card E = 27 := by
  obtain ⟨A, hA, hAc⟩ := hexacode_elementary_plane
  let := hA
  let B := zpowers (DihedralGroup.r (1 : ZMod 3))
  have hx : orderOf (DihedralGroup.r (1 : ZMod 3)) = 3 :=
    DihedralGroup.orderOf_r_one
  let : IsElementaryAbelian 3 B :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (DihedralGroup.r_one_pow_n (n := 3))
  let D := A.prod B
  have hD : IsElementaryAbelian 3 D := {
    toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (Prod.ext
      (congrArg Subtype.val (mul_comm' (⟨x.val.1, x.property.1⟩ : A)
        (⟨y.val.1, y.property.1⟩ : A)))
      (congrArg Subtype.val (mul_comm' (⟨x.val.2, x.property.2⟩ : B)
        (⟨y.val.2, y.property.2⟩ : B))))⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro x
      apply Subtype.ext
      exact Prod.ext
        (elemPow_eq_one_of_isElementaryAbelian x.val.1 x.property.1)
        (elemPow_eq_one_of_isElementaryAbelian x.val.2 x.property.2)) }
  refine ⟨D, hD, ?_⟩
  have hB : Nat.card B = 3 := (Nat.card_zpowers _).trans hx
  rw [Nat.card_congr (Subgroup.prodEquiv A B).toEquiv, Nat.card_prod, hAc, hB]

variable {G : Type*} [Group G] [Finite G]

/-- The literal quotient by the two-core lifts the elementary cube. -/
theorem exists_elementary_cube_of_code_cubic_quotient (e : (G ⧸ pCore 2 G) ≃* (HexEvenAutomorphisms × DihedralGroup 3)) :
    ∃ E : Subgroup G, IsElementaryAbelian 3 E ∧ Nat.card E = 27 := by
  obtain ⟨D, hD, hDc⟩ := hexacode_dihedral_elementary_cube
  let := hD
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
  have hs : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 G := by
    ext x
    change e (QuotientGroup.mk' (pCore 2 G) x) = 1 ↔ x ∈ pCore 2 G
    rw [map_eq_one_iff e e.injective]
    exact QuotientGroup.eq_one_iff x
  have hc : Nat.Coprime 3 (Nat.card f.ker) := by
    rw [hk]
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  obtain ⟨E, hE, _, hEc⟩ :=
    exists_elementaryAbelian_map_eq_of_surjective_coprime f hs hc D
  exact ⟨E, hE, hEc.trans hDc⟩

end CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition.SmallActions
