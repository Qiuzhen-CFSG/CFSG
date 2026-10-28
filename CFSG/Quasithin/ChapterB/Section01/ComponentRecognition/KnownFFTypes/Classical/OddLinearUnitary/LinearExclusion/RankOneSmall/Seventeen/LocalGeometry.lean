module
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.Seventeen.LocalGeometry.Diagonal
public import Theory.SpecificGroups.PSL2.SeventeenFourGeometry

/-!
# Literal Frobenius actors and centralizer products for the PSL₂(17) branch

The compatible component is first identified with PSL₂(17) by its universal
cover and the modular two-core argument. The degree-eight obstruction then
removes diagonal outer actors from the actual ambient conjugation image.
The concrete 17:8 pair, involution fusion, and the dihedral four-group product
therefore all transport into the original group G.

These are exactly the two geometric inputs in
`source_exclusion_of_local_calculations`. No displacement or ratio conclusion
is assumed. The independent Frobenius-module calculation and final exclusion
remain with the Seventeen assembly.

Source: Aschbacher--Smith K.2, printed p.453; Guralnick--Malle,
Classification of 2F-modules I, Proposition 4.1, manuscript p.9.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.Seventeen
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : SourceAction ρ)
include h

/-- A four-group in the actual source group has the required centralizer
product, conjugate to the square of the supplied order-eight actor. -/
theorem source_four_group_product
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 17)
    (hd : Module.finrank (ZMod 2) V ≤ 8)
    (r : G) (hr : orderOf r = 8) (A : Subgroup G)
    (hA : IsElementaryTwo A) (hrA : rank A = 2) :
    ∃ t g a b : G, t ∈ A ∧ orderOf t = 2 ∧ Commute g t ∧ a ∈ A ∧ b ∈ A ∧
      IsConj (r ^ 2) (a * (g * b * g⁻¹)) := by
  obtain ⟨e⟩ := source_ambient_equiv_seventeen ρ h hm hd
  let : IsElementaryAbelian 2 A := hA.2
  have hcard : Nat.card A = 4 := by simpa [hrA] using hA.card_eq_two_pow_rank
  let : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hAk : IsKleinFour A := ⟨hcard, IsElementaryAbelian.exponent_eq_prime⟩
  let B := A.map e.toMonoidHom
  let eA : A ≃* B := A.equivMapOfInjective e.toMonoidHom e.injective
  have hBk : IsKleinFour B := {
    card_four := (Nat.card_congr eA.toEquiv).symm.trans hAk.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eA).symm.trans hAk.exponent_two }
  obtain ⟨t, g, a, b, ht, ht2, hgt, ha, hb, hp⟩ :=
    Theory.PSL2.SeventeenGeometry.four_group_product (e r) ((e.orderOf_eq r).trans hr) B hBk
  refine ⟨e.symm t, e.symm g, e.symm a, e.symm b,
    Subgroup.mem_map_equiv.mp ht, (e.symm.orderOf_eq t).trans ht2,
    hgt.map e.symm.toMonoidHom, Subgroup.mem_map_equiv.mp ha,
    Subgroup.mem_map_equiv.mp hb, ?_⟩
  simpa only [MulEquiv.coe_toMonoidHom, map_pow, map_mul, map_inv, MulEquiv.symm_apply_apply] using
    e.symm.toMonoidHom.map_isConj hp

/-- The exact geometric contract for the source PSL₂(17) exclusion: a literal
17:8 pair, full involution fusion, and all four-group centralizer products. -/
theorem source_local_geometry
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 17)
    (hd : Module.finrank (ZMod 2) V ≤ 8) :
    ∃ x r : G, orderOf x = 17 ∧ orderOf r = 8 ∧ r * x * r⁻¹ = x ^ 2 ∧
      (∀ t : G, orderOf t = 2 → IsConj (r ^ 4) t) ∧
      (∀ A : Subgroup G, IsElementaryTwo A → rank A = 2 →
        ∃ t g a b : G, t ∈ A ∧ orderOf t = 2 ∧ Commute g t ∧ a ∈ A ∧ b ∈ A ∧
          IsConj (r ^ 2) (a * (g * b * g⁻¹))) := by
  obtain ⟨x, r, _, hrL, hx, hr, hrel⟩ := source_component_frobenius_actors ρ h hm
  have htop := source_component_eq_top ρ h hm hd
  refine ⟨x, r, hx, hr, hrel, ?_, ?_⟩
  · intro t ht
    apply source_inner_involutions_isConj ρ h hm
      ((generalizedFitting G).pow_mem hrL 4) (htop ▸ mem_top t) ?_ ht
    rw [orderOf_pow, hr]
    decide
  · intro A hA hrA
    exact source_four_group_product ρ h hm hd r hr A hA hrA

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.Seventeen
