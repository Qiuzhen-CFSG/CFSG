module

public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.LieFamilies.Actions
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.LieFamilies.Exceptional.Rows

/-!
# The derived binary G₂ comparison

The earlier root rows identify the inner residual with the concrete
quaternion--cubic subgroup of order 24 and the outer residual with A₄.
The centerless clause is exactly the G₂(2)′ case of 16.1.2(1); it remains
an explicit earlier multiplier input. Conjugation transports that clause
to the other component, without identifying their central images.

The actual containment and relative normality then give a quotient of
order two of O²(C_L(r)). A finite two-residual has no such quotient.
Containment alone would not suffice for this endpoint.

Source: Aschbacher--Smith, 16.1.2(1), 16.1.4(1), printed pp.1170--1171,
and proof of 16.4.11(2), p.1193, combined manuscript (1 March 2004).
-/

public section
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.LieFamilies
open Subgroup Theory.GroupTheory LiePreliminaries Exceptional
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- The binary G₂ constructor, conditional on its source root rows and the
centerless clause of 16.1.2. The full G₂(2) action is retained in the rows. -/
theorem not_g2_derived_quotient (d : Contrary T z L g R r)
    (rows : BinaryG2InvolutionRows) (hZ : center L = ⊥)
    (e : (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  let c := (centerQuotientEquivTwoCore (component_oddCore d)).trans e
  obtain ⟨_, _, _, _, ⟨ei⟩⟩ := rows.inner_root (innerAction d c)
    (innerAction_order d c) (innerAction_inner d c)
  obtain ⟨_, _, _, _, ⟨eo⟩⟩ := rows.outer_root (outerAction d c)
    (outerAction_order d c) (outerAction_outer d c)
  have hZM : center (L.conjBy g) = ⊥ := by
    apply Subgroup.card_eq_one.mp
    let ec : L ≃* L.conjBy g := (MulAut.conj g).subgroupMap L
    have hc := Nat.card_congr (centerCongr ec).toEquiv
    rw [hZ, card_bot] at hc
    exact hc.symm
  let X := residual L r
  let Y := residual (L.conjBy g) z
  have hX : Nat.card X = 24 := by
    let ex := (centralImageEquiv ((residual_le L r).trans inf_le_left) hZ).trans
      ((innerResidualEquiv d c).trans ei)
    exact (Nat.card_congr ex.toEquiv).trans Atlas.G2.BinaryParabolicPair.ResidualAction.card_K
  have hY : Nat.card Y = 12 := by
    let ey := (centralImageEquiv
      ((residual_le (L.conjBy g) z).trans inf_le_left) hZM).trans
      ((outerResidualEquiv d c).trans eo)
    rw [Nat.card_congr ey.toEquiv, nat_card_alternatingGroup]
    norm_num
  let N := Y.subgroupOf X
  let : N.Normal := d.residual_normal.2.1
  have hN : Nat.card N = 12 :=
    (Nat.card_congr (subgroupOfEquivOfLe d.residual_normal.1).toEquiv).trans hY
  have hidx : N.index = 2 := by
    have hc := N.card_mul_index
    rw [hN, hX] at hc
    omega
  have hp : IsPGroup 2 (X ⧸ N) := IsPGroup.of_card (n := 1) (by
    change N.index = 2 ^ 1
    simpa using hidx)
  have hperfect : IsPPerfect 2 X :=
    isPPerfect_embedded_pResidual 2 (L ⊓ centralizer ({r} : Set G))
  have htop := hperfect N inferInstance hp
  rw [htop, index_top] at hidx
  contradiction

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.LieFamilies
