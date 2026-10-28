module

public import Theory.SpecificGroups.BinaryLinear.FiveComponentCentralizer

/-!
# Centralizers of A₆-sized subgroups in the two binary linear models

A centerless subgroup of order 360 in GL₄(2) has trivial centralizer.
A subgroup of order five makes that centralizer's order divide fifteen,
using the faithful action on the sixteen-element natural module. The
direct-product order calculation makes the same order divide 56. These
bounds are coprime. Together with the degree-five calculation this treats
both binary models, for every embedding of the subgroup.

Source: Aschbacher–Smith, E.6.23, combined manuscript of 1 March 2004,
printed p.254 (PDF p.265), the assertion that the actual involution is outer.
-/

open Subgroup BinaryLinear.OuterCyclic

namespace BinaryLinear.SixSubgroupCentralizers

private def natural : LinearGroup 4 →* MulAut (Multiplicative (Space 4)) where
  toFun g := g.toAddEquiv.toMultiplicative
  map_one' := by ext x; rfl
  map_mul' _ _ := by ext x; rfl

private theorem natural_injective : Function.Injective natural := by
  intro g h hh
  apply LinearEquiv.ext
  intro v
  exact congrArg Multiplicative.toAdd (MulEquiv.congr_fun hh (Multiplicative.ofAdd v))

private instance : Finite (LinearGroup 4) := Finite.of_injective natural natural_injective

private theorem linearGroup_card : Nat.card (LinearGroup 4) = 20160 := by
  calc
    Nat.card (LinearGroup 4) =
        Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :=
      (Nat.card_congr (matrixEquivLinear 4).toEquiv).symm
    _ = ∏ i : Fin 4, (Fintype.card (ZMod 2) ^ 4 - Fintype.card (ZMod 2) ^ i.val) :=
      Matrix.card_GL_field (𝔽 := ZMod 2) 4
    _ = 20160 := by decide

/-- The degree-four counterpart of the degree-five centralizer calculation. -/
public theorem centralizer_eq_bot_four (P : Subgroup (LinearGroup 4))
    (hP : Nat.card P = 360) (hz : center P = ⊥) :
    centralizer (P : Set (LinearGroup 4)) = ⊥ := by
  let V := Multiplicative (Space 4)
  let : MulDistribMulAction (LinearGroup 4) V := MulDistribMulAction.compHom V natural
  let : FaithfulSMul (LinearGroup 4) V := ⟨by
    intro a b hab
    apply natural_injective
    apply MulEquiv.ext
    intro v
    exact hab v⟩
  have hV : Nat.card V = 16 := by
    change Nat.card (Fin 4 → ZMod 2) = 16
    rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]
    decide
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨A₀, hA₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := P) 5
    (n := 1) (by rw [hP]; decide)
  let A := A₀.map P.subtype
  have hA : Nat.card A = 5 := by
    rw [card_map_of_injective P.subtype_injective]
    simpa using hA₀
  let C := centralizer (P : Set (LinearGroup 4))
  have hC15 : Nat.card C ∣ 15 :=
    (card_dvd_of_le (centralizer_le (map_subtype_le A₀))).trans
      (card_centralizer_five_dvd_fifteen (V := V) A hA hV)
  have hdisj : Disjoint P C := by
    apply disjoint_iff_inf_le.mpr
    intro x hx
    have hxc : (⟨x, hx.1⟩ : P) ∈ center P := by
      apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      exact mem_centralizer_iff.mp hx.2 y.val y.property
    rw [hz, mem_bot] at hxc
    exact mem_bot.mpr (congrArg Subtype.val hxc)
  have hprod : Nat.card (P ⊔ C : Subgroup (LinearGroup 4)) = 360 * Nat.card C := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint P C
      (centralizer_le_normalizer _) hdisj, hP]
  have hd : 360 * Nat.card C ∣ 360 * 56 := by
    have hh := (P ⊔ C).card_subgroup_dvd_card
    rw [hprod, linearGroup_card] at hh
    exact hh
  have hc : Nat.card C = 1 := Nat.eq_one_of_dvd_coprimes
    (by decide : Nat.Coprime 15 56) hC15
    (Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 360) hd)
  exact Subgroup.card_eq_one.mp hc

/-- Uniform centralizer rigidity in the two actual binary natural models. -/
public theorem centralizer_eq_bot {n : ℕ} (hn : n = 4 ∨ n = 5)
    (P : Subgroup (LinearGroup n)) (hP : Nat.card P = 360) (hz : center P = ⊥) :
    centralizer (P : Set (LinearGroup n)) = ⊥ := by
  rcases hn with rfl | rfl
  · exact centralizer_eq_bot_four P hP hz
  · exact FiveComponentCentralizer.centralizer_eq_bot P hP hz

end BinaryLinear.SixSubgroupCentralizers
