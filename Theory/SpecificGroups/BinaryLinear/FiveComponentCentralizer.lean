module

public import Theory.GroupAction.FiveThirtyTwoCentralizer
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Centralizers of centerless subgroups of order 360 in GL₅(2)

A subgroup of order 360 contains a subgroup of order five. On the actual
binary natural module, the centralizer of this five-subgroup has order
dividing fifteen. A centerless subgroup and its centralizer form a direct
product inside GL₅(2). The standard GL order formula then makes the
centralizer order divide 27776, which is coprime to fifteen. Thus the
centralizer is trivial.

In particular this applies to every embedded A₆, without an embedding
classification or an involution-table assumption. The natural action is
constructed from the given linear maps; the matrix comparison is the
actual change between the matrix and natural-action models.

Source: the PSL₅(2) case in Aschbacher–Smith, 16.1.7(3e) and 16.3.5,
combined manuscript of 1 March 2004, printed pp.1172 and 1178–1179.
-/

open Subgroup
open scoped IsMulCommutative
open BinaryLinear.OuterCyclic

namespace BinaryLinear.FiveComponentCentralizer
private def natural : LinearGroup 5 →* MulAut (Multiplicative (Space 5)) where
  toFun g := g.toAddEquiv.toMultiplicative
  map_one' := by ext x; rfl
  map_mul' _ _ := by ext x; rfl

private theorem natural_injective : Function.Injective natural := by
  intro g h hh
  apply LinearEquiv.ext
  intro v
  exact congrArg Multiplicative.toAdd (MulEquiv.congr_fun hh (Multiplicative.ofAdd v))

private instance : Finite (LinearGroup 5) := Finite.of_injective natural natural_injective

private theorem linearGroup_card : Nat.card (LinearGroup 5) = 9999360 := by
  calc
    Nat.card (LinearGroup 5) =
        Nat.card (Matrix.GeneralLinearGroup (Fin 5) (ZMod 2)) :=
      (Nat.card_congr (matrixEquivLinear 5).toEquiv).symm
    _ = ∏ i : Fin 5, (Fintype.card (ZMod 2) ^ 5 - Fintype.card (ZMod 2) ^ i.val) :=
      Matrix.card_GL_field (𝔽 := ZMod 2) 5
    _ = 9999360 := by decide

/-- Every centerless subgroup of order 360 in the actual binary natural
linear group of degree five has trivial ambient centralizer. -/
public theorem centralizer_eq_bot (P : Subgroup (LinearGroup 5))
    (hP : Nat.card P = 360) (hz : center P = ⊥) :
    centralizer (P : Set (LinearGroup 5)) = ⊥ := by
  let V := Multiplicative (Space 5)
  let : MulDistribMulAction (LinearGroup 5) V := MulDistribMulAction.compHom V natural
  let : FaithfulSMul (LinearGroup 5) V := ⟨by
    intro a b hab
    apply natural_injective
    apply MulEquiv.ext
    intro v
    exact hab v⟩
  have hV : Nat.card V = 32 := by
    change Nat.card (Fin 5 → ZMod 2) = 32
    rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]
    decide
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨A₀, hA₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := P) 5
    (n := 1) (by rw [hP]; decide)
  let A := A₀.map P.subtype
  have hA : Nat.card A = 5 := by
    rw [card_map_of_injective P.subtype_injective]
    simpa using hA₀
  let C := centralizer (P : Set (LinearGroup 5))
  have hC15 : Nat.card C ∣ 15 :=
    (card_dvd_of_le (centralizer_le (map_subtype_le A₀))).trans
      (Subgroup.FiveThirtyTwo.centralizer_card_dvd_fifteen (V := V) A hA hV)
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
  have hprod : Nat.card (P ⊔ C : Subgroup (LinearGroup 5)) = 360 * Nat.card C := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint P C
      (centralizer_le_normalizer _) hdisj, hP]
  have hd : 360 * Nat.card C ∣ 360 * 27776 := by
    have hh := (P ⊔ C).card_subgroup_dvd_card
    rw [hprod, linearGroup_card] at hh
    exact hh
  have hc : Nat.card C = 1 := Nat.eq_one_of_dvd_coprimes
    (by decide : Nat.Coprime 15 27776) hC15
    (Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 360) hd)
  exact Subgroup.card_eq_one.mp hc
end BinaryLinear.FiveComponentCentralizer
