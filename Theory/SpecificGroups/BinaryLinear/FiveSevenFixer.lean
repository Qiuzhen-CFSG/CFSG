module

public import Theory.SpecificGroups.BinaryLinear.FiveSevenGraph
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic
public import Theory.GroupAction.FiveThirtyTwoCentralizer

/-!
# Automorphisms of GL₅(2) fixing elements of orders five and seven

The proved inner/graph coverage separates the two cases. A graph automorphism
cannot fix a seven-element, by the reciprocal-characteristic-polynomial
obstruction. An inner automorphism fixing a five-subgroup is induced by an
element of its centralizer, whose order divides fifteen on the actual natural
module. Consequently the automorphism itself has order dividing fifteen.

Source: the PSL₅(2) case of the Theorem C inspection in Aschbacher–Smith,
combined manuscript (1 March 2004), E.6.18, printed p.252. The argument uses
actual automorphisms and the natural binary action, without a centralizer table.
-/

open Subgroup BinaryLinear.OuterCyclic
open scoped IsMulCommutative

namespace BinaryLinear.FiveSevenFixer

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

private theorem centralizer_five (A : Subgroup (LinearGroup 5)) (hA : Nat.card A = 5) :
    Nat.card (centralizer (A : Set (LinearGroup 5))) ∣ 15 := by
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
  exact Subgroup.FiveThirtyTwo.centralizer_card_dvd_fifteen (V := V) A hA hV

/-- An automorphism fixing a five-subgroup pointwise and a seven-element
has odd order dividing fifteen. -/
public theorem order_dvd_fifteen (A : Subgroup (LinearGroup 5)) (hA : Nat.card A = 5)
    (x : LinearGroup 5) (hx : orderOf x = 7) (a : MulAut (LinearGroup 5))
    (hfix : ∀ y ∈ A, a y = y) (hxfix : a x = x) : orderOf a ∣ 15 := by
  obtain ⟨g, hg | hg⟩ := inner_graph (Or.inr rfl) a
  · have hgC : g ∈ centralizer (A : Set (LinearGroup 5)) := by
      apply mem_centralizer_iff.mpr
      intro y hy
      have hf := hfix y hy
      rw [hg, MulAut.conj_apply] at hf
      exact (mul_inv_eq_iff_eq_mul.mp hf).symm
    have hd : orderOf g ∣ 15 := by
      have hh := (orderOf_dvd_natCard
        (⟨g, hgC⟩ : centralizer (A : Set (LinearGroup 5)))).trans (centralizer_five A hA)
      simpa only [Subgroup.orderOf_mk] using hh
    rw [hg]
    exact (orderOf_map_dvd (MulAut.conj : LinearGroup 5 →* MulAut (LinearGroup 5)) g).trans hd
  · have he := FiveSevenGraph.graph_fixed_seven_eq_one g x
      (by simpa only [hx] using pow_orderOf_eq_one x) (hg ▸ hxfix)
    rw [he, orderOf_one] at hx
    omega
end BinaryLinear.FiveSevenFixer
