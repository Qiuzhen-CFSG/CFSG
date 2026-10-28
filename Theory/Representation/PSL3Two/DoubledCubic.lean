module
public import Theory.Representation.BinaryCubicFixedIndex
public import Theory.Representation.PSL3Two.SmallModuleProperties
public import Theory.GroupAction.NoncentralTwoChiefLength.Native

/-!
# Cubic movement on two natural binary three-spaces

A faithful cubic in SL₃(2) has fixed index four on the natural module.
The upper bound follows because the index is a power of four dividing eight;
faithfulness excludes index one. Fixed indices multiply on the literal direct
sum, so the same cubic has length two on two naturally marked summands.
The final transport retains the actual conjugation action and actor map.

Source application: Aschbacher–Smith, 13.4.10(4), printed p.909, where
these two contributions contradict the original A₆-block chief budget.
-/

public noncomputable section
open Subgroup
namespace BinaryLinearThree
variable {G : Type*} [_root_.Group G] [Finite G]

/-- A faithful cubic in the natural SL₃(2) action has fixed index four. -/
theorem natural_cubic_fixedIndex
    {A : Type*} [_root_.Group A] [Finite A] (hA : Nat.card A = 3)
    (q : A →* BinaryLinearThree.Group) (hq : Function.Injective q) :
    Representation.BinaryFixedPoints.fixedIndex (BinaryLinearThree.W.comp q) = 4 := by
  let ρ := BinaryLinearThree.W.comp q
  have hp : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hb := Representation.BinaryFixedPoints.fixedIndex_le_four_of_card_eight ρ hp
    (by change Nat.card (Fin 3 → ZMod 2) = 8; simp)
  let := Representation.BinaryFixedPoints.action ρ
  let : IsElementaryAbelian 2 (Multiplicative BinaryLinearThree.Vector) :=
    Representation.BinaryGroupAction.elementary
  have hi := FixedPoints.index_eq_four_pow_cubicLength
    (V := Multiplicative BinaryLinearThree.Vector) hp (IsElementaryAbelian.isPGroup 2 _)
  change Representation.BinaryFixedPoints.fixedIndex ρ = _ at hi
  have hn : Representation.BinaryFixedPoints.fixedIndex ρ ≠ 1 := by
    intro hone
    have ht : FixedPoints.subgroup A (Multiplicative BinaryLinearThree.Vector) = ⊤ :=
      index_eq_one.mp hone
    have htriv (a : A) : a = 1 := by
      apply hq
      apply BinaryLinearThree.natural_injective
      rw [q.map_one,BinaryLinearThree.W.map_one]
      apply LinearMap.ext
      intro v
      have hh : a • Multiplicative.ofAdd v = Multiplicative.ofAdd v :=
        (show Multiplicative.ofAdd v ∈ FixedPoints.subgroup A
          (Multiplicative BinaryLinearThree.Vector) from ht ▸ mem_top _) a
      exact congrArg Multiplicative.toAdd hh
    let : Subsingleton A := ⟨fun a b => (htriv a).trans (htriv b).symm⟩
    have hc : Nat.card A = 1 := Nat.card_unique
    omega
  have hpos : 1 ≤ FixedPoints.cubicLength A (Multiplicative BinaryLinearThree.Vector) := by
    by_contra h
    have hz : FixedPoints.cubicLength A (Multiplicative BinaryLinearThree.Vector) = 0 := by omega
    rw [hz,pow_zero] at hi
    exact hn hi
  have hlo := Nat.pow_le_pow_right (n := 4) (by decide : 1 ≤ 4) hpos
  rw [←hi] at hlo
  exact le_antisymm hb (by simpa only [pow_one] using hlo)

/-- An actual nontrivial cubic acts with length two on two identically
marked natural binary three-spaces. -/
theorem doubled_natural_cubic_length
    (A U : Subgroup G) (hA : Nat.card A = 3)
    (hAU : A ≤ normalizer (U : Set G))
    (q : A →* BinaryLinearThree.Group) (hq : Function.Injective q)
    (e : U ≃* Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector))
    (he : letI := conjMulDistribMulActionOfLeNormalizer A U hAU
      ∀ (a : A) (v : U), (e (a • v)).toAdd =
        (Representation.prod BinaryLinearThree.W BinaryLinearThree.W) (q a) (e v).toAdd) :
    conjugationCubicLength A U = 2 := by
  let ρ : Representation (ZMod 2) A BinaryLinearThree.Vector := BinaryLinearThree.W.comp q
  let σ := Representation.prod ρ ρ
  let := conjMulDistribMulActionOfLeNormalizer A U hAU
  have hc := Representation.BinaryFixedPoints.cubicLength_eq_of_equivariant σ
    (MonoidHom.id A) Function.surjective_id e (by
      intro a v
      apply Multiplicative.toAdd.injective
      exact he a v)
  rw [Representation.BinaryFixedPoints.fixedIndex_prod,
    natural_cubic_fixedIndex hA q hq] at hc
  change FixedPoints.cubicLength A U = Nat.log 4 16 at hc
  exact (conjugationCubicLength_eq A U hAU).trans (hc.trans (by decide))

end BinaryLinearThree
