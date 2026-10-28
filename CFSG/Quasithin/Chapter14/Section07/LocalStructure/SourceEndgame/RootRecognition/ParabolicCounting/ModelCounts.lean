module
public import Theory.Representation.PSL3Two.SteinbergStructure.ParabolicFactors.CubicFixed
public import Theory.SpecificGroups.SL2.CubicFixedVectors
public import Theory.Representation.SL2FourNaturalOrbits.SelfDual

/-!
# Cubic fixed counts in the two marked models

Sylow conjugacy carries the coordinate three-cycle calculation to every
order-three subgroup of SL₃(2). Together with the existing Steinberg
calculation this gives fixed orders two and four. A cubic in SL₂(4) has
no nonzero natural fixed vector. The source application transports all
three facts through the original qL and qK coordinate maps.

Source: Aschbacher–Smith H.6.3(3), used in 14.7.73, printed p.1077.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.ParabolicCounting

private theorem natural_cycle_test : ∀ v : BinaryLinearThree.Vector,
    BinaryLinearThree.W BinaryLinearThree.IrreducibleCatalogue.cycle v = v ↔
      (fun _ => v 0) = v := by decide

private def naturalCycleFixedEquiv :
    fixedSpace BinaryLinearThree.W (zpowers BinaryLinearThree.IrreducibleCatalogue.cycle) ≃ ZMod 2 where
  toFun v := v.val 0
  invFun x := ⟨fun _ => x, by
    rw [mem_fixedSpace_zpowers_iff]
    exact (natural_cycle_test _).mpr rfl⟩
  left_inv v := Subtype.ext ((natural_cycle_test v.val).mp
    ((mem_fixedSpace_zpowers_iff _ _ _).mp v.property))
  right_inv _ := rfl

theorem natural_three_cubic_fixed_card (X : Subgroup BinaryLinearThree.Group)
    (hX : Nat.card X = 3) : Nat.card (fixedSpace BinaryLinearThree.W X) = 2 := by
  let c := BinaryLinearThree.IrreducibleCatalogue.cycle
  have hc : Nat.card (zpowers c) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by decide : c ^ 3 = 1) (by decide : c ≠ 1)
  let syl (J : Subgroup BinaryLinearThree.Group) (hJ : Nat.card J = 3) :
      Sylow 3 BinaryLinearThree.Group :=
    (IsPGroup.of_card (n := 1) (by simpa using hJ)).toSylow (by
      have hi := J.card_mul_index
      rw [hJ, Matrix.PSL3Two.card_SL] at hi
      have hind : J.index = 56 := by omega
      rw [hind]
      decide)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq BinaryLinearThree.Group (syl (zpowers c) hc) (syl X hX)
  have he : (zpowers c).map (MulAut.conj g).toMonoidHom = X :=
    congrArg (fun T : Sylow 3 BinaryLinearThree.Group => (T : Subgroup BinaryLinearThree.Group)) hg
  rw [← he, ← Nat.card_congr (fixedSpaceConjEquiv BinaryLinearThree.W (zpowers c) g).toEquiv]
  exact (Nat.card_congr naturalCycleFixedEquiv).trans (by simp)

theorem natural_four_cubic_fixed (X : Subgroup SL2FourNatural.SL) (hX : Nat.card X = 3) :
    fixedSpace SL2FourNatural.naturalRepresentation X = ⊥ := by
  obtain ⟨g, hg⟩ := X.isCyclic_iff_exists_zpowers_eq_top.mp (isCyclic_of_prime_card hX)
  have ho : orderOf g = 3 := by rw [← Nat.card_zpowers, hg]; exact hX
  apply bot_unique
  intro v hv
  exact Matrix.SL2.cubic_fixed_eq_zero g ho v (hv ⟨g, hg ▸ mem_zpowers g⟩)

theorem steinberg_cubic_fixed_card (X : Subgroup BinaryLinearThree.Group) (hX : Nat.card X = 3) :
    Nat.card (fixedSpace BinaryLinearThree.S X) = 4 := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    BinaryLinearThree.SteinbergStructure.ParabolicFactors.finrank_fixedSpace_order_three X hX]
  norm_num

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.ParabolicCounting
