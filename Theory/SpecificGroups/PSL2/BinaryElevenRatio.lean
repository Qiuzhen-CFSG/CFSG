module
public import Theory.Representation.BinaryOffender.ElementaryConjugateBudget.FixedSpace
public import Theory.SpecificGroups.PSL2.ElevenConjugateBudget
public import Theory.SpecificGroups.SL2.OddOrderDivisibility
public import Theory.Representation.BinaryPrimeDegree
public import GorensteinWalter.PSL2Center
/-!
# The fixed-free faithful binary PSL₂(11) cubic exclusion

The checked elementary conjugate budget bounds degree by eight at cubic
ratio at most two. The element-order degree bound forces degree at least
ten. This applies to the original C.5.13 moved dual, without irreducibility.
Source: Aschbacher–Smith K.2 and C.5.13, printed pp.453 and163.
-/
public section
open Subgroup Representation Representation.BinaryOffender
namespace Theory.PSL2
open scoped MatrixGroups
theorem two_lt_cubicRatio_of_eleven_fixed {G V : Type*} [_root_.Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hfix : fixedSpace ρ ⊤ = ⊥) {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 11) (e : G ≃* PSL(2,F)) : 2 < cubicRatio ρ := by
  have hc : center G = ⊥ := by
    apply bot_unique
    intro z hz
    apply e.injective
    have hz' : e z ∈ center PSL(2,F) := MulEquivClass.apply_mem_center e hz
    rw [GorensteinWalter.psl2_center_eq_bot F,mem_bot] at hz'
    exact hz'.trans e.map_one.symm
  have hb := elementaryBudget_of_inner hc ((ElevenConjugateBudget.budget F hF).map e.symm)
  by_contra hn
  have hdim := finrank_le_of_fixed_cubic_budget (a := 2) ρ hfix hb (le_of_not_gt hn)
  have hcard := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice
    (show Odd (Nat.card F) from hF ▸ (by decide : Odd 11))
  rw [← Nat.card_congr e.toEquiv,hF] at hcard
  have hd : 11 ∣ Nat.card G := by
    have he : Nat.card G = 660 := by omega
    rw [he]
    decide
  have hlo := BinaryPrimeDegree.orderOf_le_finrank ρ hf
    (by decide : Nat.Prime 11) (by decide) hd
  rw [BinaryPrimeDegree.orderOf_two_mod_eleven] at hlo
  norm_num at hdim
  omega
end Theory.PSL2
