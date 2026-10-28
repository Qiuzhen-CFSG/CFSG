module
public import Theory.Representation.SmallBinaryFiveOvergroup
public import Theory.Representation.SmallBinaryCyclicResidual

/-!
# The residual order bound for a normal five on a binary four-space

The two-residual acts trivially on the normal subgroup of order five,
whose automorphism group has order four. Its containment in the five's
centralizer bounds its order by a divisor of fifteen. This supplies the
quintic support calculation in original 15.1.16; eliminating a possible
cubic factor requires additional ambient information.

Source: Aschbacher--Smith, printed pp.1087--1088 and 1092--1093.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace Representation.SmallBinaryFiveResidual
variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- The original residual centralizes the normal five, hence has order dividing fifteen. -/
theorem card_twoResidual_dvd_fifteen
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (h4 : Module.finrank (ZMod 2) W = 4)
    (P : Subgroup D) [P.Normal] (hP : Nat.card P = 5) :
    Nat.card (pResidual 2 D) ∣ 15 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : IsCyclic P := isCyclic_of_prime_card hP
  have hAut : IsPGroup 2 (MulAut P) := IsPGroup.of_card (n := 2) (by
    rw [IsCyclic.card_mulAut,hP]
    decide)
  have hle : pResidual 2 D ≤ centralizer (P : Set D) := by
    rw [← MulAut.conjNormal_ker_eq_centralizer P]
    exact pResidual_le_ker_of_isPGroup 2 (MulAut.conjNormal : D →* MulAut P) hAut
  exact (card_dvd_of_le hle).trans
    (SmallBinaryFiveOvergroup.centralizer_card_dvd ρ hf h4 P hP)

end Representation.SmallBinaryFiveResidual
