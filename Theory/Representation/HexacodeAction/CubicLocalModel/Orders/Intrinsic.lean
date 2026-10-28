module

public import Theory.Representation.HexacodeAction.CubicLocalModel
public import Theory.PGroupCore

/-!
# Intrinsic and embedded point commutator residuals

A Sylow subgroup contained in a point stabilizer is Sylow in that stabilizer.
Functoriality of finite two-residuals and commutators identifies its intrinsic
commutator residual with the subgroup embedded in the hexacode cover. The
subtype map is injective, so this identification preserves the quotient by
the intrinsic two-core. No ambient normality of the point stabilizer is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1, printed p.877. This is the change of ambient group needed
for the order of L₁,₊/O₂(L₁,₊).
-/

@[expose] public section
noncomputable section
open Subgroup
namespace Representation.Hexacode.CubicLocalModel.Orders

/-- The intrinsic two-residual of the commutator of O²(X) with a Sylow two-subgroup. -/
def intrinsicCommutatorResidual {X : Type*} [Group X] (P : Sylow 2 X) : Subgroup X :=
  (pResidual 2 (⁅pResidual 2 X, (P : Subgroup X)⁆ : Subgroup X)).map
    (⁅pResidual 2 X, (P : Subgroup X)⁆).subtype

/-- The actual subtype map takes the intrinsic residual to the embedded model residual. -/
theorem intrinsicCommutatorResidual_map (W : Submodule (ZMod 2) Natural)
    (P : Sylow 2 H) (hP : (P : Subgroup H) ≤ stabilizer W) :
    (intrinsicCommutatorResidual (P.subtype hP)).map (stabilizer W).subtype =
      commutatorResidual W P := by
  rw [intrinsicCommutatorResidual, map_embedded_pResidual, map_commutator,
    Sylow.coe_subtype, map_subgroupOf_eq_of_le hP]
  rfl

/-- The residual identification is an actual multiplicative equivalence. -/
def intrinsicCommutatorResidualEquiv (W : Submodule (ZMod 2) Natural)
    (P : Sylow 2 H) (hP : (P : Subgroup H) ≤ stabilizer W) :
    intrinsicCommutatorResidual (P.subtype hP) ≃* commutatorResidual W P :=
  ((intrinsicCommutatorResidual (P.subtype hP)).equivMapOfInjective
    (stabilizer W).subtype (stabilizer W).subtype_injective).trans
    (MulEquiv.subgroupCongr (intrinsicCommutatorResidual_map W P hP))

/-- The numerical target can be calculated entirely inside the point stabilizer. -/
theorem commutatorResidual_quotient_card_eq_intrinsic (W : Submodule (ZMod 2) Natural)
    (P : Sylow 2 H) (hP : (P : Subgroup H) ≤ stabilizer W) :
    Nat.card (commutatorResidual W P ⧸ pCore 2 (commutatorResidual W P)) =
      Nat.card (intrinsicCommutatorResidual (P.subtype hP) ⧸
        pCore 2 (intrinsicCommutatorResidual (P.subtype hP))) := by
  let e := intrinsicCommutatorResidualEquiv W P hP
  exact (Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv).symm

end Representation.Hexacode.CubicLocalModel.Orders
