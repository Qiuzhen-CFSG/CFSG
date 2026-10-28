module

public import Theory.Representation.HexacodeAction.CubicLocalModel.Orders.CentralCubicSymmetricFour.KleinReduction
public import Theory.Representation.HexacodeAction.CubicLocalModel.Orders.CentralCubicSymmetricFour.ResidualTransport
public import Theory.Representation.HexacodeAction.CubicLocalModel.Orders.CentralCubicSymmetricFour.SymmetricThree

/-!
# The cubic residual quotient in a central cubic extension of S₄

Lift the normal Klein four of S₄ through the central cubic kernel and
quotient by that normal two-subgroup. The resulting central cubic extension
of S₃ has commutator residual of order three. Surjective transport preserves
the intrinsic commutator residual and its quotient by its intrinsic two-core,
so the original residual quotient also has order three.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1 and Lemma 13.2.2(3), printed pp.876–877. This finite-group
lemma supplies the numerical calculation for the covered point stabilizer;
its application to arbitrary natural-module lines is separate.
-/

public section

namespace Representation.Hexacode.CubicLocalModel.Orders

/-- The intrinsic point commutator residual has cubic quotient by its two-core
in a central cubic extension of S₄ with no elements of order nine. -/
theorem intrinsicCommutatorResidual_quotient_card_of_central_cubic_s4
    {X : Type*} [Group X] [Finite X] (f : X →* Equiv.Perm (Fin 4))
    (hf : Function.Surjective f) (hk : Nat.card f.ker = 3)
    (hc : f.ker ≤ Subgroup.center X) (h9 : ∀ x : X, x ^ 9 = 1 → x ^ 3 = 1)
    (P : Sylow 2 X) :
    Nat.card (intrinsicCommutatorResidual P ⧸ pCore 2 (intrinsicCommutatorResidual P)) = 3 := by
  obtain ⟨Q, hQn, hQp, _, g, hg, hgk, hgc, _⟩ :=
    CentralCubicSymmetricFour.exists_central_cubic_s3_quotient f hf hk hc h9
  let := hQn
  have hqk : IsPGroup 2 (QuotientGroup.mk' Q).ker := by
    rwa [QuotientGroup.ker_mk']
  rw [intrinsicCommutatorResidual_quotient_card_of_two_kernel (QuotientGroup.mk' Q)
    (QuotientGroup.mk'_surjective Q) hqk P]
  exact CentralCubicSymmetricFour.intrinsicCommutatorResidual_quotient_card_of_central_cubic_s3
    g hg hgk hgc (P.mapSurjective (QuotientGroup.mk'_surjective Q))

end Representation.Hexacode.CubicLocalModel.Orders
