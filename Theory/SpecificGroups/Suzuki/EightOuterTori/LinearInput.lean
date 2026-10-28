module

public import BenderSuzuki.MatrixGroups.Suzuki

/-!
# The linear field-twist input for the thirteen-torus of Sz(8)

The outstanding calculation says that a matrix of order thirteen in GL(4,8)
cannot be conjugate to a nontrivial defining-field twist. The formula records
the literal entrywise field map and left conjugation. It is a proof obligation,
not an axiom or an asserted automorphism calculation for the Suzuki group.

`EightOuterTori` uses this input to remove the field part of a pointwise
thirteen-torus fixer. Sylow conjugacy and counting then supply every torus
automorphism. The source consumer is Aschbacher–Smith, J.2.10, printed p.438
(PDF p.449), using GLS3, Theorems 2.5.12 and 6.5.4.
-/

namespace BenderSuzuki.MatrixGroups.EightOuterTori

open PFAppendixIII

/-- Separation of order-thirteen matrices from their nonidentity field twists. -/
@[expose] public def ThirteenTwistSeparation : Prop :=
  ∀ (x g : GL (Fin 4) (BinaryGaloisField 3))
    (σ : BinaryGaloisField 3 ≃ₐ[ZMod 2] BinaryGaloisField 3),
    orderOf x = 13 →
    g * Matrix.GeneralLinearGroup.map σ.toRingHom x * g⁻¹ = x → σ = 1

end BenderSuzuki.MatrixGroups.EightOuterTori
