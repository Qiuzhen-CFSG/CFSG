module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.FiveOuterDisplacement.Inputs
public import Theory.SpecificGroups.SU3.FiveOuterSeven

/-!
# Inverted seven-elements for the PSU₃(5) displacement argument

The intrinsic matrix construction supplies an order-seven element inverted by
any outer involution of the actual projective special unitary model. The
odd-prime normalization transports this witness from the antidiagonal form,
retaining the stored Frobenius involution and the consumer's simplicity instance.

This discharges exactly the group input in the outer displacement argument.
Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
manuscript pp.10–11; Aschbacher–Smith K.2, printed p.453.
-/

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion

/-- The concrete inversion input, for every outer involution and every
nondegenerate Hermitian form over the field of order 25. -/
public theorem five_model_outer_seven_inversion : FiveModelOuterSevenInversion := by
  intro F _ _ J _ hcard hc a ha houter
  exact BenderSuzuki.MatrixGroups.HermitianForm.FiveOuterSeven.exists_inverted_seven_of_outer_involution
    J hcard hc a ha houter

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion
