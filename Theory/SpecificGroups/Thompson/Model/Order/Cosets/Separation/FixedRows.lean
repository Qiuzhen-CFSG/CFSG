module

public import Theory.SpecificGroups.Thompson.Model.Order.Cosets.Separation.FixedRows.FirstA
public import Theory.SpecificGroups.Thompson.Model.Order.Cosets.Separation.FixedRows.SecondA
public import Theory.SpecificGroups.Thompson.Model.Order.Cosets.Separation.FixedRows.FirstB
public import Theory.SpecificGroups.Thompson.Model.Order.Cosets.Separation.FixedRows.SecondB

/-!
# The local subgroup preserves three nonzero binary rows

The first exact subgroup word fixes both chosen basis rows. The second sends
the first row to their sum and the second to the first. Linearity gives the
identities for the third nonzero row. The constituent modules contain complete
kernel-checked arithmetic certificates; no orbit size is asserted here.
See `Separation/source/README.md` for the candidate data and their provenance.
-/

namespace Thompson.OrderCertificate.Separation

public theorem fixedRow2_localA :
    Matrix.vecMul fixedRow2 (matrixHom localA) = fixedRow2 := by
  simp only [fixedRow2, Matrix.add_vecMul, fixedRow0_localA, fixedRow1_localA]

public theorem fixedRow2_localB :
    Matrix.vecMul fixedRow2 (matrixHom localB) = fixedRow1 := by
  rw [fixedRow2, Matrix.add_vecMul, fixedRow0_localB, fixedRow1_localB, fixedRow2]
  rw [add_right_comm, ZModModule.add_self, zero_add]

end Thompson.OrderCertificate.Separation
