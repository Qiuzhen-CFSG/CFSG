module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.Co3Kernel
public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover

/-!
# Applying the concrete Co₃ kernel to the canonical symplectic cover

The two-graph certificate discharges centrality for the exact homomorphism used
by the existing commutator witness. Its nontrivial central commutator therefore
proves that the canonical universal kernel is nontrivial. The independent upper
bound of two, and the final universal-double-cover assembly, remain separate.

Source motivation: GLS3 Table 5.3j and Aschbacher–Smith A.2.2(4), A.2.19.
-/

public section
namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover

/-- The canonical universal kernel is nontrivial, using the literal Co₃ quotient. -/
theorem kernel_nontrivial : Nontrivial projection.ker :=
  kernel_nontrivial_of_co3_kernel_central Co3Witness.matrixProjection_ker_le_center

end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover
