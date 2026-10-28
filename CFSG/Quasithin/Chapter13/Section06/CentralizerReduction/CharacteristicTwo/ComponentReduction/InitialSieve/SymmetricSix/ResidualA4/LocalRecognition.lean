module

public import Theory.SpecificGroups.SymmetricSix.CubicCentralizers
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.SymmetricSix.ResidualA4.ModelFacts

/-!
# The intrinsic local recognition input for the S₆ branch

The image of the actual residual in the component normalizer quotient lies
in A₆, is two-perfect, has order divisible by six, and is centralized by the
marked involution. The intrinsic permutation theorem now discharges precisely
`SixLocalRecognition`, as consumed by `residual_isA4_of_model_facts`.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927. Central-cover
rigidity and the final source assembly remain with the parent module.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.SymmetricSix

/-- Recognition inside the literal S₆ embedding, with all intrinsic model
premises discharged. -/
theorem sixLocalRecognition : SixLocalRecognition :=
  Theory.SpecificGroups.SymmetricSix.CubicCentralizers.equiv_alternatingFour

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.SymmetricSix
