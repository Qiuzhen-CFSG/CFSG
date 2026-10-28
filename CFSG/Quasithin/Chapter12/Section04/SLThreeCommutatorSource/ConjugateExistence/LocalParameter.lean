module

public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.LocalParameterModels
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.LocalParameterSplitting

/-!
# Checked local parameter branches for the original 12.4.1

The literal omega spans under H and O²(H) agree. The whole span is reduced,
its Sylow centralizer is O₂(H), and its actual H-automizer is two-core-free.
The solvable and one-or-two A₅ branches now reach the requested conjugator.
The fixed-layer transport retains the full H-action on the whole module.

The original LocalParameterSource API remains available and unchanged.
The new application uses the source's sufficient C_T(V_H) bound instead
of assuming that the entire C_H(V_H) is a two-group. The source
classification producing the alternatives is still open. LocalClassification1232
records this remaining obligation, including K/O₂(K) and maximal faithfulness;
noncommutingConjugate1241_of_classification discharges its parameter consequence.
The existing SelectionSource.localSelectionSource supplies the independent
selection argument to noncommutingConjugate1241_of_nonsolvable_parameters.
-/
