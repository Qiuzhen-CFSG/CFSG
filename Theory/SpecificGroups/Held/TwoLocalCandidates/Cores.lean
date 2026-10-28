module

public import Theory.SpecificGroups.Held.TwoLocalCandidates
public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Structure

/-!
# Intrinsic two-core calculations for Held's three local candidates

`Cores.core` is a fixed word-defined subgroup of each literal ATLAS local
candidate. `Cores.core_normal` and `Cores.core_isPGroup` prove normality and
the two-group property intrinsically. The self-centralizer calculations
needed to finish the three witnesses remain separate obligations.

Source: GLS3 Table 5.3p; ATLAS HeG1-max3W1, HeG1-max4W1 and HeG1-max5W1.
-/
