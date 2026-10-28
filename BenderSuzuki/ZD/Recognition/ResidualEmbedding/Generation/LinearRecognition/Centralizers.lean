module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Contracts
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Source

/-!
# Centralizers of involutions in the proper residual case

`Foundations` proves Lemma 12.4(a), the required proper local embedding,
the identification of involutions in the distinguished centralizer closure,
and the fixed distinguished trace. `Contracts` separates the remaining
local recognition, shearing/counting, and unitary exclusion arguments.

`Source` proves Proposition 13.1 and the Suzuki numerical specialization
of Lemma 12.10. It constructs the local data from the original hypotheses,
uses the proved counting alternatives, and excludes the unitary case.
Both conclusions retain the original residual subgroup and coset action.

Source: `refs/KGroup/GLS4/Chapter2.tex`, Sections 12–13.
-/
