module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.LocalCore

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Source

/-!
# Proper residual subgroup recognition

The actual proper residual subgroup is PSL₂(2^n), with n ≥ 2. The source
model alternatives, centralizer collapse and Suzuki coset counts discharge
all premises of the Suzuki exclusion. The original finite ambient group,
distinguished involutions and generated subgroup are preserved. Strong
embedding is used only inside that proper subgroup.

The independent Section 15 exclusion remains the next source input to
residual generation. Source: GLS IV, Chapter 2, Lemma 12.2 and Proposition 14.1.
-/
