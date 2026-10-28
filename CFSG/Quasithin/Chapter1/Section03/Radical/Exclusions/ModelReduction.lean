module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.Inputs
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.Quotients
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.Factors
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.Normalization
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.SmallQuotients
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.SieveContract

/-!
# Preparation for the pushing-up model reduction in 1.3.8

The imported modules construct embedding candidates from an outside overgroup,
compare K/O₂(K) with the actual star quotient in C.2.7, compute the order
of P ∩ K, and prove normalization by R in both surviving alternatives.
The small-quotient argument excludes the A₅-block and L₂(7) cases through
the actual solvable local image. The component input retains relative
normality, the C.2.3 setup and the global He bridge.
`PushingUpComponent.binaryBlockEmbedding` completes these last two exclusions
from the explicitly intermediate model-comparison conclusion.

The reduction to `BinaryBlockEmbedding` still needs the initial outside
overgroup and component, and the comparison with the complete C.2.7 list,
including exclusion of the linear-three alternative. No final reduction
theorem is asserted here yet.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Proposition 1.3.8, printed pp.513–514.
-/
