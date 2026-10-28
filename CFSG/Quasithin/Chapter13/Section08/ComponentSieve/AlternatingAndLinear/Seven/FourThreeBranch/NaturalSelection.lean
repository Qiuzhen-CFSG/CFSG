module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.FourThreeBranch.NaturalSelection.Stabilizer
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.FourThreeBranch.NaturalSelection.Factors
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.FourThreeBranch.NaturalSelection.Quotient
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.FourThreeBranch.NaturalSelection.Structure
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.FourThreeBranch.NaturalSelection.Structure.ThetaImage
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.FourThreeBranch.NaturalSelection.Selection
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.FourThreeBranch.NaturalSelection.LocalData
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.FourThreeBranch.NaturalSelection.Assembly

/-!
# Natural selection in the four-plus-three branch

The actual stabilizer inverse image equals H ∩ M by 13.8.13 and the theta
identity: two overlapping cubic supports force the reverse containment.
Two disjoint cycles lift through O₂(H) to an elementary nine in L₁, giving
three-rank two and the covered-A₆ quotient from the earlier local alternatives.
The image of L₁ is exactly the cubic-generated subgroup of the partition
stabilizer, without assuming that the ambient image fills S₇.

On the representation side, the literal generating seed retains its rank,
invariance, centralization and commutator identity in the quotient by an
actual maximal proper subrepresentation. The genuine B.4 alternatives and
a three-cycle in L₀ select the equivariant natural quotient. `Selection`
discharges the cubic normal form using its independently proved theorem,
and constructs that cycle from the unordered residual marking. This treats
the actual dual constituent without assuming H-invariance of the summands.
The same quotient seed then orders the factors.

`Assembly` supplies `source_structure`, deriving surjectivity from the actor on the actual
cubic quotient and the unordered marking from the intrinsic two-perfect
factors. It invokes the earlier local residual calculation only after proving
the covered-A₆ alternative. Its `source_natural_quotient` then gives
the stabilizer equality, rank two, covered quotient, full S₇ image, natural
maximal quotient and ordered factors together. Naturality and surjectivity
are outputs for the original map, not premises. The earlier source statements
and universal B.4 implication remain explicit inputs to this selection step;
the later reciprocal-actor contradiction belongs to the final A₇ exclusion.

The old `fourThree_structure` helper retains its stronger conditional
interface for compatibility. The assembly uses the theta, cubic-parity and
residual-lift proofs instead of its factor-containment and concrete-cycle inputs.

Source: Aschbacher–Smith, 13.8.24, printed pp.958–959/PDF pp.975–976
(combined manuscript, 1 March 2004).
-/
