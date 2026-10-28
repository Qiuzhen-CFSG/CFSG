module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Basic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.Residual
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.Quotient
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.HexacodeSection

/-!+# Central-cover reduction: residual, quotient and marked seed

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 13.8.21(2), printed p.956 (PDF p.973).

`Residual` proves that the literal Y = O²(O₂,Z(K)) is nontrivial,
solvable and two-perfect, maps onto the cubic center, and lies in L₁
using the universal earlier 13.8.13 conclusion and the literal theta
identity. Once Y ≠ L₁ is established, the earlier local subgroup
catalogue and Basic's normalizer argument identify Y with L₁,+.

`Quotient` proves generation on the actual U_H/V₁ from its seed identity,
and proves that the irreducible rank-two seed survives every proper
invariant quotient. `HexacodeSection` specifies the actual recognition
target and derives the marked F₄-point from it, the maximal parabolic
and cubic-scalar placement. Its action and projection are explicit.

This is not yet the full reduction. The actual K₁ construction, exclusion
of Y = L₁ through the uniqueness and Dynkin-action alternatives, and the
replacement of M̂₂₂ preserving the local setup are still required. So is
construction of `HexacodeSection` from the precise B.4.5, B.4.2(8) and
F.9.18(6) inputs. Final assembly of this conditional source reduction
stays in this module until these two independent obligations are proved.
The terminal contradiction belongs to the separate terminal source owner.
-/
