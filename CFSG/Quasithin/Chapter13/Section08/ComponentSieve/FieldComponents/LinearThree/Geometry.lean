module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.SourceGeneration
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.MarkedH65
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ExternalAssembly

/-!
# Source geometry for the binary linear-three branches

`source_H65_input` derives the marked H.6.5 input consumed by the 13.8.19
module argument. Its stronger companion constructs the Sylow-fixed cyclic
seed, both parabolics and the literal R₁* under one isomorphism. Only the
genuine earlier source actions and universal H.6.5 remain explicit.

`ordinary_source_geometry` combines the external-component reduction and
normal seed generation with 13.8.13, identifying the actual centralizer
quotient with Aut(L₃(2)). The underlying action dichotomy also retains the
constructed solvable L₁T-overgroups inside G₁. `covered_source_geometry`
derives the component identification from the same input list and constructs
the compatible L₃(2) × S₃ product, residuals, inverter, seed and critical marks.

These are conditional group-geometric reductions for Aschbacher–Smith
13.8.19 and 13.8.21(1), printed pp.953 and 956–957. The exact component list
13.8.21(2) is an input to the external branches. Representation exclusions
and final L₁ containment remain with their consumer; K* ≅ L₃(2) is retained.
-/
