module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.Construction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.Actors
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.TorusTransfer
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.SourceAssembly

/-!
# Local Borel construction and source torus alternatives

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954/PDF p.971.

The construction uses the actual source Sylow, the normalizer inside K*,
and its preimage inside K. Residual transport connects the lift to the
intrinsic model calculation. The original t* acts by conjugation, with
C_T*(K*) retained as its kernel. An outer fixer with small commutator
quotient yields precisely the exceptional model isomorphisms in (b).
The auxiliary-centralizer argument supplies torus fixation without
assuming B_C≤B in the covered case.

The full-product source calculation now supplies torus fixation and the
small commutator quotient for the original marked t. `SourceAlternatives`
combines it with the inner branch and retains an actual inverter in
T* ∩ C_H*(K*), through a separately named strengthened dichotomy. Its
projection preserves `BorelAlternative` and its original public APIs.

`Normalization` proves that L₁T normalizes the constructed Borel in all
seven higher-field models, using the actual solvable Sylow overgroups and
the characteristic two-core of their component intersection.
`SourceAssembly` constructs the reduced component quotient equivalence,
derives L₁T-solvability from the natural action, places B in M by 13.8.13,
and supplies complete ordinary and covered source alternatives. Existing
conditional assemblies remain available with their original statements.
The literal source fixer equality also remains separate without the extra
kernel control identified in TorusModels. The sufficient dichotomy retains
the kernel and does not require that stronger equality.
-/
