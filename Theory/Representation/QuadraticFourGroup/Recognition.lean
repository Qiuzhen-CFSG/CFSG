module

public import Theory.Representation.QuadraticFourGroup.Models
public import Theory.Representation.QuadraticFourGroup.Recognition.Overgroup
public import Theory.Representation.QuadraticFourGroup.Recognition.ComponentSpectrum
public import Theory.Representation.QuadraticFourGroup.Recognition.CentralCover

/-!
# Group recognition for a component moved by a quadratic four-group

The intended conclusion of GLS, volume 2, Theorem 25.14 is a `TwoFactorModel`
of the actual `componentOrbit L B`, from `Hypotheses ρ L B a` for a faithful
finite-dimensional binary representation of a finite group.

The proved reductions here restrict to the generated overgroup without changing
the quotient, pass odd transpositions to the actual component modulo its center,
and derive the full involution centralizers required for recognition. The
perfect-central-cover lemmas eliminate odd kernels once cyclicity of the odd
Sylow subgroups of the concrete simple factor is established.

The faithful irreducible-image reduction, the odd-transposition theorem,
Burnside recognition and the concrete odd-Sylow input remain separate proof
obligations. No unconditional `TwoFactorModel` construction is asserted by
these conditional reductions. The group-only assembly does not use the tensor
classification.
-/
