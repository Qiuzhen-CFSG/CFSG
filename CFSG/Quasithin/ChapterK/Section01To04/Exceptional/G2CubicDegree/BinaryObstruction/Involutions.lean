module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Inputs
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Degrees
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.Reduction
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.GroupWitnesses
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements

/-!
# Assembly of the binary G₂ involution displacement calculations

The exact binary degree list leaves degrees 14 and 32 above degree eight.
For each branch the regular-three and seven-element displacement calculations
combine with inversion witnesses on the actual derived group. Conjugation on
the full linear normalizer preserves outer actors, and the commutator rank
inequality gives the individual bounds five and six consumed by the cubic
fixed-space obstruction.

The checked unitary witnesses and flag-factor calculations discharge both
inputs, yielding `involutionBounds` for every faithful binary irreducible
above degree eight, without an absolute-irreducibility hypothesis. The
conditional degree-case interface remains available separately. Source:
Guralnick--Malle, Classification of 2F-modules I, Proposition 4.3, pp.10--11;
the degree-32 calculation extends its individual-involution argument beyond
the source's prior offender-based degree exclusion.
-/

public section

namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction
open Representation Involutions

/-- Assembly retaining both large binary degrees and the literal outer
normalizer action. The concrete model premises must be supplied separately. -/
theorem involutionBounds_of_inversion_and_degree_cases
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) Derived V) [IsIrreducible σ]
    (hf : Function.Injective σ) (hd : 8 < Module.finrank (ZMod 2) V)
    (witnesses : InversionWitnesses)
    (h14 : Module.finrank (ZMod 2) V = 14 → OddDisplacementBounds σ)
    (h32 : Module.finrank (ZMod 2) V = 32 → OddDisplacementBounds σ) :
    InvolutionBounds σ :=
  involutionBounds_of_odd_displacement σ hf witnesses
    (oddDisplacementBounds_of_degree_cases σ hd h14 h32)

/-- Every faithful binary irreducible of the actual derived G₂ group above
degree eight has cyclic fixed codimension at least five for inner involutions
and at least six for outer involutions of its full linear normalizer.
The concrete inversion and odd-displacement premises are both discharged,
including the degree-32 branch. -/
theorem involutionBounds
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) Derived V) [IsIrreducible σ]
    (hf : Function.Injective σ) (hd : 8 < Module.finrank (ZMod 2) V) :
    InvolutionBounds σ :=
  involutionBounds_of_odd_displacement σ hf inversionWitnesses
    (OddElements.oddDisplacementBounds σ hd)

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction
