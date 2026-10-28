module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.Reduction
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements.Representatives
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements.CyclicCoverage
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements.VertexCertificates
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements.CycleCertificates

/-!
# Odd-element displacement in the large binary G₂ derived modules

The actual flag-module filtration transfers concrete displacement certificates
to every irreducible module above dimension eight. All five degree-14 vertex
blocks and both degree-32 cycle factors are retained. The finite certificates
are separated from cyclic conjugacy coverage in the literal derived group;
their assembly also gives the full-normalizer involution bounds under the
independent inversion-witness premise.

The checked cyclic conjugacy and matrix certificates discharge
`ConjugacyCoverage`, `VertexSamples` and `CycleSamples`. Thus the odd-element
bounds require only irreducibility, finite dimension and dimension above eight;
faithfulness is needed only by the full-normalizer consumer. Source:
Guralnick–Malle, Classification of 2F-modules I, Proposition 4.3, pp.10–11;
the degree-32 calculation is an additional branch required by this
individual-involution interface.
-/

public section

namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements
open Representation

/-- Every binary irreducible of the actual derived G₂ group above dimension
eight has displacement at least ten on regular three-elements and at least
twelve on seven-elements. Both degree-32 factors and all degree-14 vertex
quotients are covered by the literal flag-module transport. -/
theorem oddDisplacementBounds
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) Derived V) [IsIrreducible σ]
    (hd : 8 < Module.finrank (ZMod 2) V) : OddDisplacementBounds σ :=
  oddDisplacementBounds_of_certificates σ hd conjugacyCoverage vertexSamples cycleSamples

/-- The odd-displacement calculation discharges the representation-theoretic
premise of the full-normalizer reduction. Only the independent group-theoretic
inversion witnesses remain for the parent involution-bound assembly. -/
theorem involutionBounds_of_inversionWitnesses
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) Derived V) [IsIrreducible σ]
    (hf : Function.Injective σ) (hd : 8 < Module.finrank (ZMod 2) V)
    (w : InversionWitnesses) : InvolutionBounds σ :=
  involutionBounds_of_odd_displacement σ hf w (oddDisplacementBounds σ hd)

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements
