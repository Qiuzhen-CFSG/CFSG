module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.Reduction
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.GroupWitnesses.UnitaryTransport

/-!
# Inversion witnesses for the actual derived binary G₂ group

Explicit matrices in SU₃(3), inner involution fusion, and outer involution
normalization supply both group-only witnesses. The actual special/projective
and projective/binary-G₂ equivalences preserve the element orders and the
centralizer in the derived group. Thus neither witness requires a representation
or a displacement assumption.

Applying the odd-element reduction gives the involution bounds on the literal
full linear normalizer. The independent odd-displacement calculation remains
an explicit premise, to be discharged by its own producer.

Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
manuscript pp.10–11, https://agag-malle.math.rptu.de/~malle/download/failfact.dvi.
-/

public section
open Representation
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.Involutions

/-- Both inversion clauses hold unconditionally on the actual commutator group. -/
theorem inversionWitnesses : InversionWitnesses :=
  ⟨GroupWitnesses.inner_witness, GroupWitnesses.outer_witness⟩

/-- Apply the group witnesses to the original full-linear-normalizer consumer.
The independent odd-element displacement calculation remains explicit. -/
theorem involutionBounds_of_oddDisplacementBounds
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) Derived V) [IsIrreducible σ]
    (hf : Function.Injective σ) (bounds : OddDisplacementBounds σ) :
    InvolutionBounds σ :=
  involutionBounds_of_odd_displacement σ hf inversionWitnesses bounds

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.Involutions
