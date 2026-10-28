module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.Certificates
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.Data
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.RankOne
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.FourteenCertificate.Relations
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.FourteenCertificate.Polynomial
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.FourteenCertificate.Orbits
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.FourteenCertificate.Trace

/-!
# The complete degree-fourteen Hall--Janko matrix certificate

The literal ATLAS generators satisfy all five presentation relations over every
characteristic-two field containing a root t of t²=t+1. The supplied polynomial
in a linear combination of generator words gives v times lam; its two orbit
bases and their one-sided inverses force the generated algebra to be the full
matrix algebra. The supplied positive word has trace t+1.

All numerical products are proved by kernel-checked finite arithmetic, then
transported to the arbitrary field. The certificate needs no presentation
injectivity. The final application uses that separate group-theoretic hypothesis
to produce two inequivalent irreducible actions of the literal J₂ carrier.
Source: ATLAS J2G1-f4r14aB0, J2G1-P2 and the retained witnesses in source/.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels
open Arithmetic
universe v

/-- The full numerical certificate, uniformly in the coefficient field and universe. -/
theorem fourteen_parameterCertificate :
    ParameterCertificate.{v} FourteenData.A FourteenData.B
      FourteenData.traceWord FourteenData.traceCode := by
  intro F _ _ t ht
  refine ⟨FourteenCertificate.relations t ht, ?_, FourteenCertificate.trace_eq t ht⟩
  exact density_of_rankOne (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
    (evalVector t FourteenData.v) (evalVector t FourteenData.lam)
    (evalMatrix t FourteenData.P) (evalMatrix t FourteenData.Pi)
    (evalMatrix t FourteenData.Q) (evalMatrix t FourteenData.Qi)
    FourteenData.leftWords FourteenData.rightWords
    (FourteenCertificate.rankOne_mem t ht) (FourteenCertificate.left_orbits t ht)
    (FourteenCertificate.right_orbits t ht) (FourteenCertificate.left_inverse t ht)
    (FourteenCertificate.right_inverse t ht)

/-- Application to the original carrier: the numerical density and trace premises
of `exists_pair_of_certificate` are now discharged in degree fourteen. -/
theorem fourteen_exists_pair
    (hp : Function.Injective
      Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.Presentation.toCarrier)
    (F : Type v) [Field F] [IsAlgClosed F] [CharP F 2] :
    ∃ ρ σ : Representation F Sporadic.LeechRelated.J2.Carrier (Fin 14 → F),
      IsIrreducible ρ ∧ IsIrreducible σ ∧ IsEmpty (ρ.Equiv σ) :=
  exists_pair_of_certificate hp FourteenData.A FourteenData.B
    FourteenData.traceWord FourteenData.traceCode FourteenData.traceCode_nonbinary
    fourteen_parameterCertificate F

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels
