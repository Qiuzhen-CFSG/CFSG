module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.CommutatorOrders.WordAlgebra
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.Contracts

/-!
# Matrix operation boundaries for the commutator assembly

Specialize the monoid identities before supplying concrete packed matrices.
This reconciles matrix HMul with multiplication inherited from Monoid while
all operands are symbolic; otherwise conversion expands a 320-term sum.
The two Variant modules apply these identities to the literal ATLAS matrices.
Source: John Bray, ATLAS M24G1-P1.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixRelationCertificate.CommutatorOrders

theorem matrixWord12 (a b t u c : Mat)
    (ht : a*b=t) (hu : t*b=u) (hc : u*t=c) : a*b^2*a*b=c :=
  word12 a b t u c ht hu hc

theorem matrixWord5 (a b t u c uc d : Mat)
    (ht : a*b=t) (hu : t*b=u) (hc : u*t=c) (huc : u*c=uc) (hd : uc*t=d) :
    a*b^2*a*b^2*a*b*a*b=d :=
  word5 a b t u c uc d ht hu hc huc hd

theorem matrixTwelve (c c2 c3 c6 : Mat)
    (h2 : c*c=c2) (h3 : c2*c=c3) (h6 : c3*c3=c6) (h12 : c6*c6=1) : c^12=1 :=
  twelve c c2 c3 c6 h2 h3 h6 h12

theorem matrixFive (d d2 d4 : Mat)
    (h2 : d*d=d2) (h4 : d2*d2=d4) (h5 : d4*d=1) : d^5=1 :=
  five d d2 d4 h2 h4 h5

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixRelationCertificate.CommutatorOrders
