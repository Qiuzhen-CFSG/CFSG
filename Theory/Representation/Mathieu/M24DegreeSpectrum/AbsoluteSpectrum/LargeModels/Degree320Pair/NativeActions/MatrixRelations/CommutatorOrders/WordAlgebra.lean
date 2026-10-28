module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.CommutatorOrders.Arithmetic

/-!
# Algebraic assembly of the two positive commutator words

Writing T = AB and U = AB², the source words are C = UT and D = UCT.
Repeated squaring reduces their required powers to the twelve checked products
per variant used by the parent CommutatorOrders module.
Source: John Bray, ATLAS M24G1-P1.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixRelationCertificate.CommutatorOrders

theorem word12 {M : Type*} [Monoid M] (a b t u c : M)
    (ht : a*b=t) (hu : t*b=u) (hc : u*t=c) : a*b^2*a*b=c := by
  subst t; subst u; subst c
  simp only [pow_two, mul_assoc]

theorem word5 {M : Type*} [Monoid M] (a b t u c uc d : M)
    (ht : a*b=t) (hu : t*b=u) (hc : u*t=c) (huc : u*c=uc) (hd : uc*t=d) :
    a*b^2*a*b^2*a*b*a*b=d := by
  subst t; subst u; subst c; subst uc; subst d
  simp only [pow_two, mul_assoc]

theorem twelve {M : Type*} [Monoid M] (c c2 c3 c6 : M)
    (h2 : c*c=c2) (h3 : c2*c=c3) (h6 : c3*c3=c6) (h12 : c6*c6=1) : c^12=1 := by
  have e2 : c^2=c2 := by simpa only [pow_two] using h2
  have e3 : c^3=c3 := by rw [pow_succ, e2, h3]
  have e6 : c^6=c6 := calc
    c^6 = c^3*c^3 := by rw [← pow_add]
    _ = c6 := by rw [e3, h6]
  calc
    c^12 = c^6*c^6 := by rw [← pow_add]
    _ = 1 := by rw [e6, h12]

theorem five {M : Type*} [Monoid M] (d d2 d4 : M)
    (h2 : d*d=d2) (h4 : d2*d2=d4) (h5 : d4*d=1) : d^5=1 := by
  have e2 : d^2=d2 := by simpa only [pow_two] using h2
  have e4 : d^4=d4 := calc
    d^4 = d^2*d^2 := by rw [← pow_add]
    _ = d4 := by rw [e2, h4]
  rw [pow_succ, e4, h5]
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixRelationCertificate.CommutatorOrders
