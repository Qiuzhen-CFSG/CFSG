module

public import Stellmacher.Recognition.Parrott.SylowInitialAction

/-!
# Covariance before selecting Parrott's core cosets

Write P for right conjugation by x, p = [a,d], q = [a,c], r = [b,c],
and k = c². In J/⟨z⟩, the image of E is central of exponent two.
The initial outer images are a ↦ a, b ↦ ba, c ↦ cab, d ↦ dabc.
Transporting [a,d], [a,c], [b,c], [d,b] and c² therefore gives
q = P(p)pt, r = P(p), P²(p) = pt, and P(k) = kvp modulo ⟨z⟩.

This module states those four identities as a contract; it does not assert
that they hold. They are distinct from the desired core-coset alternatives.
The covariance calculation and the elementary coefficient calculation can be
proved separately. The initial-action module supplies membership in E,
(cd)² ∈ ⟨z⟩, and commutation of d with p and k, without this contract.

For the coefficient calculation, write p and k in the supplied elementary
basis z,t,v,u,w. P²(p)/p = t fixes the u,w coefficients of p, and [d,p]=1
fixes its t coefficient. Write β for its remaining v coefficient.
The identities [c,k]=[d,k]=1 fix the v,t coefficients of k; P(k)/k=vp
then fixes its w,u coefficients as 1,1+β. The first two transport identities
give q and r. Thus the Boolean β correlates all five requested cosets.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed pp.678–679, equations (1)–(15). This is a quotient-algebra route to
those alternatives, retaining all supplied coordinates.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSylowInitialData

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- The four identities in J/⟨z⟩ obtained by transporting the initial
commutators and square under right conjugation by x. -/
public structure CoreCovariance (f : ParrottSylowInitialData n) : Prop where
  ac_transport : Tits.parrottCommutator f.a f.c /
    ((MulAut.conj f.x⁻¹) (Tits.parrottCommutator f.a f.d) *
      Tits.parrottCommutator f.a f.d * n.t) ∈ zpowers z
  bc_transport : Tits.parrottCommutator f.b f.c /
    (MulAut.conj f.x⁻¹) (Tits.parrottCommutator f.a f.d) ∈ zpowers z
  ad_iterate :
    (MulAut.conj f.x⁻¹) ((MulAut.conj f.x⁻¹) (Tits.parrottCommutator f.a f.d)) /
      (Tits.parrottCommutator f.a f.d * n.t) ∈ zpowers z
  square_transport : (MulAut.conj f.x⁻¹) (f.c ^ 2) /
    (f.c ^ 2 * n.v * Tits.parrottCommutator f.a f.d) ∈ zpowers z

end Stellmacher.Recognition.ParrottSylowInitialData
