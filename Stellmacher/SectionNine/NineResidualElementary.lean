module

public import Stellmacher.SectionNine.NineResidualCanonicalDerived
public import Stellmacher.SectionOne.OneSevenDerivedElementary

/-!
# Elementary-three residual images from a canonical local factor

In a genuine Section Nine local action killing the two-core, the exact
Section One hypotheses and one canonical factor imply that the geometric
two-residual has elementary abelian image at three. The local residual
identification uses the adjacent-edge P-set data and unique maximality;
the global canonical product has elementary-three derived subgroup.

This is the elementary consequence of Stellmacher (9.10)(3), printed
p.57 of `refs/files/stellmacher-n-group.pdf`, also used with the residual
obstruction in (9.8). The conclusion retains the literal image under
the supplied surjective homomorphism, so quotient transport remains
explicit at the application site.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_local_residual_isElementaryAbelian_of_factor
    {G X V : Type u} [Group G] [Finite G] [Group X] [Finite X]
    [Group V] [Finite V] [IsElementaryAbelian 2 V] [MulDistribMulAction X V]
    {T A B : Subgroup G} (ctx : SectionNineLocalContext G T A B)
    (vertex neighbor : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent vertex neighbor)
    (action : GAt ctx.Γ vertex →* X)
    (hsurj : Function.Surjective action) (hkernel : pCore 2 (GAt ctx.Γ vertex) ≤ action.ker)
    (hyp : SectionOne.Hypotheses X V)
    (factor : Subgroup X) (hfactor : SectionOne.IsOneSevenFactor (V := V) factor) :
    IsElementaryAbelian 3
      (((EAt ctx.Γ vertex).subgroupOf (GAt ctx.Γ vertex)).map action) := by
  rw [nine_local_residual_eq_canonical_derived ctx vertex neighbor hadj
    action hsurj hkernel hyp factor hfactor]
  exact SectionOne.oneSeven_derived_isElementaryAbelian hyp

end Stellmacher.SectionNine
