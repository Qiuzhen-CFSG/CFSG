module

public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel

/-!
# Lift a p-group action image through the Frattini quotient

Let B be a finite p-group and let a group P act on B by automorphisms.
If its induced action on B/Φ(B) has p-group image, then its action on B
also has p-group image. No finiteness hypothesis on P is required.

Burnside's basis-kernel theorem says that the kernel of the full
automorphism action on B/Φ(B) is a p-group. The preimage of the supplied
Frattini action image is therefore a p-group, and it contains the original
action image. The statement keeps the supplied action literally unchanged.

This is the standard Frattini action transfer used in the wreath-product
exclusion in Stellmacher's N-group paper, Section 10, after controlling the
action on the elementary abelian Frattini quotient.
-/

namespace MonoidHom

public theorem isPGroup_range_of_frattini_range
    {P B : Type*} [Group P] [Group B] [Finite B] {p : ℕ}
    (hB : IsPGroup p B) (action : P →* MulAut B)
    (himage : IsPGroup p
      ((Subgroup.quotientAut (frattini B)).comp action).range) :
    IsPGroup p action.range := by
  have hpreimage := himage.comap_of_ker_isPGroup
    (Subgroup.quotientAut (frattini B))
    (Subgroup.isPGroup_quotientAut_frattini_kernel hB)
  apply hpreimage.to_le
  rintro image ⟨actor, rfl⟩
  exact ⟨actor, rfl⟩

end MonoidHom
