module

public import CFSG.KnownSimple.SporadicCarriers
public import Theory.SpecificGroups.Held.Automorphisms.InvolutoryB2

/-!
# Remaining sporadic inputs to the known-simple B₂ theorem

The Held local calculation covers both inner classes and every outer
involution implemented by the full permutation normalizer. Its remaining
realization premise is explicit below. The conclusion uses the catalogue's
exact carrier and group instance.

The seven other carriers and discharge of Held realization remain source
obligations. This module does not assert completion of the eight-carrier
branch or of the full known-simple catalogue.

Sources: GLS II, Definition 2.4 and Lemma 5.28; GLS3, Table 5.3p.
-/

public section
open Theory.GroupTheory

namespace CFSG.Quasithin.ChapterI.Section03.KnownSimpleB2.RemainingSporadic

/-- The catalogue Held case, conditional only on actual automorphism realization. -/
theorem held_of_normalizer_surjective
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom) :
    HasInvolutoryB2 KnownSimple.SporadicName.he.Carrier :=
  Held.InvolutoryB2.hasInvolutoryB2_of_normalizer_surjective hreal

end CFSG.Quasithin.ChapterI.Section03.KnownSimpleB2.RemainingSporadic
