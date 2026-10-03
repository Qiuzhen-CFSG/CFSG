module

public import Stellmacher.SectionNine.DistanceOneLocalEightNormalizers
public import Stellmacher.SectionNine.DistanceOneNormalizerFromEight


/-!
# The ambient normalizer witness from the distance-one local structure

The local elementary-eight construction supplies the same subgroup U with
both actual vertex normalizer quotients S4 and terminal self-centralization.
The existing ambient transfer theorem maps U through the injective graph-group
embedding, proves its ambient self-centralization, and embeds both local S4
quotients in the actual ambient normalizer quotient. Their images are distinct
because the two vertex stabilizers intersect in a two-group.

This short assembly proves the witness obligation in Stellmacher (9.1)(c),
Journal of Algebra190 (1997), p.48. Critical length one and the faithful and
local conclusions are explicit. The numbered theorem separately supplies
these local conclusions; `distance_one_conclusion_of_data` then recognizes
the ambient normalizer quotient as PSL3(2).
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven
universe u

public theorem distance_one_normalizer_input_of_local_structure
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hlength : ctx.criticalPath.length = 1)
    (hfaithful : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (hlocal : DistanceOneLocalConclusion ctx.toLocalContext) :
    DistanceOneNormalizerInput embedding ctx.toLocalContext := by
  obtain ⟨U,hUV,hElem,hUcard,hZU,hUE,hUa,hUd,hmodela,hmodeld,hself⟩ :=
    distance_one_local_eight_normalizers ctx hlength hfaithful hlocal
  exact distance_one_normalizer_input_of_eight ctx hlength hfaithful hlocal
    U hUV hElem hUcard hZU hUE hUa hUd hmodela hmodeld hself
end Stellmacher.SectionNine
