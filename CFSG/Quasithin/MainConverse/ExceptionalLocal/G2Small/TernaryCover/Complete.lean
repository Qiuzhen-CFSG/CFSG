module

public import CFSG.Quasithin.MainConverse.ExceptionalLocal.G2Small.TernaryCover.ThreeFamily
public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.CharacterGeometry.InvolutionConjugacy
public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.CharacterGeometry.CanonicalEight
public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.CharacterGeometry.EightConjugacy

/-!
# Complete maximal-two-local cover for G₂(3)

Every maximal two-local of the actual ternary octonion automorphism group lies
in a conjugate of one of the three members of `CayleyEight.localFamily`: the
torus involution normalizer and the normalizers of the two reference eights.

The characteristic-center reduction expresses a maximal two-local as the
normalizer of a nontrivial elementary two-subgroup. The octonion character
decomposition restricts its order to two, four or eight. Involution conjugacy
handles order two; the canonical norm-line construction enlarges every
four-group to an eight while retaining its whole normalizer; the two-orbit
classification handles every eight. Thus all geometric premises of the
existing conditional cover are discharged.

This is the local coverage input for the G₂(3) converse in Aschbacher–Smith,
*The Classification of Quasithin Groups*, Volume I Theorem 0.1.2(4), printed
pp.3–4, and Volume II Theorem 0.1.1(4), pp.481–482. The recognition
configuration in §I.4, p.417, is not used to infer coverage. The octonion model
and reference embeddings use the licensed ATLAS port; see LICENSES/ATLAS.txt
and LICENSES/ATLAS-CITATION.cff.
-/

namespace CFSG.Quasithin.MainConverse.ExceptionalLocal.TernaryCover

open Atlas.G2 Atlas.G2.TernaryLocals

/-- Every maximal two-local of the actual G₂(3) model is contained in a
conjugate of a member of the complete three-member local family. -/
public theorem maximalTwoLocal_threeFamily_cover (M : Subgroup (Model (ZMod 3)))
    (hM : IsMaximalTwoLocal M) :
    ∃ (i : Fin 3) (g : Model (ZMod 3)),
      M ≤ (CayleyEight.localFamily i).map (MulAut.conj g).toMonoidHom := by
  refine maximalTwoLocal_threeFamily_cover_of_conjugacy_and_extension
    CharacterGeometry.InvolutionConjugacy.elementary_card_two_conjugate
    CharacterGeometry.CanonicalEight.exists_elementary_eight_extension ?_ hM
  intro E hE hcard
  let _ := hE
  exact CharacterGeometry.EightConjugacy.elementary_eight_conjugacy E hcard

end CFSG.Quasithin.MainConverse.ExceptionalLocal.TernaryCover
