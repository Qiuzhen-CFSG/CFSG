/-
The Golay and affine sextet constructions used here are by Gerald Höhn and
ATLAS contributors, under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt. Their source modules record revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
-/
module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.AtlasModel
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.HexacodeDual.Translations
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.HexacodeDual.Pairing
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.HexacodeDual.Irreducibility

/-!
# The sextet middle quotient as the dual hexacode module

The actual pair space and tetrad line are invariant under the affine sextet
stabilizer. Their literal quotient carries `atlasMiddleRepresentation`.
Actual translations displace the pair space into the tetrad line, and the
hexacode action agrees with conjugation on these same translations.

The binary dot pairing identifies this quotient equivariantly with the dual
hexacode. Its exact radical is the tetrad line, by Golay self-duality, and
extension of functionals proves surjectivity. The resulting representation
equivalence transfers the proved irreducibility of the affine dual action;
the checked hexacode dimension gives dimension six.

This is the concrete middle-factor calculation in Aschbacher–Smith H.15.3(1),
printed p.400/PDF p.411 of the combined manuscript of 1 March 2004. Native
coordinate transport and identification of the intrinsic two-core belong to
the source theorem's assembly.
-/

public section

open Atlas.Codes
open Representation
namespace MathieuCode.SextetLayers
noncomputable section

/-- The dot pairing is an equivalence of the actual middle quotient action with
the dual of the hexacode action induced by conjugation on translations. -/
def atlasMiddleDualRepresentationEquiv : atlasMiddleRepresentation.Equiv
    (Representation.dual (Representation.Hexacode.action.comp sextetQuotient)) :=
  .mk atlasMiddleDualEquiv fun s => LinearMap.ext (atlasMiddleDualEquiv_equivariant s)

/-- The representation equivalence has exactly the constructed pairing as its
underlying linear equivalence. -/
@[simp] lemma atlasMiddleDualRepresentationEquiv_toLinearEquiv :
    atlasMiddleDualRepresentationEquiv.toLinearEquiv = atlasMiddleDualEquiv := by
  rfl

/-- The literal pair-space quotient by the pullback tetrad line has dimension six. -/
theorem atlasMiddle_finrank : Module.finrank (ZMod 2) AtlasMiddle = 6 := by
  rw [atlasMiddleDualEquiv.finrank_eq, Subspace.dual_finrank_eq, hexacode_finrank]

/-- The actual affine sextet stabilizer acts irreducibly on the middle quotient. -/
theorem atlasMiddle_isIrreducible : IsIrreducible atlasMiddleRepresentation := by
  let f := IntertwiningMap.equivLinearMapAsModule _ _
    atlasMiddleDualRepresentationEquiv.toIntertwiningMap
  let e := LinearEquiv.ofBijective f
    (show Function.Bijective f from atlasMiddleDualRepresentationEquiv.toLinearEquiv.bijective)
  rw [irreducible_iff_isSimpleModule_asModule]
  exact e.isSimpleModule_iff.mpr
    ((irreducible_iff_isSimpleModule_asModule _).mp
      Representation.Hexacode.sextet_dual_isIrreducible)

end
end MathieuCode.SextetLayers
