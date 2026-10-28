module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.CoordinateTransport.Coordinates
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.CoordinateTransport.Actions
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.CoordinateTransport.Markings

/-!
# Coordinate transport for the native sextet cocode layers

Every native sextet has concrete code-preserving coordinates obtained from
native four-transitivity and tetrad recovery. The point and part bijections,
Golay and even-core identifications, stabilizer equivalence, and cocode
equivalence below use that same marking. Coordinate sums identify the literal
pair span, and whole columns identify the tetrad line. The actual part action
is surjective with kernel of order 192. Affine translations form a normal
subgroup of order 64 whose conjugation action is the hexacode action through
the transported affine quotient. No intrinsic prime-core identification is
asserted here.

Source: Aschbacher–Smith H.15.3(1), printed p.400. See the descendant modules
and LICENSES/ATLAS.txt for the licensed ATLAS code and affine model attribution.
-/

@[expose] public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
namespace MathieuCode.SextetLayers.CoordinateTransport
noncomputable section

def nativePointEquiv (S : Sextet) : Atlas.Codes.Omega ≃ Fin 24 :=
  (nativeMarking S).pointEquiv

def nativePartEquiv (S : Sextet) : Atlas.Codes.HexIndex ≃ SextetPart S :=
  (nativeMarking S).partEquiv

lemma nativePointEquiv_mem_part (S : Sextet) (p : Atlas.Codes.Omega) (i : Atlas.Codes.HexIndex) :
    nativePointEquiv S p ∈ (nativePartEquiv S i).val ↔ p.1 = i :=
  (nativeMarking S).mem_part p i

lemma nativePointEquiv_tetrad (S : Sextet) (i : Atlas.Codes.HexIndex) :
    (Atlas.Codes.tetrad i).image (nativePointEquiv S) = (nativePartEquiv S i).val :=
  ((nativeMarking S).part_eq_image i).symm

def nativeWordEquiv (S : Sextet) : Atlas.Codes.BinaryWord ≃ₗ[ZMod 2] Full :=
  (nativeMarking S).wordEquiv

lemma nativeWordEquiv_apply (S : Sextet) (w : Atlas.Codes.BinaryWord) (i : Fin 24) :
    nativeWordEquiv S w i = w ((nativePointEquiv S).symm i) := rfl

lemma nativeWordEquiv_golay (S : Sextet) :
    Atlas.Codes.golay.map (nativeWordEquiv S).toLinearMap = golay :=
  (nativeMarking S).golay_map

lemma nativeWordEquiv_core (S : Sextet) :
    AtlasCore.map (nativeWordEquiv S).toLinearMap = Core :=
  (nativeMarking S).core_map

def nativeCoreEquiv (S : Sextet) : AtlasCore ≃ₗ[ZMod 2] Core :=
  (nativeMarking S).coreEquiv

def nativeCocodeEquiv (S : Sextet) : AtlasCocode ≃ₗ[ZMod 2] Cocode :=
  (nativeMarking S).cocodeEquiv

lemma nativeCoreEquiv_val (S : Sextet) (w : AtlasCore) :
    (nativeCoreEquiv S w).val = nativeWordEquiv S w.val := rfl

lemma nativeCocodeEquiv_mk (S : Sextet) (w : AtlasCore) :
    nativeCocodeEquiv S (atlasCodeInCore.mkQ w) = codeInCore.mkQ (nativeCoreEquiv S w) := rfl

lemma nativeCocodeEquiv_equivariant (S : Sextet) (s : Atlas.Codes.SextetStabilizer)
    (v : AtlasCocode) :
    nativeCocodeEquiv S (atlasCocodeRepresentation s v) =
      cocodeRepresentation (nativeStabilizerEquiv S s).val (nativeCocodeEquiv S v) :=
  cocode_equivariant (nativeMarking S) (nativeStabilizerEquiv S)
    (nativeStabilizer_coordinates S) s v

lemma nativeCocodeEquiv_tetrad (S : Sextet) (i : Atlas.Codes.HexIndex) :
    nativeCocodeEquiv S (atlasCodeInCore.mkQ (atlasTetradCore i)) = sextetVector S :=
  (nativeMarking S).cocodeEquiv_tetrad i

lemma nativeTetradLine_map (S : Sextet) :
    atlasTetradLine.map (nativeCocodeEquiv S).toLinearMap = sextetTetradLine S :=
  (nativeMarking S).tetradLine_map

lemma nativePairSpace_map (S : Sextet) :
    atlasPairSpace.map (nativeCocodeEquiv S).toLinearMap =
      ⨆ B ∈ S.parts, supportedPairSpace B :=
  (nativeMarking S).pairSpace_map

lemma nativePartPerm_apply (S : Sextet) (s : Atlas.Codes.SextetStabilizer)
    (i : Atlas.Codes.HexIndex) :
    sextetPartPerm S (nativeStabilizerEquiv S s) (nativePartEquiv S i) =
      nativePartEquiv S (Atlas.Codes.hexCoordinateHom (Atlas.Codes.sextetQuotient s) i) :=
  partPerm_apply (nativeMarking S) (nativeStabilizerEquiv S) (nativeStabilizer_coordinates S) s i

lemma nativePartPerm_surjective (S : Sextet) : Function.Surjective (sextetPartPerm S) :=
  partPerm_surjective (nativeMarking S) (nativeStabilizerEquiv S) (nativeStabilizer_coordinates S)

lemma nativePartPerm_kernel (S : Sextet) : (sextetPartPerm S).ker =
    Atlas.Codes.sextetCoordinateHom.ker.map (nativeStabilizerEquiv S).toMonoidHom :=
  partPerm_kernel_map (nativeMarking S) (nativeStabilizerEquiv S) (nativeStabilizer_coordinates S)

lemma nativePartPerm_kernel_card (S : Sextet) : Nat.card (sextetPartPerm S).ker = 192 :=
  partPerm_kernel_card (nativeMarking S) (nativeStabilizerEquiv S) (nativeStabilizer_coordinates S)

def nativeTranslation (S : Sextet) :
    Multiplicative Atlas.Codes.hexacode →* sextetStabilizer S :=
  translation (nativeStabilizerEquiv S)

lemma nativeTranslation_injective (S : Sextet) : Function.Injective (nativeTranslation S) :=
  translation_injective (nativeStabilizerEquiv S)

lemma nativeTranslation_normal (S : Sextet) : (nativeTranslation S).range.Normal :=
  translation_normal (nativeStabilizerEquiv S)

lemma nativeTranslation_card (S : Sextet) : Nat.card (nativeTranslation S).range = 64 :=
  translation_card (nativeStabilizerEquiv S)

def nativeQuotient (S : Sextet) : sextetStabilizer S →* Atlas.Codes.HexAutomorphisms :=
  quotient (nativeStabilizerEquiv S)

lemma nativeQuotient_apply (S : Sextet) (s : Atlas.Codes.SextetStabilizer) :
    nativeQuotient S (nativeStabilizerEquiv S s) = Atlas.Codes.sextetQuotient s :=
  congrArg Atlas.Codes.sextetQuotient ((nativeStabilizerEquiv S).symm_apply_apply s)

lemma nativeQuotient_surjective (S : Sextet) : Function.Surjective (nativeQuotient S) :=
  quotient_surjective (nativeStabilizerEquiv S)

lemma nativeQuotient_kernel (S : Sextet) : (nativeQuotient S).ker = (nativeTranslation S).range :=
  quotient_kernel (nativeStabilizerEquiv S)

lemma nativeTranslation_conjugation (S : Sextet) (g : sextetStabilizer S)
    (t : Multiplicative Atlas.Codes.hexacode) :
    g * nativeTranslation S t * g⁻¹ =
      nativeTranslation S
        (Multiplicative.ofAdd (Atlas.Codes.hexAction (nativeQuotient S g) t.toAdd)) :=
  translation_conjugation (nativeStabilizerEquiv S) g t

end
end MathieuCode.SextetLayers.CoordinateTransport
